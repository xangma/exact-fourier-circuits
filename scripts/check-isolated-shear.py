#!/usr/bin/env python3
"""Small CUDA shear diagnostic with exact references for stored inputs.

Four algebraically identical variants, FP32/FP64 and FMA on/off. The caller
must impose a process deadline. Raw inputs/outputs and generated CUDA are kept.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from exact_fourier.scalars import GaussianRational as QI
from exact_fourier.words import KERNEL_C, Word, shear_steps

spec = importlib.util.spec_from_file_location('projected', ROOT / 'scripts/check-projected-cuda.py')
projected = importlib.util.module_from_spec(spec)
spec.loader.exec_module(projected)
VARIANTS = ('direct', 'compiled', 'common_power_two', 'source_scaled')

KERNEL = r'''
extern "C" __global__ void isolated(const T* inputs,const int* ids,const T* coefficients,
 const T* normalizers,T* outputs,double* peaks,unsigned long long* nan_events,
 unsigned long long* inf_events,int count,int variant,int one_id) {
 int k=blockIdx.x*blockDim.x+threadIdx.x; if(k>=count) return;
 Z s0={inputs[4*k],inputs[4*k+1]},s1={inputs[4*k+2],inputs[4*k+3]};
 double peak=0; unsigned long long nans=0,infs=0;
 track(s0,peak,nans,infs); track(s1,peak,nans,infs);
 T t=coefficients[k],scale=normalizers[k];
 if(variant==0) s0=add_z(s0,scale_z(s1,t,(T)0,peak,nans,infs),peak,nans,infs);
 else {
   if(variant==2) {
     s0=scale_z(s0,scale,(T)0,peak,nans,infs);
     s1=scale_z(s1,scale,(T)0,peak,nans,infs);
   }
   if(variant==3) s1=scale_z(s1,t,(T)0,peak,nans,infs);
   compiled_shear(variant==3 ? one_id : ids[k],s0,s1,peak,nans,infs);
   if(variant==3) {s1.r/=t; s1.i/=t; track(s1,peak,nans,infs);}
   if(variant==2) {
     s0.r/=scale; s0.i/=scale; s1.r/=scale; s1.i/=scale;
     track(s0,peak,nans,infs); track(s1,peak,nans,infs);
   }
 }
 outputs[4*k]=s0.r;outputs[4*k+1]=s0.i;outputs[4*k+2]=s1.r;outputs[4*k+3]=s1.i;
 peaks[k]=peak;nan_events[k]=nans;inf_events[k]=infs;
}
'''


def cases(dtype):
    import numpy as np
    rows, meta = [], []
    def add(family, t, y, x):
        row = np.array([y.real,y.imag,x.real,x.imag],dtype=dtype)
        assert np.isfinite(row).all()
        rows.append(row); meta.append({'family':family,'coefficient':str(t)})
    coefficients = [Q(1,4),Q(-1,4),Q(1,2),Q(-1,2),Q(1),Q(-1),Q(5,4),Q(2)]
    eps = np.finfo(dtype).eps
    for t in coefficients:
        for j in range(16):
            x = complex((j+1)/16,(17-j)/32)
            add('balanced',t,complex((j-8)/8,(j%5-2)/4),x)
            for residual in (0,eps,8*eps):
                add('cancellation',t,-float(t)*x+complex(residual,-residual),x)
        for power in ((0,8,16,24,32) if dtype==np.float32 else (0,16,32,48,64)):
            add('large_target_small_source',t,complex(math.ldexp(1,power),0),1+0j)
        for power in ((-100,100,120,124) if dtype==np.float32 else (-900,900,1016,1020)):
            magnitude=math.ldexp(1,power)
            add('range',t,complex(magnitude,-magnitude/2),complex(magnitude/2,magnitude/4))
    tiny=Q(1,2**(100 if dtype==np.float32 else 900))
    add('tiny_coefficient',tiny,complex(math.ldexp(1,40 if dtype==np.float32 else 200),0),1+0j)
    return np.asarray(rows),meta


def exact_metrics(inputs,outputs,meta,u):
    # Fraction arithmetic includes output subtraction: FP64 is not its own oracle.
    results=[]
    for row,out,description in zip(inputs,outputs,meta):
        t=Q(description['coefficient']); q=[Q(float(v)) for v in row]
        reference=[q[0]+t*q[2],q[1]+t*q[3],q[2],q[3]]
        finite=all(math.isfinite(float(v)) for v in out)
        target_scale=max(abs(q[0])+abs(t*q[2]),abs(q[1])+abs(t*q[3]))
        source_scale=max(abs(q[2]),abs(q[3]))
        if finite:
            errors=[abs(Q(float(v))-ref) for v,ref in zip(out,reference)]
            target_error=max(errors[:2]);source_error=max(errors[2:])
            target_rel=target_error/target_scale if target_scale else target_error
            source_rel=source_error/source_scale if source_scale else source_error
            small_scale=max(abs(reference[0]),abs(reference[1]))
            small_rel=float(target_error/small_scale) if small_scale else None
            passes=target_rel<=64*u and source_rel<=64*u
        else:
            target_rel=source_rel=small_rel=None;passes=False
        results.append({**description,'finite':finite,'passes':bool(passes),
          'target_scaled_error':float(target_rel) if finite else None,
          'source_relative_error':float(source_rel) if finite else None,
          'target_output_relative_error':small_rel,
          'input_hex':[float(v).hex() for v in row],
          'output_hex':[float(v).hex() for v in out],
          'exact_target':[str(v) for v in reference[:2]]})
    return results


def main():
    import numpy as np
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--prepare-only',action='store_true')
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    started=time.monotonic();all_results=[];source_hashes={}
    for dtype in (np.float32,np.float64):
        inputs,meta=cases(dtype)
        coefficients=sorted({Q(m['coefficient']) for m in meta}|{Q(1)})
        # Verify each generated literal word with independent Gaussian rationals.
        for t in coefficients:
            word=Word(KERNEL_C,2,shear_steps(0,1,t))
            assert word.compile().verify_matrix(((1,t),(0,1)))
        source=projected.CUDA_TEMPLATE.split('extern "C" __global__ void projected_network')[0]
        source=source.replace('@TYPE@','float' if dtype==np.float32 else 'double')
        source=source.replace('@SHEAR_CASES@',projected.shear_cases(coefficients)[0])+KERNEL
        label=np.dtype(dtype).name;source_path=args.output/f'{label}.cu'
        source_path.write_text(source);source_hashes[label]=hashlib.sha256(source.encode()).hexdigest()
        np.savez(args.output/f'{label}-inputs.npz',inputs=inputs)
        if args.prepare_only:continue
        import cupy as cp
        ids=np.array([coefficients.index(Q(m['coefficient'])) for m in meta],dtype=np.int32)
        ts=np.array([float(Q(m['coefficient'])) for m in meta],dtype=dtype)
        normals=np.array([math.ldexp(1,-math.frexp(float(max(abs(v) for v in row)))[1])
                          for row in inputs],dtype=dtype)
        device_args=[cp.asarray(a) for a in (inputs,ids,ts,normals)]
        for fma in (False,True):
            options=('--std=c++11',f'--fmad={str(fma).lower()}','--ftz=false')
            # CuPy's RawKernel cache injects -ftz=true. Compile directly with
            # NVRTC, then load its retained object, to control this flag exactly.
            obj,_=cp.cuda.compiler.compile_using_nvrtc(source,options=options,
                arch=cp.cuda.Device().compute_capability)
            binary=args.output/f'{label}-fma{int(fma)}.cubin';binary.write_bytes(obj)
            kernel=cp.RawModule(path=str(binary)).get_function('isolated')
            for variant,name in enumerate(VARIANTS):
                out=cp.empty_like(device_args[0]);peaks=cp.zeros(len(inputs),dtype=cp.float64)
                nans=cp.zeros(len(inputs),dtype=cp.uint64);infs=cp.zeros_like(nans)
                kernel(((len(inputs)+127)//128,),(128,),(*device_args,out,peaks,nans,infs,
                       np.int32(len(inputs)),np.int32(variant),np.int32(coefficients.index(Q(1)))))
                cp.cuda.runtime.deviceSynchronize()
                raw=cp.asnumpy(out)
                path=args.output/f'{label}-fma{int(fma)}-{name}.npz'
                np.savez(path,outputs=raw,peaks=cp.asnumpy(peaks),nans=cp.asnumpy(nans),infs=cp.asnumpy(infs))
                metrics=exact_metrics(inputs,raw,meta,Q(float(np.finfo(dtype).eps/2)))
                all_results.append({'precision':label,'fma':fma,'variant':name,
                  'cases':len(inputs),'failed':sum(not m['passes'] for m in metrics),
                  'nonfinite':sum(not m['finite'] for m in metrics),'metrics':metrics,
                  'raw_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
                print(json.dumps({k:v for k,v in all_results[-1].items() if k!='metrics'}),flush=True)
    receipt={'schema':'isolated-shear/v1','host':platform.node(),'elapsed_seconds':time.monotonic()-started,
      'criterion':'finite; target error <=64u*(|y|+|t*x|) component max; source error <=64u*|x| component max',
      'reference':'exact rational arithmetic on stored input and output components',
      'source_hashes':source_hashes,'results':all_results,'prepared_only':args.prepare_only,
      'harness_hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in (Path(__file__).resolve(),ROOT/'scripts/check-projected-cuda.py',
                  ROOT/'src/exact_fourier/words.py',ROOT/'src/exact_fourier/scalars.py')},
      'compiler_options':{'ftz':False,'fma':[False,True],'standard':'c++11'}}
    (args.output/'results.json').write_text(json.dumps(receipt,indent=2,allow_nan=False)+'\n')


if __name__=='__main__':main()
