#!/usr/bin/env python3
"""Execute exported scalar DAGs on CUDA; compare to exact rational references.

No benchmark or formal-proof claim. Coefficients round only at this boundary.
Requires NumPy and CuPy; never edits the supplied Python environment.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import time
import numpy as np
import cupy as cp


def scalar(z):
    return complex(z['real'][0]/z['real'][1],z['imag'][0]/z['imag'][1])


def evaluate(circuit,inputs,dtype):
    n=circuit['n_inputs']; gates=circuit['gates']; batch=len(inputs)
    count=n+len(gates)
    if count*batch > 1_000_000 or count > 250000 or batch > 512:
        raise ValueError('CUDA evaluator exceeds fixed allocation limits')
    opcode=cp.asarray([{'add':0,'sub':1,'scale':2}[g['op']] for g in gates],dtype=cp.int32)
    lhs=cp.asarray([g['a'] for g in gates],dtype=cp.int32)
    rhs=cp.asarray([g.get('b',-1) for g in gates],dtype=cp.int32)
    coefficients=np.asarray([scalar(g['coefficient']) if g['op']=='scale' else 0j for g in gates])
    cr=cp.asarray(coefficients.real,dtype=dtype); ci=cp.asarray(coefficients.imag,dtype=dtype)
    vr=cp.zeros((count,batch),dtype=dtype); vi=cp.zeros_like(vr)
    host=np.asarray([[scalar(z) for z in x] for x in inputs])
    vr[:n]=cp.asarray(host.real.T,dtype=dtype); vi[:n]=cp.asarray(host.imag.T,dtype=dtype)
    typename='float' if dtype==np.float32 else 'double'
    source='''extern "C" __global__ void dag(int n,int ng,int batch,
        const int* op,const int* aa,const int* bb,const T* cr,const T* ci,T* vr,T* vi) {
      int t=blockDim.x*blockIdx.x+threadIdx.x;
      if(t>=batch)return;
      for(int g=0;g<ng;++g){
        int a=aa[g],b=bb[g];
        T ar=a<0?0:vr[a*batch+t],ai=a<0?0:vi[a*batch+t];
        T br=b<0?0:vr[b*batch+t],bi=b<0?0:vi[b*batch+t];
        T re,im;
        if(op[g]==2){re=cr[g]*ar-ci[g]*ai;im=cr[g]*ai+ci[g]*ar;}
        else if(op[g]==0){re=ar+br;im=ai+bi;}
        else {re=ar-br;im=ai-bi;}
        vr[(n+g)*batch+t]=re;vi[(n+g)*batch+t]=im;
      }
    }'''.replace('T',typename)
    kernel=cp.RawKernel(source,'dag',options=('--std=c++11','--fmad=false'))
    kernel(((batch+127)//128,),(128,),
           (np.int32(n),np.int32(len(gates)),np.int32(batch),opcode,lhs,rhs,cr,ci,vr,vi))
    cp.cuda.Stream.null.synchronize()
    outputs=circuit['outputs']
    result=np.zeros((len(outputs),batch),dtype=np.complex128)
    for row,ref in enumerate(outputs):
        if ref>=0: result[row]=cp.asnumpy(vr[ref])+1j*cp.asnumpy(vi[ref])
    return result.T


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('fixture',type=Path); parser.add_argument('--output',type=Path,default=Path('cuda-results.json'))
    args=parser.parse_args()
    if args.fixture.stat().st_size>64*1024*1024: raise ValueError('fixture exceeds64MiB')
    raw=args.fixture.read_bytes(); fixture=json.loads(raw)
    if fixture.get('schema')!='exact-fourier-cuda-fixture/v1' or len(fixture['cases'])>16:
        raise ValueError('invalid fixture')
    props=cp.cuda.runtime.getDeviceProperties(0)
    name=props['name'].decode() if isinstance(props['name'],bytes) else props['name']
    report={'schema':'exact-fourier-cuda-result/v1','host':platform.node(),'pid':os.getpid(),
            'device':name,'cupy':cp.__version__,'numpy':np.__version__,
            'cuda_runtime':cp.cuda.runtime.runtimeGetVersion(),'cuda_driver':cp.cuda.runtime.driverGetVersion(),
            'fixture_sha256':hashlib.sha256(raw).hexdigest(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'compile_options':['--std=c++11','--fmad=false'],'cases':[]}
    started=time.monotonic()
    for case in fixture['cases']:
        if not case['certificate']['passed']: raise ValueError('fixture lacks exact basis verification')
        expected=np.asarray([[scalar(z) for z in x] for x in case['expected']])
        record={'name':case['name'],'inputs':case['circuit']['n_inputs'],
                'scalar_gates':len(case['circuit']['gates']),'vectors_checked':len(expected),'errors':{}}
        for dtype,label,tolerance in [(np.float32,'complex64',1e-4),(np.float64,'complex128',1e-12)]:
            actual=evaluate(case['circuit'],case['inputs'],dtype)
            absolute=float(np.max(np.abs(actual-expected)))
            scale=max(1.,float(np.max(np.abs(expected))))
            record['errors'][label]={'max_absolute':absolute,'max_scaled':absolute/scale,
                                      'tolerance':tolerance,'within_tolerance':bool(np.isfinite(absolute) and absolute/scale<=tolerance)}
        report['cases'].append(record)
        print(json.dumps(record),flush=True)
    report['elapsed_seconds']=time.monotonic()-started
    report['passed']=all(e['within_tolerance'] for c in report['cases'] for e in c['errors'].values())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'passed':report['passed'],'elapsed_seconds':report['elapsed_seconds']}))
    return 0 if report['passed'] else 1


if __name__=='__main__': raise SystemExit(main())
