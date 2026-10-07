#!/usr/bin/env python3
"""Exact full-program checks and CUDA fixtures for dyadic stress families."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import time
import numpy as np
from exact_fourier.dyadic import exact_rows,run_program,independent_target,state_hash
from exact_fourier.projection import build_projected_program


def arrays(rows):
    real,imag=zip(*(row.floats() for row in rows))
    return np.asarray(real,dtype=np.float64),np.asarray(imag,dtype=np.float64)


def families(shape,seed):
    rng=np.random.default_rng(seed)
    r=rng.integers(-16,17,shape).astype(np.float64)/8
    i=rng.integers(-16,17,shape).astype(np.float64)/8
    yield 'moderate_dyadic',r,i
    r=np.ldexp(rng.integers(-16,17,shape).astype(np.float64),rng.integers(-40,41,shape))/8
    i=np.ldexp(rng.integers(-16,17,shape).astype(np.float64),rng.integers(-40,41,shape))/8
    yield 'wide_dynamic_range',r,i
    signs=np.where((np.indices(shape).sum(axis=0)%2)==0,1.,-1.)
    r=signs*(2.**20+rng.integers(0,5,shape)/8)
    i=-signs*(2.**20+rng.integers(0,5,shape)/8)
    yield 'cancellation',r,i


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits',type=int,default=6)
    parser.add_argument('--seed',type=int,default=130)
    parser.add_argument('--output',type=Path,default=Path('outputs/projected-stability/bits6'))
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    began=time.monotonic()
    print(json.dumps({'host':platform.node(),'pid':os.getpid(),'cwd':str(Path.cwd()),
                      'output':str(args.output),'bits':args.bits,'next_check':'family/checkpoint progress within60seconds',
                      'stop':f'kill -TERM {os.getpid()}'}),flush=True)
    program=build_projected_program(bits=args.bits,seed=args.seed).to_dict()
    program_path=args.output/'program.json'
    program_path.write_text(json.dumps(program,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps({'program':program['metadata']}),flush=True)
    rr=[];ii=[];ref_r=[];ref_i=[];cp_r=[];cp_i=[];names=[];receipts=[]
    for name,real,imag in families((program['metadata']['roles'],program['metadata']['width']),args.seed):
        started=time.monotonic()
        if not (np.array_equal(real,real.astype(np.float32).astype(np.float64)) and
                np.array_equal(imag,imag.astype(np.float32).astype(np.float64))):
            raise AssertionError('stress input is not exactly representable in both precisions')
        print(json.dumps({'family':name,'status':'exact-reference-started'}),flush=True)
        initial=exact_rows(real,imag)
        expected=independent_target(program,initial)
        checkpoint_real=[];checkpoint_imag=[];checkpoint_hashes=[]
        def capture(label,rows):
            a,b=arrays(rows)
            checkpoint_real.append(a);checkpoint_imag.append(b)
            checkpoint_hashes.append({'label':label,'exact_state_sha256':state_hash(rows)})
            print(json.dumps({'family':name,'checkpoint':label,'elapsed_seconds':time.monotonic()-started}),flush=True)
        actual=run_program(program,initial,capture)
        if actual!=expected:
            raise AssertionError(f'full projected program differs from independent exact target: {name}')
        a,b=arrays(expected)
        names.append(name);rr.append(real);ii.append(imag);ref_r.append(a);ref_i.append(b)
        cp_r.append(checkpoint_real);cp_i.append(checkpoint_imag)
        receipts.append({'family':name,'exact_agreement':True,'roles_checked':len(actual),
                         'complex_coordinates_checked':real.size,'exact_input_sha256':state_hash(initial),
                         'exact_source_sha256':state_hash(actual),'exact_target_sha256':state_hash(expected),
                         'checkpoint_hashes':checkpoint_hashes,'input_exact_in_fp32_and_fp64':True,
                         'elapsed_seconds':time.monotonic()-started})
        print(json.dumps(receipts[-1]),flush=True)
    fixture_path=args.output/'fixture.npz'
    np.savez_compressed(fixture_path,real=np.asarray(rr),imag=np.asarray(ii),
                        reference_real=np.asarray(ref_r),reference_imag=np.asarray(ref_i),
                        checkpoint_reference_real=np.asarray(cp_r),checkpoint_reference_imag=np.asarray(cp_i),
                        family_names=np.asarray(names),checkpoint_labels=np.asarray([c['label'] for c in program['checkpoints']]))
    receipt={'schema':'exact-projected-fixture-verification/v1','host':platform.node(),'pid':os.getpid(),
             'numpy':np.__version__,'program_sha256':hashlib.sha256(program_path.read_bytes()).hexdigest(),
             'fixture_sha256':hashlib.sha256(fixture_path.read_bytes()).hexdigest(),
             'metadata':program['metadata'],'families':receipts,'elapsed_seconds':time.monotonic()-began,
             'scope':'exact agreement on three dirty dyadic arrays; not an exhaustive matrix certificate or a saving witness'}
    (args.output/'exact-verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'completed','elapsed_seconds':receipt['elapsed_seconds']}),flush=True)


if __name__=='__main__':main()
