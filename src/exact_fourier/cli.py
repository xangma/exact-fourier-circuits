"""Bounded exports and exact verification. The seed command stays lazy."""
import argparse
from dataclasses import fields, is_dataclass
from fractions import Fraction
from itertools import islice
import json
from pathlib import Path
import sys
from .examples import demo_cases
from .network import saving_seed_plan
from .words import Word, verify_finite_win


def encode(value):
    if isinstance(value,Fraction): return [value.numerator,value.denominator]
    if is_dataclass(value):
        return {'type':type(value).__name__,**{f.name:encode(getattr(value,f.name)) for f in fields(value)}}
    if isinstance(value,(tuple,list)): return [encode(v) for v in value]
    return value


def write_json(path,value):
    path=Path(path); path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    seed=sub.add_parser('seed',help='exact saving budget and optional lazy macro prefix')
    seed.add_argument('--h',type=int,default=100)
    seed.add_argument('--columns',type=int)
    seed.add_argument('--prefix',type=int,default=0)
    seed.add_argument('--output',type=Path)
    demo=sub.add_parser('demo',help='compile and verify four small exact circuits')
    demo.add_argument('--output',type=Path,default=Path('outputs/demo'))
    verify=sub.add_parser('verify-word',help='verify an actual bounded strict finite-win word')
    verify.add_argument('path',type=Path)
    verify.add_argument('--exponent',type=int,required=True)
    args=parser.parse_args(argv)
    try:
        if args.command=='seed':
            if not 0 <= args.prefix <= 10000: raise ValueError('prefix must be between0 and10000')
            plan=saving_seed_plan(args.h,args.columns)
            value={'schema':'exact-fourier-lazy-seed/v1','budget':plan.metadata(),
                   'prefix_is_complete':False,
                   'instruction_prefix':[encode(i) for i in islice(plan.instructions(),args.prefix)]}
            if args.output: write_json(args.output,value)
            print(json.dumps(value,indent=2))
        elif args.command=='demo':
            summaries=[]
            for name,circuit,matrix in demo_cases():
                certificate=circuit.linear_map_certificate(matrix)
                if not certificate['passed']: raise ValueError(f'exact identity failed: {name}')
                write_json(args.output/(name+'.json'),circuit.to_dict())
                write_json(args.output/(name+'-certificate.json'),certificate)
                summaries.append({'name':name,'inputs':circuit.n_inputs,'scalar_gates':circuit.gate_count,
                                  'exact_basis_verified':True,'circuit_sha256':circuit.stable_hash()})
            write_json(args.output/'summary.json',summaries)
            print(json.dumps(summaries,indent=2))
        else:
            if args.path.stat().st_size > 64*1024*1024: raise ValueError('word file exceeds64MiB')
            word=Word.from_dict(json.loads(args.path.read_text()),max_inputs=256)
            print(json.dumps(verify_finite_win(word,args.exponent),indent=2))
    except (ValueError,OSError,json.JSONDecodeError) as error:
        parser.exit(2,f'error: {error}\n')
    return 0


if __name__=='__main__': sys.exit(main())
