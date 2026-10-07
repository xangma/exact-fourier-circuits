#!/usr/bin/env python3
"""Produce exact inputs, exact outputs and full scalar DAGs for the CUDA check."""
from fractions import Fraction
import json
from pathlib import Path
import random
import sys
from exact_fourier.examples import demo_cases
from exact_fourier.scalars import GaussianRational as QI

random_source=random.Random(130)
cases=[]
for name,circuit,matrix in demo_cases():
    certificate=circuit.linear_map_certificate(matrix)
    if not certificate['passed']: raise SystemExit(f'failed exact basis identity: {name}')
    inputs=[[QI(int(i==j)) for i in range(circuit.n_inputs)] for j in range(circuit.n_inputs)]
    inputs.extend([[QI(Fraction(random_source.randrange(-16,17),8),
                       Fraction(random_source.randrange(-16,17),8))
                    for _ in range(circuit.n_inputs)] for _ in range(8)])
    cases.append({'name':name,'circuit':circuit.to_dict(),'certificate':certificate,
                  'inputs':[[z.to_dict() for z in x] for x in inputs],
                  'expected':[[z.to_dict() for z in circuit.evaluate(x)] for x in inputs]})
target=Path(sys.argv[1] if len(sys.argv)>1 else 'outputs/cuda-fixture.json')
target.parent.mkdir(parents=True,exist_ok=True)
target.write_text(json.dumps({'schema':'exact-fourier-cuda-fixture/v1','cases':cases},sort_keys=True)+'\n')
print(target)
