#!/usr/bin/env python3
"""Independently verify retained shear arrays and replay two source-loss traces."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from exact_fourier.words import Call, Scale, Word, KERNEL_C, shear_steps


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replay(dtype, target_power, source):
    # Every primitive scalar operation rounds separately, matching --fmad=false.
    def add(x, y): return tuple(dtype(a+b) for a, b in zip(x, y))
    def sub(x, y): return tuple(dtype(a-b) for a, b in zip(x, y))
    def scale(x, z):
        r, i = dtype(float(z.real)), dtype(float(z.imag))
        return (dtype(dtype(r*x[0])-dtype(i*x[1])),
                dtype(dtype(r*x[1])+dtype(i*x[0])))
    values = [(dtype(math.ldexp(1, target_power)), dtype(0)), (dtype(source), dtype(0))]
    trace = []
    for index, step in enumerate(shear_steps(0, 1, 1)):
        if isinstance(step, Scale):
            values[step.coordinate] = scale(values[step.coordinate], step.coefficient)
        else:
            assert isinstance(step, Call)
            a, b = step.coordinates
            d = sub(values[b], values[a]); z = scale(d, KERNEL_C[0][1])
            values[a], values[b] = add(values[a], z), sub(values[b], z)
        trace.append({'step':index, 'op':type(step).__name__,
                      'state_hex':[float(v).hex() for pair in values for v in pair]})
    return np.array([v for pair in values for v in pair], dtype=dtype), trace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('retained', type=Path, help='extracted completed.tar.gz root')
    parser.add_argument('--summary', type=Path, required=True)
    parser.add_argument('--traces', type=Path, required=True)
    args = parser.parse_args(); output = args.retained/'output'
    receipt = json.loads((output/'results.json').read_text())
    for relative, expected in receipt['harness_hashes'].items():
        assert digest(ROOT/relative) == expected, relative
        assert digest(args.retained/relative) == expected, relative
    for name, expected in receipt['source_hashes'].items():
        assert digest(output/f'{name}.cu') == expected
    arms = []; traces = []; arrays = {}
    for arm in receipt['results']:
        precision, fma, variant = arm['precision'], arm['fma'], arm['variant']
        inputs = np.load(output/f'{precision}-inputs.npz')['inputs']
        raw_path = output/f'{precision}-fma{int(fma)}-{variant}.npz'
        assert digest(raw_path) == arm['raw_sha256']
        outputs = np.load(raw_path)['outputs']; arrays[precision, fma, variant] = outputs
        assert len(inputs) == len(outputs) == len(arm['metrics']) == 585
        u = Q(float(np.finfo(inputs.dtype).eps))/2; failed = nonfinite = 0
        for row, out, m in zip(inputs, outputs, arm['metrics']):
            t = Q(m['coefficient']); q = [Q(float(x)) for x in row]
            target = [q[0]+t*q[2], q[1]+t*q[3]]
            finite = all(math.isfinite(float(x)) for x in out)
            if finite:
                errors = [abs(Q(float(x))-ref) for x, ref in zip(out, target+q[2:])]
                ts = max(abs(q[0])+abs(t*q[2]), abs(q[1])+abs(t*q[3]))
                ss = max(abs(q[2]), abs(q[3]))
                te = max(errors[:2])/ts if ts else max(errors[:2])
                se = max(errors[2:])/ss if ss else max(errors[2:])
                passes = te <= 64*u and se <= 64*u
                assert float(te) == m['target_scaled_error']
                assert float(se) == m['source_relative_error']
            else:
                nonfinite += 1; passes = False
            assert finite == m['finite'] and passes == m['passes']
            assert [float(x).hex() for x in row] == m['input_hex']
            assert [float(x).hex() for x in out] == m['output_hex']
            assert list(map(str, target)) == m['exact_target']
            failed += not passes
        assert failed == arm['failed'] and nonfinite == arm['nonfinite']
        arms.append({k:v for k,v in arm.items() if k != 'metrics'})
    for precision, variant in {(p,v) for p,f,v in arrays}:
        assert arrays[precision,False,variant].tobytes() == arrays[precision,True,variant].tobytes()
    for dtype, power in ((np.float32,24), (np.float64,64)):
        label = np.dtype(dtype).name
        one, t1 = replay(dtype, power, 1); zero, t0 = replay(dtype, power, 0)
        coalescence = next(i for i,(a,b) in enumerate(zip(t1,t0)) if a['state_hex'] == b['state_hex'])
        assert all(a['state_hex'] == b['state_hex'] for a,b in zip(t1[coalescence:],t0[coalescence:]))
        assert one.tobytes() == zero.tobytes()
        word = Word(KERNEL_C,2,shear_steps(0,1,1))
        assert word.compile().verify_matrix(((1,1),(0,1)))
        arm = next(a for a in receipt['results'] if a['precision']==label and not a['fma'] and a['variant']=='compiled')
        i = next(i for i,m in enumerate(arm['metrics']) if m['family']=='large_target_small_source' and
                 m['coefficient']=='1' and m['input_hex']==[float(math.ldexp(1,power)).hex(),float(0).hex(),float(1).hex(),float(0).hex()])
        assert arrays[label,False,'compiled'][i].tobytes() == one.tobytes()
        assert arrays[label,False,'direct'][i,2] == 1 and one[2] == 0
        traces.append({'precision':label,'target_power':power,'coefficient':'1',
                       'first_coalescing_step_zero_based':coalescence,
                       'source_one':t1,'source_zero':t0,
                       'matches_cuda_nonfma':True,'exact_matrix_verified':True})
    summary = {'passed':True,'arms':len(arms),'cases_per_arm':585,'total_cases':sum(a['cases'] for a in arms),
               'fma_arrays_bitwise_equal':True,'results':arms,
               'archive_sha256':digest(ROOT/'verification/isolated-shear/completed.tar.gz'),
               'reference':'independent Fraction subtraction on raw stored float components',
               'source_hashes_checked':receipt['harness_hashes']}
    args.summary.write_text(json.dumps(summary,indent=2)+'\n')
    args.traces.write_text(json.dumps({'method':'CPU scalar-component rounding; chronological literal word; no FMA',
                                     'traces':traces,'replay_source_sha256':digest(Path(__file__))},indent=2)+'\n')
    print(f"Verified {summary['total_cases']} raw cases; source-loss CPU traces match CUDA.")


if __name__ == '__main__': main()
