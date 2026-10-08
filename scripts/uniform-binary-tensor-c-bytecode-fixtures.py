"""Execute the fixed all-axis C tensor loop against direct exact tensor entries."""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute, add, mul

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT/'logs/uniform-bytecode/binary-tensor-c'
CODE = json.loads((PACKET/'program.json').read_text())
assert len(CODE) == 42
A = scalar(4, F(1, 2), F(1, 2))
B = scalar(4, F(1, 2), F(-1, 2))
WRITES = {0, 1, 2, 2800, 2801, 2802, 2803, 2804, 2805, 2806,
          2810, 2811, 2820, 2821, 2822}


def fresh(k, base, salt):
    s = dict(pc=0, nat=[(17*i+salt)%97 for i in range(2830)],
             nh={0: 17, 100: 31}, sh={1: A, 2: B},
             sr={0: scalar(4, 3, -7, True), 8: scalar(4, F(3, 7), F(2, 3))},
             out={2: scalar(4, -3, 2)[0]}, roots=[4, 12])
    for r, v in {2823: base, 2824: 2**k, 2825: k}.items():
        s['nat'][r] = v
    for z in range(2**k):
        s['sh'][base+z] = scalar(4, F(3*z+salt-5, 7), F(2*z-salt+1, 11),
                                  (z+salt)%3 != 0)
    s['sh'][base-1] = scalar(4, 3, 2, True)
    s['sh'][base+2**k] = scalar(4, -7, 0)
    return s


def reference(k, values):
    # Full tensor matrix entries, independent of machine stage/control order.
    out = []
    for row in range(2**k):
        result = scalar(4, 0)
        for col in range(2**k):
            coefficient = scalar(4, 1)
            for axis in range(k):
                coefficient = mul(coefficient, A if ((row >> axis)&1) ==
                                  ((col >> axis)&1) else B)
            result = add(result, mul(coefficient, values[col]))
        out.append(result)
    return out


cases = []; covered = set(); ticks = 0
for k in range(6):
    for base in (7, 1000):
        for salt in (0, 31):
            s = fresh(k, base, salt); before = copy.deepcopy(s)
            values = [before['sh'][base+z] for z in range(2**k)]
            expected = copy.deepcopy(s['sh'])
            for z, value in enumerate(reference(k, values)):
                expected[base+z] = value
            budget = k*(25*2**max(k-1, 0)+11)+8
            steps, pcs, peak = execute(CODE, s, 10000, budget, 4)
            assert steps == budget and s['pc'] == 41
            assert s['sh'] == expected, (k, base, salt)
            assert s['nat'][2820] == k and s['nat'][2800] == 2**k
            assert s['nat'][2802] == 0
            for key in ('nh', 'out', 'roots'):
                assert s[key] == before[key], key
            for r in range(len(s['nat'])):
                if r not in WRITES:
                    assert s['nat'][r] == before['nat'][r], r
            for r in set(s['sr']) | set(before['sr']):
                if r >= 8:
                    assert s['sr'].get(r) == before['sr'].get(r), r
            ticks += steps; covered.update(pcs)
            cases.append(dict(bits=k, volume=2**k, base=base, salt=salt,
                              steps=steps, maximumWord=peak))

controls = []


def reject(name, state, bound=10000, fuel=10000):
    try:
        execute(CODE, state, bound, fuel, 4)
    except (AssertionError, KeyError):
        controls.append(name)
        return
    raise AssertionError('negative control accepted: '+name)


s = fresh(1, 7, 31); del s['sh'][1]; reject('missing diagonal coefficient', s)
s = fresh(1, 7, 31); del s['sh'][2]; reject('missing off-diagonal coefficient', s)
s = fresh(1, 7, 31); del s['sh'][7]; reject('missing source', s)
s = fresh(1, 7, 31); s['sh'][1] = (A[0], True); reject('data-data multiplication guard', s)
reject('charged runtime guard', fresh(3, 7, 31), fuel=340)
s = fresh(0, 7, 31); s['nat'] = [0]*2830
s['nat'][2823:2826] = [7, 1, 0]; s['nh'] = {}; s['out'] = {}; s['roots'] = []
reject('final cursor word guard from bounded initial state', s, bound=40)
s = fresh(1, 7, 31); s['pc'] = 39; s['nat'][2822] = 0
reject('division-zero guard in update fragment', s)
assert covered == set(range(42)), sorted(set(range(42))-covered)
result = dict(status='PASS', exactCases=len(cases), chargedSteps=ticks, cases=cases,
              negativeControls=controls, coveredPCs=sorted(covered),
              scope='Continuous actual fixed42 all-axis binary C tensor loop; direct exact full tensor matrix reference, dependency flags and complete outside frame. Prepared physical a/b constants and power-of-two volume headers are stated entry inputs. No saving-network recursion, coefficient startup, DFT output or CUDA timing claim.',
              hashes={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in [Path(__file__), PACKET/'program.json',
                                ROOT/'verification/ExportBinaryTensorCBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS', len(cases), 'complete exact binary C tensors,', ticks,
      'charged steps,', len(controls), 'guard controls')
