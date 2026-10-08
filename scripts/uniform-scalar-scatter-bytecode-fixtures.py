"""Actual inverse scatter of arbitrary tagged arrays; no roots/division occur."""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_cyclotomic_engine import execute, scalar, Poly
ROOT = Path(__file__).resolve().parents[1]
P = ROOT / 'logs/uniform-bytecode/scalar-scatter'
CODE = json.loads((P/'program.json').read_text())
SPECS = json.loads((P/'specs.json').read_text())
B = 100000
assert len(CODE) == 12
assert all(x[0] not in ('root', 'input', 'output', 'fadd', 'fsub', 'fmul', 'fdiv') for x in CODE)


def fresh(spec, reverse, dirty):
    L, phi = spec['L'], spec['permutation']
    a, d = (3000, 1000) if reverse else (1000, 3000)
    b = 7000
    s = dict(pc=0, nat=[13*q+dirty+7 for q in range(1530)], nh={4: 73, B-1: 19},
             sh={0: scalar(8, 9, -7), B-1: scalar(8, 19, -21, True)},
             sr={q: scalar(8, F(2*q+1, 5), F(7-q, 3), q % 2) for q in range(100)},
             out={3: Poly(8, {1: F(7, 5), 4: -3})}, roots=[16, 9, 1])
    values = [scalar(8, F(3*j-7, 11), F(2*j+5, 13), (j+dirty) % 3 != 0) for j in range(L)]
    for i in range(L):
        s['nh'][b+i] = phi[i]
        s['sh'][a+i] = values[phi[i]]
        s['sh'][d+i] = scalar(8, -i-100, dirty+17, True)
    for q, v in {1506: L, 1507: a, 1508: d, 1509: b}.items():
        s['nat'][q] = v
    return s, a, d, b, values


cases, covered = [], set()
for spec in SPECS:
    L, phi = spec['L'], spec['permutation']
    assert sorted(phi) == list(range(L))
    assert spec['inverse'] == [phi.index(j) for j in range(L)]
    for reverse in [False, True]:
        for dirty in [0, 1]:
            s, a, d, b, values = fresh(spec, reverse, dirty)
            old = copy.deepcopy(s)
            steps, pcs = execute(CODE, s, B, 9*L+4, 8)
            assert steps == 9*L+4 and s['pc'] == 11 and s['nat'][1510] == L
            assert [s['sh'][d+j] for j in range(L)] == values
            assert [s['sh'][a+j] for j in range(L)] == [old['sh'][a+j] for j in range(L)]
            assert all(s['sh'][d+phi[i]] == old['sh'][a+i] for i in range(L))
            assert s['nh'] == old['nh'] and s['out'] == old['out'] and s['roots'] == old['roots']
            assert all(s['sh'][q] == v for q, v in old['sh'].items() if not d <= q < d+L)
            assert {q: v for q, v in s['sr'].items() if q != 90} == {q: v for q, v in old['sr'].items() if q != 90}
            assert all(s['nat'][q] == old['nat'][q] for q in range(len(s['nat'])) if not 1510 <= q <= 1516)
            if L == 3 and spec['shift'] == 1 and not spec['reversed']:
                assert [old['sh'][a+phi[j]] for j in range(L)] != values
            covered.update(pcs)
            cases.append(dict(**spec, reverseLayout=reverse, dirty=dirty, steps=steps))

controls = []
control = next(x for x in SPECS if x['L'] == 3 and x['shift'] == 1 and not x['reversed'])


def reject(name, s, budget=100000):
    try:
        execute(CODE, s, B, budget, 8)
    except (AssertionError, KeyError):
        controls.append(name)
    else:
        raise AssertionError(name+' accepted')


s, a, d, b, _ = fresh(control, False, 1); del s['nh'][b+1]; reject('missing-inverse-entry', s)
s, a, d, b, _ = fresh(control, False, 1); del s['sh'][a+2]; reject('missing-packed-source', s)
s, *_ = fresh(control, False, 1); s['nat'][1508] = B; reject('destination-word-overflow', s)
s, *_ = fresh(control, False, 1); s['nat'][1509] = B+1; reject('initial-word-guard', s)
s, *_ = fresh(control, False, 1); reject('charged-step-budget', s, 3)
assert covered == set(range(12))
result = dict(status='PASS', instructions=12, exactCases=len(cases), chargedSteps=sum(c['steps'] for c in cases),
              allPCsVisited=True, negativeControls=controls,
              arithmetic='Exact Gaussian rational tags in Q[X]/(X^8+1); copying only, no root or field division.',
              scope='Actual permutation bank, disjoint tagged banks in either address order, dirty destination, L0 and non-involutive cycles. This is inverse scatter, not gather; no six-C/full-DFT claim.', cases=cases,
              sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [P/'program.json', P/'specs.json', ROOT/'verification/ExportScalarScatterBytecode.lean',
                       Path(__file__), ROOT/'scripts/uniform_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: result[k] for k in ['status', 'exactCases', 'chargedSteps', 'allPCsVisited', 'negativeControls']}, indent=2))
