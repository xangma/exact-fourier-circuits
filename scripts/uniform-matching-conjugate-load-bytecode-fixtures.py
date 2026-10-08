"""Exact traces of signed matching coefficient/conjugate loads, including row reads."""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_cyclotomic_engine import execute, scalar, Poly

ROOT = Path(__file__).resolve().parents[1]
P = ROOT/'logs/uniform-bytecode/matching-conjugate-load'
PROGRAMS = {False: json.loads((P/'program.json').read_text()),
            True: json.loads((P/'row-program.json').read_text())}
B, M = 100000, 8
assert [len(PROGRAMS[i]) for i in [False, True]] == [18, 25]


def conjugate(v):
    out = {}
    for k, q in v.c.items():
        j, sign = (0, 1) if k == 0 else (M-k, -1)
        out[j] = out.get(j, F(0))+sign*q
    return Poly(M, out)


def fresh(R, K, kind, index, dirty, row):
    C, T, P0, V, a, b, D = 20, 100, 200, 400, 600, 601, 1000
    state = dict(pc=0, nat=[(19*i+dirty+37) % 971 for i in range(2200)],
                 sr={i: scalar(M, i+5, dirty-7, True) for i in range(120)},
                 nh={17: 61, 1009: 13}, sh={}, out={1: Poly(M, {2: 17})}, roots=[16])
    bank = [Poly(M) if i % 7 == 0 else
            Poly(M, {0: F(3*i-7, 13), 1: F(i+1, 17), 4: F(2*i-5, 19), 6: F(i-4, 23)})
            for i in range(R)]
    constants = [Poly(M, {0: q}) for q in [1, -1, F(1, 2**K), -F(1, 2**K), F(5, 4), F(4, 5)]]
    for i, v in enumerate(bank):
        state['sh'][C+i] = (v, False)
        state['sh'][T+i] = (-v, False)
        state['sh'][V+i] = (conjugate(v), False)
    for i, v in enumerate(constants):
        state['sh'][P0+i] = (v, False)
    for j in [a, b, 777]:
        state['sh'][j] = scalar(M, -100-j, dirty+13, True)
    address = {'positive': C, 'negative': T, 'constant': P0}[kind]+index
    for register, value in {2100: C, 2101: T, 2102: P0, 2103: V, 2106: a, 2107: b,
                            2140: D, 2141: dirty+1}.items():
        state['nat'][register] = value
    state['nat'][2105] = 9999 if row else address
    for j in range(dirty+2):
        state['nh'][D+3*j] = 55+j
        state['nh'][D+3*j+1] = 33+j
        state['nh'][D+3*j+2] = address
    return state, a, b, address, state['sh'][address][0]


cases, covered = [], {False: set(), True: set()}
for R in [0, 1, 7, 14, 56]:
    coefficients = [('positive', i) for i in range(R)]+[('negative', i) for i in range(R)]
    coefficients += [('constant', i) for i in range(6)]
    for K in [0, 1, 3, 12]:
        for dirty in [0, 1, 2]:
            for kind, index in coefficients:
                for row in [False, True]:
                    state, a, b, address, value = fresh(R, K, kind, index, dirty, row)
                    old = copy.deepcopy(state)
                    expected = {'positive': 10, 'negative': 12, 'constant': 9}[kind]+7*row
                    steps, pcs = execute(PROGRAMS[row], state, B, expected, M)
                    assert steps == expected and state['pc'] == (24 if row else 17)
                    assert state['sh'][a] == (value, False)
                    assert state['sh'][b] == (conjugate(value), False)
                    assert state['nh'] == old['nh'] and state['out'] == old['out'] and state['roots'] == old['roots']
                    assert all(state['sh'][q] == v for q, v in old['sh'].items() if q not in (a, b))
                    scratch = {2112} | ({2105, 2110, 2111} if row else set())
                    assert all(state['nat'][q] == old['nat'][q] for q in range(len(state['nat'])) if q not in scratch)
                    assert all(state['sr'][q] == old['sr'][q] for q in old['sr'] if q not in (70, 71, 72))
                    covered[row].update(pcs)
                    cases.append(dict(R=R, K=K, kind=kind, index=index, dirty=dirty, row=row, steps=steps))
assert all(covered[row] == set(range(len(PROGRAMS[row]))) for row in covered)

controls = []


def reject(name, state, row=False, limit=100000, bound=B):
    try:
        execute(PROGRAMS[row], state, bound, limit, M)
    except (AssertionError, KeyError):
        controls.append(name)
    else:
        raise AssertionError(name+' accepted')


s, *_ = fresh(7, 3, 'positive', 1, 2, False); del s['sh'][21]; reject('missing-original', s)
s, *_ = fresh(7, 3, 'positive', 1, 2, False); del s['sh'][401]; reject('missing-positive-conjugate', s)
s, *_ = fresh(7, 3, 'negative', 1, 2, False); del s['sh'][401]; reject('missing-signed-conjugate', s)
s, *_ = fresh(7, 3, 'constant', 4, 2, False); del s['sh'][204]; reject('missing-normalization-constant', s)
s, *_ = fresh(7, 3, 'negative', 1, 2, True); del s['nh'][1000+3*3+2]; reject('missing-mapped-coefficient-field', s, True)
s, *_ = fresh(7, 3, 'negative', 1, 2, False); s['nat'][2107] = B+1; reject('initial-word-overflow', s)
s, *_ = fresh(7, 3, 'negative', 1, 2, False); reject('charged-runtime-shortfall', s, limit=11)
result = dict(status='PASS', instructions=18, rowInstructions=25, exactCases=len(cases),
              chargedSteps=sum(c['steps'] for c in cases), allPCsVisited=True,
              negativeControls=controls, uniform_algorithm_verified=False,
              arithmetic='Exact Q[X]/(X^8+1), general non-Gaussian cyclotomic coefficients; no division or new root.',
              scope='Actual mapped three-word row reads and ordered positive/negative/conjugate/real constant banks, all six constants, zero coefficients and dirty flags. Physical input banks are diagnostic fixtures; not an actual selected SeedChunk producer or full DFT execution.',
              cases=cases,
              sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [P/'program.json', P/'row-program.json', ROOT/'verification/ExportMatchingConjugateLoadBytecode.lean',
                       ROOT/'lean/UniformMatchingConjugateLoadMachine.lean', Path(__file__), ROOT/'scripts/uniform_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: result[k] for k in ['status', 'exactCases', 'chargedSteps', 'allPCsVisited', 'negativeControls']}, indent=2))
