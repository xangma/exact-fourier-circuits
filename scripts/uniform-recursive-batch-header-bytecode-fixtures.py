"""Exact dispatch diagnostics; recursive body fragments are explicitly marked.

The paper's first recursive k is 72,000,000. Its entire repeated-doubling
trace is handled by the universal Lean proof, not materialized by this test.
"""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'logs/uniform-bytecode/recursive-batch-header'
CODE = json.loads((PACKET / 'program.json').read_text())
SPEC = json.loads((PACKET / 'spec.json').read_text())
T, M, H, W, R = [SPEC[k] for k in ('threshold', 'blockSize', 'roleBits', 'width', 'residuals')]
assert len(CODE) == 25 and (T, M, H) == (72000000, 1000000, 71)
assert W == 2**H and R == 2361183241427951204156000000
assert all(i[0] in ('lit', 'div', 'sub', 'mul', 'add', 'branch', 'jump', 'halt') for i in CODE)


def fresh(k, salt=0, pc=0):
    s = dict(pc=pc, nat=[(17*i+salt) % 97 for i in range(2460)],
             nh={0:17, 100:31}, sh={7:scalar(4,F(2,3),F(-3,7),True)},
             sr={0:scalar(4,3,-7,True), 100:scalar(4,0,0,False)},
             out={2:scalar(4,-3,2)[0]}, roots=[4,12])
    s['nat'][2440] = k
    return s


def frames(before, after):
    for key in ('nh', 'sh', 'sr', 'out', 'roots'):
        assert before[key] == after[key], key
    for i in range(len(after['nat'])):
        if i not in range(2441,2453):
            assert before['nat'][i] == after['nat'][i], i


cases, covered, ticks = [], set(), 0
for k in (0,1,70,71,1000,T-1):
    for salt in (0,41):
        s = fresh(k,salt); before = copy.deepcopy(s)
        steps, pcs, peak = execute(CODE,s,T+100,8,4)
        assert steps == 8 and s['pc'] == 24
        assert [s['nat'][r] for r in (2441,2442,2443,2445,2446)] == [0]*5
        assert s['nat'][2447] == T
        frames(before,s); covered.update(pcs); ticks += steps
        cases.append(dict(scope='complete actual base dispatch',k=k,steps=steps,maximumWord=peak))

# The same exported program, entered at pc3: exercise its actual arithmetic
# body with small exponents. These k take the BASE branch when entered at pc0.
for e in (0,1,2,7,15):
    k = H+e
    for salt in (0,41):
        s = fresh(k,salt,3); before = copy.deepcopy(s)
        steps, pcs, peak = execute(CODE,s,max(T,R*2**e,100),4*e+15,4)
        assert steps == 4*e+15 and s['pc'] == 24
        assert [s['nat'][r] for r in (2441,2442,2443,2444,2445,2446)] == [0,e,2**e,e,R*2**e,1]
        assert s['nat'][2445]*(W*2**s['nat'][2441]) == R*2**k
        frames(before,s); covered.update(pcs); ticks += steps
        cases.append(dict(scope='recursive-body fragment at pc3; below real threshold',k=k,steps=steps,maximumWord=peak))

# Nonzero loop progress and its final count, without changing the bytecode.
for e in (1,7,15):
    for i in (0,e//2,e):
        s = fresh(H+e,41,13)
        for r,v in {2441:0,2442:e,2443:2**i,2444:i,2450:R,2451:1,2452:2}.items():
            s['nat'][r] = v
        before=copy.deepcopy(s)
        steps,pcs,peak=execute(CODE,s,max(T,R*2**e),4*(e-i)+5,4)
        assert steps==4*(e-i)+5 and s['nat'][2445]==R*2**e and s['nat'][2444]==e
        frames(before,s);covered.update(pcs);ticks+=steps
        cases.append(dict(scope='loop suffix fragment at pc13',exponent=e,startIndex=i,steps=steps,maximumWord=peak))

controls=[]
def reject(name,state,bound,fuel):
    try:
        execute(CODE,state,bound,fuel,4)
    except (AssertionError,KeyError):
        controls.append(name); return
    raise AssertionError('negative control accepted: '+name)

reject('base charged runtime guard',fresh(1),T,7)
reject('initial Nat word guard',fresh(T+1),T,100)
reject('threshold literal word guard',fresh(1),T-1,100)
reject('recursive residual literal guard',fresh(H,pc=3),T,100)
s=fresh(H+1,pc=13)
for r,v in {2441:0,2442:1,2443:1,2444:0,2450:R,2451:1,2452:2}.items(): s['nat'][r]=v
reject('child count intermediate word guard',s,R,100)
s=fresh(H,pc=8);s['nat'][2448]=0
reject('integer division zero guard',s,T,100)
assert covered == set(range(25))
result=dict(status='PASS',exactCases=len(cases),chargedSteps=ticks,cases=cases,
            negativeControls=controls,coveredPCs=sorted(covered),
            scope='Complete base paths plus explicitly entered arithmetic fragments of the unchanged fixed25. No full genuine paper-threshold recursive trace, child transform, scheduler or UniformDFTStatement claim.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [Path(__file__),PACKET/'program.json',PACKET/'spec.json',ROOT/'verification/ExportRecursiveBatchHeaderBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'exact dispatch/fragment cases,',ticks,'charged steps,',len(controls),'guard controls')
