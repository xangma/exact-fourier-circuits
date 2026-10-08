"""Exact canonical-header bytecode tests, with explicit caller boundaries.

Three traces start empty and execute the actual935 startup, charged ordinary
fixture literals, and actual31 header preparation. Full1317 phase diagnostics
use synthetic radix256/original H/G; they do not instantiate Retained n1.
All states remain in the same3**19 budget, and no host interphase writes occur.
"""
from pathlib import Path
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import Poly, F, scalar, execute, direct_dft

ROOT = Path(__file__).resolve().parents[1]
P = ROOT / 'logs/uniform-bytecode/canonical-seed-chunk'
programs = json.loads((P / 'programs.json').read_text())
spec = json.loads((P / 'spec.json').read_text())
code = programs['canonicalSeedChunk']
assert len(code) == 1317 and spec['K'] == 2 and spec['G'] == 194 and spec['capacity'] == 196
assert all(i[0] not in ('root', 'input', 'output') for i in code)


def relocate(ins, base, end):
    op, *a = ins
    if op == 'halt': return ['jump', end]
    if op == 'jump': a[0] += base
    if op == 'branch': a[2] += base; a[3] += base
    return [op, *a]


assert code[:30] == programs['canonicalHeader'][:-1]
assert code[30:1316] == [relocate(i,30,1316) for i in programs['seedChunk']]
assert code[-1] == ['halt']
D, K, N, G, H, radix, B = 128, 2, 4, 194, 23, 256, 3**19
unit = 100000*(1+2)**2
axis_base, axis_directory = 10000, 302
HB, GB = axis_base + 3*radix, axis_base + 4*radix
S,A,fft_rows,C,conv,tape,depth,Q,R = [q*unit for q in [1,2,1,3,2,3,4,5,6]]
Z,CP,RD,FC,U,J = [q*unit for q in [4,5,7,8,9,10]]
borrow,selected,ordinals,mapped_base,perm,widths,markers,axis_row = [q*unit for q in range(30,38)]
NAT_SENTINEL,SCALAR_SENTINEL=B-7,B-11
POINTERS={1127:S,1128:A,1129:fft_rows,1130:C,1131:conv,1132:tape,1133:depth,
          1134:Q,1135:R,1136:Z,1137:CP,1220:RD,1221:FC,1222:U,1223:J,
          1230:borrow,1231:selected,1232:ordinals,1233:mapped_base,1234:perm,
          1235:widths,1236:markers,1237:axis_row}



def greedy(rows):
    colors = []
    for i, (d, s, _) in enumerate(rows):
        used = {colors[j] for j, (x, y, _) in enumerate(rows[:i]) if d in (x, y) or s in (x, y)}
        colors.append(next(c for c in range(11) if c not in used))
    return colors


def fresh(enabled, nonreal, layer, color):
    s = dict(pc=0, nat=[17*i+3 for i in range(1850)], nh={}, sh={}, sr={}, out={}, roots=[D])
    s['nat'][100:107] = [1, 1, 1, 2, D, 100, 200]
    s['nh'] = {axis_directory: axis_base, axis_directory+1: radix, 2: 77, NAT_SENTINEL: 19}
    s['sh'][0] = (Poly(D, {1: 1}), False)
    h = [scalar(D, 1)[0], scalar(D, 2 if nonreal else 0, 3 if nonreal else 0)[0]]
    h += [Poly(D)] * (radix-2)
    g = [h[0], -h[1]] + [Poly(D)] * (radix-2)
    for i in range(radix):
        s['sh'][HB+i] = (h[i], False)
        s['sh'][GB+i] = (g[i], False)
    for q in range(100): s['sr'][q] = scalar(D, F(q-4, 7), F(2-q, 9), q%2)
    for q in list(range(S,S+6*N))+list(range(C,C+7*N+1))+list(range(Z,Z+7*N))+list(range(CP,CP+6)):
        s['sh'][q] = scalar(D, q-3, 11-q, True)
    for q in [fft_rows, conv, tape, depth, Q, R, RD, FC, U, J, borrow, selected, ordinals,
              mapped_base, perm, widths, markers, axis_row]: s['nh'][q] = q+31
    s['sh'][SCALAR_SENTINEL] = scalar(D, -7, 3, True)
    s['out'][0] = scalar(D, 7, -2)[0]
    header = {1120:0,1122:1,1123:1,1124:1,1125:0,1126:1,1224:int(enabled),1238:layer,1239:color}
    for q,v in header.items(): s['nat'][q] = v
    # Computed exponent and all helper headers deliberately start stale.
    assert s['nat'][1121] != K and s['nat'][1180] != radix
    return s, h, g


def reference(enabled):
    rows = spec['rows']
    labels = [0, 0]
    for op, left, right, kind, payload in rows:
        labels.append((max(labels[left], labels[right]) if op < 2 else labels[left]) + 1)
    order = sorted(range(G), key=lambda i:(labels[2+i], i))
    buckets = [[] for _ in range(H)]
    for i in order:
        op,left,right,kind,payload = rows[i]
        def emit(source, coefficient):
            if (source < 1 and enabled) or source > 1:
                buckets[labels[2+i]].append([2+i, source, coefficient])
        if op < 2:
            emit(left, CP); emit(right, CP+op)
        else: emit(left, C+payload if kind==1 else CP if payload<2 else CP+2)
    return labels, order, buckets


def check(s, old, h, g, enabled, layer, color):
    assert s['pc'] == 1316 and s['nat'][1121] == K and s['nat'][1180] == radix
    assert s['nat'][1241:1244] == [0,1,0]
    assert s['nat'][1181:1193] == [0,1,borrow,selected,ordinals,mapped_base,perm,widths,markers,axis_row,layer,color]
    one, zero = scalar(D, 1), scalar(D)
    kernels = [[(g[1],False),zero,zero,zero], [(-h[0],False),zero,zero,zero],
               [(h[1]*g[0]+h[0]*g[1],False),zero,zero,zero], [one,zero,zero,zero],
               [one,zero,zero,zero], [zero]*N]
    omega = Poly(D,{1:1}) ** (D//N)
    values = [(omega**j,False) for j in range(N)]
    for slot, kernel in enumerate(kernels):
        assert [s['sh'][S+slot*N+j] for j in range(N)] == kernel
        values += direct_dft(omega, kernel)
    assert [s['sh'][C+j] for j in range(7*N)] == values
    assert s['sh'][C+7*N] == (omega,False)
    assert [s['sh'][Z+j] for j in range(7*N)] == [(-v,False) for v,_ in values]
    assert [s['sh'][CP+j] for j in range(6)] == [scalar(D,q) for q in [1,-1,F(1,N),F(-1,N),F(5,4),F(4,5)]]
    labels, order, buckets = reference(enabled)
    assert [s['nh'][depth+j] for j in range(2+G)] == labels
    assert [s['nh'][Q+j] for j in range(G)] == order
    assert [s['nh'][R+j] for j in range(G+2)] == [sum(labels[2+i]<j for i in range(G)) for j in range(G+2)]
    for i, row in enumerate(spec['rows']): assert [s['nh'][tape+5*i+j] for j in range(5)] == row
    for d,W in enumerate(buckets):
        rb, fb = RD+6*G*d, FC+2*G*d
        assert [s['nh'][rb+3*i+j] for i in range(len(W)) for j in range(3)] == [v for row in W for v in row]
        assert [s['nh'][fb+i] for i in range(len(W))] == greedy(W)
        assert [s['nh'][J+3*d+j] for j in range(3)] == [len(W),rb,fb]
    W = buckets[layer]; indices = [i for i,c in enumerate(greedy(W)) if c==color]
    chosen = [W[i] for i in indices]
    borrowed = [i for i in range(radix) if i not in (0,1)][:G]
    def coordinate(p):
        assert p<1 or 2<=p<2+G+1
        return p if p<1 else borrowed[p-2] if p<2+G else 1+p-2-G
    physical = [[coordinate(d),coordinate(src),c] for d,src,c in chosen]
    assert [s['nh'][borrow+i] for i in range(G)] == borrowed
    assert s['nat'][894] == len(indices)
    assert [s['nh'][ordinals+i] for i in range(len(indices))] == indices
    assert [[s['nh'][selected+3*i+j] for j in range(3)] for i in range(len(chosen))] == chosen
    assert [[s['nh'][mapped_base+3*i+j] for j in range(3)] for i in range(len(physical))] == physical
    used = [p for d,src,c in physical for p in (d,src)]
    assert len(used)==len(set(used)) and all(0<=p<radix for p in used)
    permutation = used + [p for p in range(radix) if p not in used]
    ws = [2]*len(physical)+[1]*(radix-2*len(physical))
    assert [s['nh'][perm+i] for i in range(radix)] == permutation
    assert [s['nh'][widths+i] for i in range(len(ws))] == ws
    assert [s['nh'][axis_row+i] for i in range(4)] == [len(ws),widths,radix,perm]
    assert sum(ws)==radix and sorted(permutation)==list(range(radix))
    assert s['roots']==old['roots'] and s['out']==old['out'] and s['nat'][100:107]==old['nat'][100:107]
    for q in [0,axis_directory,axis_directory+1,2,NAT_SENTINEL]:
        bank = 'sh' if q==0 else 'nh'; assert s[bank][q]==old[bank][q]
    for q in range(HB,HB+radix): assert s['sh'][q]==old['sh'][q]
    for q in range(GB,GB+radix): assert s['sh'][q]==old['sh'][q]
    assert s['sh'][SCALAR_SENTINEL]==old['sh'][SCALAR_SENTINEL]
    return len(chosen), len(W)


# Actual empty935 startup followed by charged ordinary-header installation and
# the literal31 header phase. Full chunk capacity is NOT asserted for n1.
startup_cases=[]
for re,im in [(0,0),(1,2),(-2,3)]:
    value=scalar(D,re,im,True)[0]
    empty=dict(pc=0,nat=[0]*1850,nh={},sh={},sr={},out={},roots=[])
    reference_state=copy.deepcopy(empty)
    t0,_,_=execute(programs['seedStartup'],reference_state,B,100000,D,1,[value])
    state=copy.deepcopy(empty)
    t,pcs,peak=execute(programs['startupHeader'],state,B,100000,D,1,[value])
    assert t==t0+64 and state['pc']==998
    assert state['sh']==reference_state['sh'] and state['nh']==reference_state['nh']
    assert state['sr']==reference_state['sr'] and state['out']==reference_state['out']
    assert state['roots']==reference_state['roots']==[128]
    assert state['nat'][100:107]==reference_state['nat'][100:107]
    assert state['nat'][101]==1
    assert {q:state['nat'][q] for q in POINTERS}==POINTERS
    assert set(range(967,998))<=set(pcs)
    startup_cases.append(dict(input=[re,im],steps=t,startupSteps=t0,maximumWord=peak,
                              scope='Actual empty startup plus charged header-only fixture; no valid full chunk for n1.'))

cases,covered,steps_total=[],set(),0
for enabled in [False,True]:
    _,_,buckets=reference(enabled)
    occupied=[d for d,W in enumerate(buckets) if W]
    assert occupied
    for nonreal in [False,True]:
        for layer,color in [(0,10),(occupied[0],0),(H-1,0)]:
            s,h,g=fresh(enabled,nonreal,layer,color);before=copy.deepcopy(s)
            assert all(s['nat'][q]!=v for q,v in POINTERS.items())
            steps,pcs,peak=execute(code,s,B,5000000,D,1)
            count,raw=check(s,before,h,g,enabled,layer,color)
            assert {q:s['nat'][q] for q in POINTERS}==POINTERS
            cases.append(dict(enabled=enabled,nonreal=nonreal,layer=layer,color=color,
                              selected=count,raw=raw,steps=steps,maximumWord=peak))
            steps_total+=steps;covered.update(pcs)
            print('continuous1317 synthetic physical phase',len(cases),count,steps,flush=True)

controls=[]
def reject(name,state,code_=code,budget=5000000):
    try:execute(code_,state,B,budget,D,1)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')
for name,bank,address in [('missing-axis-offset','nh',axis_directory),('missing-axis-width','nh',axis_directory+1),
                         ('missing-master','sh',0),('missing-H','sh',HB+1),('missing-G','sh',GB+1)]:
    s,_,_=fresh(True,True,1,0);del s[bank][address];reject(name,s)
s,_,_=fresh(True,True,1,0);s['nat'][1230]=B+1;reject('initial-word-guard',s)
s,_,_=fresh(True,True,1,0);reject('charged-step-budget',s,budget=10)
s,_,_=fresh(True,True,1,0)
for q in [HB,HB+1,GB,GB+1]:s['sh'][q]=(s['sh'][q][0],True)
reject('data-data-guard',s)
s,_,_=fresh(True,True,H,0);reject('missing-out-of-range-directory',s)
mutant=copy.deepcopy(code);mutant[30+1]=['jump',30+2]
s,_,_=fresh(True,True,1,0);reject('axis-capture-mutation',s,mutant)
new=set(range(30))|{1316}
assert new<=covered and any(c['selected'] for c in cases)
result=dict(status='PASS',instructions=1317,headerInstructions=31,startupHeaderFixtureInstructions=999,
            exactCases=len(cases)+len(startup_cases),actualStartupHeaderCases=startup_cases,
            syntheticPhysicalPhaseCases=cases,chargedSteps=steps_total+sum(c['steps'] for c in startup_cases),
            visitedPCs=len(covered),unvisitedPCs=sorted(set(range(1317))-covered),
            allNewCallerPCsVisited=True,negativeControls=controls,
            arithmetic='Sparse exact rational cyclotomic Q[eta]/Phi128; no floats.',
            scope='Three actual empty startup/header-only traces; twelve full continuous1317 synthetic physical diagnostics with radix256 and supplied original H/G, NOT actual Retained n1 selected coefficients. No output banks/tables/allocation headers or interphase host writes are supplied. Universal Lean theorem applies to genuine selected geometry/Retained; nonempty actual selected witness is formal. No full DFT/global scheduler claim.',
            sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in
                    [P/'programs.json',P/'spec.json',ROOT/'verification/ExportCanonicalSeedChunkBytecode.lean',
                     Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','exactCases','chargedSteps','visitedPCs','allNewCallerPCsVisited','negativeControls']},indent=2))
