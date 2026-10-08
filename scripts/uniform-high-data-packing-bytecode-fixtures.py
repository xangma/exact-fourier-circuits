"""Exact continuous physical1286 ->167 copy/packing diagnostics.
Synthetic H/G and radix256 are generic physical inputs, not a canonical selected
startup instance. Actual generated matching tables, widths, permutation, count
are produced by the exported1286 before the new167. No interphase host writes.
"""
from pathlib import Path
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import Poly, F, scalar, execute, direct_dft

ROOT = Path(__file__).resolve().parents[1]
P = ROOT / 'logs/uniform-bytecode/high-data-packing'
programs = json.loads((P / 'programs.json').read_text())
spec = json.loads((P / 'spec.json').read_text())
code = programs['seedChunkPacking']
assert len(code) == 1438 and spec['K'] == 2 and spec['G'] == 194 and spec['capacity'] == 196
assert all(i[0] not in ('root', 'input', 'output') for i in code)


def relocate(ins, base, end):
    op, *a = ins
    if op == 'halt': return ['jump', end]
    if op == 'jump': a[0] += base
    if op == 'branch': a[2] += base; a[3] += base
    return [op, *a]


assert code[:1286] == [relocate(i,0,1286) for i in programs['seedChunk']]
assert code[4:1050] == [relocate(i, 4, 1050) for i in programs['height']]
assert code[1070:1285] == [relocate(i, 1070, 1285) for i in programs['chunk']]
assert code[-1] == ['halt']
D, K, N, G, H, radix, B = 128, 2, 4, 194, 23, 256, 10**9
axis_base, axis_directory = 10000, 302
HB, GB = axis_base + 3*radix, axis_base + 4*radix
S, A, fft_rows, C, conv, tape, depth, Q, R = 20000, 30000, 30000, 40000, 40000, 50000, 60000, 100000, 200000
Z, CP, RD = 50000, 60000, 300000
FC, U = RD + 6*G*H + 50, RD + 8*G*H + 100
J = U + 100
borrow = J + 3*H + 50
selected = borrow + G + 50
ordinals = selected + 6*G + 50
mapped_base = ordinals + 2*G + 50
perm = mapped_base + 6*G + 50
widths = perm + radix + 50
markers = widths + radix + 50
axis_row = markers + radix + 50
suffix, stack, inverse = axis_row+10, axis_row+20, axis_row+40
data_source, data_dest = 5000, 700000


def greedy(rows):
    colors = []
    for i, (d, s, _) in enumerate(rows):
        used = {colors[j] for j, (x, y, _) in enumerate(rows[:i]) if d in (x, y) or s in (x, y)}
        colors.append(next(c for c in range(11) if c not in used))
    return colors


def validate_numeric_layout(layer, color):
    # Genuine generic Matching/Packing capacity and address placements.
    # This is not the selected-axis Layout n j: radix256 is synthetic.
    assert G+1+1 <= radix and 2 <= radix and layer < H and color < 11
    assert RD+6*G*H <= borrow and FC+2*G*H <= borrow and J+3*H <= borrow
    assert borrow+G <= selected and selected+6*G <= ordinals
    assert ordinals+2*G <= mapped_base and mapped_base+6*G <= perm
    assert perm+radix <= widths and widths+radix <= markers and markers+radix <= axis_row
    assert axis_row+4 <= suffix and suffix+2 <= stack and stack+9 <= inverse
    assert inverse+radix <= B and data_source+radix <= data_dest and data_dest+radix <= B
    assert data_source+radix <= axis_base and axis_base+5*radix <= data_dest
    assert C+7*N+1 <= data_dest and Z+7*N <= data_dest and CP+6 <= data_dest
    assert 0 < 1 <= 1 < radix and 2 <= radix  # a=e=1, i0=split1, j0=0.
    assert HB+radix <= S and GB+radix <= S and S+6*N <= A
    assert conv+5*(3*K*N+2*N) <= tape and tape+5*G <= depth
    assert depth+2+G <= Q and Q+G*(G+1) <= R and R+G+2 <= RD


def fresh(enabled, nonreal, layer, color):
    if layer < H and color < 11:
        validate_numeric_layout(layer,color)
    s = dict(pc=0, nat=[17*i+3 for i in range(1520)], nh={}, sh={}, sr={}, out={}, roots=[D])
    s['nat'][100:107] = [1, 0, 1, 2, D, 100, 200]
    s['nh'] = {axis_directory: axis_base, axis_directory+1: radix, 2: 77, 900000: 19}
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
    s['sh'][900000] = scalar(D, -7, 3, True)
    s['out'][0] = scalar(D, 7, -2)[0]
    for i in range(radix):
        s['sh'][data_source+i]=scalar(D,F(3*i-7,11),F(4-i,13),i%3!=0)
        s['sh'][data_dest+i]=scalar(D,-i-9,17+i,True)
    header = {1120:0,1122:1,1123:1,1124:1,1125:0,1126:1,1127:S,1128:A,1129:fft_rows,
              1130:C,1131:conv,1132:tape,1133:depth,1134:Q,1135:R,1136:Z,1137:CP,
              1220:RD,1221:FC,1222:U,1223:J,1224:int(enabled),
              1230:borrow,1231:selected,1232:ordinals,1233:mapped_base,1234:perm,
              1235:widths,1236:markers,1237:axis_row,1238:layer,1239:color,
              1450:suffix,1451:stack,1452:inverse,1453:data_source,1454:data_dest}
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


HIGH=650000
NEW=programs['highData'];SEED=programs['seedChunk']
assert len(NEW)==167 and len(SEED)==1286
assert NEW[:4]==[['lit',2241,0],['add',147,1180,2241],['add',148,2240,2241],['add',149,1453,2241]]
assert NEW[4:14]==[relocate(i,4,14)for i in programs['copy']]
assert NEW[14:166]==[relocate(i,14,166)for i in programs['continuation']]
WHOLE=[relocate(i,0,1286)for i in SEED]+[relocate(i,1286,1453)for i in NEW]+[['halt']]
assert len(WHOLE)==1454 and all(i[0]not in('input','root','output')for i in WHOLE)

def entry(enabled,nonreal,layer,color,zero=False):
    s,h,g=fresh(enabled,nonreal,layer,color)
    s['nat'] += [17*i+3 for i in range(len(s['nat']),2300)]
    s['nat'][1453]=HIGH;s['nat'][2240]=data_source
    for i in range(radix):
        if zero and i%3==0:s['sh'][data_source+i]=scalar(D,dep=i%2)
        s['sh'][HIGH+i]=scalar(D,-i-21,17+i,True)
    # Frozen generated tables and all caller/result registers are initially dirty.
    assert s['nat'][894]!=0 and s['nat'][147]!=radix
    return s,h,g

cases=[];pcs=set();controls=[]
for enabled,nonreal,layer,color,zero in [(True,True,1,0,False),(False,False,0,10,True),
 (True,False,2,1,True),(False,True,H-1,0,False)]:
    s,h,g=entry(enabled,nonreal,layer,color,zero);old=copy.deepcopy(s)
    steps,covered,peak=execute(WHOLE,s,B,5_000_000,D,1)
    assert s['pc']==1453 and s['nat'][1180]==radix and s['nat'][147]==radix
    permutation=[s['nh'][perm+i]for i in range(radix)]
    assert sorted(permutation)==list(range(radix))
    assert [s['sh'][HIGH+i]for i in range(radix)]==[old['sh'][data_source+i]for i in range(radix)]
    assert [s['sh'][data_dest+i]for i in range(radix)]==[old['sh'][data_source+i]for i in permutation]
    assert [s['nh'][inverse+i]for i in range(radix)]==permutation
    assert [s['sh'][data_source+i]for i in range(radix)]==[old['sh'][data_source+i]for i in range(radix)]
    assert s['roots']==old['roots']and s['out']==old['out']and s['nat'][100:107]==old['nat'][100:107]
    assert s['sh'][0]==old['sh'][0]and s['sh'][900000]==old['sh'][900000]
    assert all(s['sh'][q]==old['sh'][q]for q in range(HB,HB+radix))
    assert all(s['sh'][q]==old['sh'][q]for q in range(GB,GB+radix))
    assert s['nh'][axis_directory]==old['nh'][axis_directory]and s['nh'][900000]==old['nh'][900000]
    # Staged duplicate, diagnostic only: measure new167 independently and check
    # all unchanged physical stores and exact tags against continuous trace.
    staged=copy.deepcopy(old);seedTicks,_,_=execute(SEED,staged,B,5_000_000,D,1)
    before=copy.deepcopy(staged);staged['pc']=0
    newTicks,newCovered,_=execute(NEW,staged,B,100000,D,1)
    assert newTicks<=220*radix+44 and staged['pc']==166
    assert steps==seedTicks+newTicks+1
    assert all(staged[k]==s[k]for k in ['nat','nh','sh','sr','out','roots'])
    assert {i for i in range(14)}|{166}<=set(newCovered)
    assert all(staged['sh'][q]==before['sh'][q]for q in range(C,C+7*N+1))
    assert all(staged['sh'][q]==before['sh'][q]for q in range(Z,Z+7*N))
    assert all(staged['sh'][q]==before['sh'][q]for q in range(CP,CP+6))
    pcs.update(newCovered);cases.append(dict(enabled=enabled,nonreal=nonreal,layer=layer,color=color,
     zeros=zero,selected=s['nat'][894],newTicks=newTicks,continuousTicks=steps,maximumWord=peak))
    print('continuous1454',len(cases),steps,'new167',newTicks,flush=True)

def reject(name,state,code_=WHOLE,budget=5_000_000):
    try:execute(code_,state,B,budget,D,1)
    except(AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')
for name,bank,address in [('missing-low-data','sh',data_source+1),('missing-master','sh',0),
 ('missing-H','sh',HB+1),('missing-G','sh',GB+1),('missing-original-directory','nh',axis_directory)]:
    s,_,_=entry(True,True,1,0);del s[bank][address];reject(name,s)
s,_,_=entry(True,False,1,0);s['nat'][2240]=B+1;reject('initial-word-guard',s)
s,_,_=entry(True,True,1,0);reject('charged-budget',s,budget=20)
mutant=copy.deepcopy(WHOLE);mutant[1286+3]=['lit',149,0]
s,_,_=entry(True,True,1,0)
try:
 execute(mutant,s,B,5_000_000,D,1)
 assert [s['sh'][data_dest+i]for i in range(radix)]==[s['sh'][data_source+s['nh'][inverse+i]]for i in range(radix)]
except(AssertionError,KeyError):controls.append('copy-destination-mutation')
else:raise AssertionError('copy destination mutation silently passed')
result=dict(status='PASS',instructions=167,continuousInstructions=1454,exactCases=len(cases),successfulCases=len(cases),
 negativeControls=controls,visitedPCs=len(pcs),unvisitedPCs=sorted(set(range(167))-pcs),allNewCallerPCsVisited=True,cases=cases,
 scope='Actual exported1286 derives typed cross/order/depth/color/matching permutation/count from synthetic H/G/radix256, then continuous167 copies tagged low data to high source and runs generated-axis packing. No interphase host writes. Synthetic selected inputs are not actual canonical Retained/Metadata/Layout n1. Universal theorem covers genuine selected Result with ordinary high allocation and present low data. No six-C or fullDFT theorem.',
 sha256={str(q.relative_to(ROOT)):hashlib.sha256(q.read_bytes()).hexdigest()for q in
 [ROOT/'lean/UniformHighDataPackingPreparation.lean',ROOT/'verification/ExportHighDataPackingBytecode.lean',Path(__file__),
 ROOT/'scripts/uniform_seed_cyclotomic_engine.py',P/'programs.json',P/'spec.json']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k]for k in['status','exactCases','visitedPCs','negativeControls']},indent=2))
