"""Exact continuous1438 packing diagnostics; not a feasible selected-axis startup.

The universal Lean theorem consumes actual Retained selected coefficients. These
small exact tests use ordinary synthetic physical H/G and a directory radix256
with master order128. That is NOT the actual n1 selected radix or coefficient
bank. No generated output table/bank/header and no interphase host writes enter.
"""
from pathlib import Path
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import Poly, F, scalar, execute, direct_dft

ROOT = Path(__file__).resolve().parents[1]
P = ROOT / 'logs/uniform-bytecode/seed-chunk-packing'
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


def check(s, old, h, g, enabled, layer, color):
    assert s['pc'] == 1437 and s['nat'][1121] == K and s['nat'][1180] == radix
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
    for q in [0,axis_directory,axis_directory+1,2,900000]:
        bank = 'sh' if q==0 else 'nh'; assert s[bank][q]==old[bank][q]
    for q in range(HB,HB+radix): assert s['sh'][q]==old['sh'][q]
    for q in range(GB,GB+radix): assert s['sh'][q]==old['sh'][q]
    assert s['sh'][900000]==old['sh'][900000]
    assert [s['nh'][inverse+i] for i in range(radix)]==permutation
    assert [s['sh'][data_dest+i] for i in range(radix)]==[old['sh'][data_source+j] for j in permutation]
    assert [s['sh'][data_source+i] for i in range(radix)]==[old['sh'][data_source+i] for i in range(radix)]
    # Frozen Packing137 produces the inverse-address array internally; for one
    # matching axis its packed ordinal maps to exactly this original endpoint.
    for i,(d,src,_) in enumerate(physical):
        assert s['sh'][data_dest+2*i]==old['sh'][data_source+d]
        assert s['sh'][data_dest+2*i+1]==old['sh'][data_source+src]
    assert [s['sh'][data_dest+i] for i in range(radix)]!=[old['sh'][data_source+i] for i in range(radix)] or not chosen
    assert s['nh'][suffix]==radix and s['nh'][suffix+1]==1
    assert s['nat'][1400:1405]==[suffix,stack,inverse,data_source,data_dest]
    return len(chosen), len(W)


cases, covered, steps_total = [], set(), 0
for enabled in [False,True]:
    _,_,buckets=reference(enabled)
    occupied=[i for i,W in enumerate(buckets) if W]
    layers = sorted(set([0,H-1] + occupied[:2] + occupied[-1:]))
    for nonreal in [False,True]:
        for layer in layers:
            for color in [0,1,10]:
                s,h,g = fresh(enabled,nonreal,layer,color); before=copy.deepcopy(s)
                steps,pcs,peak=execute(code,s,B,5_000_000,D,1)
                count,raw=check(s,before,h,g,enabled,layer,color)
                cases.append(dict(enabled=enabled,nonreal=nonreal,layer=layer,color=color,selected=count,raw=raw,steps=steps,maximumWord=peak))
                steps_total+=steps;covered.update(pcs)
                print('continuous1438 generic-phase',len(cases),enabled,nonreal,layer,color,count,steps,flush=True)

controls=[]
def reject(name, state, code_=code, budget=5_000_000):
    try: execute(code_,state,B,budget,D,1)
    except (AssertionError,KeyError): controls.append(name)
    else: raise AssertionError(name+' accepted')
for name,bank,address in [('missing-axis-offset','nh',axis_directory),('missing-axis-width','nh',axis_directory+1),
                         ('missing-master','sh',0),('missing-H','sh',HB+1),('missing-G','sh',GB+1)]:
    s,_,_=fresh(True,True,1,0);del s[bank][address];reject(name,s)
s,_,_=fresh(True,True,1,0);s['nat'][1230]=B+1;reject('initial-word-guard',s)
s,_,_=fresh(True,True,1,0);reject('charged-step-budget',s,budget=10)
s,_,_=fresh(True,True,1,0)
for q in [HB,HB+1,GB,GB+1]: s['sh'][q]=(s['sh'][q][0],True)
reject('data-data-guard',s)
s,_,_=fresh(True,True,1,0);del s['sh'][data_source+1];reject('missing-contiguous-data',s)
s,_,_=fresh(True,True,H,0);reject('missing-out-of-range-directory',s)
# Fresh exported caller mutation: delete the charged boot capture instruction.
mutant=copy.deepcopy(code);mutant[1]=['jump',2]
s,_,_=fresh(True,True,1,0);reject('axis-capture-mutation',s,mutant)
new=set(range(1286,1438))
assert set(range(1286))<=set(range(len(code)))
assert new<=covered and any(c['selected'] for c in cases)
result=dict(status='PASS',instructions=1438,exactCases=len(cases),chargedSteps=steps_total,visitedPCs=len(covered),
            unvisitedPCs=sorted(set(range(1438))-covered),allNewCallerPCsVisited=True,allContinuationPCsVisited=True,negativeControls=controls,cases=cases,
            contracts=dict(actualTypedCross=True,genericMatchingCapacity=True,packingPlacement=True,contiguousTaggedSource=True,actualSelectedRetained=False,actualSelectedMetadata=False,actualSelectedLayout=False),
            arithmetic='Sparse exact rational cyclotomic Q[eta]/Phi128; no floats.',
            scope='Generic physical phase diagnostics only. Synthetic directory radix256 and supplied original prepared H/G are not actual Retained n1 selected coefficients. Entire1438 is continuous; no generated banks/tables/helper headers or interphase host writes. Universal Lean theorem proves genuine selected inputs; formal selected nonempty capacity196 witness uses primeProduct194. Ordinary capacity/packing placements, live bank disjointness and low contiguous SourceReady hold; the canonical selected Retained/Metadata contracts do not. No feasible large-axis startup execution or full DFT is claimed. Generated packing inverse addresses are checked, coefficient tags retained; no six-C round or unpack runs in this diagnostic.',
            sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in
                    [P/'programs.json',P/'spec.json',ROOT/'verification/ExportSeedChunkPackingBytecode.lean',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','exactCases','chargedSteps','visitedPCs','allNewCallerPCsVisited','negativeControls']},indent=2))
