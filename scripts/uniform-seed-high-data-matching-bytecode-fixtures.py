"""Exact physical generated matching ->1366 copy/packing/conjugate/six-C diagnostics.
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
P = ROOT / 'logs/uniform-bytecode/seed-high-data-matching'
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


JOIN=programs['producer'];MATCH=programs['conjugateMatching']
assert len(JOIN)==1366 and JOIN[:167]==[relocate(i,0,167)for i in NEW]
assert JOIN[167:1365]==[relocate(i,167,1365)for i in MATCH]
WS,WA,WC,WD,WCONV,WTAPE,WDEPTH=70000,80000,90000,1000000,1001000,1010000,1020000
V,mu,bar=WC+7*N+20,WC+14*N+40,WC+14*N+41
CONJBASE,CONJDIR=18000,axis_directory+4
future={1820:V,1821:0,484:1,485:1,486:1,487:0,488:1,490:WS,525:K,
        527:WA,528:WD,529:WC,563:WCONV,564:WTAPE,675:WDEPTH}
# Diagnostic wrapper physically installs allocation headers after1286. Its
# literal layout is fixed for these fixtures; it is not a universal caller.
INSTALL=[['lit',q,v]for q,v in future.items()]
BASE=1286+len(INSTALL);END=BASE+1366
COMBINED=programs['whole'];BASE=1302;END=2668
assert COMBINED[:1286]==[relocate(i,0,1286)for i in SEED]
assert COMBINED[1302:2668]==[relocate(i,1302,2668)for i in JOIN]
assert COMBINED[1286:1302]==[['lit',2265,0]]+[['add',target,2250+i,2265]for i,target in enumerate(future)]
assert len(COMBINED)==END+1

def ready(enabled,nonreal,layer,color,zero):
 s,h,g=entry(enabled,nonreal,layer,color,zero)
 for i,value in enumerate(future.values()):s['nat'][2250+i]=value
 s['nh'][CONJDIR]=CONJBASE;s['nh'][CONJDIR+1]=radix
 # Distinct complete original/conjugate compact-lane storage: the cross
 # operands are specifically lane3 invH and lane4 G, never lane0 H.
 for lane in range(3):
  for i in range(radix):
   value=scalar(D,37+lane+2*i,11-lane+i if nonreal else 0)[0]
   s['sh'][axis_base+lane*radix+i]=(value,False)
   s['sh'][CONJBASE+lane*radix+i]=(value.conjugate(),False)
 assert s['sh'][axis_base][0]!=h[0]
 for i in range(radix):
  s['sh'][CONJBASE+3*radix+i]=(h[i].conjugate(),False)
  s['sh'][CONJBASE+4*radix+i]=(g[i].conjugate(),False)
 for i,(re,im) in enumerate([(F(1,2),F(1,2)),(F(1,2),F(-1,2)),(1,-1),(0,1),(1,1)],1):s['sh'][i]=scalar(D,re,im)
 for address in range(WS,V+7*N):s['sh'][address]=scalar(D,address%7,3-address%9,True)
 for address in range(WD,WDEPTH+G+2):s['nh'][address]=(7*address+11)%73
 for address in [mu,bar]:s['sh'][address]=scalar(D,19,-37,True)
 c=[radix,data_dest,HIGH,inverse,mapped_base,C,Z,CP,V,mu,bar]
 for i,value in enumerate(c):s['nat'][2200+i]=value
 return s,h,g

cases=[];pcs=set();controls=[];sample=None
for enabled,nonreal,layer,color,zero in [(True,True,2,1,False),(False,False,0,10,True),
 (True,False,3,0,True),(False,True,H-1,0,False)]:
 s,h,g=ready(enabled,nonreal,layer,color,zero);old=copy.deepcopy(s)
 ticks,covered,peak=execute(COMBINED,s,B,5_000_000,D,1)
 assert s['pc']==END and s['nat'][1640:1651]==[radix,data_dest,HIGH,inverse,mapped_base,C,Z,CP,V,mu,bar]
 z=scalar(D);one=scalar(D,1)
 kernels=[[(g[1],False)]+[z]*(N-1),[(-h[0],False)]+[z]*(N-1),
  [(h[1]*g[0]+h[0]*g[1],False)]+[z]*(N-1),[one]+[z]*(N-1),[one]+[z]*(N-1),[z]*N]
 omega=Poly(D,{1:1})**(D//N)
 bank=[(omega**i,False)for i in range(N)]
 for kernel in kernels:bank+=direct_dft(omega,kernel)
 assert [s['sh'][C+i]for i in range(7*N)]==bank
 assert [s['sh'][V+i]for i in range(7*N)]==[(value.conjugate(),False)for value,_ in bank]
 _,_,buckets=reference(enabled);W=buckets[layer]
 ids=[i for i,c in enumerate(greedy(W))if c==color]
 chosen=[W[i]for i in ids]
 borrowed=[i for i in range(radix)if i not in(0,1)][:G]
 def coordinate(p):return p if p<1 else borrowed[p-2]if p<2+G else 1+p-2-G
 physical=[[coordinate(d),coordinate(src),c]for d,src,c in chosen]
 assert s['nat'][894]==len(physical)
 assert [[s['nh'][mapped_base+3*i+f]for f in range(3)]for i in range(len(physical))]==physical
 def coefficient(pointer):
  if C<=pointer<C+7*N:return bank[pointer-C][0]
  if Z<=pointer<Z+7*N:return -bank[pointer-Z][0]
  assert CP<=pointer<CP+6
  return scalar(D,[1,-1,F(1,N),F(-1,N),F(5,4),F(4,5)][pointer-CP])[0]
 original=[old['sh'][data_source+i]for i in range(radix)];want=copy.deepcopy(original)
 for dest,source,pointer in physical:
  left,right=original[dest],original[source];tag=left[1]or right[1]
  want[dest]=(left[0]+coefficient(pointer)*right[0],tag);want[source]=(right[0],tag)
 phi=[s['nh'][inverse+i]for i in range(radix)]
 assert sorted(phi)==list(range(radix))
 assert [s['sh'][HIGH+i]for i in range(radix)]==want
 assert [s['sh'][data_dest+i]for i in range(radix)]==[want[phi[i]]for i in range(radix)]
 assert [s['sh'][data_source+i]for i in range(radix)]==original
 assert s['roots']==old['roots']and s['out']==old['out']and s['nat'][100:107]==old['nat'][100:107]
 for source in [axis_base,axis_base+radix,axis_base+2*radix,HB,GB,CONJBASE,CONJBASE+radix,CONJBASE+2*radix,CONJBASE+3*radix,CONJBASE+4*radix]:
  assert all(s['sh'][source+i]==old['sh'][source+i]for i in range(radix))
 for source in [axis_directory,CONJDIR]:assert all(s['nh'][source+i]==old['nh'][source+i]for i in range(2))
 assert s['sh'][0]==old['sh'][0]and s['sh'][900000]==old['sh'][900000]
 for pc in covered:
  pcs.add(pc)
 cases.append(dict(enabled=enabled,nonreal=nonreal,layer=layer,color=color,zeros=zero,
  selected=len(physical),sixCCalls=6*len(physical),continuousTicks=ticks,maximumWord=peak))
 if len(physical):sample=copy.deepcopy(old)
 print('continuous'+str(len(COMBINED)),len(cases),len(physical),ticks,flush=True)
assert sample is not None and any(not c['selected']for c in cases)

def reject(name,state,code_=COMBINED,budget=5_000_000):
 try:execute(code_,state,B,budget,D,1)
 except(AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
for name,bank,address in [('missing-original-invH','sh',HB+1),('missing-original-G','sh',GB+1),('missing-low-data','sh',data_source+1),('missing-conjugate-H','sh',CONJBASE+3*radix+1),
 ('missing-conjugate-G','sh',CONJBASE+4*radix+1),('missing-conjugate-directory','nh',CONJDIR),
 ('missing-master','sh',0),('missing-C-constant','sh',1)]:
 q=copy.deepcopy(sample);del q[bank][address];reject(name,q)
q=copy.deepcopy(sample);q['nat'][1453]=B+1;reject('initial-word-guard',q)
reject('charged-budget',copy.deepcopy(sample),budget=20)
q=copy.deepcopy(sample)
for a in [CONJBASE+3*radix,CONJBASE+3*radix+1,CONJBASE+4*radix,CONJBASE+4*radix+1]:q['sh'][a]=(q['sh'][a][0],True)
reject('prepared-conjugate-data-guard',q)
new=set(range(1286,1302))|{2668}|set(range(1302,1302+14))|{1302+166}|set(range(1302+167+763,1302+167+775))|{1302+1365}
assert new<=pcs
result=dict(status='PASS',instructions=2669,continuousInstructions=len(COMBINED),exactCases=len(cases),successfulCases=len(cases),
 negativeControls=controls,visitedPCs=len(pcs),unvisitedPCs=sorted(set(range(2669))-pcs),allNewCallerPCsVisited=True,cases=cases,
 scope='Actual physical1286 generic typed seed/height/chunk, charged16 universal header-copy instructions, then continuous1366 copy/generated packing/conjugate producer/six-C/scatter. Synthetic original and coefficientwise conjugate H/G/radix256 supplied at initial boundary are not canonical selected Retained/Metadata/Layout. No prefilled matching/permutation/count/conjugate spectrum/scales, and no host phase writes. Universal theorem derives selected Result from actual1286 and real retained pools. Only ordinary physical initial parameters, real low data and placements are input. Canonical allocator/empty-startup join/fullDFT remain open.',
 sha256={str(q.relative_to(ROOT)):hashlib.sha256(q.read_bytes()).hexdigest()for q in
 [ROOT/'lean/UniformSeedHighDataMatchingPreparation.lean',ROOT/'lean/UniformSeedConjugatePreservation.lean',ROOT/'verification/ExportSeedHighDataMatchingBytecode.lean',Path(__file__),
 ROOT/'scripts/uniform_seed_cyclotomic_engine.py',P/'programs.json',P/'spec.json']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k]for k in['status','exactCases','visitedPCs','negativeControls']},indent=2))
