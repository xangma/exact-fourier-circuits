"""Literal683: forward rows -> inverse36 -> axis55 -> packing137 -> sixC422.

Exact cyclotomic data, Gaussian-rational prepared coefficients; no floats. Typed
cross cases use actual Lean depth/color-selected syntax, with generic physical
prepared coefficient banks. They are not selected-axis startup witnesses.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json
from uniform_seed_cyclotomic_engine import Poly,scalar,execute
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/six-c-inverse-matching'
PROGS=json.loads((P/'programs.json').read_text());SPEC=json.loads((P/'spec.json').read_text())
CODE=PROGS['joined'];B=30000
assert len(CODE)==683 and CODE[-1]==['halt']

def relocate(ins,base,end):
    op,*args=ins
    if op=='halt':return ['jump',end]
    if op=='jump':args[0]+=base
    if op=='branch':args[2]+=base;args[3]+=base
    return [op,*args]
for name,start,end in [('inverse',7,43),('matchingAxis',50,105),('packing',112,249),('matchingShear',260,682)]:
    assert CODE[start:end]==[relocate(ins,start,end) for ins in PROGS[name]]
assert CODE[1]==['add',980,894,2418] and CODE[259]==['add',1650,2417,2418]
assert not any(ins[0] in ['root','input','output'] for ins in CODE)
NW={i[1] for i in CODE if i[0] in ['lit','add','sub','mul','div','mod','getnat']}
SW={i[1] for i in CODE if i[0] in ['rat','getscalar','fadd','fsub','fmul','fdiv']}
C,T,CP,V,MU,BAR=32,128,224,256,320,321
FWD,INV,PERM,WIDTHS,MARKERS,AXIS,SUFFIX,STACK,UNPACK=5000,6000,7000,8000,9000,10000,11000,12000,13000
SOURCE,DEST=512,1000

def pointer(c,K):
    if c[0]=='prepared':assert c[2] is False;return C+c[1]
    q=F(c[1],c[2]);assert q in [1,-1,F(1,2**K)]
    return CP+(0 if q==1 else 1 if q==-1 else 2)
def invpointer(c,K):
    if c[0]=='prepared':return T+c[1]
    q=F(c[1],c[2]);return CP+(1 if q==1 else 0 if q==-1 else 3)
def value(c,bank,D):
    return bank[c[1]] if c[0]=='prepared' else scalar(D,F(c[1],c[2]))[0]

def fresh(spec,D,pattern):
    K,R,r=spec['K'],spec['R'],spec['radix'];rows=spec['logical'];M=len(rows)
    assert r>=2 and 2*M<=r and SOURCE+r<=DEST and C+R<=T and V+R<=MU
    assert len({q for l,r,_ in rows for q in (l,r)})==2*M
    assert all(0<=l<r0 and 0<=r1<r0 and l!=r1 for l,r1,_ in rows for r0 in [r])
    s=dict(pc=0,nat=[(17*q+29)%113 for q in range(2430)],nh={17:31,B-1:9},
        sh={0:(Poly(D,{1:1}),False),B-1:scalar(D,23,-19,True)},
        sr={q:scalar(D,F(q+1,17),F(5-q,19),q%2) for q in range(120)},
        out={0:scalar(D,19,-17)[0]},roots=[D,1,12])
    A=scalar(D,F(1,2),F(1,2))[0];I=scalar(D,0,1)[0];AI=scalar(D,1,-1)[0]
    for j,v in {1:A,2:A.conjugate(),3:AI,4:I,5:I*AI}.items():s['sh'][j]=(v,False)
    choices=[scalar(D,F(1,2),F(1,3))[0],Poly(D),scalar(D,-2,1)[0]]
    bank=[choices[i%3] for i in range(R)]
    for j,v in enumerate(bank):s['sh'][C+j]=(v,False);s['sh'][T+j]=(-v,False);s['sh'][V+j]=(v.conjugate(),False)
    constants=[1,-1,F(1,2**K),-F(1,2**K),F(5,4),F(4,5)]
    for j,v in enumerate(constants):s['sh'][CP+j]=scalar(D,v)
    original=[(Poly(D,{1+i%3:1})+scalar(D,F(i-3,7),F(11-i,13))[0],bool((i+pattern)%3)) for i in range(r)]
    # Include exact inverse cancellation with arbitrary conservative tags.
    if pattern%2:
        for left,right,c in rows:
            original[left]=(value(c,bank,D)*original[right][0],original[left][1])
    for i,v in enumerate(original):s['sh'][SOURCE+i]=v;s['sh'][DEST+i]=scalar(D,100+i,-300-i,True)
    for q in [MU,BAR,SOURCE-1,SOURCE+r,DEST-1,DEST+r]:s['sh'][q]=scalar(D,q,-q,True)
    forward=[[l,rr,pointer(c,K)] for l,rr,c in rows]
    inverse=[[l,rr,invpointer(c,K)] for l,rr,c in reversed(rows)]
    if 'forward' in spec:assert spec['forward']==forward and spec['inverse']==inverse
    for i,row in enumerate(forward):
        for j,v in enumerate(row):s['nh'][FWD+3*i+j]=v
    # Dirty output banks must be initialized by real execution, not fixtures.
    for base,count in [(INV,3*M),(PERM,r),(WIDTHS,r),(MARKERS,r),(AXIS,4),(SUFFIX,2),(STACK,9),(UNPACK,r)]:
        for j in range(count):s['nh'][base+j]=(base+j+pattern)%97
    params=[FWD,INV,PERM,WIDTHS,MARKERS,AXIS,SUFFIX,STACK,UNPACK,SOURCE,DEST,r,C,T,CP,V,MU,BAR]
    for j,v in enumerate(params):s['nat'][2400+j]=v
    s['nat'][894]=M
    expect=deepcopy(original)
    for left,right,c in reversed(rows):
        u,v=expect[left],expect[right];tag=u[1] or v[1]
        expect[left]=(u[0]-value(c,bank,D)*v[0],tag);expect[right]=(v[0],tag)
    order=[q for l,rr,c in inverse for q in [l,rr]]+[j for j in range(r) if all(j not in [l,rr] for l,rr,_ in rows)]
    widths=[2]*M+[1]*(r-2*M)
    assert sorted(order)==list(range(r)) and sum(widths)==r
    mc=sum(388 if c[0]=='prepared' else 385 for _,_,c in rows)
    budget=mc+33*M+239*r+101
    assert budget<=450*r+101
    return s,expect,original,forward,inverse,order,widths,budget

def generic(K,M,tail,pattern):
    r=max(2,2*M+tail);order=list(range(r));rot=(pattern+1)%r
    order=order[rot:]+order[:rot]
    if pattern%2:order=order[::-1]
    choices=[['rational',1,1],['rational',-1,1],['rational',1,2**K]]+[['prepared',j,False] for j in range(3)]
    rows=[[order[2*i],order[2*i+1],choices[(i+pattern)%len(choices)]] for i in range(M)]
    return dict(name=f'generic-K{K}-M{M}-tail{tail}-pattern{pattern}',K=K,R=3,radix=r,logical=rows)

cases=[];covered=set();pcCounts={};noninvolutive=0

def check(spec,D,pattern,kind):
    global noninvolutive
    s,want,orig,forward,inverse,order,widths,budget=fresh(spec,D,pattern);old=deepcopy(s)
    steps,pcs,peak=execute(CODE,s,B,budget,D)
    r=spec['radix'];M=len(forward)
    assert s['pc']==682 and steps<=budget and peak<=B
    for i in range(r):
        assert s['sh'][SOURCE+i]==want[i]
        assert s['sh'][DEST+i]==want[order[i]]
        assert s['nh'][PERM+i]==s['nh'][UNPACK+i]==order[i]
        assert s['nh'][MARKERS+i]==int(i in order[:2*M])
    assert [s['nh'][WIDTHS+i] for i in range(r-M)]==widths
    assert [s['nh'][AXIS+i] for i in range(4)]==[r-M,WIDTHS,r,PERM]
    assert [[s['nh'][INV+3*i+j] for j in range(3)] for i in range(M)]==inverse
    assert [[s['nh'][FWD+3*i+j] for j in range(3)] for i in range(M)]==forward
    assert s['out']==old['out'] and s['roots']==old['roots'] and s['nat'][894]==M
    assert s['nat'][100:107]==old['nat'][100:107] and s['nat'][2400:2418]==old['nat'][2400:2418]
    scalarWrites={MU,BAR,*range(SOURCE,SOURCE+r),*range(DEST,DEST+r)}
    assert all(s['sh'][q]==v for q,v in old['sh'].items() if q not in scalarWrites)
    assert set(s['sh'])==set(old['sh'])
    natHeapWrites={*range(INV,INV+3*M),*range(PERM,PERM+r),*range(WIDTHS,WIDTHS+r),*range(MARKERS,MARKERS+r),*range(AXIS,AXIS+4),*range(SUFFIX,SUFFIX+2),*range(STACK,STACK+9),*range(UNPACK,UNPACK+r)}
    assert all(s['nh'][q]==v for q,v in old['nh'].items() if q not in natHeapWrites)
    assert set(s['nh'])==set(old['nh'])
    assert all(s['nat'][q]==v for q,v in enumerate(old['nat']) if q not in NW)
    assert all(s['sr'][q]==v for q,v in old['sr'].items() if q not in SW)
    if any(order[order[j]]!=j for j in range(r)):noninvolutive+=1
    covered.update(pcs)
    for pc,count in pcs.items():pcCounts[pc]=pcCounts.get(pc,0)+count
    cases.append(dict(name=spec['name'],kind=kind,D=D,pattern=pattern,pairs=M,radix=r,ticks=steps,budget=budget))

for K in SPEC['K']:
 for M in SPEC['pairs']:
  for tail in SPEC['tails']:
   for pattern in range(6):
    for D in SPEC['fields']:check(generic(K,M,tail,pattern),D,pattern,'genericMatching')
for spec in SPEC['typedCases']:
 for pattern in range(2):check(spec,4,pattern,'typedCrossColorSubset')

controls=[]
def rejects(name,state,code=CODE,budget=2000):
    try:execute(code,state,B,budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' unexpectedly accepted')
base=generic(3,1,2,0)
for name,heap,cell in [('missing-forward-field','nh',FWD+2),('missing-original-data','sh',SOURCE),('missing-conjugate','sh',V),('missing-H-I','sh',4)]:
    spec=generic(3,1,2,3 if heap=='sh' and cell==V else 0)
    s,*_=fresh(spec,12,0);del s[heap][cell];rejects(name,s)
s,*_=fresh(generic(3,1,2,3),12,0);s['sh'][T]=(s['sh'][T][0],True);rejects('prepared-coefficient-guard',s)
s,*_=fresh(base,12,0);s['nat'][2409]=B+1;rejects('initial-word-guard',s)
s,*_=fresh(base,12,0);rejects('charged-budget',s,budget=100)
s,*_=fresh(base,12,0);mutant=deepcopy(CODE);mutant[0]=['jump',1];rejects('mutated-zero-header-setup',s,mutant)
# Domain/matching remain real proof premises: deliberately unsupported rational
# q cannot enter ForwardLeaf, and overlapping endpoints invalidate Matching.
assert F(2,3) not in [1,-1,F(1,8)]
assert not len({0,1,1,2})==4
unusedPositiveBranch={284,285,286,287}
assert covered==set(range(683))-unusedPositiveBranch,sorted(set(range(683))-covered)
assert CODE[283]==['branch',2105,2101,284,288]
assert CODE[284:288]==[['sub',2112,2105,2100],['add',2112,2103,2112],['getscalar',72,2112],['jump',296]]
result=dict(status='PASS',instructions=683,exactCases=len(cases),chargedSteps=sum(c['ticks'] for c in cases),
 reachablePCsVisited=len(covered),all679InverseDomainPCsVisited=True,unusedPositiveBranchPCs=sorted(unusedPositiveBranch),
 unreachableReason="ForwardLeaf permits only unsigned prepared leaves, whose inverse addresses are in negativeT; rational inverses are in constantsP. The generic RowLoader positive branch has no valid inverse-domain entry. inverse_address_lower proves the address bound.",negativeControls=controls,nonInvolutiveCases=noninvolutive,
 counts=dict(generic=sum(c['kind']=='genericMatching' for c in cases),typed=sum(c['kind']=='typedCrossColorSubset' for c in cases)),
 contracts=dict(actualGeneratedInverseRows=True,actualGeneratedMatchingPermutation=True,actualGeneratedPackingInverse=True,
  actual894CountRead=True,ordinaryLayout=True,forwardLeafDomain=True,matchingAndInRange=True,
  typedCrossColorSubsets=True,genericPreparedCoefficientBanks=True,fullSelectedStartup=False,globalReverseChronology=False),
 arithmetic='Exact Q[eta]/Phi_D for D4/8/12; Gaussian-rational coefficients and verified nonzero scale inverses. Arbitrary tagged cyclotomic data. No floats/root requests.',
 scope='Fresh literal683 traces: inverse36 prints reversed/negated pointers; matching55 prints actual geometry; packing137 computes inverse/gathers; 422 performs six real C calls per row and scatters. Entire original-coordinate inverse action checked independently from logical coefficients, including N1/N>1, mu0, complex, exact cancellation, dirty tags/tails/nonidentity permutations. Typed cases are real Lean cross-DAG depth/color selected syntax with generic physical banks and ample ordinary layout, not actual selected-axis startup.',
 open='Whole reversed bucket/color driver, auxiliary scratch numeric restoration, recursive/tensor-saving scheduler and stronger UniformDFT theorem are not tested or proved here.',
 cases=cases,sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
  [P/'programs.json',P/'spec.json',ROOT/'verification/ExportSixCInverseMatchingBytecode.lean',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['cases','sha256']},indent=2))
