"""Actual literal1136 matching forward + generated matching inverse.

Matching55 and Packing137 generate the entry geometry in the diagnostics. The
1136 theorem begins at that physical packed entry; it does not charge a joined
producer-to-entry driver. Fresh K0 cases use genuine Lean cross/color syntax,
with generic prepared banks, not a selected-axis startup or whole six-phase DAG.
Exact Q[eta]/Phi_D arithmetic (D=4,12); no floating point or new root requests.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import json,hashlib
from uniform_seed_cyclotomic_engine import Poly,scalar,execute
ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'logs/uniform-bytecode/six-c-dirty-replay'
programs=json.loads((HERE/'programs.json').read_text())
SPEC=json.loads((HERE/'spec.json').read_text())
code=programs['joined'];B=30000
assert len(code)==1136 and code[-1]==['halt']
assert not any(i[0] in ['root','input','output'] for i in code)
def relocate(ins,base,end):
 op,*args=ins
 if op=='halt':return ['jump',end]
 if op=='jump':args[0]+=base
 if op=='branch':args[2]+=base;args[3]+=base
 return [op,*args]
for name,start,end in [('forward',12,434),('inverse',452,1135)]:
 assert code[start:end]==[relocate(ins,start,end) for ins in programs[name]]
assert code[0]==['lit',3000,0]
NW={i[1] for i in code if i[0] in ['lit','add','sub','mul','div','mod','getnat']}
SW={i[1] for i in code if i[0] in ['rat','getscalar','fadd','fsub','fmul','fdiv']}
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

P=CP;PACKED=DEST
INVERSE_PACKED,FORWARD_UNPACK=2000,14000
cases=[];covered=set();allsteps=0

def prepare(spec,D,pattern):
 s,_,original,forward,_,_,_,_=fresh(spec,D,pattern)
 r,M=spec['radix'],len(forward)
 s['nat'] += [(37*q+11)%191 for q in range(len(s['nat']),3051)]
 for j,v in enumerate([r,M,FWD,PERM,WIDTHS,MARKERS,AXIS]):s['nat'][840+j]=v
 s['pc']=0
 axisSteps,_,_=execute(programs['matchingAxis'],s,B,100000,D)
 for j,v in enumerate([1,AXIS,SUFFIX,STACK,SOURCE,PACKED]):s['nat'][600+j]=v
 s['nat'][637]=FORWARD_UNPACK;s['pc']=0
 packingSteps,_,_=execute(programs['packing'],s,B,100000,D)
 order=[q for left,right,_ in forward for q in [left,right]]+[j for j in range(r) if all(j not in [l,rr] for l,rr,_ in forward)]
 assert [s['nh'][FORWARD_UNPACK+j] for j in range(r)]==order
 assert [s['sh'][PACKED+j] for j in range(r)]==[original[q] for q in order]
 for j in range(r):s['sh'][INVERSE_PACKED+j]=scalar(D,100+j,-30-j,True)
 for j,v in enumerate([r,PACKED,SOURCE,FORWARD_UNPACK,FWD,C,T,P,V,MU,BAR,INV,PERM,WIDTHS,MARKERS,AXIS,SUFFIX,STACK,UNPACK,INVERSE_PACKED]):s['nat'][3001+j]=v
 s['pc']=0
 return s,original,forward,order,axisSteps+packingSteps

def check(spec,D,pattern,kind):
 global allsteps
 s,orig,forward,order,prep=prepare(spec,D,pattern);oldstate=deepcopy(s)
 K,r,M=spec['K'],spec['radix'],len(forward)
 # Generic +1/-1 constants and normalization use different source branches;
 # the Lean universal bound rather than a hand-derived timing formula is used.
 budget=660*r+153
 steps,pcs,peak=execute(code,s,B,budget,D)
 assert s['pc']==1135 and peak<=B
 want=deepcopy(orig)
 for left,right,_ in forward:
  flag=orig[left][1] or orig[right][1]
  want[left]=(orig[left][0],flag);want[right]=(orig[right][0],flag)
 assert [s['sh'][SOURCE+j] for j in range(r)]==want
 assert s['nat'][894]==M and s['nat'][3001:3021]==oldstate['nat'][3001:3021]
 assert s['nat'][100:107]==oldstate['nat'][100:107]
 assert s['out']==oldstate['out'] and s['roots']==oldstate['roots']
 writes={MU,BAR,*range(SOURCE,SOURCE+r),*range(PACKED,PACKED+r),*range(INVERSE_PACKED,INVERSE_PACKED+r)}
 assert all(s['sh'][q]==v for q,v in oldstate['sh'].items() if q not in writes)
 assert [[s['nh'][FWD+3*i+j] for j in range(3)] for i in range(M)]==forward
 assert all(s['nat'][q]==v for q,v in enumerate(oldstate['nat']) if q not in NW)
 assert all(s['sr'][q]==v for q,v in oldstate['sr'].items() if q not in SW)
 assert [s['nh'][FORWARD_UNPACK+j] for j in range(r)]==order
 covered.update(pcs);allsteps+=steps
 cases.append(dict(name=spec['name'],D=D,pattern=pattern,kind=kind,pairs=M,radix=r,preparationTicks=prep,ticks=steps,budget=budget))

for K in SPEC['K']:
 for M in SPEC['pairs']:
  for tail in SPEC['tails']:
   for pattern in SPEC['patterns']:
    for D in SPEC['fields']:check(generic(K,M,tail,pattern),D,pattern,'genericMatching')
for spec in SPEC['typedCases']:
 for pattern in [0,1]:check(spec,4,pattern,'freshTypedCrossColorSubset')
controls=[]
def reject(name,s,program=code,budget=2000):
 try:execute(program,s,B,budget,12)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name)
base=generic(3,1,3,3)
for name,bank,cell in [('missing-forward-row','nh',FWD+2),('missing-packing-inverse','nh',FORWARD_UNPACK),('missing-conjugate','sh',V),('missing-H-constant','sh',4)]:
 s,*_=prepare(base,12,0);del s[bank][cell];reject(name,s,budget=20000)
s,*_=prepare(base,12,0);s['sh'][C]=(s['sh'][C][0],True);reject('prepared-multiply-guard',s,budget=20000)
s,*_=prepare(base,12,0);s['nat'][3003]=B+1;reject('word-guard',s)
s,*_=prepare(base,12,0);reject('charged-budget',s,budget=10)
s,*_=prepare(base,12,0);mutant=deepcopy(code);mutant[0]=['jump',1];reject('mutated-zero-setup',s,mutant,budget=20000)
result=dict(status='PASS',instructions=1136,exactCases=len(cases),steps=allsteps,
 reachablePCs=len(covered),unvisitedPCs=sorted(set(range(1136))-covered),negativeControls=controls,
 provenance='Fresh literal1136 and Lean K0 typed cross/color export. Actual Matching55+Packing137 generate the entry permutation, inverse and packed data in each trace. Typed logical cases have generic prepared banks, not giant selected startup inputs.',
 contracts='All generic and fresh typed cases satisfy matching/in-range, ForwardLeaf, contiguous SourceReady and ordinary disjoint allocation/Layout. Producer diagnostics use real bytecode, but the1136 theorem entry is the already produced packed state, not a continuously charged Matching/Packing/1136 driver.',
 scope='execution_numeric proves original-coordinate matching numeric restoration using actual six-C forward/inverse loops, internally generated inverse rows/axis/packing; exact traces also verify conservative OR flags, tails and external frames.',
 open='Descending depth/color controller, output broadcasts and full six-phase dirty cross replay remain open. No stronger UniformDFT theorem.',
 unreachableReason='ForwardLeaf has unsigned prepared references, excluding forward negative-pointer branch41..45. Its inverse prepared pointers lie in the negative bank, excluding inverse generic positive-pointer branch736..739. All other PCs reached.',
 cases=cases,
 sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [
 HERE/'programs.json',HERE/'spec.json',Path(__file__),
 ROOT/'verification/ExportSixCDirtyReplayBytecode.lean',ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(HERE/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['cases','sha256']},indent=2))
