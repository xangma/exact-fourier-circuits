"""Literal422: generated count/read pointers, real six-C shears, inverse scatter.

Generic physical matching rows and genuine permutation tables; no full selected
startup witness. Exact Q[eta]/Phi_D using the versioned engine, no floats.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib
import json
from uniform_seed_cyclotomic_engine import Poly, scalar, execute

ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/packed-matching-shear'
PROGRAMS=json.loads((P/'programs.json').read_text())
SPEC=json.loads((P/'spec.json').read_text())
CODE=PROGRAMS['joined'];B=20000
assert len(CODE)==422 and CODE[-1]==['halt']


def relocate(ins,base,end):
    op,*args=ins
    if op=='halt':return ['jump',end]
    if op=='jump':args[0]+=base
    if op=='branch':args[2]+=base;args[3]+=base
    return [op,*args]


for name,start,end in [('rowLoader',14,39),('sixC',44,403),('scatter',409,421)]:
    assert CODE[start:end]==[relocate(ins,start,end) for ins in PROGRAMS[name]]
assert CODE[4]==['add',1664,894,1663]
assert not any(i[0] in ['root','input','output','putnat'] for i in CODE)
NAT_WRITES={ins[1] for ins in CODE if ins[0] in ['lit','add','sub','mul','div','mod','getnat']}
SCALAR_WRITES={ins[1] for ins in CODE if ins[0] in ['rat','getscalar','fadd','fsub','fmul','fdiv']}


def fresh(D,K,M,tail,layout,pattern,flags,family):
    L=2*M+tail
    packed,dest=[(256,1000),(1000,256)][layout]
    C,T,Pc,V,mu,bar=32,40,48,64,80,81
    inv,rows=5000,6000
    # Rotation is non-involutive for most lengths; this is the genuine scatter
    # map packed ordinal -> original ordinal, never a gather substitution.
    phi=[(i+(2 if L>3 else 1))%L for i in range(L)] if L else []
    s=dict(pc=0,nat=[(13*q+17)%97 for q in range(2150)],nh={18:31,B-1:7},
           sh={0:(Poly(D,{1:1}),False),B-1:scalar(D,17,-13,True)},
           sr={q:scalar(D,F(q+3,11),F(2-q,13),q%2) for q in range(120)},
           out={0:scalar(D,19,-17)[0]},roots=[D,1,12])
    a=scalar(D,F(1,2),F(1,2))[0];I=scalar(D,0,1)[0];ainv=scalar(D,1,-1)[0]
    for j,v in {1:a,2:a.conjugate(),3:ainv,4:I,5:I*ainv}.items():s['sh'][j]=(v,False)
    bank=[scalar(D,F(1,2),F(1,3))[0],scalar(D)[0],scalar(D,-2,1)[0]]
    for j,value in enumerate(bank):
        s['sh'][C+j]=(value,False);s['sh'][T+j]=(-value,False);s['sh'][V+j]=(value.conjugate(),False)
    constants=[1,-1,F(1,2**K),-F(1,2**K),F(5,4),F(4,5)]
    for j,value in enumerate(constants):s['sh'][Pc+j]=scalar(D,value)
    choices=[('p',i) for i in range(3)]+[('n',i) for i in range(3)]+[('c',i) for i in range(6)]
    labels=[choices[(i+2*pattern)%len(choices)] for i in range(M)]
    coeff=[];cost=0
    for i,(kind,index) in enumerate(labels):
        if kind=='p':pointer=C+index;value=bank[index];runtime=10
        elif kind=='n':pointer=T+index;value=-bank[index];runtime=12
        else:pointer=Pc+index;value=scalar(D,constants[index])[0];runtime=9
        coeff.append(value);cost+=376+runtime
        # The data orientation is the actual matching's printed dst/src order.
        for f,v in enumerate([phi[2*i],phi[2*i+1],pointer]):s['nh'][rows+3*i+f]=v
    original=[]
    for i in range(L):
        if family=='zero':value=Poly(D)
        elif family=='cancel' and i<2*M:
            right=Poly(D,{1:1})+scalar(D,F(3,7),F(-2,5))[0]
            value=right if i%2 else -(coeff[i//2]*right)
        else:value=Poly(D,{1+i%3:1})+scalar(D,F(i-7,11),F(9-i,13))[0]
        tagged=(value,flags[i%2]);original.append(tagged);s['sh'][packed+i]=tagged
        s['sh'][dest+i]=scalar(D,100+i,-300-i,True);s['nh'][inv+i]=phi[i]
    # Genuine dirty coefficient temporaries and ordinary tails.
    s['sh'][mu]=scalar(D,97,-61,True);s['sh'][bar]=scalar(D,-71,83,True)
    for q in [packed-1,packed+L,dest-1,dest+L]:s['sh'][q]=scalar(D,q,-q,True)
    params=[L,packed,dest,inv,rows,C,T,Pc,V,mu,bar]
    for j,value in enumerate(params):s['nat'][1640+j]=value
    s['nat'][894]=M
    expected=deepcopy(original)
    for i,value in enumerate(coeff):
        u,v=original[2*i:2*i+2];tag=u[1] or v[1]
        expected[2*i]=(u[0]+value*v[0],tag);expected[2*i+1]=(v[0],tag)
    assert 2*M<=L and C+3<=T and T+3<=Pc and Pc+6<=V and V+3<=mu<bar<min(packed,dest)
    assert packed+L<=dest or dest+L<=packed
    assert rows+3*M<=B and inv+L<=B
    return s,expected,original,phi,params,cost+9*L+21


cases=[];covered=set()
for D in SPEC['fields']:
 for K in SPEC['K']:
  for M in SPEC['pairs']:
   for tail in SPEC['tails']:
    for layout in range(2):
     for pattern in range(6):
      for flags in [[(False,False),(False,True),(True,False),(True,True)][pattern%4]]:
       for family in ['cancel' if pattern%2 else 'mixed']:
        s,want,original,phi,p,cost=fresh(D,K,M,tail,layout,pattern,flags,family);old=deepcopy(s)
        ticks,pcs,peak=execute(CODE,s,B,cost,D)
        L,packed,dest,inv,rows,C,T,Pc,V,mu,bar=p
        assert ticks==cost and s['pc']==421 and peak<=B
        assert ticks<=388*M+9*L+21<=203*L+21
        for i in range(L):
            assert s['sh'][packed+i]==want[i] and s['sh'][dest+phi[i]]==want[i]
            if i>=2*M:assert want[i]==original[i]
        assert s['nh']==old['nh'] and s['out']==old['out'] and s['roots']==old['roots']
        written={mu,bar,*range(packed,packed+2*M),*range(dest,dest+L)}
        assert all(s['sh'][q]==value for q,value in old['sh'].items() if q not in written)
        assert set(s['sh'])==set(old['sh'])
        assert all(s['nat'][q]==old['nat'][q] for q in range(2150) if q not in NAT_WRITES)
        assert all(s['sr'][q]==old['sr'][q] for q in range(120) if q not in SCALAR_WRITES)
        assert s['nat'][894]==M and s['nat'][100:107]==old['nat'][100:107]
        covered.update(pcs)
        cases.append(dict(D=D,K=K,pairs=M,tail=tail,layout=layout,pattern=pattern,flags=flags,family=family,ticks=ticks))

controls=[]

def reject(name,s,code=CODE,budget=2000):
    try:execute(code,s,B,budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')

# Each missing producer/load bank must really be read along the executed path.
for name,cell in [('missing-coefficient-pointer',6002),('missing-positive',32),('missing-conjugate',64),('missing-data',256),('missing-inverse',5000),('missing-H-I',4)]:
    s,*_=fresh(12,1,1,1,0,0,(True,False),'mixed')
    del s['nh' if cell in [6002,5000] else 'sh'][cell];reject(name,s)
s,*_=fresh(12,1,1,1,0,0,(True,False),'mixed');s['sh'][32]=(s['sh'][32][0],True);reject('coefficient-prepared-guard',s)
s,*_=fresh(12,1,1,1,0,0,(True,False),'mixed');s['nat'][1641]=B+1;reject('initial-word-guard',s)
s,*_=fresh(12,1,1,1,0,0,(True,False),'mixed');reject('charged-budget',s,budget=100)
mutant=deepcopy(CODE);mutant[4]=['jump',5]
s,*_=fresh(12,1,1,1,0,0,(True,False),'mixed');reject('omitted-generated-count-load',s,mutant)
mutant=deepcopy(CODE);mutant[39]=['jump',40]
s,*_=fresh(12,1,1,1,0,0,(True,False),'mixed');reject('omitted-pair-address-setup',s,mutant)
assert covered==set(range(422))
result=dict(status='PASS',instructions=422,exactCases=len(cases),chargedSteps=sum(c['ticks'] for c in cases),
            all422PCsVisited=True,sixPhysicalCCallsPerProducedRow=True,negativeControls=controls,
            contracts=dict(genericPhysicalRows=True,actualCountRead894=True,actualCoefficientPointerRead=True,
                           actualPermutationTable=True,ordinaryLayout=True,preparedConjugateBank=True,
                           initialSelectedStartup=False,typedCrossRows=False),
            scope='Continuous422 internally loads generated row count and coefficient pointers, derives mu/conj and four nonzero scales, executes six physical C calls per row, then actual inverse scatter. Exact tagged data; dirty scratch/tails/non-involutive permutations. No full selected-axis startup or fast global scheduler claim.',
            arithmetic='Exact Q[eta]/Phi_D,D4/8/12,Gaussian-rational coefficients/divisors; arbitrary cyclotomic tagged data. Every inverse product checked; no floats/root requests.',
            cases=cases,sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
             [P/'programs.json',P/'spec.json',ROOT/'verification/ExportPackedMatchingShearBytecode.lean',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['cases','sha256']},indent=2))
