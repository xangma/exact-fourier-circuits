"""Actual359: internal kappa/rho/scales + six C calls, exact tagged pair action.

Q[eta]/Phi_D (D4/8/12) data; Gaussian-rational mu makes every divisor's
norm rational for the versioned exact engine. Lean proves all complex mu.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib
import json
from uniform_seed_cyclotomic_engine import Poly, scalar, execute

ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/zero-free-pair-shear'
PROGRAMS=json.loads((P/'programs.json').read_text())
SPECS=json.loads((P/'spec.json').read_text())
CODE=PROGRAMS['joined'];B=100000
assert len(CODE)==359 and CODE[-1]==['halt']
assert all(i[0] not in ('branch','root','input','output','putnat') for i in CODE)
assert [j for j,i in enumerate(CODE) if i[0]=='fdiv']==[11,15]


def relocate(ins,base,end):
    op,*a=ins
    if op=='halt':return ['jump',end]
    if op=='jump':a[0]+=base
    if op=='branch':a[2]+=base;a[3]+=base
    return [op,*a]


# Physical chronology: two five-diagonal/three-Hadamard blocks, not bare C.
for b in [18,188]:
    for local in [10,60,110]:
        start=b+local
        assert CODE[start:start+40]==[relocate(i,start,start+40) for i in PROGRAMS['hadamard']]
        assert CODE[start+16:start+27]==[relocate(i,start+16,start+27) for i in PROGRAMS['C']]
    for local in [0,50,100,150,160]:
        start=b+local
        assert CODE[start+2:start+9]==[relocate(i,start+2,start+9) for i in PROGRAMS['diagonal']]


def fresh(D,mu,layout,flags,family):
    left,right=[(512,513),(777,222),(800,900),(900,800)][layout]
    co,bar=(600,600) if layout==2 and mu==mu.conjugate() else (600,601)
    s=dict(pc=0,nat=[(7*q+13)%101 for q in range(1630)],nh={17:31,B-1:7},
           sh={0:(Poly(D,{1:1}),False),B-1:scalar(D,17,-13,True)},
           sr={q:scalar(D,F(q-3,7),F(9-q,11),q%2) for q in range(120)},
           out={0:scalar(D,19,-17)[0]},roots=[D,1,12])
    a=scalar(D,F(1,2),F(1,2))[0]
    inv=scalar(D,1,-1)[0];imag=scalar(D,0,1)[0]
    for j,v in {1:a,2:a.conjugate(),3:inv,4:imag,5:imag*inv}.items():s['sh'][j]=(v,False)
    s['sh'][co]=(mu,False);s['sh'][bar]=(mu.conjugate(),False)
    if family=='zero':u=Poly(D);v=Poly(D)
    elif family=='cancel':v=Poly(D,{1:1})+scalar(D,F(3,7),F(-2,5))[0];u=-(mu*v)
    else:u=Poly(D,{1:1})+scalar(D,F(-7,11),F(3,13))[0];v=Poly(D,{2:1})+scalar(D,F(2,3),F(-1,5))[0]
    u=(u,flags[0]);v=(v,flags[1]);s['sh'][left]=u;s['sh'][right]=v
    for j in [left+1,left+2,left+3,right+2,right+3]:
        if j not in (left,right,co,bar):s['sh'][j]=scalar(D,j,-j,True)
    for q,value in {1620:left,1621:right,1622:co,1623:bar}.items():s['nat'][q]=value
    assert s['nat'][1624]!=0
    return s,left,right,co,bar,u,v


cases=[];covered=set()
for D in [4,8,12]:
    for spec in SPECS:
        mu=scalar(D,F(spec['reNum'],spec['reDen']),F(spec['imNum'],spec['imDen']))[0]
        for layout in range(4):
            for flags in [(False,False),(False,True),(True,False),(True,True)]:
                for family in ['mixed','zero','cancel']:
                    s,left,right,co,bar,u,v=fresh(D,mu,layout,flags,family);old=deepcopy(s)
                    ticks,pcs,peak=execute(CODE,s,B,359,D)
                    assert ticks==359 and s['pc']==358 and peak<=B
                    joined=u[1] or v[1]
                    assert s['sh'][left]==(u[0]+mu*v[0],joined)
                    assert s['sh'][right]==(v[0],joined)
                    if family=='cancel':assert s['sh'][left]==scalar(D,dep=joined)
                    if not mu.c:assert s['sh'][left]==(u[0],joined) and s['sh'][right]==(v[0],joined)
                    assert s['nh']==old['nh'] and s['out']==old['out'] and s['roots']==old['roots']
                    assert all(s['sh'][q]==value for q,value in old['sh'].items() if q not in (left,right))
                    assert set(s['sh'])==set(old['sh'])
                    assert all(s['nat'][q]==old['nat'][q] for q in range(1630) if q not in (0,1,2,1624))
                    assert all(s['sr'][q]==old['sr'][q] for q in range(8,120) if not 100<=q<110)
                    assert s['nat'][100:107]==old['nat'][100:107]
                    k=scalar(D,1)[0]+mu*mu.conjugate();rho=mu-k
                    assert k.c and rho.c
                    assert s['sr'][104]==(scalar(D,F(5,4))[0]*k.inverse(),False)
                    assert s['sr'][105]==(scalar(D,F(4,5))[0]*k,False)
                    assert s['sr'][108]==(scalar(D,F(5,4))[0]*rho.inverse(),False)
                    assert s['sr'][109]==(scalar(D,F(4,5))[0]*rho,False)
                    covered.update(pcs)
                    cases.append(dict(D=D,mu=spec,layout=layout,flags=flags,family=family,ticks=ticks,
                                      sharedCoefficientAddress=co==bar))

controls=[]
mu=scalar(12,F(1,2),F(1,3))[0]

def reject(name,s,code=CODE,budget=359):
    try:execute(code,s,B,budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')

for name,cell in [('missing-mu',600),('missing-conjugate',601),('missing-I',4),('missing-H-post',5)]:
    s,*_=fresh(12,mu,0,(True,True),'mixed');del s['sh'][cell];reject(name,s)
for name,index in [('missing-left',0),('missing-right',1)]:
    s,l,r,*_=fresh(12,mu,0,(True,True),'mixed');del s['sh'][[l,r][index]];reject(name,s)
for cell in [600,601]:
    s,*_=fresh(12,mu,0,(True,False),'mixed');s['sh'][cell]=(s['sh'][cell][0],True)
    reject('unprepared-coefficient-'+str(cell),s)
s,*_=fresh(12,scalar(12,1)[0],0,(True,False),'mixed');s['sh'][601]=scalar(12)
reject('wrong-conjugate-zero-rho',s)
s,*_=fresh(12,mu,0,(True,False),'mixed');s['nat'][1620]=B+1;reject('initial-word-guard',s)
s,*_=fresh(12,mu,0,(True,False),'mixed');reject('charged-budget',s,budget=358)
mutant=deepcopy(CODE);mutant[2]=['jump',3]
s,*_=fresh(12,mu,0,(True,False),'mixed');reject('omitted-data-address-install',s,mutant)
# An alias violates the explicit distinct-data contract; bytecode is not claimed
# to dynamically reject it. Likewise deleting a fixed diagonal changes action.
diagnostics=[]
s,l,r,co,bar,u,v=fresh(12,mu,0,(True,False),'mixed');s['nat'][1621]=l
execute(CODE,s,B,359,12)
assert s['sh'][l]!=(u[0]+mu*v[0],True)
diagnostics.append('data-alias-contract-necessary')
mutant=deepcopy(CODE);mutant[68]=['jump',70]
s,l,r,co,bar,u,v=fresh(12,mu,0,(True,False),'mixed');execute(mutant,s,B,359,12)
assert s['sh'][l]!=(u[0]+mu*v[0],True)
diagnostics.append('omitted-minus-three-diagonal-changes-action')
assert covered==set(range(359))
result=dict(status='PASS',instructions=359,exactCases=len(cases),chargedSteps=sum(c['ticks'] for c in cases),
            all359PCsVisited=True,sixPhysicalCCalls=True,negativeControls=controls,contractDiagnostics=diagnostics,cases=cases,
            arithmetic='Exact Q[eta]/Phi_D,D4/8/12; Gaussian-rational mu/conj and divisors, general cyclotomic tagged data. Versioned engine checks every inverse product. No floats/root requests. Lean theorem covers arbitrary complex mu.',
            contracts=dict(actualSources=True,actualStartupConstantValues=True,disjointData=True,
                           legalSharedCoefficientAddress=True,initialSelectedStartup=False,matchingLoop=False),
            scope='Actual359 internally computes kappa/rho/four scales then literal two three-C words. Zero mu still executes six C calls and OR tags. Dirty scratch/tails and readonly banks retained; no free scales/helper-header/action premise, no matching/global saving claim.',
            sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [P/'programs.json',P/'spec.json',ROOT/'verification/ExportZeroFreePairShearBytecode.lean',
                     Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','exactCases','chargedSteps','all359PCsVisited','sixPhysicalCCalls','negativeControls','contractDiagnostics']},indent=2))
