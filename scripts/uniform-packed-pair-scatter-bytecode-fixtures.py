"""Fresh continuous45 C-round→inverse-scatter; exact values and actual OR tags.

The optional Packing137 prefix computes the inverse bank from honest physical
width/permutation source tables. No generated inverse or transformed bank is
injected between helpers. This diagnostic is not a six-C/full-DFT execution.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib
import json
from uniform_seed_cyclotomic_engine import Poly, scalar, execute

ROOT = Path(__file__).resolve().parents[1]
P = ROOT/'logs/uniform-bytecode/packed-pair-scatter'
PROGRAMS = json.loads((P/'programs.json').read_text())
SPECS = json.loads((P/'spec.json').read_text())
CODE = PROGRAMS['joined']
B = 100000


def relocate(ins, base, end):
    op, *a = ins
    if op == 'halt':
        return ['jump', end]
    if op == 'jump':
        a[0] += base
    if op == 'branch':
        a[2] += base; a[3] += base
    return [op, *a]


assert len(CODE) == 45
assert CODE[5:28] == [relocate(i, 5, 28) for i in PROGRAMS['pairRound']]
assert CODE[32:44] == [relocate(i, 32, 44) for i in PROGRAMS['scatter']]
assert CODE[0] == ['lit',1607,0] and CODE[-1] == ['halt']
assert all(i[0] not in ('putnat','root','input','output') for i in CODE)


def fresh(D, spec, reverse, family, generated=False):
    L, M, phi = spec['L'], spec['M'], spec['permutation']
    assert 2*M <= L and sorted(phi) == list(range(L))
    assert spec['inverse'] == [phi.index(j) for j in range(L)]
    a, d = (1024,4096) if reverse else (4096,1024)
    b = 9500
    s = dict(pc=0,nat=[(7*q+13)%101 for q in range(1620)],nh={17:31,B-1:7},
             sh={0:(Poly(D,{1:1}),False),B-1:scalar(D,17,-13,True)},
             sr={q:scalar(D,F(q-3,7),F(9-q,11),q%2) for q in range(100)},
             out={0:scalar(D,19,-17)[0]},roots=[D,1,12])
    s['sh'][1]=scalar(D,F(1,2),F(1,2))
    s['sh'][2]=scalar(D,F(1,2),F(-1,2))
    eta=Poly(D,{1:1})
    values=[]
    for i in range(L):
        if family=='cancellation' and i<2*M:
            v=scalar(D,0,1,True) if i%2==0 else scalar(D,1,0,False)
        elif family=='zero':
            v=scalar(D,dep=i%2==0)
        elif family=='prepared':
            v=(eta**((5*i+1)%D),False)
        else:
            v=scalar(D,F(3*i-7,11),F(2*i+5,13),i%3!=0)
        values.append(v)
        s['sh'][a+i]=scalar(D,-i-31,23+i,True) if generated else v
        s['sh'][d+i]=v if generated else scalar(D,100+i,-13-i,True)
        if not generated:
            s['nh'][b+i]=phi[i]
    for q,v in {1600:L,1601:M,1602:a,1603:d,1604:b,1605:1,1606:2}.items():
        s['nat'][q]=v
    assert s['nat'][1607]!=0  # Both helper-ready headers/zero start stale.
    if generated:
        assert not reverse and L>0
        rows,widths,forward,suffix,stack=9000,9010,9100,9200,9210
        ws=[2]*M+[1]*(L-2*M)
        assert sum(ws)==L and rows+4<=suffix and forward+L<=suffix
        assert suffix+2<=stack and stack+9<=b and b+L<=B
        s['nh'].update({rows:len(ws),rows+1:widths,rows+2:L,rows+3:forward})
        s['nh'].update({widths+i:q for i,q in enumerate(ws)})
        s['nh'].update({forward+i:q for i,q in enumerate(phi)})
        for q,v in {600:1,601:rows,602:suffix,603:stack,604:d,605:a,637:b}.items():
            s['nat'][q]=v
    return s,a,d,b,values


def round_reference(D,values,M):
    # Independent sum/difference formulation of C, ordinary orientation.
    half=Poly(D,{0:F(1,2)}); imag=Poly(D,{D//4:1})
    w=list(values)
    for i in range(M):
        u,v=values[2*i],values[2*i+1]
        mean=half*(u[0]+v[0]);rotation=half*imag*(u[0]-v[0])
        flag=u[1] or v[1]
        w[2*i],w[2*i+1]=(mean+rotation,flag),(mean-rotation,flag)
    return w


def check(D,spec,s,old,a,d,packed,source,prefix=False):
    L,M,phi=spec['L'],spec['M'],spec['permutation']
    expected=round_reference(D,packed,M)
    assert [s['sh'][a+i] for i in range(L)]==expected
    assert [s['sh'][d+j] for j in range(L)]==[expected[phi.index(j)] for j in range(L)]
    assert [s['sh'][a+i] for i in range(2*M,L)]==packed[2*M:]
    assert s['sh'][0]==old['sh'][0] and s['sh'][1]==old['sh'][1] and s['sh'][2]==old['sh'][2]
    assert s['out']==old['out'] and s['roots']==old['roots']
    assert all(s['sh'][q]==v for q,v in old['sh'].items() if not a<=q<a+L and not d<=q<d+L)
    if not prefix:
        assert s['nh']==old['nh']
        assert all(s['nat'][q]==old['nat'][q] for q in range(1620)
                   if q not in {0,1,1280,1281,1282,1283,1284,1285,1286,1287,
                                1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1607})
        assert all(s['sr'][q]==old['sr'][q] for q in range(8,100) if q!=90)
    assert s['nat'][100:107]==old['nat'][100:107]
    assert [s['nh'][9500+i] for i in range(L)]==phi
    if source=='cancellation' and M and not prefix:
        assert s['sh'][d+phi[0]]==scalar(D,dep=True)
    if L==3 and spec['shift']==1 and not spec['reversed'] and source=='mixed':
        assert [expected[phi[j]] for j in range(L)]!=[expected[phi.index(j)] for j in range(L)]


cases,covered=[],set()
for D in [4,8,12]:
    for spec in SPECS:
        for reverse in [False,True]:
            for family in ['mixed','prepared','zero','cancellation']:
                s,a,d,b,values=fresh(D,spec,reverse,family)
                old=deepcopy(s)
                ticks,pcs,peak=execute(CODE,s,B,17*spec['M']+9*spec['L']+21,D)
                assert ticks==17*spec['M']+9*spec['L']+21 and s['pc']==44 and peak<=B
                check(D,spec,s,old,a,d,values,family)
                covered.update(pcs)
                cases.append(dict(D=D,L=spec['L'],M=spec['M'],shift=spec['shift'],reversed=spec['reversed'],
                                  reverseBanks=reverse,family=family,ticks=ticks,generatedInverse=False))

# The actual Packing137 prefix produces the very table and scalars consumed by45.
# Header/physical source rows are entry facts; there are no interphase host writes.
PREFIX=[relocate(i,0,137) for i in PROGRAMS['packing']]
PREFIX += [relocate(i,137,182) for i in CODE]+[['halt']]
for spec in SPECS:
    if not spec['L'] or spec['shift']!=1 or spec['reversed']:
        continue
    for family in ['mixed','cancellation']:
        D=12
        s,a,d,b,original=fresh(D,spec,False,family,generated=True)
        old=deepcopy(s)
        packed=[original[j] for j in spec['permutation']]
        ticks,pcs,peak=execute(PREFIX,s,B,213*spec['L']+20+17*spec['M']+9*spec['L']+22,D)
        assert s['pc']==182 and peak<=B
        check(D,spec,s,old,a,d,packed,family,prefix=True)
        cases.append(dict(D=D,L=spec['L'],M=spec['M'],shift=1,reversed=False,reverseBanks=False,
                          family=family,ticks=ticks,generatedInverse=True))

controls=[]
control=next(s for s in SPECS if s['L']==3 and s['M']==1 and s['shift']==1 and not s['reversed'])


def reject(name,s,code=CODE,budget=10000):
    try:
        execute(code,s,B,budget,12)
    except (AssertionError,KeyError):
        controls.append(name)
    else:
        raise AssertionError(name+' accepted')


for name,which in [('missing-diagonal',1),('missing-off-diagonal',2)]:
    s,*_=fresh(12,control,False,'cancellation');del s['sh'][which];reject(name,s)
s,a,d,b,_=fresh(12,control,False,'cancellation');del s['sh'][a+1];reject('missing-paired-source',s)
s,a,d,b,_=fresh(12,control,False,'cancellation');del s['sh'][a+2];reject('missing-tail-source',s)
s,a,d,b,_=fresh(12,control,False,'cancellation');del s['nh'][b+2];reject('missing-inverse',s)
s,*_=fresh(12,control,False,'cancellation');s['sh'][1]=(s['sh'][1][0],True);reject('prepared-multiply-guard',s)
s,*_=fresh(12,control,False,'mixed');s['nat'][1603]=B;reject('destination-word-overflow',s)
s,*_=fresh(12,control,False,'mixed');reject('charged-step-budget',s,budget=3)
s,*_=fresh(12,control,False,'mixed');s['nat'][1602]=B+1;reject('initial-word-guard',s)
mutant=deepcopy(CODE);mutant[4]=['jump',5]
s,*_=fresh(12,control,False,'mixed');reject('omitted-round-header-copy',s,mutant)
mutant=deepcopy(CODE);mutant[31]=['jump',32]
s,*_=fresh(12,control,False,'mixed');reject('omitted-scatter-inverse-copy',s,mutant)
assert covered==set(range(45))
result=dict(status='PASS',instructions=45,exactCases=len(cases),standaloneCases=sum(not c['generatedInverse'] for c in cases),
            generatedInverseCases=sum(c['generatedInverse'] for c in cases),chargedSteps=sum(c['ticks'] for c in cases),
            all45PCsVisited=True,negativeControls=controls,cases=cases,
            arithmetic='Exact Q[eta]/Phi_D for D4/8/12, no floats; no roots or division requested by joined code.',
            contracts=dict(ordinarySource=True,capacity=True,actualPermutation=True,actualCConstants=True,
                           generatedInverseProducerInPrefixCases=True,initialSelectedStartup=False,sixCExecution=False),
            scope='Continuous45 setup5→C-round23→setup4→scatter12→halt. Arbitrary/non-involutive inverse permutations, dirty destination, OR/cancellation flags, M0/unpaired tail. Generated-prefix cases run actual Packing137 then45 continuously from honest physical axis tables; no interphase host writes. No selected-axis startup or full/six-C Fourier execution claim.',
            sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [P/'programs.json',P/'spec.json',ROOT/'verification/ExportPackedPairScatterBytecode.lean',
                     Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','exactCases','standaloneCases','generatedInverseCases','chargedSteps','all45PCsVisited','negativeControls']},indent=2))
