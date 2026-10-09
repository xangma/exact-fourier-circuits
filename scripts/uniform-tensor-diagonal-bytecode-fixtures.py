"""Actual81 tensor monomial/diagonal traversal, exact values and flags.
Inputs are genuine physical prepared Axis banks with arbitrary present tagged
role arrays and true disjoint placement; no selected/full-FFT claim.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction
from itertools import product
import json,sys,random,hashlib
ROOT=Path(__file__).resolve().parents[1];BASE=ROOT/'logs/uniform-bytecode/operational-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,mul
programs=json.loads((BASE/'tensor-bytecode/programs.json').read_text())
specs=json.loads((BASE/'tensor-bytecode/specs.json').read_text())
B=100000;ROW,NSTACK,SOURCE,SSTACK,DEST=100,1000,2000,10000,12000

def make(spec,W,D,seed):
    rng=random.Random(seed);radices=spec['radices'];L=1
    for r in radices:L*=r
    s=dict(pc=0,nat=[rng.randrange(30) for _ in range(4600)],nh={3:17,B-1:7},
      sh={0:scalar(D,7,-3,True),B-1:scalar(D,-17,2,True)},
      sr={r:scalar(D,Fraction(r+1,13),Fraction(3-r,17),r%2) for r in range(140)},
      out={0:scalar(D,19,-11)[0]},roots=[4,1])
    coefs=[]
    for axis,(r,perm) in enumerate(zip(radices,spec['permutations'])):
        pb,cb=200+20*axis,500+20*axis
        values=[scalar(D,Fraction(3*j-2*axis+seed,7),Fraction(1+axis-j,11),False) for j in range(r)]
        if axis==0 and seed%2==0:values[0]=scalar(D)
        coefs.append(values)
        for j in range(r):s['nh'][pb+j]=perm[j];s['sh'][cb+j]=values[j]
        for field,value in enumerate([r,pb,cb]):s['nh'][ROW+3*axis+field]=value
    data=[[scalar(D,Fraction(7*j-3*i-11,19),Fraction(i+5*j+7,23),(i+j+seed)%2) for j in range(L)] for i in range(W)]
    for i in range(W):
      for j in range(L):s['sh'][SOURCE+i*L+j]=data[i][j];s['sh'][DEST+i*L+j]=scalar(D,-j-i,13,True)
    for j in range(len(radices)):
        s['sh'][SSTACK+j]=scalar(D,99,-77,True)
        for field in range(3):s['nh'][NSTACK+3*j+field]=37+field
    for reg,val in {4501:L,4502:SOURCE,4503:DEST,4504:len(radices),4505:ROW,4506:NSTACK,4507:SSTACK}.items():s['nat'][reg]=val
    return s,data,coefs,L

cases=[];covered=set()
for p in programs:
  W=p['W'];assert len(p['code'])==81
  for sid,spec in enumerate(specs):
    for D in (4,8,12):
      for seed in range(3):
        s,data,coefs,L=make(spec,W,D,seed);old=deepcopy(s)
        expected=W*(spec['treeCost']+20)+6
        ticks,pcs,peak=execute(p['code'],s,B,expected,D)
        assert ticks==expected and s['pc']==80 and peak<=B;covered.update(pcs)
        digits=list(product(*(range(r) for r in spec['radices'])))
        assert len(digits)==L
        for i in range(W):
          for j,z in enumerate(digits):
            ans=data[i][j]
            for axis,local in enumerate(z):ans=mul(coefs[axis][local],ans)
            target=spec['tensorPermutation'][j]
            assert s['sh'][DEST+i*L+target]==ans,(W,sid,D,seed,i,j)
        for addr,value in old['sh'].items():
          if not(SSTACK<=addr<SSTACK+len(spec['radices']) or DEST<=addr<DEST+W*L):assert s['sh'].get(addr)==value
        for addr,value in old['nh'].items():
          if not(NSTACK<=addr<NSTACK+3*len(spec['radices'])):assert s['nh'].get(addr)==value
        assert s['out']==old['out'] and s['roots']==old['roots']
        assert all(s['sr'][r]==value for r,value in old['sr'].items() if r>=2)
        assert all(s['nat'][r]==value for r,value in enumerate(old['nat']) if r>=20 and r not in (4500,4510,4511,4512,4513))
        cases.append(dict(W=W,spec=sid,D=D,seed=seed,ticks=ticks))
controls=[]

def reject(name,mutate,budget=None):
    s,_,_,_=make(specs[3],3,12,1);mutate(s)
    try:execute(programs[2]['code'],s,B,1000000 if budget is None else budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')
reject('missing-axis-row',lambda s:s['nh'].pop(ROW+1))
reject('missing-permutation',lambda s:s['nh'].pop(200))
reject('missing-prepared-coefficient',lambda s:s['sh'].pop(500))
reject('missing-present-input',lambda s:s['sh'].pop(SOURCE))
reject('prepared-multiplication-guard',lambda s:s['sh'].__setitem__(500,scalar(12,3,2,True)))
reject('word-address-guard',lambda s:s['nat'].__setitem__(4503,B+1))
reject('charged-budget-guard',lambda s:None,budget=1)
assert covered==set(range(81)),sorted(set(range(81))-covered)
result=dict(status='PASS',exactCases=len(cases),negativeControls=controls,coveredPCs=sorted(covered),
 contracts='True physical Rows/permutation/prepared-coefficient Banks, present W role arrays and valid disjoint Geometry. Generic mixed-radix Axis banks, not the full selected FFT cache. Small W1,2,3,5 specializations only; no astronomical fixed-W scalar materialization.',
 model='Exact Q[eta]/Phi_D, D4/8/12; no floating point, flags and retained banks checked exactly.',
 sourceHashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),BASE/'tensor-bytecode/programs.json',BASE/'tensor-bytecode/specs.json',ROOT/'scripts/uniform_seed_cyclotomic_engine.py']},cases=cases)
(BASE/'tensor-bytecode/fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','coveredPCs')}))
