"""Actual49 factor-row production and continuous49->81 tensor diagonals.
Entry has original physical(radix,pool) directory, prepared9-lane pools,
present arbitrary tagged W data, and true disjoint placement. This is not a
full selected-cache producer or recursive/six-C scheduler witness.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction
from itertools import product
import json,sys,random,hashlib
ROOT=Path(__file__).resolve().parents[1];BASE=ROOT/'logs/uniform-bytecode/operational-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,mul
programs=json.loads((BASE/'produced-tensor-bytecode/programs.json').read_text())
specs=json.loads((BASE/'produced-tensor-bytecode/specs.json').read_text())
B=100000;DIR,ROW,PERM,COEF,NSTACK,SSTACK,DEST=4000,5000,6000,8000,16000,20000,30000

def lane_values(D,r,seed):
    values=[[scalar(D,1) for _ in range(r)] for _ in range(9)]
    for j in range(0,r-1,2):
        # Independent Gaussian rational kappa/rho for a genuine matched pair.
        re=Fraction(j-seed,3);im=Fraction(seed-j+1,5)
        kappa=1+re*re+im*im;rr=re-kappa;ri=im;norm=rr*rr+ri*ri
        left=[scalar(D,Fraction(5,4)/kappa),scalar(D,Fraction(4,5)*kappa),
          scalar(D,Fraction(5,4)*rr/norm,-Fraction(5,4)*ri/norm),
          scalar(D,Fraction(4,5)*rr,Fraction(4,5)*ri),scalar(D,-3),scalar(D,2),
          scalar(D,Fraction(-1,8)),scalar(D,1),scalar(D,Fraction(4,5),Fraction(-2,5))]
        right=[scalar(D,1) for _ in range(6)]+[scalar(D,Fraction(-1,6)),scalar(D,0,1),
          scalar(D,Fraction(2,5),Fraction(4,5))]
        for lane in range(9):values[lane][j]=left[lane];values[lane][j+1]=right[lane]
    return values

def make(spec,W,D,seed,lane,above):
    rng=random.Random(seed);rs=spec['radices'];V=1
    for r in rs:V*=r
    A=12000 if above else 1000
    s=dict(pc=0,nat=[rng.randrange(30) for _ in range(4700)],nh={3:17,B-1:7},
      sh={0:scalar(D,7,-3,True),B-1:scalar(D,-17,2,True)},
      sr={r:scalar(D,Fraction(r+1,13),Fraction(3-r,17),r%2) for r in range(140)},
      out={0:scalar(D,19,-11)[0]},roots=[4,1])
    pools=[]
    for i,r in enumerate(rs):
        base=200+100*i;vals=lane_values(D,r,seed+i);pools.append(vals)
        s['nh'][DIR+2*i]=r;s['nh'][DIR+2*i+1]=base
        for k in range(9):
            for j in range(r):s['sh'][base+k*r+j]=vals[k][j]
    amount=sum(rs)
    for j in range(amount):s['nh'][PERM+j]=99;s['sh'][COEF+j]=scalar(D,-17,19,True)
    for j in range(3*len(rs)):s['nh'][ROW+j]=88;s['nh'][NSTACK+j]=77
    for j in range(len(rs)):s['sh'][SSTACK+j]=scalar(D,99,-77,True)
    data=[[scalar(D,Fraction(7*j-3*i-11,19),Fraction(i+5*j+7,23),(i+j+seed)%2) for j in range(V)] for i in range(W)]
    for i in range(W):
      for j in range(V):s['sh'][A+i*V+j]=data[i][j];s['sh'][DEST+i*V+j]=scalar(D,-j-i,13,True)
    args={4580:len(rs),4581:DIR,4582:lane,4583:ROW,4584:PERM,4585:COEF,
          4501:V,4502:A,4503:DEST,4504:len(rs),4505:ROW,4506:NSTACK,4507:SSTACK}
    for reg,val in args.items():s['nat'][reg]=val
    return s,data,pools,V,A

def rows_ok(s,rs,pools,lane):
    off=0
    for i,r in enumerate(rs):
        assert [s['nh'][ROW+3*i+f] for f in range(3)]==[r,PERM+off,COEF+off]
        for j in range(r):assert s['nh'][PERM+off+j]==j;assert s['sh'][COEF+off+j]==pools[i][lane][j]
        off+=r

def outside(s,old,rs,W,V,joined):
    amount=sum(rs)
    for q,value in old['nh'].items():
        if not (ROW<=q<ROW+3*len(rs) or PERM<=q<PERM+amount or joined and NSTACK<=q<NSTACK+3*len(rs)):assert s['nh'].get(q)==value
    for q,value in old['sh'].items():
        if not (COEF<=q<COEF+amount or joined and (SSTACK<=q<SSTACK+len(rs) or DEST<=q<DEST+W*V)):assert s['sh'].get(q)==value
    assert s['out']==old['out'] and s['roots']==old['roots']
    assert all(s['nat'][q]==old['nat'][q] for q in range(100,107))
    # Complete actual known Nat footprint, including helper scratch.
    writes=set(range(170,181))|set(range(4380,4388))|set(range(4590,4596))
    if joined:writes|=set(range(20))|{4500,4510,4511,4512,4513}
    assert all(s['nat'][q]==v for q,v in enumerate(old['nat']) if q not in writes)

cases=[];cover49=set();cover131=set()
assert len(programs['rows'])==49
for sid,spec in enumerate(specs):
 for D in (4,8,12):
  for seed in range(2):
   for lane in range(9):
    s,data,pools,V,A=make(spec,1,D,seed,lane,False);old=deepcopy(s)
    cost=9*sum(spec['radices'])+35*len(spec['radices'])+7
    ticks,pcs,peak=execute(programs['rows'],s,B,cost,D)
    assert ticks==cost and s['pc']==48 and peak<=B;cover49.update(pcs)
    rows_ok(s,spec['radices'],pools,lane);outside(s,old,spec['radices'],1,V,False)
    cases.append(dict(kind='rows49',spec=sid,D=D,seed=seed,lane=lane,ticks=ticks))
    for p in programs['joined']:
     W=p['W'];assert len(p['code'])==131
     for above in (False,True):
      s,data,pools,V,A=make(spec,W,D,seed,lane,above);old=deepcopy(s)
      cost=9*sum(spec['radices'])+35*len(spec['radices'])+W*(spec['treeCost']+20)+14
      ticks,pcs,peak=execute(p['code'],s,B,cost,D)
      assert ticks==cost and s['pc']==130 and peak<=B;cover131.update(pcs)
      rows_ok(s,spec['radices'],pools,lane)
      for i in range(W):
       for j,z in enumerate(product(*(range(r) for r in spec['radices']))):
        ans=data[i][j]
        for axis,local in enumerate(z):ans=mul(pools[axis][lane][local],ans)
        assert s['sh'][DEST+i*V+j]==ans,(sid,W,D,seed,lane,above,i,j)
      outside(s,old,spec['radices'],W,V,True)
      cases.append(dict(kind='joined131',W=W,spec=sid,D=D,seed=seed,lane=lane,sourceAbove=above,ticks=ticks))
controls=[]
def reject(name,mutate,budget=None,mutate_code=None):
 s,_,_,_,_=make(specs[4],3,12,1,0,True);mutate(s);code=deepcopy(programs['joined'][2]['code'])
 if mutate_code:mutate_code(code)
 try:execute(code,s,B,1000000 if budget is None else budget,12)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
reject('missing-physical-radix',lambda s:s['nh'].pop(DIR))
reject('missing-physical-pool-address',lambda s:s['nh'].pop(DIR+1))
reject('missing-physical-pool-value',lambda s:s['sh'].pop(200))
reject('missing-present-input',lambda s:s['sh'].pop(12000))
reject('unprepared-coefficient-data-multiplication',lambda s:s['sh'].__setitem__(200,scalar(12,3,2,True)))
reject('word-address-guard',lambda s:s['nat'].__setitem__(4503,B+1))
reject('charged-budget-guard',lambda s:None,budget=1)
reject('mutated-physical-pool-load',lambda s:None,mutate_code=lambda c:c.__setitem__(10,['getnat',4381,4590]))
assert cover49==set(range(49)),sorted(set(range(49))-cover49)
assert cover131==set(range(131)),sorted(set(range(131))-cover131)
result=dict(status='PASS',exactCases=len(cases),rowsCases=sum(c['kind']=='rows49' for c in cases),
 joinedCases=sum(c['kind']=='joined131' for c in cases),negativeControls=controls,covered49=sorted(cover49),covered131=sorted(cover131),
 contracts='Original physical(radix,pool) directory and prepared9r factor pools, tagged present W arrays; all ordinary Layout/Geometry and source-coefficient disjointness hold. Pools use genuine Gaussian-rational kappa/rho factors; generic local matching pools, not actual full selected-cache producer. Small W1,2,3,5 only; no recursive child or six-C execution.',
 model='Exact Q[eta]/Phi_D D4/8/12; no floating point. Generated rows/permutations/coefficient banks, exact full-tagged data and frames checked.',
 sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),BASE/'produced-tensor-bytecode/programs.json',BASE/'produced-tensor-bytecode/specs.json',ROOT/'scripts/uniform_seed_cyclotomic_engine.py']},cases=cases)
(BASE/'produced-tensor-bytecode/fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','covered49','covered131')}))
