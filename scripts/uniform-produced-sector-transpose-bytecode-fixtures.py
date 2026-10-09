"""Continuous actual physical axes -> sector records -> W role-major gathers.
Exact small-W tagged movement and independently calculated sector C matrices.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction
from itertools import product
import hashlib,json,random,sys
ROOT=Path(__file__).resolve().parents[1];BASE=ROOT/'logs/uniform-bytecode/operational-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
programs=json.loads((BASE/'produced-transpose-bytecode/programs.json').read_text())
specs=json.loads((ROOT/'logs/uniform-bytecode/sector-padding-preparation/sector-bytecode/specs.json').read_text())
coordinates=json.loads((BASE/'produced-transpose-bytecode/coordinates.json').read_text())
X,A,E,D=1000,40000,10000,700;B=1000000

def state(spec,W,order,seed):
    rng=random.Random(seed);ell=len(spec['widths']);L=spec['volume']
    s=dict(pc=0,nat=[rng.randrange(100) for _ in range(4600)],nh={7:19,B-1:5},
       sh={0:scalar(order,3,7),B-1:scalar(order,7,-11,True)},
       sr={q:scalar(order,Fraction(q-3,7),Fraction(13-q,11),q%2) for q in range(140)},
       out={0:scalar(order,19,-17)[0]},roots=[4,1])
    values=[[scalar(order,Fraction(7*j-11*r,13),Fraction(5*j+3*r,17),(j+r+seed)%2) for j in range(L)] for r in range(W)]
    for r in range(W):
      for j in range(L):s['sh'][X+r*L+j]=values[r][j]
    for j in range(W*L):s['sh'][A+j]=scalar(order,Fraction(j+1,19),Fraction(1-j,23),True)
    for j,ws in enumerate(spec['widths']):
      widthbase=100+100*j;perm=300+100*j
      for k,v in enumerate(ws):s['nh'][widthbase+k]=v
      for k in range(sum(ws)):s['nh'][perm+k]=(k+1)%sum(ws)
      for k,v in enumerate([len(ws),widthbase,sum(ws),perm]):s['nh'][20+4*j+k]=v
    for reg,value in {102:ell-1,3201:20,3202:500,3213:600,3214:650,3215:D,
      4441:E,4442:A,4530:L,4531:X}.items():s['nat'][reg]=value
    return s,values

cases=[];covered=set()
for p in programs:
    W=p['W'];code=p['continuous202'];assert len(code)==202
    for sid,spec in enumerate(specs):
      ell=len(spec['widths'])
      if not ell:continue # physical102+1=ell contract excludes empty axes.
      L=spec['volume'];M=len(spec['sectors'])
      for order in (4,8,12):
       for seed in range(2):
        s,values=state(spec,W,order,seed);old=deepcopy(s)
        expected=spec['treeCost']+43*ell+(12*W+44)*M+7*W*L+50
        ticks,pcs,peak=execute(code,s,B,expected,order);covered.update(pcs)
        assert ticks==expected and s['pc']==201 and peak<=B
        assert s['nat'][464]==M and s['nat'][4532]==E
        for i,(start,width,q) in enumerate(spec['sectors']):
          assert [s['nh'][E+5*i+j] for j in range(5)]==[q,width,A+W*start,start,W*width]
          for r in range(W):
            for t in range(width):assert s['sh'][A+W*start+r*width+t]==values[r][start+t]
        assert all(s['sh'].get(a)==v for a,v in old['sh'].items() if not A<=a<A+W*L)
        assert all(s['nh'].get(a)==v for a,v in old['nh'].items() if a<500)
        assert s['nat'][100:107]==old['nat'][100:107]
        assert s['out']==old['out'] and s['roots']==old['roots']
        assert all(s['sr'][r]==v for r,v in old['sr'].items() if r!=32)
        cases.append(dict(W=W,spec=sid,D=order,seed=seed,ticks=ticks))
assert covered==set(range(202)),sorted(set(range(202))-covered)
controls=[]
def reject(name,mutate,budget=None,modify=None):
    s,_=state(specs[-1],3,12,1);mutate(s);code=deepcopy(programs[2]['continuous202'])
    if modify:modify(code)
    try:execute(code,s,B,10**7 if budget is None else budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')
reject('missing-original-width-cell',lambda s:s['nh'].pop(100))
reject('missing-original-axis-row-cell',lambda s:s['nh'].pop(21))
reject('missing-native-role0-cell',lambda s:s['sh'].pop(X))
reject('missing-native-later-role-cell',lambda s:s['sh'].pop(X+2*specs[-1]['volume']))
reject('word-bound-native-header',lambda s:s['nat'].__setitem__(4531,B+1))
reject('charged-budget',lambda s:None,budget=1)
reject('mutated-directory-reload',lambda s:None,modify=lambda c:c.__setitem__(159,['add',4532,4442,4572]))
# Matrix check uses exact independent Gaussian rationals. The exported digits
# are the normal library's explicit numeric child coordinates, not chosen Fin
# enumeration. Mixed positions are enumerated separately in original axis order.
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def C(x,y):return (Fraction(1,2),Fraction(1 if x==y else -1,2))
checks=0
for data in coordinates:
 k=data['k'];digits=data['digits'];assert digits==[[i//(2**b)%2 for b in range(k)] for i in range(2**k)]
for spec in specs:
    for blocks in product(*(range(len(ws)) for ws in spec['widths'])):
      radices=[ws[b] for ws,b in zip(spec['widths'],blocks)];q=radices.count(2);N=2**q
      points=list(product(*(range(r) for r in radices)));assert len(points)==N
      bits=coordinates[q]['digits']
      for ix,x in enumerate(points):
       for iy,y in enumerate(points):
        sector=(Fraction(1),Fraction(0));child=(Fraction(1),Fraction(0))
        for r,a,b in zip(radices,x,y):sector=mul(sector,C(a,b) if r==2 else (Fraction(int(a==b)),Fraction(0)))
        for a,b in zip(bits[ix],bits[iy]):child=mul(child,C(a,b))
        assert sector==child
        checks+=1
result=dict(status='PASS',exactCases=len(cases),matrixEntries=checks,negativeControls=controls,coveredPCs=sorted(covered),
 contracts='Genuine Lean-exported generic Axis partitions; only original four-word physical rows/width cells and arbitrary present W-role native Scalars are initialized. Generated sector records/count and child layout are produced continuously by202. Ordinary true disjoint layout/WB. W1,2,3,5. Not actual selected startup/large-W bank, recursive child or complete FFT execution.',
 model='Exact Q[eta]/Phi_D D4,8,12 copied tags; independent exact Gaussian rational matrix entries and actual normal LE coordinate export; no floating point.',
 sourceHashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),BASE/'produced-transpose-bytecode/programs.json',BASE/'produced-transpose-bytecode/coordinates.json',ROOT/'logs/uniform-bytecode/sector-padding-preparation/sector-bytecode/specs.json',ROOT/'scripts/uniform_seed_cyclotomic_engine.py']},cases=cases)
(BASE/'produced-transpose-bytecode/fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','coveredPCs')}))
