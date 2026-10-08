"""Exact independent reference for real variable-length mixed335 records."""
from pathlib import Path
from fractions import Fraction as F
import sys,copy,json,hashlib
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,add,mul
P=ROOT/'logs/uniform-bytecode/fixed-network-record-loop'
CODE=json.loads((P/'programs.json').read_text())['recordLoop']
assert len(CODE)==335
COEFS=[F(-1),F(-1,2),F(0),F(1,2),F(1)]
WRITES=set(range(2850,2877))|set(range(2900,2917))|set(range(3302,3309))|set(range(3310,3315))|set(range(3320,3342))|{0,1,2,2800,2801,2802,2803,2804,2805,2806,2810,2811,2820,2821,2822,2823,2824,2825}
def row(q,w,it):
 op,*v=it
 if op==1:d,s,c=v;return [1,q,w,d,s,0,0,c]
 if op==5:d,count=v;return [5,q,w,d,count,0,0,0]
 pairs=v[0];return [4,q,w,0,0,0,len(pairs),0]+[v for d,s in pairs for v in [d,s,4,0]]
def tensor(D,k,vs):
 A=scalar(D,F(1,2),F(1,2));B=scalar(D,F(1,2),F(-1,2));out=[]
 for r in range(2**k):
  acc=scalar(D)
  for c,v in enumerate(vs):
   coef=scalar(D,1)
   for ax in range(k):coef=mul(coef,A if ((r>>ax)&1)==((c>>ax)&1) else B)
   acc=add(acc,mul(coef,v))
  out.append(acc)
 return out

def fresh(D,q,w,R,base,T,items,salt):
 V=2**(q*w);data=[v for it in items for v in row(q,w,it)]
 s=dict(pc=0,nat=[(i*13+salt)%211 for i in range(3500)],nh={1:3,77:19},sh={1:scalar(D,F(1,2),F(1,2)),2:scalar(D,F(1,2),F(-1,2))},sr={0:scalar(D,-3,2,True),114:scalar(D,7,-11,True)},out={3:scalar(D,-1,7)[0]},roots=[D,4])
 s['nat'][3300]=base;s['nat'][2850]=T;s['nat'][3301]=T+len(data)
 s['nh'].update({T+j:v for j,v in enumerate(data)})
 for r in range(R):
  for z in range(V):s['sh'][base+r*V+z]=scalar(D,F(3*r-z+salt,7),F(2*z+r-salt,11),(z+r+salt)%3!=0)
 s['sh'][base-1]=scalar(D,-13,5,True);s['sh'][base+R*V]=scalar(D,7,-19)
 return s

def reference(D,k,R,base,items,before):
 V=2**k;sh=copy.deepcopy(before['sh']);ticks=6
 for op,*v in items:
  if op==1:
   d,src,c=v
   for z in range(V):sh[base+d*V+z]=add(sh[base+d*V+z],mul(scalar(D,COEFS[c]),sh[base+src*V+z]))
   ticks+=10*V+4*k+c+67
  elif op==5:
   first,count=v
   for r in range(first,first+count):
    vs=tensor(D,k,[sh[base+r*V+z] for z in range(V)])
    for z,a in enumerate(vs):sh[base+r*V+z]=a
   ticks+=count*(k*(25*2**max(k-1,0)+11)+15)+4*k+59
  else:
   pairs=v[0]
   for d,src in pairs:
    for z in range(V):
     a,b=sh[base+d*V+z],sh[base+src*V+z]
     sh[base+d*V+z]=b;sh[base+src*V+z]=(-a[0],a[1])
   ticks+=(10*V+21)*len(pairs)+4*k+57
 return sh,ticks

lean_items=[(1,0,1,0),(4,[(0,1),(1,2)]),(5,0,3),(1,2,3,2),(4,[]),(5,4,0)]
for spec in json.loads((P/'spec.json').read_text()):
 q,w=spec['q'],spec['width'];data=[v for it in lean_items for v in row(q,w,it)]
 assert data==spec['data'],'host row builder differs from actual Lean Record/serialize'
 b=fresh(4,q,w,4,100,20000,lean_items,0)
 assert reference(4,q*w,4,100,lean_items,b)[1]==spec['runtime'],'independent runtime differs from Lean Item.cost'

cases=[];pcs=set();ticks=0
for D in (4,12,32):
 for q,w in ((0,3),(1,0),(1,1),(2,1),(1,3)):
  for R in (3,4):
   for salt in (0,31):
    seqs=[[],[(4,[])],[(4,[(0,1)])],[(4,[(0,1),(1,2),(0,R-1)])],[(5,0,R)],[(1,0,1,c) for c in range(5)],[(1,1,0,4),(4,[(0,2)]),(5,0,2),(1,0,2,0),(4,[(2,1),(1,0)]),(5,R,0),(1,2,1,2),(4,[]),(5,1,R-1)]]
    for its in seqs:
     s=fresh(D,q,w,R,100,20000,its,salt);before=copy.deepcopy(s)
     out,budget=reference(D,q*w,R,100,its,before)
     count,seen,peak=execute(CODE,s,100000,budget,D)
     assert count==budget and s['pc']==334 and s['nat'][2850]==before['nat'][3301]
     assert s['sh']==out,(D,q,w,R,its)
     for name in ('nh','out','roots'):assert s[name]==before[name],name
     for r in range(3500):
      if r not in WRITES:assert s['nat'][r]==before['nat'][r],r
     for r in set(s['sr'])|set(before['sr']):
      if r>=114:assert s['sr'].get(r)==before['sr'].get(r),r
     pcs.update(seen);ticks+=count
     cases.append(dict(D=D,q=q,width=w,roles=R,items=its,salt=salt,steps=count,maxWord=peak))
controls=[]
def reject(name,s,B=100000,fuel=100000):
 try:execute(CODE,s,B,fuel,4)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted:'+name)
for op in (0,2,3,6,7):
 s=fresh(4,1,1,3,100,20000,[(1,0,1,0)],0);s['nh'][20000]=op;reject('unsupported opcode '+str(op),s)
s=fresh(4,1,1,3,100,20000,[(1,0,1,4)],0);s['nh'][20007]=5;reject('invalid Fin5',s)
s=fresh(4,1,1,3,100,20000,[(4,[(0,1)])],0);del s['nh'][20010];reject('missing physical exchange code field',s)
s=fresh(4,1,1,3,100,20000,[(4,[(0,1)])],0);del s['sh'][102];reject('missing exchange source',s)
s=fresh(4,1,1,3,100,20000,[(5,0,1)],0);s['sh'][1]=(s['sh'][1][0],True);reject('data-data multiply',s)
reject('charged step guard',fresh(4,1,1,3,100,20000,[(4,[(0,1)])],0),fuel=20)
s=fresh(4,0,0,3,100,99990,[(4,[(0,1)])],0);s['nat'][3301]=99990+8;reject('body cursor bound',s)
result=dict(status='PASS',exactCases=len(cases),chargedSteps=ticks,coveredPCs=sorted(pcs),negativeControls=controls,cases=cases,scope='Continuous actual fixed335 record interpreter for shear1, signed-exchange4 and padding5. Exact arbitrary data/flags and external frames. Printed records/original role bank/prepared C constants are entry contracts. Residual0/Y3/block2/layout6 and recursive dispatcher remain open; no full saving-network or unconditional UniformDFTStatement claim.',hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),P/'programs.json',P/'spec.json',ROOT/'verification/ExportFixedNetworkRecordLoopBytecode.lean')})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'continuous exact variable-body mixed cases',ticks,'charged steps',len(pcs),'successful PCs',len(controls),'guard controls')
