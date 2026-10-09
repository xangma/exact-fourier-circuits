"""Exact diagnostics of scalar106 with the full native volume and real record reads."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,add,mul
CODE=json.loads((P/'native-scalar-program.json').read_text());assert len(CODE)==106
COEFS=[F(-1),F(-1,2),F(0),F(1,2),F(1)]
WRITES=set(range(2850,2877))|set(range(2900,2917))|set(range(3302,3307))

def fresh(D,k,q,w,R,d,src,c,family):
 A=1000;T=8000;V=2**k
 s=dict(pc=0,nat=[(17*i+31)%233 for i in range(5320)],nh={1:3,77:19},sh={},
        sr={i:scalar(D,F(i+2,7),F(9-i,11),True) for i in range(108)},
        out={7:scalar(D,11,-3)[0]},roots=[D,4])
 for r,v in ((2850,T),(3300,A),(5300,k)):s['nat'][r]=v
 record=[1,q,w,d,src,0,0,c];s['nh'].update({T+i:v for i,v in enumerate(record)})
 for role in range(R):
  for z in range(V):
   if family=='zero':v=scalar(D,dep=(role+z)%2==0)
   elif family=='prepared':v=scalar(D,F(role-z+31,11),F(z+3*role,13))
   elif family=='cancellation':v=scalar(D,(-1)**(z+role),dep=(role+z)%3!=0)
   else:v=scalar(D,F(3*z-7*role+31,11),F(z+role+5,13),(z+31+role)%2==0)
   s['sh'][A+role*V+z]=v
 for a in (A-1,A+R*V,20000):s['sh'][a]=scalar(D,-13,7,True)
 return s

cases=[];pcs=set();ticks=0
for D in (4,12):
 for k in range(6):
  for w in (1,2,3,5):
   q=k//w
   for R in (3,4):
    for d,src in ((0,1),(R-1,0)):
     for c in range(5):
      for family in ('zero','prepared','cancellation','mixed'):
       s=fresh(D,k,q,w,R,d,src,c,family);before=deepcopy(s);expected=deepcopy(s['sh']);V=2**k
       for z in range(V):
        expected[1000+d*V+z]=add(before['sh'][1000+d*V+z],mul(scalar(D,COEFS[c]),before['sh'][1000+src*V+z]))
       cost=10*V+4*k+c+62
       steps,seen,peak=execute(CODE,s,30000,cost,D)
       assert steps==cost and s['pc']==105 and s['nat'][2850]==8008
       assert s['sh']==expected,(D,k,q,w,R,d,src,c,family)
       for name in ('nh','out','roots'):assert s[name]==before[name],name
       for r in range(5320):
        if r not in WRITES:assert s['nat'][r]==before['nat'][r],r
       for r in range(108):
        if r not in (100,101,102,104):assert s['sr'][r]==before['sr'][r],r
       assert peak<=30000
       pcs.update(seen);ticks+=steps
       cases.append(dict(D=D,bits=k,q=q,width=w,remainder=k-q*w,roles=R,dest=d,source=src,coefficient=c,family=family,steps=steps))
controls=[]
for missing in ('record','destination','source'):
 s=fresh(4,3,1,2,3,0,1,4,'mixed')
 if missing=='record':del s['nh'][8002]
 else:del s['sh'][1000+(0 if missing=='destination' else 8)+1]
 try:execute(CODE,s,30000,30000,4)
 except (AssertionError,KeyError):controls.append(missing)
 else:raise AssertionError('missing entry accepted: '+missing)
s=fresh(4,3,1,2,3,0,1,9,'mixed')
try:execute(CODE,s,30000,30000,4)
except (AssertionError,KeyError):controls.append('invalidCoefficientCode')
else:raise AssertionError('invalid coefficient accepted')
paths=[ROOT/'lean/UniformNativeScalarRecordMachine.lean',ROOT/'verification/ExportNativeScalarRecordBytecode.lean',
       P/'native-scalar-program.json',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,pcCoverage=sorted(pcs),controls=controls,
            sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            scope='Actual scalar106, real printed q/width record, full native k=q*width+r role bank; no recursive or global DFT claim.')
(P/'native-scalar-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))
