"""Exact diagnostics for the current Lean zero-free diagonal producer.
The original/conjugate coefficient banks are explicit caller fixtures.
"""
from pathlib import Path
from fractions import Fraction as F
import json,copy,random
P=Path(__file__).resolve().parents[1]/'logs'/'uniform-bytecode'
code=json.loads((P/'programs.json').read_text())['zeroFree'];assert len(code)==30
hits=set()
Z=(F(0),F(0));ONE=(F(1),F(0))
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def inv(a):
 q=a[0]*a[0]+a[1]*a[1];assert q!=0,'division by zero'
 return(a[0]/q,-a[1]/q)
def run(s,B,limit):
 pc=0;steps=0;r=s['r'];h=s['h'];q=s['q'];sh=s['sh']
 assert all(0<=v<=B for v in r.values())
 assert all(0<=i<=B and 0<=v<=B for i,v in h.items())
 assert all(0<=i<=B for i in sh)
 while True:
  assert 0<=pc<len(code) and pc<=B
  op,*a=code[pc];hits.add(pc);steps+=1;assert steps<=limit;pc+=1
  if op=='halt':return steps,pc-1
  if op=='lit':r[a[0]]=a[1];assert 0<=a[1]<=B
  elif op=='add':
   r[a[0]]=r[a[1]]+r[a[2]];assert r[a[0]]<=B,'word overflow'
  elif op=='rat':q[a[0]]=((F(a[1],a[2]),F(0)),False)
  elif op=='getscalar':
   assert r[a[1]] in sh,'missing scalar';q[a[0]]=sh[r[a[1]]]
  elif op=='putscalar':assert r[a[0]]<=B;sh[r[a[0]]]=q[a[1]]
  elif op in ['fadd','fsub','fmul','fdiv']:
   x,dx=q[a[1]];y,dy=q[a[2]]
   if op=='fmul':assert not(dx and dy),'dependent product';z=mul(x,y)
   elif op=='fdiv':assert not(dx or dy),'dependent division';z=mul(x,inv(y))
   elif op=='fadd':z=add(x,y)
   else:z=sub(x,y)
   q[a[0]]=(z,dx or dy)
  elif op=='branch':l,t,y,n=a;pc=y if r[l]<r[t] else n
  elif op=='jump':pc=a[0]
  else:raise AssertionError(op)

def caller(c,mode):
 k=len(c);a,b,d,e,f=(32,128,256,512,1024) if mode==0 else (192,320,512,768,1536)
 s={'r':{i:(i*17+3)%2000 for i in range(401)},'h':{i:(i*3+11)%2000 for i in range(1800)},
  'q':{i:((F(i,3),F(-2,7)),bool(i%2)) for i in range(40)},
  'sh':{i:((F(2*i-7,11),F(i%5,3)),bool(i%2)) for i in range(2000)},
  'roots':[128],'outputs':{0:(F(5),F(-3))}}
 s['sh'][0]=((F(0),F(1)),False)
 s['r'].update({370:k,371:a,372:b,373:d,374:e,375:f})
 for j,z in enumerate(c):s['sh'][a+j]=(z,False);s['sh'][b+j]=((z[0],-z[1]),False)
 return s,(a,b,d,e,f)

rng=random.Random(934619);cases=[]
for k in [0,1,2,3,5,10,17,32,64]:
 for t in range(20):
  c=[Z if t%4==0 or j%4==0 else (F(rng.randrange(-9,10),rng.randrange(1,8)),F(rng.randrange(-9,10),rng.randrange(1,8))) for j in range(k)]
  initial,(a,b,d,e,f)=caller(c,t%2);s=copy.deepcopy(initial)
  steps,pc=run(s,4096,20*k+12)
  lam=(F(1)+sum(z[0]**2+z[1]**2 for z in c),F(0))
  assert steps==20*k+12 and pc==29 and lam[0]>0
  assert s['sh'][d]==(lam,False) and s['sh'][d+1]==(inv(lam),False)
  for j,z in enumerate(c):
   diff=sub(z,lam);assert diff!=Z
   assert s['sh'][e+j]==(diff,False) and s['sh'][f+j]==(inv(diff),False)
   assert s['sh'][a+j]==initial['sh'][a+j] and s['sh'][b+j]==initial['sh'][b+j]
  assert all(s['sh'][i]==v for i,v in initial['sh'].items() if i not in [d,d+1] and not e<=i<e+k and not f<=i<f+k)
  assert all(s['r'][i]==v for i,v in initial['r'].items() if i<376 or i>=380)
  assert all(s['q'][i]==v for i,v in initial['q'].items() if i<10 or i>=16)
  assert all(s[z]==initial[z] for z in ['h','roots','outputs'])
  cases.append({'width':k,'layout':t%2,'zero_bank':t%4==0,'steps':steps})
assert hits==set(range(30)),hits
negative=[]
for name in ['missing-original','missing-conjugate','dependent-original','dependent-conjugate','zero-shift-from-invalid-conjugate','computed-word-overflow']:
 s,(a,b,d,e,f)=caller([(F(1),F(0))],0)
 if name=='missing-original':del s['sh'][a]
 elif name=='missing-conjugate':del s['sh'][b]
 elif name=='dependent-original':s['sh'][a]=(ONE,True)
 elif name=='dependent-conjugate':s['sh'][b]=(ONE,True)
 elif name=='zero-shift-from-invalid-conjugate':s['sh'][b]=((F(-1),F(0)),False)
 else:
  s['r'][370]=2;s['r'][371]=4096;s['sh'][4096]=(ONE,False);s['sh'][b+1]=(ONE,False)
 try:run(s,4096,200)
 except AssertionError as exc:negative.append({'case':name,'rejected':str(exc)})
 else:raise AssertionError(name)
result={'status':'PASS','instructions':30,'cases':cases,'negative_controls':negative,'all_program_counters':True,
 'exact_oracle':'Independent real norm-square lambda and exact Gaussian-rational inverses; no floating point.',
 'scope':'Physical coefficient/conjugate banks are honest entry inputs; invalid conjugate consistency is not itself runtime-tested.'}
(P/'zero-free-fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS:{len(cases)} exact30 cases/allPCs;{len(negative)} guard controls')
