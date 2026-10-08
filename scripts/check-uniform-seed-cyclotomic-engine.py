"""Independent defining-polynomial check and dyadic engine regression."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from heapq import heapify,heappush,heappop
import importlib.util,json,random
from uniform_seed_cyclotomic_engine import Poly,scalar,execute
P=Path(__file__).resolve().parents[1]/"logs/uniform-bytecode/seed-rank-cross"
old_path=Path(__file__).resolve().parent/'uniform_cyclotomic_engine.py'
spec=importlib.util.spec_from_file_location('old_engine',old_path);old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
def poly_div(a,b):
 a=dict(a);db=max(b);lb=b[db];q={};heap=[-k for k in a];heapify(heap)
 while heap:
  k=-heappop(heap)
  if k not in a:continue
  if k<db:break
  coeff=a[k]/lb;off=k-db;q[off]=coeff
  for j,v in b.items():
   key=off+j;a[key]=a.get(key,F(0))-coeff*v
   if not a[key]:del a[key]
   elif key!=k:heappush(heap,-key)
 return q,a
phis={1:{0:F(-1),1:F(1)}}
def divisors(n):
 out=set()
 for d in range(1,isqrt(n)+1):
  if n%d==0:out.update([d,n//d])
 return sorted(out)
def phi(n):
 if n not in phis:
  p={n:F(1),0:F(-1)}
  for d in divisors(n)[:-1]:
   p,rem=poly_div(p,phi(d));assert not rem
  phis[n]=p
 return phis[n]
for D,mod in [(128,{64:F(1),0:F(1)}),(24576,{8192:F(1),4096:F(-1),0:F(1)})]:
 assert phi(D)==mod,(D,phi(D))
 eta=Poly(D,{1:1});one=Poly(D,{0:1})
 assert eta**D==one and eta**(D//2)!=one
 if D%3==0:assert eta**(D//3)!=one
 assert Poly(D,mod)==Poly(D)
 print('independent Phi',D,mod,flush=True)
rng=random.Random(130);comparisons=0
for D in [4,8,16,32,128]:
 m=D//2
 for _ in range(50):
  a={j:F(rng.randrange(-7,8),rng.randrange(1,6)) for j in rng.sample(range(m),min(m,5))}
  b={j:F(rng.randrange(-7,8),rng.randrange(1,6)) for j in rng.sample(range(m),min(m,5))}
  A,B=Poly(D,a),Poly(D,b);x,y=old.Poly(m,a),old.Poly(m,b)
  assert (A+B).c==(x+y).c and (A-B).c==(x-y).c and (A*B).c==(x*y).c
  exp=rng.randrange(12);assert (A**exp).c==(x**exp).c
  re,im=F(rng.randrange(1,8),3),F(rng.randrange(-3,4),5)
  den=Poly(D,{0:re,D//4:im});inverse=Poly(D,{0:re/(re*re+im*im),D//4:-im/(re*re+im*im)})
  assert den.inverse()==inverse;comparisons+=1
# Composite use of the previous quotient would admit explicit zero divisors.
D=24576;m=D//2
factor=old.Poly(m,{0:1,4096:1});cyclo=old.Poly(m,{0:1,4096:-1,8192:1})
assert factor.c and cyclo.c and not (factor*cyclo).c
assert Poly(D,{0:1,4096:-1,8192:1})==Poly(D)
# End-to-end dyadic state/step regression of actual empty935 with old engine.
startup=json.loads((P/'startup.json').read_text());D=128;m=64;n=1
new={'pc':0,'nat':[0]*1200,'sr':{},'nh':{},'sh':{},'out':{},'roots':[]}
prev={'pc':0,'nat':[0]*1200,'sr':{j:old.scalar(m) for j in range(1200)},'nh':{},'sh':{},'out':{},'roots':[]}
run=execute(startup,new,3**19,100000,D,n,[scalar(D,3,-2)[0]])
oldRun=old.execute(startup,prev,3**19,100000,m,n,[old.scalar(m,3,-2)[0]],D)
assert run[:2]==oldRun
for field in ['pc','nat','nh','roots']:assert new[field]==prev[field]
for field in ['sh']:
 assert set(new[field])==set(prev[field])
 for j in new[field]:assert new[field][j][0].c==prev[field][j][0].c and new[field][j][1]==prev[field][j][1]
for j in set(new['sr'])|set(prev['sr']):
 a=new['sr'].get(j,scalar(D));b=prev['sr'][j];assert a[0].c==b[0].c and a[1]==b[1]
assert set(new['out'])==set(prev['out'])
for j in new['out']:assert new['out'][j].c==prev['out'][j].c
result={'status':'PASS','independentPhiConstruction':[128,24576],'primitiveOrderChecks':['eta^D=1','eta^(D/2)!=1','eta^(D/3)!=1 for compositeD'],
 'dyadicRandomComparisons':comparisons,'actualEmpty935DyadicComparisonSteps':run[0],
 'oldCompositeZeroDivisorDemonstrated':True,'oldCompositeRingUsedForNewFixtures':False,
 'inversionScope':'Only divisors with nonzero rational complex norm; every inverse product checked. No general modular inverse claim.',
 'comparisonSource':str(old_path),'comparisonOrigin':'scripts/uniform_cyclotomic_engine.py'}
(P/'engine-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
