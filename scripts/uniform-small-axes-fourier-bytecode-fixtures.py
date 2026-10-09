"""Actual182 all-small-axis loop, true canonical roots in exact Phi4/12/60/120."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import sys,json,hashlib,os
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_general_cyclotomic_engine import Poly,scalar,execute,cyclotomic,mul_poly
print('host=mac cwd='+str(ROOT)+' pid='+str(os.getpid()),flush=True)
programs=json.loads((P/'small-axes-programs.json').read_text());assert all(len(p['code'])==182 for p in programs)
specPath=ROOT/'logs/uniform-bytecode/all-tensor-fibers/spec.json';specs=json.loads(specPath.read_text())
# The field engine checks the defining exact factorization and actual inverses,
# including divisors with nonrational conjugate norm rejected by the old engine.
fields=[]
for D in (4,8,12,20,60,120,196):
 product=[F(1)]
 for d in range(1,D+1):
  if D%d==0:product=mul_poly(product,cyclotomic(d))
 assert product==[F(-1)]+[F(0)]*(D-1)+[F(1)]
 eta=Poly(D,{1:1});one=Poly(D,{0:1});assert eta**D==one
 for c in (1,2,3):
  v=eta+Poly(D,{0:c});assert v*v.inverse()==one
 fields.append(dict(D=D,degree=len(cyclotomic(D))-1))
cases=[];pcs=set();steps=0;controls=[]
def state(spec,D,family,salt):
 B=(spec['n']+2)**19;A,G,E=20000,40000,60000;L=spec['L']
 s=dict(pc=0,nat=[(17*i+13+salt)%7000 for i in range(5120)],nh={B-7:31},
  sh={B-11:scalar(D,-2,3,True)},sr={i:scalar(D,F(i-5,3),F(11-i,7),i%2==0) for i in range(102)},
  out={3:scalar(D,7,-2)[0]},roots=[4,12])
 s['nat'][100:107]=[spec['nextPrime'],spec['n'],spec['ell'],L,spec['D'],spec['M'],spec['amount']]
 for z in range(spec['amount']):s['nh'][spec['M']+z]=0
 for j,v in enumerate(spec['primes']):s['nh'][spec['M']+j]=v
 for j,row in enumerate(spec['crt']):
  for f,v in enumerate(row):s['nh'][spec['M']+spec['ell']+4*j+f]=v
 for j,v in enumerate(spec['alpha']):s['nh'][spec['M']+spec['alphaBase']+j]=v
 for j,v in enumerate(spec['beta']):s['nh'][spec['M']+spec['betaBase']+j]=v
 for reg,v in [(5102,A),(5103,G),(5104,E)]:s['nat'][reg]=v
 for j,r in enumerate(spec['radices']):
  assert D%r==0;s['sh'][6+j]=(Poly(D,{D//r:1}),False)
 for z in range(L):
  if family=='zero':v=scalar(D,dep=z%2==0)
  elif family=='prepared':v=scalar(D,F(z-7,5),F(13-z,9))
  elif family=='cancellation':v=scalar(D,(-1)**z,dep=z%3!=0)
  else:v=scalar(D,F(z-7,5),F(13-z,9),z%3==0)
  s['sh'][A+z]=v;s['sh'][G+z]=scalar(D,F(5-z,11),F(z+1,13),z%2==1)
  s['sh'][E+z]=scalar(D,100-z,z-100,True)
 return s,B,A,G,E
for spec in specs:
 D={1:4,2:12,3:12,5:12,11:60,40:120}[spec['n']]
 for program in programs:
  T,code=program['threshold'],program['code']
  written={i[1] for i in code if i[0] in ('lit','add','sub','mul','div','mod','getnat')}
  scalarWritten={i[1] for i in code if i[0] in ('rat','getscalar','fadd','fsub','fmul','fdiv','root','input')}
  for family in ('zero','prepared','cancellation','mixed'):
   for salt in (0,41):
    s,B,A,G,E=state(spec,D,family,salt);before=deepcopy(s);want=deepcopy(s['sh'])
    time=10+7*len(spec['axisSpecs']);active=[]
    for ax in spec['axisSpecs']:
     r,p,q=ax['r'],ax['P'],ax['Q'];count=p*q
     if r>=T:continue
     active.append(ax['axis']);eta=want[6+ax['axis']][0];bank=[want[A+z] for z in range(spec['L'])]
     for j,row in enumerate(ax['positions']):
      for t,coord in enumerate(row):want[G+j*r+t]=bank[coord]
      for k,coord in enumerate(row):
       val=Poly(D);dep=False
       for t,source in enumerate(row):
        val=val+eta**(k*t)*bank[source][0];dep=dep or bank[source][1]
       want[E+j*r+k]=want[A+coord]=(val,dep)
     copycost=count*(9*r+27)+7*ax['axis']+14
     time+=5+2*copycost+count*((8*r+10)*r+14)+22
    ticks,coverage,peak=execute(code,s,B,time,D)
    assert ticks==time and s['pc']==181
    assert s['sh']==want,(spec['n'],T,D,family,salt)
    for key in ('nh','out','roots'):assert s[key]==before[key],key
    for reg in range(len(s['nat'])):
     if reg not in written:assert s['nat'][reg]==before['nat'][reg],reg
    for reg in range(102):
     if reg not in scalarWritten:assert s['sr'].get(reg)==before['sr'].get(reg),reg
    assert s['nat'][5105]==len(spec['axisSpecs'])
    assert s['nat'][100:107]==before['nat'][100:107]
    bound=10+7*(spec['ell']+1)+(T+1)*((8*T+96)*spec['L']+14*spec['ell']+55)
    assert ticks<=bound
    pcs.update(coverage);steps+=ticks
    cases.append(dict(n=spec['n'],T=T,active=active,D=D,family=family,salt=salt,steps=ticks,maximumWord=peak))
    if len(cases)%32==0:print('cases='+str(len(cases))+' steps='+str(steps),flush=True)
def reject(name,edit,budget=None):
 spec=specs[-1];s,B,A,G,E=state(spec,120,'mixed',0);edit(s,spec,A,G,E)
 try:execute(programs[-1]['code'],s,B,budget or 1000000,120)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted '+name)
reject('missing later selected CRT radix',lambda s,sp,A,G,E:s['nh'].pop(sp['M']+sp['ell']+4))
reject('zero selected divisor',lambda s,sp,A,G,E:s['nh'].__setitem__(sp['M']+sp['ell']+4,0))
reject('missing later source',lambda s,sp,A,G,E:s['sh'].pop(A+sp['L']-1))
reject('missing actual prepared axis root',lambda s,sp,A,G,E:s['sh'].pop(7))
reject('dependent actual axis root',lambda s,sp,A,G,E:s['sh'].__setitem__(7,(s['sh'][7][0],True)))
reject('charged budget',lambda *args:None,10)
assert pcs==set(range(182)),sorted(set(range(182))-pcs)
paths=[Path(__file__),P/'small-axes-programs.json',ROOT/'verification/ExportSmallAxesFourierBytecode.lean',ROOT/'lean/UniformSmallAxesMachine.lean',ROOT/'lean/UniformSmallAxesBudget.lean',ROOT/'lean/UniformSmallAxisFourierPreservation.lean',ROOT/'lean/UniformSmallAxisFourierMachine.lean',ROOT/'scripts/uniform_general_cyclotomic_engine.py',ROOT/'lean/UniformHeapDirectBatch.lean',ROOT/'lean/UniformHeapDirectFourier.lean',specPath,ROOT/'lean/UniformAllTensorFibersCopyMachine.lean',ROOT/'lean/UniformSelectedAxisFiberPreparation.lean',ROOT/'lean/UniformTensorFiberCopyMachine.lean',ROOT/'lean/UniformMachine.lean']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=steps,pcCoverage=sorted(pcs),controls=controls,fields=fields,sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},scope='Complete182 physically selected small-axis Fourier loop over all actual exported CRT axes; canonical roots3/5/8, exact tags/state frames, active/skip branches. No complete large-axis recursive algorithm claim.')
(P/'small-axes-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}),flush=True)
