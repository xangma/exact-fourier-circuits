"""Literal161 from actual exported CRT metadata; exact values/tags/full frames."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import sys,json,hashlib,os
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import Poly,scalar,execute
print('host=mac cwd='+str(ROOT)+' pid='+str(os.getpid()),flush=True)
code=json.loads((P/'small-axis-program.json').read_text());assert len(code)==161
specPath=ROOT/'logs/uniform-bytecode/all-tensor-fibers/spec.json';specs=json.loads(specPath.read_text())
cases=[];pcs=set();steps=0;controls=[]
written={i[1] for i in code if i[0] in ('lit','add','sub','mul','div','mod','getnat')}
def state(spec,axis,D,power,family,salt):
 B=(spec['n']+2)**19;A,G,E,root=20000,40000,60000,80000;L=spec['L']
 s=dict(pc=0,nat=[(17*i+13+salt)%7000 for i in range(5010)],nh={B-7:31},
  sh={B-11:scalar(D,-2,3,True)},sr={i:scalar(D,F(i-5,3),F(11-i,7),i%2==0) for i in range(102)},
  out={3:scalar(D,7,-2)[0]},roots=[4,12])
 s['nat'][100:107]=[spec['nextPrime'],spec['n'],spec['ell'],L,spec['D'],spec['M'],spec['amount']]
 for z in range(spec['amount']):s['nh'][spec['M']+z]=0
 for j,v in enumerate(spec['primes']):s['nh'][spec['M']+j]=v
 for j,row in enumerate(spec['crt']):
  for f,v in enumerate(row):s['nh'][spec['M']+spec['ell']+4*j+f]=v
 for j,v in enumerate(spec['alpha']):s['nh'][spec['M']+spec['alphaBase']+j]=v
 for j,v in enumerate(spec['beta']):s['nh'][spec['M']+spec['betaBase']+j]=v
 for reg,v in [(4970,axis),(4971,A),(4972,G),(4973,E),(4975,root)]:s['nat'][reg]=v
 r=spec['radices'][axis];eta=Poly(D,{D//r:1}) if D%r==0 else Poly(D,{1:1})**power
 s['sh'][root]=(eta,False)
 for z in range(L):
  if family=='zero':v=scalar(D,dep=z%2==0)
  elif family=='prepared':v=scalar(D,F(z-7,5),F(13-z,9))
  elif family=='cancellation':v=scalar(D,(-1)**z,dep=z%3!=0)
  else:v=scalar(D,F(z-7,5),F(13-z,9),z%3==0)
  s['sh'][A+z]=v;s['sh'][G+z]=scalar(D,F(5-z,11),F(z+1,13),z%2==1)
  s['sh'][E+z]=scalar(D,100-z,z-100,True)
 return s,B,A,G,E,root,eta
for spec in specs:
 for ax in spec['axisSpecs']:
  for D in (4,8,12):
   for power in (1,2):
    for family in ('zero','prepared','cancellation','mixed'):
     for salt in (0,41):
      s,B,A,G,E,root,eta=state(spec,ax['axis'],D,power,family,salt)
      before=deepcopy(s);want=deepcopy(s['sh']);r,p,q=ax['r'],ax['P'],ax['Q'];count=p*q
      for j,row in enumerate(ax['positions']):
       for t,coord in enumerate(row):want[G+j*r+t]=before['sh'][A+coord]
       for k,coord in enumerate(row):
        val=Poly(D);dep=False
        for t,source in enumerate(row):
         val=val+eta**(k*t)*before['sh'][A+source][0];dep=dep or before['sh'][A+source][1]
        want[E+j*r+k]=want[A+coord]=(val,dep)
      copycost=count*(9*r+27)+7*ax['axis']+14
      time=2*copycost+count*((8*r+10)*r+14)+22
      ticks,coverage,peak=execute(code,s,B,time,D)
      assert ticks==time and s['pc']==160
      assert s['sh']==want,(spec['n'],ax['axis'],D,power,family,salt)
      for key in ('nh','out','roots'):assert s[key]==before[key],key
      for reg in range(len(s['nat'])):
       if reg not in written:assert s['nat'][reg]==before['nat'][reg],reg
      assert s['nat'][100:107]==before['nat'][100:107]
      for reg in range(102):
       if not 90<=reg<=95 and reg!=100:assert s['sr'].get(reg)==before['sr'].get(reg),reg
      pcs.update(coverage);steps+=ticks
      cases.append(dict(n=spec['n'],axis=ax['axis'],r=r,fibers=count,D=D,root='canonical' if D%r==0 else 'generic',power=power,family=family,salt=salt,steps=ticks,maximumWord=peak))
def reject(name,edit,budget=None):
 s,B,A,G,E,root,eta=state(specs[-1],1,12,1,'mixed',0);edit(s,specs[-1],A,G,E,root)
 try:execute(code,s,B,budget or 1000000,12)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted '+name)
reject('missing actual selected radix',lambda s,sp,A,G,E,root:s['nh'].pop(sp['M']+sp['ell']+4))
reject('zero actual divisor',lambda s,sp,A,G,E,root:s['nh'].__setitem__(sp['M']+sp['ell']+4,0))
reject('missing later source',lambda s,sp,A,G,E,root:s['sh'].pop(A+sp['L']-1))
reject('missing prepared root',lambda s,sp,A,G,E,root:s['sh'].pop(root))
reject('dependent root guard',lambda s,sp,A,G,E,root:s['sh'].__setitem__(root,(s['sh'][root][0],True)))
reject('charged budget',lambda *args:None,10)
assert pcs==set(range(161)),sorted(set(range(161))-pcs)
paths=[Path(__file__),P/'small-axis-program.json',ROOT/'verification/ExportSmallAxisFourierBytecode.lean',ROOT/'lean/UniformSmallAxisFourierMachine.lean',ROOT/'lean/UniformHeapDirectBatch.lean',ROOT/'lean/UniformHeapDirectFourier.lean',specPath,ROOT/'scripts/uniform_seed_cyclotomic_engine.py',ROOT/'lean/UniformAllTensorFibersCopyMachine.lean',ROOT/'lean/UniformSelectedAxisFiberPreparation.lean',ROOT/'lean/UniformTensorFiberCopyMachine.lean',ROOT/'lean/UniformMachine.lean']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=steps,pcCoverage=sorted(pcs),controls=controls,sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},scope='Complete161 selected-axis Fourier caller from actual exported metadata; generic/canonical roots, all native fibers, exact tags/full state frames. No all-length uniform algorithm claim.')
(P/'small-axis-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}),flush=True)
