"""Exact diagnostics of the actual Lean-exported heap Fourier22 bytecode."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib, json, sys
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import Poly, scalar, execute
CODE=json.loads((P/'direct-program.json').read_text())
assert len(CODE)==22
assert all(i[0] not in ('root','input','output','putnat') for i in CODE)
B=100000
def fresh(D,r,p,reverse,family):
    A,E=(3000,1000) if reverse else (1000,3000)
    eta=Poly(D,{1:1})**p
    s=dict(pc=0,nat=[(13*i+17)%233 for i in range(4900)],nh={0:71,8000:37},
        sh={0:scalar(D,19,-7,True),9000:(eta,False),B-1:scalar(D,-13,5)},
        sr={i:scalar(D,F(i+2,7),F(9-i,11),True) for i in range(100)},
        out={7:scalar(D,11,-3)[0]},roots=[D,12])
    for reg,val in ((4800,r),(4801,A),(4802,E),(4803,9000)):s['nat'][reg]=val
    for j in range(r):
        if family=='zero':v=scalar(D,dep=j%2==0)
        elif family=='prepared':v=(Poly(D,{1:1})**((3*j+1)%D),False)
        elif family=='cancellation':v=scalar(D,(-1)**j,F(j%3-1,3),j%3!=0)
        else:v=scalar(D,F(3*j-7,11),F(j+5,13),j%2==0)
        s['sh'][A+j]=v
        s['sh'][E+j]=scalar(D,100+j,-13-j,True)
    return s,A,E,eta
cases=[];pcs=set();total_steps=0
for D in (4,8,12):
 for r in range(9):
  for p in sorted(set((0,1,D//4,D//2,D-1))):
   for reverse in (False,True):
    for family in ('zero','prepared','cancellation','mixed'):
     s,A,E,eta=fresh(D,r,p,reverse,family);before=deepcopy(s)
     want=deepcopy(s['sh'])
     for k in range(r):
      value=Poly(D);dependent=False
      for j in range(r):
       value=value+(eta**(k*j))*before['sh'][A+j][0]
       dependent=dependent or before['sh'][A+j][1]
      want[E+k]=(value,dependent)
     runtime=(8*r+10)*r+6
     count,seen,peak=execute(CODE,s,B,runtime,D)
     assert count==runtime and s['pc']==21
     assert s['sh']==want,(D,r,p,reverse,family)
     for name in ('nh','out','roots'):assert s[name]==before[name],name
     for reg in range(4900):
      if reg not in range(4804,4808):assert s['nat'][reg]==before['nat'][reg],reg
     for reg in range(100):
      if reg not in range(90,96):assert s['sr'].get(reg)==before['sr'].get(reg),reg
     assert peak<=B
     pcs.update(seen);total_steps+=count
     cases.append(dict(D=D,width=r,rootPower=p,reverse=reverse,family=family,runtime=count,peak=peak))
assert pcs==set(range(22)),pcs
controls=[]
for missing in ('root','source'):
 s,A,E,eta=fresh(8,4,1,False,'mixed')
 del s['sh'][9000 if missing=='root' else A+2]
 try:execute(CODE,s,B,10000,8)
 except AssertionError as e:
  assert 'missing scalar' in str(e)
  controls.append(missing)
 else:raise AssertionError('missing bank accepted')
paths=[ROOT/'lean/UniformHeapDirectFourier.lean',ROOT/'verification/ExportHeapDirectFourierBytecode.lean',P/'direct-program.json',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=total_steps,
    pcCoverage=sorted(pcs),controls=controls,sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
(P/'direct-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))
