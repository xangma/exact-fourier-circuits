"""Actual exported direct-batch and translated-row bytecode; exact state checks."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,Poly,execute
def fresh():
    return dict(pc=0,nat=[(13*i+17)%233 for i in range(5010)],
        nh={0:71,9000:37},sh={1:scalar(4,7,-3,True),9999:scalar(4,-13,5)},
        sr={i:scalar(4,F(i+2,7),F(9-i,11),True) for i in range(105)},
        out={7:scalar(4,11,-3)[0]},roots=[4,12])
def finish(name,code,cases,ticks,pcs,controls,paths):
    assert pcs==set(range(len(code))),sorted(set(range(len(code)))-pcs)
    paths=paths+[Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']
    receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,
        pcCoverage=sorted(pcs),controls=controls,
        sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (P/(name+'-fixtures.json')).write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
    print(name,json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))

CODE=json.loads((P/'direct-batch-program.json').read_text());assert len(CODE)==34
assert all(i[0] not in ('root','input','output','putnat') for i in CODE)
cases=[];pcs=set();ticks=0
for r in range(9):
 for count in (0,1,2,5):
  for p in (0,1,2,3):
   for reverse in (False,True):
    for family in ('zero','prepared','cancellation','mixed'):
     A,D=(3000,1000) if reverse else (1000,3000)
     s=fresh();eta=Poly(4,{1:1})**p;s['sh'][8000]=(eta,False)
     for reg,value in ((4950,r),(4951,count),(4952,A),(4953,D),(4954,8000)):
        s['nat'][reg]=value
     for w in range(count):
      for j in range(r):
        if family=='zero':v=scalar(4,dep=(w+j)%2==0)
        elif family=='prepared':v=scalar(4,F(3*j-w,7),F(j+2*w,11))
        elif family=='cancellation':v=scalar(4,(-1)**j,dep=(w+j)%3!=0)
        else:v=scalar(4,F(3*j-7*w,11),F(j+w+5,13),(w+j)%2==0)
        s['sh'][A+w*r+j]=v;s['sh'][D+w*r+j]=scalar(4,100+j,-13-w,True)
     before=deepcopy(s);want=deepcopy(s['sh'])
     for w in range(count):
      for k in range(r):
        val=Poly(4);dep=False
        for j in range(r):
            val=val+(eta**(k*j))*before['sh'][A+w*r+j][0]
            dep=dep or before['sh'][A+w*r+j][1]
        want[D+w*r+k]=(val,dep)
     runtime=count*((8*r+10)*r+14)+5
     steps,seen,peak=execute(CODE,s,10000,runtime,4)
     assert steps==runtime and s['pc']==33
     assert s['sh']==want,(r,count,p,reverse,family)
     for key in ('nh','out','roots'):assert s[key]==before[key],key
     for reg in range(len(s['nat'])):
        if not 4800<=reg<=4807 and not 4955<=reg<=4958:
            assert s['nat'][reg]==before['nat'][reg],reg
     for reg in range(105):
        if not 90<=reg<=95:assert s['sr'].get(reg)==before['sr'].get(reg),reg
     pcs.update(seen);ticks+=steps
     cases.append(dict(radix=r,arrays=count,rootPower=p,reverse=reverse,family=family,runtime=steps,peak=peak))
finish('direct-batch',CODE,cases,ticks,pcs,[],[ROOT/'lean/UniformHeapDirectBatch.lean',ROOT/'lean/UniformHeapDirectFourier.lean',ROOT/'verification/ExportHeapDirectBatchBytecode.lean',P/'direct-batch-program.json'])

