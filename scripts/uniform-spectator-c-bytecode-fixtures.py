"""Exact diagnostics of the actual Lean-exported 69-instruction spectator suffix batch loop."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib, json, sys

ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar, execute, add, mul
CODE=json.loads((P/'spectator-program.json').read_text())
assert len(CODE)==69
assert all(i[0] not in ('root','input','output','putnat') for i in CODE)
CA=scalar(4,F(1,2),F(1,2)); CB=scalar(4,F(1,2),F(-1,2))
WRITES={0,1,2,2800,2801,2802,2803,2804,2805,2806,2810,2811,
        2820,2821,2822,2823,2824,2825,5209,5212,5207,5210,5205,5206,5208,5211}

def fresh(k,b,count,base,family,salt):
    s=dict(pc=0,nat=[(17*i+salt)%233 for i in range(5230)],
        nh={0:71,8000:37},sh={1:CA,2:CB},
        sr={i:scalar(4,F(i+2,7),F(9-i,11),True) for i in range(15)},
        out={7:scalar(4,11,-3)[0]},roots=[4,12])
    for r,value in ((5200,k),(5201,count),(5202,base),(5203,2**k),(5204,b)):
        s['nat'][r]=value
    for w in range(count):
        for z in range(2**k):
            if family=='zero':v=scalar(4,dep=(w+z)%2==0)
            elif family=='prepared':v=scalar(4,F(w-z+salt,11),F(z+3*w,13))
            elif family=='cancellation':v=scalar(4,(-1)**(z+w),dep=(w+z)%3!=0)
            else:v=scalar(4,F(3*z-7*w+salt,11),F(z+w+5,13),(z+salt+w)%2==0)
            s['sh'][base+w*2**k+z]=v
    for address in (base-1,base+count*2**k,9000):
        s['sh'][address]=scalar(4,-13,7,True)
    return s

def reference(k,b,values):
    out=[]
    for row in range(2**k):
        total=scalar(4)
        for col in range(2**k):
            if row%(2**b)!=col%(2**b): continue
            coefficient=scalar(4,1)
            for axis in range(b,k):
                coefficient=mul(coefficient,CA if ((row>>axis)&1)==((col>>axis)&1) else CB)
            total=add(total,mul(coefficient,values[col]))
        out.append(total)
    return out

cases=[];pcs=set();ticks=0
for k in range(6):
 for b in range(k+1):
  for count in (0,1,2,3,5):
   for base in (7,1000):
    for family in ('zero','prepared','cancellation','mixed'):
     s=fresh(k,b,count,base,family,31);before=deepcopy(s);expected=deepcopy(s['sh'])
     for w in range(count):
        values=[before['sh'][base+w*2**k+z] for z in range(2**k)]
        for z,value in enumerate(reference(k,b,values)):expected[base+w*2**k+z]=value
     cost=4*b+count*((k-b)*(25*2**max(k-1,0)+11)+18)+9
     steps,seen,peak=execute(CODE,s,10000,cost,4)
     assert steps==cost and s['pc']==68
     assert s['sh']==expected,(k,b,count,base,family)
     assert s['nat'][5209]==count and s['nat'][5205]==2**b
     for name in ('nh','out','roots'):assert s[name]==before[name],name
     for reg in range(len(s['nat'])):
        if reg not in WRITES:assert s['nat'][reg]==before['nat'][reg],reg
     for reg in set(s['sr'])|set(before['sr']):
        if reg>=8:assert s['sr'].get(reg)==before['sr'].get(reg),reg
     assert peak<=10000
     pcs.update(seen);ticks+=steps
     cases.append(dict(bits=k,startAxis=b,arrays=count,base=base,family=family,runtime=steps,peak=peak))
expectedPCs=set(range(69))-set(range(24,30))
assert pcs==expectedPCs,sorted(expectedPCs-pcs)
controls=[]
for missing in ('diagonal','offDiagonal','source'):
 s=fresh(2,1,3,1000,'mixed',31)
 del s['sh'][1 if missing=='diagonal' else 2 if missing=='offDiagonal' else 1000+2**2+1]
 try:execute(CODE,s,10000,10000,4)
 except (AssertionError,KeyError):controls.append(missing)
 else:raise AssertionError('missing bank accepted: '+missing)
s=fresh(2,1,3,1000,'mixed',31);s['sh'][1]=(CA[0],True)
try:execute(CODE,s,10000,10000,4)
except AssertionError:controls.append('dataDataGuard')
else:raise AssertionError('dependent constant accepted')
paths=[ROOT/'lean/UniformBinarySpectatorCMachine.lean',ROOT/'verification/ExportSpectatorCBytecode.lean',P/'spectator-program.json',
       Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,
    pcCoverage=sorted(pcs),controls=controls,
    sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
(P/'spectator-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))
