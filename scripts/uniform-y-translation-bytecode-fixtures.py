"""Exact tests of the exported continuous116 Y preparer; no interphase writes.
Entry has original data/descriptor and ordinary q,width,address headers only.
The table, mask, volume and translated output are created by actual instructions.
"""
from pathlib import Path
from fractions import Fraction as F
import sys, copy, json, hashlib
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/y-translation'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar, execute
CODE=json.loads((P/'programs.json').read_text())['preparedY']
assert len(CODE)==116
PAIRS=[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(4,1)]
WRITES={0,1,3368,3353,3354,3361,3362,3363,3365,3366}|set(range(1900,1909))|set(range(3350,3353))|set(range(3355,3360))|set(range(3371,3379))|set(range(3400,3431))|set(range(3440,3447))
def runtime(q,w):
 N=2**q;V=2**(q*w)
 return 4*q+10+(12*q+15)*N*N+9*q*w+(17*w+25)*V+31
for spec in json.loads((P/'spec.json').read_text()):
 assert spec['runtime']==runtime(spec['q'],spec['width'])

def fresh(q,w,direction,salt):
 V=2**(q*w);N=2**q;A,E,T,U=100,1000,5000,300
 s=dict(pc=0,nat=[(i*13+salt)%211 for i in range(3500)],nh={1:3,77:19,20000:7},
  sh={0:scalar(4,1,2),1:scalar(4,3,4,True),2:scalar(4,-9,7)},
  sr={0:scalar(4,7,-3,True),100:scalar(4,-11,5,True),114:scalar(4,13,17,True),200:scalar(4,5,-19)},
  out={3:scalar(4,-1,7)[0]},roots=[4,12])
 for r,val in {3420:q,3421:T,3369:w,3370:U,3360:A,3364:E}.items():s['nat'][r]=val
 for j in range(w):s['nh'][U+j]=(direction>>j)&1
 # Dirty prior table and buffer are deliberately wrong, including dependency tags.
 for j in range(N*N):s['nh'][T+j]=(j*17+salt+101)%397
 for j in range(V):
  s['sh'][A+j]=scalar(4,F(3*j+salt,7),F(2*j-salt,11),(j+salt)%3!=0)
  s['sh'][E+j]=scalar(4,F(-13-j,3),F(5*j-salt,17),(j+salt)%2==0)
 for addr in (A-1,A+V,E-1,E+V):s['sh'][addr]=scalar(4,-13,5,True)
 return s

cases=[];pcs=set();steps=0
for q,w in PAIRS:
 for direction in range(2**w):
  for salt in (0,31,73):
   s=fresh(q,w,direction,salt);before=copy.deepcopy(s)
   V=2**(q*w);N=2**q;A,E,T,U=100,1000,5000,300
   # Independent copied-direction reference from the original width descriptor.
   mask=sum(direction<<(c*w) for c in range(q))
   want=copy.deepcopy(before['sh'])
   for j in range(V):
    want[A+j]=before['sh'][A+(j^mask)]
    want[E+j]=before['sh'][A+(j^mask)]
   count,seen,peak=execute(CODE,s,100000,runtime(q,w),4)
   assert count==runtime(q,w) and s['pc']==115
   assert s['sh']==want,(q,w,direction,salt)
   nh=copy.deepcopy(before['nh']);nh.update({T+j:(j//N)^(j%N) for j in range(N*N)})
   assert s['nh']==nh
   assert s['nat'][3371]==mask and s['nat'][3375]==V
   assert s['nat'][3423]==N and s['nat'][3362]==V
   for name in ('out','roots'):assert s[name]==before[name],name
   for r in range(3500):
    if r not in WRITES:assert s['nat'][r]==before['nat'][r],r
   for r in set(before['sr'])|set(s['sr']):
    if r not in (100,114):assert s['sr'].get(r)==before['sr'].get(r),r
   pcs.update(seen);steps+=count
   cases.append(dict(q=q,width=w,direction=direction,salt=salt,steps=count,maxWord=peak))
assert pcs==set(range(116)),sorted(set(range(116))-pcs)
controls=[]
def rejects(name,s,B=100000,fuel=100000):
 try:execute(CODE,s,B,fuel,4)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted: '+name)
s=fresh(2,3,5,0);del s['nh'][301];rejects('missing original descriptor',s)
s=fresh(2,3,5,0);del s['sh'][107];rejects('missing original data',s)
s=fresh(4,1,1,0);s['nh']={k:v for k,v in s['nh'].items() if k<5000};rejects('generated table exceeds word bound',s,B=5100)
s=fresh(2,3,5,0);rejects('insufficient charged fuel',s,fuel=runtime(2,3)-1)
# Actual physical mask16 independently guards width division if wrong control jumps into empty width.
mask_code=json.loads((P/'programs.json').read_text())['mask']
s=fresh(1,0,0,0);s['pc']=7
try:execute(mask_code,s,100000,100,4)
except AssertionError:controls.append('zero-width branch bypass division')
else:raise AssertionError('zero-width invalid internal entry accepted')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(status='PASS',scope='continuous fixed116 caller from ordinary original data/descriptor; no actual saving-network/full-DFT claim',exactCases=len(cases),chargedSteps=steps,successfulPCs=len(pcs),programInstructions=116,negativeControls=controls,cases=cases,sourceHashes={name:sha(ROOT/'lean'/name) for name in ('UniformBlockXorMachine.lean','UniformXorTranslationMachine.lean','UniformRepeatedMaskMachine.lean','UniformPreparedYTranslationMachine.lean')},exportHash=sha(ROOT/'verification/ExportYBytecode.lean'),programHash=sha(P/'programs.json'),specHash=sha(P/'spec.json'),engineHash=sha(ROOT/'scripts/uniform_seed_cyclotomic_engine.py'),fixtureHash=sha(Path(__file__)))
(P/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','exactCases','chargedSteps','successfulPCs','programInstructions','negativeControls')},indent=2))
