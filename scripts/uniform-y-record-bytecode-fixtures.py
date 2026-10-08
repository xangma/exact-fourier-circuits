"""Exact continuous real opcode3 records: no interphase host writes."""
from pathlib import Path
from fractions import Fraction as F
import sys,copy,json,hashlib
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/y-record'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,add,mul
CODE=json.loads((P/'programs.json').read_text())['recordY']
assert len(CODE)==197
WRITES={0,1,3360,3368,3369,3370,3353,3354,3361,3362,3363,3365,3366}|set(range(1900,1909))|set(range(3350,3353))|set(range(3355,3360))|set(range(3371,3379))|set(range(3400,3431))|set(range(3440,3447))|set(range(2850,2877))|set(range(3302,3307))|set(range(3380,3388))
def yruntime(q,w):
 N=2**q;V=2**(q*w)
 return 4*q+10+(12*q+15)*N*N+9*q*w+(17*w+25)*V+31

def row(q,w,dirs):return [3,q,w,0,0,0,len(dirs),0]+[v for r,bits in dirs for v in [r]+[(bits>>j)&1 for j in range(w)]]
def runtime(q,w,count):return count*(yruntime(q,w)+11)+4*q*w+52
for e in json.loads((P/'spec.json').read_text()):
 for name,k in [('oneRow',1),('threeRows',3),('emptyRows',0)]:assert e[name]==runtime(e['q'],e['width'],k)
def fresh(D,q,w,R,dirs,salt):
 V=2**(q*w);N=2**q;A,E,T,PTR=100,10000,50000,30000
 s=dict(pc=0,nat=[(i*13+salt)%211 for i in range(3500)],nh={1:3,77:19,99000:7},
 sh={0:scalar(D,1,2),1:scalar(D,3,4,True),2:scalar(D,-9,7)},
 sr={0:scalar(D,7,-3,True),100:scalar(D,-11,5,True),114:scalar(D,13,17,True),200:scalar(D,5,-19)},
 out={3:scalar(D,-1,7)[0]},roots=[D,4])
 for r,v in {2850:PTR,3300:A,3364:E,3389:T}.items():s['nat'][r]=v
 s['nh'].update({PTR+j:v for j,v in enumerate(row(q,w,dirs))})
 for j in range(N*N):s['nh'][T+j]=(j*17+salt+101)%397
 for r in range(R):
  for j in range(V):s['sh'][A+r*V+j]=scalar(D,F(3*j+r+salt,7),F(2*j-3*r-salt,11),(j+r+salt)%3!=0)
 for j in range(V):s['sh'][E+j]=scalar(D,F(-13-j,3),F(5*j-salt,17),(j+salt)%2==0)
 for addr in (A-1,A+R*V,E-1,E+V):s['sh'][addr]=scalar(D,-13,5,True)
 return s

def reference(D,q,w,R,dirs,before):
 V=2**(q*w);want=copy.deepcopy(before['sh'])
 for r,bits in dirs:
  mask=sum(bits<<(c*w) for c in range(q))
  old=[want[100+r*V+j] for j in range(V)]
  for j in range(V):want[100+r*V+j]=old[j^mask];want[10000+j]=old[j^mask]
 return want
cases=[];pcs=set();ticks=0
for D in (4,12,32):
 for q,w in ((0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(4,1)):
  for salt in (0,31):
   seqs=[[],[(2,0)],[(1,(1<<w)-1)],[(0,1%(1<<w)),(2,(1<<w)-1),(0,1%(1<<w))]]
   for dirs in seqs:
    R=3;V=2**(q*w);N=2**q
    s=fresh(D,q,w,R,dirs,salt);before=copy.deepcopy(s)
    want=reference(D,q,w,R,dirs,before)
    count,seen,peak=execute(CODE,s,100000,runtime(q,w,len(dirs)),D)
    assert count==runtime(q,w,len(dirs)) and s['pc']==196
    assert s['nat'][2850]==30000+len(row(q,w,dirs))
    assert s['sh']==want,(D,q,w,dirs,salt)
    nh=copy.deepcopy(before['nh'])
    if dirs:nh.update({50000+j:(j//N)^(j%N) for j in range(N*N)})
    assert s['nh']==nh
    for k in ('roots','out'):assert s[k]==before[k]
    for r in range(3500):
     if r not in WRITES:assert s['nat'][r]==before['nat'][r],r
    for r in set(s['sr'])|set(before['sr']):
     if r not in (100,114):assert s['sr'].get(r)==before['sr'].get(r),r
    pcs.update(seen);ticks+=count;cases.append(dict(D=D,q=q,width=w,rows=dirs,salt=salt,steps=count,maxWord=peak))
# Empty role bank is meaningful only with no listed roles; real sizing still executes.
s=fresh(4,1,3,0,[],0);before=copy.deepcopy(s);cost=runtime(1,3,0)
c,seen,peak=execute(CODE,s,100000,cost,4);assert c==cost and s['sh']==before['sh'];cases.append(dict(D=4,q=1,width=3,roles=0,rows=[],steps=c,maxWord=peak));pcs.update(seen);ticks+=c
controls=[]
def reject(name,s,B=100000,fuel=1000000):
 try:execute(CODE,s,B,fuel,4)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted: '+name)
s=fresh(4,2,3,3,[(1,5)],0);del s['nh'][30009];reject('missing real bit descriptor',s)
s=fresh(4,2,3,3,[(1,5)],0);del s['nh'][30008];reject('missing real role field',s)
s=fresh(4,2,3,3,[(1,5)],0);del s['sh'][164];reject('missing role data',s)
s=fresh(4,2,3,3,[(1,5)],0);reject('insufficient charged fuel',s,fuel=runtime(2,3,1)-1)
s=fresh(4,2,3,3,[(1,5)],0);del s['nh'][30007];reject('missing actual header',s)
assert 196 in pcs and 194 in pcs and 76 in pcs
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(status='PASS',scope='actual continuous197 real opcode3 caller; ordinary original role array/tape and disjoint addresses only; generic phase and original width>=3 for linear absorption; no complete saving network or global DFT',exactCases=len(cases),chargedSteps=ticks,successfulPCs=len(pcs),coveredPCs=sorted(pcs),programInstructions=197,negativeControls=controls,cases=cases,sourceHash=sha(ROOT/'lean/UniformFixedNetworkYRecordMachine.lean'),programHash=sha(P/'programs.json'),fixtureHash=sha(Path(__file__)),engineHash=sha(ROOT/'scripts/uniform_seed_cyclotomic_engine.py'))
(P/'record-fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(cases),'exact continuous197 cases',ticks,'steps',len(pcs),'PCs',len(controls),'controls')
