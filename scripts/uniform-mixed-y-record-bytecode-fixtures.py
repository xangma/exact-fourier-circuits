"""Independent exact reference for continuous535 actual four-opcode tapes.
No host intervention occurs between record selection and any child or return.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,copy,json,hashlib,itertools
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/y-record';sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,add,mul
CODE=json.loads((P/'programs.json').read_text())['mixedY'];assert len(CODE)==535
COEFS=[F(-1),F(-1,2),F(0),F(1,2),F(1)]
WRITES=set(range(2850,2877))|set(range(2900,2917))|set(range(3302,3309))|set(range(3310,3316))|set(range(3320,3342))|{0,1,2,2800,2801,2802,2803,2804,2805,2806,2810,2811,2820,2821,2822,2823,2824,2825,3360,3368,3369,3370,3353,3354,3361,3362,3363,3365,3366}|set(range(1900,1909))|set(range(3350,3353))|set(range(3355,3360))|set(range(3371,3379))|set(range(3400,3431))|set(range(3440,3447))|set(range(3380,3388))
def yruntime(q,w):
 N=2**q;V=2**(q*w)
 return 4*q+10+(12*q+15)*N*N+9*q*w+(17*w+25)*V+31

def row(q,w,it):
 op,*a=it
 if op==1:d,src,c=a;return [1,q,w,d,src,0,0,c]
 if op==5:d,count=a;return [5,q,w,d,count,0,0,0]
 if op==4:pairs=a[0];return [4,q,w,0,0,0,len(pairs),0]+[v for d,s in pairs for v in [d,s,4,0]]
 if op==3:dirs=a[0];return [3,q,w,0,0,0,len(dirs),0]+[v for d,bits in dirs for v in [d]+[(bits>>j)&1 for j in range(w)]]
 raise AssertionError(op)
def tensor(D,k,vs):
 A=scalar(D,F(1,2),F(1,2));B=scalar(D,F(1,2),F(-1,2));out=[]
 for r in range(2**k):
  acc=scalar(D)
  for c,v in enumerate(vs):
   coef=scalar(D,1)
   for ax in range(k):coef=mul(coef,A if ((r>>ax)&1)==((c>>ax)&1) else B)
   acc=add(acc,mul(coef,v))
  out.append(acc)
 return out

def fresh(D,q,w,R,items,salt):
 V=2**(q*w);N=2**q;A,E,T,PTR=100,10000,50000,30000
 data=[v for it in items for v in row(q,w,it)]
 s=dict(pc=0,nat=[(i*13+salt)%211 for i in range(3500)],nh={1:3,77:19,99000:7},
 sh={0:scalar(D,7,3,True),1:scalar(D,F(1,2),F(1,2)),2:scalar(D,F(1,2),F(-1,2))},
 sr={0:scalar(D,7,-3,True),100:scalar(D,-11,5,True),114:scalar(D,13,17,True),200:scalar(D,5,-19)},
 out={3:scalar(D,-1,7)[0]},roots=[D,4])
 for r,v in {2850:PTR,3301:PTR+len(data),3300:A,3364:E,3389:T}.items():s['nat'][r]=v
 s['nh'].update({PTR+j:v for j,v in enumerate(data)})
 for j in range(N*N):s['nh'][T+j]=(j*17+salt+101)%397
 for r in range(R):
  for j in range(V):s['sh'][A+r*V+j]=scalar(D,F(3*j+r+salt,7),F(2*j-3*r-salt,11),(j+r+salt)%3!=0)
 for j in range(V):s['sh'][E+j]=scalar(D,F(-13-j,3),F(5*j-salt,17),(j+salt)%2==0)
 for addr in (A-1,A+R*V,E-1,E+V):s['sh'][addr]=scalar(D,-13,5,True)
 return s

def reference(D,q,w,R,items,before):
 V=2**(q*w);want=copy.deepcopy(before['sh']);ticks=7;table=False
 for op,*args in items:
  if op==1:
   d,src,c=args
   for j in range(V):want[100+d*V+j]=add(want[100+d*V+j],mul(scalar(D,COEFS[c]),want[100+src*V+j]))
   ticks+=10*V+4*q*w+c+67
  elif op==5:
   first,count=args
   for r in range(first,first+count):
    out=tensor(D,q*w,[want[100+r*V+j] for j in range(V)])
    for j,v in enumerate(out):want[100+r*V+j]=v
   ticks+=count*(q*w*(25*2**max(q*w-1,0)+11)+15)+4*q*w+61
  elif op==4:
   pairs=args[0]
   for d,src in pairs:
    for j in range(V):
     a,b=want[100+d*V+j],want[100+src*V+j]
     want[100+d*V+j]=b;want[100+src*V+j]=(-a[0],a[1])
   ticks+=(10*V+21)*len(pairs)+4*q*w+59
  else:
   dirs=args[0]
   for r,bits in dirs:
    mask=sum(bits<<(c*w) for c in range(q));old=[want[100+r*V+j] for j in range(V)]
    for j in range(V):want[100+r*V+j]=old[j^mask];want[10000+j]=old[j^mask]
   ticks+=len(dirs)*(yruntime(q,w)+11)+4*q*w+59
   table|=bool(dirs)
 return want,ticks,table

for e in json.loads((P/'mixed-spec.json').read_text()):
 q,w=e['q'],e['width'];alt=sum((j%2)<<j for j in range(w))
 sample=[(1,0,1,k) for k in range(5)]+[(3,[(2,alt),(1,0),(2,alt)]),(4,[(0,1),(1,2)]),(5,0,3),(3,[]),(4,[]),(5,4,0)]
 assert e['data']==[v for it in sample for v in row(q,w,it)],'real Lean typed record differs from host reference'
 s=fresh(4,q,w,4,sample,0);assert reference(4,q,w,4,sample,s)[1]==e['runtime'],'actual Lean time mismatch'
cases=[];pcs=set();ticks=0
for D in (4,12,32):
 for q,w in ((0,0),(0,3),(1,0),(1,1),(2,1),(1,3),(2,3)):
  for salt in (0,31):
   R=4;V=2**(q*w);N=2**q;allbits=(1<<w)-1;one=1%(1<<w)
   small=[(1,0,1,4),(3,[(0,allbits),(2,0),(0,one)]),(4,[(0,1),(1,2)]),(5,0,2)]
   seqs=[[],[(3,[])],[(3,[(1,0)])],[(3,[(1,allbits)])],[(4,[])],[(5,R,0)],[(1,0,1,k) for k in range(5)],
    small,small[::-1],small+[small[1]],[(5,0,R),(3,[(2,allbits)]),(1,2,3,2),(4,[(2,1)]),(3,[(2,one)]),(5,3,1)]]
   # Different chronology is checked, rather than assuming commuting actions.
   if V<=8:seqs.extend(list(itertools.permutations(small)))
   for its in seqs:
    s=fresh(D,q,w,R,its,salt);before=copy.deepcopy(s);want,budget,table=reference(D,q,w,R,its,before)
    count,seen,peak=execute(CODE,s,100000,budget,D)
    assert count==budget and s['pc']==534 and s['nat'][2850]==before['nat'][3301]
    assert s['sh']==want,(D,q,w,its,salt)
    nh=copy.deepcopy(before['nh'])
    if table:nh.update({50000+j:(j//N)^(j%N) for j in range(N*N)})
    assert s['nh']==nh
    for k in ('roots','out'):assert s[k]==before[k]
    for r in range(3500):
     if r not in WRITES:assert s['nat'][r]==before['nat'][r],r
    for r in set(s['sr'])|set(before['sr']):
     if r>=115:assert s['sr'].get(r)==before['sr'].get(r),r
    pcs.update(seen);ticks+=count;cases.append(dict(D=D,q=q,width=w,records=its,salt=salt,steps=count,maxWord=peak))
controls=[]
def reject(name,s,B=100000,fuel=1000000):
 try:execute(CODE,s,B,fuel,4)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted: '+name)
for op in (0,2,6,7):
 s=fresh(4,1,3,4,[(1,0,1,4)],0);s['nh'][30000]=op;reject('unsupported opcode '+str(op),s)
s=fresh(4,1,3,4,[(3,[(1,5)])],0);del s['nh'][30009];reject('missing actual bit descriptor',s)
s=fresh(4,1,3,4,[(3,[(1,5)])],0);del s['sh'][108];reject('missing translated role data',s)
s=fresh(4,1,3,4,[(1,0,1,4)],0);s['nh'][30007]=5;reject('invalid scalar code',s)
s=fresh(4,1,3,4,[(5,0,2)],0);s['sh'][1]=(s['sh'][1][0],True);reject('prepared-data multiplication guard',s)
s=fresh(4,1,3,4,[(3,[(1,5)])],0);reject('charged runtime guard',s,fuel=100)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(status='PASS',scope='actual continuous535 real mixed opcode1/3/4/5; original present role bank/tape/prepared fixed C constants and disjoint ordinary address inputs; opcode0/2/6 and full recursion open',exactCases=len(cases),chargedSteps=ticks,successfulPCs=len(pcs),coveredPCs=sorted(pcs),programInstructions=535,negativeControls=controls,cases=cases,sourceHashes={m:sha(ROOT/'lean'/m) for m in ['UniformFixedNetworkYRecordMachine.lean','UniformFixedNetworkYRecordLoopMachine.lean']},programHash=sha(P/'programs.json'),specHash=sha(P/'mixed-spec.json'),fixtureHash=sha(Path(__file__)),engineHash=sha(ROOT/'scripts/uniform_seed_cyclotomic_engine.py'))
(P/'mixed-fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(cases),'exact continuous535 cases',ticks,'steps',len(pcs),'PCs',len(controls),'controls')
