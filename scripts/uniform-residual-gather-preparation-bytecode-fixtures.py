"""Exact finite diagnostics: continuous original-descriptor→gather bytecode.
No startup/full saving recursion claim. Independent native bit permutation.
"""
from pathlib import Path
from fractions import Fraction
import sys,json,copy,hashlib
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/residual-gather-preparation'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
CODES=json.loads((P/'programs.json').read_text())
assert len(CODES['permutation'])==188 and len(CODES['gather'])==210 and len(CODES['copy'])==16
CASES=[(q,m,d) for q,m in [(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)] for d in range(1,2**m)]
U,I,S,O,T,A,D=100,1000,2000,3000,10000,20000,30000
B=1000000

def phi(q,m,direction,j):
 p=(direction & -direction).bit_length()-1
 selected=j%(2**q);rep=j//(2**q)
 result=0
 for c in range(q):
  r=(rep>>(c*(m-1)))&((1<<(m-1))-1)
  column=(r&((1<<p)-1))|((r>>p)<<(p+1))
  if (selected>>c)&1:column^=direction
  result|=column<<(c*m)
 return result

def tree(m,k):return (17*m+67)*2**k-(17*m+62)
def cost(q,m,d):
 p=(d&-d).bit_length()-1
 rounds=sum(6+(5 if j%m==0 else 1)+(7 if j%m<p else 9 if p<j%m else 2) for j in range(q*m))
 descriptor=40+6*p+9*m+rounds
 return descriptor+4*q+10+(12*q+15)*4**q+tree(m,q*m)+17

def fresh(q,m,d,salt):
 N=2**q;V=2**(q*m)
 s=dict(pc=0,nat=[(r*19+salt)%199 for r in range(4300)],nh={7:4,77:9,99999:31},
  sh={0:scalar(4,3,5,True),7:scalar(4,-3,11)},sr={0:scalar(4,7,13,True),120:scalar(4,-17,19,True),250:scalar(4,23,-29)},
  out={4:scalar(4,31,37)[0]},roots=[4,12])
 for r,val in {4060:q,4061:m,4062:U,4063:I,4066:S,4067:O,4068:T,4090:A,4091:D}.items():s['nat'][r]=val
 for j in range(m):s['nh'][U+j]=(d>>j)&1
 for j in range(q*m):s['nh'][I+j]=191
 for j in range(2*q*m):s['nh'][S+j]=193
 for j in range(V):s['nh'][O+j]=197
 for j in range(N*N):s['nh'][T+j]=199
 for j in range(V):
  s['sh'][A+j]=scalar(4,Fraction(3*j+salt,7),Fraction(5*j-salt,11),(j+salt)%3!=0)
  s['sh'][D+j]=scalar(4,Fraction(-13-j,17),Fraction(19*j+salt,23),(j+salt)%2==0)
 for a in (A-1,A+V,D-1,D+V):s['sh'][a]=scalar(4,-41,43,True)
 return s

seen={key:set() for key in CODES};results=[];steps=0
for q,m,d in CASES:
 for salt in (0,17):
  V=2**(q*m);N=2**q;p=(d&-d).bit_length()-1
  for kind in ('permutation','gather'):
   s=fresh(q,m,d,salt);before=copy.deepcopy(s)
   ticks=cost(q,m,d)+(11*V+10 if kind=='gather' else 0)
   t,pcs,peak=execute(CODES[kind],s,B,ticks,4)
   assert t==ticks and s['pc']==len(CODES[kind])-1
   assert s['nat'][4023]==V and s['nat'][4069]==1
   expected=list(map(lambda j:phi(q,m,d,j),range(V)))
   assert sorted(expected)==list(range(V))
   assert [s['nh'][O+j] for j in range(V)]==expected
   for c in range(q):assert s['nh'][I+c]==d<<(c*m)
   for c in range(q):
    for i in range(m):
     if i!=p:assert s['nh'][I+q+c*(m-1)+(i if i<p else i-1)]==1<<(c*m+i)
   assert [s['nh'][T+j] for j in range(N*N)]==[(j//N)^(j%N) for j in range(N*N)]
   for z in set(before['nh'])|set(s['nh']):
    if not (I<=z<T+N*N):assert s['nh'].get(z)==before['nh'].get(z)
   assert [s['nh'][U+i] for i in range(m)]==[(d>>i)&1 for i in range(m)]
   want=copy.deepcopy(before['sh'])
   if kind=='gather':
    for j in range(V):want[D+j]=before['sh'][A+expected[j]]
   assert s['sh']==want,(q,m,d,kind)
   for name in ('out','roots'):assert s[name]==before[name]
   for r in range(4300):
    if not(3350<=r<=3446 or 4000<=r<=4081):assert s['nat'][r]==before['nat'][r]
   for r in set(before['sr'])|set(s['sr']):
    if not(kind=='gather' and r==120):assert s['sr'].get(r)==before['sr'].get(r)
   seen[kind].update(pcs);steps+=t
   if kind=='gather':seen['copy'].update(i-193 for i in pcs if 193<=i<209)
   results.append(dict(kind=kind,q=q,width=m,direction=d,salt=salt,steps=t,maxWord=peak))
   if kind=='gather':
    # Caller test of the copy helper only: separately labelled header installation.
    cs=copy.deepcopy(s);cs['pc']=0
    for r,val in {4070:V,4071:O,4072:D,4073:A,4074:1}.items():cs['nat'][r]=val
    t,pcs,peak=execute(CODES['copy'],cs,B,10*V+4,4)
    assert t==10*V+4 and cs['sh']=={**s['sh'],**{A+j:before['sh'][A+j] for j in range(V)}}
    seen['copy'].update(pcs);steps+=t
controls=[]
def rejects(name,s,code='gather',fuel=100000,B=B):
 try:execute(CODES[code],s,B,fuel,4)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('accepted '+name)
s=fresh(2,3,5,0);del s['nh'][U+1];rejects('missing original descriptor',s)
s=fresh(2,3,5,0);del s['sh'][A+7];rejects('missing original data',s)
s=fresh(2,3,5,0);rejects('insufficient fuel',s,fuel=cost(2,3,5)+11*64+9)
s=fresh(2,3,0,0);rejects('zero direction violates pivot contract',s)
report=dict(status='PASS',scope='original descriptor fixed188 and continuous gather210; inverse scatter16 helper; no recursive child/global DFT claim',
 exactCases=len(results)+len(CASES)*2,chargedSteps=steps,negativeControls=controls,programPCs={k:len(v) for k,v in seen.items()},
 missingPCs={k:sorted(set(range(len(CODES[k])))-v) for k,v in seen.items()},cases=results)
(P/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
