import copy,json,random,hashlib
from fractions import Fraction as Q
from pathlib import Path
r=Path(__file__).resolve().parents[1]/"logs/uniform-bytecode/machine-conjugation"
zero=(Q(0),Q(0),False)
def conjv(v):return(v[0],-v[1],v[2])
def conj(s):
 s=copy.deepcopy(s);s['sr']={j:conjv(v) for j,v in s['sr'].items()};s['sh']={j:conjv(v) for j,v in s['sh'].items()};s['out']={j:(a,-b) for j,(a,b) in s['out'].items()};return s
def word(s,B):return s['pc']<=B and all(v<=B for v in s['nr'].values()) and all(j<=B and v<=B for j,v in s['nh'].items()) and all(j<=B for j in s['sh']) and all(j<=B for j in s['out']) and all(d<=B for d in s['roots'])
def step(code,n,s):
 s=copy.deepcopy(s);pc=s['pc'];nr=s['nr'];sr=s['sr'];nh=s['nh'];sh=s['sh']
 if not 0<=pc<len(code):return 'failed',None
 op,*v=code[pc];s['pc']+=1
 if op==6:s['pc']=pc;return'halted',s
 if op==0:d,a=v;nr[d]=a
 elif op==1:
  k,d,l,h=v;a,b=nr.get(l,0),nr.get(h,0)
  if k in (3,4) and b==0:return'failed',None
  nr[d]=[lambda:a+b,lambda:max(0,a-b),lambda:a*b,lambda:a//b,lambda:a%b][k]()
 elif op==2:
  d,a=v;a=nr.get(a,0)
  if a not in nh:return'failed',None
  nr[d]=nh[a]
 elif op==3:a,d=v;nh[nr.get(a,0)]=nr.get(d,0)
 elif op==4:l,h,y,no=v;s['pc']=y if nr.get(l,0)<nr.get(h,0) else no
 elif op==5:s['pc']=v[0]
 elif op==7:
  d,a=v;a=nr.get(a,0)
  if a not in sh:return'failed',None
  sr[d]=sh[a]
 elif op==8:a,d=v;sh[nr.get(a,0)]=sr.get(d,zero)
 elif op==9:d,num,den=v;sr[d]=(Q(num,den),Q(0),False)
 elif op==10:
  k,d,l,h=v;a,b,da=sr.get(l,zero);c,e,db=sr.get(h,zero)
  if k==0:z=(a+c,b+e,da or db)
  elif k==1:z=(a-c,b-e,da or db)
  elif k==2:
   if da and db:return'failed',None
   z=(a*c-b*e,a*e+b*c,da or db)
  else:
   if da or db or c==e==0:return'failed',None
   norm=c*c+e*e;z=((a*c+b*e)/norm,(b*c-a*e)/norm,False)
  sr[d]=z
 elif op==11:nr[v[0]]=n
 elif op==14:
  j,d=v;j=nr.get(j,0)
  if j>=n:return'failed',None
  s['out'][j]=sr.get(d,zero)[:2]
 else:raise AssertionError('External input/root instruction outside permitted scope')
 return'running',s
code=json.loads((r/'program.json').read_text());instructions=json.loads((r/'instructions.json').read_text())
allowed=json.loads((r/'allowed.json').read_text());assert allowed==[True]*20+[False]*2
assert len(code)==29 and len(instructions)==20
rng=random.Random(9401);checks=0;failures=0
for inst in instructions:
 for i in range(100):
  n=i%4;s=dict(pc=0,nr={j:rng.randrange(8) for j in range(13)},sr={j:(Q(rng.randrange(-3,4),3),Q(rng.randrange(-3,4),5),bool(rng.randrange(2))) for j in range(8)},nh={j:rng.randrange(9) for j in range(5)},sh={j:(Q(rng.randrange(-3,4),7),Q(rng.randrange(-3,4),11),bool(rng.randrange(2))) for j in range(5)},out={0:(Q(3),Q(2))},roots=[8,16])
  if i%5==0:s['sr'][2]=zero
  result,u=step([inst],n,s);result2,v=step([inst],n,conj(s))
  assert result==result2 and(v==conj(u) if u else v is None)
  assert conj(conj(s))==s and word(s,50)==word(conj(s),50)
  checks+=1;failures+=result=='failed'
traces=[];seen=set()
for family in range(48):
 n=family%5;s=dict(pc=0,nr={j:rng.randrange(300) for j in range(20)},sr={j:(Q(rng.randrange(-4,5),3),Q(rng.randrange(-4,5),7),bool(rng.randrange(2))) for j in range(10)},nh={200:37},sh={100:(Q(family%4),Q((family%3)-1),False),101:(Q(2),Q(-3),family%2==0),102:(Q(91),Q(93),True),103:(Q(97),Q(99),True),200:(Q(13),Q(17),True)},out={2:(Q(7),Q(9))},roots=[64])
 initial=copy.deepcopy(s);v=conj(s);ticks=0;pcs=set()
 while ticks<100:
  pcs.add(s['pc']);res,u=step(code,n,s);res2,w=step(code,n,v)
  assert res==res2 and(w==conj(u) if u else w is None);ticks+=1
  if res!='running':break
  s,v=u,w;assert word(s,1000)==word(v,1000)
 else:raise AssertionError('nontermination')
 traces.append(dict(family=family,n=n,ticks=ticks,outcome=res));seen|=pcs
 if res=='halted':
  assert u['nh']==w['nh'] and u['nr']==w['nr'] and u['roots']==initial['roots']
  assert ticks==28 and u['pc']==28
# Root and input negative scope controls: an unchanged nonreal supply breaks simulation.
external=(Q(0),Q(1),False)
assert external!=conjv(external)
base=dict(pc=0,nr={1:7,2:0},sr={1:(Q(1),Q(0),False),2:zero},nh={},sh={},out={},roots=[])
controls=[]
for label,program,n,state in [
 ('missing instruction',[],2,base),
 ('missing Nat read',[[2,0,1]],2,base),
 ('missing Scalar read',[[7,0,1]],2,base),
 ('zero Nat divisor',[[1,3,0,1,2]],2,base),
 ('zero prepared complex denominator',[[10,3,0,1,2]],2,base),
 ('dependent division operand',[[10,3,0,1,2]],2,{**base,'sr':{1:(Q(1),Q(2),True),2:(Q(1),Q(0),False)}}),
 ('two dependent multiply operands',[[10,2,0,1,2]],2,{**base,'sr':{1:(Q(1),Q(2),True),2:(Q(1),Q(0),True)}}),
 ('output index out of range',[[14,1,2]],2,base)]:
 assert step(program,n,state)==('failed',None) and step(program,n,conj(state))==('failed',None)
 controls.append(dict(name=label,original='failed',reflected='failed'))
report=dict(status='PASS',cases=checks+len(traces),one_step_cases=checks,one_step_failed_outcomes=failures,continuous_cases=len(traces),continuous_ticks=sum(t['ticks'] for t in traces),allowed_constructor_cases=len(instructions),program_pcs=sorted(seen),unvisited_fixture_pcs=sorted(set(range(29))-seen),guard_classes=controls,external_supply_exclusion_controls=['Unchanged nonreal input supply does not commute','Fresh canonical nonreal root supply does not commute'],cases_detail=traces,program_sha256=hashlib.sha256((r/'program.json').read_bytes()).hexdigest(),instructions_sha256=hashlib.sha256((r/'instructions.json').read_bytes()).hexdigest(),scope='Semantic reflection diagnostics using paired virtual initial states; not a physical conjugated-state producer or new RAM primitive. Generic Lean proof covers all admitted programs and tick counts.')
(r/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n');print({k:v for k,v in report.items() if k!='cases_detail'})
