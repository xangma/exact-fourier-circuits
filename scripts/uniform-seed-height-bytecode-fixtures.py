"""Actual empty935 -> caller Args -> continuous1046. No interphase writes.
Exact true cyclotomic arithmetic imported immutably from frozen835 engine.
"""
from pathlib import Path
import copy,json,sys,hashlib
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/seed-height'
OLD=P.parent/'seed-rank-cross'
from uniform_seed_cyclotomic_engine import Poly,F,scalar,execute,direct_dft
code=json.loads((P/'program.json').read_text());models=json.loads((P/'models.json').read_text())
startup=json.loads((OLD/'startup.json').read_text());seedcode=json.loads((OLD/'program.json').read_text())
assert len(code)==1046 and len(startup)==935
assert all(i[0] not in ['root','input','output'] for i in code)
def relocate(ins,base,ret):
 op,*a=ins
 if op=='halt':return ['jump',ret]
 if op=='jump':a[0]+=base
 if op=='branch':a[2]+=base;a[3]+=base
 return [op,*a]
assert code[11:846]==[relocate(i,11,846) for i in seedcode]
hraw=json.loads((P.parent/'cross-height/program.json').read_text())
ops=['add','sub','mul','div','mod'];height=[]
for op,*a in hraw:
 if op==0:height.append(['lit',*a])
 elif op==1:height.append([ops[a[0]],*a[1:]])
 else:height.append([{2:'getnat',3:'putnat',4:'branch',5:'jump',6:'halt'}[op],*a])
assert code[859:1045]==[relocate(i,859,1045) for i in height]
assert code[1045]==['halt']

def seed_values(D,r):
 eta=Poly(D,{1:1});omega=eta**(D//r);H=[Poly(D,{0:1})];scale=[Poly(D,{0:1})]
 for j in range(1,r):
  H.append(H[-1]*(Poly(D,{0:1})-omega**j));scale.append(scale[-1]*-(omega**(j-1)))
 h=[v.inverse() for v in H];g=[Poly(D,{0:1})]
 for j in range(1,r):
  val=Poly(D)
  for u in range(1,j+1):val=val+h[u]*g[j-u]
  g.append(-val)
 return [H,scale,[(v*w).inverse() for v,w in zip(H,scale)],h,g]
def greedy(rows):
 colors=[]
 for i,(d,s,c) in enumerate(rows):
  used={colors[j] for j,(x,y,_) in enumerate(rows[:i]) if d in (x,y) or s in (x,y)}
  colors.append(next((c for c in range(11) if c not in used),11))
 return colors
starts={};startcases=[]
for n in [1,4]:
 m=next(m for m in models if m['n']==n);D=m['masterOrder'];B=(n+2)**19
 for dirty in [0,1]:
  st={'pc':0,'nat':[0]*1240,'sr':{},'nh':{},'sh':{},'out':{},'roots':[]}
  inp=[scalar(D,0 if dirty else i+1,0 if dirty else 2-i)[0] for i in range(n)]
  steps,pcs,peak=execute(startup,st,B,100000,D,n,inp)
  base=m['poolEnd']-5*sum(m['radices'])
  assert st['roots']==[D] and st['sh'][0]==(Poly(D,{1:1}),False)
  for j,r in enumerate(m['radices']):
   assert st['nh'][m['directoryBase']+2*j]==base and st['nh'][m['directoryBase']+2*j+1]==r
   val=seed_values(D,r)
   for q in range(5):assert [st['sh'][base+q*r+i] for i in range(r)]==[(v,False) for v in val[q]]
   base+=5*r
  assert base==m['poolEnd'];starts[n,dirty]=st
  startcases.append(dict(n=n,dirty=dirty,steps=steps,maximumWord=peak,rootOrder=D))
  print('actual935',n,dirty,steps,flush=True)
summary=[];pcsall=set();total=0;saved=None
for m in models:
 n,j,a,e,K,r,D=[m[k] for k in ['n','axis','a','e','height','radix','masterOrder']]
 assert K==(2*(a+e)-1).bit_length();N=1<<K;H=8*K+7;G=3*K*N//2;Gconv=3*K*N+2*N;T=6*Gconv+2*a
 split,i0,j0=m['split'],m['i0'],m['j0'];rows=m['rows'];assert len(rows)==T
 for dirty in [0,1]:
  S,A,d,C,V,tape,depth,Q,R=(1000,2000,30000,10000,40000,100000,200000,1000000,2000000) if dirty==0 else (2000,4000,70000,20000,100000,300000,400000,2000000,3000000)
  TN=2*C;CP=TN+7*N+100;RD=R+T+100;FC=RD+6*T*H+100;U=FC+2*T*H+100;J=U+100
  B=(n+2)**19;enabled=bool(dirty);HB=m['axisBase']+3*r;GB=m['axisBase']+4*r
  st=copy.deepcopy(starts[n,dirty]);st['pc']=0
  for q in range(160,1240):st['nat'][q]=17*q+dirty
  for q in range(100):st['sr'][q]=scalar(D,q-2,3-q,q%2)
  headers={1120:j,1122:a,1123:e,1124:i0,1125:j0,1126:split,1127:S,1128:A,1129:d,1130:C,1131:V,1132:tape,1133:depth,1134:Q,1135:R,1136:TN,1137:CP,1220:RD,1221:FC,1222:U,1223:J,1224:int(enabled)}
  for q,v in headers.items():st['nat'][q]=v
  st['nat'][1121]=12345+dirty # deliberately stale; not an entry argument
  for q in list(range(S,S+6*N))+list(range(C,C+7*N+1))+list(range(TN,TN+7*N))+list(range(CP,CP+6)):
   st['sh'][q]=scalar(D,q-3,11-q,True)
  for q in [d,V,tape,depth,Q,R,RD,FC,U,J,9000000]:st['nh'][q]=q+19+dirty
  st['sh'][9000000]=scalar(D,-7,3,True);st['out'][0]=scalar(D,7+dirty,-2)[0]
  before=copy.deepcopy(st)
  steps,pcs,peak=execute(code,st,B,m['runtimeBudget'],D,n)
  assert st['pc']==1045 and st['nat'][1121]==K and st['nat'][1050]==K
  assert st['nat'][1229]==N and st['nat'][1071]==N and st['nat'][1072]==T and st['nat'][1073]==H and st['nat'][1074]==H
  h=[before['sh'][HB+i][0] for i in range(r)];g=[before['sh'][GB+i][0] for i in range(r)]
  def matrix(i,j):
   acc=Poly(D)
   for u in range(split-(j0+j)):acc=acc+h[i0+i-(j0+j)-u]*g[u]
   return acc
  v=[-h[i0+i-split] for i in range(a)];w=[g[split-(j0+j)] for j in range(e)]
  row=[matrix(0,j)-v[0]*w[j] for j in range(e)];col=[Poly(D) if i==0 else matrix(i,0)-v[i]*w[0] for i in range(a)]
  delta=[Poly(D,{0:1})]+[Poly(D) for _ in range(N-1)]
  kernels=[[(arr[i] if i<len(arr) else Poly(D),False) for i in range(N)] for arr in [w,v,row,delta,delta,col]]
  for b in range(6):assert [st['sh'][S+b*N+i] for i in range(N)]==kernels[b]
  omega=Poly(D,{1:1})**(D//N);expected=[(omega**i,False) for i in range(N)]
  for kernel in kernels:expected.extend(direct_dft(omega,kernel))
  assert [st['sh'][C+i] for i in range(7*N)]==expected
  assert st['sh'][C+7*N]==(omega,False)
  assert [st['sh'][TN+i] for i in range(7*N)]==[(-v,False) for v,_ in expected]
  assert [st['sh'][CP+i] for i in range(6)]==[scalar(D,z) for z in [1,-1,F(1,N),F(-1,N),F(5,4),F(4,5)]]
  labels=[0]*(e+1)
  for i,row in enumerate(rows):
   assert [st['nh'].get(tape+5*i+b) for b in range(5)]==row
   op,lft,rgt,kind,pay=row;labels.append((max(labels[lft],labels[rgt]) if op<2 else labels[lft])+1)
  assert [st['nh'][depth+i] for i in range(e+1+T)]==labels
  order=sorted(range(T),key=lambda i:(labels[e+1+i],i))
  assert [st['nh'][Q+i] for i in range(T)]==order
  assert [st['nh'][R+i] for i in range(T+2)]==[sum(labels[e+1+q]<i for q in range(T)) for i in range(T+2)]
  buckets=[[] for _ in range(H)]
  for i in order:
   op,lft,rgt,kind,pay=rows[i];dst=e+1+i;level=labels[dst]
   def emit(src,coef):
    if (src<e and enabled) or src>e:buckets[level].append([dst,src,coef])
   if op<2:emit(lft,CP);emit(rgt,CP+op)
   else:emit(lft,C+pay if kind==1 else CP if pay<2 else CP+2)
  for level,W in enumerate(buckets):
   colors=greedy(W);assert all(c<11 for c in colors)
   rb=RD+6*T*level;fb=FC+2*T*level
   assert [st['nh'][rb+3*i+b] for i in range(len(W)) for b in range(3)]==[v for row in W for v in row]
   assert [st['nh'][fb+i] for i in range(len(W))]==colors
   assert [st['nh'][J+3*level+b] for b in range(3)]==[len(W),rb,fb]
   assert all(not({W[i][0],W[i][1]} & {W[j][0],W[j][1]}) for i in range(len(W)) for j in range(i) if colors[i]==colors[j])
  for q in range(m['directoryEnd']):assert st['nh'].get(q)==before['nh'].get(q)
  for q in range(m['poolEnd']):assert st['sh'].get(q)==before['sh'].get(q)
  for q in range(100,107):assert st['nat'][q]==before['nat'][q]
  for q in headers:assert st['nat'][q]==before['nat'][q]
  assert st['out']==before['out'] and st['roots']==before['roots']
  for q in set(before['sh'])|set(st['sh']):
   RA=A+N+G+5*N+4
   if (q<S or S+6*N<=q) and (q<A or RA+1<=q) and (q<C or C+7*N+1<=q) and (q<TN or TN+7*N<=q) and (q<CP or CP+6<=q):assert st['sh'].get(q)==before['sh'].get(q)
  regions=[(d,3*G),(V,5*Gconv),(tape,5*T),(depth,e+1+T),(Q,T*(T+1)),(R,T+2),
           (RD,6*T*H),(FC,2*T*H),(U,12),(J,3*H)]
  for q in set(before['nh'])|set(st['nh']):
   if all(q<base or base+length<=q for base,length in regions):assert st['nh'].get(q)==before['nh'].get(q)
  total+=steps;pcsall.update(pcs)
  summary.append(dict(n=n,axis=j,radix=r,K=K,a=a,e=e,enabled=enabled,steps=steps,maximumWord=peak,rootOrder=D,maximumDepth=max(labels),runtimeBudget=m['runtimeBudget']))
  print('continuous1046',len(summary),n,j,K,a,e,enabled,steps,flush=True)
  if n==4 and r==3 and a==2 and dirty==0:saved=(before,D,B,HB,GB,m['directoryBase']+2*j,m['runtimeBudget'])
controls=[];before,D,B,HB,GB,axis,budget=saved
for name,bank,addr in [('missing-axis-offset','nh',axis),('missing-axis-width','nh',axis+1),('missing-H','sh',HB+1),('missing-G','sh',GB+1),('missing-master','sh',0)]:
 bad=copy.deepcopy(before);del bad[bank][addr]
 try:execute(code,bad,B,budget,D)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
for name,mut,limit in [('word-guard',lambda s:s['nat'].__setitem__(1220,B+1),budget),('step-budget',lambda s:None,10),('data-data-guard',lambda s:[s['sh'].__setitem__(p,(s['sh'][p][0],True)) for p in [HB,HB+1,HB+2,GB,GB+1,GB+2]],budget)]:
 bad=copy.deepcopy(before);mut(bad)
 try:execute(code,bad,B,limit,D)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
mutant=copy.deepcopy(code);mutant[2]=['jump',3];bad=copy.deepcopy(before)
try:execute(mutant,bad,B,budget,D)
except (AssertionError,KeyError):controls.append('sizing-counter-reset-mutation')
else:raise AssertionError('counter reset mutation accepted')
new=set(range(11))|set(range(846,859))|{1045}
assert new<=pcsall
result=dict(status='PASS',programSHA256=hashlib.sha256((P/'program.json').read_bytes()).hexdigest(),engineSHA256=hashlib.sha256((Path(__file__).resolve().parent/'uniform_seed_cyclotomic_engine.py').read_bytes()).hexdigest(),startupSHA256=hashlib.sha256((OLD/'startup.json').read_bytes()).hexdigest(),instructions=1046,startupInstructions=935,startupCases=startcases,exactCases=len(summary),chargedSteps=total,visitedPCs=len(pcsall),unvisitedPCs=sorted(set(range(1046))-pcsall),allNewPCsVisited=True,negativeControls=controls,cases=summary,
 arithmetic='Frozen true cyclotomic Q[eta]/Phi128 and Q[eta]/Phi24576; no floats; every inverse product checked.',
 scope='Actual935 builds retained H/G/master. Separate ordinary caller Args installed;1121 deliberately dirty. Entire sizing→835→header13→Height186→halt1046 executes continuously. No generated banks/rows/order or interphase writes supplied. Full global FFT scheduler and initial→caller installation remain separate.')
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','exactCases','chargedSteps','visitedPCs','allNewPCsVisited','negativeControls']},indent=2))
