"""Fresh literal835 with sources produced by actual empty-state935.
Between the two separate programs, the caller interface installs ordinary Args
and dirty fresh workspace only. No H/G/master/phase-output host writes.
"""
from pathlib import Path
import copy,json,hashlib
from uniform_seed_cyclotomic_engine import Poly,F,scalar,execute,direct_dft
P=Path(__file__).resolve().parents[1]/"logs/uniform-bytecode/seed-rank-cross"
code=json.loads((P/'program.json').read_text());startup=json.loads((P/'startup.json').read_text());models=json.loads((P/'models.json').read_text())
old=json.loads((P.parent/'rank-cross-replay/program.json').read_text())
assert len(code)==835 and len(startup)==935 and len(old)==799
assert all(i[0] in ['lit','add','mul','getnat'] for i in code[:35])
assert all(i[0] not in ['root','input','output'] for i in code)
def relocate(ins):
 op,*a=ins
 if op=='halt':return ['jump',834]
 if op=='jump':a[0]+=35
 if op=='branch':a[2]+=35;a[3]+=35
 return [op,*a]
assert code[35:834]==[relocate(x) for x in old]
assert code[834]==['halt']

def seed_values(D,r):
 eta=Poly(D,{1:1});omega=eta**(D//r)
 H=[Poly(D,{0:1})];scale=[Poly(D,{0:1})]
 for j in range(1,r):
  H.append(H[-1]*(Poly(D,{0:1})-omega**j));scale.append(scale[-1]*-(omega**(j-1)))
 h=[v.inverse() for v in H];g=[Poly(D,{0:1})]
 for j in range(1,r):
  val=Poly(D)
  for u in range(1,j+1):val=val+h[u]*g[j-u]
  g.append(-val)
 return [H,scale,[(v*w).inverse() for v,w in zip(H,scale)],h,g]

startups={};startCases=[]
for n in [1,4]:
 model=next(x for x in models if x['n']==n);D=model['masterOrder'];B=(n+2)**19
 for seed in [17,99]:
  s={'pc':0,'nat':[0]*1200,'sr':{},'nh':{},'sh':{},'out':{},'roots':[]}
  inputs=[scalar(D,0 if seed==99 else j+1,0 if seed==99 else 2-j)[0] for j in range(n)]
  steps,pcs,peak=execute(startup,s,B,100000,D,n,inputs)
  assert s['pc']==934 and s['roots']==[D] and s['sh'][0]==(Poly(D,{1:1}),False)
  pool=model['poolEnd']-5*sum(model['radices']);base=pool
  for j,r in enumerate(model['radices']):
   assert s['nh'][model['directoryBase']+2*j]==base and s['nh'][model['directoryBase']+2*j+1]==r
   values=seed_values(D,r)
   for lane in range(5):
    assert [s['sh'][base+lane*r+i] for i in range(r)]==[(v,False) for v in values[lane]]
   assert s['sh'][6+j]==(Poly(D,{1:1})**(D//r),False)
   base+=5*r
  assert base==model['poolEnd']
  startups[n,seed]=copy.deepcopy(s)
  startCases.append({'n':n,'seed':seed,'rootOrder':D,'radices':model['radices'],'steps':steps,'maximumWord':peak})
  print('startup',n,seed,'steps',steps,flush=True)

cases=[];coverage=set();total=0;saved=None
for model in models:
 n,j,K,a,e,r,D=[model[k] for k in ['n','axis','height','a','e','radix','masterOrder']]
 split,i0,j0=model['split'],model['i0'],model['j0'];N=2**K;G=3*K*N//2;convG=3*K*N+2*N
 rows=model['rows'];T=6*convG+2*a;assert len(rows)==T
 assert 0<a<=N and 0<e<=N and i0+a<=r and split<r and split<=i0 and j0+e<=split
 assert N<=8*r and D%N==0
 for layout in [(1000,2000,30000,10000,40000,100000,200000,1000000,2000000),
                (2000,4000,70000,20000,100000,300000,400000,2000000,3000000)]:
  S,A,d,C,V,tape,depth,Q,R=layout;TN=2*C;CP=TN+7*N+100;B=(n+2)**19
  H=model['axisBase']+3*r;GB=model['axisBase']+4*r;eta=Poly(D,{1:1});omega=eta**(D//N)
  RA=A+N+G+5*N+4
  fftBudget=A+(100*(N+G+K+1)**2+200)+(d+3*G)+(RA+5)+(d+4*G+(A+N)+42)+199
  specBudget=fftBudget+S+C+7*N+600
  crossBudget=V+tape+5*(7*convG+2*a)+(100*(N+G+K+1)**2+200)+10000*(N+convG+a+e+K+1)**2
  assert H+r<=S and GB+r<=S and S+6*N<=A and RA+1<=C and specBudget<=B
  assert V+5*convG<=tape and crossBudget<=B and tape+5*T<=depth and depth+e+1+T<=B
  assert d+3*G<=Q and depth+e+1+T<=Q and Q+T*(T+1)<=R and R+T+2<=B
  assert C+7*N+1<=TN and TN+7*N<=CP and CP+6<=B
  assert min(d,V,tape,depth,Q,R)>=model['directoryEnd']
  assert min(S,A,C,TN,CP)>=model['poolEnd']
  for seed in [17,99]:
   s=copy.deepcopy(startups[n,seed]);s['pc']=0
   # Ordinary caller Args plus dirty scratch/fresh workspaces; retained state unchanged.
   for q in range(160,1200):s['nat'][q]=19*q+seed
   for q in range(90):s['sr'][q]=scalar(D,q-2,3-q,q%2)
   headers={1120:j,1121:K,1122:a,1123:e,1124:i0,1125:j0,1126:split,1127:S,1128:A,
    1129:d,1130:C,1131:V,1132:tape,1133:depth,1134:Q,1135:R,1136:TN,1137:CP}
   for q,v in headers.items():s['nat'][q]=v
   for q in list(range(S,S+6*N))+list(range(C,C+7*N+1))+list(range(TN,TN+7*N))+list(range(CP,CP+6)):
    s['sh'][q]=scalar(D,q-3,11-q,True)
   for q in [d,V,tape,depth,Q,R,9000000]:s['nh'][q]=seed+q
   s['sh'][9000000]=scalar(D,-7,3,True);s['out'][0]=scalar(D,seed,-2)[0]
   before=copy.deepcopy(s)
   h=[before['sh'][H+i][0] for i in range(r)];g=[before['sh'][GB+i][0] for i in range(r)]
   steps,pcs,peak=execute(code,s,B,model['runtimeBudget'],D,n)
   def matrix(i,j):
    acc=Poly(D)
    for u in range(split-(j0+j)):acc=acc+h[i0+i-(j0+j)-u]*g[u]
    return acc
   v=[-h[i0+i-split] for i in range(a)];w=[g[split-(j0+j)] for j in range(e)]
   row=[matrix(0,j)-v[0]*w[j] for j in range(e)]
   col=[Poly(D) if i==0 else matrix(i,0)-v[i]*w[0] for i in range(a)]
   delta=[Poly(D,{0:1})]+[Poly(D) for _ in range(N-1)]
   kernels=[[(arr[i] if i<len(arr) else Poly(D),False) for i in range(N)] for arr in [w,v,row,delta,delta,col]]
   for b in range(6):assert [s['sh'][S+b*N+i] for i in range(N)]==kernels[b]
   expected=[(omega**i,False) for i in range(N)]
   for kernel in kernels:expected.extend(direct_dft(omega,kernel))
   assert [s['sh'][C+i] for i in range(7*N)]==expected
   assert s['sh'][C+7*N]==(omega,False)
   for i,row in enumerate(rows):assert [s['nh'].get(tape+5*i+b) for b in range(5)]==row
   labels=[0]*(e+1)
   for i,row in enumerate(rows):
    op,left,right,kind,payload=row;assert left<e+1+i and (op==2 or right<e+1+i)
    labels.append((max(labels[left],labels[right]) if op<2 else labels[left])+1)
   assert max(labels)<=8*K+6
   assert [s['nh'].get(depth+i) for i in range(e+1+T)]==labels
   order=sorted(range(T),key=lambda i:(labels[e+1+i],i))
   assert [s['nh'].get(Q+i) for i in range(T)]==order
   assert [s['nh'].get(R+i) for i in range(T+2)]==[sum(1 for q in range(T) if labels[e+1+q]<i) for i in range(T+2)]
   assert [s['sh'].get(TN+i) for i in range(7*N)]==[(-v,False) for v,_ in expected]
   assert [s['sh'].get(CP+i) for i in range(6)]==[scalar(D,z) for z in [1,-1,F(1,N),F(-1,N),F(5,4),F(4,5)]]
   assert s['pc']==834 and s['nat'][651]==T and s['nat'][489]==N and s['nat'][526]==S
   for q in range(100,107):assert s['nat'][q]==before['nat'][q]
   for q in headers:assert s['nat'][q]==before['nat'][q]
   assert s['out']==before['out'] and s['roots']==before['roots']
   for q in set(before['sh'])|set(s['sh']):
    if (q<S or S+6*N<=q) and (q<A or RA+1<=q) and (q<C or C+7*N+1<=q) and (q<TN or TN+7*N<=q) and (q<CP or CP+6<=q):assert s['sh'].get(q)==before['sh'].get(q)
   for q in set(before['nh'])|set(s['nh']):
    if (q<d or d+3*G<=q) and (q<V or V+5*convG<=q) and (q<tape or tape+5*T<=q) and (q<depth or depth+e+1+T<=q) and (q<Q or Q+T*(T+1)<=q) and (q<R or R+T+2<=q):assert s['nh'].get(q)==before['nh'].get(q)
   total+=steps;coverage.update(pcs)
   cases.append({'n':n,'axis':j,'radix':r,'height':K,'width':N,'a':a,'e':e,'seed':seed,'layout':layout,'steps':steps,'runtimeBudget':model['runtimeBudget'],'maximumWord':peak,'masterOrder':D,'maximumDepth':max(labels)})
   print('case',len(cases),'n/j/K',n,j,K,'a/e',a,e,'seed',seed,'steps',steps,flush=True)
   if n==4 and K==2 and a==3 and seed==17:saved=(before,D,B,H,GB,model['directoryBase']+2*j,model['runtimeBudget'])
controls=[]
before,D,B,H,GB,axisCell,budget=saved
for name,bank,address in [('missing-axis-offset','nh',axisCell),('missing-axis-width','nh',axisCell+1),('missing-H','sh',H+1),('missing-G','sh',GB+1),('missing-master','sh',0)]:
 bad=copy.deepcopy(before);del bad[bank][address]
 try:execute(code,bad,B,budget,D)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
bad=copy.deepcopy(before)
for base in [H,GB]:
 for i in range(4):bad['sh'][base+i]=(bad['sh'][base+i][0],True)
try:execute(code,bad,B,budget,D)
except (AssertionError,KeyError):controls.append('data-data-guard')
else:raise AssertionError('data-data guard accepted')
for name,mut in [('initial-word-guard',lambda s:s['nat'].__setitem__(1146,B+1)),('execution-budget',lambda s:None)]:
 bad=copy.deepcopy(before);mut(bad)
 try:execute(code,bad,B,10 if name=='execution-budget' else budget,D)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
# The caller relies on the supplied physical directory; it does not silently
# substitute a host-selected base. Remove its actual load and require a mismatch.
mutated=copy.deepcopy(code);mutated[9]=['jump',10];bad=copy.deepcopy(before)
try:execute(mutated,bad,B,budget,D)
except (AssertionError,KeyError):controls.append('directory-load-mutation')
else:raise AssertionError('directory-load mutation accepted')
result={'status':'PASS','instructions':835,'startupInstructions':935,'startupCases':startCases,'exactCases':len(cases),'chargedSteps':total,
 'visitedPCs':len(coverage),'unvisitedPCs':sorted(set(range(835))-coverage),'allNewPCsVisited':set(range(35)).issubset(coverage) and 834 in coverage,
 'negativeControls':controls,'cases':cases,
 'arithmetic':'Exact sparse rational cyclotomic arithmetic in Q[eta]/Phi128 andQ[eta]/Phi24576. All tested divisions have rational complex norm; inverse products checked.',
 'scope':'Each835 starts with real H/G/master from actual empty-state935. Ordinary Args/dirty workspace installed at the separate caller interface. No source/phase-output writes or interphase writes during835; no single935→835 composition claim.'}
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','exactCases','chargedSteps','visitedPCs','allNewPCsVisited','negativeControls']},indent=2))
