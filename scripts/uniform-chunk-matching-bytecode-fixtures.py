from pathlib import Path
from fractions import Fraction as F
import copy,json
from uniform_cyclotomic_engine import scalar,execute,Poly
P=Path(__file__).resolve().parents[1]/"logs/uniform-bytecode/chunk-matching"
programs=json.loads((P/'programs.json').read_text());typed=json.loads((P/'typed.json').read_text())
fast=json.loads((P/'typed-fast.json').read_text())
assert [c for c in fast if c['K']==0]==typed
# The efficient fresh Lean oracle uses an explicit cached integer recurrence;
# every K0 case agrees with the actual typed cross constructor reference.
typed += [c for c in fast if c['K']>0]
B=1000000

def fresh():
 s={'pc':0,'nat':[(17*i+13)%10000 for i in range(1250)],'nh':{0:71,7:41,B-1:3},
    'sh':{i:scalar(8,F(i-7,3),F(11-i,5),i%3==0) for i in range(47)} |
         {200000+i:scalar(8,0 if i%3==0 else F(i-3,7),0 if i%3==0 else F(4-i,9),False) for i in range(150)} |
         {300000+i:scalar(8,F(5-i,13),F(i,7),False) for i in range(5)} |
         {400000+i:scalar(8,F(i-1,7),F(1-i,9),False) for i in range(150)},
    'sr':{i:scalar(8,F(i-5,3),F(11-i,2),i%2==1) for i in range(100)},
    'out':{9:Poly(8,{0:3,2:-7,5:F(9,2)})},'roots':[16,7,1]}
 for j in range(100,107):s['nat'][j]=17*j+9
 return s

def greed(rows):
 out=[]
 for i,(d,s,_) in enumerate(rows):
  blocked={out[j] for j,(x,y,_) in enumerate(rows[:i]) if d in (x,y) or s in(x,y)}
  out.append(next(j for j in range(11) if j not in blocked))
 return out

def relocate(code,base,returnPC):
 out=[]
 for op,*a in code:
  if op=='halt':out.append(['jump',returnPC])
  elif op=='jump':out.append([op,base+a[0]])
  elif op=='branch':out.append([op,a[0],a[1],base+a[2],base+a[3]])
  else:out.append([op,*a])
 return out

def pools(K,a,e,dirty):
 N=1<<K;G=6*(3*K*N+2*N)+2*a;H=8*K+7
 T=13+dirty*19;Q=T+5*G+9;R=Q+G+9;D=R+G+11;F0=D+6*G*H+9;U=F0+2*G*H+9;J=U+23
 v=G+e+a+7;src=2;tgt=v-a-2
 b=J+3*H+17;o=b+G+3;ids=o+6*G+3;m=ids+2*G+3;perm=m+6*G+3;w=perm+v+3;mark=w+v+3;axis=mark+v+3
 return dict(K=K,a=a,e=e,N=N,G=G,H=H,T=T,Q=Q,R=R,D=D,F=F0,U=U,J=J,C=200000,P=300000,Z=400000,
  v=v,src=src,tgt=tgt,b=b,o=o,ids=ids,m=m,perm=perm,w=w,mark=mark,axis=axis)

def headers(s,p,d,k,enabled):
 s['nat'][1050:1063]=[p[q] for q in ['K','a','e','T','Q','R','D','F','U','J','C']]+[int(enabled),p['P']]
 s['nat'][1180:1193]=[p[q] for q in ['v','src','tgt','b','o','ids','m','perm','w','mark','axis']]+[d,k]

def check_chunk(s,old,p,W,k,steps,origin):
 G,e,a,v,src,tgt=p['G'],p['e'],p['a'],p['v'],p['src'],p['tgt']
 cols=greed(W);ids=[i for i,c in enumerate(cols) if c==k];selected=[W[i] for i in ids]
 av=[i for i in range(v) if not src<=i<src+e and not tgt<=i<tgt+a][:G]
 assert len(av)==G
 def mapped(q):
  assert q<e or e+1<=q<e+1+G+a
  return src+q if q<e else av[q-e-1] if q<e+1+G else tgt+q-e-1-G
 rows=[[mapped(d),mapped(q),co] for d,q,co in selected]
 assert s['nat'][894]==len(ids)
 assert [s['nh'][p['ids']+i] for i in range(len(ids))]==ids
 assert [[s['nh'][p['o']+3*i+j] for j in range(3)] for i in range(len(ids))]==selected
 assert [[s['nh'][p['m']+3*i+j] for j in range(3)] for i in range(len(ids))]==rows
 assert [s['nh'][p['b']+j] for j in range(G)]==av
 used=[j for d,q,_ in rows for j in[d,q]];assert len(used)==len(set(used)) and all(j<v for j in used)
 perm=used+[j for j in range(v) if j not in used]
 widths=[2]*len(rows)+[1]*(v-2*len(rows))
 assert [s['nh'][p['perm']+j] for j in range(v)]==perm
 assert [s['nh'][p['w']+j] for j in range(len(widths))]==widths
 assert [s['nh'][p['axis']+j] for j in range(4)]==[v-len(rows),p['w'],v,p['perm']]
 assert sum(widths)==v and sorted(perm)==list(range(v))
 assert all(s[j]==old[j] for j in ['sh','sr','out','roots'])
 assert all(s['nat'][r]==old['nat'][r] for r in range(100,107))
 return {'origin':origin,'K':p['K'],'a':a,'e':e,'v':v,'selectedColor':k,'rows':len(W),'selected':len(ids),'steps':steps}

results=[];cover=set();combinedcover=set();saved=[]
# Every caller runs continuously after the ACTUAL Height186, with both sets of
# original caller headers installed before instruction0 and no phase host writes.
for c in typed:
 K,a,e,enabled=(c[q] for q in ['K','a','e','enabled'])
 for dirty in [0,1]:
  p=pools(K,a,e,dirty)
  choices=[(d,k) for d in range(p['H']) for k in [0,1,2,10]]
  for d,k in choices:
   s=fresh();headers(s,p,d,k,enabled)
   for j,row in enumerate(c['typed']):
    for z,val in enumerate(row):s['nh'][p['T']+5*j+z]=val
   for j,val in enumerate(c['order']):s['nh'][p['Q']+j]=val
   for j,val in enumerate(c['offsets']):s['nh'][p['R']+j]=val
   for q in range(p['D'],p['axis']+4):s['nh'][q]=(31*q+dirty+7)%10000
   old=copy.deepcopy(s)
   steps,pcs=execute(programs['heightChunk'],s,B,10000000,8)
   assert s['pc']==401
   W=c['slices'][d]['rows'];assert c['slices'][d]['colors']==greed(W)
   for z,sl in enumerate(c['slices']):
    rd=p['D']+6*p['G']*z;cd=p['F']+2*p['G']*z
    assert [s['nh'][p['J']+3*z+j] for j in range(3)]==[len(sl['rows']),rd,cd]
    assert [[s['nh'][rd+3*i+j] for j in range(3)] for i in range(len(sl['rows']))]==sl['rows']
    assert [s['nh'][cd+i] for i in range(len(sl['rows']))]==sl['colors']
   def writable(q):return p['D']<=q<p['D']+6*p['G']*p['H'] or p['F']<=q<p['F']+2*p['G']*p['H'] or p['U']<=q<p['U']+12 or p['J']<=q<p['J']+3*p['H'] or p['b']<=q<p['axis']+4
   assert all(s['nh'].get(q)==old['nh'].get(q) for q in set(s['nh'])|set(old['nh']) if not writable(q))
   protected=lambda r:all(not(lo<=r<hi) for lo,hi in [(720,750),(800,824),(900,915),(920,925),(1063,1080),(261,273),(840,862),(880,900),(1020,1035),(1080,1101),(1193,1206)])
   assert all(s['nat'][r]==old['nat'][r] for r in range(1250) if protected(r))
   out=check_chunk(s,old,p,W,k,steps,'continuous actual Height186 then215; fresh Lean cached integer recurrence, K0 cross-constructor agreement');out['depth']=d;out['dirty']=dirty;results.append(out)
   cover.update(pc-186 for pc in pcs if 186<=pc<401);combinedcover.update(pcs)
   saved.append((copy.deepcopy(old),p,d,k,enabled,c))
# Generic theorem permits output ports as well. These genuine domain+degree
# physical layer fixtures cover mapper target branches; they are NOT claimed
# to be forward Height-produced cross rows.
for K,exact in [(K,exact) for K in [0,1,2] for exact in [False,True]]:
 p=pools(K,2 if K else 1,1,0)
 if exact:p.update(v=p['G']+p['e']+p['a'],src=0,tgt=p['G']+p['e'])
 e=p['e'];G=p['G'];a=p['a']
 W=[[e+1,0,200000],[e+1+G,e+2,300000],[e+3,e+4,200003],[0,e+1+G,400000]]
 for k in [0,1,10]:
  s=fresh();headers(s,p,0,k,True)
  for q in range(p['D'],p['axis']+4):s['nh'][q]=(31*q+7)%10000
  for i,row in enumerate(W):
   for j,val in enumerate(row):s['nh'][p['D']+3*i+j]=val
  for i,val in enumerate(greed(W)):s['nh'][p['F']+i]=val
  for j,val in enumerate([len(W),p['D'],p['F']]):s['nh'][p['J']+j]=val
  old=copy.deepcopy(s);steps,pcs=execute(programs['chunk'],s,B,100000,8)
  assert steps<=4*K+180*p['v']+92 and s['pc']==214
  results.append(check_chunk(s,old,p,W,k,steps,'generic valid Domain/degree physical layer; includes target ports'+ (' at exact capacity (raw port may equal v)' if exact else '')))
  cover.update(pcs)
  def writable(q):return p['b']<=q<p['axis']+4
  assert all(s['nh'].get(q)==old['nh'].get(q) for q in set(s['nh'])|set(old['nh']) if not writable(q))
  protected=lambda r:all(not(lo<=r<hi) for lo,hi in [(261,273),(840,862),(880,900),(1020,1035),(1080,1101),(1193,1206)])
  assert all(s['nat'][r]==old['nat'][r] for r in range(1250) if protected(r))
  assert s['nh'][p['J']]==len(W)
controls=[]
def reject(name,code,s,b=B):
 try:execute(code,s,b,10000000,8)
 except (AssertionError,KeyError):controls.append({'name':name,'kind':'model WordBound guard rejects; no invented bytecode branch' if 'word bound' in name else 'actual bytecode missing-load failure'});return
 raise AssertionError('negative control accepted: '+name)
# Missing source cells are diagnosed by the actual composed bytecode.
s,p,d,k,en,c=saved[0];s['nh'].pop(p['R'],None);reject('missing earlier physical depth directory',programs['heightChunk'],s)
p=pools(0,1,1,0);s=fresh();headers(s,p,0,0,True);s['nh'].pop(p['J'],None);reject('missing actual Height layer directory record',programs['chunk'],s)
s=fresh();headers(s,p,0,0,True)
for j,val in enumerate([1,p['D'],p['F']]):s['nh'][p['J']+j]=val
s['nh'][p['D']]=2;s['nh'][p['D']+1]=0;s['nh'][p['D']+2]=200000
s['nh'].pop(p['F'],None);reject('missing actual indexed color cell',programs['chunk'],s)
s=fresh();headers(s,p,0,0,True)
for j,val in enumerate([1,p['D'],p['F']]):s['nh'][p['J']+j]=val
s['nh'][p['F']]=0;s['nh'][p['D']]=2;s['nh'].pop(p['D']+1,None);reject('missing actual logical row source',programs['chunk'],s)
s=fresh();headers(s,p,0,0,True);reject('insufficient ambient word bound',programs['chunk'],s,214)
assert not(2+3<=3 or 3+2<=2);controls.append({'name':'overlapping placement intervals','kind':'theorem contract rejects; no invented bytecode guard'})
assert not(1<1 or 2<=1<2+14+1);controls.append({'name':'literal zero-hole port','kind':'theorem Domain rejects; no invented bytecode guard'})
assert cover==set(range(215)),sorted(set(range(215))-cover)
report={'status':'PASS','caseCount':len(results),'totalSteps':sum(x['steps'] for x in results),'cases':results,'negativeControls':controls,
 'coverage':{'chunk215':{'visited':len(cover),'length':215,'unvisited':sorted(set(range(215))-cover)},'heightThenChunk402':{'visited':len(combinedcover),'length':402,'unvisited':sorted(set(range(402))-combinedcover)}},
 'boundary':'Universal formal cross adapter starts from earlier actual Height.Processed. Typed fixture caller initializes only original physical typed tape+Bucket order/directory; ACTUAL Height186 and Chunk215 run continuously with no host phase writes. Separate generic domain layers cover target branches absent from forward cross. Pure Nat preparation preserves exact cyclotomic scalars/tags; no scalar action or global DFT claim.'}
(P/'fixtures.json').write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
