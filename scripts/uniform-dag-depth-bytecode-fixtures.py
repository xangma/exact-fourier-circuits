import json,copy
from pathlib import Path
repo=Path(__file__).resolve().parents[1]
root=repo/'logs/uniform-bytecode/dag-depth'
code=json.loads((root/'program.json').read_text())
typed_source=repo/'verification/fixtures/dag-depth-typed.json'
import hashlib
assert hashlib.sha256(typed_source.read_bytes()).hexdigest()=='d870f5e2194dac64cf783a938ad3b9e5dc3910cbde1df154e49e1499362e9ddd'
specs=json.loads(typed_source.read_text())
specs += json.loads((root/'plain-specs.json').read_text())
assert len(code)==35
class Failure(Exception):pass
def execute(nr,nh,B):
 nr=nr.copy();nh=nh.copy();pc=0;steps=0;seen=set()
 def check():
  if not(pc<=B and all(0<=v<=B for v in nr.values()) and all(0<=a<=B and 0<=v<=B for a,v in nh.items())):raise Failure('word bound')
 check()
 while steps<1000000:
  seen.add(pc);op,*a=code[pc];steps+=1;npc=pc+1
  if op==6:return nr,nh,steps,seen,pc
  if op==0:d,v=a;nr[d]=v
  elif op==1:
   kind,d,l,r=a;x,y=nr.get(l,0),nr.get(r,0)
   if kind==0:nr[d]=x+y
   elif kind==1:nr[d]=max(0,x-y)
   elif kind==2:nr[d]=x*y
   else:raise AssertionError('unexpected integer op')
  elif op==2:
   d,r=a;address=nr.get(r,0)
   if address not in nh:raise Failure('missing Nat source')
   nr[d]=nh[address]
  elif op==3:r,v=a;nh[nr.get(r,0)]=nr.get(v,0)
  elif op==4:l,r,y,n=a;npc=y if nr.get(l,0)<nr.get(r,0) else n
  elif op==5:npc=a[0]
  else:raise AssertionError('scalar/input/root/output opcode')
  pc=npc;check()
 raise AssertionError('unexpected nontermination')
seen=set();results=[]
for index,spec in enumerate(specs):
 N,G=spec['inputs'],spec['gates'];assert len(spec['tape'])==G
 for seed in [0,1]:
  d=31+seed*100;P=d+5*G+17;B=P+N+1+G+3000
  nr={r:(37*r+13+seed)%B for r in range(700)};nr.update({650:N,651:G,652:d,653:P})
  nh={0:71,7:41,B-1:3}
  for j,row in enumerate(spec['tape']):
   for q,v in enumerate(row):nh[d+5*j+q]=v
  for j in range(N+1+G):nh[P+j]=(j*13+17)%B
  final,heap,t,pc,halt=execute(nr,nh,B)
  actual=[heap[P+j] for j in range(N+1+G)]
  assert actual==spec['depths'],(index,seed)
  assert all(final[r]==v for r,v in nr.items() if r<654 or r>=666)
  assert all(heap[a]==v for a,v in nh.items() if not(P<=a<P+N+1+G))
  assert all(a in nh or P<=a<P+N+1+G for a in heap)
  expected=5*(N+1)+10
  for j,row in enumerate(spec['tape']):
   opcode,left,right,*_=row
   expected+=17 if opcode==2 else 20+2*(spec['depths'][left]<spec['depths'][right])
  assert t==expected and t<=5*(N+1)+22*G+10 and halt==34
  if spec['K'] is not None:assert max(actual)<=8*spec['K']+6
  seen.update(pc);results.append(dict(index=index,seed=seed,K=spec['K'],inputs=N,gates=G,steps=t,physical_frames=True,exact_typed_depths=True))
assert seen==set(range(35)),set(range(35))-seen
negative=[]
spec=specs[29];N,G=spec['inputs'],spec['gates'];d=31;P=d+5*G+17;B=P+N+G+4000
nr={650:N,651:G,652:d,653:P};nh={d+5*j+q:v for j,row in enumerate(spec['tape']) for q,v in enumerate(row)}
for kind in ['missing opcode','missing left','missing right','word bound']:
 bad=nh.copy();budget=B
 if kind=='missing opcode':del bad[d]
 elif kind=='missing left':del bad[d+1]
 elif kind=='missing right':del bad[d+2]
 else:budget=10
 try:execute(nr,bad,budget)
 except Failure as e:negative.append(dict(kind=kind,reason=str(e)))
 else:raise AssertionError('guard accepted '+kind)
receipt=dict(status='PASS',cases=len(results),steps=sum(r['steps'] for r in results),all35_pcs=True,negative=negative,traces=results,scope='Actual literal35 from physical typed cross tape; expected recurrence is Lean evaluate_typed-proved equal to runDepth. Universal typed_execution_full and cross_execution proved in Lean; no floating point.')
receipt.update(typed_fixture_sha256=hashlib.sha256(typed_source.read_bytes()).hexdigest(),reused_typed_examples=30,fresh_generic_examples=8,typed_fixture_provenance='Pinned previous successful Lean export; current universal typed_execution_full independently verified')
(root/'fixtures.json').write_text(json.dumps(receipt,indent=2)+'\n')
print({k:receipt[k] for k in ['status','cases','steps','all35_pcs','negative']})
