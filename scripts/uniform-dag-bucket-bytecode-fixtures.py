import json
from pathlib import Path
repo=Path(__file__).resolve().parents[1]
root=repo/'logs/uniform-bytecode/dag-bucket'
code=json.loads((root/'program.json').read_text())
orders=json.loads((root/'orders.json').read_text())
assert len(code)==24
assert all(row[0] in range(7) for row in code), 'No scalar/root/input/output opcode'
class Failure(Exception):pass

def execute(nr,nh,B,start=0):
    nr,nh=nr.copy(),nh.copy();pc=start;steps=0;seen=set();writes=[]
    def check():
        if not(0<=pc<=B and all(0<=v<=B for v in nr.values()) and all(0<=a<=B and 0<=v<=B for a,v in nh.items())):
            raise Failure('word bound')
    check()
    while steps<1000000:
        if not(0<=pc<len(code)):raise Failure('missing instruction')
        seen.add(pc);op,*a=code[pc];steps+=1;npc=pc+1
        if op==6:return nr,nh,steps,seen,pc,writes
        if op==0:d,v=a;nr[d]=v
        elif op==1:
            kind,d,l,r=a;x,y=nr.get(l,0),nr.get(r,0)
            if kind==0:nr[d]=x+y
            elif kind==1:nr[d]=max(0,x-y)
            elif kind==2:nr[d]=x*y
            elif kind in [3,4]:
                if y==0:raise Failure('zero divisor')
                nr[d]=x//y if kind==3 else x%y
            else:raise AssertionError(kind)
        elif op==2:
            d,r=a;address=nr.get(r,0)
            if address not in nh:raise Failure('missing Nat source')
            nr[d]=nh[address]
        elif op==3:
            r,v=a;address=nr.get(r,0);value=nr.get(v,0);nh[address]=value;writes.append((address,value))
        elif op==4:l,r,y,n=a;npc=y if nr.get(l,0)<nr.get(r,0) else n
        elif op==5:npc=a[0]
        else:raise AssertionError(op)
        pc=npc;check()
    raise AssertionError('nontermination')

specs=[]
for G,seed,lean_order,lean_offsets in orders:
    depths=[(i*i+seed*i+3*seed)%(G+3) for i in range(G)]
    expected=sorted([i for i in range(G) if depths[i]<=G],key=lambda i:(depths[i],i))
    offsets=[sum(value<d for value in depths) for d in range(G+2)]
    assert expected==lean_order and offsets==lean_offsets
    specs.append(dict(G=G,depths=depths,order=expected,offsets=offsets,origin='fresh generic Lean102',seed=seed))
# Reuse only cached height-zero actual typed graph depths, no large reconstruction.
typed_source=repo/'verification/fixtures/dag-depth-typed.json'
import hashlib
assert hashlib.sha256(typed_source.read_bytes()).hexdigest()=='d870f5e2194dac64cf783a938ad3b9e5dc3910cbde1df154e49e1499362e9ddd'
typed=json.loads(typed_source.read_text())
seen_typed=set()
for index,spec in enumerate(typed):
    if spec['K']!=0:continue
    N,G=spec['inputs'],spec['gates'];depths=spec['depths'][N+1:]
    key=(N,tuple(depths))
    if key in seen_typed:continue
    seen_typed.add(key)
    assert len(depths)==G and all(0<value<=G for value in depths)
    expected=sorted(range(G),key=lambda i:(depths[i],i))
    offsets=[sum(value<d for value in depths) for d in range(G+2)]
    specs.append(dict(G=G,depths=depths,order=expected,offsets=offsets,origin='cached actual typed cross K0',parent_spec_index=index))
traces=[];all_pcs=set()
for index,spec in enumerate(specs):
    G=spec['G'];depths=spec['depths'];order=spec['order'];offsets=spec['offsets']
    for dirty in [0,1]:
        P=13+dirty*100;Q=P+G+9;R=Q+G*(G+1)+9;B=R+G+2+2000
        nr={r:(37*r+13+dirty)%B for r in range(770)};nr.update({700:G,701:P,702:Q,703:R})
        nh={0:71,7:41,B-1:3}
        for j,v in enumerate(depths):nh[P+j]=v
        for j in range(G*(G+1)):nh[Q+j]=(j*13+17)%B
        for j in range(G+2):nh[R+j]=(j*11+19)%B
        final,heap,t,pcs,halt,writes=execute(nr,nh,B)
        assert [heap[Q+j] for j in range(len(order))]==order
        assert [heap[R+j] for j in range(G+2)]==offsets
        assert [heap[P+j] for j in range(G)]==depths
        assert all(final[r]==v for r,v in nr.items() if r<704 or r>=712)
        assert all(heap[a]==v for a,v in nh.items() if not(Q<=a<Q+G*(G+1) or R<=a<R+G+2))
        assert all(a in nh or Q<=a<Q+G*(G+1) or R<=a<R+G+2 for a in heap)
        expected=9+7*(G+1)+sum(6 if v<d else 7 if d<v else 10 for d in range(G+1) for v in depths)
        assert t==expected and t<=10*G*(G+1)+7*(G+1)+9 and halt==23
        assert [(a,v) for a,v in writes if Q<=a<Q+G*(G+1)]==[(Q+j,v) for j,v in enumerate(order)]
        assert [(a,v) for a,v in writes if R<=a<R+G+2]==[(R+j,v) for j,v in enumerate(offsets)]
        complete=all(v<=G for v in depths)
        if complete:assert sorted(order)==list(range(G))
        assert all((depths[a],a)<(depths[b],b) for a,b in zip(order,order[1:]))
        all_pcs.update(pcs)
        traces.append(dict(index=index,dirty=dirty,G=G,steps=t,origin=spec['origin'],complete_permutation=complete,exact_bank=True,exact_directory=True,frames=True))
assert all_pcs==set(range(24)),set(range(24))-all_pcs
negative=[];G=3;P=13;Q=25;R=50;B=2200
nr={700:G,701:P,702:Q,703:R};nh={P:1,P+1:2,P+2:1}
for kind in ['missing first depth','missing interior depth','word bound','missing instruction']:
    heap=nh.copy();budget=B;start=0
    if kind=='missing first depth':del heap[P]
    elif kind=='missing interior depth':del heap[P+1]
    elif kind=='word bound':budget=10
    else:start=24
    try:execute(nr,heap,budget,start)
    except Failure as exc:negative.append(dict(kind=kind,reason=str(exc)))
    else:raise AssertionError('guard accepted '+kind)
receipt=dict(status='PASS',cases=len(traces),specs=len(specs),fresh_generic_specs=len(orders),cached_typed_specs=len(seen_typed),steps=sum(t['steps'] for t in traces),all24_pcs=True,negative=negative,traces=traces,scope='Actual literal24 Nat-only bytecode, charged WordBound at every step, exact order/directory/write chronology/frames. Full typed_execution theorem links computed Depth35 labels; generic out-of-range diagnostics intentionally have incomplete order.')
receipt.update(typed_fixture_sha256=hashlib.sha256(typed_source.read_bytes()).hexdigest(),typed_fixture_provenance='Pinned previous successful Lean export of actual typed K0 Cross depths; current typed_execution independently audited')
(root/'fixtures.json').write_text(json.dumps(receipt,indent=2)+'\n')
print({k:receipt[k] for k in ['status','cases','specs','fresh_generic_specs','cached_typed_specs','steps','all24_pcs','negative']})
