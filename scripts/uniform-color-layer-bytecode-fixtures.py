#!/usr/bin/env python3
"""Exact selected-row and actual Color51-bank diagnostics; phase setup boundaries explicit."""
import json,random,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/color-layer'
code=json.loads((root/'program.json').read_text())
lean_specs=json.loads((root/'specs.json').read_text())
assert len(code)==30 and all(row[0] in range(7) for row in code)
class Failure(Exception):pass

def execute(nr,nh,B,start=0):
    nr,nh=nr.copy(),nh.copy();pc=start;steps=0;seen=set();writes=[];reads=[]
    def bound(v):
        if not 0<=v<=B:raise Failure('word bound')
    bound(pc)
    for v in nr.values():bound(v)
    for a,v in nh.items():bound(a);bound(v)
    while steps<2000000:
        if not 0<=pc<len(code):raise Failure('missing instruction')
        seen.add(pc);op,*a=code[pc];steps+=1;npc=pc+1
        if op==6:return nr,nh,steps,seen,pc,writes,reads
        if op==0:r,v=a;bound(v);nr[r]=v
        elif op==1:
            kind,r,l,h=a;x,y=nr.get(l,0),nr.get(h,0)
            if kind==0:v=x+y
            elif kind==1:v=max(0,x-y)
            elif kind==2:v=x*y
            elif kind in (3,4):
                if not y:raise Failure('zero divisor')
                v=x//y if kind==3 else x%y
            else:raise AssertionError(kind)
            bound(v);nr[r]=v
        elif op==2:
            r,a=a;address=nr.get(a,0);bound(address)
            if address not in nh:raise Failure('missing Nat source')
            nr[r]=nh[address];reads.append(address)
        elif op==3:
            a,r=a;address=nr.get(a,0);v=nr.get(r,0);bound(address);bound(v)
            nh[address]=v;writes.append((address,v))
        elif op==4:l,r,y,n=a;npc=y if nr.get(l,0)<nr.get(r,0) else n
        elif op==5:npc=a[0]
        else:raise AssertionError(op)
        bound(npc);pc=npc
    raise AssertionError('nontermination')

def selected(colors,k):return [i for i,c in enumerate(colors) if c==k]
def charged(colors,k):return 7+sum(6 if c<k else 7 if k<c else 24 for c in colors)
def greedy(edges):
    colors=[]
    for edge in edges:
        used={colors[j] for j,e in enumerate(edges[:len(colors)]) if set(edge)&set(e)}
        colors.append(next((c for c in range(11) if c not in used),11))
    return colors
specs=[]
for M,family,k,colors,rows,ords,selectedrows in lean_specs:
    assert ords==selected(colors,k) and selectedrows==[rows[j] for j in ords]
    specs.append(dict(M=M,k=k,colors=colors,rows=rows,ords=ords,origin='fresh Lean selected'))
rng=random.Random(130)
for M in [31,100,257]:
    for family in ['all','none','ragged']:
        colors=[2]*M if family=='all' else [1]*M if family=='none' else [rng.randrange(11) for _ in range(M)]
        rows=[[rng.randrange(700),rng.randrange(700),700+i] for i in range(M)]
        specs.append(dict(M=M,k=2,colors=colors,rows=rows,ords=selected(colors,2),origin='independent integer oracle'))
# Actual physical Color51 execution feeds the filter, including repeated/parallel edges.
greedy_code=json.loads((root.parent/'greedy-color/program.json').read_text())
layer_code=code
physical_matching=0
for M in range(7):
    for family in ['parallel','chain','ragged']:
        if family=='parallel':edges=[[1,2]]*M
        elif family=='chain':edges=[[i,i+1] for i in range(M)]
        else:edges=[[2*(i%3),2*(i%3)+1] for i in range(M)]
        T=100;C=T+3*M;U=C+M;B=5000
        regs={800:M,801:T,802:C,803:U}
        heap={T+3*i+j:v for i,e in enumerate(edges) for j,v in enumerate(e+[700+i])}
        code=greedy_code
        nr,nh,*_=execute(regs,heap,B)
        code=layer_code
        colors=[nh[C+i] for i in range(M)]
        assert colors==greedy(edges)
        for k in range(11):
            rows=[e+[700+i] for i,e in enumerate(edges)]
            ords=selected(colors,k)
            assert all(not(set(edges[i])&set(edges[j])) for i in ords for j in ords if i!=j)
            specs.append(dict(M=M,k=k,colors=colors,rows=rows,ords=ords,origin='actual Color51 bank',matching=True))
traces=[];all_pcs=set()
for index,spec in enumerate(specs):
    M,k,colors,rows,ords=(spec[x] for x in ['M','k','colors','rows','ords'])
    for dirty in range(3):
        T=13+100*dirty;C=T+3*M+3*dirty;O=C+M+7*dirty;I=O+3*M+11*dirty;B=I+M+3000
        nr={q:(q*37+dirty+17)%B for q in range(960)};nr.update({880:M,881:T,882:C,883:k,884:O,885:I})
        nh={0:19,7:21,B-1:17}
        for i,row in enumerate(rows):
            for j,v in enumerate(row):nh[T+3*i+j]=v
            nh[C+i]=colors[i]
        for base,length in [(O,3*M),(I,M)]:
            for j in range(length):
                if j%3!=dirty:nh[base+j]=(47+3*j)%B
        out,heap,t,pcs,halt,writes,reads=execute(nr,nh,B)
        assert out[894]==len(ords)
        assert [heap[I+j] for j in range(len(ords))]==ords
        assert [[heap[O+3*j+h] for h in range(3)] for j in range(len(ords))]==[rows[i] for i in ords]
        assert t==charged(colors,k) and t<=24*M+7 and halt==29
        assert all(out[q]==v for q,v in nr.items() if q<890 or q>=900)
        writable=lambda a:O<=a<O+3*M or I<=a<I+M
        assert all(heap[a]==v for a,v in nh.items() if not writable(a))
        assert all(a in nh or writable(a) for a in heap)
        assert all(writable(a) for a,_ in writes)
        assert [a for a in reads if T<=a<T+3*M]==[T+3*i+h for i in ords for h in range(3)]
        if spec.get('matching'):
            physical_matching+=1
            assert all(not(set(rows[i][:2])&set(rows[j][:2])) for i in ords for j in ords if i!=j)
        all_pcs.update(pcs)
        traces.append(dict(index=index,dirty=dirty,M=M,k=k,steps=t,count=len(ords),origin=spec['origin'],exact_selected=True,frames=True))
assert all_pcs==set(range(30)),set(range(30))-all_pcs
negative=[]
M=2;k=1;T=100;C=106;O=108;I=114;B=4000
nr={880:M,881:T,882:C,883:k,884:O,885:I}
nh={T:1,T+1:2,T+2:700,T+3:3,T+4:4,T+5:701,C:1,C+1:0}
for name,regs,heap,word,start in [
 ('missing color',nr,{a:v for a,v in nh.items() if a!=C},B,0),
 ('missing interior color',nr,{a:v for a,v in nh.items() if a!=C+1},B,0),
 ('missing selected destination',nr,{a:v for a,v in nh.items() if a!=T},B,0),
 ('missing selected source',nr,{a:v for a,v in nh.items() if a!=T+1},B,0),
 ('missing selected coefficient',nr,{a:v for a,v in nh.items() if a!=T+2},B,0),
 ('oversized selected coefficient',nr,{**nh,T+2:B+1},B,0),
 ('entry word guard',nr,nh,113,0),
 ('runtime output word guard',{**nr,884:B-2,885:B-1},{**nh,C+1:1},B,0),('missing instruction',nr,nh,B,30)]:
    try:execute(regs,heap,word,start)
    except Failure as e:negative.append(dict(name=name,observed=str(e)))
    else:raise AssertionError(name)
# Unselected row data are not loaded; fullRows is a sufficient entry contract.
out,heap,*_=execute(nr,{a:v for a,v in nh.items() if not(T+3<=a<T+6)},B)
assert out[894]==1
# Arbitrary corrupt colors filter honestly but need not imply matching.
out,heap,*_=execute(nr,{**nh,C+1:1,T+3:2,T+4:3},B)
assert [heap[O+j] for j in range(6)]==[1,2,700,2,3,701]
report=dict(status='PASS',cases=len(traces),steps=sum(t['steps'] for t in traces),all_pcs=sorted(all_pcs),physical_Color51_matching_cases=physical_matching,negative=negative,diagnostics=['unselected row data not loaded','incorrect arbitrary colors may select conflicting endpoints'],program_sha256=hashlib.sha256((root/'program.json').read_bytes()).hexdigest(),specs_sha256=hashlib.sha256((root/'specs.json').read_bytes()).hexdigest(),traces=traces)
(root/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='traces'},indent=2))
