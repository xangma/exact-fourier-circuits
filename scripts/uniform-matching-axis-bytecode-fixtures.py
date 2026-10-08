#!/usr/bin/env python3
"""Exact fresh Lean bytecode and reference-table diagnostics."""
import json, random, hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/matching-axis'
code=json.loads((root/'program.json').read_text())
lean_specs=json.loads((root/'specs.json').read_text())
assert len(code)==55 and all(row[0] in range(7) for row in code)
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

def oracle(r,edges):
    paired=[v for e in edges for v in e]
    return paired+[j for j in range(r) if j not in paired], [2]*len(edges)+[1]*(r-2*len(edges))

specs=[]
for r,M,seed,edges,order,widths in lean_specs:
    o,w=oracle(r,edges);assert (o,w)==(order,widths)
    specs.append(dict(r=r,M=M,edges=edges,order=o,widths=w,origin='fresh Lean ordered/widths'))
rng=random.Random(130)
for r in [1,2,7,31,100,257]:
    for M in [0,r//3,r//2]:
        coords=list(range(r));rng.shuffle(coords)
        edges=[coords[2*j:2*j+2] for j in range(M)]
        o,w=oracle(r,edges)
        specs.append(dict(r=r,M=M,edges=edges,order=o,widths=w,origin='independent integer oracle'))
traces=[];all_pcs=set()
for index,spec in enumerate(specs):
    r,M,edges=spec['r'],spec['M'],spec['edges']
    order,widths=spec['order'],spec['widths']
    assert len(order)==r and len(set(order))==r and sorted(order)==list(range(r))
    for dirty in range(3):
        T=11+dirty*100;P=T+3*M+3*dirty;W=P+r+7*dirty;U=W+r+11*dirty;A=U+r+13*dirty;B=A+3000
        nr={q:(q*37+dirty+17)%B for q in range(920)};nr.update({840:r,841:M,842:T,843:P,844:W,845:U,846:A})
        nh={0:19,7:21,B-1:17}
        for j,(l,h) in enumerate(edges):
            nh[T+3*j]=l;nh[T+3*j+1]=h
            if j%3!=dirty:nh[T+3*j+2]=(71*j+dirty)%B
        for base,length in [(P,r),(W,r),(U,r),(A,4)]:
            for j in range(length):
                if j%3!=dirty:nh[base+j]=(47+3*j)%B
        out,heap,t,pcs,halt,writes,reads=execute(nr,nh,B)
        assert [heap[P+j] for j in range(r)]==order
        assert [heap[W+j] for j in range(len(widths))]==widths
        assert [heap[U+j] for j in range(r)]==[int(any(j in e for e in edges)) for j in range(r)]
        assert [heap[A+j] for j in range(4)]==[r-M,W,r,P]
        assert t==17*r+8*M+21 and t<=21*r+21 and halt==54
        assert all(out[q]==v for q,v in nr.items() if q<850 or q>=862)
        def writable(a):return P<=a<P+r or W<=a<W+r or U<=a<U+r or A<=a<A+4
        assert all(heap[a]==v for a,v in nh.items() if not writable(a))
        assert all(a in nh or writable(a) for a in heap)
        assert all(writable(a) for a,_ in writes)
        assert all(a<T+3*M for a in reads if a<U),'coefficient ignored/read rows only'
        assert not any(a==T+3*j+2 for j in range(M) for a in reads)
        assert sum(widths)==r and len(widths)==r-M and set(widths)<=set([1,2])
        all_pcs.update(pcs)
        traces.append(dict(index=index,dirty=dirty,r=r,M=M,steps=t,origin=spec['origin'],exact_axis=True,frames=True))
assert all_pcs==set(range(55)),set(range(55))-all_pcs
negative=[]
r=4;M=1;T=100;P=120;W=130;U=140;A=150;B=4000
nr={840:r,841:M,842:T,843:P,844:W,845:U,846:A};nh={T:0,T+1:1}
for name,regs,heap,word,start in [
 ('missing left',nr,{T+1:1},B,0),('missing right',nr,{T:0},B,0),
 ('oversized loaded endpoint',nr,{T:0,T+1:B+1},B,0),
 ('address/result word guard',nr,nh,150,0),('missing instruction',nr,nh,B,55)]:
    try:execute(regs,heap,word,start)
    except Failure as e:negative.append(dict(name=name,observed=str(e)))
    else:raise AssertionError(name)
# A shared endpoint violates Matching and visibly fails the permutation/width contract.
r=4;M=2;T=100;P=110;W=120;U=130;A=140
nr={840:r,841:M,842:T,843:P,844:W,845:U,846:A}
nh={T:0,T+1:1,T+3:1,T+4:2}
out,heap,t,pcs,halt,writes,reads=execute(nr,nh,B)
nonmatching=[heap[P+j] for j in range(out[855])]
assert nonmatching==[0,1,1,2,3] and out[855]!=r and heap[A]!=r-M
report=dict(status='PASS',cases=len(traces),steps=sum(c['steps'] for c in traces),all_pcs=sorted(all_pcs),negative=negative,nonmatching_diagnostic=dict(order=nonmatching,actual_count=out[855],radix=r),program_sha256=hashlib.sha256((root/'program.json').read_bytes()).hexdigest(),specs_sha256=hashlib.sha256((root/'specs.json').read_bytes()).hexdigest(),traces=traces)
(root/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='traces'},indent=2))
