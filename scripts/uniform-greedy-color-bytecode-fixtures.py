#!/usr/bin/env python3
"""Exact fresh Lean bytecode and reference-table diagnostics."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/greedy-color'
code=json.loads((root/'program.json').read_text())
lean_specs=json.loads((root/'specs.json').read_text())
assert len(code)==51 and all(row[0] in range(7) for row in code)
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

def greedy(edges):
    colors=[]
    for j,current in enumerate(edges):
        used={colors[i] for i,old in enumerate(edges[:j]) if set(current)&set(old)}
        colors.append(next((c for c in range(11) if c not in used),11))
    return colors

def tests_cost(current,old):
    steps=0
    for left,right in [(old[0],current[0]),(old[0],current[1]),(old[1],current[0]),(old[1],current[1])]:
        steps+=1 if left<right else 2
        if left==right:return steps,True
    return steps,False

def expected_runtime(edges,colors):
    rows=0
    for j,current in enumerate(edges):
        scan=0
        for old in edges[:j]:
            comparisons,conflict=tests_cost(current,old)
            scan+=8+comparisons+(5 if conflict else 0)
        choose=6*colors[j]+(1 if colors[j]==11 else 4)
        rows+=69+scan+choose
    return 7+len(edges)+rows

specs=[]
for M,family,edges,lean_colors in lean_specs:
    colors=greedy(edges);assert colors==lean_colors and len(edges)==M
    specs.append(dict(M=M,family=family,edges=edges,colors=colors,origin='fresh Lean greedy'))
for M in [25,36,64]:
    for family in ['parallel','star','ragged','reverse']:
        if family=='parallel':edges=[(1,2)]*M
        elif family=='star':edges=[(0,i+1) for i in range(M)]
        elif family=='reverse':edges=[(i,i+1) if i%2==0 else (i+1,i) for i in range(M)]
        else:
            edges=[((7*i*i+i+3)%17,(10*i+7)%17) for i in range(M)]
            edges=[(a,b+1 if a==b else b) for a,b in edges]
        specs.append(dict(M=M,family=family,edges=edges,colors=greedy(edges),origin='independent integer oracle'))
traces=[];all_pcs=set();sentinel_cases=0;degree_cases=0
for index,spec in enumerate(specs):
    M=spec['M'];edges=spec['edges'];colors=spec['colors']
    assert all(a!=b for a,b in edges)
    for dirty in range(3):
        T=13+dirty*100;C=T+3*M+7*dirty;U=C+M+11*dirty;B=U+3000
        nr={r:(r*37+dirty+17)%B for r in range(860)};nr.update({800:M,801:T,802:C,803:U})
        nh={0:19,7:21,B-1:17}
        for j,(a,b) in enumerate(edges):nh[T+3*j]=a;nh[T+3*j+1]=b;nh[T+3*j+2]=(71*j+dirty)%B
        for j in range(M):nh[C+j]=29+j
        for j in range(12):
            if j%3!=dirty:nh[U+j]=47+3*j
        out,heap,t,pcs,halt,writes,reads=execute(nr,nh,B)
        assert [heap[C+j] for j in range(M)]==colors
        assert t==expected_runtime(edges,colors) and t<=200*(M+1)**2 and halt==50
        assert all(v<=11 for v in colors)
        assert all(out[r]==v for r,v in nr.items() if r<810 or r>=824)
        assert all(heap[a]==v for a,v in nh.items() if not(C<=a<C+M or U<=a<U+12))
        assert all(a in nh or C<=a<C+M or U<=a<U+12 for a in heap)
        assert all(not(U+11==a) for a in reads),'sentinel read'
        assert [v for a,v in writes if C<=a<C+M]==colors
        assert all(a in range(C,C+M) or a in range(U,U+12) for a,_ in writes)
        degree=max([sum(v in edge for edge in edges) for v in {v for edge in edges for v in edge}],default=0)
        if degree<=6:
            degree_cases+=1;assert all(v<11 for v in colors)
            assert all(colors[i]!=colors[j] for i in range(M) for j in range(i) if set(edges[i])&set(edges[j]))
        if 11 in colors:sentinel_cases+=1
        if colors.count(11)>=2:assert any(a==U+11 for a,_ in writes)
        all_pcs.update(pcs)
        traces.append(dict(index=index,dirty=dirty,M=M,steps=t,degree=degree,origin=spec['origin'],exact_greedy=True,sentinel_unread=True,frames=True))
assert all_pcs==set(range(51)),set(range(51))-all_pcs
negative=[]
M=13;T=100;C=200;U=300;B=3000
nr={800:M,801:T,802:C,803:U};nh={T+3*i+j:v for i in range(M) for j,v in enumerate([1,2,37+i])}
for kind in ['missing first endpoint','missing interior endpoint','word bound','missing instruction','missing color at mark','missing palette at selection','unallocated sentinel']:
    heap=nh.copy();regs=nr.copy();budget=B;start=0
    if kind=='missing first endpoint':del heap[T]
    elif kind=='missing interior endpoint':del heap[T+3*5+1]
    elif kind=='word bound':budget=50
    elif kind=='missing instruction':start=51
    elif kind=='missing color at mark':start=34;regs.update({815:0,811:1})
    elif kind=='missing palette at selection':start=41;regs.update({816:0})
    else:budget=U+10
    try:execute(regs,heap,budget,start)
    except Failure as exc:negative.append(dict(kind=kind,reason=str(exc)))
    else:raise AssertionError('guard accepted '+kind)
receipt=dict(status='PASS',cases=len(traces),fresh_lean_specs=len(lean_specs),independent_large_specs=len(specs)-len(lean_specs),steps=sum(t['steps'] for t in traces),all51_pcs=True,sentinel_cases=sentinel_cases,degree_six_cases=degree_cases,negative_controls=negative,traces=traces,scope='Fresh literal51 and bounded Lean expected greedy tables; larger independent integer oracle clearly separate. Exact Nat arithmetic, original-source/read/write frames, charged per-instruction WordBound. No Scalar/root/input/output opcode. Sentinel11 is marked but never read. Degree-six matching asserted only for actually measured local fixture degree<=6.')
(root/'fixtures.json').write_text(json.dumps(receipt,indent=2)+'\n')
print({k:receipt[k] for k in ['status','cases','fresh_lean_specs','independent_large_specs','steps','all51_pcs','sentinel_cases','degree_six_cases','negative_controls']})
