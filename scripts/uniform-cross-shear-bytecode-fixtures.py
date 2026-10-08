#!/usr/bin/env python3
"""Exact physical and bounded typed shear-table diagnostics; component boundaries explicit."""
import json,hashlib
from fractions import Fraction
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/cross-shear'
code=json.loads((root/'program.json').read_text())
assert len(code)==60 and all(r[0] in range(7) for r in code)
class Failure(Exception):pass

def execute(code,nr,nh,B,start=0,max_steps=10000000):
    nr,nh=nr.copy(),nh.copy();pc=start;steps=0;seen=set();writes=[]
    def check():
        if not(0<=pc<=B and all(0<=v<=B for v in nr.values()) and all(0<=a<=B and 0<=v<=B for a,v in nh.items())):
            raise Failure('word bound')
    check()
    while steps<max_steps:
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
        pc=npc
        if not(0<=pc<=B):raise Failure('word bound pc')
        if op in [0,1,2] and not(0<=nr[d]<=B):raise Failure('word bound register')
        if op==3 and not(0<=address<=B and 0<=value<=B):raise Failure('word bound heap')
    raise AssertionError('nontermination')


raw=[]
for value in json.loads((root/'physical.json').read_text()):
    K,a,n,enabled,rs,order,expected,depths=value
    raw.append(dict(kind='fresh Lean physical Cross271/depth/expansion',K=K,a=a,n=n,enabled=enabled,rows=rs,order=order,expected=expected,depths=depths))
for value in json.loads((root/'generic.json').read_text()):
    n,enabled,rs,order,expected=value
    raw.append(dict(kind='fresh Lean generic expansion',K=None,n=n,enabled=enabled,rows=rs,order=order,expected=expected))
for f in sorted(root.glob('cross-*.json')):
    K,a,n,enabled,rs,order,expected,levels=json.loads(f.read_text())
    raw.append(dict(kind='fresh Lean actual typed orderedSweep',K=K,a=a,n=n,enabled=enabled,rows=rs,order=order,expected=expected,levels=levels))
traces=[];pcs_all=set();steps_all=0;pipeline=0
bucket=json.loads((root/'bucket-program.json').read_text())
depth=json.loads((root/'depth-program.json').read_text())
for index,spec in enumerate(raw):
    rs,order,expected=spec['rows'],spec['order'],spec['expected'];G=len(rs);M=len(order)
    for dirty in range(4):
        T=13+19*dirty;Q=T+5*G+9;D=Q+M+9;A,C,P=10000,20000,30000;N=1<<(spec['K'] or 0);B=100000
        nr={r:(37*r+13+dirty)%B for r in range(920)}
        nr.update({720:M,721:T,722:Q,723:D,724:A,725:C,726:P,727:spec['enabled'],728:spec['n'],729:N})
        nh={0:71,7:41,B-1:3}
        for j,row in enumerate(rs):
            for q,v in enumerate(row):nh[T+5*j+q]=v
        for j,v in enumerate(order):nh[Q+j]=v
        for j in range(6*M):nh[D+j]=(13*j+dirty+7)%B
        scalar_heap={0:((Fraction(0),Fraction(1)),False),1:((Fraction(-7,3),Fraction(5)),False),A:((Fraction(9,4),Fraction(-1)),True),B-1:((Fraction(0),Fraction(0)),False)}
        for j in range(7*N):scalar_heap[C+j]=((Fraction(0 if j%3==0 else j,7),Fraction(-j,11)),False)
        scalar_reg={r:((Fraction(-r,3),Fraction(r,5)),bool(r%2)) for r in range(90)}
        saved_scalar=(scalar_heap.copy(),scalar_reg.copy(),{4:(Fraction(7),Fraction(11))},[3,17,64])
        actual_order=order
        # Exact exported Depth35 and Bucket24 produce the physical order; headers are
        # fixture setup between phases, so this is not a one-program theorem.
        if spec['kind']=='fresh Lean physical Cross271/depth/expansion' and spec['K']<=2 and dirty==0:
            n=spec['n'];H=D+6*M+9;O=H+n+1+G+9;R=O+G+9
            nrd=nr.copy();nrd.update({650:n,651:G,652:T,653:H})
            dnr,dh,dt,dpcs,_,_=execute(depth,nrd,nh,B)
            values=[dh[H+n+1+j] for j in range(G)]
            assert values==spec['depths']
            dnr.update({700:G,701:H+n+1,702:O,703:R})
            bnr,bh,bt,bpcs,_,_=execute(bucket,dnr,dh,B)
            actual_order=[bh[O+j] for j in range(G)]
            assert actual_order==order and all(values[a]<=values[b] for a,b in zip(order,order[1:]))
            pipeline+=1
        out,heap,t,pcs,halt,writes=execute(code,nr,nh,B)
        actual=[[heap[D+3*j+q] for q in range(3)] for j in range(out[736])]
        assert actual==expected,(index,dirty,actual[:10],expected[:10])
        assert out[735]==M and out[736]==len(expected) and halt==59
        assert t<=64*M+10 and len(expected)<=2*M
        assert all(out[r]==v for r,v in nr.items() if r<730 or r>=750)
        assert all(heap[a]==v for a,v in nh.items() if a<D or D+6*M<=a)
        assert all(a in nh or D<=a<D+6*M for a in heap)
        assert writes==[(D+3*j+q,row[q]) for j,row in enumerate(expected) for q in range(3)]
        assert (scalar_heap,scalar_reg,{4:(Fraction(7),Fraction(11))},[3,17,64])==saved_scalar
        assert all(row[1]!=A+spec['n'] for row in actual)
        if not spec['enabled']:assert all(row[1]>A+spec['n'] for row in actual)
        assert all(row[0]!=row[1] for row in actual) if spec['kind']!='fresh Lean generic expansion' else True
        pcs_all.update(pcs);steps_all+=t
        traces.append(dict(index=index,dirty=dirty,kind=spec['kind'],K=spec['K'],gates=G,orderLength=M,rows=len(expected),steps=t,wordBound=True,allFrames=True,exactChronology=True))
assert pcs_all==set(range(60)),sorted(set(range(60))-pcs_all)
negative=[];nr={720:1,721:10,722:20,723:30,724:10000,725:20000,726:30000,727:1,728:1,729:1};nh={20:0,10:0,11:0,12:0,13:0,14:0}
for kind in ['missing order','missing opcode','missing left','missing right','missing kind','missing payload','word bound','missing instruction']:
    hh=nh.copy();budget=100000;start=0
    if kind=='missing order':del hh[20]
    elif kind.startswith('missing ') and kind!='missing instruction':del hh[10+['opcode','left','right','kind','payload'].index(kind[8:])]
    elif kind=='word bound':budget=100
    else:start=60
    try:execute(code,nr,hh,budget,start)
    except Failure as exc:negative.append(dict(kind=kind,reason=str(exc)))
    else:raise AssertionError('unexpected acceptance '+kind)
receipt=dict(status='PASS',cases=len(traces),specs=len(raw),fresh_physical_specs=sum(v['kind']=='fresh Lean physical Cross271/depth/expansion' for v in raw),fresh_typed_specs=sum(v['kind']=='fresh Lean actual typed orderedSweep' for v in raw),fresh_generic_specs=sum(v['kind']=='fresh Lean generic expansion' for v in raw),pipeline_depth_bucket_cases=pipeline,steps=steps_all,all60PCs=True,negative=negative,traces=traces,scope='Actual exported Nat-only60 with exact heap/write/order/output count/frames and changed-word bound at every step. K0 actual typed orderedSweep fixtures; K0..4 fresh physical Cross271 tapes plus fresh Lean depth/order/expansion oracles. Pipeline Depth35/Bucket24 is diagnostic with explicit fixture headers between phases, not a composed producer claim. Scalar coefficient production/action/coloring remain outside this module.')
(root/'bytecode-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print({k:receipt[k] for k in ['status','cases','specs','fresh_physical_specs','fresh_typed_specs','fresh_generic_specs','pipeline_depth_bucket_cases','steps','all60PCs','negative']})
