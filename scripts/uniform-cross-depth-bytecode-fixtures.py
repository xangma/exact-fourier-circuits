#!/usr/bin/env python3
"""Actual132 directory→shears→colors, fresh typed K0 and fresh physical K0..4 references."""
import json,hashlib
from fractions import Fraction
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/cross-depth'
code=json.loads((root/'program.json').read_text())
assert len(code)==132 and all(r[0] in range(7) for r in code)
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


def greed(rows):
    colors=[]
    for i,(dst,src,_) in enumerate(rows):
        blocked={colors[j] for j,(a,b,_) in enumerate(rows[:i]) if dst in (a,b) or src in(a,b)}
        colors.append(next((c for c in range(11) if c not in blocked),11))
    return colors

cases=[]
for K,a,n,enabled,d,rs,order,offsets,expected,colors in json.loads((root/'typed-cross.json').read_text()):
    cases.append(dict(origin='fresh Lean actual typed K0 bucket/colors',K=K,a=a,n=n,enabled=enabled,d=d,
                      rows=rs,order=order,offsets=offsets,expected=expected,colors=colors))
for K,a,n,enabled,d,rs,order,offsets,expected,colors in json.loads((root/'typed.json').read_text()):
    cases.append(dict(origin='fresh Lean explicit4-gate typed bucket/colors',K=K,a=a,n=n,enabled=enabled,d=d,
                      rows=rs,order=order,offsets=offsets,expected=expected,colors=colors))
cached=root.parent/'cross-shear/physical.json' 
for K,a,n,enabled,rs,order,expected,levels in json.loads(cached.read_text()):
    if K==0:continue
    G=len(rs);depth=dict(enumerate(levels))
    offsets=[sum(1 for j in order if depth[j]<d) for d in range(G+2)]
    chosen=list(range(8*K+7)) if K<=2 else sorted({0,1,8*K+6,max(range(8*K+7),key=lambda d:levels.count(d))})
    for d in chosen:
        output=[row for row in expected if depth[row[0]-10000-n-1]==d]
        colors=greed(output)
        cases.append(dict(origin='fresh frozen60 physical Cross271/depth/expansion + independent greedy',K=K,a=a,n=n,
                          enabled=enabled,d=d,rows=rs,order=order,offsets=offsets,expected=output,colors=colors))

summary=[];allpcs=set();total=0
for index,spec in enumerate(cases):
    rs,order,expected,colors=spec['rows'],spec['order'],spec['expected'],spec['colors'];G=len(rs);M=len(expected)
    assert colors==greed(expected)
    degree={}
    for a,b,_ in expected:
        assert a!=b
        degree[a]=degree.get(a,0)+1;degree[b]=degree.get(b,0)+1
    assert max(degree.values(),default=0)<=6
    for dirty in range(2):
        T=13+dirty*19;Q=T+5*G+9;R=Q+G+9;D=R+G+11;F=D+6*G+9;U=F+2*G+9
        A,C,P,N=10000,20000,30000,1<<spec['K'];B=200000
        nr={j:(37*j+13+dirty)%B for j in range(1024)}
        nr.update({900:G,901:spec['d'],902:T,903:Q,904:R,905:D,906:A,907:C,908:P,909:spec['n'],
                   911:N,912:spec['enabled'],913:F,914:U})
        nh={0:71,7:41,B-1:3}
        for j,row in enumerate(rs):
            for q,v in enumerate(row):nh[T+5*j+q]=v
        for j,value in enumerate(order):nh[Q+j]=value
        for j,value in enumerate(spec['offsets']):nh[R+j]=value
        for j in range(6*G):nh[D+j]=(13*j+dirty+7)%B
        for j in range(2*G):nh[F+j]=(19*j+dirty+5)%B
        for j in range(12):nh[U+j]=(17*j+dirty+11)%B
        sh={0:((Fraction(0),Fraction(1)),False),C:((Fraction(0),Fraction(0)),False),
            A:((Fraction(9,4),Fraction(-1)),True),B-1:((Fraction(-1,7),Fraction(5,3)),True)}
        sr={j:((Fraction(j,11),Fraction(-j,7)),bool(j%2)) for j in range(100)}
        output={0:((Fraction(3),Fraction(4)),True)};roots=[17,64]
        before=(nr.copy(),nh.copy(),sh.copy(),sr.copy(),output.copy(),roots.copy())
        result,heap,steps,pcs,pc,writes=execute(code,nr,nh,B)
        assert pc==131 and result[800]==M and result[736]==M, dict(case=index,K=spec["K"],n=spec["n"],enabled=spec["enabled"],d=spec["d"],M=M,pc=pc,count800=result[800],count736=result[736],headers={j:result[j] for j in range(720,730)})
        actual=[[heap[D+3*j+q] for q in range(3)] for j in range(M)]
        actual_colors=[heap[F+j] for j in range(M)]
        assert actual==expected and actual_colors==colors and all(c<11 for c in colors)
        assert steps<=64*G+200*(2*G+1)**2+31
        for j,v in nr.items():
            if not(720<=j<750 or 800<=j<824 or 920<=j<925):assert result[j]==v,(j,result[j],v)
        for a,v in nh.items():
            if not(D<=a<D+6*G or F<=a<F+2*G or U<=a<U+12):assert heap[a]==v
        assert all(D<=a<D+6*G or F<=a<F+2*G or U<=a<U+12 for a,_ in writes)
        assert (sh,sr,output,roots)==before[2:]
        for i,(a,b,_) in enumerate(actual):
            for j,(c,d,_) in enumerate(actual[:i]):
                if actual_colors[i]==actual_colors[j]:assert len({a,b,c,d})==4
        assert all(result[j]==nr[j] for j in range(100,107))
        assert all(heap[R+j]==v for j,v in enumerate(spec['offsets']))
        total+=steps;allpcs|=pcs
        summary.append(dict(index=index,dirty=dirty,origin=spec['origin'],K=spec['K'],G=G,d=spec['d'],rows=M,
                            max_degree=max(degree.values(),default=0),colors=max(colors,default=-1)+1,steps=steps))

# Negative controls exercise actual loads and ambient-word guards.
spec=next(s for s in cases if s['expected'] and s['n']==1 and s['enabled'])
G=len(spec['rows']);T=13;Q=T+5*G+9;R=Q+G+9;D=R+G+11;F=D+6*G+9;U=F+2*G+9;B=200000
nr={900:G,901:spec['d'],902:T,903:Q,904:R,905:D,906:10000,907:20000,908:30000,909:spec['n'],
    911:1<<spec['K'],912:1,913:F,914:U}
nh={}
for j,row in enumerate(spec['rows']):
    for q,v in enumerate(row):nh[T+5*j+q]=v
for j,v in enumerate(spec['order']):nh[Q+j]=v
for j,v in enumerate(spec['offsets']):nh[R+j]=v
first=spec['offsets'][spec['d']];ordinal=spec['order'][first]
negative=[]
for name,removed in [('missing directory start',R+spec['d']),('missing directory end',R+spec['d']+1),
                     ('missing stable ordinal',Q+first),('missing typed opcode',T+5*ordinal),
                     ('missing typed coefficient payload',T+5*ordinal+4)]:
    h=nh.copy();h.pop(removed)
    try:execute(code,nr,h,B)
    except Failure as e:negative.append([name,str(e)])
    else:raise AssertionError(name+' did not fail')
try:execute(code,nr,nh,131)
except Failure as e:negative.append(['insufficient shared word bound',str(e)])
else:raise AssertionError('word bound')

report=dict(status='PASS',literal_instructions=len(code),success_cases=len(summary),negative_controls=negative,
            steps_total=total,pcs_covered=sorted(allpcs),pcs_uncovered=sorted(set(range(len(code)))-allpcs),
            cases=summary,provenance=dict(fresh_typed_case_specs=56,
                fresh_physical_source=str(cached),fresh_physical_sha256=hashlib.sha256(cached.read_bytes()).hexdigest(),
                physical_color_oracle='Independent Python indexed greedy; fresh K0 colors come from Lean.',
                source_entry='Physical typed tape/order/directory are honest input banks; no phase host writes inside132.'))
(root/'bytecode-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('cases','provenance')},indent=2))
