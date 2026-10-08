import json,hashlib
from fractions import Fraction
from pathlib import Path
repo=Path(__file__).resolve().parents[1]
root=repo/'logs/uniform-bytecode/cross-height'
code=json.loads((root/'program.json').read_text())
assert len(code)==186 and all(r[0] in range(7) for r in code)
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
for K,a,e,enabled,rs,order,offsets,slices in json.loads((root/'typed.json').read_text()):
    assert len(slices)==8*K+7
    cases.append(dict(origin='fresh Lean actual Cross typed full-height rows/colors',K=K,a=a,e=e,
                      enabled=enabled,rows=rs,order=order,offsets=offsets,slices=slices))
cached=root.parent/'cross-shear/physical.json'
for K,a,e,enabled,rs,order,expected,levels in json.loads(cached.read_text()):
    if K==0:continue
    G=len(rs)
    assert G==6*(3*K*(1<<K)+2*(1<<K))+2*a
    offsets=[sum(1 for j in order if levels[j]<d) for d in range(G+2)]
    rows=[[dst-10000,src-10000,c] for dst,src,c in expected]
    slices=[]
    for d in range(8*K+7):
        W=[row for row in rows if levels[row[0]-e-1]==d]
        slices.append([W,greed(W)])
    cases.append(dict(origin='fresh standard60 actual Cross rows/order/levels with independent grouped greedy',
                      K=K,a=a,e=e,enabled=enabled,rows=rs,order=order,offsets=offsets,slices=slices))

summary=[];pcs=set();stepstotal=0
for index,c in enumerate(cases):
    K,a,e,enabled,rs,order,offsets,slices=(c[k] for k in ['K','a','e','enabled','rows','order','offsets','slices'])
    N=1<<K;G=6*(3*K*N+2*N)+2*a;H=8*K+7
    assert len(rs)==G and len(order)==G and len(offsets)==G+2
    assert sorted(order)==list(range(G))
    assert all(colors==greed(rows) for rows,colors in slices)
    for dirty in range(3):
        T=13+dirty*19;Q=T+5*G+9;R=Q+G+9;D=R+G+11
        F=D+6*G*H+9;U=F+2*G*H+9;J=U+23;C=20000;P=30000;Z=40000
        B=max(200000,J+3*H+10000)
        nr={j:(37*j+13+dirty)%B for j in range(1150)}
        nr.update({1050:K,1051:a,1052:e,1053:T,1054:Q,1055:R,1056:D,1057:F,
                   1058:U,1059:J,1060:C,1061:enabled,1062:P})
        nh={0:71,7:41,B-1:3}
        for j,row in enumerate(rs):
            for q,v in enumerate(row):nh[T+5*j+q]=v
        for j,v in enumerate(order):nh[Q+j]=v
        for j,v in enumerate(offsets):nh[R+j]=v
        for j in range(6*G*H):nh[D+j]=(13*j+dirty+7)%B
        for j in range(2*G*H):nh[F+j]=(19*j+dirty+5)%B
        for j in range(12):nh[U+j]=(17*j+dirty+11)%B
        for j in range(3*H):nh[J+j]=(23*j+dirty+7)%B
        sh={0:((Fraction(0),Fraction(1)),False),C:((Fraction(0),Fraction(0)),False),
            10000:((Fraction(9,4),Fraction(-1)),True),B-1:((Fraction(-1,7),Fraction(5,3)),True)}
        sr={j:((Fraction(j,11),Fraction(-j,7)),bool(j%2)) for j in range(100)}
        outputs={0:(Fraction(3),Fraction(4))};roots=[17,64]
        before=(nr.copy(),nh.copy(),sh.copy(),sr.copy(),outputs.copy(),roots.copy())
        result,heap,steps,seen,pc,writes=execute(code,nr,nh,B)
        assert pc==185 and result[1071]==N and result[1072]==G and result[1073]==H and result[1074]==H
        assert result[1075]==D+6*G*H and result[1076]==F+2*G*H and result[1077]==J+3*H
        for d,(rows,colors) in enumerate(slices):
            rd,cd=D+6*G*d,F+2*G*d;M=len(rows)
            assert M<=2*G and [heap[J+3*d+q] for q in range(3)]==[M,rd,cd]
            assert [[heap[rd+3*j+q] for q in range(3)] for j in range(M)]==rows
            assert [heap[cd+j] for j in range(M)]==colors and all(x<11 for x in colors)
            degree={}
            for dst,src,coefficient in rows:
                assert src!=e and dst>e and src<dst<e+1+G
                degree[dst]=degree.get(dst,0)+1;degree[src]=degree.get(src,0)+1
            assert max(degree.values(),default=0)<=6
            for i,(dst,src,_) in enumerate(rows):
                for j,(otherdst,othersrc,_) in enumerate(rows[:i]):
                    if colors[i]==colors[j]:assert len({dst,src,otherdst,othersrc})==4
        assert steps<=4*K+27+H*(64*G+200*(2*G+1)**2+56)
        def changed(j):return (720<=j<750 or 800<=j<824 or 900<=j<915 or 920<=j<925 or 1063<=j<1080)
        for j,v in nr.items():
            if not changed(j):assert result[j]==v,(j,result[j],v)
        def writable(j):return D<=j<D+6*G*H or F<=j<F+2*G*H or U<=j<U+12 or J<=j<J+3*H
        for j,v in nh.items():
            if not writable(j):assert heap[j]==v
        assert all(writable(j) for j,_ in writes)
        assert (sh,sr,outputs,roots)==before[2:]
        assert all(result[j]==nr[j] for j in range(100,107))
        pcs|=seen;stepstotal+=steps
        summary.append(dict(index=index,dirty=dirty,origin=c['origin'],K=K,G=G,height=H,
                            total_rows=sum(len(v[0]) for v in slices),empty_depths=sum(not v[0] for v in slices),steps=steps))

# Actual missing-read controls; no host phase initialization between calls.
c=next(c for c in cases if c['K']==1 and c['enabled'])
K,a,e,rs,order,offsets=c['K'],c['a'],c['e'],c['rows'],c['order'],c['offsets'];G=len(rs);H=8*K+7
T=13;Q=T+5*G+9;R=Q+G+9;D=R+G+11;F=D+6*G*H+9;U=F+2*G*H+9;J=U+23;B=200000
nr={1050:K,1051:a,1052:e,1053:T,1054:Q,1055:R,1056:D,1057:F,1058:U,1059:J,1060:20000,1061:1,1062:30000}
nh={}
for j,row in enumerate(rs):
    for q,v in enumerate(row):nh[T+5*j+q]=v
for j,v in enumerate(order):nh[Q+j]=v
for j,v in enumerate(offsets):nh[R+j]=v
negative=[]
for name,removed in [('missing initial bucket start',R),('missing terminal active bucket end',R+H),
                     ('missing first actual ordinal',Q),('missing typed opcode',T+5*order[0]),
                     ('missing typed payload',T+5*order[0]+4)]:
    broken=nh.copy();broken.pop(removed)
    try:execute(code,nr,broken,B)
    except Failure as ex:negative.append([name,str(ex)])
    else:raise AssertionError(name+' unexpectedly succeeded')
try:execute(code,nr,nh,185)
except Failure as ex:negative.append(['insufficient shared word bound',str(ex)])
else:raise AssertionError('word bound')
report=dict(status='PASS',literal_instructions=186,success_cases=len(summary),negative_controls=negative,
            steps_total=stepstotal,pcs_covered=sorted(pcs),pcs_uncovered=sorted(set(range(186))-pcs),cases=summary,
            provenance=dict(fresh_Lean_specs=4,fresh_cross_sizes=[12,14],cached_physical_source=str(cached),
                cached_physical_sha256=hashlib.sha256(cached.read_bytes()).hexdigest(),
                cached_color_oracle='Independent Python indexed greedy, grouped by original ordinal depth; fresh colors from Lean.',
                entry='Only original physical typed tape and Bucket24 source order/directory are initialized; no host writes between phases.',
                scalar_frame='Exact Gaussian dirty banks/tags/root/output are retained; exported186 instructions are ALLNat and never access them.'))
(root/'bytecode-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('cases','provenance')},indent=2))
