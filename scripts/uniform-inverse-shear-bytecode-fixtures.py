import json,random,hashlib
from pathlib import Path
repo=Path(__file__).resolve().parents[1]
root=repo/'logs/uniform-bytecode/inverse-shear'
code=json.loads((root/'program.json').read_text())
lean_specs=json.loads((root/'specs.json').read_text())
assert len(code)==36 and all(row[0] in range(7) for row in code)
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


from fractions import Fraction as F
# Execute frozen literal42 independently to obtain the actual prepared signed bank.
coeff_root=root.parent/'replay-coefficient'
coeff_script=repo/'scripts/uniform-replay-coefficient-bytecode-fixtures.py'
coeff_namespace={'__file__':str(coeff_script)}
coeff_prefix=coeff_script.read_text().split('traces=[];all_pcs=set();total_steps=0')[0]
exec(compile(coeff_prefix,str(coeff_script),'exec'),coeff_namespace)
value=coeff_namespace['value'];coeff_execute=coeff_namespace['execute']
prepared={};coeff_traces=[]
for K in range(9):
    m=7*2**K;C=29;T=C+m+11;P=T+m+17;B=P+2000
    source={C+j:value(F((j*j+K+3)%19-9,3),F((j+K)%7-3,5)) for j in range(m)}
    source[C]=value(0)
    nr,nh,sr,sh,steps,pcs,halt,_=coeff_execute({760:K,761:C,762:T,763:P},{},{},source,B)
    assert steps==5*K+56*2**K+31 and halt==41
    assert [sh[T+j] for j in range(m)]==[coeff_namespace['neg'](source[C+j]) for j in range(m)]
    assert sh[P+2]==value(F(1,2**K)) and sh[P+3]==value(F(-1,2**K))
    prepared[K]=sh
    coeff_traces.append(dict(K=K,steps=steps,actual_literal42=True))

def inverse(C,T,P,q):
    if q<P:return T+(q-C)
    if q==P:return P+1
    if q==P+1:return P
    return q+1

def charged(P,rows):
    return 6+sum(19+(4 if q<P else 5 if q==P else 6 if q==P+1 else 5) for _,_,q in rows)

def exact_action(rows,heap,array):
    array=array.copy()
    for dst,src,q in rows:
        ar,ai,ad=array[dst];br,bi,bd=array[src];cr,ci,cd=heap[q]
        assert not cd
        array[dst]=(ar+cr*br-ci*bi,ai+cr*bi+ci*br,ad or bd)
    return array

specs=[]
for M,K,family,C,T,P,rows,expected in lean_specs:
    independent=[[d,s,inverse(C,T,P,q)] for d,s,q in reversed(rows)]
    assert expected==independent
    specs.append(dict(M=M,K=K,family=family,C=C,T=T,P=P,rows=rows,expected=expected,origin='fresh Lean inverseRows'))
rng=random.Random(130)
for M in [31,257,1000]:
    for K in [0,4,8]:
        m=7*2**K;C=29;T=C+m+11;P=T+m+17
        for family in ['parallel','chain','ragged']:
            rows=[]
            for i in range(M):
                if family=='parallel':d,s=1,2
                elif family=='chain':d,s=i+1,i
                else:
                    s=rng.randrange(20);d=rng.randrange(19)
                    if d>=s:d+=1
                q=[C+rng.randrange(m),P,P+1,P+2][i%4]
                rows.append([d,s,q])
            expected=[[d,s,inverse(C,T,P,q)] for d,s,q in reversed(rows)]
            specs.append(dict(M=M,K=K,family=family,C=C,T=T,P=P,rows=rows,expected=expected,origin='independent integer oracle'))
traces=[];all_pcs=set();gaussian=0
for index,spec in enumerate(specs):
    M,K,C,T,P,rows,expected=(spec[k] for k in ['M','K','C','T','P','rows','expected'])
    for dirty in range(3):
        Fbase=[0,137,701][dirty];O=Fbase+3*M+[0,17,31][dirty]
        B=max(O+3*M,P+6,7*M+10)+3000
        nr={q:(q*37+dirty+17)%B for q in range(1040)}
        nr.update({980:M,981:Fbase,982:O,983:C,984:T,985:P})
        nh={B-1:17,B-2:29}
        for i,row in enumerate(rows):
            for j,v in enumerate(row):nh[Fbase+3*i+j]=v
        for j in range(3*M):
            if j%3!=dirty:nh[O+j]=(47+3*j)%B
        scalar=prepared[K].copy();scalar[B-1]=value(5,7,True)
        scalar_snapshot=scalar.copy()
        scalar_regs={r:value(F(r-42,7),F(r%5-2,3),bool((r+dirty)%2)) for r in range(90)}
        outputs={2:value(5,9,True)};roots=[190,190,7]
        out,heap,t,pcs,halt,writes,reads=execute(nr,nh,B)
        actual=[[heap[O+3*i+j] for j in range(3)] for i in range(M)]
        assert actual==expected and t==charged(P,rows) and t<=25*M+6 and halt==35
        assert writes==[(O+3*i+j,v) for i,row in enumerate(expected) for j,v in enumerate(row)]
        assert reads==[Fbase+3*i+j for i in reversed(range(M)) for j in range(3)]
        assert all(out[q]==v for q,v in nr.items() if q<990 or q>=1001)
        writable=lambda a:O<=a<O+3*M
        assert all(heap[a]==v for a,v in nh.items() if not writable(a))
        assert all(a in nh or writable(a) for a in heap)
        assert scalar==scalar_snapshot
        assert all(op[0] in range(7) for op in code) # no scalar/input/output/root instruction
        for (d,s,q),(dd,ss,qq) in zip(reversed(rows),actual):
            assert d==dd and s==ss and scalar[qq]==coeff_namespace['neg'](scalar[q])
            assert not scalar[qq][2]
        # The algebraic reverse action is checked on arbitrary dirty Gaussian arrays.
        if M<=31:
            refs={j for d,s,q in rows for j in [d,s]}
            array={j:value(F((j+dirty)%11-5,3),F((j*2+dirty)%7-3,5),True) for j in refs}
            assert exact_action(actual,scalar,exact_action(rows,scalar,array))==array
            gaussian+=1
        all_pcs.update(pcs)
        traces.append(dict(index=index,dirty=dirty,M=M,K=K,steps=t,origin=spec['origin'],exact_reverse=True,actual42_prepared_negatives=True,frames=True))
assert all_pcs==set(range(36)),set(range(36))-all_pcs
negative=[]
M=2;C=29;T=47;P=71;Fbase=100;O=106;B=4000
nr={980:M,981:Fbase,982:O,983:C,984:T,985:P}
nh={Fbase:1,Fbase+1:2,Fbase+2:C,Fbase+3:2,Fbase+4:3,Fbase+5:P+1}
for name,regs,heap,word,start in [
 ('missing reversed destination',nr,{a:v for a,v in nh.items() if a!=Fbase+3},B,0),
 ('missing reversed source',nr,{a:v for a,v in nh.items() if a!=Fbase+4},B,0),
 ('missing reversed coefficient',nr,{a:v for a,v in nh.items() if a!=Fbase+5},B,0),
 ('missing later destination',nr,{a:v for a,v in nh.items() if a!=Fbase},B,0),
 ('oversized physical coefficient',nr,{**nh,Fbase+5:B+1},B,0),
 ('entry word guard',nr,nh,105,0),
 ('runtime output word guard',{**nr,982:B-2},nh,B,0),
 ('runtime coefficient-address guard',{**nr,985:B},{**nh,Fbase+5:B},B,0),
 ('missing instruction',nr,nh,B,36)]:
    try:execute(regs,heap,word,start)
    except Failure as e:negative.append(dict(name=name,observed=str(e)))
    else:raise AssertionError(name)
# Out-of-domain coefficients are deliberately not silently presented as a valid inverse.
_,corrupt,*_=execute(nr,{**nh,Fbase+5:P+4},B)
assert corrupt[O+2]==P+5
report=dict(status='PASS',cases=len(traces),steps=sum(t['steps'] for t in traces),all_pcs=sorted(all_pcs),gaussian_dirty_restoration_cases=gaussian,actual42_generation=coeff_traces,negative=negative,diagnostics=['out-of-domain address follows literal policy but has no negative-coefficient guarantee'],program_sha256=hashlib.sha256((root/'program.json').read_bytes()).hexdigest(),specs_sha256=hashlib.sha256((root/'specs.json').read_bytes()).hexdigest(),traces=traces)
(root/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='traces'},indent=2))
