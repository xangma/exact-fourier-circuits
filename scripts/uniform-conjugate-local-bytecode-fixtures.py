"""Exact independent execution of the Lean-exported local coefficient producer.
Global caller banks are supplied; local Newton rows/coefficients are not supplied.
"""
from __future__ import annotations
import hashlib, json
from fractions import Fraction as F
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]/"logs/uniform-bytecode/conjugate-local"
PB=(BASE/'program.json').read_bytes()
PROGRAM=json.loads(PB)
assert len(PROGRAM)==301 and all(row[0] != 99 for row in PROGRAM)
ZERO=(F(0),F(0)); ONE=(F(1),F(0))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def inv(a):
    d=a[0]*a[0]+a[1]*a[1]
    assert d
    return (a[0]/d,-a[1]/d)
def powi(a,j):
    out=ONE
    for _ in range(j): out=mul(out,a)
    return out

def run_case(name,n,radices,j,root,missing=None,dependent_root=False,zero_root=False,dirty=0):
    ell=len(radices)-1; length=1
    for q in radices: length*=q
    r=radices[j]
    amount=6*ell+5+2*length; copy=amount+24*length+9
    end=ell+8+2*n+3*length
    result=end+8*r+5; scratch=result+8*r+3; source=scratch+6
    nat={100: (3 if n==1 else 5),101:n,102:ell,103:length,104:(128 if n==1 else 30720),105:copy,106:amount,110:j,
         24:71,27:37,16:91,17:92,18:93,19:94}
    heapn={copy+a: 0 for a in range(amount)}
    digits=[]
    for k in range(length):
        x=k; ds=[]
        for q in radices: ds.append(x%q);x//=q
        digits.append(ds)
    idem=[]; cof=[]
    for i,q in enumerate(radices):
        c=length//q; v=pow(c,-1,q) if q>1 else 0
        idem.append((c*v)%length); cof.append(c)
        for f,value in enumerate([q,c,v,(c*v)%length]): heapn[copy+ell+4*i+f]=value
    alpha=[sum(w*d for w,d in zip(idem,ds))%length for ds in digits]
    beta=[sum(w*d for w,d in zip(cof,ds))%length for ds in digits]
    assert sorted(alpha)==sorted(beta)==list(range(length))
    for k in range(length):
        heapn[copy+5*ell+4+(ell+1)+k]=alpha[k]
        heapn[copy+5*ell+4+(ell+1)+length+k]=beta[k]
    ibase=copy+amount
    for k,value in enumerate(beta): heapn[ibase+value]=k
    # All global banks deliberately contain distinct dirty values. Only the selected
    # canonical axis root is numerically inspected by the local program.
    heaps={a:((F(17+a+dirty,3),F(11-a-dirty,7)),bool(a%2)) for a in range(end)}
    heaps[6+j]=(ZERO if zero_root else root,dependent_root)
    pool=end+17*length+16
    for a in range(pool,pool+5*sum(radices)+13): heaps[a]=((F((a+dirty)%17),F((dirty-a)%13)),bool((a+dirty)%2))
    heaps[pool+2]=(ZERO,False)
    heaps[result-1]=((F(-37),F(5)),True)
    heaps[source+r+3]=((F(97),F(2)),True)
    # Local destination starts dirty; no local rows or coefficients are ready.
    for a in range(result,result+8*r+3): heaps[a]=((F(73),F(-29)),True)
    for a in range(source+1,source+1+r): heaps[a]=((F(79),F(-31)),True)
    scal={20:((F(71),F(-11)),True)}
    if missing=='radix': del heapn[copy+ell+4*j]
    if missing=='root': del heaps[6+j]
    onat=dict(nat); onheap=dict(heapn); osheap=dict(heaps)
    outputs={0:(F(7),F(13))}; roots=[128 if n==1 else 30720]
    original_outputs=dict(outputs); original_roots=list(roots)
    bound=(n+2)**19
    pc=0;charged=0;failure=None;maxword=0;divisions=0;visited=set()
    def guard():
        nonlocal maxword
        words=[pc,*nat.values(),*heapn.keys(),*heapn.values(),*heaps.keys(),*outputs.keys(),*roots]
        maxword=max(maxword,*words)
        assert all(0<=v<=bound for v in words)
    while True:
        guard(); visited.add(pc); tag,*args=PROGRAM[pc]; charged+=1
        if tag==0:
            d,v=args;nat[d]=v;pc+=1
        elif tag==1:
            op,d,a,b=args;left=nat.get(a,0);right=nat.get(b,0)
            if op>=3 and right==0: failure={'pc':pc,'reason':'Nat division/modulo by zero'};break
            nat[d]=[lambda:left+right,lambda:max(0,left-right),lambda:left*right,
                    lambda:left//right,lambda:left%right][op]();pc+=1
        elif tag==2:
            d,a=args;pointer=nat.get(a,0)
            if pointer not in heapn: failure={'pc':pc,'address':pointer,'reason':'missing Nat load'};break
            nat[d]=heapn[pointer];pc+=1
        elif tag==3:
            a,v=args;heapn[nat.get(a,0)]=nat.get(v,0);pc+=1
        elif tag==4:
            a,b,y,no=args;pc=y if nat.get(a,0)<nat.get(b,0) else no
        elif tag==5: pc=args[0]
        elif tag==6: break
        elif tag==7:
            d,a=args;pointer=nat.get(a,0)
            if pointer not in heaps: failure={'pc':pc,'address':pointer,'reason':'missing scalar load'};break
            scal[d]=heaps[pointer];pc+=1
        elif tag==8:
            a,v=args;heaps[nat.get(a,0)]=scal.get(v,(ZERO,False));pc+=1
        elif tag==9:
            d,num,den=args;scal[d]=((F(num,den),F(0)),False);pc+=1
        elif tag==10:
            op,d,a,b=args;left,ld=scal.get(a,(ZERO,False));right,rd=scal.get(b,(ZERO,False))
            if op==2 and ld and rd: failure={'pc':pc,'reason':'data-data multiplication'};break
            if op==3 and (ld or rd or right==ZERO): failure={'pc':pc,'reason':'unprepared or zero divisor'};break
            if op==3: divisions+=1
            val=[add,sub,mul,lambda a,b:mul(a,inv(b))][op](left,right)
            scal[d]=(val,False if op==3 else ld or rd);pc+=1
        else: raise AssertionError(PROGRAM[pc])
        assert charged<100000
    guard()
    if missing or dependent_root or zero_root:
        assert failure is not None
        if missing: assert pc=={'radix':4,'root':7}[missing]
        else: assert pc==9
        return {'name':name,'charged':charged,'failure':failure}
    assert failure is None and pc==300
    expected_count=252*r+sum(13*k+10 for k in range(1,r))+10+179+32
    assert charged==expected_count
    assert all(heaps[a]==value for a,value in osheap.items() if a<end)
    assert all(heapn[a]==value for a,value in onheap.items() if a>=copy)
    assert all(nat[k]==onat[k] for k in range(100,107))
    assert outputs==original_outputs and roots==original_roots
    assert all(heaps[a]==value for a,value in osheap.items() if a>=pool)
    assert heaps[source]==(inv(root),False)
    original_root=root
    root=inv(root)
    H=[ONE];scale=[ONE]
    for k in range(1,r):
        H.append(mul(H[-1],sub(ONE,powi(root,k))))
        scale.append(mul(scale[-1],sub(ZERO,powi(root,k-1))))
    for k in range(r):
        indices=[1 if k==0 else 5*k,1 if k==0 else 5*k+2,5*r+3*k+3,5*r+3*k+4,5*r+3*k+5]
        vals=[H[k],scale[k],inv(H[k]),mul(H[k],scale[k]),inv(mul(H[k],scale[k]))]
        assert all(heaps[result+i]==(v,False) for i,v in zip(indices,vals))
    h=[inv(v) for v in H];g=[inv(h[0])]
    for k in range(1,r):
        value=ZERO
        for i in range(1,k+1): value=add(value,mul(h[i],g[k-i]))
        g.append(mul(sub(ZERO,inv(h[0])),value))
    assert all(heaps[source+1+k]==(v,False) for k,v in enumerate(g))
    def conj(z): return (z[0],-z[1])
    OH=[ONE];OS=[ONE]
    for k in range(1,r):
        OH.append(mul(OH[-1],sub(ONE,powi(original_root,k))))
        OS.append(mul(OS[-1],sub(ZERO,powi(original_root,k-1))))
    OG=[ONE]
    for k in range(1,r):
        total=ZERO
        for t in range(1,k+1): total=add(total,mul(inv(OH[t]),OG[k-t]))
        OG.append(sub(ZERO,total))
    assert all(g[k]==conj(OG[k]) for k in range(r))
    for k in range(r):
        original_values=[OH[k],OS[k],inv(OH[k]),mul(OH[k],OS[k]),inv(mul(OH[k],OS[k]))]
        indices=[1 if k==0 else 5*k,1 if k==0 else 5*k+2,5*r+3*k+3,5*r+3*k+4,5*r+3*k+5]
        assert all(heaps[result+i]==(conj(v),False) for i,v in zip(indices,original_values))
    expected_rows=[(0,1,0),(0,3,0),(0,4,0)]
    power=lambda k:1 if k==0 else 5*k-2
    hi=lambda k:1 if k==0 else 5*k
    si=lambda k:1 if k==0 else 5*k+2
    for k in range(r): expected_rows += [(2,result+power(k),result),(1,result+1,result+5*k+3),(2,result+hi(k),result+5*k+4),(2,result+si(k),result+power(k)),(2,result+2,result+5*k+6)]
    for k in range(r): expected_rows += [(3,result+1,result+hi(k)),(2,result+hi(k),result+si(k)),(3,result+1,result+5*r+3*k+4)]
    rowbytes=[v for row in expected_rows for v in row]
    assert all(heapn[k]==v for k,v in enumerate(rowbytes))
    return {'name':name,'n':n,'axis':j,'radix':r,'global_end':end,'result_base':result,
            'scratch_base':scratch,'root_source':source,'charged':charged,'max_word':maxword,
            'word_bound':bound,'actual_rows':len(expected_rows),'prepared_divisions':divisions,
            'global_operands_saved_headers_protected_tables_preserved':True,
            'actual_Newton_outputs_and_reciprocal_prefix':True,'additional_root_requests':0,'original_compact_pool_preserved':True,'newton_and_G_coefficientwise_conjugates':True,'visited':sorted(visited)}

def main():
    cases=[]
    for dirty in range(32):
        cases += [run_case(f'canonical-n1-axis0-r2-dirty-{dirty}',1,[2],0,(-F(1),F(0)),dirty=dirty),
                  run_case(f'canonical-n5-axis1-r4-dirty-{dirty}',5,[3,4],1,(F(0),F(1)),dirty=dirty)]
    # Positive-n theorem fixtures above use actual selected radices. This r1
    # test covers the executable boundary without claiming the n>0 corollary.
    cases.append(run_case('physical-r1-boundary',0,[1],0,ONE,dirty=97))
    cases += [run_case('missing-radix',1,[2],0,(-F(1),F(0)),missing='radix'),
              run_case('missing-selected-root',5,[3,4],1,(F(0),F(1)),missing='root'),
              run_case('nonprepared-selected-root',5,[3,4],1,(F(0),F(1)),dependent_root=True),
              run_case('zero-selected-root',5,[3,4],1,(F(0),F(1)),zero_root=True)]
    successes=[c for c in cases if 'failure' not in c]
    visited=sorted(set().union(*(set(c['visited']) for c in successes)))
    assert visited==list(range(301))
    result={'status':'PASS','program_sha256':hashlib.sha256(PB).hexdigest(),'program_length':301,
            'successful_cases':len(successes),'negative_cases':len(cases)-len(successes),'cases':cases,
            'visited_pcs':visited,'scope':'fresh actual Lean-exported301; exact Gaussian execution, initialized global entry tables and dirty original operands/pools supplied; no startup execution/full canonical global Operands fixture'}
    (BASE/'runtime-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS {len(successes)} exact charged301 producers, {len(cases)-len(successes)} missing/unprepared/zero controls')
if __name__=='__main__': main()
