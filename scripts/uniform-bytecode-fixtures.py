"""Exact diagnostics for exported convolution, startup and CRT-transfer programs.
All phases execute as bytecode with rational cyclotomic values and dependency tags.
Startup uses empty heaps; convolution and transfer use explicit caller operands."""
from fractions import Fraction as F
from pathlib import Path
import json,copy
P=Path(__file__).resolve().parents[1]/"logs"/"uniform-bytecode"
programs=json.loads((P/"programs.json").read_text())
code=programs["convolution"];assert len(code)==769
assert all(row[0]!='unsupported' for row in code)
class Poly:
    def __init__(self,m,items=None):
        self.m=m;self.c={k:F(v) for k,v in (items or {}).items() if v}
        assert all(0<=k<m for k in self.c)
    def __eq__(self,b):return isinstance(b,Poly) and self.m==b.m and self.c==b.c
    def __add__(self,b):
        assert self.m==b.m;c=dict(self.c)
        for k,v in b.c.items():c[k]=c.get(k,F(0))+v
        return Poly(self.m,c)
    def __neg__(self):return Poly(self.m,{k:-v for k,v in self.c.items()})
    def __sub__(self,b):return self+-b
    def __mul__(self,b):
        assert self.m==b.m;c={}
        for i,u in self.c.items():
            for j,v in b.c.items():
                k=i+j;sign=1
                if k>=self.m:k-=self.m;sign=-1
                c[k]=c.get(k,F(0))+sign*u*v
        return Poly(self.m,c)
    def __pow__(self,n):
        a=self;o=Poly(self.m,{0:1})
        while n:
            if n%2:o=o*a
            a=a*a;n//=2
        return o

def scalar(m,re=0,im=0,dep=False):return (Poly(m,{0:F(re),m//2:F(im)}),bool(dep))
def add(a,b):return (a[0]+b[0],a[1] or b[1])
def sub(a,b):return (a[0]-b[0],a[1] or b[1])
def mul(a,b):assert not(a[1] and b[1]);return (a[0]*b[0],a[1] or b[1])
def execute(code,s,B,budget,m,n=None,inputs=None,root_order=None):
    assert s['pc']<=B and max(s['nat'])<=B
    assert all(i<=B and v<=B for i,v in s['nh'].items())
    assert all(i<=B for i in s['sh']) and all(i<=B for i in s['out']) and all(o<=B for o in s['roots'])
    steps=0;pcs={}
    while True:
        pc=s['pc'];assert 0<=pc<len(code) and pc<=B
        pcs[pc]=pcs.get(pc,0)+1
        op,*args=code[pc];steps+=1;assert steps<=budget
        if op=='halt':return steps,pcs
        s['pc']+=1
        if op=='lit':dst,v=args;s['nat'][dst]=v;assert v<=B
        elif op in ('add','sub','mul','div','mod'):
            dst,l,r=args;a,b=s['nat'][l],s['nat'][r]
            if op=='add':v=a+b
            elif op=='sub':v=max(a-b,0)
            elif op=='mul':v=a*b
            elif op=='div':assert b!=0;v=a//b
            else:assert b!=0;v=a%b
            s['nat'][dst]=v;assert v<=B
        elif op=='getnat':
            dst,a=args;address=s['nat'][a];assert address in s['nh'];s['nat'][dst]=s['nh'][address]
        elif op=='putnat':a,r=args;address,value=s['nat'][a],s['nat'][r];assert address<=B and value<=B;s['nh'][address]=value
        elif op=='rat':dst,num,den=args;s['sr'][dst]=scalar(m,F(num,den))
        elif op=='getscalar':dst,a=args;address=s['nat'][a];assert address in s['sh'], ("missing scalar",pc,address);s['sr'][dst]=s['sh'][address]
        elif op=='putscalar':a,r=args;address=s['nat'][a];assert address<=B;s['sh'][address]=s['sr'][r]
        elif op in ('fadd','fsub','fmul','fdiv'):
            dst,l,r=args
            left,right=s['sr'][l],s['sr'][r]
            if op=='fmul':assert not (left[1] and right[1]), ('multiply guard',pc)
            if op=='fdiv':
                assert not left[1] and not right[1] and right[0].c, ('division guard',pc)
                assert set(right[0].c)<={0,m//2}, ('non-Gaussian divisor',pc)
                re,im=right[0].c.get(0,F(0)),right[0].c.get(m//2,F(0))
                den=re*re+im*im
                inverse=Poly(m,{0:re/den,m//2:-im/den})
                s['sr'][dst]=(left[0]*inverse,False)
            else:s['sr'][dst]={'fadd':add,'fsub':sub,'fmul':mul}[op](left,right)
        elif op=='branch':l,r,yes,no=args;s['pc']=yes if s['nat'][l]<s['nat'][r] else no
        elif op=='jump':s['pc']=args[0]
        elif op=='length':dst=args[0];assert n is not None;s['nat'][dst]=n
        elif op=='root':
            dst,r=args;assert s['nat'][r]==root_order==2*m
            s['sr'][dst]=(Poly(m,{1:1}),False);s['roots'].append(root_order)
        elif op=='input':
            dst,j=args;assert inputs is not None and s['nat'][j]<len(inputs)
            s['sr'][dst]=(inputs[s['nat'][j]],True)
        elif op=='output':j,r=args;assert s['nat'][j]<n;s['out'][s['nat'][j]]=s['sr'][r][0]
        else:raise AssertionError(op)
        assert s['pc']<=B

def direct_dft(omega,x):
    m=omega.m;out=[];powers=[omega**j for j in range(len(x))]
    for i in range(len(x)):
        acc=scalar(m)
        for j,v in enumerate(x):acc=add(acc,(powers[(i*j)%len(x)]*v[0],v[1]))
        out.append(acc)
    return out

def loop_cost(e):
    if not e:return 2
    return loop_cost(e//2)+(7 if e%2 else 6)

def cyclic(v,k):
    m=v[0][0].m;N=len(v);result=[]
    for i in range(N):
        acc=Poly(m)
        for j in range(N):acc=acc+v[j][0]*k[(i-j)%N][0]
        result.append((acc,any(x[1] for x in v)))
    return result

def initialized(f,layout,kind):
    K,N,G=f['height'],f['width'],f['count'];D=4*N;m=2*N
    A,d=layout['arena'],layout['table'];B=layout['wordBudget']
    span=G+6*N+5;norm=A+3*span;out=norm+1
    eta=Poly(m,{1:1});omega=eta**4;S=64;T=256
    s={'pc':0,'nat':[(17*i+13)%(B//8+1) for i in range(256)],
      'nh':{i:(31*i+7)%(B//4+1) for i in range(4097) if i%5!=3},
      'sh':{i:scalar(m,i-2,3-i,i%7==0) for i in range(513)}|{out+N+201:scalar(m,-7,11,True)},
      'sr':{i:scalar(m,i-3,2*i-1,i%2==1) for i in range(40)},
      'out':{0:(F(-7),F(19)),6:(F(0),F(0))},'roots':[D,3,1]}
    s['nat'][100:107]=[23,445,3,128,D,512,257]
    s['nat'][70],s['nat'][107],s['nat'][200],s['nat'][201],s['nat'][202]=K,d,S,T,A
    s['sh'][0]=(eta,False)
    data=[];kernel=[]
    for i in range(N):
        dv=scalar(m,F((7*i+3)%17-8,8),F((11*i+1)%13-6,4),kind!='prepared' and i%3!=1)
        kv=scalar(m,F((3*i+2)%11-5,4),F((5*i+4)%7-3,8))
        if kind=='data-zero':dv=scalar(m,0,0,i%3==0)
        if kind=='kernel-zero':kv=scalar(m)
        if kind=='impulse':dv=scalar(m,1 if i==0 else 0,0,i==0)
        if kind=='zero-prepared':dv=scalar(m);kv=scalar(m)
        data.append(dv);kernel.append(kv);s['sh'][S+i]=dv;s['sh'][T+i]=kv
    return s,data,kernel,(K,N,G,D,m,A,d,S,T,span,norm,out,omega)

def fixture(f,layout,kind):
    s,data,kernel,meta=initialized(f,layout,kind)
    K,N,G,D,m,A,d,S,T,span,norm,out,omega=meta
    before=copy.deepcopy(s);B=layout['wordBudget'];bound=f['runtime']
    steps,pcs=execute(code,s,B,bound,m)
    actual=[s['sh'][out+i] for i in range(N)]
    assert actual==cyclic(data,kernel),(K,kind)
    assert all(s['sh'][S+i]==data[i] and s['sh'][T+i]==kernel[i] for i in range(N))
    ks=direct_dft(omega,kernel);ds=direct_dft(omega,data)
    assert [s['sh'][A+G+i] for i in range(N)]==ks
    spectrum=[mul(a,b) for a,b in zip(ds,ks)]
    assert [s['sh'][A+span+G+i] for i in range(N)]==spectrum
    assert [s['sh'][A+2*span+i] for i in range(N)]==spectrum
    third=direct_dft(omega,spectrum)
    assert [s['sh'][A+2*span+G+i] for i in range(N)]==third
    assert s['sh'][norm]==scalar(m,F(1,N))
    for i in range(N):assert actual[i]==(third[(-i)%N][0]*scalar(m,F(1,N))[0],third[(-i)%N][1])
    for arena in [A,A+span,A+2*span]:
        root=arena+G+6*N+4;power=arena+N+G
        assert s['sh'][root]==(omega,False)
        for c in range(N):assert s['sh'][power+(1 if c==0 else 5*c-2)]==(omega**c,False)
    expected_table=[v for row in f['rows'] for v in [row[0],A+2*span+row[1],A+2*span+row[2]]]
    assert all(s['nh'][d+i]==v for i,v in enumerate(expected_table))
    assert all(s['nh'].get(i)==before['nh'].get(i) for i in set(s['nh'])|set(before['nh']) if i<d or i>=d+3*G)
    for address in set(s['sh'])|set(before['sh']):
        if address<A or address>=out+N:assert s['sh'].get(address)==before['sh'].get(address)
    assert s['out']==before['out'] and s['roots']==before['roots']
    for r in range(256):
        if r in [70,107] or 100<=r<=106 or 160<=r<174 or 184<=r<=202 or r>=224:
            assert s['nat'][r]==before['nat'][r],(K,r,s['nat'][r],before['nat'][r])
    assert s['nat'][203:213]==[N,G,span,A+span,A+2*span,norm,out,A+G,A+span+G,A+2*span+G]
    assert s['pc']==768 and steps<=bound
    assert all(pcs.get(pc,0)>=1 for pc in [0,9,13,14,26,30,251,255,476,479,491,495,716,718,754,768])
    assert pcs.get(486,0)==N and pcs.get(762,0)==N
    if kind in ['data-zero','kernel-zero']:assert all(not x[0].c and x[1] for x in actual)
    if kind in ['prepared','zero-prepared']:assert all(not x[1] for x in actual)
    return {'K':K,'N':N,'gate_count_per_fft':G,'kind':kind,'arena':A,'table':d,'steps':steps,
      'charged_bound':bound,'same_word_B':B,'norm_steps':f['normRuntime'],'output_base':out}

def negative(f,layout,kind):
    s,data,kernel,meta=initialized(f,layout,'mixed')
    K,N,G,D,m,A,d,S,T,span,norm,out,omega=meta
    if kind=='missing-kernel':del s['sh'][T+1]
    elif kind=='missing-data':del s['sh'][S+1]
    elif kind=='unprepared-kernel':s['sh'][T]=(s['sh'][T][0],True)
    else:raise AssertionError(kind)
    try:execute(code,s,layout['wordBudget'],f['runtime'],m)
    except AssertionError as err:
        if kind=='missing-kernel':assert err.args==(('missing scalar',43,T+1),),err.args
        if kind=='missing-data':assert err.args==(('missing scalar',268,S+1),),err.args
        if kind=='unprepared-kernel':assert err.args==(('multiply guard',486),),err.args
        return {'case':kind,'rejected':err.args}
    raise AssertionError('invalid entry accepted')

cases=[];expected=json.loads((P/'expected.json').read_text())
for f in expected:
    for layout in f['layouts']:
        for kind in ['mixed','prepared','data-zero','kernel-zero','impulse','zero-prepared']:cases.append(fixture(f,layout,kind))
negative_cases=[negative(expected[2],expected[2]['layouts'][0],kind) for kind in ['missing-kernel','missing-data','unprepared-kernel']]
summary={'status':'PASS','bytecode_length':len(code),'single_program_executions':len(cases),
  'executed_typed_fft_rows':sum(3*c['gate_count_per_fft'] for c in cases),'negative_cases':negative_cases,
  'exact_oracle':'Direct cyclic sum over Q[eta]/(eta^(D/2)+1), D=4N; exact Fraction coefficients, no floating arithmetic. Phase spectra checked against independent direct DFT.',
  'scope':'Universal symbolic Lean theorem is primary; actual exported bytecode cases K0..6/two layouts/six tagged input families are bounded diagnostics.',
  'initialization':'Only initial original data/kernel/master cells and caller arguments; no interphase host writes, precomputed spectrum, table, powers or root.',
  'frames':'Original source banks, outside scalar allocation, Natheap outside row table, saved/global metadata registers, outputs/rootOrders retained. Nat174..176 are explicit phase workspace.',
  'tags':'Mixed/prepared/nonreal/zero values tested; numerical zero never substitutes for prepared-false flag.',
  'cases':cases}
# Exact complete empty-state runs. Fresh scalar and Nat banks are produced by
# exported Lean code; no phase writes or prepared table inputs are inserted.
def empty_state(m):
    return {'pc':0,'nat':[0]*256,'nh':{},'sh':{},'sr':{i:scalar(m) for i in range(40)},'out':{},'roots':[]}
startup_cases=[]
for re,im in [(0,0),(3,2),(-7,0)]:
    value=scalar(64,re,im)[0];base=empty_state(64);actual=empty_state(64)
    p,_=execute(programs['seedStartup'],base,3**19,10000,64,n=1,inputs=[value],root_order=128)
    t,_=execute(programs['traversalStartup'],actual,3**19,10000,64,n=1,inputs=[value],root_order=128)
    assert p==1652 and t==1736 and actual['pc']==988
    assert actual['sh']==base['sh'] and actual['sr']==base['sr']
    assert actual['roots']==[128] and actual['out']=={}
    assert actual['nat'][100:107]==[3,1,0,2,128,66,9]
    assert all(actual['nh'][i]==base['nh'][i] for i in range(66,79))
    assert [actual['nh'][3+j] for j in range(2)]==[0,1] and actual['nat'][8]==2
    assert actual['sh'][14]==(value,True) and actual['sh'][15]==scalar(64)
    startup_cases.append({'input':[re,im],'steps':t,'preinitialized_heaps':False,'host_phase_writes':False})
# Genuine selected metadata/permutation fixtures, including equal CRT maps.
# Native scalar
# banks are caller fixtures, not claimed products of an executed transform.
transfer_cases=[]
for n,rs,next_prime in [(5,[3,4],5),(8,[3,5,2],7),(31,[3,5,8],7)]:
    ell=len(rs)-1;L=1
    for r in rs:L*=r
    amount=6*ell+5+2*L;M=amount+24*L+9;I=M+amount
    alphabase=M+6*ell+5;betabase=alphabase+L
    factors=[L//r for r in rs];idempotents=[c*pow(c,-1,r)%L for c,r in zip(factors,rs)]
    alpha=[];beta=[]
    for j in range(L):
        q=j;digits=[]
        for r in rs:digits.append(q%r);q//=r
        alpha.append(sum(d*e for d,e in zip(digits,idempotents))%L)
        beta.append(sum(d*c for d,c in zip(digits,factors))%L)
    assert sorted(alpha)==sorted(beta)==list(range(L))
    assert (alpha!=beta)==(n!=8)
    D=(2*n)*L*2**((16*L-1).bit_length())
    for variant in range(3):
        state=empty_state(64);state['nat'][100:107]=[next_prime,n,ell,L,D,M,amount]
        state['nh']={M+j:0 for j in range(amount)}
        for j,r in enumerate(rs[:-1]):state['nh'][M+j]=r
        for j,r in enumerate(rs):
            for f,v in enumerate([r,factors[j],pow(factors[j],-1,r),idempotents[j]]):state['nh'][M+ell+4*j+f]=v
        for j,(a,b) in enumerate(zip(alpha,beta)):
            state['nh'][alphabase+j]=a;state['nh'][betabase+j]=b;state['nh'][I+b]=j
        S=4096;T=S+L;A=T+L;state['nat'][201:204]=[S,T,A]
        values=[scalar(64,j+variant,j-variant,bool((j+variant)%2)) for j in range(L)]
        state['sh']={S+j:values[beta[j]] for j in range(L)}|{T+j:scalar(64,-11,7,True) for j in range(L)}|{A+j:scalar(64,9,-3) for j in range(L)}
        state['roots']=[D];before=copy.deepcopy(state)
        steps,pcs=execute(programs['transfer'],state,(n+2)**19,10000,64)
        assert steps==18*L+25 and set(pcs)==set(range(41))
        assert [state['sh'][T+j] for j in range(L)]==values
        assert [state['sh'][A+j] for j in range(L)]==[values[alpha[j]] for j in range(L)]
        assert state['nh']==before['nh'] and state['roots']==before['roots'] and state['out']==before['out']
        assert state['nat'][100:107]==before['nat'][100:107]
        assert all(state['sh'][S+j]==before['sh'][S+j] for j in range(L))
        transfer_cases.append({'n':n,'L':L,'variant':variant,'steps':steps,'alpha_differs_beta':alpha!=beta,'native_bank':'explicit caller fixture'})
summary['empty_startup_cases']=startup_cases;summary['transfer_cases']=transfer_cases
summary['startup_scope']='Three n=1 exact empty-heap startup/traversal runs; comparison uses the separately executed seed-startup program.'
summary['transfer_scope']='Nine selected-metadata caller cases; native scalar banks are explicit fixtures. Six cases use different alpha/beta maps and three use coincident maps.'
(P/'fixtures.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'status':'PASS','convolution_cases':len(cases),'guard_failure_controls':len(negative_cases),'exact_empty_startup_cases':len(startup_cases),'CRT_transfer_cases':len(transfer_cases),'different_CRT_map_cases':sum(c['alpha_differs_beta'] for c in transfer_cases),'receipt':str(P/'fixtures.json')},indent=2))
