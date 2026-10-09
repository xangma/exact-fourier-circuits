"""Exact Q[eta]/Phi_D with polynomial Euclidean inverses; no floats.
The VM below is the frozen seed VM instruction interpreter copied unchanged.
"""
from fractions import Fraction as F
from functools import lru_cache

def trim(a):
    while a and not a[-1]: a.pop()
    return a

def divmod_poly(a,b):
    a=trim(list(a));b=trim(list(b));assert b
    q=[F(0)]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b):
        j=len(a)-len(b);v=a[-1]/b[-1];q[j]=v
        for k,w in enumerate(b):a[k+j]-=v*w
        trim(a)
    return trim(q),a

def add_poly(a,b,sign=1):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a):c[i]+=v
    for i,v in enumerate(b):c[i]+=sign*v
    return trim(c)

def mul_poly(a,b):
    c=[F(0)]*max(0,len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):c[i+j]+=v*w
    return trim(c)

@lru_cache(None)
def cyclotomic(D):
    assert D>=1
    a=[F(-1)]+[F(0)]*(D-1)+[F(1)]
    for d in range(1,D):
        if D%d==0:
            a,r=divmod_poly(a,cyclotomic(d));assert not r
    assert a[-1]==1 and all(x.denominator==1 for x in a)
    return tuple(a)

class Poly:
    def __init__(self,D,items=None):
        assert D>=4
        self.D=D;f=cyclotomic(D);self.m=len(f)-1
        c={}
        for k,v in (items or {}).items():
            assert k>=0
            j=k%D;c[j]=c.get(j,F(0))+F(v)
        c={k:v for k,v in c.items() if v}
        terms=[(j,v) for j,v in enumerate(f[:-1]) if v]
        while c and max(c)>=self.m:
            k=max(c);v=c.pop(k)
            for j,w in terms:
                z=k-self.m+j;c[z]=c.get(z,F(0))-v*w
                if not c[z]:del c[z]
        assert all(0<=k<self.m for k in c)
        self.c=c
    def __repr__(self):return repr(self.c)
    def __deepcopy__(self,memo):return self
    def __eq__(self,b):return isinstance(b,Poly) and self.D==b.D and self.c==b.c
    def __add__(self,b):
        assert self.D==b.D;c=dict(self.c)
        for k,v in b.c.items():c[k]=c.get(k,F(0))+v
        return Poly(self.D,c)
    def __neg__(self):return Poly(self.D,{k:-v for k,v in self.c.items()})
    def __sub__(self,b):return self+-b
    def __mul__(self,b):
        assert self.D==b.D;c={}
        for i,u in self.c.items():
            for j,v in b.c.items():c[i+j]=c.get(i+j,F(0))+u*v
        return Poly(self.D,c)
    def __pow__(self,n):
        assert n>=0
        a=self;o=Poly(self.D,{0:1})
        while n:
            if n%2:o=o*a
            a=a*a;n//=2
        return o
    def conjugate(self):return Poly(self.D,{(-j)%self.D:v for j,v in self.c.items()})
    def inverse(self):
        assert self.c,'zero scalar divisor'
        a=list(cyclotomic(self.D));b=[self.c.get(i,F(0)) for i in range(max(self.c)+1)]
        u,v=[],[F(1)]
        while b:
            q,r=divmod_poly(a,b);a,b=b,r;u,v=v,add_poly(u,mul_poly(q,v),-1)
        assert len(a)==1
        ans=Poly(self.D,{j:w/a[0] for j,w in enumerate(u) if w})
        assert self*ans==Poly(self.D,{0:1})
        return ans

def scalar(D,re=0,im=0,dep=False):
    assert D%4==0, "complex embedding requires fourth root of unity"
    return (Poly(D,{0:F(re),D//4:F(im)}),bool(dep))
def add(a,b):return (a[0]+b[0],a[1] or b[1])
def sub(a,b):return (a[0]-b[0],a[1] or b[1])
def mul(a,b):assert not(a[1] and b[1]);return (a[0]*b[0],a[1] or b[1])
def execute(code,s,B,budget,D,n=None,inputs=None):
    assert s['pc']<=B and max(s['nat'])<=B
    assert all(0<=i<=B and 0<=v<=B for i,v in s['nh'].items())
    assert all(0<=i<=B for i in s['sh']) and all(0<=i<=B for i in s['out']) and all(0<o<=B for o in s['roots'])
    zero=scalar(D);steps=0;pcs={};peak=max(s['pc'],max(s['nat']),max(s['nh'],default=0),max(s['nh'].values(),default=0),max(s['sh'],default=0))
    while True:
        pc=s['pc'];assert 0<=pc<len(code) and pc<=B,('pc guard',pc)
        pcs[pc]=pcs.get(pc,0)+1
        op,*args=code[pc];steps+=1;assert steps<=budget,('budget',pc,steps)
        if op=='halt':return steps,pcs,peak
        s['pc']+=1
        if op=='lit':dst,v=args;s['nat'][dst]=v;assert v<=B;peak=max(peak,v)
        elif op in ('add','sub','mul','div','mod'):
            dst,l,r=args;a,b=s['nat'][l],s['nat'][r]
            if op=='add':v=a+b
            elif op=='sub':v=max(a-b,0)
            elif op=='mul':v=a*b
            elif op=='div':assert b!=0;v=a//b
            else:assert b!=0;v=a%b
            s['nat'][dst]=v;assert v<=B,('word guard',pc,v,B);peak=max(peak,v)
        elif op=='getnat':
            dst,a=args;address=s['nat'][a];assert address in s['nh'],('missing Nat',pc,address);s['nat'][dst]=s['nh'][address]
        elif op=='putnat':
            a,r=args;address,value=s['nat'][a],s['nat'][r];assert address<=B and value<=B;s['nh'][address]=value;peak=max(peak,address,value)
        elif op=='rat':dst,num,den=args;s['sr'][dst]=scalar(D,F(num,den))
        elif op=='getscalar':
            dst,a=args;address=s['nat'][a];assert address in s['sh'],('missing scalar',pc,address);s['sr'][dst]=s['sh'][address]
        elif op=='putscalar':a,r=args;address=s['nat'][a];assert address<=B;s['sh'][address]=s['sr'].get(r,zero);peak=max(peak,address)
        elif op in ('fadd','fsub','fmul','fdiv'):
            dst,l,r=args;left,right=s['sr'].get(l,zero),s['sr'].get(r,zero)
            if op=='fmul':assert not(left[1] and right[1]),('multiply guard',pc)
            if op=='fdiv':
                assert not left[1] and not right[1] and right[0].c,('division guard',pc)
                s['sr'][dst]=(left[0]*right[0].inverse(),False)
            else:s['sr'][dst]={'fadd':add,'fsub':sub,'fmul':mul}[op](left,right)
        elif op=='branch':l,r,yes,no=args;s['pc']=yes if s['nat'][l]<s['nat'][r] else no
        elif op=='jump':s['pc']=args[0]
        elif op=='length':dst=args[0];assert n is not None;s['nat'][dst]=n
        elif op=='root':
            dst,r=args;assert 0<s['nat'][r]<=B and D%s['nat'][r]==0
            s['sr'][dst]=(Poly(D,{1:1})**(D//s['nat'][r]),False);s['roots'].append(s['nat'][r])
        elif op=='input':
            dst,j=args;assert inputs is not None and s['nat'][j]<len(inputs)
            s['sr'][dst]=(inputs[s['nat'][j]],True)
        elif op=='output':j,r=args;assert s['nat'][j]<n;s['out'][s['nat'][j]]=s['sr'].get(r,zero)[0]
        else:raise AssertionError(op)
        assert s['pc']<=B

def direct_dft(omega,x):
    D=omega.D;out=[];powers=[omega**j for j in range(len(x))]
    for i in range(len(x)):
        acc=scalar(D)
        for j,v in enumerate(x):acc=add(acc,(powers[(i*j)%len(x)]*v[0],v[1]))
        out.append(acc)
    return out
