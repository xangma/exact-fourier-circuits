from fractions import Fraction as F
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
