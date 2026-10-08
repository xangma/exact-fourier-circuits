from fractions import Fraction
from dataclasses import dataclass
from pathlib import Path
import json, copy, random
B=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode'
@dataclass(frozen=True)
class Gaussian:
    real: Fraction=Fraction(0)
    imag: Fraction=Fraction(0)
    def __add__(self,x): return Gaussian(self.real+x.real,self.imag+x.imag)
    def __sub__(self,x): return Gaussian(self.real-x.real,self.imag-x.imag)
    def __mul__(self,x): return Gaussian(self.real*x.real-self.imag*x.imag,self.real*x.imag+self.imag*x.real)
    def __neg__(self): return Gaussian(-self.real,-self.imag)
    def __str__(self): return f'{self.real}+({self.imag})i'
Z=Gaussian();O=Gaussian(Fraction(1));I=Gaussian(Fraction(0),Fraction(1))
def prepared(v):return (v,False)
P=json.loads((B/'rank-kernel-export.log').read_text());assert len(P)==90
(B/'rank-kernel-programs.json').write_text(json.dumps({'rankKernel':P})+'\n')
class Failed(Exception):pass
class Machine:
    def __init__(self,program,nats,scalars,nh,sh,out,roots,word=20000):
        self.p=program;self.pc=0;self.r=copy.deepcopy(nats);self.c=copy.deepcopy(scalars)
        self.nh=copy.deepcopy(nh);self.sh=copy.deepcopy(sh);self.out=copy.deepcopy(out);self.roots=list(roots)
        self.word=word;self.steps=0;self.visited=[]
    def R(self,i):return self.r.get(i,19)
    def C(self,i):return self.c.get(i,(Gaussian(Fraction(17),Fraction(-3)),True))
    def bound(self):
        assert 0<=self.pc<=self.word
        assert all(0<=v<=self.word for v in self.r.values())
        assert all(0<=a<=self.word and 0<=v<=self.word for a,v in self.nh.items())
        assert all(0<=a<=self.word for a in self.sh)
        assert all(0<=a<=self.word for a in self.out)
        assert all(0<=v<=self.word for v in self.roots)
    def run(self):
        self.bound()
        while self.steps<1000000:
            self.visited.append(self.pc);op,*args=self.p[self.pc];self.steps+=1;self.pc+=1
            if op==0:d,v=args;self.r[d]=v
            elif op==1:
                kind,d,l,r=args;a,b=self.R(l),self.R(r)
                if kind==0:v=a+b
                elif kind==1:v=max(a-b,0)
                elif kind==2:v=a*b
                elif kind==3:
                    if not b:raise Failed('zero Nat division')
                    v=a//b
                elif kind==4:
                    if not b:raise Failed('zero Nat remainder')
                    v=a%b
                self.r[d]=v
            elif op==4:a,b,y,no=args;self.pc=y if self.R(a)<self.R(b) else no
            elif op==5:self.pc=args[0]
            elif op==6:self.pc-=1;self.bound();return self
            elif op==7:
                d,a=args;address=self.R(a)
                if address not in self.sh:raise Failed('uninitialized scalar load')
                self.c[d]=self.sh[address]
            elif op==8:a,c=args;self.sh[self.R(a)]=self.C(c)
            elif op==9:d,num,den=args;self.c[d]=prepared(Gaussian(Fraction(num,den)))
            elif op==10:
                kind,d,l,r=args;(a,da),(b,db)=self.C(l),self.C(r)
                if kind==0:v=a+b
                elif kind==1:v=a-b
                elif kind==2:
                    if da and db:raise Failed('data-data multiplication')
                    v=a*b
                else:raise AssertionError('unexpected field division')
                self.c[d]=(v,da or db)
            else:raise AssertionError(f'unexpected opcode {op}')
            self.bound()
        raise Failed('timeout')

def expected(p,h,g):
    a,e,i0,j0,s,N=p['a'],p['e'],p['i0'],p['j0'],p['split'],p['N']
    def v(i):return -h[i0+i-s]
    def w(j):return g[s-j0-j]
    def cross(i,j):return sum((h[i0+i-j0-j-u]*g[u] for u in range(s-j0-j)),Z)
    return [[w(j) if j<e else Z for j in range(N)],
        [v(i) if i<a else Z for i in range(N)],
        [cross(0,j)-v(0)*w(j) if j<e else Z for j in range(N)],
        [O if j==0 else Z for j in range(N)],
        [O if j==0 else Z for j in range(N)],
        [cross(i,0)-v(i)*w(0) if 0<i<a else Z for i in range(N)]]

def state(K,a,e,s,i0,j0,mode):
    N=2**K;assert 0<a<=N and 0<e<=N and j0+e<=s<=i0
    p=dict(H=31,G=113,hSize=i0+a+1,gSize=s+2,a=a,e=e,i0=i0,j0=j0,split=s,N=N,S=300)
    rng=random.Random(921+K+100*a+1000*e+s)
    def value(j):
        if mode=='zero':return Z
        if mode=='sparse':return Z if j%2==0 else Gaussian(Fraction(-2*j,3),Fraction(j+1,5))
        return Gaussian(Fraction(rng.randrange(-7,8),rng.randrange(1,5)),Fraction(rng.randrange(-5,6),rng.randrange(1,5)))
    h=[value(j) for j in range(p['hSize'])];g=[value(j) for j in range(p['gSize'])]
    regs={480+i:p[k] for i,k in enumerate(['H','hSize','G','gSize','a','e','i0','j0','split','N','S'])}
    regs.update({100+j:700+j for j in range(7)});regs.update({10:58,525:77,549:81})
    scalars={0:(Gaussian(Fraction(5),Fraction(-7)),True),49:(I,True),60:(O,True)}
    nh={0:22,1000:333,19000:17};out={17:Gaussian(Fraction(9),Fraction(4))};roots=[4]
    sh={0:prepared(I),29:(Gaussian(Fraction(3)),True),299:(I,True),15000:(O,True)}
    for j,z in enumerate(h):sh[p['H']+j]=prepared(z)
    for j,z in enumerate(g):sh[p['G']+j]=prepared(z)
    for j in range(6*N):sh[p['S']+j]=(Gaussian(Fraction(j+77),Fraction(-j)),True)
    return p,h,g,regs,scalars,nh,sh,out,roots

def verify(K,a,e,s,i0,j0,mode):
    p,h,g,r,c,nh,sh,out,roots=state(K,a,e,s,i0,j0,mode)
    m=Machine(P,r,c,nh,sh,out,roots).run();spec=expected(p,h,g)
    for b in range(6):
        for j in range(p['N']):assert m.sh[p['S']+b*p['N']+j]==prepared(spec[b][j]),(b,j,p)
    exact=28+30*p['N']+sum(19+11*(s-j0-j) for j in range(e))+11+(a-1)*(21+11*(s-j0))
    assert m.steps==exact,(m.steps,exact)
    assert m.steps<=28+30*p['N']+e*(19+11*s)+a*(21+11*s)
    assert m.nh==nh and m.out==out and m.roots==roots
    for addr,val in sh.items():
        if not(p['S']<=addr<p['S']+6*p['N']):assert m.sh[addr]==val
    for reg in set(r)|set(m.r):
        if reg<491 or reg>524:assert m.R(reg)==r.get(reg,19)
    for reg in set(c)|set(m.c):
        if reg<50 or reg>59:assert m.C(reg)==c.get(reg,(Gaussian(Fraction(17),Fraction(-3)),True))
    assert m.pc==89
    return m,{'K':K,'N':p['N'],'a':a,'e':e,'split':s,'i0':i0,'j0':j0,'mode':mode,
        'instructions':m.steps,'exact_count':True,'same_word_bound':True,'all_prepared':True,'sources_external_and_master_preserved':True,
        'kernel_values':[[str(z) for z in row] for row in spec]}

cases=[];visited=set()
for K,a,e,s,i0,j0 in [(0,1,1,1,1,0),(1,1,1,2,3,1),(1,2,1,2,2,0),
    (2,2,3,4,5,1),(2,4,4,5,6,1),(3,5,2,4,5,2),(3,2,7,7,9,0),(4,11,9,11,13,2)]:
    for mode in ['mixed','zero','sparse']:
        m,result=verify(K,a,e,s,i0,j0,mode);cases.append(result);visited.update(m.visited)
assert visited==set(range(90)),sorted(set(range(90))-visited)
negative=[]
p,h,g,r,c,nh,sh,out,roots=state(2,2,3,4,5,1,'mixed')
for label,addr in [('missing H cache',p['H']+p['i0']-p['split']),('missing G cache',p['G']+p['split']-p['j0'])]:
    bad=copy.deepcopy(sh);del bad[addr]
    try:Machine(P,r,c,nh,bad,out,roots).run();raise AssertionError('accepted missing read')
    except Failed as err:negative.append({'control':label,'rejected':True,'reason':str(err)})
bad=copy.deepcopy(sh)
for addr in list(bad):
    if p['H']<=addr<p['H']+p['hSize'] or p['G']<=addr<p['G']+p['gSize']:bad[addr]=(bad[addr][0],True)
try:Machine(P,r,c,nh,bad,out,roots).run();raise AssertionError('accepted data-data product')
except Failed as err:negative.append({'control':'input-dependent H/G tags','rejected':True,'reason':str(err)})
badP=copy.deepcopy(P);assert badP[50]==[8,501,59];badP[50]=[8,501,54]
bad=Machine(badP,r,c,nh,sh,out,roots).run();spec=expected(p,h,g)
assert any(bad.sh[p['S']+b*p['N']+j]!=prepared(spec[b][j]) for b in range(6) for j in range(p['N']))
negative.append({'control':'mutated w store uses row scalar','rejected':True,'reason':'independent six-slot exact bank mismatch'})
res={'status':'PASS','arithmetic':'exact Gaussian rationals (two Fractions); no floating point',
    'program_length':len(P),'actual_prepared_source_cases':cases,'visited_pcs':sorted(visited),
    'all90_pcs_covered':True,'negative_controls':negative,
    'boundary':'These are actual fixed90 executions from physical prepared H/G caller states with dirty output/external banks. They are not empty global startup, reciprocal-bank production, or full DFT executions.'}
(B/'rank-kernel-fixtures.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'status':res['status'],'cases':len(cases),'all90_pcs_covered':True,'negative_controls':negative},indent=2))
