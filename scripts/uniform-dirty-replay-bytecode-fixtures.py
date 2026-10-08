import json, random, hashlib
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parents[1]/"logs/uniform-bytecode/dirty-replay"
code=json.loads((root/'program.json').read_text())
assert len(code)==81
assert {r[0] for r in code}<={0,1,2,3,4,5,6,7,8,9,10}
@dataclass(frozen=True)
class Q8:
    # Exact Q[zeta_8], zeta_8^4=-1. Gaussian a+bi is (a,0,b,0).
    a:tuple
    @staticmethod
    def rational(x=0): return Q8((F(x),F(0),F(0),F(0)))
    def __add__(self,y):return Q8(tuple(x+v for x,v in zip(self.a,y.a)))
    def __neg__(self):return Q8(tuple(-x for x in self.a))
    def __sub__(self,y):return self+-y
    def __mul__(self,y):
        v=[F(0)]*4
        for i,x in enumerate(self.a):
            for j,z in enumerate(y.a):v[(i+j)%4]+=x*z*(1 if i+j<4 else -1)
        return Q8(tuple(v))
def val(x=0,tag=False):return (x if isinstance(x,Q8) else Q8.rational(x),tag)
def gauss(re=0,im=0,tag=False):return val(Q8((F(re),F(0),F(im),F(0))),tag)
class Failure(Exception):pass
def run(nr,nh,sr,sh,B,start=0,outputs=None,orders=None):
    nr,nh,sr,sh=nr.copy(),nh.copy(),sr.copy(),sh.copy()
    outputs=dict(outputs or {});orders=list(orders or [])
    pc=start;steps=0;pcs=set();writes=[]
    def bound(v):
        if not 0<=v<=B:raise Failure('word bound')
    bound(pc)
    for v in nr.values():bound(v)
    for q,v in nh.items():bound(q);bound(v)
    for q in sh:bound(q)
    while steps<1000000:
        if not 0<=pc<len(code):raise Failure('missing instruction')
        pcs.add(pc);op,*args=code[pc];steps+=1;nextpc=pc+1
        if op==6:return nr,nh,sr,sh,steps,pcs,pc,writes,outputs,orders
        if op==0:
            q,v=args;bound(v);nr[q]=v
        elif op==1:
            kind,q,l,r=args;x,y=nr.get(l,0),nr.get(r,0)
            if kind==0:v=x+y
            elif kind==1:v=max(0,x-y)
            elif kind==2:v=x*y
            elif kind in (3,4):
                if not y:raise Failure('zero Nat divisor')
                v=x//y if kind==3 else x%y
            else:raise AssertionError(kind)
            bound(v);nr[q]=v
        elif op==2:
            q,a=args;a=nr.get(a,0);bound(a)
            if a not in nh:raise Failure('missing Nat source')
            nr[q]=nh[a]
        elif op==3:
            a,q=args;a=nr.get(a,0);v=nr.get(q,0);bound(a);bound(v);nh[a]=v
        elif op==4:
            l,r,yes,no=args;nextpc=yes if nr.get(l,0)<nr.get(r,0) else no
        elif op==5:nextpc=args[0]
        elif op==7:
            q,a=args;a=nr.get(a,0);bound(a)
            if a not in sh:raise Failure('missing Scalar source')
            sr[q]=sh[a]
        elif op==8:
            a,q=args;a=nr.get(a,0);bound(a);sh[a]=sr.get(q,val());writes.append(a)
        elif op==9:
            q,num,den=args;sr[q]=val(F(num,den))
        elif op==10:
            kind,q,l,r=args;x,dx=sr.get(l,val());y,dy=sr.get(r,val())
            if kind==0:z=x+y
            elif kind==1:z=x-y
            elif kind==2:
                if dx and dy:raise Failure('data-data product')
                z=x*y
            else:raise AssertionError('unexpected field opcode')
            sr[q]=(z,dx or dy)
        else:raise AssertionError(op)
        bound(nextpc);pc=nextpc
    raise Failure('step cap')
def model(rows,data,coef):
    data=data.copy()
    for d,s,q in rows:
        x,dx=data[d];y,dy=data[s];c,dc=coef[q];assert not dc
        data[d]=(x+c*y,dx or dy)
    return data
def dec(z):return gauss(F(z[0],z[1]),F(z[2],z[3]),z[4])
def inverse_addr(C,T,P,q):return T+q-C if q<P else P+1 if q==P else P if q==P+1 else P+3
specs=json.loads((root/'specs.json').read_text());assert len(specs)==396
seen=set();traces=[];tag_changed=False;master_changed=False
for specno,(K,M,family,raw,init,coef,expected,leanInverse) in enumerate(specs):
    data={j:dec(v) for j,v in enumerate(init)};coefs={j:dec(v) for j,v in enumerate(coef)}
    final={j:dec(v) for j,v in enumerate(expected)}
    invcoef={j:(-z,t) for j,(z,t) in coefs.items()}
    assert model(raw[::-1],model(raw,data,coefs),invcoef)==final
    toy=[[d,s,inverse_addr(100,200,300,100+q if q<7 else 300+q-7)] for d,s,q in raw[::-1]]
    assert toy==leanInverse
    for layout in range(2):
        Fbase,O,C,T,P=(120,600,3000,4000,5000) if layout==0 else (5000,10000,100000,120000,140000)
        B=1000000;rng=random.Random(31+specno+layout)
        physical=[[d,s,C+q if q<7 else P+q-7] for d,s,q in raw]
        rowsinv=[[d,s,inverse_addr(C,T,P,q)] for d,s,q in physical[::-1]]
        nr={j:rng.randrange(B) for j in [*range(100,107),*range(980,986),*range(990,1001),*range(1160,1169),1170,1180]}
        nr.update({980:M,981:Fbase,982:O,983:C,984:T,985:P})
        nh={Fbase+3*i+k:v for i,row in enumerate(physical) for k,v in enumerate(row)}
        nh.update({O+3*i+k:882+k for i in range(M) for k in range(3)});nh[31]=994
        bank={C+j:coefs[j%7] for j in range(7*2**K)}
        negative={T+j:(-z,t) for j,(z,t) in enumerate(bank.values())}
        constants=[val(1),val(-1),val(F(1,2**K)),val(F(-1,2**K)),val(F(5,4)),val(F(4,5))]
        sh={**data,**bank,**negative,**{P+j:z for j,z in enumerate(constants)},900000:gauss(7,9,True)}
        sr={j:gauss(rng.randrange(13),rng.randrange(17),True) for j in [89,90,91,92,93,94]}
        outputs={0:gauss(9,2)[0]};orders=[8,16]
        rn,hn,rs,hs,steps,pcs,halt,writes,out,order=run(nr,nh,sr,sh,B,outputs=outputs,orders=orders)
        assert steps==21+32*M+sum(23 if q<P else 24 if q in [P,P+2] else 25 for _,_,q in physical)
        assert steps<=57*M+21 and halt==80
        assert all(hn[O+3*i+k]==v for i,row in enumerate(rowsinv) for k,v in enumerate(row))
        assert all(hn[q]==v for q,v in nh.items() if not O<=q<O+3*M)
        assert {j:hs[j] for j in data}==final
        assert all(hs[j][0]==data[j][0] for j in data)
        assert all(hs[q]==v for q,v in sh.items() if q not in {r[0] for r in physical})
        assert all(rn[q]==v for q,v in nr.items() if (q<990 or q>=1001) and(q<1160 or q>=1169) and q!=1170)
        assert all(rs[q]==v for q,v in sr.items() if q<90 or q>=94)
        assert out==outputs and order==orders
        tag_changed|=any(hs[j][1]!=data[j][1] for j in data)
        master_changed|=hs[0]!=sh[0]
        seen|=pcs;traces.append(dict(K=K,M=M,family=family,layout=layout,steps=steps,origin='fresh Lean Gaussian/action + inverse-table specs'))
# Exact non-Gaussian cyclotomic coefficients and dirty data, continuous81 only.
zeta=Q8((F(0),F(1),F(0),F(0)))
for M in [0,1,2,7,32,128]:
    C,T,P,Fbase,O,B=200,400,600,1000,2000,10000
    raw=[(i%5,(i+1)%5,C+(i%7)) for i in range(M)]
    bank={C+j:val(zeta*zeta if j==0 else zeta*Q8.rational(F(j,3))) for j in range(7)}
    neg={T+j:(-v,t) for j,(v,t) in enumerate(bank.values())}
    const=[val(1),val(-1),val(1),val(-1),val(F(5,4)),val(F(4,5))]
    data={j:val(zeta*Q8.rational(j)+Q8.rational(F(1,3)),j%2==0) for j in range(5)}
    nr={980:M,981:Fbase,982:O,983:C,984:T,985:P,100:8,1170:99}
    nh={Fbase+3*i+k:v for i,row in enumerate(raw) for k,v in enumerate(row)};nh[9000]=37
    sh={**data,**bank,**neg,**{P+j:v for j,v in enumerate(const)},9000:val(zeta,True)}
    rn,hn,rs,hs,steps,pcs,halt,*_=run(nr,nh,{},sh,B)
    inverse=[(d,s,inverse_addr(C,T,P,q)) for d,s,q in raw[::-1]]
    expect=model(inverse,model(raw,data,sh),sh)
    assert all(hs[j]==expect[j] and hs[j][0]==data[j][0] for j in data)
    seen|=pcs;traces.append(dict(M=M,steps=steps,origin='independent exact Q[zeta8] continuous bytecode'))
assert tag_changed and master_changed and seen==set(range(81))
# Guard controls are observed failures; violated algebraic geometry is a separate control.
C,T,P,Fbase,O,B=200,400,600,1000,2000,10000
nr={980:1,981:Fbase,982:O,983:C,984:T,985:P};nh={Fbase:0,Fbase+1:1,Fbase+2:C}
sh={0:val(3),1:val(7,True),C:val(0),T:val(0),P:val(1),P+1:val(-1)}
controls=[('missing forward dst',nr,{q:v for q,v in nh.items() if q!=Fbase},sh,B,0),('missing forward src',nr,{q:v for q,v in nh.items() if q!=Fbase+1},sh,B,0),('missing forward coefficient',nr,{q:v for q,v in nh.items() if q!=Fbase+2},sh,B,0)]
controls +=[(name,nr,nh,{q:v for q,v in sh.items() if q!=a},B,0) for name,a in [('missing data dst',0),('missing data src',1),('missing positive coefficient',C),('missing negative coefficient',T)]]
controls +=[('unprepared positive coefficient',nr,nh,{**sh,C:val(1,True)},B,0),('unprepared inverse coefficient',nr,nh,{**sh,T:val(-1,True)},B,0),('entry word guard',nr,nh,sh,80,0),('inverse allocation word guard',{**nr,982:B},nh,sh,B,0),('missing instruction',nr,nh,sh,B,81)]
negative=[]
for name,n,h,s,b,pc in controls:
    try:run(n,h,{},s,b,pc)
    except Failure as e:negative.append(dict(name=name,observed=str(e)))
    else:raise AssertionError(name)
_,_,_,out,*_=run(nr,nh,{},sh,B);assert out[0][0]==sh[0][0] and out[0][1]
selfnh={**nh,Fbase+1:0};selfsh={**sh,C:val(1),T:val(-1)}
_,_,_,bad,*_=run(nr,selfnh,{},selfsh,B);assert bad[0][0]!=selfsh[0][0]
report=dict(status='PASS',cases=len(traces),steps=sum(c['steps'] for c in traces),all_pcs=sorted(seen),negative=negative,zero_coefficient_tag_growth_observed=True,master_tag_change_without_no_dst0_observed=True,self_shear_geometry_control='dst=src violates required hypothesis; numeric restoration fails without runtime guard failure',cases_detail=traces,program_sha256=hashlib.sha256((root/'program.json').read_bytes()).hexdigest(),specs_sha256=hashlib.sha256((root/'specs.json').read_bytes()).hexdigest(),scope='Actual continuous81 inverse-table + forward20 + inverse20; honest original physical rows and prepared signed banks, no between-phase host writes. Numeric restoration only; exact tags may grow. Independent Q[zeta8] arithmetic is diagnostic, not Lean Complex evaluation.')
(root/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k!='cases_detail'})
