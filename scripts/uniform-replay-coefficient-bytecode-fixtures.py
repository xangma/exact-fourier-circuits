import json
from fractions import Fraction as F
from pathlib import Path
repo=Path(__file__).resolve().parents[1]
root=repo/'logs/uniform-bytecode/replay-coefficient'
code=json.loads((root/'program.json').read_text())
sizes=json.loads((root/'sizes.json').read_text())
assert len(code)==42
assert {row[0] for row in code} <= {0,1,4,5,6,7,8,9,10}
class Failure(Exception): pass

def value(re=0,im=0,data=False): return (F(re),F(im),data)
def neg(z): return (-z[0],-z[1],z[2])
def field(kind,x,y):
    a,b,dx=x;c,d,dy=y
    if kind==0:return (a+c,b+d,dx or dy)
    if kind==1:return (a-c,b-d,dx or dy)
    if kind==2:
        if dx and dy:raise Failure('data-data product')
        return (a*c-b*d,a*d+b*c,dx or dy)
    if kind==3:
        if dx or dy:raise Failure('unprepared division')
        norm=c*c+d*d
        if not norm:raise Failure('zero denominator')
        return ((a*c+b*d)/norm,(b*c-a*d)/norm,False)
    raise AssertionError(kind)

def execute(nr,nh,sr,sh,B,start=0):
    nr,nh,sr,sh=nr.copy(),nh.copy(),sr.copy(),sh.copy()
    pc=start;steps=0;seen=set();writes=[]
    def bound(v):
        if not 0<=v<=B:raise Failure('word bound')
    bound(pc)
    for v in nr.values():bound(v)
    for a,v in nh.items():bound(a);bound(v)
    for a in sh:bound(a)
    while steps<200000:
        if not 0<=pc<len(code):raise Failure('missing instruction')
        seen.add(pc);op,*args=code[pc];steps+=1;npc=pc+1
        if op==6:return nr,nh,sr,sh,steps,seen,pc,writes
        if op==0:
            r,v=args;bound(v);nr[r]=v
        elif op==1:
            kind,r,l,h=args;x,y=nr.get(l,0),nr.get(h,0)
            if kind==0:v=x+y
            elif kind==1:v=max(0,x-y)
            elif kind==2:v=x*y
            elif kind in (3,4):
                if not y:raise Failure('zero Nat divisor')
                v=x//y if kind==3 else x%y
            else:raise AssertionError(kind)
            bound(v);nr[r]=v
        elif op==4:
            l,r,y,n=args;npc=y if nr.get(l,0)<nr.get(r,0) else n
        elif op==5:npc=args[0]
        elif op==7:
            r,a=args;address=nr.get(a,0);bound(address)
            if address not in sh:raise Failure('missing scalar source')
            sr[r]=sh[address]
        elif op==8:
            a,r=args;address=nr.get(a,0);bound(address);v=sr.get(r,value())
            sh[address]=v;writes.append((address,v))
        elif op==9:
            r,num,den=args;sr[r]=value(F(num,den))
        elif op==10:
            kind,r,l,h=args;sr[r]=field(kind,sr.get(l,value()),sr.get(h,value()))
        else:raise AssertionError(op)
        bound(npc);pc=npc
    raise AssertionError('nontermination')

traces=[];all_pcs=set();total_steps=0
for K,N,runtime in sizes:
    assert N==2**K and runtime==5*K+56*N+31
    M=7*N
    for layout in range(3):
        C=[0,13,503][layout];T=C+M+layout*9;P=T+M+layout*13;B=P+2000
        for dirty in range(2):
            bank=[value(F((j*j+K+3)%19-9,3),F((j+K)%7-3,5)) for j in range(M)]
            if dirty==0:bank[0]=value(0)
            nr={r:(r*31+dirty+7)%B for r in range(830)}
            nr.update({760:K,761:C,762:T,763:P})
            nh={0:17,31:9,B-1:K}
            sr={r:value(F(r-42,7),F(r%5-2,3),bool((r+dirty)%2)) for r in range(96)}
            sh={0:value(1,1),B-1:value(41,7,True)}
            for j,v in enumerate(bank):sh[C+j]=v
            for j in range(M):sh[T+j]=value(j+3,-j,bool(dirty))
            for j in range(6):
                if j%2==dirty:sh[P+j]=value(j+101,j+2,True)
            nr2,nh2,sr2,sh2,t,pcs,halt,writes=execute(nr,nh,sr,sh,B)
            constants=[value(1),value(-1),value(F(1,N)),value(F(-1,N)),value(F(5,4)),value(F(4,5))]
            assert t==runtime and halt==41
            assert [sh2[C+j] for j in range(M)]==bank
            assert [sh2[T+j] for j in range(M)]==[neg(v) for v in bank]
            assert [sh2[P+j] for j in range(6)]==constants
            assert writes==[(P+j,v) for j,v in enumerate(constants)]+[(T+j,neg(v)) for j,v in enumerate(bank)]
            assert nh2==nh
            assert all(nr2[r]==v for r,v in nr.items() if r<765 or r>=773)
            assert all(sr2[r]==v for r,v in sr.items() if r<80 or r>=89)
            assert sh2[0]==sh[0]
            assert all(sh2[a]==v for a,v in sh.items() if not(T<=a<T+M or P<=a<P+6))
            assert set(sh2)==set(sh)|set(range(T,T+M))|set(range(P,P+6))
            assert nr2[769]==N and nr2[770]==M and nr2[768]==M
            all_pcs.update(pcs);total_steps+=t
            traces.append(dict(K=K,layout=layout,dirty=dirty,steps=t,exact_values=True,prepared_false=True,exact_write_order=True,frames=True))
assert all_pcs==set(range(42)),set(range(42))-all_pcs
negative=[]
K=2;M=28;C=13;T=50;P=90;B=2200
nr={760:K,761:C,762:T,763:P};nh={};sr={};sh={C+j:value(j) for j in range(M)}
for kind in ['missing first source','missing interior source','word bound','missing instruction','zero division','unprepared division']:
    heap=sh.copy();regs=sr.copy();budget=B;start=0
    if kind=='missing first source':del heap[C]
    elif kind=='missing interior source':del heap[C+17]
    elif kind=='word bound':budget=10
    elif kind=='missing instruction':start=42
    elif kind=='zero division':start=14;regs={80:value(1),82:value(0)}
    else:start=14;regs={80:value(1),82:value(2,data=True)}
    try:execute(nr,nh,regs,heap,budget,start)
    except Failure as exc:negative.append(dict(kind=kind,reason=str(exc)))
    else:raise AssertionError('guard accepted '+kind)
# Out-of-contract true source flags are propagated, never silently retagged.
sh[C+3]=value(2,1,True)
_,_,_,out,*_=execute(nr,nh,sr,sh,B)
assert out[T+3]==value(-2,-1,True)
receipt=dict(status='PASS',cases=len(traces),steps=total_steps,all42_pcs=True,negative_controls=negative,data_flag_propagation=True,traces=traces,scope='Fresh Lean-exported literal42. Exact Fraction Gaussian arithmetic and charged WordBound on every mutation. Prepared input premise verified; dirty destination/source retained, normalization and signs generated physically. Division controls deliberately enter PC14 outside startup theorem.')
(root/'fixtures.json').write_text(json.dumps(receipt,indent=2)+'\n')
print({k:receipt[k] for k in ['status','cases','steps','all42_pcs','negative_controls','data_flag_propagation']})
