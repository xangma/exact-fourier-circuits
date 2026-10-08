#!/usr/bin/env python3
"""Exact execution of the Lean-exported271; expected tape is independently typed records."""
from pathlib import Path
from collections import Counter
import copy, json, hashlib, random
BASE=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/cross-topology'
CODE=json.loads((BASE/'program.json').read_text())
EXPECTED=json.loads((BASE/'record-fixtures.json').read_text())
assert len(CODE)==271
assert all(row[0] in {'lit','add','sub','mul','div','mod','putnat','getnat','branch','jump','halt'} for row in CODE)
assert sum(row[0]=='putnat' for row in CODE)==15

class Failure(Exception): pass

def dimensions(K):
    N=1<<K;G=3*K*N//2;T=2*G+2*N
    return N,G,T

def allocation(K,d):
    N,G,T=dimensions(K)
    return d+5*T+100*(N+G+K+1)**2+200+500

def state(K,a,e,c,d,seed):
    rng=random.Random(seed);N,G,T=dimensions(K);H=6*T+2*a
    nat={560:K,561:a,562:e,563:c,564:d}
    nat.update({i:rng.randrange(1000)for i in range(565,600)})
    nat.update({i:rng.randrange(1000)for i in range(400,420)})
    nat.update({i:1+i for i in range(70,97)})
    nat.update({i:100+i for i in [*range(100,107),*range(450,480),*range(480,525),*range(525,550),*range(550,556),559,600]})
    heap={0:111,9:211,100:313,1000:717,c-1:891,c+5*T:893,d-1:897,d+5*H:899}
    heap.update({c+i:rng.randrange(1000)for i in range(5*T)})
    heap.update({d+i:rng.randrange(1000)for i in range(5*H)})
    return dict(pc=0,nat=nat,heap=heap,scalar_heap={0:('master',False),25:('input',True),999:('kernel',False)},
                scalar_reg={0:('dirty',True),70:('prepared',False)},output={0:'dirty',7:'retained'},roots=[1,17,64])

def execute(initial,B):
    s=copy.deepcopy(initial);R=s['nat'];H=s['heap'];pc=s['pc'];steps=0;counts=Counter();maxWord=0;writes=[]
    if pc>B or any(not 0<=v<=B for v in R.values()): raise Failure('initial word bound')
    if any(not (0<=a<=B and 0<=v<=B) for a,v in H.items()): raise Failure('initial Nat heap bound')
    while steps<2_000_000:
        if pc>B or not 0<=pc<len(CODE): raise Failure('pc bound')
        ins=CODE[pc];op=ins[0];counts[op]+=1;steps+=1
        if op=='halt':s['pc']=pc;return s,steps,counts,maxWord,writes
        if op=='lit':d,v=ins[1:]
        elif op in {'add','sub','mul','div','mod'}:
            d,l,r=ins[1:];a,b=R.get(l,0),R.get(r,0)
            if op in {'div','mod'} and b==0: raise Failure(f'{op} zero at {pc}')
            v=a+b if op=='add' else max(a-b,0) if op=='sub' else a*b if op=='mul' else a//b if op=='div' else a%b
        elif op=='getnat':
            d,address=ins[1:];a=R.get(address,0)
            if a not in H:raise Failure(f'missing Nat at {pc}')
            v=H[a]
        elif op=='putnat':
            a,v=R.get(ins[1],0),R.get(ins[2],0)
            if a>B or v>B: raise Failure(f'heap bound at {pc}')
            H[a]=v;writes.append(a);pc+=1;continue
        elif op=='branch':pc=ins[3] if R.get(ins[1],0)<R.get(ins[2],0) else ins[4];continue
        elif op=='jump':pc=ins[1];continue
        else:raise AssertionError(op)
        if not 0<=v<=B:raise Failure(f'written word bound at {pc}')
        R[d]=v;maxWord=max(maxWord,v);pc+=1
    raise Failure('runaway')

cases=[]
for key,expected in EXPECTED.items():
    K,a,e=map(int,key.split(','));N,_,G=dimensions(K);H=6*G+2*a
    for seed in (0,17):
        c=10000+seed*31;d=c+5*G+100
        before=state(K,a,e,c,d,seed);B=c+d+5*(G+H)+100*(N+(3*K*N//2)+K+1)**2+200+10000*(N+G+a+e+K+1)**2
        after,t,counts,maxWord,writes=execute(before,B)
        rows=[[after['heap'][d+5*j+h]for h in range(5)]for j in range(H)]
        assert rows==expected,(key,seed,next((i for i,(r,s)in enumerate(zip(rows,expected))if r!=s),None))
        assert len(rows)==6*(3*K*N+2*N)+2*a
        assert after['pc']==270
        assert writes==list(range(c,c+5*G))+list(range(d,d+5*H))
        assert t<=4*K+113+(19*K+344)*G+40*a
        for j,(op,l,r,kind,payload)in enumerate(rows):
            assert op in (0,1,2) and l<e+1+j,(key,j,l)
            if op<2:assert r<e+1+j and kind==payload==0
            elif kind==1:assert 0<=payload<7*N and r==0
            else:assert kind==0 and payload==N and r==0
        for field in ('scalar_heap','scalar_reg','output','roots'):assert after[field]==before[field]
        for x,v in before['heap'].items():
            if not(c<=x<c+5*G or d<=x<d+5*H):assert after['heap'][x]==v
        for i,v in before['nat'].items():
            if not(70<=i<=96 or 400<=i<=419 or 560<=i<=599):assert after['nat'][i]==v
        for i in range(560,565):assert after['nat'][i]==before['nat'][i]
        cases.append(dict(height=K,target=a,source=e,seed=seed,nodes=H,steps=t,maxWritten=maxWord,opCounts=dict(counts)))
        print(json.dumps(cases[-1]),flush=True)
failed=[]
for pc,reg in [(16,410),(167,582)]:
    s=state(0,1,1,10000,10100,0);s['pc']=pc;s['nat'][reg]=0
    try:execute(s,10**9)
    except Failure as ex:failed.append(str(ex))
    else:raise AssertionError('missing arithmetic guard')
s=state(0,1,1,10000,10100,0);s['pc']=174;s['nat'][569]=999999
try:execute(s,10**9)
except Failure as ex:failed.append(str(ex))
else:raise AssertionError('missing load guard')
s=dict(pc=0,nat={560:0,561:0,562:0,563:0,564:0},heap={},scalar_heap={},scalar_reg={},output={},roots=[])
try:execute(s,4)
except Failure as ex:failed.append(str(ex))
else:raise AssertionError('missing bound guard')
receipt=dict(status='PASS',positiveCases=len(cases),chargedSteps=sum(c['steps']for c in cases),cases=cases,
 expectedFailures=failed,programSha256=hashlib.sha256((BASE/'program.json').read_bytes()).hexdigest(),
 comparison='actual typed Lean crossDAG.program records encoder K0..6 empty/full/ragged',
 noSuppliedTape=True,topologicalEveryOperand=True,scalarRootOutputFrames=True)
(BASE/'runtime-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='cases'}),flush=True)
