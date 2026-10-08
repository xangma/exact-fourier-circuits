"""Literal contiguous-power writer: exact Gaussian diagnostics and physical frames."""
from pathlib import Path
from fractions import Fraction as F
import copy,json
output_dir=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode'
code=json.loads((output_dir/'programs.json').read_text())['contiguousPower']
assert len(code)==11 and all(row[0]!='unsupported' for row in code)
def scalar(re=0,im=0,dep=False):return ((F(re),F(im)),bool(dep))
def field(op,a,b):
    (ar,ai),ad=a;(br,bi),bd=b
    if op=='fadd':return ((ar+br,ai+bi),ad or bd)
    if op=='fsub':return ((ar-br,ai-bi),ad or bd)
    if op=='fmul':
        assert not(ad and bd),'multiply guard'
        return ((ar*br-ai*bi,ar*bi+ai*br),ad or bd)
    assert op=='fdiv' and not ad and not bd and (br or bi),'division guard'
    norm=br*br+bi*bi
    return ((F(ar*br+ai*bi,norm),F(ai*br-ar*bi,norm)),False)
class Failure(Exception):
    pass
def execute(s,B,budget):
    steps=0;visits={}
    def check():
        assert s['pc']<=B and max(s['nat'].values())<=B
        assert all(i<=B and v<=B for i,v in s['nh'].items())
        assert all(i<=B for i in s['sh']) and all(i<=B for i in s['out'])
        assert all(r<=B for r in s['roots'])
    check()
    while True:
        pc=s['pc'];assert 0<=pc<len(code)
        op,*args=code[pc];steps+=1;assert steps<=budget
        visits[pc]=visits.get(pc,0)+1
        if op=='halt':return steps,visits
        s['pc']+=1
        if op=='lit':d,v=args;s['nat'][d]=v
        elif op in ['add','sub','mul','div','mod']:
            d,l,r=args;a,b=s['nat'][l],s['nat'][r]
            if op=='add':v=a+b
            elif op=='sub':v=max(0,a-b)
            elif op=='mul':v=a*b
            elif not b:raise Failure(('zero Nat divisor',pc))
            elif op=='div':v=a//b
            else:v=a%b
            s['nat'][d]=v
        elif op=='putnat':
            a,r=args;s['nh'][s['nat'][a]]=s['nat'][r]
        elif op=='getnat':
            d,a=args;address=s['nat'][a]
            if address not in s['nh']:raise Failure(('missing Nat source',pc,address))
            s['nat'][d]=s['nh'][address]
        elif op=='getscalar':
            d,a=args;address=s['nat'][a]
            if address not in s['sh']:raise Failure(('missing scalar source',pc,address))
            s['sr'][d]=s['sh'][address]
        elif op=='rat':d,num,den=args;s['sr'][d]=scalar(F(num,den))
        elif op in ['fadd','fsub','fmul','fdiv']:
            d,l,r=args
            try:s['sr'][d]=field(op,s['sr'][l],s['sr'][r])
            except AssertionError as e:raise Failure((str(e),pc))
        elif op=='putscalar':a,r=args;s['sh'][s['nat'][a]]=s['sr'][r]
        elif op=='branch':l,r,y,n=args;s['pc']=y if s['nat'][l]<s['nat'][r] else n
        elif op=='jump':s['pc']=args[0]
        else:raise AssertionError(op)
        check()

def initial(N,P,Q,omega,B=10000):
    assert P+N<=Q<=B
    s={'pc':0,'nat':{j:(19*j+7)%(B//8+1) for j in range(600)},
       'nh':{j:(31*j+5)%(B//8+1) for j in range(20)},
       'sr':{j:scalar(j-2,3-j,j%2) for j in range(70)},
       'sh':{j:scalar(j-3,11-j,j%3!=1) for j in range(600)},
       'out':{0:(F(3),F(-5)),7:(F(0),F(1))},'roots':[4,31,1]}
    s['nat'].update({550:N,551:Q,552:P})
    s['sh'][Q]=omega
    return s

cases=[];visited=set();total=0
roots=[scalar(),scalar(1),scalar(-1),scalar(0,1),scalar(3,4),scalar(F(3,5),F(4,5))]
for N in [0,1,2,3,7,32,64]:
    for P,Q in [(20,100),(200,300),(401,600)]:
        for omega in roots:
            s=initial(N,P,Q,omega);before=copy.deepcopy(s)
            cost=6*N+6;steps,visits=execute(s,10000,cost)
            assert steps==cost and s['pc']==10
            # Independent multiplication using exact Gaussian rational pairs.
            re,im=F(1),F(0);wr,wi=omega[0]
            for j in range(N):
                assert s['sh'][P+j]==((re,im),False)
                re,im=re*wr-im*wi,re*wi+im*wr
            for j in set(before['sh'])|set(s['sh']):
                if j<P or P+N<=j:assert s['sh'].get(j)==before['sh'].get(j)
            assert s['sh'][Q]==omega
            assert s['nh']==before['nh'] and s['out']==before['out'] and s['roots']==before['roots']
            for j in range(600):
                if j<553 or j>=556:assert s['nat'][j]==before['nat'][j]
            for j in range(70):
                if j<60 or j>=62:assert s['sr'][j]==before['sr'][j]
            cases.append({'width':N,'destination':P,'source':Q,'root':str(omega),'steps':steps})
            visited.update(visits);total+=steps

negative=[]
for kind in ['missing-root','dependent-root']:
    s=initial(4,20,100,scalar(0,1))
    if kind=='missing-root':del s['sh'][100]
    else:s['sh'][100]=scalar(0,1,True)
    try:execute(s,10000,100);raise AssertionError('accepted '+kind)
    except Failure as ex:negative.append({'kind':kind,'failure':ex.args[0]})
s=initial(7,20,100,scalar(0,1));s['nat'][552]=9999
try:execute(s,10000,100);raise AssertionError('accepted computed address overflow')
except AssertionError as ex:
    assert 'accepted' not in str(ex)
    negative.append({'kind':'computed-address-overflow','failure':'WordBound exceeded during address arithmetic'})
assert visited==set(range(11))
result={'status':'PASS','instructions':11,'exactCases':len(cases),'totalChargedSteps':total,
        'visitedPCs':len(visited),'cases':cases,'negativeCases':negative,
        'scope':'Physical prepared root is an explicit entry input; exact Gaussian Fraction diagnostics complement the universal Lean execution theorem.'}
(output_dir/'contiguous-power-fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','instructions','exactCases','totalChargedSteps','visitedPCs','negativeCases']},indent=2))
