"""Continuous literal374 exact Gaussian diagnostics. No phase host writes."""
from pathlib import Path
from fractions import Fraction as F
import copy,json
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode'
code=json.loads((P/'programs.json').read_text())['preparedZeroFree']
assert len(code)==374 and all(row[0]!='unsupported' for row in code)
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
def loop_cost(e):
    return 2 if not e else loop_cost(e//2)+(7 if e%2 else 6)
def runtime(rows):return 7+sum(25+loop_cost(a)+loop_cost(d)+(1 if flag==0 else 2) for a,d,flag in rows)


specs=json.loads((P/'prepared-zero-free-specs.json').read_text())
def lower_rows(spec,b,a):
    rows=[];r=spec['rootCount']
    for j,(tag,left,right) in enumerate(spec['nodes']):
        if tag==0:row=(0,b+1+r+j,b)
        elif tag==1:row=(0,b+1+left,b)
        else:row=(tag-2,a+left,a+right)
        rows.append(row)
    return rows

def pass_runtime(spec):
    r=spec['rootCount'];rows=spec['rationals']
    leaf=7*r+15+runtime(rows)
    printer=7+sum(24 if tag<2 else 22 for tag,_,_ in spec['nodes'])
    interpreter=5+sum([18,20,22,22][op] for op,_,_ in lower_rows(spec,100,200))
    return leaf+printer+interpreter+16

def direct_eval(spec,roots):
    values=[]
    for j,(tag,left,right) in enumerate(spec['nodes']):
        if tag==0:
            mag,den,sign=spec['rationals'][j]
            values.append(scalar((-1 if sign else 1)*F(mag,den)))
        elif tag==1:values.append(roots[left])
        else:values.append(field(['fadd','fsub','fmul','fdiv'][tag-2],values[left],values[right]))
    return values


def total_runtime(spec):return 2*pass_runtime(spec)+22+20*spec['nodeCount']+20

def conjugate(z):
    (re,im),dep=z;return ((re,-im),dep)

def initial(spec,layout,omega):
    l,c,rows,b0,a0,R,b1,a1,d,e,f=layout;k=spec['nodeCount']
    assert 0<b0 and b0+2+k<=a0 and a0+k<=R and R+1<=b1 and b1+2+k<=a1
    assert c+3*k<=rows or rows+3*k<=c
    assert l+3*k<=rows or rows+3*k<=l
    assert a1+k<=d and d+2<=e and e+k<=f
    B=max(10000,l+c+rows+b0+a0+R+b1+a1+8*k+500+d+e+f,max([v for row in spec['rationals'] for v in row]+[0]))
    s={'pc':0,'nat':{j:(19*j+7)%(B//8+1) for j in range(420)},
       'nh':{j:(31*j+5)%(B//8+1) for j in range(1700) if j%7!=3},
       'sr':{j:scalar(j-2,3-j,j%2) for j in range(64)},
       'sh':{j:scalar(j-3,11-j,j%3!=1) for j in range(10000)}|{a1+k+9:scalar(9,-7,True)},
       'out':{0:(F(3),F(-5)),7:(F(0),F(1))},'roots':[4,31,1]}
    s['nat'].update({350:k,351:b0,352:a0,353:R,354:b1,355:a1,356:l,357:c,358:rows,380:d,381:e,382:f})
    s['sh'][0]=omega
    # Inverse source, leaves, row output, and coefficient banks are all dirty.
    for j,row in enumerate(spec['rationals']):
        for t,v in enumerate(row):s['nh'][l+3*j+t]=v
    for j,row in enumerate(spec['nodes']):
        for t,v in enumerate(row):s['nh'][c+3*j+t]=v
    return s,B

cases=[];total=0;allVisits=set()
layouts=[(500,700,1000,2000,2100,2200,2300,2400,2500,2510,2600),
 (1000,700,500,2048,2200,2400,2600,2800,3000,3010,3100),
 (1000,700,500,33,80,130,164,240,300,310,400)]
roots=[('i',scalar(0,1)),('minus-i',scalar(0,-1)),('one',scalar(1)),
 ('minus-one',scalar(-1)),('unit-rational-nonreal',scalar(F(3,5),F(4,5)))]
for spec in specs:
    assert spec['runtime']==total_runtime(spec)
    for layout in layouts:
        for name,omega in roots:
            s,B=initial(spec,layout,omega);before=copy.deepcopy(s)
            l,c,rows,b0,a0,R,b1,a1,d,e,f=layout;k=spec['nodeCount']
            inverse=field('fdiv',scalar(1),omega);assert inverse==conjugate(omega)
            values=direct_eval(spec,[omega]);conjugates=[conjugate(v) for v in values]
            assert direct_eval(spec,[inverse])==conjugates
            lam=scalar(1+sum(re*re+im*im for (re,im),dep in values))
            lamInv=field('fdiv',scalar(1),lam)
            shifted=[field('fsub',v,lam) for v in values]
            shiftedInv=[field('fdiv',scalar(1),v) for v in shifted]
            cost=total_runtime(spec);steps,visits=execute(s,B,cost);assert steps==cost
            assert steps<=156+2*k*(14*((B+1).bit_length())+87)
            assert s['sh'][0]==before['sh'][0] and s['sh'][R]==inverse
            assert [s['sh'][a0+j] for j in range(k)]==values
            assert [s['sh'][a1+j] for j in range(k)]==conjugates
            assert s['sh'][d]==lam and s['sh'][d+1]==lamInv
            assert [s['sh'][e+j] for j in range(k)]==shifted
            assert [s['sh'][f+j] for j in range(k)]==shiftedInv
            assert lam[0]!=(0,0) and all(v[0]!=(0,0) for v in shifted)
            for b in [b0,b1]:
                assert s['sh'][b]==scalar()
                assert s['sh'][b+1]==(omega if b==b0 else inverse)
                for j,(mag,den,sign) in enumerate(spec['rationals']):
                    assert s['sh'][b+2+j]==scalar((-1 if sign else 1)*F(mag,den))
            for j,row in enumerate(lower_rows(spec,b1,a1)):
                assert [s['nh'][rows+3*j+i] for i in range(3)]==list(row)
            for i in set(before['sh'])|set(s['sh']):
                if i!=R and all(i<lo or i>=hi for lo,hi in [(b0,b0+2+k),(a0,a0+k),(b1,b1+2+k),(a1,a1+k),(d,d+2),(e,e+k),(f,f+k)]):
                    assert s['sh'].get(i)==before['sh'].get(i)
            for i in set(before['nh'])|set(s['nh']):
                if i<rows or i>=rows+3*k:assert s['nh'].get(i)==before['nh'].get(i)
            for i in range(420):
                if i>=10 and (i<147 or i>=154) and (i<220 or i>=226) and (i<230 or i>=260) and (i<273 or i>=282) and (i<370 or i>=380) and i not in [137,281,359,383]:
                    assert s['nat'][i]==before['nat'][i]
            assert [s['nh'][l+j] for j in range(3*k)]==[before['nh'][l+j] for j in range(3*k)]
            assert [s['nh'][c+j] for j in range(3*k)]==[before['nh'][c+j] for j in range(3*k)]
            assert s['out']==before['out'] and s['roots']==before['roots']
            assert visits[335]==1 and visits[336]==1 and visits[342]==1 and visits[372]==1 and visits[373]==1 and s['pc']==373
            total+=steps;allVisits.update(visits)
            cases.append({'name':spec['name'],'layout':layout,'master':name,'steps':steps,'wordBound':B})
negative=[]
spec=next(p for p in specs if p['name']=='shared-all-operations');layout=layouts[0]
for kind,value in [('missing-master',None),('zero-master',scalar()),('unprepared-master',scalar(0,1,True))]:
    s,B=initial(spec,layout,scalar(0,1))
    if value is None:del s['sh'][0]
    else:s['sh'][0]=value
    try:execute(s,B,total_runtime(spec));raise AssertionError('accepted '+kind)
    except Failure as ex:negative.append({'kind':kind,'failure':ex.args[0]})
for kind,address in [('missing-rational',500),('missing-typed',700)]:
    s,B=initial(spec,layout,scalar(0,1));del s['nh'][address]
    try:execute(s,B,total_runtime(spec));raise AssertionError('accepted '+kind)
    except Failure as ex:negative.append({'kind':kind,'failure':ex.args[0]})
s,B=initial(spec,layout,scalar(0,1));s['nh'][501]=0
try:execute(s,B,total_runtime(spec));raise AssertionError('accepted literal denominator0')
except Failure as ex:negative.append({'kind':'zero-literal-denominator','failure':ex.args[0]})
s,B=initial(spec,layout,scalar(0,1));s['nh'][500]=0
try:execute(s,B,total_runtime(spec));raise AssertionError('accepted inadmissible DAG')
except Failure as ex:negative.append({'kind':'actual-DAG-zero-divisor','failure':ex.args[0]})
assert allVisits==set(range(374)),sorted(set(range(374))-allVisits)
result={'status':'PASS','programInstructions':len(code),'exactCases':len(cases),
 'totalChargedSteps':total,'cases':cases,'negativeCases':negative,'visitedPCs':len(allVisits),
 'checks':['one continuous374 trace, no per-phase host writes','all374 literal PCs visited',
 'actual same typed/rational tapes used twice','independent exact Gaussian Fraction oracle',
 'empty/root/rational/all shared operations/retained zeros/32-node DAG cases',
 'nonreal unit masters i,-i,3/5+4/5i','zero coefficients without coefficient-zero branches',
 'actual original+conjugate prepared banks retained','lambda=1+sum normSquared and exact inverse',
 'actual nonzero shifted coefficients and prepared inverses','all dirty external banks/tags retained',
 'same WordBound every step/exact phase and helper costs','complete output/rootOrders retained',
 'master heap0 and conjugate root retained','both original source tapes retained',
 'NatHeap outside row region retained','ScalarHeap outside allocated regions retained',
 'saved100..106/caller350..358/380..382 retained','missing-source/unprepared/div0 controls']}
(P/'prepared-zero-free-fixtures.json').write_text(json.dumps(result,indent=2))
print(json.dumps({key:result[key] for key in ['status','programInstructions','exactCases','totalChargedSteps','visitedPCs','negativeCases']},indent=2))
