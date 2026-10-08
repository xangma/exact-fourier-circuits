"""Fresh exact physical C-axis traces; not a whole saving-network execution."""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute, add, mul

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'logs/uniform-bytecode/binary-c-stage'
CODE=json.loads((PACKET/'program.json').read_text())
assert len(CODE)==30
DIAGONAL=scalar(4,F(1,2),F(1,2))
OFF_DIAGONAL=scalar(4,F(1,2),F(-1,2))
WRITES={0,1,2,2803,2804,2805,2806,2810,2811}


def fresh(p,q,base,salt):
    s=dict(pc=0,nat=[(17*i+salt)%97 for i in range(2820)],
           nh={0:17,100:31},sh={1:DIAGONAL,2:OFF_DIAGONAL},
           sr={0:scalar(4,3,-7,True),8:scalar(4,F(3,7),F(2,3))},
           out={2:scalar(4,-3,2)[0]},roots=[4,12])
    for r,v in {2800:p,2801:base,2802:q}.items():s['nat'][r]=v
    for z in range(p*2*q):
        s['sh'][base+z]=scalar(4,F(3*z+salt-5,7),F(2*z-salt+1,11),(z+salt)%3!=0)
    s['sh'][base-1]=scalar(4,3,2,True)
    s['sh'][base+p*2*q]=scalar(4,-7,0,False)
    return s


cases=[];covered=set();ticks=0
for p in (1,2,5):
    for q in (0,1,3):
        for base in (7,1000):
            for salt in (0,31):
                s=fresh(p,q,base,salt);before=copy.deepcopy(s)
                expected=copy.deepcopy(s['sh'])
                for i in range(p*q):
                    left=base+i%p+2*p*(i//p);right=left+p
                    u,v=before['sh'][left],before['sh'][right]
                    expected[left]=add(mul(DIAGONAL,u),mul(OFF_DIAGONAL,v))
                    expected[right]=add(mul(OFF_DIAGONAL,u),mul(DIAGONAL,v))
                steps,pcs,peak=execute(CODE,s,10000,25*p*q+6,4)
                assert steps==25*p*q+6 and s['pc']==29
                assert s['sh']==expected
                for key in ('nh','out','roots'):assert s[key]==before[key],key
                for r in range(len(s['nat'])):
                    if r not in WRITES:assert s['nat'][r]==before['nat'][r],r
                for r in set(s['sr'])|set(before['sr']):
                    if r>=8:assert s['sr'].get(r)==before['sr'].get(r),r
                assert s['nat'][2804]==p*q
                assert s['nat'][100:107]==before['nat'][100:107]
                covered.update(pcs);ticks+=steps
                cases.append(dict(P=p,Q=q,base=base,steps=steps,maximumWord=peak))

controls=[]
def reject(name,state,bound=10000,fuel=10000):
    try:execute(CODE,state,bound,fuel,4)
    except (AssertionError,KeyError):controls.append(name);return
    raise AssertionError('negative control accepted: '+name)

s=fresh(1,1,7,31);del s['sh'][1];reject('missing diagonal coefficient',s)
s=fresh(1,1,7,31);del s['sh'][2];reject('missing off-diagonal coefficient',s)
s=fresh(1,1,7,31);del s['sh'][7];reject('missing left source',s)
s=fresh(1,1,7,31);del s['sh'][8];reject('missing right source',s)
s=fresh(1,1,7,31);s['sh'][1]=(DIAGONAL[0],True);reject('data-data multiply guard',s)
reject('charged runtime guard',fresh(1,1,7,31),fuel=30)
s=fresh(2,2,7,31);s['nat']=[0]*2820;s['nat'][2800:2803]=[2,7,2];s['nh']={};s['out']={};s['roots']=[]
reject('final PC word guard from bounded initial state',s,bound=20)
s=fresh(5,1,97,31);s['sh']={a:v for a,v in s['sh'].items() if a<=100}
reject('computed right address word guard from bounded initial state',s,bound=100)
s=fresh(1,1,7,31);s['pc']=5;s['nat'][2800]=0
reject('division zero in index fragment',s)
assert covered==set(range(30))
result=dict(status='PASS',exactCases=len(cases),chargedSteps=ticks,cases=cases,
            negativeControls=controls,coveredPCs=sorted(covered),
            scope='Actual complete ordinary binary C-axis stages on arbitrary tagged exact Scalars. Physical constants a/b supplied as stated input bank. No coefficient startup, full tensor product, residual child, all-length DFT or CUDA timing claim.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [Path(__file__),PACKET/'program.json',ROOT/'verification/ExportBinaryCStageBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'complete exact C-axis stages,',ticks,'charged steps,',len(controls),'guard controls')
