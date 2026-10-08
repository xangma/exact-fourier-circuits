"""Exact continuous fixed-template→runtime-q patch checks; no host phase writes.

Small generic templates only. No child/opcode interpretation or huge seed run.
"""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute
ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'logs/uniform-bytecode/fixed-network-literal-decoder'
PROGRAMS=json.loads((PACKET/'programs.json').read_text())
SPECS=json.loads((PACKET/'spec.json').read_text())

def fresh(base,q,bound):
    s=dict(pc=0,nat=[(17*i+23)%101 for i in range(2715)],
           nh={base-1:13,base+500:31,bound-1:47},
           sh={base:scalar(4,F(2,3),F(-4,7),True),bound-2:scalar(4,0,0,False)},
           sr={0:scalar(4,3,-7,True),2700:scalar(4,-2,9,False)},
           out={1:scalar(4,-1,7)[0]},roots=[4,12])
    s['nat'][2599]=q;s['nat'][2600]=base
    return s
cases,coverage,charged=[],{},0
for spec in SPECS:
    name,data,lens=spec['name'],spec['data'],spec['recordLengths']
    code=PROGRAMS[name]
    assert len(code)==spec['steps']==3*len(data)+3*len(lens)+7
    assert sum(lens)==len(data) and all(size>=8 for size in lens)
    assert all(i[0] in ('lit','putnat','add','jump','halt') for i in code)
    # Runtime q is never a code literal or an input-dependent program argument.
    assert any(i==['putnat',2700,2599] for i in code) if lens else True
    coverage[name]=set()
    for base in [7,500,10000]:
        for q in [0,1,3,2**71]:
            bound=max(base+1000,len(code)+10,max(data,default=0)+10,q+10)
            state=fresh(base,q,bound);before=copy.deepcopy(state)
            expected=list(data);pos=0
            for size in lens:expected[pos+1]=q;pos+=size
            steps,pcs,peak=execute(code,state,bound,1000000,4)
            assert steps==spec['steps']
            assert [state['nh'][base+j] for j in range(len(data))]==expected
            assert state['nat'][2700]==base+len(data)+1
            assert state['nat'][2599]==q
            for z in set(state['nh'])|set(before['nh']):
                if not base<=z<base+len(data):assert state['nh'].get(z)==before['nh'].get(z)
            for k in ('sh','sr','out','roots'):assert state[k]==before[k]
            for r in range(len(state['nat'])):
                if r not in (2601,2602,2603,2604,2700,2701):assert state['nat'][r]==before['nat'][r]
            assert state['nat'][100:107]==before['nat'][100:107]
            assert peak<=bound
            coverage[name].update(pcs);charged+=steps
            cases.append(dict(name=name,q=q,base=base,steps=steps,maximumWord=peak,
                              scope='small generic continuous template printer and runtime-q patch'))
    assert coverage[name]==set(range(len(code)))
controls=[]
def minimal(base,q):
    s=dict(pc=0,nat=[0]*2715,nh={},sh={},sr={},out={},roots=[])
    s['nat'][2599]=q;s['nat'][2600]=base;return s
def reject(name,state,bound,budget=1000000,program='seedShape'):
    try:execute(PROGRAMS[program],state,bound,budget,4)
    except (AssertionError,KeyError):controls.append(name);return
    raise AssertionError('negative control accepted: '+name)
shape=next(s for s in SPECS if s['name']=='seedShape')
reject('runtime q initial word guard',minimal(0,10001),10000)
reject('final charged halt budget',minimal(7,3),10000,budget=shape['steps']-1)
reject('extra patch-cursor word beyond printed template extent',minimal(10000-len(shape['data']),1),10000)
reject('code PC word guard from valid initial state',minimal(0,0),30)
reject('fixed literal value word guard from valid initial state',minimal(0,1),10000,program='largeFields')
result=dict(status='PASS',exactCases=len(cases),chargedSteps=charged,cases=cases,
            negativeControls=controls,coveredPCs={k:sorted(v) for k,v in coverage.items()},
            scope='One continuous exported fixed program per small generic template, independent of runtime q. Actual fixed seed handled symbolically by Lean fixed_execution. No giant seed materialization, opcode interpreter, residual child, global runtime or unconditional uniform DFT claim.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [Path(__file__),PACKET/'programs.json',PACKET/'spec.json',ROOT/'verification/ExportFixedNetworkLiteralDecoderBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'continuous exact cases,',charged,'charged instructions,',len(controls),'negative controls')
