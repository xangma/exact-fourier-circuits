"""Exact charged Nat printer diagnostics against fresh Lean literal exports.

These use small generic descriptors, not the full fixed-seed metadata (whose
finite size is astronomical). No residual child or network action is executed.
"""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'logs/uniform-bytecode/fixed-network-schedule'
PROGRAMS = json.loads((PACKET / 'programs.json').read_text())
SPECS = json.loads((PACKET / 'spec.json').read_text())


def fresh(base, bound, salt):
    return dict(pc=0, nat=[(11*i+salt)%97 for i in range(2610)],
                nh={base-1:71, base:41, base+3:17, base+300:31, bound-1:29},
                sh={base:scalar(4,F(2,3),F(-3,7),True), bound-2:scalar(4,0,0,False)},
                sr={0:scalar(4,5,-7,True), 2601:scalar(4,0,0,False)},
                out={2:scalar(4,-3,2)[0]}, roots=[4,12])


cases, coverage, charged = [], {}, 0
for spec in SPECS:
    name, data = spec['name'], spec['data']
    code = PROGRAMS[name]
    assert len(code) == spec['steps'] == 3*len(data)+4
    assert spec['inputBaseRegister'] == 2600 and spec['scratchRegisters'] == [2601,2602,2603,2604]
    assert all(ins[0] in ('lit','putnat','add','halt') for ins in code)
    coverage[name] = set()
    for base, salt in [(7,0),(500,31),(10000,87)]:
        bound = max(base+500,len(code)+10,max(data,default=0)+10,1000)
        state=fresh(base,bound,salt)
        state['nat'][2600]=base
        before=copy.deepcopy(state)
        steps, pcs, peak=execute(code,state,bound,1000000,4)
        assert steps == spec['steps']
        assert state['nat'][2601] == base+len(data)
        assert [state['nh'][base+j] for j in range(len(data))] == data
        writes=set(range(base,base+len(data)))
        for z in set(state['nh'])|set(before['nh']):
            if z not in writes: assert state['nh'].get(z) == before['nh'].get(z)
        for k in ('sh','sr','out','roots'): assert state[k] == before[k], k
        for i in range(len(state['nat'])):
            if i not in (2601,2602,2603,2604): assert state['nat'][i] == before['nat'][i]
        assert state['nat'][100:107] == before['nat'][100:107]
        assert peak <= bound
        coverage[name].update(pcs);charged+=steps
        cases.append(dict(name=name,base=base,steps=steps,maximumWord=peak,
                          scope='small generic literal descriptor printer'))
    assert coverage[name] == set(range(len(code)))

# Independently decode the small eight-field records and check chronology,
# shared original-width basis bits and five-valued scalar codes.
for q in (0,1,3):
    data=next(s['data'] for s in SPECS if s['name']==f'q{q}')
    body_sizes=[0,4,6,0,0,3,0,0,8,8,0]
    pos=0;records=[]
    for size in body_sizes:
        header=data[pos:pos+8];body=data[pos+8:pos+8+size];pos+=8+size
        assert header[1] == q and header[2] == 3
        records.append((header,body))
    assert pos == len(data)
    assert [h[0] for h,_ in records] == [6,2,0,1,1,0,1,1,3,4,5]
    assert records[2][1] == [1,0,1,0,1,0] and records[5][1] == [1,1,0]
    assert [h[7] for h,_ in records if h[0]==1] == [0,1,3,4]
    assert records[2][0][5] == 0 and records[5][0][5] == 1
    assert records[-1][0][3:5] == [7,1]
assert [len(next(s['data'] for s in SPECS if s['name']==f'q{q}')) for q in (0,1,3)] == [117]*3

controls=[]
def reject(name, state, bound, budget=1000000, code_name="q1"):
    try: execute(PROGRAMS[code_name],state,bound,budget,4)
    except (AssertionError,KeyError): controls.append(name);return
    raise AssertionError('negative control accepted: '+name)
# Dirty headers are overwritten, but word/address/time preconditions matter.
s=fresh(100,10000,31);s['nat'][2600]=100;reject('charged runtime guard',s,10000,budget=20)
s=fresh(100,10000,31);s['nat'][2600]=10001;reject('initial pointer word guard',s,10000)
s=dict(pc=0,nat=[0]*2610,nh={},sh={},sr={},out={},roots=[])
reject('code PC word bound from valid initial state',s,30)
s=dict(pc=0,nat=[0]*2610,nh={},sh={},sr={},out={},roots=[]);s['nat'][2600]=390
reject('output extent intermediate word bound from valid initial state',s,400)
s=dict(pc=0,nat=[0]*2610,nh={},sh={},sr={},out={},roots=[])
reject('literal value word bound from valid initial state',s,1000,code_name='integerBounds')
result=dict(status='PASS',exactCases=len(cases),chargedSteps=charged,cases=cases,
            negativeControls=controls,coveredPCs={k:sorted(v) for k,v in coverage.items()},
            scope='Generic charged descriptor printer and exact full frames only. Actual fixed seed handled symbolically by Lean fixed_execution; no materialized seed, residual child execution, network runtime or unconditional uniform DFT claim.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [Path(__file__),PACKET/'programs.json',PACKET/'spec.json',ROOT/'verification/ExportFixedNetworkScheduleBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'generic exact printer cases,',charged,'charged instructions,',len(controls),'negative controls')
