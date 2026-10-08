"""Exact physical header dispatch and continuous fixed-template/q printer traces.
Small generic tables only: this does not execute circuit children or the huge seed.
"""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute
ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'logs/uniform-bytecode/fixed-network-opcode'
PROGRAMS = json.loads((PACKET/'programs.json').read_text())
SPECS = json.loads((PACKET/'spec.json').read_text())

def fresh(base,q,bound,D):
    s=dict(pc=0,nat=[(19*i+23)%97 for i in range(2891)],
           nh={base-1:13,base+500:31,bound-1:47},
           sh={base:scalar(D,F(2,3),F(-4,7),True),bound-2:scalar(D,0,0,False)},
           sr={0:scalar(D,3,-7,True),2850:scalar(D,-2,9,False)},
           out={1:scalar(D,-1,7)[0]},roots=[4,D])
    s['nat'][2599]=q;s['nat'][2600]=base
    return s

def reference(records,q):
    data=[];pointers=[]
    for r in records:
        h=list(r['header']);h[1]=q;op,_,width,_,source,_,dim,_=h
        size=(dim*width if op==0 else 0 if op==1 else source if op==2
              else dim*(width+1) if op==3 else 4*dim if op==4 else 0)
        assert 0<=op<7 and size==len(r['body'])==r['bodyLength']
        assert r['headSteps']==32+op+(op==3)
        pointers.append(len(data));data+=h+r['body']
    return data,pointers

cases=[];coverage={};total=0
for spec in SPECS:
    name=spec['name'];code=PROGRAMS[name];records=spec['records']
    assert len(code)==spec['codeSize']==spec['printerSteps']+61
    assert spec['printerSteps']==3*len(spec['data'])+3*len(records)+7
    assert spec['steps']==spec['printerSteps']+4+2+sum(r['headSteps']+3 for r in records)+1
    coverage[name]=set()
    for base in (7,500,10000):
        for q in (0,1,3,2**71):
            for D in (4,12,32):
                bound=max(base+1000,len(code)+10,max(spec['data'],default=0)+10,q+10)
                state=fresh(base,q,bound,D);before=copy.deepcopy(state)
                data,_=reference(records,q)
                steps,pcs,peak=execute(code,state,bound,1000000,D)
                assert steps==spec['steps'] and state['nat'][2850]==base+len(data)
                assert state['nat'][2880]==base+len(data)
                assert [state['nh'][base+j] for j in range(len(data))]==data
                for z in set(state['nh'])|set(before['nh']):
                    if not base<=z<base+len(data):assert state['nh'].get(z)==before['nh'].get(z)
                for k in ('sh','sr','out','roots'):assert state[k]==before[k]
                for r in range(len(state['nat'])):
                    if not (2850<=r<2882) and r not in (2601,2602,2603,2604,2700,2701):
                        assert state['nat'][r]==before['nat'][r]
                assert state['nat'][100:107]==before['nat'][100:107]
                assert peak<=bound
                coverage[name].update(pcs);total+=steps
                cases.append(dict(program=name,base=base,q=q,rootOrder=D,steps=steps,maximumWord=peak,
                                  scope='continuous unprinted table -> runtime q patch -> charged cursor setup -> actual opcode loop'))
    if name=='allOpcodes':
        guard=spec['loopBase']+34
        assert coverage[name]==set(range(len(code)))-{guard}

# Standalone header and traversal components also start with arbitrary dirty registers.
components=[];headCoverage=set();loopCoverage=set()
for spec in SPECS:
    for base in (7,500):
        q=2**19;D=12;bound=max(base+1000,max(spec['data'],default=0)+10,q+10)
        data,ptrs=reference(spec['records'],q)
        s=fresh(base,q,bound,D);s['nh'].update({base+j:v for j,v in enumerate(data)})
        s['nat'][2850]=base;s['nat'][2880]=base+len(data);before=copy.deepcopy(s)
        steps,pcs,_=execute(PROGRAMS['loop'],s,bound,1000000,D)
        assert steps==2+sum(r['headSteps']+3 for r in spec['records'])
        assert s['nat'][2850]==base+len(data) and s['nh']==before['nh']
        for k in ('sh','sr','out','roots'):assert s[k]==before[k]
        loopCoverage.update(pcs);components.append(dict(kind='physical loop component',name=spec['name'],steps=steps))
        for r,offset in zip(spec['records'],ptrs):
            t=copy.deepcopy(before);t['nat'][2850]=base+offset;old=copy.deepcopy(t)
            count,pcset,_=execute(PROGRAMS['head'],t,bound,1000000,D)
            assert count==r['headSteps']
            expected=list(r['header']);expected[1]=q
            assert t['nat'][2851:2859]==expected
            assert t['nat'][2864]==r['bodyLength'] and t['nat'][2865]==base+offset+8+len(r['body'])
            assert t['nat'][2850]==base+offset and t['nh']==old['nh']
            for k in ('sh','sr','out','roots'):assert t[k]==old[k]
            for j in range(len(t['nat'])):
                if j<2850 or 2877<=j:assert t['nat'][j]==old['nat'][j]
            headCoverage.update(pcset);components.append(dict(kind='physical header component',opcode=expected[0],steps=count))
assert headCoverage==set(range(52))-{33}
assert loopCoverage==set(range(56))-{34}

controls=[]
def minimal(base=0,q=0):
    s=dict(pc=0,nat=[0]*2891,nh={},sh={},sr={},out={},roots=[])
    s['nat'][2599]=q;s['nat'][2600]=base;s['nat'][2850]=base;return s
def reject(label,code,s,bound,budget=1000000):
    try:execute(code,s,bound,budget,4)
    except (AssertionError,KeyError) as error:
        controls.append(dict(name=label,pcAfterFailure=s['pc'],reason=str(error)));return
    raise AssertionError('negative control accepted: '+label)
s=minimal();s['nh'].update(enumerate([7,0,0,0,0,0,0,0]));reject('unsupported opcode7 actual zero-divisor guard',PROGRAMS['head'],s,100)
assert s['pc']==34
s=minimal();s['nh'].update(enumerate([3,0,100,0,0,0,0,0]));reject('translation width+1 intermediate guard even dimension0',PROGRAMS['head'],s,100)
s=minimal();reject('missing physical first header',PROGRAMS['head'],s,100)
s=minimal();s['nh'].update(enumerate([1,0,0,0,0,0,0]));reject('missing physical scalar-code field',PROGRAMS['head'],s,100)
reject('runtime q initial word guard',PROGRAMS['allOpcodes'],minimal(q=10001),10000)
allSpec=next(z for z in SPECS if z['name']=='allOpcodes')
reject('last charged halt cannot be omitted',PROGRAMS['allOpcodes'],minimal(base=7,q=3),10000,allSpec['steps']-1)
reject('template extra cursor word beyond table extent',PROGRAMS['allOpcodes'],minimal(base=10000-len(allSpec['data']),q=1),10000)
reject('code PC word guard from bounded initial state',PROGRAMS['allOpcodes'],minimal(),30)
result=dict(status='PASS',exactCases=len(cases),componentCases=len(components),chargedContinuousSteps=total,
            cases=cases,components=components,negativeControls=controls,
            coveredPCs={k:sorted(v) for k,v in coverage.items()},headCoveredPCs=sorted(headCoverage),loopCoveredPCs=sorted(loopCoverage),
            scope='Small generic exact diagnostics with mixed dirty scalar flags and roots; no host writes between continuous caller phases. All opcode0..6 heads and guard7 tested. Actual fixed astronomical seed is a symbolic Lean theorem, not materialized. Circuit child execution/global uniform DFT remain open.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [Path(__file__),PACKET/'programs.json',PACKET/'spec.json',ROOT/'verification/ExportFixedNetworkOpcodeBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'continuous exact cases;',len(components),'physical component cases;',total,'charged continuous instructions;',len(controls),'negative controls')
