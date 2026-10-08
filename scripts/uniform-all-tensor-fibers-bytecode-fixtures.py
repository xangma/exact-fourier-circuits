"""Exact literal55 all-fiber gather/scatter and inverse checks.

Selected-caller cases use original protected metadata and a present ordinary
Scalar array, with dirty computed headers. Empty-startup cases execute the actual
935 instructions plus charged headers and the whole gather, without host phase
writes. Round trips reset the bank pointer with one charged instruction.
"""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute

ROOT = Path(__file__).resolve().parents[1]
P = ROOT / 'logs/uniform-bytecode/all-tensor-fibers'
programs = json.loads((P / 'programs.json').read_text())
specs = json.loads((P / 'spec.json').read_text())
assert [len(programs[k]) for k in ['gather', 'scatter', 'roundTrip', 'startupGather']] == [55,55,112,999]
for k in ['gather', 'scatter', 'roundTrip']:
    assert not any(i[0] in ('root','input','output','fmul','fadd','fsub','fdiv') for i in programs[k])


def fresh(B, D=4):
    return dict(pc=0,nat=[(17*i+13)%7000 for i in range(1960)],
                nh={B-7:31},sh={B-11:scalar(D,-2,3,True)},
                sr={i:scalar(D,F(i-5,3),F(11-i,7),i%2==0) for i in range(102)},
                out={3:scalar(D,7,-2)[0]},roots=[4,12])


def selected_state(spec, axis):
    B=(spec['n']+2)**19
    s=fresh(B);ell,L,M=spec['ell'],spec['L'],spec['M'];a,d=20000,40000
    s['nat'][100:107]=[spec['nextPrime'],spec['n'],ell,L,spec['D'],M,spec['amount']]
    for z in range(spec['amount']): s['nh'][M+z]=0
    for j,v in enumerate(spec['primes']): s['nh'][M+j]=v
    for j,row in enumerate(spec['crt']):
        assert row[0] == spec['radices'][j]
        for f,v in enumerate(row): s['nh'][M+ell+4*j+f]=v
    for j,v in enumerate(spec['alpha']): s['nh'][M+spec['alphaBase']+j]=v
    for j,v in enumerate(spec['beta']): s['nh'][M+spec['betaBase']+j]=v
    s['nat'][1910]=axis;s['nat'][1912]=a;s['nat'][1913]=d
    # Fiber/P/r/Q/decoder/copy headers stay dirty; only these original inputs
    # and the actual exported protected metadata are supplied by the caller.
    for z in range(L):
        s['sh'][a+z]=scalar(4,0 if z%7==0 else F(z-7,5),0 if z%7==0 else F(13-z,9),z%3==0)
        s['sh'][d+z]=scalar(4,0 if z%5==0 else F(5-z,11),0 if z%5==0 else F(z+1,13),z%2==1)
    return s,B,a,d


def frame(before, after, code, heap_writes):
    nat_writes={i[1] for i in code if i[0] in ('lit','add','sub','mul','div','mod','getnat','length')}
    for k in ['nh','out','roots']: assert before[k] == after[k], k
    assert all(before['nat'][i] == after['nat'][i] for i in range(len(before['nat'])) if i not in nat_writes)
    assert before['nat'][100:107] == after['nat'][100:107]
    assert before['nat'][1910] == after['nat'][1910] and before['nat'][1912] == after['nat'][1912]
    assert all(before['sr'][i] == after['sr'][i] for i in before['sr'] if i != 100)
    assert all(before['sh'].get(i) == after['sh'].get(i) for i in set(before['sh'])|set(after['sh']) if i not in heap_writes)


cases, coverage, charged = [], {k:set() for k in programs}, 0
for spec in specs:
    L=spec['L']
    for ax in spec['axisSpecs']:
        axis,r,p,q=ax['axis'],ax['r'],ax['P'],ax['Q']
        native=[z for row in ax['positions'] for z in row]
        # Independent formula and exhaustive inverse, checked against fresh
        # Lean finite coordinates; neither is used to execute the bytecode.
        formula=[j%p+p*(t+r*(j//p)) for j in range(p*q) for t in range(r)]
        assert native == formula and sorted(native) == list(range(L))
        inverse=[None]*L
        for z,v in enumerate(native): inverse[v]=z
        assert all(native[inverse[z]] == z and inverse[native[z]] == z for z in range(L))
        cost=p*q*(9*r+27)+7*axis+14
        assert cost <= 36*L+7*axis+14
        for mode in ['gather','scatter','roundTrip']:
            s,B,a,d=selected_state(spec,axis);before=copy.deepcopy(s)
            t,pcs,peak=execute(programs[mode],s,B,1000000,4)
            assert t == (2*cost+2 if mode=='roundTrip' else cost)
            if mode=='gather':
                assert all(s['sh'][d+z] == before['sh'][a+native[z]] for z in range(L))
                writes=set(range(d,d+L))
            elif mode=='scatter':
                assert all(s['sh'][a+z] == before['sh'][d+inverse[z]] for z in range(L))
                writes=set(range(a,a+L))
            else:
                assert all(s['sh'][a+z] == before['sh'][a+z] for z in range(L))
                assert all(s['sh'][d+z] == before['sh'][a+native[z]] for z in range(L))
                writes=set(range(a,a+L))|set(range(d,d+L))
            frame(before,s,programs[mode],writes)
            assert s['nat'][1911] == p*q and s['nat'][1913] == d+L
            assert s['nat'][70:73] == [p,r,q] and s['nat'][1952] == p*q
            coverage[mode].update(pcs);charged+=t
            cases.append(dict(scope='actual selected-radix original metadata/source caller',n=spec['n'],axis=axis,radix=r,fibers=p*q,mode=mode,steps=t,maximumWord=peak))

# Exact initial-state n=1: full935 creates metadata, chirps, native padded input
# and the one canonical root. The remaining instructions install only axis/A/D
# headers and execute whole-bank gather. No host writes between phases.
for re,im in [(0,0),(1,2),(-2,3)]:
    D,B=128,3**19;value=scalar(D,re,im,True)[0]
    s=dict(pc=0,nat=[0]*1960,nh={},sh={},sr={},out={},roots=[])
    t,pcs,peak=execute(programs['startupGather'],s,B,1000000,D,1,[value])
    assert s['roots'] == [D] and s['nat'][1912] == 9 and s['nat'][1913] == 100002
    assert s['sh'][100000] == s['sh'][9] == (value,True)
    assert s['sh'][100001] == s['sh'][10] == scalar(D,0,0,False)
    coverage['startupGather'].update(pcs);charged+=t
    cases.append(dict(scope='actual empty935 + charged8 headers + whole gather55 + halt',n=1,input=[re,im],steps=t,maximumWord=peak))

controls=[]
def reject(name, s, B, budget=1000000):
    try: execute(programs['gather'],s,B,budget,4)
    except (AssertionError,KeyError): controls.append(name);return
    raise AssertionError('negative control accepted: '+name)
s,B,a,d=selected_state(specs[-1],1);del s['sh'][a+specs[-1]['L']-1];reject('missing later-fiber scalar source',s,B)
s,B,a,d=selected_state(specs[-1],1);del s['nh'][specs[-1]['M']+specs[-1]['ell']];reject('missing actual prefix radix',s,B)
s,B,a,d=selected_state(specs[-1],1);del s['nh'][specs[-1]['M']+specs[-1]['ell']+4];reject('missing actual selected radix',s,B)
s,B,a,d=selected_state(specs[-1],1);s['nh'][specs[-1]['M']+specs[-1]['ell']+4]=0;reject('zero selected divisor',s,B)
s,B,a,d=selected_state(specs[-1],1);s['nat'][1913]=B+1;reject('ambient word guard',s,B)
s,B,a,d=selected_state(specs[-1],1);reject('charged step budget',s,B,budget=10)
for k in ['gather','scatter','roundTrip']:
    assert coverage[k] == set(range(len(programs[k]))), (k,sorted(set(range(len(programs[k])))-coverage[k]))
result=dict(status='PASS',exactCases=len(cases),chargedSteps=charged,cases=cases,negativeControls=controls,
            coveredPCs={k:sorted(v) for k,v in coverage.items()},
            scope='Actual whole physical all-fiber permutation/inverse from selected original metadata and ordinary Scalar source, exact tags/frames; three empty935 startup gathers. Continuous roundTrip112 diagnostic uses one charged pointer reset. No global scheduler or DFT claim.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),P/'programs.json',P/'spec.json',ROOT/'verification/ExportAllTensorFibersCopyBytecode.lean']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'exact cases',charged,'charged instructions;',len(controls),'negative controls')
