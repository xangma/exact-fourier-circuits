"""Exact exported RAM copy tests; selected caller and empty-startup scopes explicit.

No floating arithmetic, callback decoder or interphase host writes. The selected
fixtures supply ordinary physical source/CRT metadata, never P/r/Q or copy headers.
The empty-startup fixture executes the literal935 + charged headers + gather49.
"""
from pathlib import Path
from fractions import Fraction as F
import copy, hashlib, json
from uniform_seed_cyclotomic_engine import Poly, scalar, execute

ROOT = Path(__file__).resolve().parents[1]
P = ROOT / 'logs/uniform-bytecode/tensor-fiber-copy'
programs = json.loads((P / 'programs.json').read_text())
specs = json.loads((P / 'spec.json').read_text())
assert [len(programs[k]) for k in ['copy', 'gather', 'scatter', 'roundTrip', 'startupGather']] == [12,49,49,99,993]
for k in ['copy','gather','scatter','roundTrip']:
    assert not any(i[0] in ('root','input','output','fmul','fadd','fsub','fdiv') for i in programs[k])


def fresh(B=10**9, D=4):
    return dict(pc=0,nat=[(17*i+13)%7000 for i in range(1940)],
                nh={13:77,B-7:31},sh={B-11:scalar(D,-2,3,True)},
                sr={i:scalar(D,F(i-5,3),F(11-i,7),i%2==0) for i in range(102)},
                out={3:scalar(D,7,-2)[0]},roots=[4,12])


def frame(before, after, nat_writes, heap_writes):
    for k in ['nh','out','roots']: assert before[k] == after[k], k
    assert all(before['nat'][i] == after['nat'][i] for i in range(len(before['nat'])) if i not in nat_writes)
    assert all(before['sr'][i] == after['sr'][i] for i in before['sr'] if i != 100)
    assert all(before['sh'].get(i) == after['sh'].get(i) for i in set(before['sh'])|set(after['sh']) if i not in heap_writes)


cases, coverage, charged = [], {k:set() for k in ['copy','gather','scatter','roundTrip','startupGather']}, 0
for m,p,q in [(0,1,1),(1,1,1),(3,1,7),(5,7,1),(4,3,5),(3,0,1)]:
    B,a,d = 10**9,100,1000
    s=fresh(B);s['nat'][1900:1905]=[m,a,d,p,q]
    for j in range(m): s['sh'][a+j*p]=scalar(4,F(j-2,7),F(5-j,3),j%2==0)
    for j in range(m): s['sh'][d+j*q]=scalar(4,-123,37,True)
    before=copy.deepcopy(s);t,pcs,peak=execute(programs['copy'],s,B,100000,4)
    assert t == 9*m+4
    assert all(s['sh'][d+j*q] == before['sh'][a+j*p] for j in range(m))
    frame(before,s,set(range(1905,1909)),{d+j*q for j in range(m)})
    coverage['copy'].update(pcs);charged+=t
    cases.append(dict(scope='generic literal12',m=m,p=p,q=q,steps=t,maximumWord=peak))


def selected_state(spec, axis, j, mode):
    B=(spec['n']+2)**19
    s=fresh(B);ell,L,M=spec['ell'],spec['L'],spec['M'];a,d=20000,40000
    # Actual selected-radix values from the fresh Lean export; only original
    # caller metadata/source are installed. All computed/helper headers are dirty.
    s['nat'][100:107]=[97,spec['n'],ell,L,spec['D'],M,6*ell+5+2*L]
    for k,r in enumerate(spec['radices']):
        cof=L//r;inv=pow(cof,-1,r) if r>1 else 0
        for f,v in enumerate([r,cof,inv,cof*inv]): s['nh'][M+ell+4*k+f]=v
    s['nat'][1910:1914]=[axis,j,a,d]
    for z in range(L): s['sh'][a+z]=scalar(4,F(z-7,5),F(13-z,9),z%3==0)
    r=spec['radices'][axis]
    for z in range(r): s['sh'][d+z]=scalar(4,F(5-z,11),0 if z%2 else F(z+1,13),z%2==1)
    return s,B,a,d


for spec in specs:
    for ax in spec['axisSpecs']:
        axis,r,p,q=ax['axis'],ax['r'],ax['P'],ax['Q']
        assert p*r*q == spec['L'] and sorted(z for row in ax['positions'] for z in row)==list(range(spec['L']))
        fibers=sorted({0,p*q-1,(p*q)//2})
        for j in fibers:
            positions=ax['positions'][j]
            assert positions == [j%p+p*(t+r*(j//p)) for t in range(r)]
            for mode in ['gather','scatter','roundTrip']:
                s,B,a,d=selected_state(spec,axis,j,mode);before=copy.deepcopy(s)
                t,pcs,peak=execute(programs[mode],s,B,100000,4)
                one=9*r+7*axis+35
                assert t == (2*one+1 if mode=='roundTrip' else one)
                writes={d+z for z in range(r)} if mode=='gather' else {a+z for z in positions}
                if mode=='gather':
                    assert all(s['sh'][d+t] == before['sh'][a+z] for t,z in enumerate(positions))
                elif mode=='scatter':
                    assert all(s['sh'][a+z] == before['sh'][d+t] for t,z in enumerate(positions))
                else:
                    assert all(s['sh'][a+z] == before['sh'][a+z] for z in range(spec['L']))
                    assert all(s['sh'][d+t] == before['sh'][a+z] for t,z in enumerate(positions))
                    writes={d+z for z in range(r)} | {a+z for z in positions}
                frame(before,s,set(range(70,74))|{81}|set(range(89,94))|{99}|set(range(1900,1909))|set(range(1915,1930)),writes)
                assert s['nat'][70:74] == [p,r,q,j] and s['nat'][99] == positions[0]
                coverage[mode].update(pcs);charged+=t
                cases.append(dict(scope='actual selected-radix physical caller',n=spec['n'],axis=axis,fiber=j,radix=r,mode=mode,steps=t,maximumWord=peak))

# Native padded/chirped source and sole canonical master root arise from the
# actual empty935 startup, not a ready bank or a host-written interphase state.
for re,im in [(0,0),(1,2),(-2,3)]:
    D,B=128,3**19;value=scalar(D,re,im,True)[0]
    s=dict(pc=0,nat=[0]*1940,nh={},sh={},sr={},out={},roots=[])
    t,pcs,peak=execute(programs['startupGather'],s,B,100000,D,1,[value])
    assert s['roots']==[D] and s['nat'][1912]==9 and s['nat'][1913]==100000
    assert s['sh'][100000] == s['sh'][9] and s['sh'][100001] == s['sh'][10]
    assert s['sh'][100000] == (value,True) and s['sh'][100001] == scalar(D,0,0,False)
    coverage['startupGather'].update(pcs);charged+=t
    cases.append(dict(scope='actual empty935 + charged8 headers + gather49 + halt',n=1,input=[re,im],steps=t,maximumWord=peak))

controls=[]
def reject(name, code, s, B=10**9, budget=100000):
    try: execute(code,s,B,budget,4)
    except (AssertionError,KeyError): controls.append(name);return
    raise AssertionError('negative control accepted: '+name)
s=fresh();s['nat'][1900:1905]=[1,111,1000,1,1];reject('missing scalar source',programs['copy'],s)
s,B,a,d=selected_state(specs[-1],1,0,'gather');del s['nh'][specs[-1]['M']+specs[-1]['ell']];reject('missing actual prefix radix',programs['gather'],s,B)
s,B,a,d=selected_state(specs[-1],1,0,'gather');del s['nh'][specs[-1]['M']+specs[-1]['ell']+4];reject('missing actual selected radix',programs['gather'],s,B)
s,B,a,d=selected_state(specs[-1],1,0,'gather');s['nh'][specs[-1]['M']+specs[-1]['ell']+4]=0;reject('zero selected divisor',programs['gather'],s,B)
s,B,a,d=selected_state(specs[-1],1,0,'gather');s['nat'][1913]=B+1;reject('ambient word guard',programs['gather'],s,B)
s,B,a,d=selected_state(specs[-1],1,0,'gather');reject('charged step budget',programs['gather'],s,B,budget=10)
for k in ['copy','gather','scatter','roundTrip']:
    assert coverage[k] == set(range(len(programs[k]))), (k,sorted(set(range(len(programs[k])))-coverage[k]))
result=dict(status='PASS',exactCases=len(cases),chargedSteps=charged,cases=cases,negativeControls=controls,
            coveredPCs={k:sorted(v) for k,v in coverage.items()},
            scope='Full exact flagged copy on supplied ordinary physical selected metadata/source; three continuous empty935 startup/native-operand gathers. No all-fiber outer driver or global DFT claim.',
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),P/'programs.json',P/'spec.json',ROOT/'verification/ExportTensorFiberCopyBytecode.lean']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(cases),'exact cases',charged,'charged instructions;',len(controls),'negative controls')
