"""Real generated-sector movement adapters; exact copied tags and spectators.
Generic valid Lean sector partitions, not the complete selected FFT scheduler.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction
import hashlib,json,random,sys
ROOT=Path(__file__).resolve().parents[1];BASE=ROOT/'logs/uniform-bytecode/operational-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
programs=json.loads((BASE/'transpose-bytecode/programs.json').read_text())
specs=json.loads((ROOT/'logs/uniform-bytecode/sector-padding-preparation/sector-bytecode/specs.json').read_text())
X,A,Y,E=1000,40000,200000,10000;B=1000000

def make(spec,W,D,seed,mode,ordinal):
    rng=random.Random(seed);L=spec['volume'];states=spec['sectors']
    native=X if mode in ('forward34','child39','forward41') else Y
    s=dict(pc=0,nat=[rng.randrange(50) for _ in range(4600)],nh={3:17,B-1:7},
      sh={0:scalar(D,7,-3,True),B-1:scalar(D,-17,2,True)},
      sr={r:scalar(D,Fraction(r+1,13),Fraction(3-r,17),r%2) for r in range(140)},
      out={0:scalar(D,19,-11)[0]},roots=[4,1])
    original=[[scalar(D,Fraction(5*j-3*r-11,19),Fraction(3*j+r+7,23),(j+r+seed)%2) for j in range(L)] for r in range(W)]
    children={}
    for r in range(W):
      for j in range(L):s['sh'][X+r*L+j]=original[r][j];s['sh'][Y+r*L+j]=scalar(D,-111-j,77+r,True)
    for i,(start,width,q) in enumerate(states):
      assert width==2**q
      for field,value in enumerate([q,width,A+W*start,start,W*width]):s['nh'][E+5*i+field]=value
      children[i]=[[scalar(D,Fraction(7*t+2*r+seed+1,29),Fraction(r-5*t+11,31),(r+t+seed)%2) for t in range(width)] for r in range(W)]
      for r in range(W):
        for t in range(width):s['sh'][A+W*start+r*width+t]=children[i][r][t]
    for reg,value in {4530:L,4531:native,4532:E,4533:ordinal,4534:500000,4535:X,464:len(states)}.items():s['nat'][reg]=value
    return s,original,children

covered={name:set() for name in programs[0] if name!='W'};cases=[]
for p in programs:
 W=p['W']
 for sid,spec in enumerate(specs+[dict(volume=0,sectors=[])]):
  L=spec['volume'];states=spec['sectors'];M=len(states)
  for D in (4,8,12):
   for seed in range(2):
    for i,(start,width,q) in enumerate(states):
     if i not in (0,M-1):continue
     for mode in ('forward34','reverse34','child39','restoring51'):
      s,original,children=make(spec,W,D,seed,mode,i);old=deepcopy(s)
      expected=W*(7*width+12)+(22 if mode=='child39' else 17)
      if mode=='restoring51':expected=7*W*L+W*(7*width+12)+28
      ticks,pcs,peak=execute(p[mode],s,B,expected,D);covered[mode].update(pcs)
      assert ticks==expected and s['pc']==len(p[mode])-1 and peak<=B
      if mode in ('forward34','child39'):
       for r in range(W):
        for t in range(width):assert s['sh'][A+W*start+r*width+t]==original[r][start+t]
       written=lambda a:A+W*start<=a<A+W*(start+width)
      else:
       for r in range(W):
        for j in range(L):
         value=children[i][r][j-start] if start<=j<start+width else (original[r][j] if mode=='restoring51' else old['sh'][Y+r*L+j])
         assert s['sh'][Y+r*L+j]==value
       written=lambda a:Y<=a<Y+W*L if mode=='restoring51' else any(Y+r*L+start<=a<Y+r*L+start+width for r in range(W))
      assert all(s['sh'].get(a)==v for a,v in old['sh'].items() if not written(a))
      assert s['nh']==old['nh'] and s['out']==old['out'] and s['roots']==old['roots']
      assert all(s['sr'][r]==v for r,v in old['sr'].items() if r!=32)
      changed=set(range(147,154))|set(range(4550,4562))
      if mode=='child39':changed|=set(range(4120,4124));assert [s['nat'][j] for j in range(4120,4124)]==[q,A+W*start,width,500000]
      if mode=='restoring51':changed|=set(range(4563,4566))
      assert all(s['nat'][r]==v for r,v in enumerate(old['nat']) if r not in changed)
      cases.append(dict(program=mode,W=W,spec=sid,sector=i,D=D,seed=seed,ticks=ticks))
    for mode in ('forward41','reverse41'):
     if mode not in p:continue
     s,original,children=make(spec,W,D,seed,mode,0);old=deepcopy(s)
     expected=7*W*L+(12*W+20)*M+5
     ticks,pcs,peak=execute(p[mode],s,B,expected,D);covered[mode].update(pcs)
     assert ticks==expected and s['pc']==40
     for i,(start,width,q) in enumerate(states):
      for r in range(W):
       for t in range(width):
        address=A+W*start+r*width+t if mode=='forward41' else Y+r*L+start+t
        assert s['sh'][address]==(original[r][start+t] if mode=='forward41' else children[i][r][t])
     base=A if mode=='forward41' else Y
     assert all(s['sh'].get(a)==v for a,v in old['sh'].items() if not base<=a<base+W*L)
     assert s['nh']==old['nh'] and s['out']==old['out'] and s['roots']==old['roots']
     changed=set(range(147,154))|set(range(4550,4562))|{4533,4570,4571}
     assert all(s['nat'][r]==v for r,v in enumerate(old['nat']) if r not in changed)
     cases.append(dict(program=mode,W=W,spec=sid,D=D,seed=seed,ticks=ticks))
controls=[]

def reject(name,mutate,mode='child39',budget=None,modify_code=None):
    spec=specs[-1];i=len(spec['sectors'])-1;s,_,_=make(spec,3,12,1,mode,i);mutate(s)
    code=deepcopy(programs[2][mode])
    if modify_code:modify_code(code)
    try:execute(code,s,B,10000000 if budget is None else budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')
reject('missing-sector-exponent',lambda s:s['nh'].pop(E+5*s['nat'][4533]))
reject('missing-sector-width',lambda s:s['nh'].pop(E+5*s['nat'][4533]+1))
reject('missing-sector-buffer',lambda s:s['nh'].pop(E+5*s['nat'][4533]+2))
reject('missing-sector-start',lambda s:s['nh'].pop(E+5*s['nat'][4533]+3))
reject('missing-native-source',lambda s:s['sh'].pop(X+specs[-1]['sectors'][-1][0]))
reject('missing-child-source',lambda s:s['sh'].pop(A+3*specs[-1]['sectors'][-1][0]),mode='reverse34')
reject('missing-original-baseline',lambda s:s['sh'].pop(X),mode='restoring51')
reject('word-bound-header',lambda s:s['nat'].__setitem__(4531,B+1))
reject('charged-budget',lambda s:None,budget=1)
reject('mutated-fivecell-stride',lambda s:None,modify_code=lambda code:code.__setitem__(3,['lit',4553,999]))
for name,pcs in covered.items():assert pcs==set(range(len(programs[0][name]))),(name,sorted(set(range(len(programs[0][name])))-pcs))
result=dict(status='PASS',exactCases=len(cases),negativeControls=controls,coveredPCs={k:sorted(v) for k,v in covered.items()},
 contracts='Genuine Lean-exported generic sector partitions/physical fivecell records, actual count464 and present arbitrary tagged native/child banks under valid ordinary placement. W1,2,3,5 only. Forward39 derives the physical child ABI, not a child action. Reverse34 retains entry destination spectators; restoring51 actually copies the original full bank before overlay. Complete reverse41 covers every native coordinate from the full partition. Not full selected FFT/startup/recursive saving execution.',
 model='Exact Q[eta]/Phi_D D4,8,12, no floating point or division; exact tags and retained native spectators/banks.',
 sourceHashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),BASE/'transpose-bytecode/programs.json',ROOT/'logs/uniform-bytecode/sector-padding-preparation/sector-bytecode/specs.json',ROOT/'scripts/uniform_seed_cyclotomic_engine.py']},cases=cases)
(BASE/'transpose-bytecode/fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','coveredPCs')}))
