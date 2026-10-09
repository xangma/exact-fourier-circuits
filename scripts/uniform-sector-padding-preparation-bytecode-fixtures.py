"""Actual sector production/padding bytecode; exact Q[eta]/Phi_D tagged data.
Small-W specializations exercise physical padding. Fixed W=2^71 is exercised
only for the finite Nat-only producers, never with an astronomical data bank.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction
import hashlib,json,random,sys
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'logs/uniform-bytecode/sector-padding-preparation'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
raw=json.loads((BASE/'sector-bytecode/programs.json').read_text())
specs=json.loads((BASE/'sector-bytecode/specs.json').read_text())
programs={p['W']:p for p in raw['specializations']}
S,A,E,D=1000,40000,10000,700
B=1000000

def state(spec,W,order,seed,mode='continuous205',bound=B):
    rng=random.Random(seed)
    ell=len(spec['widths']);L=spec['volume'];states=spec['sectors']
    s=dict(pc=0,nat=[rng.randrange(100) for _ in range(4500)],nh={7:19,bound-1:5},
      sh={0:scalar(order,3,7),bound-1:scalar(order,7,-11,True)},
      sr={q:scalar(order,Fraction(q-3,7),Fraction(13-q,11),q%2) for q in range(130)},
      out={0:scalar(order,19,-17)[0]},roots=[4,1])
    source=[scalar(order,Fraction(7*j-11,13),Fraction(5*j+3,17),(j+seed)%2) for j in range(L)]
    for j,v in enumerate(source):s['sh'][S+j]=v
    if mode not in ('directory33','producer158'):
      for j in range(W*L):s['sh'][A+j]=scalar(order,Fraction(j+1,19),Fraction(1-j,23),True)
    for j,ws in enumerate(spec['widths']):
      widths=100+100*j;perm=300+100*j
      for k,v in enumerate(ws):s['nh'][widths+k]=v
      for k in range(sum(ws)):s['nh'][perm+k]=k
      for k,v in enumerate([len(ws),widths,sum(ws),perm]):s['nh'][20+4*j+k]=v
    for reg,value in {102:max(ell-1,0),3201:20,3202:500,3213:600,3214:650,3215:D,
       4441:E,4442:A,4472:S,4473:E}.items():s['nat'][reg]=value
    if mode in ('directory33','padding44','padding37'):
      for i,(start,width,q) in enumerate(states):
        for f,v in enumerate([start,width,q]):s['nh'][D+3*i+f]=v
        for f,v in enumerate([q,width,A+W*start,start,W*width]):s['nh'][E+5*i+f]=v
      s['nat'][464]=len(states)
    return s,source

cases=[];covered={name:set() for name in ['directory33','producer158','padding25','padding37','padding44','continuous205']}

def common(old,s,order,start,length):
    assert s['out']==old['out'] and s['roots']==old['roots']
    assert s['nat'][100:107]==old['nat'][100:107]
    assert all(s['sh'].get(q)==v for q,v in old['sh'].items() if not(start<=q<start+length))
    assert s['sh'][0]==old['sh'][0]

def table(s,spec,W):
    for i,(start,width,q) in enumerate(spec['sectors']):
      assert [s['nh'][E+5*i+j] for j in range(5)]==[q,width,A+W*start,start,W*width]
    assert s['nat'][464]==len(spec['sectors'])

def padded(s,spec,W,source,order):
    zero=scalar(order)
    for start,width,q in spec['sectors']:
      assert width==2**q
      base=A+W*start
      for j in range(W*width):assert s['sh'][base+j]==(source[start+j] if j<width else zero)
    assert all(s['sh'][S+j]==v for j,v in enumerate(source))

for W,p in programs.items():
  assert {name:len(p[name]) for name in covered}==dict(directory33=33,producer158=158,padding25=25,padding37=37,padding44=44,continuous205=205)
  for sid,spec in enumerate(specs):
    ell=len(spec['widths']);L=spec['volume'];M=len(spec['sectors']);tree=spec['treeCost']
    assert sum(w for _,w,_ in spec['sectors'])==L
    assert all(spec['sectors'][i][0]+spec['sectors'][i][1]==spec['sectors'][i+1][0] for i in range(M-1))
    for order in [4,8,12]:
      for seed in range(2):
        for name in ['directory33','padding44']+(['producer158','continuous205'] if ell else []):
          s,source=state(spec,W,order,seed,name);old=deepcopy(s)
          expected={'directory33':24*M+10,'producer158':tree+43*ell+24*M+42,
              'padding44':(5*W+2)*L+30*M+5,'continuous205':tree+43*ell+54*M+(5*W+2)*L+50}[name]
          ticks,pcs,peak=execute(p[name],s,B,expected,order)
          assert ticks==expected and s['pc']==len(p[name])-1 and peak<=B
          covered[name].update(pcs)
          if name in ('directory33','producer158'):table(s,spec,W);assert s['sh']==old['sh'] and s['sr']==old['sr']
          else:padded(s,spec,W,source,order);common(old,s,order,A,W*L)
          if name in ('padding44',):assert s['nh']==old['nh']
          if name=='continuous205':
            table(s,spec,W)
            assert all(s['nh'].get(q)==v for q,v in old['nh'].items() if q<500)
          cases.append(dict(program=name,W=W,spec=sid,D=order,seed=seed,ticks=ticks))
        # Each generated sector read by the literal37 caller.
        for i,(start,width,q) in enumerate(spec['sectors']):
          if i not in (0,M-1):continue
          s,source=state(spec,W,order,seed,'padding37');s['nat'][4474]=i;old=deepcopy(s)
          expected=5*W*width+2*width+27
          ticks,pcs,_=execute(p['padding37'],s,B,expected,order)
          assert ticks==expected and s['pc']==36 and s['nh']==old['nh']
          zero=scalar(order)
          assert all(s['sh'][A+W*start+j]==(source[start+j] if j<width else zero) for j in range(W*width))
          common(old,s,order,A+W*start,W*width);covered['padding37'].update(pcs)
          cases.append(dict(program='padding37',W=W,spec=sid,sector=i,D=order,seed=seed,ticks=ticks))
  # Standalone25 includes empty source, dirty destination and unitW.
  for width in [0,1,2,3,7]:
    for order in [4,8,12]:
      spec=dict(widths=[],volume=width,sectors=[],treeCost=0)
      s,source=state(spec,W,order,3,'padding25');s['nat'][4460]=width;s['nat'][4461]=S;s['nat'][4462]=A;old=deepcopy(s)
      expected=5*W*width+2*width+15
      ticks,pcs,_=execute(p['padding25'],s,B,expected,order)
      assert ticks==expected and s['pc']==24 and s['nh']==old['nh']
      zero=scalar(order);assert all(s['sh'][A+j]==(source[j] if j<width else zero) for j in range(W*width))
      common(old,s,order,A,W*width);covered['padding25'].update(pcs)
      cases.append(dict(program='padding25',W=W,width=width,D=order,ticks=ticks))
# The actual fixedW Nat producers, including huge printed buffer addresses.
W=raw['fixedW'];fixedBound=W*1000+100000
for sid,spec in enumerate(specs):
  ell=len(spec['widths']);M=len(spec['sectors']);tree=spec['treeCost']
  for name,key in [('directory33','fixedDirectory33')]+([('producer158','fixedProducer158')] if ell else []):
    s,_=state(spec,W,4,7,name,fixedBound);old=deepcopy(s)
    expected=24*M+10 if name=='directory33' else tree+43*ell+24*M+42
    ticks,pcs,_=execute(raw[key],s,fixedBound,expected,4)
    assert ticks==expected and s['sh']==old['sh'];table(s,spec,W)
    cases.append(dict(program='fixed-'+name,W=W,spec=sid,D=4,ticks=ticks))
controls=[]

def reject(name,mutate,mode='continuous205',budget=None):
    spec=specs[-1];s,_=state(spec,3,12,1,mode);mutate(s)
    try:execute(programs[3][mode],s,B,10**7 if budget is None else budget,12)
    except (AssertionError,KeyError):controls.append(name)
    else:raise AssertionError(name+' accepted')
reject('missing-original-width-cell',lambda s:s['nh'].pop(100))
reject('missing-axis-row-cell',lambda s:s['nh'].pop(21))
reject('missing-tagged-source',lambda s:s['sh'].pop(S))
reject('missing-produced-sector-width',lambda s:s['nh'].pop(E+1),mode='padding44')
reject('word-bound-source',lambda s:s['nat'].__setitem__(4472,B+1))
reject('charged-budget',lambda s:None,budget=1)
for name,pcs in covered.items():assert pcs==set(range(len(programs[1][name]))),(name,sorted(set(range(len(programs[1][name])))-pcs))
result=dict(status='PASS',exactCases=len(cases),negativeControls=controls,coveredPCs={k:sorted(v) for k,v in covered.items()},
 contracts='Genuine Lean-exported valid Axis sectors and ordinary physical four-word rows/width cells; arbitrary exact tagged Source, true disjoint layout. These are generic physical-axis inputs, not selected all-axis FFT startup witnesses. Padding uses W1,2,3,5 specializations; fixed W=2^71 exercised only for finite Nat producers.',
 model='Exact Q[eta]/Phi_D D4,8,12; no floating point; copied tags checked exactly.',
 sourceHashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [BASE/'sector-bytecode/programs.json',BASE/'sector-bytecode/specs.json',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']},cases=cases)
(BASE/'sector-bytecode/fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cases','coveredPCs')}))
