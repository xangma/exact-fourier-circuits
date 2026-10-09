"""Exact Q[i] tests of tiny placements of the frozen terminal/spectator slices.
The low prefix is prepared by an independent dense C tensor oracle, not
claimed as RAM production. No giant W, actual commonProgram or PC evaluated.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
import json,sys
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/recursive-foundations/terminal'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,add,mul
PROGRAMS=json.loads((P/'programs.json').read_text());SLICES=json.loads((P/'slices.json').read_text())
CA=scalar(4,F(1,2),F(1,2));CB=scalar(4,F(1,2),F(-1,2));B=20000;WORK=7000;END=8000
WRITES={0,1,2,2800,2801,2802,2803,2804,2805,2806,2810,2811,2820,2821,2822,2823,2824,2825,5200,5201,5202,5203,5204,5205,5206,5207,5208,5209,5210,5211,5212,3301,4178,4179}
def relocated(code,base,ret):
 rows=deepcopy(code)
 for row in rows:
  if row[0]=='branch':row[3]+=base;row[4]+=base
  elif row[0]=='jump':row[1]+=base
  elif row[0]=='halt':row[:]=['jump',ret]
 return rows
for count in range(5):
 for child in (False,True):
  code=PROGRAMS[('child' if child else 'root')+str(count)];assert len(code)==(82 if child else 81)
  assert code[:3]==SLICES['loop'] and code[3]==['branch',2850,3301,80,4]
  setup=deepcopy(SLICES['setup']);setup[1][2]=count
  assert code[4:9]==setup and code[9]==['jump',10]
  assert code[10:79]==relocated(SLICES['spectator'],10,79)
  assert code[79]==['branch',4151,4153,80,81] and code[80]==['halt']
  if child:assert code[81]==['halt']
  assert all(row[0] not in ('root','input','output','putnat') for row in code)

@lru_cache(None)
def coefficients(n):
 out=[]
 for h in range(n+1):
  c=scalar(4,1)
  for j in range(n):c=mul(c,CB if j<h else CA)
  out.append(c)
 return tuple(out)
def dense(k,axes,values):
 selected=sum(1<<j for j in axes);outside=(2**k-1)^selected;coeff=coefficients(len(axes));out=[]
 for row in range(2**k):
  total=scalar(4)
  for col in range(2**k):
   diff=row^col
   if diff&outside:continue
   total=add(total,mul(coeff[(diff&selected).bit_count()],values[col]))
  out.append(total)
 return tuple(out)
@lru_cache(None)
def original(k,w,family):
 salt=31+3*k
 return tuple(scalar(4,F(w-z+salt,11),F(z+3*w,13)) if family=='prepared' else scalar(4,F(3*z-7*w+salt,11),F(z+w+5,13),(z+salt+w)%2==0) for z in range(2**k))
@lru_cache(None)
def prefixed(k,b,w,family):return dense(k,tuple(range(b)),original(k,w,family))
@lru_cache(None)
def full(k,w,family):return dense(k,tuple(range(k)),original(k,w,family))
@lru_cache(None)
def suffix(k,b,w,family):return dense(k,tuple(range(b,k)),prefixed(k,b,w,family))

def fresh(k,q,m,count,base,depth,family,slack):
 b=q*m
 s=dict(pc=0,nat=[(17*i+31)%233 for i in range(5240)],nh={0:71,WORK-1:END,15000:19},sh={1:CA,2:CB},
 sr={i:scalar(4,F(i+2,7),F(9-i,11),True) for i in range(20)},out={7:scalar(4,11,-3)[0]},roots=[4,12])
 # Actual saved-frame sentinels and unrelated heap entries are retained.
 s['nh'].update({9000+j:37+5*j for j in range(40)})
 for reg,val in ((2850,END+slack),(4123,WORK),(4120,k),(4121,base),(4122,2**k),(4060,q),(4061,m),(4151,depth),(4153,1)):s['nat'][reg]=val
 for w in range(count):
  for z,value in enumerate(prefixed(k,b,w,family)):s['sh'][base+w*2**k+z]=value
 for address in (base-1,base+count*2**k,19000):
  if address>=3:s['sh'][address]=scalar(4,-13,7,True)
 return s

def expected(s,k,count,base,family):
 result=deepcopy(s['sh'])
 for w in range(count):
  for z,value in enumerate(full(k,w,family)):result[base+w*2**k+z]=value
 return result
cases=[];coverage={'root':set(),'child':set()};total=0;branchProbeSteps=0
for k in range(7):
 for b in range(k+1):
  factorizations=[(1,b)]
  if b==0:factorizations.append((0,k+2))
  elif b%2==0:factorizations.append((2,b//2))
  for q,m in factorizations:
   for count in range(5):
    for base in (3,1000):
     for family in ('prepared','mixed'):
      for depth in (0,1,4):
       child=depth>0;kind='child' if child else 'root';slack=depth%2
       s=fresh(k,q,m,count,base,depth,family,slack);before=deepcopy(s);want=expected(s,k,count,base,family)
       # Independent suffix oracle agrees with full tensor only after the
       # independently prepared low prefix. This is a diagnostic identity.
       for w in range(count):assert suffix(k,b,w,family)==full(k,w,family)
       arrayCost=(k-b)*(25*2**max(k-1,0)+11)+18
       terminalRuns=4*b+count*arrayCost+20
       # Root final halt is actual. Child halt is the added diagnostic stop;
       # terminal theorem itself stops one instruction earlier at returnSite.
       cost=terminalRuns+1;code=PROGRAMS[kind+str(count)]
       steps,pcs,peak=execute(code,s,B,cost,4)
       assert steps==cost and s['pc']==(81 if child else 80)
       assert s['sh']==want,(k,b,count,base,depth,family)
       assert s['nat'][2850]==END+slack and s['nat'][3301]==END
       assert s['nat'][5200:5205]==[k,count,base,2**k,b]
       assert s['nat'][5209]==count and s['nat'][5205]==2**b
       for name in ('nh','out','roots'):assert s[name]==before[name],name
       for reg in range(5240):
        if reg not in WRITES:assert s['nat'][reg]==before['nat'][reg],('NatFrame',reg)
       for reg in range(8,20):assert s['sr'][reg]==before['sr'][reg],('ScalarFrame',reg)
       for reg in (100,101,102,103,104,105,106,4120,4121,4122,4123,4060,4061,4151,4153):assert s['nat'][reg]==before['nat'][reg]
       # Stop immediately before finish to verify terminalRuns and inspect
       # the unchanged branch source. One artificial probe halt is counted.
       probe=deepcopy(code);probe[79]=['halt'];t=deepcopy(before)
       psteps,_,_=execute(probe,t,B,terminalRuns,4)
       assert psteps==terminalRuns and t['pc']==79 and t['sh']==want and t['nh']==before['nh']
       assert t['nat'][4151]==depth and t['nat'][4153]==1
       assert peak<=B
       total+=steps;branchProbeSteps+=psteps;coverage[kind].update(pcs)
       cases.append(dict(bits=k,startAxis=b,q=q,m=m,arrays=count,base=base,depth=depth,family=family,expiredSlack=slack,terminalRuns=terminalRuns,totalSteps=steps,rootActualHalt=not child,childDiagnosticHalt=child))
assert coverage['root']==set(range(81))-set(range(34,40))
assert coverage['child']==set(range(82))-set(range(34,40))-{80}
controls=[]
def guard(name,mutate,budget=100000):
 s=fresh(3,1,1,2,1000,0,'mixed',0);code=deepcopy(PROGRAMS['root2']);mutate(s,code)
 try:execute(code,s,B,budget,4)
 except (AssertionError,KeyError) as err:controls.append(dict(name=name,mode='runtimeGuard',reason=str(err)));return
 raise AssertionError('guard unexpectedly accepted '+name)
guard('missingMainEndMetadata',lambda s,c:s['nh'].pop(WORK-1))
guard('missingDiagonalConstant',lambda s,c:s['sh'].pop(1))
guard('missingOffDiagonalConstant',lambda s,c:s['sh'].pop(2))
guard('missingInputArrayEntry',lambda s,c:s['sh'].pop(1000+8+1))
guard('dependentCConstant',lambda s,c:s['sh'].__setitem__(1,(CA[0],True)))
guard('wrongNativeVolumeMissingData',lambda s,c:s['nat'].__setitem__(4122,16))
guard('insufficientChargedFuel',lambda s,c:None,budget=4+2*((3-1)*(25*4+11)+18)+20)
for name,mutate in [('wrongNativeBits',lambda s,c:s['nat'].__setitem__(4120,2)),('liveTapeInsteadOfExpired',lambda s,c:s['nh'].__setitem__(WORK-1,END+1)),('wrongStartAxisHeader',lambda s,c:s['nat'].__setitem__(4061,2))]:
 s=fresh(3,1,1,2,1000,0,'mixed',0);want=expected(s,3,2,1000,'mixed');code=deepcopy(PROGRAMS['root2']);mutate(s,code)
 execute(code,s,B,100000,4);assert s['sh']!=want
 controls.append(dict(name=name,mode='expectedOutcomeMismatch'))
receipt=dict(status='PASS',cases=len(cases),steps=total,finishProbeSteps=branchProbeSteps,pcCoverage={k:sorted(v) for k,v in coverage.items()},controls=controls,default_proof_limits=True,uniform_algorithm_verified=False,
 scope='Exact Q[i] dense full C tensor after independent dense low-prefix preparation, then identical loop4/setup6/spectator69/finish1/root-halt1 slices in81/82 tiny cells. Arrays0..4,bits0..6,all axis splits,q*m factorizations and stack depths0/1/4. Child halt is only a diagnostic stop after the proven finish branch; no saved-frame return execution or prefix RAM producer claimed. Actual W/commonSavingProgram/PC numerals remain symbolic; full uniform DFT remains open.')
(P/'fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='pcCoverage'}))
