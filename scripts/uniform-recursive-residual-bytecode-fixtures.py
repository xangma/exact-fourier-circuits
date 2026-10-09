"""Finite exact placements of residual controls and raw opcode0 entry.
The gather destination is a diagnostic jump to directionNext: neither child
nor numerical residual semantics are exercised or inferred from termination.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import sys,json
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-bytecode/recursive-foundations/residual'
sys.path.insert(0,str(R/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
C=json.loads((D/'program.json').read_text());SL=json.loads((D/'slices.json').read_text());B=30000
RAW_WRITES=set(range(2850,2877))|{3301,4177,4178,4179,4130,4131,4132,4134}
CTRL_WRITES={2850,4177,4178,4179,4130,4131,4132,4134}
def relocated(code,base,ret):
 rows=deepcopy(code)
 for row in rows:
  if row[0]=='branch':row[3]+=base;row[4]+=base
  elif row[0]=='jump':row[1]+=base
  elif row[0]=='halt':row[:]=['jump',ret]
 return rows
assert len(C)==89 and C[0:3]==SL['loop'] and C[3]==['branch',2850,3301,4,86]
assert C[4:56]==relocated(SL['reader'],4,56) and C[56:68]==SL['dispatch']
assert C[68:72]==SL['mark'] and C[72:76]==SL['init'] and C[76]==['jump',77]
assert C[77]==['branch',4134,4132,87,80]
assert C[78:79]==SL['next'] and C[79]==['jump',77]
assert C[80:83]==SL['edge'] and C[83]==['branch',4177,4153,84,88]
assert C[84:85]==SL['advance'] and C[85:]==[['jump',0],['halt'],['jump',78],['halt']]
def fresh(work=7000,T=1000,m=2,dimension=3,inverse=1,q=3,index=0,flag=2,pc=0):
 raw=[0,q,m,7,5,inverse,dimension,11]+[(7*j+3)%2 for j in range(m*dimension)]
 end=T+len(raw)
 s=dict(pc=pc,nat=[(31+19*j)%241 for j in range(6000)],nh={max(work-6,0):flag,max(work-2,0):17000,max(work-1,0):end,18000:37},
 sh={1:scalar(4,F(1,2),F(1,2)),2:scalar(4,F(1,2),F(-1,2)),19000:scalar(4,-7,5,True)},
 sr={j:scalar(4,F(3*j+1,13),F(9-j,11),j%3==0) for j in range(20)},out={7:scalar(4,11,-3)[0]},roots=[4,12])
 s['nh'].update({T+j:v for j,v in enumerate(raw)})
 for j in range(40):s['nh'][9000+j]=37+5*j
 for reg,val in ((4123,work),(2850,T),(4153,1),(2857,dimension),(2865,end),(2856,inverse),(4134,index),
 (4132,dimension),(4130,end),(4131,inverse),(4120,q*m+1),(4121,2000),(4122,64),(4127,1),(4150,9000),(4151,4),(5300,q*m+1)):
  s['nat'][reg]=val
 return s,raw,end

def frame(before,after,allowed,heapChanges=None):
 for key in ('sh','sr','out','roots'):assert after[key]==before[key],key
 for j in range(6000):
  if j not in allowed:assert after['nat'][j]==before['nat'][j],('NatFrame',j)
 want=deepcopy(before['nh']);want.update(heapChanges or {});assert after['nh']==want,('HeapFrame',heapChanges)
rows=[];coverage=set();stepsTotal=0;probeTotal=0
for m in range(5):
 for dim in range(7):
  for inv in (0,1,3):
   for q in (0,3):
    for work in (6,7,7000):
     for T in (1000,12000):
      s,raw,end=fresh(work,T,m,dim,inv,q);before=deepcopy(s)
      # Exact raw_entry stops before directionTest. One explicit probe halt
      # is added at77 and excluded from the theorem's46 charged instructions.
      p=deepcopy(C);p[77]=['halt'];probe=deepcopy(before)
      ps,_,_=execute(p,probe,B,47,4);assert ps==47 and probe['pc']==77
      assert probe['nat'][4134]==0 and probe['nat'][4132]==dim and probe['nat'][4130]==end and probe['nat'][4131]==inv
      assert probe['nat'][2851:2859]==raw[:8] and probe['nat'][2864]==dim*m and probe['nat'][2865]==end
      assert probe['nh'][work-6]==0 and probe['nh'][work-1]==end and probe['nh'][work-2]==17000
      assert [probe['nh'][T+j] for j in range(len(raw))]==raw
      frame(before,probe,RAW_WRITES,{max(work-6,0):0})
      # Direction handler87 is synthetic. Actual tested controls have
      # 57+3*dim steps, plus dim synthetic jumps and one stop.
      cost=58+4*dim;steps,pcs,peak=execute(C,s,B,cost,4)
      assert steps==cost and s['pc']==86 and s['nat'][2850]==end and s['nat'][4134]==dim
      assert s['nat'][4132]==dim and s['nat'][4130]==end and s['nat'][4131]==inv
      frame(before,s,RAW_WRITES,{max(work-6,0):0});assert peak<=B
      coverage.update(pcs);stepsTotal+=steps;probeTotal+=ps
      rows.append(dict(kind='rawEntry46AndControlCycle',width=m,dimension=dim,inverse=inv,q=q,work=work,record=T,body=dim*m,
       actualSteps=57+3*dim,diagnosticJumps=dim,diagnosticStop=1,totalSteps=steps,rawEntrySteps=46,probeStopSteps=1))
assert len(rows)==1260
# Isolated controls cover all branch outcomes, including saturated subtraction
# at work<6 in the generic controls (raw_entry itself requires work>=6).
controlCoverage=set()
for work in (0,3,6,7,7000):
 for flag in (0,1,2,9):
  for index,dimension in ((0,0),(0,1),(1,1),(1,2),(3,2)):
   for kind,start,stop,charged in (('mark',68,72,4),('init',72,77,5),('next',78,77,2),
    ('advance',84,0,2),('test',77,87 if index<dimension else 80,1),('edge',80,84 if flag<1 else 88,4)):
    s,raw,end=fresh(work=work,index=index,dimension=dimension,flag=flag,pc=start);s['nh'][max(work-6,0)]=flag;before=deepcopy(s)
    p=deepcopy(C);p[stop]=['halt'];steps,pcs,_=execute(p,s,B,charged+1,4)
    assert steps==charged+1 and s['pc']==stop,(kind,work,flag,index,dimension)
    frame(before,s,CTRL_WRITES,{max(work-6,0):0} if kind=='mark' else {})
    if kind=='init':assert (s['nat'][4134],s['nat'][4132],s['nat'][4130],s['nat'][4131])==(0,dimension,end,1)
    if kind=='next':assert s['nat'][4134]==index+1
    if kind=='advance':assert s['nat'][2850]==end
    if kind=='edge':assert s['nat'][4177]==before['nh'][max(work-6,0)]
    coverage.update(pcs);controlCoverage.update(pcs);stepsTotal+=steps
    rows.append(dict(kind=kind,work=work,flag=flag,index=index,dimension=dimension,actualSteps=charged,diagnosticStop=1,totalSteps=steps))
assert len(rows)==1860
assert set(range(68,86))<=controlCoverage
assert coverage==set(range(89))-set(range(31,38))-set(range(40,53))-set(range(57,68)),sorted(coverage)
controls=[]
def guard(name,mutate,pc=0,at77=False,budget=10000):
 s,raw,end=fresh(pc=pc);p=deepcopy(C)
 if at77:p[77]=['halt']
 mutate(s,p)
 try:execute(p,s,B,budget,4)
 except (AssertionError,KeyError) as err:controls.append(dict(name=name,mode='runtimeGuard',reason=str(err)));return
 raise AssertionError('guard unexpectedly accepted '+name)
guard('missingMainEndMetadata',lambda s,p:s['nh'].pop(6999))
guard('missingRawHeaderDimension',lambda s,p:s['nh'].pop(1006))
guard('missingEdgeModeMetadata',lambda s,p:s['nh'].pop(6994),pc=80)
guard('opcodeAboveSixDecoderTrap',lambda s,p:s['nh'].__setitem__(1000,7))
guard('directionIncrementWordOverflow',lambda s,p:s['nat'].__setitem__(4134,B),pc=78)
guard('rawEntryFuel46ExcludesProbeStop',lambda s,p:None,at77=True,budget=46)
for name,mutate in [('wrongUnitRegister',lambda s,p:s['nat'].__setitem__(4153,2)),
 ('wrongWidthViolatesPrintedBodyGeometry',lambda s,p:s['nh'].__setitem__(1002,4)),
 ('wrongModeStoreCell',lambda s,p:p.__setitem__(69,['sub',4178,4123,4153])),
 ('wrongDimensionCopy',lambda s,p:p.__setitem__(73,['mul',4132,2856,4153])),
 ('wrongRecordEndCopy',lambda s,p:p.__setitem__(74,['mul',4130,2850,4153]))]:
 s,raw,end=fresh();p=deepcopy(C);p[77]=['halt'];mutate(s,p)
 execute(p,s,B,10000,4)
 correct=s['nat'][4134]==0 and s['nat'][4132]==3 and s['nat'][4130]==end and s['nat'][4131]==1 and s['nh'][6994]==0
 assert not correct,name
 controls.append(dict(name=name,mode='expectedOutcomeMismatch'))
# Missing unit-pointer metadata is deliberately not consumed by these controls;
# its absence is preserved. This catches accidental stronger producer claims.
s,raw,end=fresh();s['nh'].pop(6998);p=deepcopy(C);p[77]=['halt'];execute(p,s,B,47,4);assert 6998 not in s['nh']
nonconsumption=dict(name='unitPointerCellNotRead',passed=True,meaning='Raw entry preserves absence, rather than manufacturing or checking a child unit producer.')
receipt=dict(status='PASS',cases=len(rows),rawEntryCases=1260,isolatedControlCases=600,steps=stepsTotal,rawEntryProbeSteps=probeTotal,
 controls=controls,pcCoverage=sorted(coverage),controlPcCoverage=sorted(controlCoverage),nonconsumption=nonconsumption,
 default_proof_limits=True,uniform_algorithm_verified=False,
 scope='Actual symbolic CodeAt links verified by default rebuild; identical89-cell finite placements of loop4/raw header52/dispatch12/mark4/init5/test1/next2/edge4/advance2. Raw opcode0 entry has46 charged steps before directionTest;1260 raw cases plus600 isolated controls. True/false direction and mode branches, dimensions0..6,widths0..4,inverses0/1/3,q0/3,work6/7/7000 plus isolated saturated work0/3, records1000/12000, all scalar/tag/output/root/Nat/outside-metadata/saved-stack frames. Gather87 is a diagnostic continuation directly to Next; destinations86/88 and probe halt77 are explicit stops. No actual huge SavingProgram/PC/payload, residual numerical handler, recursive child, saving result or full uniform algorithm executed or claimed.')
(D/'fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=rows),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('pcCoverage','controlPcCoverage')}))
