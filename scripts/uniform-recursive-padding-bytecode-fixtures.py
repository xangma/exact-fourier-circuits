"""Exact finite placements of the six actual padding control slices.
There is no residual child execution: PC90 is an explicit diagnostic
continuation to Next, and PC89 an explicit stop after Finish.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import json,sys
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-bytecode/recursive-foundations/padding'
sys.path.insert(0,str(R/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
CODE=json.loads((D/'program.json').read_text());SL=json.loads((D/'slices.json').read_text())
B=30000;U=1000;SAVED=8000;END=8100
WRITES=set(range(2850,2877))|{5300}|set(range(4175,4180))
def relocated(code,base,ret):
 rows=deepcopy(code)
 for row in rows:
  if row[0]=='branch':row[3]+=base;row[4]+=base
  elif row[0]=='jump':row[1]+=base
  elif row[0]=='halt':row[:]=['jump',ret]
 return rows
assert len(CODE)==91
assert CODE[0:10]==SL['init'] and CODE[10]==['jump',11]
assert CODE[11:16]==SL['test'] and CODE[16]==['branch',4175,4176,17,85]
assert CODE[17:26]==SL['patch'] and CODE[26]==['jump',27]
assert CODE[27:79]==relocated(SL['reader'],27,90)
assert CODE[79:84]==SL['next'] and CODE[84]==['jump',11]
assert CODE[85:88]==SL['finish'] and CODE[88:]==[['jump',89],['halt'],['jump',79]]
assert all(row[0] in ('lit','add','sub','mul','getnat','putnat','jump','branch','halt','div') for row in CODE)
def fresh(m,q,r,count,dest,work,prepared=False,pc=0):
 k=q*m+r
 s=dict(pc=pc,nat=[(17*i+31)%233 for i in range(6000)],nh={work-2:U,work-1:END,17000:59},
 sh={1:scalar(4,F(1,2),F(1,2)),2:scalar(4,F(1,2),F(-1,2)),19000:scalar(4,5,-7,True)},
 sr={i:scalar(4,F(i+2,7),F(9-i,11),i%2==0) for i in range(20)},out={7:scalar(4,11,-3)[0]},roots=[4,12])
 for reg,val in ((4123,work),(4153,1),(2865,SAVED),(2854,dest),(2855,count),(4060,q),(4120,k),
 (4121,2000),(4122,64),(4127,r),(4150,9000),(4151,4)):s['nat'][reg]=val
 for j in range(40):s['nh'][9000+j]=37+5*j
 # Genuine opcode0 record, initially carrying unrelated previous columns
 # and destination: Patch must update those fields and retain every body bit.
 raw=[0,5,m,17,0,0,m,0]+[int(j==i) for j in range(m) for i in range(m)]
 s['nh'].update({U+j:v for j,v in enumerate(raw)})
 for address in (U-1,U+len(raw)):s['nh'][address]=71
 if prepared:s['nh'].update({work-6:1,work-5:SAVED,work-4:dest,work-3:dest+count})
 return s,raw
cases=[];coverage=set();total=0;probeTotal=0
for m in (0,1,2,4,6):
 for q in (0,1,3):
  for r in (0,1,4):
   for count in (0,1,2,4):
    for dest in (0,3):
     for work in (6,7000):
      s,raw=fresh(m,q,r,count,dest,work);before=deepcopy(s)
      want=deepcopy(s['nh']);want.update({work-6:1,work-5:SAVED,work-4:dest+count,work-3:dest+count})
      if count:want.update({U+1:q,U+3:dest+count-1})
      # Actual six-slice charge excludes count continuation cells and final
      # diagnostic stop. There are54 actual cells executed per visited role.
      actualCost=21+54*count;cost=actualCost+count+1
      steps,pcs,peak=execute(CODE,s,B,cost,4)
      assert steps==cost and s['pc']==89 and s['nh']==want,(m,q,r,count,dest,work)
      assert s['nat'][2850]==SAVED
      if count:
       assert s['nat'][2851:2859]==[0,q,m,dest+count-1,0,0,m,0]
       assert s['nat'][2864]==m*m and s['nat'][2865]==U+len(raw) and s['nat'][5300]==q*m+r
      else:assert s['nat'][5300]==before['nat'][5300]
      for key in ('sh','sr','out','roots'):assert s[key]==before[key],key
      for j in range(6000):
       if j not in WRITES:assert s['nat'][j]==before['nat'][j],j
      assert [s['nh'][U+8+j] for j in range(m*m)]==raw[8:]
      if count:
       # Stop precisely at reader's result to check fields, unit pointer,
       # physical body, actual k and all parent registers before any Next.
       probe=deepcopy(CODE);probe[90]=['halt'];t=deepcopy(before)
       ps,_,_=execute(probe,t,B,60,4);assert ps==60 and t['pc']==90
       assert t['nat'][2851:2859]==[0,q,m,dest,0,0,m,0]
       assert t['nat'][2850]==U and t['nat'][2864]==m*m and t['nat'][2865]==U+len(raw)
       assert t['nat'][5300]==q*m+r and t['nh'][work-4]==dest and t['nh'][work-3]==dest+count
       assert [t['nh'][U+j] for j in range(len(raw))]==[0,q,m,dest,0,0,m,0]+raw[8:]
       for j in (4120,4121,4122,4127,4150,4151,4153,4123):assert t['nat'][j]==before['nat'][j]
       probeTotal+=ps
      total+=steps;coverage.update(pcs)
      cases.append(dict(m=m,q=q,remainder=r,actualBits=q*m+r,roles=count,dest=dest,work=work,actualControlSteps=actualCost,
       diagnosticContinuationSteps=count,diagnosticStopSteps=1,totalSteps=steps))
assert len(cases)==720
assert coverage==set(range(91))-set(range(54,61))-set(range(63,76)),sorted(coverage)
controls=[]
def guard(name,mutate,pc=0,budget=10000):
 s,raw=fresh(2,3,1,2,3,7000,True,pc);c=deepcopy(CODE);mutate(s,c)
 try:execute(c,s,B,budget,4)
 except (AssertionError,KeyError) as e:controls.append(dict(name=name,mode='runtimeGuard',reason=str(e)));return
 raise AssertionError('guard unexpectedly accepted '+name)
guard('missingUnitPointer',lambda s,c:s['nh'].pop(6998),pc=17)
guard('missingCurrentRole',lambda s,c:s['nh'].pop(6996),pc=11)
guard('missingRoleEnd',lambda s,c:s['nh'].pop(6997),pc=11)
guard('missingSavedMainCursor',lambda s,c:s['nh'].pop(6995),pc=85)
guard('missingRetainedHeaderField',lambda s,c:s['nh'].pop(U+4),pc=17)
# A wrong one may terminate on existing stale metadata; termination alone
# does not validate the raw one-register premise. Check the physical result.
s,raw=fresh(2,3,1,2,3,7000,True);s['nat'][4153]=2
execute(CODE,s,B,10000,4)
assert s['nh'][6994]!=1 and s['nh'][6998]!=U
controls.append(dict(name='wrongOneCorruptsMetadata',mode='expectedOutcomeMismatch'))
guard('insufficientChargedFuel',lambda s,c:None,budget=131)
for name,mutate in [('wrongNativeBits',lambda s,c:s['nat'].__setitem__(4120,6)),
 ('wrongPhysicalWidth',lambda s,c:s['nh'].__setitem__(U+2,1)),
 ('wrongColumns',lambda s,c:s['nat'].__setitem__(4060,2)),
 ('wrongUnitDestinationStore',lambda s,c:c.__setitem__(22,['putnat',4178,4176]))]:
 s,raw=fresh(2,3,1,2,3,7000);c=deepcopy(CODE);c[90]=['halt'];mutate(s,c)
 execute(c,s,B,10000,4)
 expected=s['nat'][2851:2859]==[0,3,2,3,0,0,2,0] and s['nat'][5300]==7
 assert not expected,name
 controls.append(dict(name=name,mode='expectedOutcomeMismatch'))
receipt=dict(status='PASS',cases=len(cases),steps=total,readerProbeSteps=probeTotal,controls=controls,pcCoverage=sorted(coverage),
 default_proof_limits=True,uniform_algorithm_verified=False,
 scope='Identical Init11/Test6/Patch10/reader52/Next6/Finish4 finite91-cell placements. The reader executes32 charged opcode0 cells. Role counts0/1/2/4; q0/1/3, m0/1/2/4/6; remainders0/1/4 and actualk=q*m+r; destinations0/3; work6/7000; complete scalar/tag/output/root and outside Nat/saved-stack frames. The count PC90 continuation to Next and PC89 halt are explicit diagnostics; no residual handler, child call, huge W/program/actualPC, native saving instance or whole uniform algorithm evaluated or claimed.')
(D/'fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='pcCoverage'}))
