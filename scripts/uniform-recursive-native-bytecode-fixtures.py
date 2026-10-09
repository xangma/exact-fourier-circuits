"""Bounded exact tests of small placements of the identical control/native slices.
No actual SavingProgram, numeric SavingProgram PC, huge seed or W-bank evaluated.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import json,sys,hashlib,os
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'logs/uniform-bytecode/recursive-foundations/native'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute,add,mul
CODE=json.loads((P/'small-program.json').read_text());SLICES=json.loads((P/'slices.json').read_text())
assert len(CODE)==524
PLACEMENTS={'loop':(0,4,None),'head':(4,52,56),'dispatch':(56,12,None),'scalar':(68,106,0),'exchange':(174,98,0),'translation':(272,197,0),'marker':(469,54,0)}
def relocate(code,base,ret):
 out=deepcopy(code)
 for row in out:
  if row[0]=='branch':row[3]+=base;row[4]+=base
  elif row[0]=='jump':row[1]+=base
  elif row[0]=='halt':row[:]=['jump',ret]
 return out
for name,(base,size,ret) in PLACEMENTS.items():
 assert len(SLICES[name])==size
 expect=SLICES[name] if ret is None else relocate(SLICES[name],base,ret)
 assert CODE[base:base+size]==expect,name
assert CODE[523]==['halt']
COEFS=[F(-1),F(-1,2),F(0),F(1,2),F(1)]
CONTROL=set(range(2850,2877))|{3301,4177,4178,4179}
SCALAR=CONTROL|set(range(2900,2917))|set(range(3302,3307))
EXCHANGE=CONTROL|set(range(3320,3342))|set(range(3302,3307))
Y=CONTROL|{0,1,3360,3365,3366,3368,3369,3370,3380,3381,3382,3383,3384,3386,3387,3353,3354}|set(range(1900,1909))|set(range(3350,3360))|set(range(3361,3364))|set(range(3371,3379))|set(range(3400,3431))|set(range(3440,3447))|set(range(3302,3307))
B=60000;A=1000;PBASE=8000;WORK=7000;E=6000;TABLE=10000;ROLES=3

def fresh(D,q,w,rest,records,family):
 k=q*w+rest;V=2**k;data=sum(records,[])
 s=dict(pc=0,nat=[(17*i+31)%233 for i in range(5400)],nh={1:3,77:19,WORK-1:PBASE+len(data),TABLE-1:91,TABLE+2**(2*q):93},sh={},
        sr={i:scalar(D,F(i+2,7),F(9-i,11),True) for i in range(120)},out={7:scalar(D,11,-3)[0]},roots=[D,4])
 for r,v in ((2850,PBASE),(3300,A),(5300,k),(5301,rest),(3364,E),(3389,TABLE),(4123,WORK),(4153,1)):s['nat'][r]=v
 s['nh'].update({PBASE+i:v for i,v in enumerate(data)})
 for role in range(ROLES):
  for z in range(V):
   s['sh'][A+role*V+z]=scalar(D,F(role-z+31,11),F(z+3*role,13),False) if family=='prepared' else scalar(D,F(3*z-7*role+31,11),F(z+role+5,13),(z+31+role)%2==0)
 for a in (A-1,A+ROLES*V,E-1,E+V,50000):s['sh'][a]=scalar(D,-13,7,True)
 return s

def shear(q,w,d,src,c):return [1,q,w,d,src,0,0,c]
def exchange(q,w,pairs):return [4,q,w,0,0,0,len(pairs),0]+sum(([d,s,4,0] for d,s in pairs),[])
def translate(q,w,ds):return [3,q,w,0,0,0,len(ds),0]+sum(([r]+bits for r,bits in ds),[])
def marker(q,w,opcode,body):return [opcode,q,w,2,len(body) if opcode==2 else 7,0,3,4]+body

def iteration_cost(record,k,rest):
 opcode,q,w,d,src,iv,count,c=record[:8];V=2**k
 head=32+opcode+(opcode==3);dispatch=12 if opcode==6 else 2*opcode+1
 if opcode==1:return 10*V+4*k+c+102
 if opcode==4:return (10*V+21)*count+4*k+99
 if opcode==3:
  tableCost=4*q+10+(12*q+15)*2**(2*q)
  child=tableCost+9*q*w+(17*(w+rest)+25)*V+31
  return count*(child+11)+4*k+52+47
 return 6+2*head+dispatch

def expected(records,before,k):
 out=deepcopy(before['sh']);V=2**k
 for record in records:
  opcode,q,w,d,src,iv,count,c=record[:8];body=record[8:]
  if opcode==1:
   assert d!=src
   for z in range(V):out[A+d*V+z]=add(out[A+d*V+z],mul(scalar(before['roots'][0],COEFS[c]),out[A+src*V+z]))
  elif opcode==4:
   for j in range(count):
    d,src=body[4*j:4*j+2];assert d!=src
    for z in range(V):a,b=out[A+d*V+z],out[A+src*V+z];out[A+d*V+z]=b;out[A+src*V+z]=(-a[0],a[1])
  elif opcode==3:
   for j in range(count):
    r,*bits=body[(w+1)*j:(w+1)*(j+1)]
    mask=sum(bit*2**(column*w+bitidx) for column in range(q) for bitidx,bit in enumerate(bits))%V
    old=[out[A+r*V+z] for z in range(V)]
    for z in range(V):out[A+r*V+z]=old[z^mask]
 return out

cases=[];pcs=set();ticks=0;prefixTicks=0;terminalCases=0

def check(records,D,q,w,rest,family,kind):
 global ticks,prefixTicks,terminalCases
 s=fresh(D,q,w,rest,records,family);before=deepcopy(s);k=q*w+rest;V=2**k
 want=expected(records,before,k);cost=sum(iteration_cost(r,k,rest) for r in records)+5
 steps,seen,peak=execute(CODE,s,B,cost,D)
 assert steps==cost and s['pc']==523 and s['nat'][2850]==PBASE+sum(map(len,records))
 for address,value in want.items():
  if E<=address<E+V and any(r[0]==3 and r[6] for r in records):continue
  assert s['sh'].get(address)==value,(kind,q,w,rest,address)
 assert set(s['sh'])<=set(want)|set(range(E,E+V))
 allowNat=set(range(TABLE,TABLE+2**(2*q))) if any(r[0]==3 and r[6] for r in records) else set()
 assert {a:v for a,v in s['nh'].items() if a not in allowNat}=={a:v for a,v in before['nh'].items() if a not in allowNat}
 for name in ('out','roots'):assert s[name]==before[name],name
 allowed=CONTROL.copy();scalarAllowed=set()
 for r in records:
  if r[0]==1:allowed|=SCALAR;scalarAllowed|={100,101,102,104}
  elif r[0]==4:allowed|=EXCHANGE;scalarAllowed|={110,111,112,113}
  elif r[0]==3:allowed|=Y;scalarAllowed|={100,114}
 for j in range(5400):
  if j not in allowed:assert s['nat'][j]==before['nat'][j],(kind,'NatFrame',j)
 for j in range(120):
  if j not in scalarAllowed:assert s['sr'][j]==before['sr'][j],(kind,'ScalarFrame',j)
 assert s['nat'][5300]==k and s['nat'][5301]==rest
 if records:
  r=records[0];opcode=r[0];target={1:68,2:469,3:272,4:174,6:469}[opcode]
  prefix=deepcopy(CODE);prefix[target]=['halt'];t=deepcopy(before)
  head=32+opcode+(opcode==3);dispatch=12 if opcode==6 else 2*opcode+1
  csteps,_,_=execute(prefix,t,B,4+head+dispatch+1,D)
  assert csteps==4+head+dispatch+1 and t['pc']==target
  assert t['nat'][2850]==PBASE and t['nat'][3301]==PBASE+sum(map(len,records))
  assert t['nat'][2851:2859]==r[:8]
  assert t['nat'][2864]==len(r)-8 and t['nat'][2865]==PBASE+len(r)
  for name in ('nh','sh','sr','out','roots'):assert t[name]==before[name],('ControlFrame',name)
  for j in range(5400):
   if j not in CONTROL:assert t['nat'][j]==before['nat'][j],('ControlFrame',j)
  prefixTicks+=csteps
 else:terminalCases+=1
 ticks+=steps;pcs.update(seen)
 cases.append(dict(kind=kind,D=D,q=q,width=w,remainder=rest,nativeBits=k,family=family,records=records,steps=steps,peak=peak))

for D in (4,12):
 for q,w,rest in ((0,2,1),(1,1,0),(1,2,1),(2,1,1),(2,2,1)):
  for family in ('prepared','mixed'):
   for d,src in ((0,1),(2,0)):
    for c in range(5):check([shear(q,w,d,src,c)],D,q,w,rest,family,'scalar')
   for pairs in ([],[(0,1)],[(0,1),(1,2),(2,0)]):check([exchange(q,w,pairs)],D,q,w,rest,family,'exchange')
   for opcode in (2,6):
    for body in ([[],[0,2,4,6]] if opcode==2 else [[]]):check([marker(q,w,opcode,body)],D,q,w,rest,family,'marker')
   if q:
    for ds in ([],[(0,[0]*w)],[(2,[1]*w)],[(0,[1]*w),(2,[i%2 for i in range(w)]),(0,[1]*w)]):check([translate(q,w,ds)],D,q,w,rest,family,'translation')
    records=[marker(q,w,6,[]),shear(q,w,0,1,3),translate(q,w,[(2,[1]*w)]),exchange(q,w,[(0,1),(1,2)]),marker(q,w,2,[0,2,4,6]),shear(q,w,2,0,0)]
    check(records,D,q,w,rest,family,'mixedContinuousTape')
   check([],D,q,w,rest,family,'emptyTapeExit')

controls=[]
def guard(name,mutate,record=None,budget=None):
 record=record or shear(1,2,0,1,4);s=fresh(4,1,2,1,[record],'mixed');code=deepcopy(CODE);mutate(s,code)
 try:execute(code,s,B,budget or 100000,4)
 except (AssertionError,KeyError):controls.append(dict(name=name,mode='runtimeGuard'))
 else:raise AssertionError('guard unexpectedly accepted: '+name)
guard('missingMainEndMetadata',lambda s,c:s['nh'].pop(WORK-1))
guard('missingRawHeader',lambda s,c:s['nh'].pop(PBASE+2))
guard('missingNativeDestination',lambda s,c:s['sh'].pop(A+1))
guard('missingNativeSource',lambda s,c:s['sh'].pop(A+8+1))
guard('invalidScalarCoefficientCode',lambda s,c:s['nh'].__setitem__(PBASE+7,9))
guard('missingVariablePairBody',lambda s,c:s['nh'].pop(PBASE+8),exchange(1,2,[(0,1)]))
guard('missingOriginalYDirection',lambda s,c:s['nh'].pop(PBASE+9),translate(1,2,[(0,[1,0])]))
guard('widthIncrementWordOverflow',lambda s,c:s['nh'].__setitem__(PBASE+2,B),translate(1,2,[(0,[1,0])]))
guard('nativeVolumeWordOverflow',lambda s,c:s['nat'].__setitem__(5300,16))
record=shear(1,2,0,1,4);budget=iteration_cost(record,3,1)+4
guard('insufficientChargedFuel',lambda s,c:None,record,budget)
# These malformed headers remain readable; assert their observable data/cursor
# differs, instead of falsely describing them as machine rejection.
for name,mutate in [('wrongNativeBits',lambda s,c:s['nat'].__setitem__(5300,2)),('prematureMainEnd',lambda s,c:s['nh'].__setitem__(WORK-1,PBASE)),('wrongScalarDispatchTarget',lambda s,c:c[58].__setitem__(3,272))]:
 record=shear(1,2,0,1,4);s=fresh(4,1,2,1,[record],'mixed');before=deepcopy(s);code=deepcopy(CODE);mutate(s,code)
 execute(code,s,B,100000,4)
 assert s['sh']!=expected([record],before,3) or s['nat'][2850]!=PBASE+len(record)
 controls.append(dict(name=name,mode='expectedOutcomeMismatch'))
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,prefixProbeSteps=prefixTicks,pcCoverage=sorted(pcs),terminalCases=terminalCases,controls=controls,placementSizes={k:v[1] for k,v in PLACEMENTS.items()},
 scope='524-cell small equivalent generic placement of exact4/52/12 control and exact106/98/197/54 native slices. Each tape iteration returns to the same small PC0. Terminal branch4+halt1 counted separately; prefix probes add one artificial halt. Actual huge recursive SavingProgram PCs, saving witness, complete cache/child execution/global DFT are never evaluated or claimed.')
(P/'fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('pcCoverage',)}))
