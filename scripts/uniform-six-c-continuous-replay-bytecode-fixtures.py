"""Fresh5375 bytecode; actual typed cross tapes, generic and actual rank-kernel banks.
No selected-axis startup claimed. Scalar arithmetic is exact Q[i], D=4.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json,sys,time,os
ROOT=next(parent for parent in Path(__file__).resolve().parents if (parent/'lean/UniformMachine.lean').is_file())
HERE=Path(os.environ.get('UNIFORM_SIX_C_OUTPUT_DIR',str(ROOT/'logs/uniform-bytecode/six-c-continuous')))
HERE.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import Poly,scalar,execute
programs=json.loads((HERE/'programs.json').read_text());code=programs['full']
specs=json.loads((HERE/'specs.json').read_text());B=400000;D=4
assert len(code)==5375 and code[-1]==['halt']
assert not any(i[0] in ['root','input','output','length'] for i in code)
C,T,P,V,MU,BAR=32,128,224,256,320,321
SOURCE,FWD_PACK,INV_PACK=1000,2000,3000
TAPE,ORDER,DIRECTORY=10000,12000,13000
ROWS,COLORS,PALETTE,RECORDS=20000,24000,27000,28000
BORROW,SELECTED,ORDINALS,MAPPED,PERM,WIDTHS,MARKERS,AXIS=40000,42000,44000,46000,48000,50000,52000,54000
SUFFIX,STACK,UNPACK=56000,58000,60000
INVROWS,IPERM,IWIDTH,IMARK,IAXIS,ISUFFIX,ISTACK,IUNPACK=64000,66000,68000,70000,72000,74000,76000,78000

def fresh(spec,pattern):
 K,a,e,G=map(spec.__getitem__,['K','a','e','G']);N=2**K;R=7*N;r=2**max(6,(G+e+a-1).bit_length());src=0;tgt=r//2
 global COLORS,PALETTE,RECORDS,BORROW,SELECTED,ORDINALS,MAPPED,PERM,WIDTHS,MARKERS,AXIS,SUFFIX,STACK,UNPACK,INVROWS,IPERM,IWIDTH,IMARK,IAXIS,ISUFFIX,ISTACK,IUNPACK
 COLORS=ROWS+6*G*(8*K+7)+2000
 PALETTE=COLORS+2*G*(8*K+7)+1000
 RECORDS=PALETTE+23
 bases=list(range(100000,140000,2000)) if K>=2 else list(range(40000,80000,2000))
 BORROW,SELECTED,ORDINALS,MAPPED,PERM,WIDTHS,MARKERS,AXIS,SUFFIX,STACK,UNPACK,INVROWS,IPERM,IWIDTH,IMARK,IAXIS,ISUFFIX,ISTACK,IUNPACK=bases[:19]
 assert G==6*(3*K*N+2*N)+2*a and G+e+a<=r and a<=G
 sh={0:(Poly(D,{1:1}),False),B-1:scalar(D,21,-17,True)}
 A=scalar(D,F(1,2),F(1,2))[0];I=scalar(D,0,1)[0];AI=scalar(D,1,-1)[0]
 for j,v in {1:A,2:A.conjugate(),3:AI,4:I,5:I*AI}.items():sh[j]=(v,False)
 bank=[scalar(D,F(j+1,3),F(2-j,7))[0] if pattern%2 else scalar(D,1 if j%3==0 else 0)[0] for j in range(R)]
 if K==2:
  assert a==e==1 and N==4 and 2*(a+e)<=N
  matrix=scalar(D,2,1)[0];left=scalar(D,1,-1)[0];right=scalar(D,F(3,2))[0]
  lane=[right,left,matrix-left*right,scalar(D,1)[0],scalar(D,1)[0],Poly(D)]
  bank=[I**j for j in range(N)]+[value for value in lane for _ in range(N)]
 for j,v in enumerate(bank):sh[C+j]=(v,False);sh[T+j]=(-v,False);sh[V+j]=(v.conjugate(),False)
 for j,v in enumerate([1,-1,F(1,N),-F(1,N),F(5,4),F(4,5)]):sh[P+j]=scalar(D,v)
 values=[scalar(D,F(j+pattern-7,11),F(9-j,13),(j+pattern)%3==0) for j in range(r)]
 for j,v in enumerate(values):sh[SOURCE+j]=v;sh[FWD_PACK+j]=scalar(D,80+j,-40-j,True);sh[INV_PACK+j]=scalar(D,-70-j,99+j,True)
 for q in [MU,BAR,SOURCE-1,SOURCE+r,FWD_PACK-1,FWD_PACK+r,INV_PACK-1,INV_PACK+r]:sh[q]=scalar(D,q,-q,True)
 nr=[(17*j+pattern+7)%113 for j in range(3300)];nh={17:31,B-1:11}
 nr[1050:1063]=[K,a,e,TAPE,ORDER,DIRECTORY,ROWS,COLORS,PALETTE,RECORDS,C,0,P]
 nr[1180:1191]=[r,src,tgt,BORROW,SELECTED,ORDINALS,MAPPED,PERM,WIDTHS,MARKERS,AXIS]
 nr[1400:1405]=[SUFFIX,STACK,UNPACK,SOURCE,FWD_PACK]
 nr[3001:3021]=[r,FWD_PACK,SOURCE,UNPACK,MAPPED,C,T,P,V,MU,BAR,INVROWS,IPERM,IWIDTH,IMARK,IAXIS,ISUFFIX,ISTACK,IUNPACK,INV_PACK]
 for i,row in enumerate(spec['rows']):
  for j,v in enumerate(row):nh[TAPE+5*i+j]=v
 for i,v in enumerate(spec['order']):nh[ORDER+i]=v
 for i,v in enumerate(spec['offsets']):nh[DIRECTORY+i]=v
 for base,length in [(ROWS,6*G*(8*K+7)),(COLORS,2*G*(8*K+7)),(PALETTE,12),(RECORDS,3*(8*K+7)),(BORROW,G),(SELECTED,6*G),(ORDINALS,2*G),(MAPPED,6*G),(PERM,r),(WIDTHS,r),(MARKERS,r),(AXIS,4),(SUFFIX,2),(STACK,9),(UNPACK,r),(INVROWS,6*G),(IPERM,r),(IWIDTH,r),(IMARK,r),(IAXIS,4),(ISUFFIX,2),(ISTACK,9),(IUNPACK,r)]:
  for j in range(length):nh[base+j]=(31*j+pattern+5)%97
 state=dict(pc=0,nat=nr,nh=nh,sh=sh,sr={j:scalar(D,j,-j,j%2) for j in range(120)},out={0:scalar(D,17,-23)[0]},roots=[4,1])
 regs=[values[src+j][0] for j in range(e)]+[Poly(D)]
 for op,l,rr,kind,payload in spec['rows']:
  if op==0:v=regs[l]+regs[rr]
  elif op==1:v=regs[l]-regs[rr]
  elif op==2:v=regs[l]*(bank[payload] if kind==1 else scalar(D,F(1,payload))[0])
  else:raise AssertionError(op)
  regs.append(v)
 expected=[v[0] for v in values]
 for j in range(a):expected[tgt+j]=expected[tgt+j]+regs[e+1+G-a+j]
 if K==2:
  assert expected[tgt]==values[tgt][0]+scalar(D,2,1)[0]*values[src][0], 'independent rank-kernel matrix identity'
 return state,expected,values

cases=[];covered=set();totalsteps=0;start=time.time()
for spec in specs:
 for pattern in range(1 if spec['K']==2 else 2):
  s,expected,original=fresh(spec,pattern);before=deepcopy(s)
  steps,pcs,peak=execute(code,s,B,250000000,D)
  for j,v in enumerate(expected):assert s['sh'][SOURCE+j][0]==v,(spec['a'],spec['e'],pattern,j,s['sh'][SOURCE+j][0],v)
  for j in range(7*2**spec['K']):
   for base in [C,T,V]:assert s['sh'][base+j]==before['sh'][base+j]
  for j in range(6):assert s['sh'][P+j]==before['sh'][P+j]
  for j in range(6):assert s['sh'][j]==before['sh'][j]
  assert s['out']==before['out'] and s['roots']==before['roots']
  assert s['nh'][17]==before['nh'][17] and s['nh'][B-1]==before['nh'][B-1]
  assert s['sh'][B-1]==before['sh'][B-1]
  assert all(s['nat'][j]==before['nat'][j] for j in range(100,107))
  totalsteps+=steps;covered.update(pcs)
  cases.append(dict(K=spec['K'],a=spec['a'],e=spec['e'],pattern=pattern,steps=steps,peak=peak,
   origin=f'fresh Lean actual K{spec["K"]} corrected-cross tape/order; '+('actual sharedBank(rankKernels) for nonempty M=[2+i], v=[1-i], w=[3/2], size-valid N4; ' if spec['K']==2 else 'generic exact prepared banks; ')+'ordinary placement/capacity satisfied' ))
  print(json.dumps(cases[-1]),flush=True)
controls=[]
def guard(name,change,mutate=None):
 spec=next(q for q in specs if q['K']==0 and q['a']==q['e']==1)
 s,expected,_=fresh(spec,1);change(s);p=deepcopy(code)
 if mutate:mutate(p)
 try:
  execute(p,s,B,20000000,D)
  assert all(s['sh'][SOURCE+j][0]==v for j,v in enumerate(expected)), 'numeric mismatch'
 except (AssertionError,KeyError) as error:
  controls.append(dict(name=name,observed=type(error).__name__+': '+str(error)))
 else:raise AssertionError(('guard did not fire',name))
guard('missing actual typed tape',lambda s:s['nh'].pop(TAPE))
guard('missing actual positive coefficient',lambda s:s['sh'].pop(C+1))
guard('bad caller conjugate address',lambda s:s['nat'].__setitem__(3009,B-100))
def wrongRows(p):
 index=next(i for i,ins in enumerate(p) if ins[:2]==['add',2400]);p[index][2]=3008
guard('mutated actual inverse-row header setup',lambda s:None,wrongRows)
guard('mutated false-sweep flag',lambda s:None,lambda p:p[2687].__setitem__(2,1))
def wrongDescending(p):
 index=1752+11;assert p[index][:2]==['sub',3028];p[index][0]='add'
guard('mutated actual descending ordinal subtraction',lambda s:None,wrongDescending)
summary=dict(status='PASS',scope='complete literal5375 exact diagnostic; universal execution and corrected-cross numeric restoration are separately proved in UniformSixCWholeReplay/CorrectedReplay; not selected-axis startup or full UniformDFT',
 exactCases=len(cases),totalSteps=totalsteps,coveredPC=len(covered),literalInstructions=len(code),
 elapsedSeconds=time.time()-start,cases=cases,negativeControls=controls,
 inputHashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'programs.json',HERE/'specs.json',Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']})
(HERE/'fixtures.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['cases','inputHashes']}),flush=True)
