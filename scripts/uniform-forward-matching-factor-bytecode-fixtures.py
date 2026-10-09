"""Fresh typed K0 Height186→forward415/430 physical traces.
Generic K1 synthetic-row diagnostics cover negative prepared/normalization
routes; they are not typed Processed theorem witnesses. All normal entries
use true ordinary capacity and disjoint layouts. No generated pool/rows are
initialized for415/430. Coefficient banks are exact Gaussian prepared values,
not asserted canonical retained spectrum values or full Fourier witnesses.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import json,sys,hashlib,random
ROOT=Path(__file__).resolve().parents[1];BASE=ROOT/'logs/uniform-bytecode/forward-matching-factor'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
programs=json.loads((BASE/'programs.json').read_text())
specs=json.loads((BASE/'specs.json').read_text())
B=1_000_000;C,TNEG,P,V,MU,CONJ,POOL=200000,210000,220000,230000,240000,240001,250000
assert len(programs['body'])==415 and len(programs['reload'])==430 and len(programs['height'])==186

def geometry(spec,dirty):
 K,a,e=[spec[x] for x in ('K','a','e')];N=1<<K;G=6*(3*K*N+2*N)+2*a;H=8*K+7
 tape=100+dirty*11;order=tape+5*G+9;directory=order+G+9
 rows=directory+G+12;colors=rows+6*G*H+9;palette=colors+2*G*H+9;records=palette+20
 borrowed=records+3*H+10;selected=borrowed+G+4;ids=selected+6*G+4;mapped=ids+2*G+4
 v=G+a+e+7;perm=mapped+6*G+4;widths=perm+v+4;markers=widths+v+4;axis=markers+v+4
 translated=axis+10;slot=translated+6*G+10;offset=3+dirty;ambient=offset+v+5
 return dict(K=K,a=a,e=e,N=N,G=G,H=H,tape=tape,order=order,directory=directory,
 rows=rows,colors=colors,palette=palette,records=records,borrowed=borrowed,selected=selected,
 ids=ids,mapped=mapped,v=v,source=2,target=v-a-2,perm=perm,widths=widths,markers=markers,
 axis=axis,translated=translated,slot=slot,offset=offset,ambient=ambient)

def height_header(p,en):return [p[k] for k in ('K','a','e','tape','order','directory','rows','colors','palette','records')]+[C,int(en),P]
def fresh(spec,D,dirty):
 p=geometry(spec,dirty);rng=random.Random(dirty)
 s=dict(pc=0,nat=[rng.randrange(37) for _ in range(5100)],nh={0:71,B-1:13},
 sh={B-1:scalar(D,3,-7,True)},sr={i:scalar(D,F(i-5,17),F(7-i,13),i%2) for i in range(140)},
 out={2:scalar(D,19,-11)[0]},roots=[D,1])
 s['nat'][1050:1063]=height_header(p,spec['enabled'])
 for j,row in enumerate(spec['typed']):
  for f,x in enumerate(row):s['nh'][p['tape']+5*j+f]=x
 for j,x in enumerate(spec['order']):s['nh'][p['order']+j]=x
 for j,x in enumerate(spec['offsets']):s['nh'][p['directory']+j]=x
 for q in range(p['rows'],p['slot']+5):s['nh'][q]=(q*13+dirty)%B
 values={};R=7*p['N']
 for j in range(R):
  re,im=(F(0),F(0)) if j==0 else (F(j-2-dirty,3),F(5-j+dirty,7))
  for base,x,y in [(C,re,im),(TNEG,-re,-im),(V,re,-im)]:s['sh'][base+j]=scalar(D,x,y);values[base+j]=(x,y)
 constants=[F(1),F(-1),F(1,p['N']),F(-1,p['N']),F(5,4),F(4,5)]
 for j,x in enumerate(constants):s['sh'][P+j]=scalar(D,x);values[P+j]=(x,F(0))
 for j,(re,im) in enumerate([(F(1,2),F(1,2)),(F(1,2),F(-1,2)),(F(1),F(-1)),(F(0),F(1)),(F(1),F(1))],1):s['sh'][j]=scalar(D,re,im)
 for j in range(9*p['ambient']):s['sh'][POOL+j]=scalar(D,17+j,-13,True)
 s['sh'][MU]=scalar(D,5,-3,True);s['sh'][CONJ]=scalar(D,-11,7,True)
 s['sh'][100000]=scalar(D,F(7,11),F(-3,13),True)
 return s,p,values

def check_height(s,p,spec):
 for d,sl in enumerate(spec['slices']):
  rd=p['rows']+6*p['G']*d;cd=p['colors']+2*p['G']*d
  assert [s['nh'][p['records']+3*d+f] for f in range(3)]==[len(sl['rows']),rd,cd]
  assert [[s['nh'][rd+3*i+f] for f in range(3)] for i in range(len(sl['rows']))]==sl['rows']
  assert [s['nh'][cd+i] for i in range(len(sl['colors']))]==sl['colors']

def configure(s,p,en,d,color,reload):
 args=[p[k] for k in ('v','source','target','borrowed','selected','ids','mapped','perm','widths','markers','axis','slot','translated','offset')]+[POOL,p['ambient'],MU,CONJ,V,TNEG]
 s['nat'][4410:4430]=args;s['nat'][4440:4453]=height_header(p,en)
 if reload:s['nat'][1050:1063]=[p[k] for k in ('K','a','e','tape','order','directory','rows','colors','palette','records')]+[C,int(not en),P]
 for i,x in enumerate([0,int(en),0,d,color]):s['nh'][p['slot']+i]=x
 s['pc']=0

def expected_rows(p,sl,color):
 selected=[row for row,c in zip(sl['rows'],sl['colors']) if c==color]
 used={q for q in range(p['v']) if p['source']<=q<p['source']+p['e'] or p['target']<=q<p['target']+p['a']}
 borrowed=[q for q in range(p['v']) if q not in used][:p['G']]
 def location(q):
  if q<p['e']:return p['source']+q
  if q<p['e']+1+p['G']:return borrowed[q-p['e']-1]
  return p['target']+q-p['e']-1-p['G']
 return [[p['offset']+location(d),p['offset']+location(t),co] for d,t,co in selected]

def expected_pool(p,rs,values,D):
 out=[scalar(D,1) for _ in range(9*p['ambient'])]
 for d,t,co in rs:
  re,im=values[co];kap=1+re*re+im*im;rr,ri=re-kap,im;norm=rr*rr+ri*ri
  left=[scalar(D,F(5,4)/kap),scalar(D,F(4,5)*kap),scalar(D,F(5,4)*rr/norm,-F(5,4)*ri/norm),
   scalar(D,F(4,5)*rr,F(4,5)*ri),scalar(D,-3),scalar(D,2),scalar(D,F(-1,8)),scalar(D,1),scalar(D,1,-1)]
  right=[scalar(D,1) for _ in range(6)]+[scalar(D,F(-1,6)),scalar(D,0,1),scalar(D,1,1)]
  for lane in range(9):out[lane*p['ambient']+d]=left[lane];out[lane*p['ambient']+t]=right[lane]
 return out

def check(s,old,p,rs,values,D):
 assert s['nat'][894]==len(rs)
 assert [[s['nh'][p['translated']+3*i+f] for f in range(3)] for i in range(len(rs))]==rs
 exp=expected_pool(p,rs,values,D)
 assert [s['sh'][POOL+j] for j in range(9*p['ambient'])]==exp
 assert s['out']==old['out'] and s['roots']==old['roots']
 assert all(s['nat'][q]==old['nat'][q] for q in range(100,107))
 for q,x in old['sh'].items():
  if not(POOL<=q<POOL+9*p['ambient'] or q in (MU,CONJ)):assert s['sh'][q]==x
 for q,x in old['nh'].items():
  if q<p['borrowed'] or q>=p['translated']+6*p['G'] and not p['slot']<=q<p['slot']+5:assert s['nh'][q]==x

cases=[];coverage={k:set() for k in ('body','reload','height')};total=0
for sid,spec in enumerate(specs):
 for D in (4,12):
  for dirty in (0,1):
   base,p,values=fresh(spec,D,dirty);before=deepcopy(base)
   ticks,seen,peak=execute(programs['height'],base,B,2_000_000,D);check_height(base,p,spec)
   assert base['sh']==before['sh'] and base['sr']==before['sr'];coverage['height'].update(seen);total+=ticks
   slots=[(d,c) for d,sl in enumerate(spec['slices']) for c in sorted(set(sl['colors']))]+[(0,10)]
   for depth,color in slots:
    for kind in ('body','reload'):
     s=deepcopy(base);configure(s,p,spec['enabled'],depth,color,kind=='reload');old=deepcopy(s)
     rs=expected_rows(p,spec['slices'][depth],color)
     budget=4*p['K']+180*p['v']+45*p['ambient']+136*len(rs)+(163 if kind=='reload' else 148)
     steps,pcs,peak=execute(programs[kind],s,B,budget,D);check(s,old,p,rs,values,D)
     assert s['pc']==(429 if kind=='reload' else 414);coverage[kind].update(pcs);total+=steps
     cases.append(dict(origin='fresh actual typed K0 cross→actual186→consumer',spec=sid,D=D,dirty=dirty,
      kind=kind,depth=depth,color=color,M=len(rs),ticks=steps,capacityLayout=True,canonicalSpectrum=False))
# Honest generic physical-row diagnostic: this is not typed Processed.
generic={'K':1,'a':1,'e':1,'enabled':True,'typed':[],'order':[],'offsets':[],'slices':[]}
for D in (4,12):
 for dirty in (0,1):
  for kind,flip in [(kind,flip) for kind in ('body','reload') for flip in (False,True)]:
   s,p,values=fresh(generic,D,dirty)
   W=[[0,2,C],[4,3,TNEG],[6,5,P+2],([7,p['e']+1+p['G'],P+1] if flip else [p['e']+1+p['G'],7,P+1])];rd=p['rows']+6*p['G'];cd=p['colors']+2*p['G']
   for i,row in enumerate(W):
    for f,x in enumerate(row):s['nh'][rd+3*i+f]=x
    s['nh'][cd+i]=0
   for f,x in enumerate([len(W),rd,cd]):s['nh'][p['records']+3+f]=x
   configure(s,p,True,1,0,kind=='reload');old=deepcopy(s);rs=expected_rows(p,{'rows':W,'colors':[0]*4},0)
   budget=4*p['K']+180*p['v']+45*p['ambient']+136*len(rs)+(163 if kind=='reload' else 148)
   steps,pcs,peak=execute(programs[kind],s,B,budget,D);check(s,old,p,rs,values,D)
   coverage[kind].update(pcs);total+=steps
   cases.append(dict(origin='generic synthetic physical rows, not typed Processed',D=D,dirty=dirty,kind=kind,M=4,ticks=steps,capacityLayout=True))
controls=[]
def control(name,mutate,budget=1_000_000,mutate_code=None,semantic=False):
 spec=next(x for x in specs if x['a']==1 and x['e']==1 and x['enabled'])
 base,p,values=fresh(spec,12,1);execute(programs['height'],base,B,2_000_000,12)
 d=next(i for i,sl in enumerate(spec['slices']) if any(row[2]>=C and row[2]<TNEG for row in sl['rows']))
 color=spec['slices'][d]['colors'][0];s=deepcopy(base);configure(s,p,True,d,color,True);old=deepcopy(s)
 rs=expected_rows(p,spec['slices'][d],color);mutate(s,p,rs);code=deepcopy(programs['reload'])
 if mutate_code:mutate_code(code)
 try:
  execute(code,s,B,budget,12)
  if semantic:check(s,old,p,rs,values,12)
 except (AssertionError,KeyError) as err:controls.append(dict(name=name,reason=str(err)));return
 raise AssertionError('control accepted '+name)
control('missingSlotField',lambda s,p,r:s['nh'].pop(p['slot']+2))
control('missingGeneratedHeightRecord',lambda s,p,r:s['nh'].pop(p['records']+3*next(i for i,sl in enumerate(next(x for x in specs if x['a']==1 and x['e']==1 and x['enabled'])['slices']) if any(C<=row[2]<TNEG for row in sl['rows']))))
control('missingPreparedCoefficient',lambda s,p,r:s['sh'].pop(r[0][2]))
control('preparedSourceTagViolation',lambda s,p,r:s['sh'].__setitem__(r[0][2],(s['sh'][r[0][2]][0],True)))
control('wordGuard',lambda s,p,r:s['nat'].__setitem__(4440,B+1))
control('chargedBudget',lambda s,p,r:None,budget=10)
control('mutatedCoefficientHeaderCopy',lambda s,p,r:None,mutate_code=lambda c:c.__setitem__(11,['add',1060,4443,4453]),semantic=True)
for kind in ('body','reload'):
 assert coverage[kind]==set(range(len(programs[kind]))),(kind,sorted(set(range(len(programs[kind])))-coverage[kind]))
result=dict(status='PASS_EXACT',exactCases=len(cases),typedCases=sum('typed K0' in x['origin'] for x in cases),genericCases=sum('generic' in x['origin'] for x in cases),positiveMatchingCases=sum(x['M']>0 for x in cases),controls=controls,totalSteps=total,
 pcCoverage={k:len(v) for k,v in coverage.items()},scopes=['actual typed K0 a/e four combinations plus bothenabled bank production','generic K1 physical rows only, not a typed Processed witness','Gaussian prepared coefficient bank boundary; not canonical retained spectrum/startup','ordinary capacity/disjoint layout holds; arbitrary tagged outside scalar banks retained','no global scheduler, inverse/broadcast phase or child execution claim'],cases=cases,
 engineSHA256=hashlib.sha256((ROOT/'scripts/uniform_seed_cyclotomic_engine.py').read_bytes()).hexdigest())
(BASE/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','exactCases','typedCases','genericCases','positiveMatchingCases','totalSteps','pcCoverage')}))
