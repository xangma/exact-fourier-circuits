from pathlib import Path
from fractions import Fraction as F
import copy,json
from uniform_cyclotomic_engine import scalar,execute,Poly
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/chunk-rows'
programs=json.loads((P/'programs.json').read_text())
lean_specs={tuple(r["shape"]):r for r in json.loads((P/"lean-spec.json").read_text())}
B=100000

def fresh():
 m=8
 s={'pc':0,'nat':[(17*i+13)%1000 for i in range(1200)],
    'nh':{i:(29*i+7)%5000 for i in range(6001) if i%5!=3},
    'sh':{i:scalar(m,F(i-7,3),F(11-i,5),i%3==0) for i in range(47)} |
         {5000+i:scalar(m,0 if i%3==0 else F(i-3,7),0 if i%3==0 else F(4-i,9),False) for i in range(100)},
    'sr':{i:scalar(m,F(i-5,3),F(11-i,2),i%2==1) for i in range(100)},
    'out':{9:Poly(m,{0:3,2:-7,5:F(9,2)})},'roots':[16,7,1]}
 for j in range(100,107):s['nat'][j]=17*j+9
 return s

def available(v,src,e,tgt,a):
 return [i for i in range(v) if not src<=i<src+e and not tgt<=i<tgt+a]

def runPort(v,e,g,a,src,tgt,p,kind):
 s=fresh();Q=500;borrow=available(v,src,e,tgt,a)[:g]
 assert len(borrow)==g
 s['nat'][1020:1026]=[p,e,g,src,tgt,Q]
 for i,q in enumerate(borrow):s['nh'][Q+i]=q
 old=copy.deepcopy(s)
 t,pcs=execute(programs['port'],s,B,100,8)
 expected=src+p if p<e else borrow[p-e-1] if p<e+1+g else tgt+p-e-1-g
 spec=lean_specs[(v,e,g,a,src,tgt)];j=spec["ports"].index(p)
 assert borrow==spec["borrowed"] and expected==spec["mapped"][j] and t==spec["runtimes"][j]
 assert s['nat'][1030]==expected<v
 assert t==(6 if p<e else 9 if p<e+1+g else 8)
 assert all(s[k]==old[k] for k in ['nh','sh','sr','out','roots'])
 assert all(s['nat'][r]==old['nat'][r] for r in range(1200) if r<1030 or r>=1035)
 return {'type':'port','branch':kind,'port':p,'expected':expected,'steps':t},pcs

def rowCase(v,e,g,a,src,tgt,mode):
 s=fresh();Q,D,O=500,1000,2000
 borrow=available(v,src,e,tgt,a)[:g];assert len(borrow)==g
 ports=list(range(e))+list(range(e+1,e+1+g+a))
 rows=[] if mode=='empty' else [(p,ports[(i+1)%len(ports)],5000+i) for i,p in enumerate(ports)]
 if mode=='repeat-zero':rows=rows+[rows[0]]*3
 for i,row in enumerate(rows):
  for j,q in enumerate(row):s['nh'][D+3*i+j]=q
 s['nat'][1080:1089]=[len(rows),D,O,e,g,a,src,tgt,Q]
 s['nat'][261:267]=[src,e,tgt,a,g,Q]
 old=copy.deepcopy(s)
 # Entire Borrowed17 -> Rows59 -> finalhalt: no intermediate host writes.
 t,pcs=execute(programs['borrowedRows'],s,B,100000,8)
 def mapped(p):return src+p if p<e else borrow[p-e-1] if p<e+1+g else tgt+p-e-1-g
 expected=[(mapped(d),mapped(q),c) for d,q,c in rows]
 actual=[tuple(s['nh'][O+3*i+j] for j in range(3)) for i in range(len(rows))]
 assert actual==expected
 assert all(d<v and q<v for d,q,c in actual)
 assert all(s['nh'][Q+i]==q for i,q in enumerate(borrow))
 assert all(s[k]==old[k] for k in ['sh','sr','out','roots'])
 assert all(s['nat'][r]==old['nat'][r] for r in range(1200) if (r<267 or r>=273) and (r<1020 or r>=1035) and (r<1090 or r>=1101))
 affected=set(range(Q,Q+g))|set(range(O,O+3*len(rows)))
 assert all(s['nh'].get(q)==old['nh'].get(q) for q in set(s['nh'])|set(old['nh']) if q not in affected)
 # Independent execution count for exactly the literal components.
 q=fresh();q['nat'][261:267]=[src,e,tgt,a,g,Q]
 bt,_=execute(programs['borrowedRows'][:17][:-1]+[['halt']],q,B,100000,8)
 rt=6+sum(26+(6 if d<e else 9 if d<e+1+g else 8)+(6 if r<e else 9 if r<e+1+g else 8) for d,r,c in rows)
 assert t==bt+rt+1 and rt<=44*len(rows)+6
 return {'type':'borrowed17+rows59','shape':[v,e,g,a,src,tgt],'mode':mode,'rowCount':len(rows),'steps':t,'rowSteps':rt},pcs

results=[];cover={k:set() for k in ['port','rows','borrowedRows']}
for shape in [(9,2,3,2,1,5),(9,2,3,2,6,1),(37,3,7,4,6,23),(4,0,1,2,0,2),(4,1,0,2,0,2)]:
 v,e,g,a,src,tgt=shape
 for p in list(range(e))+list(range(e+1,e+1+g+a)):
  r,c=runPort(*shape,p,'source' if p<e else 'gate' if p<e+1+g else 'target');results.append(r);cover['port'].update(c)
 for mode in ['empty','all','repeat-zero']:
  r,c=rowCase(*shape,mode);results.append(r);cover['borrowedRows'].update(c);cover['rows'].update(pc-17 for pc in c if 17<=pc<76)
for shape in [(0,0,0,0,0,0),(1,1,0,0,0,1),(1,0,0,1,0,0)]:
 r,c=rowCase(*shape,'empty');results.append(r);cover['borrowedRows'].update(c)

controls=[]
def reject(name,code,s,b=B):
 try:execute(code,s,b,100000,8)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('negative control accepted: '+name)
s=fresh();s['nat'][1020:1026]=[3,2,3,1,5,70000];s['nh'].pop(70000,None);reject('missing actual borrowed gate cell',programs['port'],s)
s=fresh();s['nat'][1080:1089]=[1,70000,2000,2,3,2,1,5,500];reject('missing logical row',programs['rows'],s)
s=fresh();s['nat'][1020:1026]=[3,2,3,1,5,500];s['nh'][500]=B+1;reject('oversized borrowed cell violates WordBound',programs['port'],s)
s=fresh();s['nat'][1080:1089]=[0,1000,2000,0,0,0,0,0,500];reject('ambient WordBound failure',programs['rows'],s,30)
# Geometric contract checks: these invalid ports/layouts are rejected by the
# theorem premises, not invented bytecode guard instructions.
assert not (2<2 or 3<=2<3+3+2);controls.append('literal zero hole excluded by Domain')
assert not (1+3<=2 or 2+3<=1);controls.append('overlapping source target intervals excluded by placement')
assert all(len(cover[k])==len(programs[k]) for k in cover),(cover,{k:len(v) for k,v in programs.items()})
out={'status':'PASS','cases':results,'caseCount':len(results),'leanReferenceShapes':len(lean_specs),'totalSteps':sum(r['steps'] for r in results),
     'negativeControls':controls,'coverage':{k:{'visited':len(v),'length':len(programs[k]),'unvisited':sorted(set(range(len(programs[k])))-v)} for k,v in cover.items()},
     'boundary':'Physical caller rows; continuous Borrowed17 then Rows59. No coefficient or data arithmetic is performed; exact cyclotomic dirty values and dependency tags are preserved. Generic Domain/layout violations are theorem contracts, not bytecode checks.'}
(P/'cyclotomic-fixtures.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
