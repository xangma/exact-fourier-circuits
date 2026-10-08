import json,random,hashlib
from fractions import Fraction as F
from pathlib import Path
repo=Path(__file__).resolve().parents[1];root=repo/'logs/uniform-bytecode/scalar-replay'
helper=repo/'scripts/uniform-replay-coefficient-bytecode-fixtures.py'
ns={'__file__':str(helper)}
prefix=helper.read_text().split('traces=[];all_pcs=set();total_steps=0')[0]
needle='        elif op==7:'
assert needle in prefix
prefix=prefix.replace(needle,'''        elif op==2:
            r,a=args;address=nr.get(a,0);bound(address)
            if address not in nh:raise Failure('missing Nat source')
            nr[r]=nh[address]
'''+needle)
exec(compile(prefix,str(helper),'exec'),ns)
code=json.loads((root/'program.json').read_text());ns['code']=code
execute=ns['execute'];Failure=ns['Failure'];value=ns['value']
assert len(code)==20
specs=json.loads((root/'specs.json').read_text());assert len(specs)==231

def decode(v):return(F(v[0],v[1]),F(v[2],v[3]),v[4])
def step(rows,data,coef):
 data=data.copy()
 for d,s,q in rows:
  ar,ai,ad=data[d];br,bi,bd=data[s];cr,ci,cd=coef[q];assert not cd
  data[d]=(ar+cr*br-ci*bi,ai+cr*bi+ci*br,ad or bd)
 return data
for M,fam in [(m,f) for m in [128,512,2048] for f in range(7)]:
 rows=[[(7*i+fam)%9,(5*i+fam+1)%9,(i+fam)%7] for i in range(M)]
 data={j:value(F((j*j+fam)%13,3)-2,F((j+2*fam)%11,5)-1,j%3==fam%3) for j in range(9)}
 coef={j:(value(0) if j==0 else value(F(j,7)-F(3,7),F((j+fam)%5,11)-F(2,11))) for j in range(7)}
 enc=lambda z:[z[0].numerator,z[0].denominator,z[1].numerator,z[1].denominator,z[2]]
 specs.append([M,fam,rows,[enc(data[j]) for j in range(9)],[enc(coef[j]) for j in range(7)],[enc(step(rows,data,coef)[j]) for j in range(9)]])
seen=set();traces=[]
for specno,(M,fam,rows,init,coefs,expected) in enumerate(specs):
 data={j:decode(v) for j,v in enumerate(init)};coef={j:decode(v) for j,v in enumerate(coefs)}
 assert step(rows,data,coef)=={j:decode(v) for j,v in enumerate(expected)}
 for layout,(T,C,seed) in enumerate([(120,700,17),(4000,19000,31),(30000,70000,83)]):
  rng=random.Random(seed+specno);B=1000000
  nr={1160:M,1161:T,**{q:rng.randrange(B) for q in range(1162,1169)},1200:991}
  nh={T+3*i+k:(C+v if k==2 else v) for i,row in enumerate(rows) for k,v in enumerate(row)};nh[99]=112
  sh={**data,**{C+j:z for j,z in coef.items()},90000:value(7,9,True)}
  sr={q:value(rng.randrange(11),rng.randrange(13),True) for q in [89,90,91,92,93,94]}
  rn,hn,rs,hs,steps,pcs,halt,writes=execute(nr,nh,sr,sh,B)
  assert steps==16*M+5 and halt==19 and hn==nh
  assert {j:hs[j] for j in range(9)}=={j:decode(v) for j,v in enumerate(expected)}
  assert all(hs[a]==z for a,z in sh.items() if a not in {r[0] for r in rows})
  assert all(rn[q]==v for q,v in nr.items() if q<1162 or q>=1169)
  assert rs[89]==sr[89] and rs[94]==sr[94]
  seen|=pcs;traces.append(dict(M=M,family=fam,layout=layout,steps=steps,origin='fresh Lean Gaussian/tag reference' if specno<231 else 'independent large reference'))
assert seen==set(range(20))
M=1;T=100;C=200;B=4000;nr={1160:M,1161:T};nh={T:0,T+1:1,T+2:C};sh={0:value(3,2,False),1:value(7,1,True),C:value(0)}
_,_,_,out,*_=execute(nr,nh,{},sh,B);assert out[0][:2]==sh[0][:2] and out[0][2]
negative=[]
controls=[('missing table destination',nr,{a:v for a,v in nh.items() if a!=T},sh,B,0),('missing table source',nr,{a:v for a,v in nh.items() if a!=T+1},sh,B,0),('missing table coefficient',nr,{a:v for a,v in nh.items() if a!=T+2},sh,B,0)]
controls +=[(name,nr,nh,{a:v for a,v in sh.items() if a!=q},B,0) for name,q in [('missing scalar destination',0),('missing scalar source',1),('missing scalar coefficient',C)]]
controls += [('data-data product',nr,nh,{**sh,C:value(2,0,True)},B,0),('entry word guard',nr,nh,sh,99,0),('runtime pointer word guard',{1160:1,1161:B}, {B:0},sh,B,0),('missing instruction',nr,nh,sh,B,20)]
for name,n,h,s,b,pc in controls:
 try:execute(n,h,{},s,b,pc)
 except Failure as e:negative.append(dict(name=name,observed=str(e)))
 else:raise AssertionError(name)
report=dict(status='PASS',cases=len(traces),steps=sum(t['steps'] for t in traces),all_pcs=sorted(seen),negative=negative,zero_coefficient_tag_preserved=True,cases_detail=traces,scope='Actual20 from physical scalar/Nat inputs; no continuous inverse/table caller claim',program_sha256=hashlib.sha256((root/'program.json').read_bytes()).hexdigest(),specs_sha256=hashlib.sha256((root/'specs.json').read_bytes()).hexdigest())
(root/'fixtures.json').write_text(json.dumps(report,indent=2)+'\n');print({k:v for k,v in report.items() if k!='cases_detail'})
