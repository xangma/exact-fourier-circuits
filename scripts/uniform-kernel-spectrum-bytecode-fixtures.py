"""Exact actual297 with canonical roots of orders4..64; caller kernels, no phase host writes."""
from pathlib import Path
import copy,json
from uniform_cyclotomic_engine import Poly,F,scalar,execute,direct_dft
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/kernel-spectrum'
code=json.loads((P/'program.json').read_text());assert len(code)==297
cases=[];coverage=set();total=0
saved=[]
for K in range(5):
 N=2**K;D=4*N;m=2*N;G=3*K*N//2
 eta=Poly(m,{1:1});omega=eta**4
 for S,A,d,C in [(20,200,1000,10000),(200,1000,20,4000)]:
  for seed in [0,17,31,99]:
   B=10000000
   s={'pc':0,'nat':[(19*j+7)%(B//8+1) for j in range(600)],
      'nh':{j:(31*j+5)%(B//8+1) for j in range(1500)},
      'sr':{j:scalar(m,j-2,3-j,j%2) for j in range(70)},
      'sh':{j:scalar(m,j-3,11-j,j%3!=1) for j in range(16000)},
      'out':{0:Poly(m,{0:3,m//2:-5}),7:Poly(m,{m//2:1})},'roots':[D,31,1]}
   for r,v in {525:K,526:S,527:A,528:d,529:C,104:D}.items():s['nat'][r]=v
   s['sh'][0]=(eta,False)
   values=[[(Poly(m) if seed==99 else eta**((seed+2*i+j)%D)*Poly(m,{0:F(j-2,3)}),False)
           for j in range(N)] for i in range(6)]
   for i in range(6):
    for j in range(N):s['sh'][S+i*N+j]=values[i][j]
   before=copy.deepcopy(s)
   steps,pcs=execute(code,s,B,1000000,m)
   expected=[(omega**j,False) for j in range(N)]
   for v in values:expected.extend(direct_dft(omega,v))
   assert [s['sh'][C+j] for j in range(7*N)]==expected
   assert s['sh'][C+7*N]==(omega,False) and s['sh'][0]==before['sh'][0]
   assert s['pc']==296 and s['nat'][535]==6 and s['nat'][530]==N and s['nat'][538]==G
   for j in range(6*N):assert s['sh'][S+j]==before['sh'][S+j]
   for r in range(600):
    if (100<=r<=106) or (184<=r<530) or 556<=r:assert s['nat'][r]==before['nat'][r]
   assert s['out']==before['out'] and s['roots']==before['roots']
   RA=A+N+G+5*N+4
   for q in set(before['sh'])|set(s['sh']):
    if (q<A or RA+1<=q) and (q<C or C+7*N+1<=q):assert s['sh'].get(q)==before['sh'].get(q)
   for q in set(before['nh'])|set(s['nh']):
    if q<d or d+3*G<=q:assert s['nh'].get(q)==before['nh'].get(q)
   total+=steps;coverage.update(pcs)
   cases.append({'height':K,'width':N,'masterOrder':D,'layout':[S,A,d,C],'seed':seed,'steps':steps})
   if K==2 and seed==17:saved.append((before,m,N,S,A,d,C))
# Contract/mutation controls: physical missing entries, dependence tags, retained copy occurrence.
controls=[]
before,m,N,S,A,d,C=saved[0]
for name,address in [('missing-kernel',S),('missing-master',0)]:
 bad=copy.deepcopy(before);del bad['sh'][address]
 try:execute(code,bad,10000000,1000000,m)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' was accepted')
bad=copy.deepcopy(before);bad['sh'][0]=(bad['sh'][0][0],True)
try:execute(code,bad,10000000,1000000,m)
except (AssertionError,KeyError):controls.append('input-dependent-master')
else:raise AssertionError('dependent master was accepted')
bad=copy.deepcopy(before);bad['sh'][S]=(bad['sh'][S][0],True)
execute(code,bad,10000000,1000000,m)
assert any(bad['sh'][C+N+j][1] for j in range(N));controls.append('kernel-tag-not-prepared')
mutated=copy.deepcopy(code);mutated[254]=['jump',255]
bad=copy.deepcopy(before);execute(mutated,bad,10000000,1000000,m)
assert any(bad['sh'][C+N+j] != s for j,s in enumerate(direct_dft(Poly(m,{1:1})**4,[before['sh'][S+t] for t in range(N)])))
controls.append('copy-store-mutation')
result={'status':'PASS','instructions':297,'exactCases':len(cases),'totalChargedSteps':total,
 'visitedPCs':len(coverage),'unvisitedPCs':sorted(set(range(297))-coverage),'negativeControls':controls,'cases':cases,
 'arithmetic':'Exact Fraction coefficients in Q[eta]/(eta^m+1), canonical dyadic root eta, D=2m=4N',
 'scope':'Single continuous exported literal297 from physical original kernels/master. No phase host writes. Universal Lean theorem is separate primary evidence.'}
(P/'cyclotomic-fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','instructions','exactCases','totalChargedSteps','visitedPCs','negativeControls']},indent=2))
