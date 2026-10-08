#!/usr/bin/env python3
"""Actual whole722 from original H/G/master. No phase host writes or ready intermediates."""
from pathlib import Path
import copy,json
from uniform_cyclotomic_engine import Poly,F,scalar,execute,direct_dft
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/rank-cross-preparation'
code=json.loads((P/'program.json').read_text());models=json.loads((P/'models.json').read_text())
assert len(code)==722 and all(i[0] not in ['root','input','output','unsupported'] for i in code)
budgets={tuple(v[:-1]):v[-1] for v in json.loads((P/'runtime-budgets.json').read_text())}
assert len(budgets)==52
cases=[];coverage=set();total=0;saved=None
for model in models:
 K,a,e=model['height'],model['a'],model['e'];N=2**K;D=4*N;m=2*N;G=3*K*N//2;convG=3*K*N+2*N
 eta=Poly(m,{1:1});omega=eta**4;rows=model['rows'];T=6*convG+2*a;assert len(rows)==T
 for (S,A,d,C,V,tape,depth) in [(1000,2000,30000,10000,40000,100000,200000),(2000,4000,70000,20000,100000,300000,400000)]:
  for seed in [17,99]:
   B=10**10;H,GB=10,200;j0=seed%2;split=j0+e+1;i0=split+1;hSize=i0+a;gSize=split+2
   h=[Poly(m) if seed==99 else eta**((seed+2*j)%D)*Poly(m,{0:F(j+1,3)}) for j in range(hSize)]
   g=[Poly(m) if seed==99 else eta**((seed+3*j)%D)*Poly(m,{0:F(2-j,5)}) for j in range(gSize)]
   s={'pc':0,'nat':[19*j+7 for j in range(850)],'sr':{j:scalar(m,j-2,3-j,j%2) for j in range(70)},
     'nh':{50000:17,900000:37},'sh':{900000:scalar(m,-7,3,True)},
     'out':{0:Poly(m,{0:3,m//2:-5}),7:Poly(m,{m//2:1})},'roots':[D,31,1]}
   headers={104:D,480:H,481:hSize,482:GB,483:gSize,484:a,485:e,486:i0,487:j0,488:split,490:S,
     525:K,527:A,528:d,529:C,563:V,564:tape,675:depth}
   for r,v in headers.items():s['nat'][r]=v
   s['nat'][489]=777;s['nat'][526]=333;s['nat'][670]=19
   s['sh'][0]=(eta,False)
   for j,v in enumerate(h):s['sh'][H+j]=(v,False)
   for j,v in enumerate(g):s['sh'][GB+j]=(v,False)
   for q in range(S,S+6*N):s['sh'][q]=scalar(m,q-3,11-q,True)
   for q in range(C,C+7*N+1):s['sh'][q]=scalar(m,q-3,11-q,True)
   RA=A+N+G+5*N+4
   fftBudget=A+(100*(N+G+K+1)**2+200)+(d+3*G)+(RA+5)+(d+4*G+(A+N)+42)+199
   specBudget=fftBudget+S+C+7*N+600
   crossBudget=V+tape+5*(7*convG+2*a)+(100*(N+G+K+1)**2+200)+10000*(N+convG+a+e+K+1)**2
   assert H+hSize<=S and GB+gSize<=S and S+6*N<=A and RA+1<=C and specBudget<=B
   assert V+5*convG<=tape and crossBudget<=B and tape+5*T<=depth and depth+e+1+T<=B
   before=copy.deepcopy(s)
   steps,pcs=execute(code,s,B,10**7,m)
   assert steps<=budgets[(K,a,e,S,A,d,C,V,tape,depth,seed)]
   def matrix(i,j):
    acc=Poly(m)
    for u in range(split-(j0+j)):acc=acc+h[i0+i-(j0+j)-u]*g[u]
    return acc
   v=[-h[i0+i-split] for i in range(a)]
   w=[g[split-(j0+j)] for j in range(e)]
   row=[matrix(0,j)-v[0]*w[j] for j in range(e)]
   col=[Poly(m) if i==0 else matrix(i,0)-v[i]*w[0] for i in range(a)]
   delta=[Poly(m,{0:1})]+[Poly(m) for _ in range(N-1)]
   kernels=[[(arr[j] if j<len(arr) else Poly(m),False) for j in range(N)] for arr in [w,v,row,delta,delta,col]]
   for b in range(6):
    for j in range(N):assert s['sh'][S+b*N+j]==kernels[b][j]
   expected=[(omega**j,False) for j in range(N)]
   for k in kernels:expected.extend(direct_dft(omega,k))
   assert [s['sh'][C+j] for j in range(7*N)]==expected
   assert s['sh'][C+7*N]==(omega,False) and s['sh'][0]==before['sh'][0]
   for j,r in enumerate(rows):assert [s['nh'].get(tape+5*j+k) for k in range(5)]==r,(K,a,e,j,r)
   labels=[0]*(e+1)
   for j,r in enumerate(rows):
    op,left,right,kind,payload=r;assert left<e+1+j and (op==2 or right<e+1+j)
    labels.append((max(labels[left],labels[right]) if op<2 else labels[left])+1)
   assert max(labels)<=8*K+6
   assert [s['nh'].get(depth+j) for j in range(e+1+T)]==labels
   assert s['pc']==721 and s['nat'][489]==N and s['nat'][526]==S and s['nat'][670]==0
   for r in range(850):
    if 100<=r<=106 or r in headers or 676<=r:assert s['nat'][r]==before['nat'][r]
   for q in list(range(H,H+hSize))+list(range(GB,GB+gSize)):assert s['sh'][q]==before['sh'][q]
   assert s['out']==before['out'] and s['roots']==before['roots']
   for q in set(before['sh'])|set(s['sh']):
    if (q<S or S+6*N<=q) and (q<A or RA+1<=q) and (q<C or C+7*N+1<=q):assert s['sh'].get(q)==before['sh'].get(q)
   for q in set(before['nh'])|set(s['nh']):
    if (q<d or d+3*G<=q) and (q<V or V+5*convG<=q) and (q<tape or tape+5*T<=q) and (q<depth or depth+e+1+T<=q):assert s['nh'].get(q)==before['nh'].get(q)
   total+=steps;coverage.update(pcs)
   cases.append({'height':K,'width':N,'a':a,'e':e,'masterOrder':D,'seed':seed,'layout':[S,A,d,C,V,tape,depth],'steps':steps,'gateCount':T,'maximumDepth':max(labels)})
   if K==2 and a==3 and seed==17:saved=(before,m,H,GB,split,j0,S,C,N,depth,expected,labels)
controls=[]
before,m,H,GB,split,j0,S,C,N,depth,expected,labels=saved
for name,address in [('missing-h',H+1),('missing-g',GB+split-j0),('missing-master',0)]:
 bad=copy.deepcopy(before);del bad['sh'][address]
 try:execute(code,bad,10**10,10**7,m)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' was accepted')
bad=copy.deepcopy(before)
for q in range(H,H+before['nat'][481]):bad['sh'][q]=(bad['sh'][q][0],True)
for q in range(GB,GB+before['nat'][483]):bad['sh'][q]=(bad['sh'][q][0],True)
try:execute(code,bad,10**10,10**7,m)
except (AssertionError,KeyError):controls.append('data-data-product')
else:raise AssertionError('data-data product accepted')
mutated=copy.deepcopy(code);mutated[10]=['jump',11]
bad=copy.deepcopy(before)
try:execute(mutated,bad,10**10,10**7,m)
except (AssertionError,KeyError):controls.append('kernel-source-setup-mutation')
else:
 assert [bad['sh'][C+j] for j in range(7*N)]!=expected;controls.append('kernel-source-setup-mutation')
mutated=copy.deepcopy(code);mutated[683]=['jump',684]
bad=copy.deepcopy(before);execute(mutated,bad,10**10,10**7,m)
assert [bad['nh'].get(depth+j) for j in range(len(labels))]!=labels;controls.append('depth-count-setup-mutation')
result={'status':'PASS','instructions':722,'exactCases':len(cases),'totalChargedSteps':total,'visitedPCs':len(coverage),
 'unvisitedPCs':sorted(set(range(722))-coverage),'negativeControls':controls,'cases':cases,
 'arithmetic':'Exact Fraction coefficients in Q[eta]/(eta^m+1), canonical dyadic eta, D=2m=4N',
 'scope':'One continuous whole722 from original H/G/master and ordinary headers. Initial489/526/670 garbage; no ready kernels/spectra/tape/depth, no phase host writes. Typed rows independently exported from actual crossDAG; depth evaluated independently.'}
(P/'cyclotomic-fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','instructions','exactCases','totalChargedSteps','visitedPCs','negativeControls']},indent=2))
