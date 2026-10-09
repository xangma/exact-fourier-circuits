"""Exact actual172 coefficient preparation. Generic matching rows, not a full selected FFT."""
from pathlib import Path
import sys,json,hashlib,random
from fractions import Fraction as F
from copy import deepcopy
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
P=ROOT/'logs/uniform-bytecode/matching-scale-preparation'
PROGRAMS=json.loads((P/'bytecode/programs.json').read_text());CODE=PROGRAMS['continuous172'];B=100000
assert len(CODE)==172
C,T,CONST,V,a,b,pool,c,D,permutation,row=64,128,192,208,256,257,512,1024,5000,6000,7000

def factors(mu):
 one=scalar(mu.D,1)[0];k=one+mu*mu.conjugate();rho=mu-k
 ai=scalar(mu.D,1,-1)[0];imag=scalar(mu.D,0,1)[0]
 return [(scalar(mu.D,F(5,4))[0]*k.inverse(),one),
 (scalar(mu.D,F(4,5))[0]*k,one),(scalar(mu.D,F(5,4))[0]*rho.inverse(),one),
 (scalar(mu.D,F(4,5))[0]*rho,one),(scalar(mu.D,-3)[0],one),
 (scalar(mu.D,2)[0],one),(scalar(mu.D,F(-1,8))[0],scalar(mu.D,F(-1,6))[0]),
 (one,imag),(ai,imag*ai)]

def fresh(order,K,r,edges,lane,seed):
 rng=random.Random(seed);R=7*2**K
 bank=[scalar(order,F((j*11)%17-8,7),F((j*13)%19-9,11))[0] for j in range(R)]
 bank[0]=scalar(order)[0];bank[1]=scalar(order,1)[0];bank[2]=scalar(order,0,1)[0]
 const=[scalar(order,v)[0] for v in [1,-1,F(1,2**K),F(-1,2**K),F(5,4),F(4,5)]]
 s=dict(pc=0,nat=[rng.randrange(200) for _ in range(4400)],nh={19:17,B-1:7},
 sh={0:scalar(order,3,4),B-1:scalar(order,17,-13,True)},
 sr={q:scalar(order,F(q-3,7),F(9-q,11),q%2) for q in range(126)},out={0:scalar(order,19,-17)[0]},roots=[4,1])
 for j in range(R):
  s['sh'][C+j]=(bank[j],False);s['sh'][T+j]=(-bank[j],False);s['sh'][V+j]=(bank[j].conjugate(),False)
 for j in range(6):s['sh'][CONST+j]=(const[j],False)
 aa=scalar(order,F(1,2),F(1,2))[0];imag=scalar(order,0,1)[0];ai=scalar(order,1,-1)[0]
 for j,v in {1:aa,2:aa.conjugate(),3:ai,4:imag,5:imag*ai}.items():s['sh'][j]=(v,False)
 for cell in range(pool,pool+9*r):s['sh'][cell]=scalar(order,cell,-cell,True)
 for cell in range(c,c+r):s['sh'][cell]=scalar(order,-cell,cell,True)
 s['sh'][a]=scalar(order,13,-7,True);s['sh'][b]=scalar(order,-3,17,True)
 # Dirty unrelated scalar data, never read by this coefficient-only program.
 for j in range(350,370):s['sh'][j]=scalar(order,F(j,13),F(-j,17),j%2)
 coeff=[];mus=[];rt=[]
 for i,(dst,src) in enumerate(edges):
  kind=(seed+i)%3
  ix=(seed+7*i)%R if kind<2 else (seed+i)%6
  ptr=[C,T,CONST][kind]+ix
  mu=[bank[ix] if kind==0 else None,-bank[ix] if kind==1 else None,const[ix] if kind==2 else None][kind]
  s['nh'][D+3*i]=dst;s['nh'][D+3*i+1]=src;s['nh'][D+3*i+2]=ptr
  coeff.append((kind,ix));mus.append(mu);rt.append([10,12,9][kind]+105)
 for j in range(r):s['nh'][permutation+j]=(j+1)%max(r,1)
 depth=seed%4
 for j in range(3):s['nh'][row+3*depth+j]=rng.randrange(100)
 for reg,value in {2100:C,2101:T,2102:CONST,2103:V,2106:a,2107:b,2140:D,894:len(edges),
 4380:r,4381:pool,4382:lane,4383:permutation,4384:c,4385:row,4386:depth}.items():s['nat'][reg]=value
 return s,mus,rt,depth

cases=[];covered=set()
for order in [4,8,12]:
 for K in [0,1,2]:
  for r in [0,1,2,3,7,12]:
   for seed in range(6):
    coords=list(range(r));random.Random(seed).shuffle(coords)
    M=min(r//2,seed%4);edges=[(coords[2*i],coords[2*i+1]) for i in range(M)]
    for lane in range(9):
     s,mus,rt,depth=fresh(order,K,r,edges,lane,seed);old=deepcopy(s)
     ticks,pcs,peak=execute(CODE,s,B,54*r+sum(rt)+38,order)
     assert ticks==54*r+sum(rt)+38 and s['pc']==171 and peak<=B
     expected=[scalar(order,1)[0] for _ in range(r)]
     for (dst,src),mu in zip(edges,mus):expected[dst],expected[src]=factors(mu)[lane]
     for ll in range(9):
      allvals=[scalar(order,1)[0] for _ in range(r)]
      for (dst,src),mu in zip(edges,mus):allvals[dst],allvals[src]=factors(mu)[ll]
      assert all(s['sh'][pool+ll*r+j]==(val,False) for j,val in enumerate(allvals))
     assert all(s['sh'][c+j]==(val,False) for j,val in enumerate(expected))
     assert all(s['nh'][permutation+j]==j for j in range(r))
     assert [s['nh'][row+depth*3+j] for j in range(3)]==[r,permutation,c]
     assert s['out']==old['out'] and s['roots']==old['roots']
     assert s['nat'][100:107]==old['nat'][100:107] and s['nat'][4380:4387]==old['nat'][4380:4387]
     assert all(s['nh'][q]==v for q,v in old['nh'].items() if not(permutation<=q<permutation+r or row+3*depth<=q<row+3*depth+3))
     assert all(s['sh'][q]==v for q,v in old['sh'].items() if q not in (a,b) and not(pool<=q<pool+9*r or c<=q<c+r))
     covered.update(pcs);cases.append(dict(D=order,K=K,r=r,M=M,lane=lane,seed=seed,ticks=ticks))
controls=[]

def reject(name,mutate,budget=None):
 s,*_=fresh(12,2,7,[(3,1),(0,6),(5,2)],0,0);mutate(s)
 try:execute(CODE,s,B,100000 if budget is None else budget,12)
 except (AssertionError,KeyError):controls.append(name)
 else:raise AssertionError(name+' accepted')
reject('missing-row-coefficient',lambda s:s['nh'].pop(D+2))
reject('missing-row-right',lambda s:s['nh'].pop(D+1))
reject('missing-positive',lambda s:s['sh'].pop(C))
reject('missing-conjugate',lambda s:s['sh'].pop(V))
reject('unprepared-divisor',lambda s:s['sh'].__setitem__(V,(s['sh'][V][0],True)))
reject('missing-I',lambda s:s['sh'].pop(4))
reject('word-guard',lambda s:s['nat'].__setitem__(4381,B+1))
reject('charged-budget',lambda s:None,1)
assert covered==set(range(172)),set(range(172))-covered
out=dict(status='PASS',exactCases=len(cases),negativeControls=controls,coveredPCs=sorted(covered),
 contracts='Generic disjoint matching rows and genuine prepared Gaussian coefficient/conjugate banks; ordinary layout/bounds hold. Not a complete selected-axis FFT witness.',
 model='Exact Q[eta]/Phi_D for D4,8,12; Gaussian divisors checked by exact inverse-product.',
 programSHA256=hashlib.sha256((P/'bytecode/programs.json').read_bytes()).hexdigest(),cases=cases)
(P/'bytecode/fixtures.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cases'}))
