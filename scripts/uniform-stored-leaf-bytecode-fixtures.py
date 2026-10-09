"""Actual stored-node82 with retained [pool,radix] loads and both leaf orientations."""
from pathlib import Path
from copy import deepcopy
import hashlib,json,sys
R=Path(__file__).resolve().parents[1];P=R/'logs/uniform-bytecode/operational-kernels/stored-leaf-bytecode'
sys.path.insert(0,str(R/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
CODE=json.loads((P/'program.json').read_text());assert len(CODE)==82

def fresh(v,o,A,r,D):
 s=dict(pc=0,nat=[(17*i+31)%233 for i in range(5630)],nh={a:(19*a+7)%71 for a in range(40000)},
        sh={1:scalar(4,7,-5,True),40000:scalar(4,-11,13)},
        sr={i:scalar(4,i+1,-i,True) for i in range(108)},out={7:scalar(4,11,-3)[0]},roots=[4,12])
 for a,b in ((5600,700),(5601,900),(5602,D),(5603,30000)):s['nat'][a]=b
 for j,w in enumerate([v,o,0,17,1,1300,0]):s['nh'][700+j]=w
 s['nh'][900]=A;s['nh'][901]=r
 return s

def reference(v,o,K):
 out=[]
 for i in reversed(range(v)):
  out.extend((0,o+i,o+i,K))
  for j in range(i):out.extend((1,o+i,o+j,K+i-j))
 return out

cases=[];pcs=set();ticks=0
for v in list(range(18))+[31,32,33,64]:
 for o in (0,7,1000):
  for A in (17,5000):
   for D in (9000,10000,15000):
    r=max(v,1)+7;K=A+3*r;s=fresh(v,o,A,r,D);old=deepcopy(s)
    words=reference(v,o,K);expected=deepcopy(old['nh'])
    expected.update({D+j:w for j,w in enumerate(words)})
    cost=34*(v+v*(v-1)//2)+37
    records=[words[j:j+4] for j in range(0,len(words),4)]
    reversedWords=[w for tag,dst,src,coef in reversed(records) for w in (tag,src,dst,coef)]
    expected.update({30000+j:w for j,w in enumerate(reversedWords)})
    steps,seen,peak=execute(CODE,s,50000,cost,4)
    assert steps==cost and s['pc']==81 and s['nat'][5414]==D+len(words) and s['nat'][5514]==30000+len(words)
    assert s['nh']==expected,(v,o,A,r,D)
    assert all(s['nh'][700+j]==old['nh'][700+j] for j in range(7))
    assert all(s['nh'][900+j]==old['nh'][900+j] for j in range(2))
    for name in ('sh','sr','out','roots'):assert s[name]==old[name],name
    written=set(range(5400,5405))|set(range(5410,5419))|set(range(5500,5505))|set(range(5510,5520))|set(range(5610,5615))
    for j in range(5630):
     if j not in written:assert s['nat'][j]==old['nat'][j],j
    pcs.update(seen);ticks+=steps;assert peak<=50000
    cases.append(dict(width=v,offset=o,poolBase=A,radix=r,kernelBase=K,destination=D,steps=steps))
assert pcs==set(range(82)),pcs
controls=[]
for fail in ('width','offset','pool','radix','wordBound','fuel'):
 s=fresh(4,1000,5000,11,9000)
 if fail in ('width','offset','pool','radix'):del s['nh'][dict(width=700,offset=701,pool=900,radix=901)[fail]]
 if fail=='wordBound':
  s['nh']={a:v for a,v in s['nh'].items() if a<=30003};s['sh']={a:v for a,v in s['sh'].items() if a<=30003}
 try:execute(CODE,s,30003 if fail=='wordBound' else 50000,376 if fail=='fuel' else 50000,4)
 except (AssertionError,KeyError):controls.append(fail)
 else:raise AssertionError('invalid run accepted: '+fail)
paths=[R/'lean/UniformStoredDirectLeafOrientations.lean',R/'verification/ExportStoredLeafBytecode.lean',P/'program.json',Path(__file__),R/'scripts/uniform_seed_cyclotomic_engine.py']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,pcCoverage=sorted(pcs),controls=controls,
 sourceHashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
 scope='Actual82 continuous stored7wordleaf/[pool,radix] reader→forward/transpose descriptors. Generic physical leaf record and original directory cells are entry inputs; no full cache/globalDFT witness.')
(P/'fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))
