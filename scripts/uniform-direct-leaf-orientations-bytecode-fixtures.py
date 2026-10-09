"""Execute literal68 and independently render the direct lower-Toeplitz topology."""
from pathlib import Path
from copy import deepcopy
import hashlib,json,sys
R=Path(__file__).resolve().parents[1];P=R/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(R/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,execute
CODE=json.loads((P/'direct-orientations-program.json').read_text());assert len(CODE)==68

def fresh(v,o,K,A):
 s=dict(pc=0,nat=[(17*i+31)%233 for i in range(5530)],nh={a:(19*a+7)%71 for a in range(16000)},
        sh={1:scalar(4,7,-5,True),20000:scalar(4,-11,13)},
        sr={i:scalar(4,i+1,-i,True) for i in range(108)},out={7:scalar(4,11,-3)[0]},roots=[4,12])
 for a,b in ((5400,v),(5401,o),(5402,K),(5403,A),(5404,20000)):s['nat'][a]=b
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
  for K in (17,5000):
   for A in (0,77,9000):
    s=fresh(v,o,K,A);old=deepcopy(s);words=reference(v,o,K);expected=deepcopy(old['nh'])
    expected.update({A+j:w for j,w in enumerate(words)})
    cost=34*(v+v*(v-1)//2)+23
    records=[words[j:j+4] for j in range(0,len(words),4)]
    reversedWords=[w for tag,dst,src,coef in reversed(records) for w in (tag,src,dst,coef)]
    expected.update({20000+j:w for j,w in enumerate(reversedWords)})
    steps,seen,peak=execute(CODE,s,30000,cost,4)
    assert steps==cost and s['pc']==67 and s['nat'][5414]==A+len(words) and s['nat'][5514]==20000+len(words)
    assert s['nh']==expected,(v,o,K,A)
    for name in ('sh','sr','out','roots'):assert s[name]==old[name],name
    for r in range(5530):
     if r not in set(range(5410,5419))|set(range(5500,5505))|set(range(5510,5520)):assert s['nat'][r]==old['nat'][r],r
    pcs.update(seen);ticks+=steps;assert peak<=30000
    cases.append(dict(width=v,offset=o,kernelBase=K,destination=A,steps=steps))
assert pcs==set(range(68)),pcs
controls=[]
for fail in ('wordBound','fuel'):
 s=fresh(4,1000,5000,9000)
 if fail=='wordBound':
  s['nh']={a:v for a,v in s['nh'].items() if a<=20003}
  s['sh']={a:v for a,v in s['sh'].items() if a<=20003}
 try:execute(CODE,s,9003 if fail=='wordBound' else 30000,362 if fail=='fuel' else 30000,4)
 except (AssertionError,KeyError):controls.append(fail)
 else:raise AssertionError('invalid run accepted: '+fail)
paths=[R/'lean/UniformDirectLeafDescriptorMachine.lean',R/'lean/UniformTransposeDescriptorMachine.lean',R/'lean/UniformDirectLeafOrientationsMachine.lean',R/'verification/ExportDirectLeafOrientationsBytecode.lean',
       P/'direct-orientations-program.json',Path(__file__),R/'scripts/uniform_seed_cyclotomic_engine.py']
receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,pcCoverage=sorted(pcs),controls=controls,
 sourceHashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
 scope='Actual68 continuous forward-leaf printer, charged count/header derivation and reverse/swapped-endpoint transpose printer; exact retained coefficient references. This does not verify the cache consumer or global DFT.')
(P/'direct-orientations-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))
