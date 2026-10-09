"""Independent exact Gaussian verification of native tensor inverse orientation."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys
R=Path(__file__).resolve().parents[1];sys.path.insert(0,str(R/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,add,mul
D=4;zero=scalar(D);one=scalar(D,1)
a=scalar(D,F(1,2),F(1,2));b=scalar(D,F(1,2),F(-1,2))
C=((a,b),(b,a));CI=((b,a),(a,b))
for i in range(2):
 for j in range(2):
  out=zero
  for t in range(2):out=add(out,mul(CI[i][t],C[t][j]))
  assert out==(one if i==j else zero)
def entry(q,x,y,inverse=False):
 out=one;M=CI if inverse else C
 for i in range(q):out=mul(out,M[(x>>i)&1][(y>>i)&1])
 return out
cases=[];entries=0
for q in range(8):
 T=2**q
 for x in range(T):
  for y in range(T):
   assert entry(q,x,y,True)==entry(q,x^(T-1),y)
   entries+=1
 cases.append(dict(bits=q,entries=T*T,mask=T-1))
P=R/'logs/uniform-bytecode/closeout-kernels';P.mkdir(parents=True,exist_ok=True)
paths=[R/'lean/UniformPhysicalBinaryInverse.lean',R/'lean/UniformNativeCopiedInverse.lean',Path(__file__),R/'scripts/uniform_seed_cyclotomic_engine.py']
receipt=dict(status='PASS',uniform_algorithm_verified=False,dimensions=len(cases),matrixEntries=entries,
 sourceHashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
 scope='Independent exactPhi4 inverse tensor entries q0..7 and positive-child/low-q-XOR identity. No executed recursive machine or global DFT claim.')
(P/'physical-inverse-fixtures.json').write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))
