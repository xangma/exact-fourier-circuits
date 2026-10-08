from pathlib import Path
import copy, hashlib, json, sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar, execute
HERE=ROOT/'logs/uniform-bytecode/xor-table'
CODES={name:json.loads((HERE/(name+'.json')).read_text()) for name in ('bitProgram','tableProgram','lookupProgram')}
assert [len(CODES[k]) for k in CODES]==[18,38,5]

def fresh(salt,B):
 return dict(pc=0,nat=[(17*i+salt)%min(B+1,97) for i in range(3500)],
  nh={0:7,3:11},sh={2:scalar(4,3,2,True)},sr={0:scalar(4,-2,1,True)},
  out={1:scalar(4,2,-3)[0]},roots=[4,12])

def fixed_frame(before,s,changed):
 for key in ('sh','sr','out','roots'):assert s[key]==before[key],key
 for r in range(3500):
  if r not in changed:assert s['nat'][r]==before['nat'][r],r

cases=[];lookup_cases=0;ticks=0;covered=set();lookup_covered=set()
TABLE_WRITES={3400,3401,3402,3403,3404,3405,3406,3407,3409,3410,3411,3422,3423,3424,3425,3426,3427,3428,3430}
for q in range(7):
 N=2**q
 for base in (7,1000):
  for salt in (0,31):
   B=max(97,base+N*N)
   s=fresh(salt,B);s['nat'][3420]=q;s['nat'][3421]=base
   # Deliberately dirty every future table entry; producer must replace all.
   for j in range(N*N):s['nh'][base+j]=(7*j+salt)%97
   before=copy.deepcopy(s)
   budget=4*q+10+(12*q+15)*N*N
   count,pcs,peak=execute(CODES['tableProgram'],s,B,budget,4)
   assert count==budget and s['pc']==37
   for a in range(N):
    for b in range(N):assert s['nh'][base+a*N+b]==a^b,(q,a,b)
   for address,value in before['nh'].items():
    if not base<=address<base+N*N:assert s['nh'][address]==value
   fixed_frame(before,s,TABLE_WRITES)
   assert s['nat'][3423]==N and s['nat'][3428]==N*N
   ticks+=count;covered.update(pcs)
   cases.append(dict(q=q,base=base,salt=salt,steps=count,maximumWord=peak))
   # Component lookup headers are ordinary caller inputs. The table is the
   # preceding real producer's heap. No host-computed table is installed.
   for a in range(N):
    for b in range(N):
     s['pc']=0
     s['nat'][3440]=base;s['nat'][3441]=N;s['nat'][3442]=a;s['nat'][3443]=b
     before_lookup=copy.deepcopy(s)
     count,pcs,peak=execute(CODES['lookupProgram'],s,B,5,4)
     assert count==5 and s['nat'][3446]==a^b and s['pc']==4
     assert s['nh']==before_lookup['nh']
     fixed_frame(before_lookup,s,{3444,3445,3446})
     ticks+=count;lookup_cases+=1;lookup_covered.update(pcs)
assert covered==set(range(38)),sorted(set(range(38))-covered)
assert lookup_covered==set(range(5))
controls=[]
def reject(name,code,s,B,fuel):
 try:execute(CODES[code],s,B,fuel,4)
 except (AssertionError,KeyError):controls.append(name);return
 raise AssertionError('accepted negative control: '+name)
s=fresh(0,97);s['nat'][3420]=2;s['nat'][3421]=7
reject('one step short of actual producer cost','tableProgram',s,97,4*2+10+(12*2+15)*16-1)
s=fresh(0,97);s['nat'][3420]=3;s['nat'][3421]=90
reject('table address exceeds bound','tableProgram',s,97,10000)
s=fresh(0,97);s['nat'][3440]=7;s['nat'][3441]=4;s['nat'][3442]=1;s['nat'][3443]=2
reject('missing physically produced lookup entry','lookupProgram',s,97,5)
s=fresh(0,97);s['pc']=13;s['nat'][3423]=0
reject('zero divisor in real header instruction','tableProgram',s,97,4)
s=fresh(0,97);s['pc']=6;s['nat'][3407]=0
reject('zero modulus in real bit instruction','bitProgram',s,97,4)
result=dict(status='PASS',producerCases=len(cases),lookupCases=lookup_cases,
 exactCases=len(cases)+lookup_cases,chargedSteps=ticks,coveredPCs=sorted(covered),
 lookupCoveredPCs=sorted(lookup_covered),negativeControls=controls,cases=cases,
 scope='Actual exported fixed38 q-bit XOR producer, dirty Nat table overwrite, exact integer XOR oracle, scalar/input-dependence/root/output frames and bounded words. Actual generated table consumed by exported lookup5; ordinary lookup headers installed as stated component entry inputs. No global saving recursion or all-length DFT claim.',
 hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),*HERE.glob('*Program.json'),ROOT/'lean/UniformXorTableMachine.lean',ROOT/'lean/UniformNatBlockMachine.lean',ROOT/'lean/UniformXorWordBounds.lean']})
(HERE/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','producerCases','lookupCases','exactCases','chargedSteps','negativeControls')}))
