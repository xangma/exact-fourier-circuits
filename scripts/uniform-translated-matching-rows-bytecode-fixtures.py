"""Actual exported direct-batch and translated-row bytecode; exact state checks."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'logs/uniform-bytecode/closeout-kernels'
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import scalar,Poly,execute
def fresh():
    return dict(pc=0,nat=[(13*i+17)%233 for i in range(5010)],
        nh={0:71,9000:37},sh={1:scalar(4,7,-3,True),9999:scalar(4,-13,5)},
        sr={i:scalar(4,F(i+2,7),F(9-i,11),True) for i in range(105)},
        out={7:scalar(4,11,-3)[0]},roots=[4,12])
def finish(name,code,cases,ticks,pcs,controls,paths):
    assert pcs==set(range(len(code))),sorted(set(range(len(code)))-pcs)
    paths=paths+[Path(__file__),ROOT/'scripts/uniform_seed_cyclotomic_engine.py']
    receipt=dict(status='PASS',uniform_algorithm_verified=False,cases=len(cases),steps=ticks,
        pcCoverage=sorted(pcs),controls=controls,
        sourceHashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (P/(name+'-fixtures.json')).write_text(json.dumps(dict(receipt=receipt,cases=cases),indent=2)+'\n')
    print(name,json.dumps({k:v for k,v in receipt.items() if k!='sourceHashes'}))

CODE=json.loads((P/'translated-rows-program.json').read_text());assert len(CODE)==23
assert all(i[0] not in ('root','input','output','rat','getscalar','putscalar','fmul','fdiv','fadd','fsub') for i in CODE)
cases=[];pcs=set();ticks=0
for count in range(13):
 for offset in (0,1,17,500):
  for source in (7,1000):
   for salt in (0,31):
    dest=3000;s=fresh();rows=[]
    for reg,value in ((4990,count),(4991,source),(4992,dest),(4993,offset)):
        s['nat'][reg]=value
    for j in range(count):
        row=((3*j+salt)%97,(11*j+salt+1)%97,(997*j+salt)%10001)
        rows.append(row)
        for k,val in enumerate(row):s['nh'][source+3*j+k]=val;s['nh'][dest+3*j+k]=23+k
    before=deepcopy(s);want=deepcopy(s['nh'])
    for j,row in enumerate(rows):
        want[dest+3*j]=offset+row[0];want[dest+3*j+1]=offset+row[1];want[dest+3*j+2]=row[2]
    steps,seen,peak=execute(CODE,s,10000,19*count+5,4)
    assert steps==19*count+5 and s['pc']==22
    assert s['nh']==want
    for key in ('sh','sr','out','roots'):assert s[key]==before[key],key
    for reg in range(len(s['nat'])):
        if not 4994<=reg<=5002:assert s['nat'][reg]==before['nat'][reg],reg
    pcs.update(seen);ticks+=steps
    cases.append(dict(rows=count,offset=offset,source=source,salt=salt,runtime=steps,peak=peak))
controls=[]
for missing in (0,1,2):
 s=fresh();s['nat'][4990:4994]=[1,1000,3000,17]
 s['nh'].update({1000:3,1001:5,1002:9000});del s['nh'][1000+missing]
 try:execute(CODE,s,10000,1000,4)
 except (AssertionError,KeyError):controls.append('missingField'+str(missing))
 else:raise AssertionError('missing row field accepted')
finish('translated-rows',CODE,cases,ticks,pcs,controls,[ROOT/'lean/UniformTranslatedMatchingRows.lean',ROOT/'verification/ExportTranslatedMatchingRowsBytecode.lean',P/'translated-rows-program.json'])
