#!/usr/bin/env python3
"""Reproduce focused exact operational tests; the all-length theorem remains open."""
from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,os,re
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-operational-foundations';D.mkdir(parents=True,exist_ok=True)
suites=[
 ('UniformBinarySpectatorCMachine','SpectatorC','closeout-kernels/spectator-fixtures.json','uniform-spectator-c-bytecode-fixtures.py',840),
 ('UniformNativeScalarRecordMachine','NativeScalarRecord','closeout-kernels/native-scalar-fixtures.json','uniform-native-scalar-record-bytecode-fixtures.py',3840),
 ('UniformNativeExchangeRecordMachine','NativeExchangeRecord','closeout-kernels/native-exchange-fixtures.json','uniform-native-exchange-record-bytecode-fixtures.py',1152),
 ('UniformDirectLeafDescriptorMachine','DirectLeafDescriptor','closeout-kernels/direct-leaf-fixtures.json','uniform-direct-leaf-descriptor-bytecode-fixtures.py',396),
 ('UniformDirectLeafOrientationsMachine','DirectLeafOrientations','closeout-kernels/direct-orientations-fixtures.json','uniform-direct-leaf-orientations-bytecode-fixtures.py',396),
 ('UniformGlobalTensorDiagonalLoop','TensorDiagonal','operational-kernels/tensor-bytecode/fixtures.json','uniform-tensor-diagonal-bytecode-fixtures.py',288),
 ('UniformAllSectorTransposeMachine','SectorTranspose','operational-kernels/transpose-bytecode/fixtures.json','uniform-sector-transpose-bytecode-fixtures.py',8544),
 ('UniformProducedSectorTransposePreparation','ProducedSectorTranspose','operational-kernels/produced-transpose-bytecode/fixtures.json','uniform-produced-sector-transpose-bytecode-fixtures.py',864)]
mods=json.loads((R/'verification/uniform-operational-modules.json').read_text())['modules']
paths={Path(__file__).resolve(),R/'verification/uniform-operational-modules.json',R/'scripts/uniform_seed_cyclotomic_engine.py',R/'scripts/uniform-physical-inverse-fixtures.py',R/'lean/lean-toolchain',R/'lean/lakefile.lean',R/'lean/lake-manifest.json',R/'lean/UPSTREAM_MANIFEST.json'}
pending=[R/'lean'/(m+'.lean') for m in mods]+[R/'verification'/('Export'+s[1]+'Bytecode.lean') for s in suites]+[R/'verification/ExportSectorPaddingPreparationBytecode.lean']
paths.update(R/'scripts'/s[3] for s in suites)
while pending:
 p=pending.pop()
 if p in paths:continue
 paths.add(p)
 for line in re.findall(r'^import (.+)$',p.read_text(),re.M):
  for im in line.split():
   q=R/'lean'/(im.replace('.','/')+'.lean')
   if q.is_file():pending.append(q)
hashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
print('host=mac cwd='+str(R)+' driverPID='+str(os.getpid())+' command=check-uniform-operational-bytecode.py',flush=True)
def run(command,cwd,log):
 p=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/log).write_text(p.stdout)
 assert p.returncode==0,(command,p.stdout[-2000:])
# Regenerate physical sector specifications from the already checked producer.
run(['lake','env','lean','../verification/ExportSectorPaddingPreparationBytecode.lean'],R/'lean','sector-spec-export.log')
records=[]
for module,export,relative,script,expected in suites:
 print('export+test '+module,flush=True)
 run(['lake','env','lean','../verification/Export'+export+'Bytecode.lean'],R/'lean',module+'-export.log')
 run(['python3','scripts/'+script],R,module+'-exact.log')
 f=R/'logs/uniform-bytecode'/relative;raw=json.loads(f.read_text());v=raw.get('summary',raw.get('receipt',raw))
 assert v['status']=='PASS'
 count=v.get('exactCases',v.get('cases'));count=len(count) if isinstance(count,list) else count
 assert count==expected,(module,count,expected)
 records.append(dict(module=module,receipt=str(f.relative_to(R)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),cases=count,matrix_entries=v.get('matrixEntries',0)))
 print('PASS '+module+' cases='+str(count),flush=True)
run(['python3','scripts/uniform-physical-inverse-fixtures.py'],R,'physical-inverse-exact.log')
f=R/'logs/uniform-bytecode/closeout-kernels/physical-inverse-fixtures.json';inv=json.loads(f.read_text())['receipt']
assert inv['status']=='PASS' and inv['matrixEntries']==21845 and inv['dimensions']==8
for path,h in hashes.items():assert hashlib.sha256((R/path).read_bytes()).hexdigest()==h,path
receipt=dict(schema='uniform-operational-bytecode/v1',passed=True,finished_utc=datetime.now(timezone.utc).isoformat(),suites=len(records),exact_cases=sum(r['cases'] for r in records),records=records,inverse=dict(receipt=str(f.relative_to(R)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),matrix_entries=inv['matrixEntries'],dimensions=inv['dimensions']),source_sha256=hashes,uniform_algorithm_verified=False,scope='Focused8 exact bytecode suites and independent physical inverse tensor checks. Full cache, common recursive self-call correctness, all-length DFT, numerical CUDA and performance claims remain open.')
(R/'verification/uniform-operational-bytecode.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS suites='+str(len(records))+' exactCases='+str(receipt['exact_cases'])+' inverseEntries='+str(inv['matrixEntries'])+' frozenInputs='+str(len(hashes)),flush=True)
