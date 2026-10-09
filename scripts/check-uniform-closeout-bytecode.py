#!/usr/bin/env python3
"""Reproduce the focused frozen closeout foundation checks; this is not the final theorem."""
from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,os
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-closeout-foundations';D.mkdir(parents=True,exist_ok=True);suites=[['UniformHeapDirectFourier', 'HeapDirectFourier', 'closeout-kernels/direct-fixtures.json', 'uniform-heap-direct-fourier-bytecode-fixtures.py'], ['UniformBinaryBatchCMachine', 'BinaryBatchC', 'closeout-kernels/batch-fixtures.json', 'uniform-binary-batch-c-bytecode-fixtures.py'], ['UniformHeapDirectBatch', 'HeapDirectBatch', 'closeout-kernels/direct-batch-fixtures.json', 'uniform-heap-direct-batch-bytecode-fixtures.py'], ['UniformTranslatedMatchingRows', 'TranslatedMatchingRows', 'closeout-kernels/translated-rows-fixtures.json', 'uniform-translated-matching-rows-bytecode-fixtures.py'], ['UniformSmallAxisFourierMachine', 'SmallAxisFourier', 'closeout-kernels/small-axis-fixtures.json', 'uniform-small-axis-fourier-bytecode-fixtures.py'], ['UniformSmallAxesMachine', 'SmallAxesFourier', 'closeout-kernels/small-axes-fixtures.json', 'uniform-small-axes-fourier-bytecode-fixtures.py'], ['UniformGlobalMatchingDiagonalPreparation', 'MatchingScalePreparation', 'matching-scale-preparation/bytecode/fixtures.json', 'uniform-matching-scale-preparation-bytecode-fixtures.py'], ['UniformProducedSectorPaddingPreparation', 'SectorPaddingPreparation', 'sector-padding-preparation/sector-bytecode/fixtures.json', 'uniform-sector-padding-preparation-bytecode-fixtures.py'], ['UniformResidualGatherPreparation', 'ResidualGatherPreparation', 'residual-gather-preparation/fixtures.json', 'uniform-residual-gather-preparation-bytecode-fixtures.py']]
paths={Path(__file__).resolve(),R/'scripts/check-uniform-bytecode.py'}|set(R.glob('scripts/uniform*.py'))|set(R.glob('verification/Export*Bytecode.lean'))|set(R.glob('lean/Uniform*.lean'))
hashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
print('host=mac cwd='+str(R)+' driverPID='+str(os.getpid())+' command=focused-normal-bytecode.py',flush=True)
records=[]
for module,export,relative,script in suites:
 print('export+test '+module,flush=True)
 for command,cwd in [(['lake','env','lean','../verification/Export'+export+'Bytecode.lean'],R/'lean'),(['python3','scripts/'+script],R)]:
  p=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (D/(module+('-export.log' if cwd.name=='lean' else '-exact.log'))).write_text(p.stdout)
  assert p.returncode==0,(module,command,p.stdout[-2000:])
 f=R/'logs/uniform-bytecode'/relative;raw=json.load(open(f));v=raw.get('summary',raw.get('receipt',raw))
 assert v['status']=='PASS'
 count=v.get('exactCases',v.get('cases'));count=len(count) if isinstance(count,list) else count
 assert isinstance(count,int) and count>0
 records.append(dict(module=module,receipt=str(f.relative_to(R)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),cases=count))
 print('PASS '+module+' cases='+str(count),flush=True)
for path,h in hashes.items():assert hashlib.sha256((R/path).read_bytes()).hexdigest()==h,path
receipt=dict(schema='uniform-closeout-bytecode/v1',passed=True,finished_utc=datetime.now(timezone.utc).isoformat(),suites=len(records),exact_cases=sum(r['cases'] for r in records),records=records,source_sha256=hashes,uniform_algorithm_verified=False,scope='Focused9 newnormalexact-bytecode suites; universalproof entryconditions are stated in each receipt. No complete uniform algorithm, positive-q recursive saving trace, numericalCUDA or performance claim.')
(R/'verification/uniform-closeout-bytecode.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS suites='+str(len(records))+' exactCases='+str(receipt['exact_cases']),flush=True)
