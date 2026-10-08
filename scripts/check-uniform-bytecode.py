#!/usr/bin/env python3
"""Export current Lean programs and run exact cyclotomic/tag/word diagnostics."""
from pathlib import Path
import argparse, subprocess, sys, hashlib, json
from datetime import datetime, timezone
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--skip-build',action='store_true',help='Use already built Lean component libraries')
a=p.parse_args();root=Path(__file__).resolve().parents[1]
# Bind the run to its exact inputs, including the Lean program definitions.
inputs = set(root.glob('scripts/uniform*.py')) | set(root.glob('scripts/check-uniform*.py'))
inputs |= set(root.glob('verification/Export*Bytecode.lean'))
inputs |= set(root.glob('verification/fixtures/*.json'))
inputs |= set(root.glob('lean/Uniform*.lean'))
input_hashes = {str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(inputs)}

(root/'logs/uniform-bytecode').mkdir(parents=True,exist_ok=True)
(root/'logs/uniform-bytecode/fixtures.json').unlink(missing_ok=True)
(root/'logs/uniform-bytecode/zero-free-fixtures.json').unlink(missing_ok=True)
(root/'logs/uniform-bytecode/prepared-zero-free-fixtures.json').unlink(missing_ok=True)
(root/'logs/uniform-bytecode/contiguous-power-fixtures.json').unlink(missing_ok=True)
(root/'logs/uniform-bytecode/sector-metadata-fixtures.json').unlink(missing_ok=True)
(root/'logs/uniform-bytecode/rank-kernel-fixtures.json').unlink(missing_ok=True)
for name,receipt in [('kernel-spectrum','cyclotomic-fixtures.json'),('cross-topology','runtime-receipt.json')]:
    (root/'logs/uniform-bytecode'/name).mkdir(parents=True,exist_ok=True)
    (root/'logs/uniform-bytecode'/name/receipt).unlink(missing_ok=True)
for name,receipt in [('dag-depth','fixtures.json'),('sector-packing','bytecode-results.json'),('dag-bucket','fixtures.json'),('replay-coefficient','fixtures.json'),('greedy-color','fixtures.json'),('cross-shear','bytecode-results.json'),('matching-axis','fixtures.json'),('rank-cross-preparation','cyclotomic-fixtures.json'),('color-layer','fixtures.json'),('cross-depth','bytecode-results.json'),('rank-cross-replay','cyclotomic-fixtures.json'),('inverse-shear','fixtures.json')]:
    (root/'logs/uniform-bytecode'/name).mkdir(parents=True,exist_ok=True)
    (root/'logs/uniform-bytecode'/name/receipt).unlink(missing_ok=True)

for name,receipt in [('cross-height','bytecode-results.json'),('scalar-replay','fixtures.json'),('chunk-rows','cyclotomic-fixtures.json'),('seed-rank-cross','fixtures.json'),('seed-rank-cross','engine-check.json'),('dirty-replay','fixtures.json')]:
    (root/'logs/uniform-bytecode'/name).mkdir(parents=True,exist_ok=True)
    (root/'logs/uniform-bytecode'/name/receipt).unlink(missing_ok=True)
for name,receipt in [('machine-conjugation','fixtures.json'),('conjugate-local','runtime-receipt.json'),('chunk-matching','fixtures.json'),('seed-height','fixtures.json'),('seed-conjugate','runtime-receipt.json'),('seed-chunk','fixtures.json'),('matching-packing','fixtures.json')]:
    (root/'logs/uniform-bytecode'/name).mkdir(parents=True,exist_ok=True)
    (root/'logs/uniform-bytecode'/name/receipt).unlink(missing_ok=True)
if not a.skip_build:
    subprocess.run(['lake','build','UniformDyadicConvolutionMachine','UniformInitialTraversalPreparation','UniformCRTTransferMachine','UniformZeroFreeDiagonalMachine','UniformPreparedZeroFreeDAGMachine','UniformContiguousPowerBankMachine','UniformSectorMetadataMachine','UniformRankKernelMachine','UniformKernelSpectrumMachine','UniformToeplitzCrossTopologyMachine','UniformDAGDepthMachine','UniformSectorPackingMachine','UniformDAGBucketMachine','UniformReplayCoefficientMachine','UniformGreedyColorMachine','UniformCrossShearTableMachine','UniformMatchingAxisTableMachine','UniformRankCrossPreparationMachine','UniformColorLayerTableMachine','UniformCrossDepthReplayPreparation','UniformRankCrossReplayPreparationMachine','UniformInverseShearTableMachine','UniformCrossHeightPreparationMachine','UniformScalarReplayMachine','UniformChunkPortMachine','UniformChunkRowTableMachine','UniformSeedRankCrossPreparation','UniformDirtyReplayMachine','UniformMachineConjugation','UniformConjugateLocalPreparation','UniformChunkMatchingPreparation','UniformSeedHeightPreparation','UniformSeedConjugatePreparation','UniformSeedChunkPreparation','UniformMatchingPackingPreparation'],cwd=root/'lean',check=True,stdout=subprocess.DEVNULL)
subprocess.run(['lake','env','lean','../verification/ExportUniformBytecode.lean'],cwd=root/'lean',check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-bytecode-fixtures.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-zero-free-bytecode-fixtures.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-prepared-zero-free-bytecode-fixtures.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-contiguous-power-bytecode-fixtures.py')],cwd=root,check=True)

with (root/'logs/uniform-bytecode/sector-metadata-export.log').open('w') as log:
    subprocess.run(['lake','env','lean','../verification/ExportSectorMetadataBytecode.lean'],cwd=root/'lean',check=True,stdout=log)
subprocess.run([sys.executable,str(root/'scripts/uniform-sector-metadata-bytecode-fixtures.py')],cwd=root,check=True)

with (root/'logs/uniform-bytecode/rank-kernel-export.log').open('w') as log:
    subprocess.run(['lake','env','lean','../verification/ExportRankKernelBytecode.lean'],cwd=root/'lean',check=True,stdout=log)
subprocess.run([sys.executable,str(root/'scripts/uniform-rank-kernel-bytecode-fixtures.py')],cwd=root,check=True)

for module,name,script in [('KernelSpectrum','kernel-spectrum','uniform-kernel-spectrum-bytecode-fixtures.py'),('CrossTopology','cross-topology','uniform-cross-topology-bytecode-fixtures.py'),('DAGDepth','dag-depth','uniform-dag-depth-bytecode-fixtures.py'),('SectorPacking','sector-packing','uniform-sector-packing-bytecode-fixtures.py'),('DAGBucket','dag-bucket','uniform-dag-bucket-bytecode-fixtures.py'),('ReplayCoefficient','replay-coefficient','uniform-replay-coefficient-bytecode-fixtures.py'),('GreedyColor','greedy-color','uniform-greedy-color-bytecode-fixtures.py'),('CrossShear','cross-shear','uniform-cross-shear-bytecode-fixtures.py'),('MatchingAxis','matching-axis','uniform-matching-axis-bytecode-fixtures.py'),('RankCrossPreparation','rank-cross-preparation','uniform-rank-cross-preparation-bytecode-fixtures.py'),('ColorLayer','color-layer','uniform-color-layer-bytecode-fixtures.py'),('CrossDepth','cross-depth','uniform-cross-depth-bytecode-fixtures.py'),('RankCrossReplay','rank-cross-replay','uniform-rank-cross-replay-bytecode-fixtures.py'),('InverseShear','inverse-shear','uniform-inverse-shear-bytecode-fixtures.py'),('CrossHeight', 'cross-height', 'uniform-cross-height-bytecode-fixtures.py'),('ScalarReplay', 'scalar-replay', 'uniform-scalar-replay-bytecode-fixtures.py'),('ChunkRows', 'chunk-rows', 'uniform-chunk-rows-bytecode-fixtures.py'),('SeedRankCross', 'seed-rank-cross', 'uniform-seed-rank-cross-bytecode-fixtures.py'),('DirtyReplay', 'dirty-replay', 'uniform-dirty-replay-bytecode-fixtures.py')]:
    with (root/'logs/uniform-bytecode'/name/'export.log').open('w') as log:
        subprocess.run(['lake','env','lean',f'../verification/Export{module}Bytecode.lean'],cwd=root/'lean',check=True,stdout=log)
    if name=='cross-depth':
        with (root/'logs/uniform-bytecode'/name/'typed-export.log').open('w') as log:
            subprocess.run(['lake','env','lean','../verification/ExportCrossDepthTypedBytecode.lean'],cwd=root/'lean',check=True,stdout=log)
    if name=='seed-rank-cross':
        subprocess.run([sys.executable,str(root/'scripts/check-uniform-seed-cyclotomic-engine.py')],cwd=root,check=True)
    subprocess.run([sys.executable,str(root/'scripts'/script)],cwd=root,check=True)

for module,name in [('MachineConjugation','machine-conjugation'),('ConjugateLocal','conjugate-local'),('ChunkMatching','chunk-matching'),('SeedHeight','seed-height'),('SeedConjugate','seed-conjugate'),('SeedChunk','seed-chunk'),('MatchingPacking','matching-packing')]:
    with (root/'logs/uniform-bytecode'/name/'export.log').open('w') as log:
        subprocess.run(['lake','env','lean',f'../verification/Export{module}Bytecode.lean'],cwd=root/'lean',check=True,stdout=log)
    subprocess.run([sys.executable,str(root/'scripts'/f'uniform-{name}-bytecode-fixtures.py')],cwd=root,check=True)

receipt_paths = [
    'logs/uniform-bytecode/fixtures.json',
    'logs/uniform-bytecode/zero-free-fixtures.json',
    'logs/uniform-bytecode/prepared-zero-free-fixtures.json',
    'logs/uniform-bytecode/contiguous-power-fixtures.json',
    'logs/uniform-bytecode/sector-metadata-fixtures.json',
    'logs/uniform-bytecode/rank-kernel-fixtures.json',
    'logs/uniform-bytecode/kernel-spectrum/cyclotomic-fixtures.json',
    'logs/uniform-bytecode/cross-topology/runtime-receipt.json',
    'logs/uniform-bytecode/dag-depth/fixtures.json',
    'logs/uniform-bytecode/sector-packing/bytecode-results.json',
    'logs/uniform-bytecode/dag-bucket/fixtures.json',
    'logs/uniform-bytecode/replay-coefficient/fixtures.json',
    'logs/uniform-bytecode/greedy-color/fixtures.json',
    'logs/uniform-bytecode/cross-shear/bytecode-results.json',
    'logs/uniform-bytecode/matching-axis/fixtures.json',
    'logs/uniform-bytecode/rank-cross-preparation/cyclotomic-fixtures.json',
    'logs/uniform-bytecode/color-layer/fixtures.json',
    'logs/uniform-bytecode/cross-depth/bytecode-results.json',
    'logs/uniform-bytecode/rank-cross-replay/cyclotomic-fixtures.json',
    'logs/uniform-bytecode/inverse-shear/fixtures.json',
    'logs/uniform-bytecode/cross-height/bytecode-results.json',
    'logs/uniform-bytecode/scalar-replay/fixtures.json',
    'logs/uniform-bytecode/chunk-rows/cyclotomic-fixtures.json',
    'logs/uniform-bytecode/seed-rank-cross/fixtures.json',
    'logs/uniform-bytecode/dirty-replay/fixtures.json',
    'logs/uniform-bytecode/machine-conjugation/fixtures.json',
    'logs/uniform-bytecode/conjugate-local/runtime-receipt.json',
    'logs/uniform-bytecode/chunk-matching/fixtures.json',
    'logs/uniform-bytecode/seed-height/fixtures.json',
    'logs/uniform-bytecode/seed-conjugate/runtime-receipt.json',
    'logs/uniform-bytecode/seed-chunk/fixtures.json',
    'logs/uniform-bytecode/matching-packing/fixtures.json',
]
records = []
for relative in receipt_paths:
    f=root/relative
    d=json.loads(f.read_text())
    assert d['status']=='PASS',relative
    if relative.endswith('/uniform-bytecode/fixtures.json'):
        count=len(d['cases'])+len(d['empty_startup_cases'])+len(d['transfer_cases'])
    elif '/rank-kernel-fixtures.json' in relative:
        count=d['actual_prepared_source_cases']
    elif '/conjugate-local/' in relative:
        count=d['successful_cases']
    elif '/seed-conjugate/' in relative:
        count=d['successfulCases']
    else:
        count=d.get('exactCases',d.get('caseCount',d.get('cases')))
    if isinstance(count,list): count=len(count)
    assert isinstance(count,int) and count>0,(relative,count)
    records.append(dict(receipt=relative,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),cases=count,status='PASS'))
engine_path='logs/uniform-bytecode/seed-rank-cross/engine-check.json'
engine=json.loads((root/engine_path).read_text())
assert engine['status']=='PASS'
assert all(hashlib.sha256((root/f).read_bytes()).hexdigest()==h for f,h in input_hashes.items()),'Input changed during run'
receipt=dict(schema='exact-uniform-bytecode-diagnostics/v1',status='PASS',created_utc=datetime.now(timezone.utc).isoformat(),command='python3 scripts/check-uniform-bytecode.py',exact_cases=sum(r['cases'] for r in records),records=records,source_sha256=input_hashes,uniform_algorithm_verified=False,scope='Bounded exact instruction diagnostics complement universal Lean proofs; fixture entry boundaries and cached-reference provenance are stated in each receipt. No full uniform fast-DFT claim.',auxiliary_checks=[dict(receipt=engine_path,sha256=hashlib.sha256((root/engine_path).read_bytes()).hexdigest(),status='PASS',dyadic_arithmetic_comparisons=engine['dyadicRandomComparisons'],actual_empty_startup_steps=engine['actualEmpty935DyadicComparisonSteps'])])
(root/'verification/uniform-bytecode-components.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(f"PASS: {len(records)} diagnostic suites, {receipt['exact_cases']} exact cases; inputs unchanged.")
