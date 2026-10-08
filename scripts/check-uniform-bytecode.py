#!/usr/bin/env python3
"""Export current Lean programs and run exact cyclotomic/tag/word diagnostics."""
from pathlib import Path
import argparse, subprocess, sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--skip-build',action='store_true',help='Use already built Lean component libraries')
a=p.parse_args();root=Path(__file__).resolve().parents[1]
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
for name,receipt in [('dag-depth','fixtures.json'),('sector-packing','bytecode-results.json')]:
    (root/'logs/uniform-bytecode'/name).mkdir(parents=True,exist_ok=True)
    (root/'logs/uniform-bytecode'/name/receipt).unlink(missing_ok=True)
if not a.skip_build:
    subprocess.run(['lake','build','UniformDyadicConvolutionMachine','UniformInitialTraversalPreparation','UniformCRTTransferMachine','UniformZeroFreeDiagonalMachine','UniformPreparedZeroFreeDAGMachine','UniformContiguousPowerBankMachine','UniformSectorMetadataMachine','UniformRankKernelMachine','UniformKernelSpectrumMachine','UniformToeplitzCrossTopologyMachine','UniformDAGDepthMachine','UniformSectorPackingMachine'],cwd=root/'lean',check=True,stdout=subprocess.DEVNULL)
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

for module,name,script in [('KernelSpectrum','kernel-spectrum','uniform-kernel-spectrum-bytecode-fixtures.py'),('CrossTopology','cross-topology','uniform-cross-topology-bytecode-fixtures.py'),('DAGDepth','dag-depth','uniform-dag-depth-bytecode-fixtures.py'),('SectorPacking','sector-packing','uniform-sector-packing-bytecode-fixtures.py')]:
    with (root/'logs/uniform-bytecode'/name/'export.log').open('w') as log:
        subprocess.run(['lake','env','lean',f'../verification/Export{module}Bytecode.lean'],cwd=root/'lean',check=True,stdout=log)
    subprocess.run([sys.executable,str(root/'scripts'/script)],cwd=root,check=True)
