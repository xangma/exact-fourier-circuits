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
if not a.skip_build:
    subprocess.run(['lake','build','UniformDyadicConvolutionMachine','UniformInitialTraversalPreparation','UniformCRTTransferMachine','UniformZeroFreeDiagonalMachine','UniformPreparedZeroFreeDAGMachine','UniformContiguousPowerBankMachine'],cwd=root/'lean',check=True,stdout=subprocess.DEVNULL)
subprocess.run(['lake','env','lean','../verification/ExportUniformBytecode.lean'],cwd=root/'lean',check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-bytecode-fixtures.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-zero-free-bytecode-fixtures.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-prepared-zero-free-bytecode-fixtures.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(root/'scripts/uniform-contiguous-power-bytecode-fixtures.py')],cwd=root,check=True)
