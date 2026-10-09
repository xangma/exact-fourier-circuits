#!/usr/bin/env python3
"""Reproduce the focused frozen operational foundation checks; this is not the final theorem."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import re,json,hashlib,subprocess,os
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-operational-foundations';D.mkdir(parents=True,exist_ok=True)
mods=json.load(open(R/'verification/uniform-operational-modules.json'))['modules'];registry=json.load(open(R/'lean/UNIFORM_CHECKS.json'))
assert registry['closed_uniform_algorithm'] is None
manifest=json.load(open(R/'lean/UPSTREAM_MANIFEST.json'));assert len(manifest['files'])==51
for it in manifest['files']:assert hashlib.sha256((R/'lean'/it['path']).read_bytes()).hexdigest()==it['sha256']
assert (R/'lean/lean-toolchain').read_text().strip()==manifest['lean_toolchain']
assert subprocess.check_output(['git','-C',str(R/'lean/.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()==manifest['mathlib_revision']
paths={Path(__file__).resolve(),R/'lean/UNIFORM_CHECKS.json',R/'lean/lakefile.lean',R/'lean/lean-toolchain',R/'lean/UPSTREAM_MANIFEST.json',R/'lean/lake-manifest.json',R/'verification/UniformOperationalCensus.lean',R/'verification/uniform-operational-modules.json'}
pending=[R/'lean'/(m+'.lean') for m in mods]+[R/'lean'/('Check'+m+'Axioms.lean') for m in mods]
while pending:
 p=pending.pop()
 if p in paths:continue
 paths.add(p)
 for line in re.findall(r'^import (.+)$',p.read_text(),re.M):
  for im in line.split():
   q=R/'lean'/(im.replace('.','/')+'.lean')
   if q.is_file():pending.append(q)
hashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
print('host=mac cwd='+str(R/'lean')+' driverPID='+str(os.getpid())+' modules='+str(len(mods)),flush=True)
expected=set()
for m in mods:
 names=registry['modules'][m];checker=(R/'lean'/('Check'+m+'Axioms.lean')).read_text()
 assert re.findall(r'^#print axioms (\S+)',checker,re.M)==names,m
 expected.update(names);expected.update(registry['environment_checks'].get(m,[]))
def check(m):
 p=subprocess.run(['lake','env','lean','Check'+m+'Axioms.lean'],cwd=R/'lean',text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(m+'.log')).write_text(p.stdout);assert p.returncode==0,(m,p.stdout[-1000:]);return p.stdout
with ThreadPoolExecutor(max_workers=4) as ex:outputs=list(ex.map(check,mods))
text='\n'.join(outputs);(D/'axioms.log').write_text(text)
results={}
for m in re.finditer(r"'?([A-Za-z0-9_.@]+)'? depends on axioms:\s*\[([^\]]*)\]",text):
 name,axs=m.groups();results[name]={a.strip() for a in axs.split(',') if a.strip()}
for m in re.finditer(r"'?([A-Za-z0-9_.@]+)'? does not depend on any axioms",text):results[m[1]]=set()
assert set(results)==expected,(set(results)^expected)
for name,axs in results.items():assert axs<={'propext','Quot.sound','Classical.choice'},(name,axs)
p=subprocess.run(['lake','env','lean','../verification/UniformOperationalCensus.lean'],cwd=R/'lean',text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(D/'census.log').write_text(p.stdout);assert p.returncode==0,p.stdout
inventory=json.load(open(D/'census.json'));assert {v['name'] for v in inventory}==expected,({v['name'] for v in inventory}^expected)
for f,h in hashes.items():assert hashlib.sha256((R/f).read_bytes()).hexdigest()==h,f
receipt=dict(schema='uniform-operational-foundations/v1',passed=True,finished_utc=datetime.now(timezone.utc).isoformat(),modules=mods,declarations=len(results),source_sha256=hashes,upstream_files_verified=51,permitted_axioms=['propext','Quot.sound','Classical.choice'],default_proof_limits=True,uniform_algorithm_verified=False,scope=f'Focused normal-path audit of {len(mods)} operational RAM, native inverse, descriptor, forward-factor and tensor/sector modules, inventoried by defining Lean module. Full cache schedule, common recursive self-call correctness and the end-to-end all-length DFT theorem remain open.')
(R/'verification/uniform-operational-foundations.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS modules='+str(len(mods))+' declarations='+str(len(results))+' frozenInputs='+str(len(hashes)),flush=True)
