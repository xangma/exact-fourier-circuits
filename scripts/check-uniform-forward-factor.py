#!/usr/bin/env python3
"""Focused normal-path audit of the stored-forward-slot factor producer.
The earlier enabled-specific Processed/Sources/Constants boundary remains explicit.
This does not verify the complete cache or all-length uniform DFT algorithm.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import os,re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-forward-factor-normal-agent-20261009';D.mkdir(parents=True,exist_ok=True)
# Historical component reports remain archived; the current command verifies the closed normal theorem.
import sys
if json.loads((R/'lean/UNIFORM_CHECKS.json').read_text()).get('closed_uniform_algorithm') is not None:
 print('Historical component report preserved; running the current closed-theorem verifier.',flush=True)
 raise SystemExit(subprocess.call([sys.executable,str(R/'scripts/verify-uniform-final.py'),*sys.argv[1:]]))
J=R/'logs/uniform-bytecode/forward-matching-factor';J.mkdir(parents=True,exist_ok=True)
mods=[m for m in json.loads((R/'verification/uniform-operational-modules.json').read_text())['modules'] if m.startswith('UniformForwardMatchingFactor')];assert len(mods)==11
reg=json.loads((R/'lean/UNIFORM_CHECKS.json').read_text());assert reg['closed_uniform_algorithm'] is None
manifest=json.loads((R/'lean/UPSTREAM_MANIFEST.json').read_text());assert len(manifest['files'])==51
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for it in manifest['files']:assert sha(R/'lean'/it['path'])==it['sha256']
assert (R/'lean/lean-toolchain').read_text().strip()==manifest['lean_toolchain']=='leanprover/lean4:v4.34.1'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R/'lean/.lake/packages/mathlib',text=True).strip()==manifest['mathlib_revision']
paths={Path(__file__).resolve(),R/'scripts/uniform-forward-matching-factor-bytecode-fixtures.py',R/'scripts/uniform_seed_cyclotomic_engine.py',R/'verification/UniformForwardFactorCensus.lean',R/'verification/ExportForwardMatchingFactorBytecode.lean',R/'verification/uniform-operational-modules.json'}
paths.update(R/'lean'/p for p in ['lakefile.lean','lean-toolchain','lake-manifest.json','UPSTREAM_MANIFEST.json','UNIFORM_CHECKS.json'])
pending=[R/'lean'/(m+'.lean') for m in mods]+[R/'lean'/('Check'+m+'Axioms.lean') for m in mods]
while pending:
 p=pending.pop()
 if p in paths:continue
 paths.add(p)
 for line in re.findall(r'^import (.+)$',p.read_text(),re.M):
  for name in line.split():
   q=R/'lean'/(name.replace('.','/')+'.lean')
   if q.is_file():pending.append(q)
for m in mods:
 text=(R/'lean'/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(?:maxRecDepth|maxHeartbeats|synthInstance.maxHeartbeats)',text),m
hashes={str(p.relative_to(R)):sha(p) for p in sorted(paths)}
(D/'source-freeze.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('host=mac cwd='+str(R/'lean')+' driverPID='+str(os.getpid())+' stop=kill -TERM '+str(os.getpid())+' command=python3 ../scripts/check-uniform-forward-factor.py',flush=True)
# lake builds normal module targets and their normal-path imports, with no
# scratch LEAN_PATH. Force source compilation once to avoid cached-only checks.
env=dict(os.environ);env.pop('LEAN_PATH',None)
for m in mods:
 p=subprocess.run(['lake','env','lean','-o',str(R/'lean/.lake/build/lib/lean'/(m+'.olean')),m+'.lean'],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(m+'-default-build.log')).write_text(p.stdout);assert p.returncode==0,(m,p.stdout[-2000:]);assert not p.stdout.strip(),(m,p.stdout)
 print(m+' build PASS',flush=True)
expected=set()
for m in mods:
 checker=(R/'lean'/('Check'+m+'Axioms.lean')).read_text();assert re.findall(r'^#print axioms (\S+)',checker,re.M)==reg['modules'][m]
 expected.update(reg['modules'][m]);expected.update(reg['environment_checks'].get(m,[]))
def check(m):
 p=subprocess.run(['lake','env','lean','Check'+m+'Axioms.lean'],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(m+'-axioms.log')).write_text(p.stdout);assert p.returncode==0,(m,p.stdout[-2000:]);return p.stdout
with ThreadPoolExecutor(max_workers=4) as ex:outputs=list(ex.map(check,mods))
text='\n'.join(outputs);(D/'axioms.log').write_text(text);results={}
for m in re.finditer(r"'?([A-Za-z0-9_.@]+)'? depends on axioms:\s*\[([^\]]*)\]",text):results[m[1]]={a.strip() for a in m[2].split(',') if a.strip()}
for m in re.finditer(r"'?([A-Za-z0-9_.@]+)'? does not depend on any axioms",text):results[m[1]]=set()
assert set(results)==expected,(set(results)^expected)
for name,axs in results.items():assert axs<={'propext','Quot.sound','Classical.choice'},(name,axs)
for source,log in [('verification/UniformForwardFactorCensus.lean','census.log'),('verification/ExportForwardMatchingFactorBytecode.lean','export.log')]:
 p=subprocess.run(['lake','env','lean',str(R/source)],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/log).write_text(p.stdout);assert p.returncode==0,(source,p.stdout[-2500:])
census=json.loads((D/'census.json').read_text());assert {v['name'] for v in census}==expected and len(census)==671
p=subprocess.run(['python3',str(R/'scripts/uniform-forward-matching-factor-bytecode-fixtures.py')],cwd=R,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(D/'exact.log').write_text(p.stdout);assert p.returncode==0,p.stdout[-3000:]
fixtures=json.loads((J/'fixtures.json').read_text());assert fixtures['status']=='PASS_EXACT' and fixtures['exactCases']==384
assert fixtures['typedCases']==368 and fixtures['genericCases']==16
for file,h in hashes.items():assert sha(R/file)==h,file
receipt=dict(schema='uniform-forward-factor-foundations/v1',passed=True,finished_utc=datetime.now(timezone.utc).isoformat(),modules=mods,declarations=len(census),private_declarations=sum(x['name'].startswith('_private.') for x in census),declarations_by_module={m:sum(x['module']==m for x in census) for m in mods},axiom_inventory_method='All defining-module constants using Lean env.getModuleIdxFor? and env.header.moduleNames, including generated/private declarations.',default_proof_limits=True,uniform_algorithm_verified=False,closed_uniform_algorithm=None,
 source_sha256=hashes,artifact_sha256={str(p.relative_to(R)):sha(p) for p in [D/'census.json',D/'axioms.log',D/'census.log',D/'export.log',D/'exact.log',J/'programs.json',J/'specs.json',J/'fixtures.json']},upstream_source_files_unmodified=51,mathlib_revision=manifest['mathlib_revision'],
 exact_cases=fixtures['exactCases'],typed_cases=fixtures['typedCases'],generic_cases=fixtures['genericCases'],positive_matching_cases=fixtures['positiveMatchingCases'],exact_steps=fixtures['totalSteps'],covered_pcs=fixtures['pcCoverage'],negative_controls=fixtures['controls'],diagnostic_scopes=fixtures['scopes'],
 scope='Actual415/430 charged forward-slot→local-v matching→translated endpoints/typed selected coefficients→9factor pool, plus actual tensor-consumer pool contract. Genuine enabled-specific physical Processed, Sources, startup Constants and ordinary allocation remain earlier-producer entries. Generic K1 physical-row diagnostics do not prove a typed K1 Processed producer. Full cache schedule, common child recursion and end-to-end uniform DFT/runtime theorem remain open.')
(R/'verification/uniform-forward-factor-foundations.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS modules='+str(len(mods))+' closures='+str(len(census))+' exactCases='+str(fixtures['exactCases'])+' frozenInputs='+str(len(hashes)),flush=True)
