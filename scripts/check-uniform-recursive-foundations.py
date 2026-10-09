#!/usr/bin/env python3
"""Reproduce the normal recursive-controller foundations bundle.
This audits component proofs and explicit small bytecode diagnostics. The
complete opcode0/5 numerical handler and all-length uniform theorem remain open.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import os,re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[1];D=R/'logs/uniform-recursive-foundations-promotion-agent-20261009';D.mkdir(parents=True,exist_ok=True)
# Historical component reports remain archived; the current command verifies the closed normal theorem.
import sys
if json.loads((R/'lean/UNIFORM_CHECKS.json').read_text()).get('closed_uniform_algorithm') is not None:
 print('Historical component report preserved; running the current closed-theorem verifier.',flush=True)
 raise SystemExit(subprocess.call([sys.executable,str(R/'scripts/verify-uniform-final.py'),*sys.argv[1:]]))
packet=json.loads((R/'verification/uniform-recursive-foundation-modules.json').read_text());mods=packet['modules'];assert len(mods)==29
reg=json.loads((R/'lean/UNIFORM_CHECKS.json').read_text());assert len(reg['modules'])==341 and reg['closed_uniform_algorithm'] is None
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((R/'lean/UPSTREAM_MANIFEST.json').read_text());assert len(manifest['files'])==51
for it in manifest['files']:assert sha(R/'lean'/it['path'])==it['sha256']
assert (R/'lean/lean-toolchain').read_text().strip()==manifest['lean_toolchain']=='leanprover/lean4:v4.34.1'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R/'lean/.lake/packages/mathlib',text=True).strip()==manifest['mathlib_revision']
env=dict(os.environ);env.pop('LEAN_PATH',None)
leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R/'lean',env=env,text=True).strip()
assert '/logs/' not in leanpath,leanpath
(D/'normal-lean-path.log').write_text(leanpath+'\n')
for file,h in packet['historical_packet_sha256'].items():assert sha(R/file)==h,file
paths={Path(__file__).resolve(),R/'verification/UniformRecursiveFoundationsCensus.lean',R/'verification/uniform-recursive-foundation-modules.json',R/'scripts/uniform_seed_cyclotomic_engine.py'}
paths.update(R/file for file in packet['historical_packet_sha256'])
paths.update(R/'lean'/p for p in ['lakefile.lean','lean-toolchain','lake-manifest.json','UPSTREAM_MANIFEST.json','UNIFORM_CHECKS.json'])
for kind in ('native','residual','padding','terminal'):
 paths.update([R/'verification'/('ExportRecursive'+kind.title()+'Bytecode.lean'),R/'scripts'/('uniform-recursive-'+kind+'-bytecode-fixtures.py')])
pending=[R/'lean'/(m+'.lean') for m in mods]+[R/'lean'/('Check'+m+'Axioms.lean') for m in mods]
while pending:
 p=pending.pop()
 if p in paths:continue
 paths.add(p)
 for line in re.findall(r'^import (.+)$',p.read_text(),re.M):
  for name in line.split():
   q=R/'lean'/(name.replace('.','/')+'.lean')
   if q.is_file():pending.append(q)
for row in packet['source_copies']:assert sha(R/'lean'/(row['module']+'.lean'))==row['sha256'],row['module']
for m in mods:
 text=(R/'lean'/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(?:maxRecDepth|maxHeartbeats|synthInstance.maxHeartbeats)',text),m
hashes={str(p.relative_to(R)):sha(p) for p in sorted(paths)}
(D/'source-freeze.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('host=mac cwd='+str(R/'lean')+' driverPID='+str(os.getpid())+' stop=kill -TERM '+str(os.getpid())+' command=python3 ../scripts/check-uniform-recursive-foundations.py',flush=True)
warnings={}
for m in mods:
 p=subprocess.run(['lake','env','lean','-o',str(R/'lean/.lake/build/lib/lean'/(m+'.olean')),m+'.lean'],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(m+'-default-build.log')).write_text(p.stdout);assert p.returncode==0,(m,p.stdout[-2500:]);warnings[m]=p.stdout.count('warning:')
 print(m+' default normal build PASS warnings='+str(warnings[m]),flush=True)
expected=set()
for m in mods:
 checker=(R/'lean'/('Check'+m+'Axioms.lean')).read_text()
 assert re.findall(r'^#print axioms (\S+)',checker,re.M)==reg['modules'][m]
 expected.update(reg['modules'][m]);expected.update(reg['environment_checks'].get(m,[]))
def check(m):
 p=subprocess.run(['lake','env','lean','Check'+m+'Axioms.lean'],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(m+'-axioms.log')).write_text(p.stdout);assert p.returncode==0,(m,p.stdout[-2500:]);return p.stdout
with ThreadPoolExecutor(max_workers=2) as ex:outputs=list(ex.map(check,mods))
text='\n'.join(outputs);(D/'axioms.log').write_text(text)
results={}
for name in expected:
 match=re.search(re.escape(name)+r"'? depends on axioms:\s*\[([^\]]*)\]",text)
 if match:results[name]={a.strip() for a in match[1].split(',') if a.strip()}
 elif re.search(re.escape(name)+r"'? does not depend on any axioms",text):results[name]=set()
 else:raise AssertionError('Missing axiom output '+name)
for name,axs in results.items():assert axs<={'propext','Quot.sound','Classical.choice'},(name,axs)
print('All29 normal axiom checkers PASS declarations='+str(len(results)),flush=True)
p=subprocess.run(['lake','env','lean',str(R/'verification/UniformRecursiveFoundationsCensus.lean')],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(D/'census.log').write_text(p.stdout);assert p.returncode==0,p.stdout[-2500:]
census=json.loads((D/'census.json').read_text());assert {v['name'] for v in census}==expected and len(census)==packet['declarations']
assert {v['module'] for v in census}==set(mods)
for m in mods:assert sum(v['module']==m for v in census)==packet['declarations_by_module'][m]
suites={};artifacts=[D/'census.json',D/'axioms.log',D/'census.log',D/'normal-lean-path.log']
for kind in ('native','residual','padding','terminal'):
 J=R/'logs/uniform-bytecode/recursive-foundations'/kind;J.mkdir(parents=True,exist_ok=True)
 p=subprocess.run(['lake','env','lean',str(R/'verification'/('ExportRecursive'+kind.title()+'Bytecode.lean'))],cwd=R/'lean',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(kind+'-export.log')).write_text(p.stdout);assert p.returncode==0,(kind,p.stdout[-2500:])
 p=subprocess.run(['python3',str(R/'scripts'/('uniform-recursive-'+kind+'-bytecode-fixtures.py'))],cwd=R,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (D/(kind+'-exact.log')).write_text(p.stdout);assert p.returncode==0,(kind,p.stdout[-2500:])
 result=json.loads((J/'fixtures.json').read_text())['receipt'];assert result['status']=='PASS' and result['uniform_algorithm_verified'] is False
 suites[kind]=result
 for file,h in packet['diagnostic_export_sha256'][kind].items():assert sha(J/file)==h,(kind,file)
 artifacts += [D/(kind+'-export.log'),D/(kind+'-exact.log')]+[J/file for file in packet['diagnostic_export_sha256'][kind]]
 print(kind+' fresh normal exact PASS cases='+str(result['cases']),flush=True)
for file,h in hashes.items():assert sha(R/file)==h,file
artifacts += [D/(m+'-default-build.log') for m in mods]+[D/(m+'-axioms.log') for m in mods]
receipt=dict(schema='uniform-recursive-foundations/v1',passed=True,finished_utc=datetime.now(timezone.utc).isoformat(),modules=mods,declarations=len(census),private_declarations=sum(x['name'].startswith('_private.') for x in census),declarations_by_module=packet['declarations_by_module'],
 axiom_inventory_method='Every defining-module constant using Lean env.getModuleIdxFor? and env.header.moduleNames, including all generated/public/private names and public names outside the defining namespace.',default_proof_limits=True,uniform_algorithm_verified=False,closed_uniform_algorithm=None,
 source_sha256=hashes,historical_packet_sha256=packet['historical_packet_sha256'],artifact_sha256={str(p.relative_to(R)):sha(p) for p in artifacts},upstream_source_files_unmodified=51,mathlib_revision=manifest['mathlib_revision'],normal_lean_path=leanpath,build_warning_counts=warnings,
 exact_suites=suites,exact_cases=sum(v['cases'] for v in suites.values()),exact_steps=sum(v['steps'] for v in suites.values()),
 scope='29 byte-identical normal-path recursive controller foundations: immutable commonProgram placements, native scalar/exchange/Y/marker joins, unit padding controls, raw opcode0 residual entry46, stack/base/self-call interfaces, node record preparation and terminal spectator suffix/value bridge. Numerical residual/gather child and typed complete opcode0/5 handler, stronger recursive IH, full cache/seed/global output and all-length DFT/runtime theorem remain open. Diagnostic continuations/stops and independently prepared low prefixes are explicitly recorded per suite.')
(R/'verification/uniform-recursive-foundations.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS modules=29 closures='+str(len(census))+' exactCases='+str(receipt['exact_cases'])+' frozenInputs='+str(len(hashes))+' warnings='+str(sum(warnings.values())),flush=True)
