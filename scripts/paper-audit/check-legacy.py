from pathlib import Path
import os,subprocess,json,hashlib,datetime,sys,signal
R=Path(__file__).resolve().parents[2];L=R/'lean';D=R/'logs/paper-audit/legacy';D.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
child=None
def stop(signum,frame):
 global child
 if child is not None and child.poll() is None:
  child.terminate()
  try:child.wait(timeout=10)
  except subprocess.TimeoutExpired:child.kill();child.wait()
 raise SystemExit(128+signum)
for sig in (signal.SIGINT,signal.SIGTERM):signal.signal(sig,stop)
def run(args,**kwargs):
 global child
 child=subprocess.Popen(args,**kwargs)
 result=child.wait();child=None
 if result:raise subprocess.CalledProcessError(result,args)

receipt_path=R/'verification/uniform-final-algorithm.json';receipt=json.loads(receipt_path.read_text())
assert receipt['passed'] and receipt['fresh_project_modules']==1271 and receipt['certified_artifacts_reused']==0
assert str(R/'lean/.lake/build/lib/lean') in receipt['normal_lean_path']
compiler=Path(subprocess.check_output(['lake','env','which','lean'],cwd=L,text=True).strip())
assert sha(compiler)==receipt['compiler_sha256']
env=dict(os.environ);env['LEAN_PATH']=str(D)+':'+receipt['normal_lean_path'];env.pop('LEAN_SRC_PATH',None)
roots=['UniformDiagonal','UniformCRTTransferMachine'];sources={name:sha(L/(name+'.lean')) for name in roots}
sys.path.insert(0,str(R/'scripts'));from uniform_final_verification_core import imports
outside=set()
def visit(name):
 p=L/(name.replace('.','/')+'.lean')
 if name in receipt['normal_project_artifact_sha256'] or name in outside or not p.is_file():return
 outside.add(name)
 for dep in imports(p.read_text()):visit(dep)
for name in roots:visit(name)
assert outside==set(roots),outside
print('HOST',subprocess.check_output(['hostname'],text=True).strip(),'CWD',L,'PID',os.getpid(),'LOG',D,'STOP kill -TERM',os.getpid(),flush=True)
for name in roots:
 with (D/(name+'.log')).open('w') as log:
  run([str(compiler),'-DautoImplicit=false','-R',str(L),'-o',str(D/(name+'.olean')),str(L/(name+'.lean'))],cwd=L,env=env,stdout=log,stderr=subprocess.STDOUT)
source='''import UniformDiagonal
import UniformCRTTransferMachine
import Lean
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mut entries : Array Json := #[]
 for (name, _) in env.constants.toList do
  let origin := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx]!.toString)
  if origin.any (fun m => m == "UniformDiagonal" || m == "UniformCRTTransferMachine") then
   let axs ← collectAxioms name
   for ax in axs do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   entries := entries.push (Json.mkObj [("name",toJson name.toString),("module",toJson origin),("axioms",toJson (axs.toList.map toString))])
 liftIO <| IO.FS.writeFile OUTPUT (Json.compress (.arr entries))
 logInfo m!"Legacy closures {entries.size}"
'''.replace('OUTPUT',json.dumps(str(D/'census.json')))
(D/'Census.lean').write_text(source)
with (D/'census.log').open('w') as log:run([str(compiler),'-DautoImplicit=false','-R',str(D),str(D/'Census.lean')],cwd=L,env=env,stdout=log,stderr=subprocess.STDOUT)
rows=json.loads((D/'census.json').read_text());assert rows and {r['module'] for r in rows}==set(roots)
for name,h in sources.items():assert sha(L/(name+'.lean'))==h
result={'passed':True,'scope':'Two annotated legacy modules outside final theorem closure; fresh builds and all defining-module closures, including private. Dependencies bound to the separately fresh final receipt.','finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':sources,'compiler_sha256':sha(compiler),'canonical_receipt_sha256':sha(receipt_path),'driver_sha256':sha(Path(__file__)),'artifact_sha256':{str(p.relative_to(R)):sha(p) for p in [D/(name+'.olean') for name in roots]+[D/'census.json',D/'census.log']},'declarations':len(rows),'private_declarations':sum(r['name'].startswith('_private.') for r in rows),'standard_axioms_only':True}
(R/'verification/paper-legacy-check.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS legacy:',len(rows),'closures',flush=True)
