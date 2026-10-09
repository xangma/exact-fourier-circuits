#!/usr/bin/env python3
"""Fresh, byte-preserving reproduction of the pinned upstream Fourier Main cone."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

if not __debug__:
    raise RuntimeError("Run without Python optimization; verification assertions are required")

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
MAIN = "OAI.Computability.FourierTransform.Main"
FINAL = ["OAI.PowerSaving.transform_main", "OAI.PowerSaving.transform_main_order",
         "OAI.PowerSaving.convolution_main", "OAI.PowerSaving.convolution_main_order"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
COMPILER_SHA256 = "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def artifact_parts(path):
    path = Path(path)
    return [Path(str(path)+suffix) for suffix in [".server", ".private"]] + [
        path.with_suffix(".ir"), path.with_suffix(".ir.sig")]


def lean_code(text):
    """Remove nested comments and strings for bounded import/shortcut discovery."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i):
                depth -= 1; i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("/-", i):
            depth = 1; i += 2
        elif text.startswith("--", i):
            stop = text.find("\n", i)
            i = len(text) if stop < 0 else stop
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: out.append("\n" if text[i] == "\n" else " "); i += 1
        else:
            out.append(text[i]); i += 1
    assert depth == 0, "unterminated source comment"
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-repo", type=Path, required=True,
                        help="Existing local Git object database containing the baseline pin")
    parser.add_argument("--cache-root", type=Path, default=Path(__file__).resolve().parents[1] / "lean",
                        help="Lean project supplying only matching external dependency caches")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] /
                        "logs/upstream-dft-baseline-20261009")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    workspace = output / "workspace"
    if workspace.exists():
        raise RuntimeError("Use a fresh --output: existing workspace must not supply old Fourier oleans")
    src = workspace / "lean"
    build = workspace / "fresh-olean"
    src.mkdir(parents=True); build.mkdir()
    logs = output / "build-logs"; logs.mkdir()
    started = time.monotonic()
    receipt = {"status": "RUNNING", "pin": PIN, "pid": os.getpid(),
               "upstreamObjectDatabase": str(args.upstream_repo.resolve()),
               "workspace": str(workspace), "builds": [], "finalTheorems": FINAL,
               "freshProjectOleans": True, "proofEdits": False, "commandLimitOverrides": False}
    current = None

    def save():
        receipt["elapsedSeconds"] = round(time.monotonic()-started, 3)
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")

    def git(*items):
        return subprocess.check_output(["git", "-C", str(args.upstream_repo), *items])

    def stop(signum, frame):
        if current is not None and current.poll() is None:
            os.killpg(current.pid, signal.SIGTERM)
            try:
                current.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(current.pid, signal.SIGKILL)
                current.wait()
        receipt["status"] = "INTERRUPTED"; save()
        raise SystemExit(128+signum)

    signal.signal(signal.SIGTERM, stop); signal.signal(signal.SIGINT, stop)
    print(f"PID {os.getpid()} workspace {workspace}", flush=True)
    try:
        assert git("rev-parse", PIN+"^{commit}").decode().strip() == PIN
        files, imports, order = {}, {}, []

        def visit(module):
            if module in files: return
            relative = "lean/"+module.replace(".", "/")+".lean"
            data = git("show", PIN+":"+relative)
            files[module] = data
            code = lean_code(data.decode())
            forbidden = re.findall(r"\b(?:sorry|admit|native_decide|axiom)\b", code)
            assert not forbidden, (module, forbidden)
            imports[module] = [name for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", code, re.M)
                               for name in line.split()]
            for dependency in imports[module]:
                if dependency.startswith("OAI."): visit(dependency)
            path = src / (module.replace(".", "/")+".lean")
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data)
            order.append(module)

        visit(MAIN)
        configs = {}
        for name in ["lean-toolchain", "lake-manifest.json", "lakefile.lean"]:
            data = git("show", PIN+":lean/"+name)
            (src/name).write_bytes(data); configs[name] = sha(data)
        agents = {}
        for path in ["AGENTS.md", "lean/AGENTS.md", "lean/OAI/AGENTS.md",
                     "lean/OAI/Computability/AGENTS.md", "lean/OAI/Computability/FourierTransform/AGENTS.md"]:
            exists = subprocess.run(["git", "-C", str(args.upstream_repo), "cat-file", "-e", PIN+":"+path],
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
            if exists:
                data = git("show", PIN+":"+path); agents[path] = data.decode()
                dest=workspace/"instructions"/path; dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(data)
        receipt.update({"modules": order, "moduleCount": len(order), "imports": imports,
                        "sourceSha256Before": {m: sha(data) for m, data in files.items()},
                        "configSha256Before": configs, "baselineInstructions": agents,
                        "upstreamLimitOptions": {m: re.findall(r"set_option\s+(max\w+)\s+([^\s]+)",
                           lean_code(data.decode())) for m,data in files.items()
                           if re.search(r"set_option\s+max", lean_code(data.decode()))}})
        manifest = json.loads((src/"lake-manifest.json").read_text())
        expected = {p["name"]:p["rev"] for p in manifest["packages"] if "rev" in p}
        clean = os.environ.copy(); clean.pop("LEAN_PATH", None)
        path_text = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                     cwd=args.cache_root, env=clean, text=True).strip()
        dependency_paths, pins = [], {}
        for component in path_text.split(os.pathsep):
            path = Path(component).resolve()
            if "/.lake/packages/" not in str(path): continue
            package = next(p for p in path.parents if p.parent.name == "packages")
            name = package.name
            rev = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
            assert expected.get(name) == rev, (name, expected.get(name), rev)
            subprocess.run(["git", "-C", str(package), "diff", "--quiet", "HEAD", "--"], check=True)
            assert not (path/"OAI").exists(), ("unexpected OAI dependency cache", path)
            pins[name] = {"rev":rev,"path":str(path)}; dependency_paths.append(str(path))
        assert "mathlib" in pins
        assert (args.cache_root/"lean-toolchain").read_bytes() == (src/"lean-toolchain").read_bytes()
        compiler = Path(subprocess.check_output(["lake", "env", "which", "lean"],
                        cwd=args.cache_root, env=clean, text=True).strip()).resolve()
        assert file_sha(compiler) == COMPILER_SHA256, "Compiler bytes differ from certified toolchain"
        # Snapshot dependencies before any project build. The later import census
        # selects the actual used modules; no project artifact is in these roots.
        external = {}
        for path in [*(Path(p) for p in dependency_paths), compiler.parent.parent/"lib/lean"]:
            for artifact in sorted(path.rglob("*.olean")):
                module = ".".join(artifact.relative_to(path).with_suffix("").parts)
                assert not module.startswith("OAI."), ("Unexpected project artifact", artifact)
                assert module not in external, ("Ambiguous dependency artifact", module)
                siblings = artifact_parts(artifact)
                external[module] = {"path": str(artifact), "sha256": file_sha(artifact),
                    "parts": {str(part): file_sha(part) for part in siblings if part.is_file()},
                    "missing_parts": [str(part) for part in siblings if not part.exists()]}
        external_path = output/"external-artifacts.json"
        external_path.write_text(json.dumps(external, sort_keys=True, indent=2)+"\n")
        env = clean | {"LEAN_PATH":os.pathsep.join([str(build),*dependency_paths])}
        version = subprocess.check_output([str(compiler), "--version"], cwd=src,env=env,text=True).strip()
        driver_digest = file_sha(__file__)
        receipt.update({"externalCaches":pins,"leanVersion":version,"leanPath":env["LEAN_PATH"],
                        "driverSha256":driver_digest,"compilerSha256":COMPILER_SHA256,
                        "externalArtifactsManifest":str(external_path),
                        "externalArtifactsManifestSha256":file_sha(external_path),
                        "externalArtifactsSnapshotted":len(external)})

        def check_artifacts():
            assert file_sha(compiler) == COMPILER_SHA256, "Compiler changed"
            assert file_sha(__file__) == driver_digest, "Verifier changed during run"
            assert file_sha(external_path) == receipt["externalArtifactsManifestSha256"]
            for module, entry in external.items():
                assert file_sha(entry["path"]) == entry["sha256"], ("Dependency artifact changed", module)
                for path, digest in entry["parts"].items():
                    assert file_sha(path) == digest, ("Dependency artifact part changed", path)
                for path in entry["missing_parts"]:
                    assert not Path(path).exists(), ("Dependency artifact part appeared", path)
            for entry in receipt["builds"]:
                assert file_sha(build/(entry["module"].replace(".","/")+".olean")) == entry["oleanSha256"], entry["module"]
                for path, digest in entry["artifactPartsSha256"].items():
                    assert file_sha(path) == digest, ("Fresh artifact part changed", path)
                for path in entry["missingArtifactParts"]:
                    assert not Path(path).exists(), ("Fresh artifact part appeared", path)

        (output/"driver-source.py").write_bytes(Path(__file__).read_bytes())
        save()
        for index,module in enumerate(order):
            relative=module.replace(".","/")
            dest=build/(relative+".olean"); dest.parent.mkdir(parents=True,exist_ok=True)
            assert not dest.exists()
            command=[str(compiler),"-DautoImplicit=false","-o",str(dest),relative+".lean"]
            log=logs/(module+".log"); t=time.monotonic()
            with log.open("w") as stream:
                current=subprocess.Popen(command,cwd=src,env=env,stdout=stream,stderr=subprocess.STDOUT,
                                         start_new_session=True)
                receipt["active"]={"module":module,"pid":current.pid,"command":command,"log":str(log)}; save()
                result=current.wait()
            receipt["builds"].append({"module":module,"returncode":result,
                "seconds":round(time.monotonic()-t,3),"log":str(log),
                "oleanSha256":sha(dest.read_bytes()) if dest.exists() else None,
                "artifactPartsSha256":{str(p):file_sha(p) for p in artifact_parts(dest) if p.is_file()},
                "missingArtifactParts":[str(p) for p in artifact_parts(dest) if not p.exists()]})
            receipt.pop("active",None); save()
            print(f"{index+1}/{len(order)} {module} exit={result} {time.monotonic()-t:.1f}s",flush=True)
            if result: raise RuntimeError("Unchanged upstream source failed: "+module)
            assert not re.search(r"\bwarning:",log.read_text()), ("Lean warning", module)
        check_artifacts()
        audit=workspace/"FinalAxioms.lean"
        audit.write_text("import "+MAIN+"\n"+"".join("#print axioms "+n+"\n" for n in FINAL))
        def check_file(path,log):
            nonlocal current
            with log.open("w") as stream:
                current=subprocess.Popen([str(compiler),"-DautoImplicit=false",str(path)],cwd=src,env=env,
                                         stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                receipt["active"]={"pid":current.pid,"command":current.args,"log":str(log)}; save()
                result=current.wait()
            receipt.pop("active",None); save()
            assert result==0,(str(path),result)
            assert not re.search(r"\bwarning:",log.read_text()), ("Lean warning", path)
        check_file(audit,output/"final-axioms.log")
        reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(output/"final-axioms.log").read_text())
        assert {n for n,_ in reports}==set(FINAL)
        final_ax={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in reports}
        assert all(set(ax)<=ALLOWED for ax in final_ax.values())
        receipt["finalAxioms"]=final_ax; save()
        census=workspace/"ConeAxioms.lean"
        census.write_text("import "+MAIN+"\nopen Lean Elab Command in\nrun_cmd do\n let env ← getEnv\n let modules : List Name := ["+
            ",".join("`"+m for m in order)+"]\n for module in env.allImportedModuleNames do\n  logInfo m!\"IMPORT {module}\"\n for (name,_) in env.constants.toList do\n  if let some idx := env.getModuleIdxFor? name then\n   let origin := env.allImportedModuleNames[idx.toNat]!\n   if modules.contains origin then\n    let axs ← collectAxioms name\n    logInfo m!\"SOURCE {origin} DECL {name} AXIOMS {axs.toList}\"\n")
        check_file(census,output/"cone-axioms.log")
        reports=re.findall(r"SOURCE (\S+) DECL (\S+) AXIOMS \[([^\]]*)\]",(output/"cone-axioms.log").read_text())
        assert reports and len({n for _,n,_ in reports})==len(reports)
        declarations=[{"module":m,"name":n,"private":n.startswith("_private."),
                       "axioms":[a.strip() for a in ax.split(',') if a.strip()]} for m,n,ax in reports]
        assert all(set(d["axioms"])<=ALLOWED for d in declarations)
        imported=set(re.findall(r"^IMPORT (\S+)", (output/"cone-axioms.log").read_text(),re.M))
        assert imported, "Missing import census"
        assert imported <= set(order)|external.keys(), ("Uncertified imports", imported-set(order)-external.keys())
        receipt["importedExternalArtifactsChecked"] = len(imported-set(order))
        (output/"declarations.json").write_text(json.dumps(declarations,indent=2)+"\n")
        receipt["declarationsSha256"] = file_sha(output/"declarations.json")
        receipt["axiomAuditSourceSha256"] = {p.name:file_sha(p) for p in [audit,census]}
        check_artifacts()
        after={m:sha((src/(m.replace(".","/")+".lean")).read_bytes()) for m in files}
        config_after={n:sha((src/n).read_bytes()) for n in configs}
        assert after==receipt["sourceSha256Before"] and config_after==configs
        receipt.update({"sourceSha256After":after,"configSha256After":config_after,
                        "sourceBytesUnchanged":True,"status":"PASS",
                        "axiomCensus":{"total":len(declarations),"private":sum(d["private"] for d in declarations),
                                      "permitted":sorted(ALLOWED)}})
        save()
        summary=root/"verification/upstream-dft-baseline-result.json"
        summary.parent.mkdir(exist_ok=True)
        result_summary={k:receipt[k] for k in ["status","pin","moduleCount","elapsedSeconds",
            "sourceBytesUnchanged","finalTheorems","finalAxioms","axiomCensus","driverSha256","leanVersion",
            "compilerSha256","externalArtifactsManifestSha256","externalArtifactsSnapshotted",
            "importedExternalArtifactsChecked","declarationsSha256"]}
        result_summary.update({"receiptPath":str(output/"receipt.json"),
                               "receiptSha256":file_sha(output/"receipt.json")})
        temporary=summary.with_name(summary.name+"."+str(os.getpid())+".tmp")
        temporary.write_text(json.dumps(result_summary,indent=2)+"\n")
        temporary.replace(summary)
        print("PASS",receipt["moduleCount"],"fresh modules",len(declarations),"declarations",flush=True)
    except Exception as exc:
        receipt["status"]="FAIL"; receipt["error"]=str(exc); save(); raise


if __name__=="__main__":
    main()
