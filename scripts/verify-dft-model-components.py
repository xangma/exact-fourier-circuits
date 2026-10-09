#!/usr/bin/env python3
"""Freshly check DFT translation components, with an explicit incomplete-compiler receipt."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import uuid

if not __debug__:
    raise RuntimeError("Run without Python optimization; verification assertions are required")

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
BUILD = LEAN / ".lake/build/lib/lean"
CERTIFICATES = {
    "verification/uniform-final-algorithm.json":
        "2ac6d22ee5292260ab17217619c2ea19f9ef488013696a8174bb22ed52ab637b",
    "verification/model-comparison.json":
        "be3518cb50ac0f31f20105b3e610fe06b8370296a8422017f28e058f061c26f9",
}


def sha(path):
    with Path(path).open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def optional_parts(olean):
    """Lean can import split artifacts as well as the main .olean file."""
    base = str(olean)[:-len(".olean")]
    candidates = [Path(str(olean) + suffix) for suffix in (".server", ".private")]
    candidates += [Path(base + suffix) for suffix in (".ir", ".ir.sig")]
    return {
        "present": {str(p): sha(p) for p in candidates if p.is_file()},
        "absent": [str(p) for p in candidates if not p.exists()],
    }


def check_parts(snapshot):
    for path, digest in snapshot["present"].items():
        assert sha(path) == digest, f"Artifact part changed: {path}"
    for path in snapshot["absent"]:
        assert not Path(path).exists(), f"Artifact part appeared: {path}"


def output(*args):
    return subprocess.check_output(args, cwd=LEAN, text=True).strip()


def strip_comments(text):
    """Remove nested Lean comments while preserving strings and line breaks."""
    result, pos, depth, quoted = [], 0, 0, False
    while pos < len(text):
        pair = text[pos:pos+2]
        char = text[pos]
        if depth:
            if pair == "/-":
                depth += 1
                pos += 2
            elif pair == "-/":
                depth -= 1
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif not quoted and pair == "/-":
            depth = 1
            pos += 2
        elif not quoted and pair == "--":
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end
        else:
            result.append(char)
            pos += 1
            if quoted and char == "\\" and pos < len(text):
                result.append(text[pos])
                pos += 1
            elif char == '"':
                quoted = not quoted
    assert not depth, "Unterminated Lean comment"
    return "".join(result)


def run_logged(args, log, env=None):
    print(f"Checking {log.stem}", flush=True)
    with log.open("w") as handle:
        process = subprocess.Popen(args, cwd=LEAN, stdout=handle,
                                   stderr=subprocess.STDOUT, start_new_session=True, env=env)
        print(f"  group {process.pid}; log {log}; stop: kill -TERM -- -{process.pid}", flush=True)
        try:
            code = process.wait()
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                pass
            # The direct child can exit while a grandchild ignores SIGTERM.
            # Clean the entire owned group even when wait() already returned.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise
    assert code == 0, f"Lean failed ({code}): {log}"
    assert not re.search(r"\bwarning:", log.read_text()), f"Lean warning: {log}"


def main():
    signal.signal(signal.SIGTERM, lambda sig, frame: (_ for _ in ()).throw(SystemExit(128+sig)))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "logs/dft-model-components")
    args = parser.parse_args()
    logs = args.output.resolve() / ("run-" + uuid.uuid4().hex)
    logs.mkdir(parents=True, exist_ok=False)
    stage = logs / "build"
    stage.mkdir()
    print(f"Host {os.uname().nodename}; cwd {LEAN}; PID {os.getpid()}", flush=True)
    print(f"Logs {logs}; stop: kill -TERM {os.getpid()}", flush=True)
    sources, artifacts, external = {}, {}, {}
    for filename, digest in CERTIFICATES.items():
        assert sha(ROOT / filename) == digest, f"Certificate changed: {filename}"
        sources[filename] = digest
    baseline = json.loads((ROOT / "verification/uniform-final-algorithm.json").read_text())
    comparison = json.loads((ROOT / "verification/model-comparison.json").read_text())
    assert baseline["passed"] and baseline["standard_axioms_only"]
    assert comparison["passed"] and comparison["standard_axioms_only"]
    assert baseline["compiler_sha256"] == comparison["compiler_sha256"]
    compiler = Path(output("lake", "env", "which", "lean"))
    compiler_digest = sha(compiler)
    assert compiler_digest == baseline["compiler_sha256"]
    upstream = json.loads((LEAN / "ModelEquivalenceUpstream/MANIFEST.json").read_text())
    assert output("git", "-C", str(LEAN / ".lake/packages/mathlib"), "rev-parse", "HEAD") == upstream["mathlib_revision"]
    assert (LEAN / "lean-toolchain").read_text().strip() == upstream["lean_toolchain"]
    sources.update(baseline["source_sha256"])
    sources.update(baseline["config_sha256"])
    sources.update(comparison["source_sha256"])
    sources.update({item["path"]: item["sha256"] for item in upstream["files"]})
    artifacts.update(baseline["normal_project_artifact_sha256"])
    for module, digest in comparison["project_artifact_sha256"].items():
        if module in artifacts:
            assert artifacts[module] == digest, f"Conflicting artifact: {module}"
        artifacts[module] = digest
    lean_path = output("lake", "env", "printenv", "LEAN_PATH")
    search = [Path(p) if Path(p).is_absolute() else LEAN / p
              for p in lean_path.split(os.pathsep)]
    # Only certified old project modules are visible. A missing fresh component
    # must fail instead of loading an old DFTModel artifact from shared BUILD.
    reused_parts = {}
    for module in artifacts:
        relative = Path(module.replace(".", "/") + ".olean")
        link = stage / relative
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(BUILD / relative)
        parts = optional_parts(BUILD / relative)
        reused_parts["project:" + module] = parts
        for source in parts["present"]:
            part_link = stage / Path(source).relative_to(BUILD)
            part_link.symlink_to(source)
        reused_parts["stage:" + module] = optional_parts(link)
    isolated_paths = [stage] + [p.resolve() for p in search if p.resolve() != BUILD.resolve()]
    build_env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, isolated_paths)))
    for module, entry in baseline["external_artifact_sha256"].items():
        rel = Path(module.replace(".", "/") + ".olean")
        path = next((p / rel for p in search if (p / rel).is_file()), None)
        assert path, f"Missing external artifact: {module}"
        external[module] = (path, entry["sha256"])
        reused_parts["external:" + module] = optional_parts(path)
    files = {p.stem: p for p in LEAN.glob("DFTModel*.lean")}
    assert files, "No translation components"
    assert not (files.keys() & artifacts.keys()), "Fresh component overlaps certified reuse"
    dependencies = {}
    for name, path in files.items():
        text = strip_comments(path.read_text())
        # Diagnostic strings can legitimately contain words such as "axiom".
        tokens = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
        assert not re.search(r"\b(?:axiom|sorry|admit|native_decide)\b", tokens), path
        options = re.findall(r"\bset_option\s+([^\n]+)", text)
        assert all(option.strip() == "autoImplicit false" for option in options), path
        dependencies[name] = set(re.findall(r"^\s*(?:public\s+)?import\s+(\S+)", text, re.M)) & files.keys()
        sources[str(path.relative_to(ROOT))] = sha(path)
    for path in ["scripts/verify-dft-model-components.py", "scripts/check-dft-model-bridge.sh",
                 "scripts/verify-upstream-dft.py", "README.md", "PLAN.md",
                 "docs/dft-model-translation.md", "docs/machine-model-comparison.md",
                 "docs/upstream-dft-reproduction.md", "docs/audit-upstream-semantics.md",
                 "docs/audit-upstream-structure.md", "docs/paper-proof-map.md",
                 "verification/upstream-dft-baseline-manifest.json",
                 "verification/upstream-dft-baseline-result.json"]:
        sources[path] = sha(ROOT / path)
    ordered, pending = [], set(files)
    while pending:
        ready = sorted(name for name in pending if not dependencies[name] & pending)
        assert ready, f"Cyclic component imports: {pending}"
        ordered.extend(ready)
        pending.difference_update(ready)

    fresh, fresh_parts = {}, {}

    def check_inputs():
        assert {p.stem for p in LEAN.glob("DFTModel*.lean")} == set(files), "Module set changed"
        assert sha(compiler) == compiler_digest, "Compiler changed"
        for path, digest in sources.items():
            assert sha(ROOT / path) == digest, f"Source/config changed: {path}"
        for module, digest in artifacts.items():
            assert sha(BUILD / (module.replace(".", "/") + ".olean")) == digest, module
            assert sha(stage / (module.replace(".", "/") + ".olean")) == digest, module
        for module, (path, digest) in external.items():
            assert sha(path) == digest, module
        for module, digest in fresh.items():
            assert sha(stage / (module+".olean")) == digest, f"Fresh artifact changed: {module}"
        for parts in [*reused_parts.values(), *fresh_parts.values()]:
            check_parts(parts)

    check_inputs()
    print(f"Certified reuse: {len(artifacts)} project and {len(external)} external artifacts.", flush=True)
    for name in ordered:
        run_logged([str(compiler), "-o", str(stage / (name+".olean")), name+".lean"],
                   logs / (name+".log"), env=build_env)
        fresh[name] = sha(stage / (name+".olean"))
        fresh_parts[name] = optional_parts(stage / (name+".olean"))
    check_inputs()
    census = "\n".join("import " + name for name in ordered) + """
import Lean
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let modules : List String := MODULES
 let mut entries : Array Json := #[]
 for (name, _) in env.constants.toList do
  let origin := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx]!.toString)
  if origin.any (fun m => modules.contains m) then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError "Unexpected axiom {ax} in {name}"
   entries := entries.push (Json.mkObj [("name", toJson name.toString),
     ("module", toJson origin), ("axioms", toJson (axioms.toList.map toString))])
 liftIO <| IO.FS.writeFile CENSUS (Json.compress (.arr entries))
 liftIO <| IO.FS.writeFile IMPORTS (Json.compress (toJson (env.header.moduleNames.toList.map toString)))
 logInfo m!"Audited {entries.size} component declaration closures"
""".replace("MODULES", json.dumps(ordered)).replace("CENSUS", json.dumps(str(logs / "census.json"))).replace("IMPORTS", json.dumps(str(logs / "imports.json")))
    checker = logs / "Census.lean"
    checker.write_text(census)
    run_logged([str(compiler), "-R", str(logs), str(checker)], logs / "census.log", env=build_env)
    entries = json.loads((logs / "census.json").read_text())
    imported = set(json.loads((logs / "imports.json").read_text()))
    assert imported <= set(ordered) | artifacts.keys() | external.keys(), "Uncertified import"
    check_inputs()
    census_bytes = (logs / "census.json").read_bytes()
    census_digest = hashlib.sha256(census_bytes).hexdigest()
    census_destination = ROOT / ("verification/dft-model-components-census-" + census_digest + ".json")
    census_temporary = census_destination.with_suffix(".json.tmp-" + uuid.uuid4().hex)
    census_temporary.write_bytes(census_bytes)
    census_temporary.replace(census_destination)
    part_manifest = logs / "artifact-parts.json"
    part_manifest.write_text(json.dumps({"reused": reused_parts, "fresh": fresh_parts},
                                        indent=2, sort_keys=True) + "\n")
    receipt = {
        "schema": "dft-model-components/v1", "passed": True,
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Checked building blocks for translating our actual all-length DFT. The cost adapter has explicit computational premises; no closed whole-program translation is certified.",
        "compiler_closed": False, "model_equivalence_proved": False,
        "default_limits_for_new_modules": True, "standard_axioms_only": True,
        "fresh_modules": ordered, "declaration_closures": len(entries),
        "private_closures": sum(e["name"].startswith("_private.") for e in entries),
        "axioms": sorted({ax for e in entries for ax in e["axioms"]}),
        "compiler_sha256": compiler_digest, "source_sha256": sources,
        "fresh_artifact_sha256": fresh,
        "artifact_parts_manifest_path": str(part_manifest),
        "artifact_parts_manifest_sha256": sha(part_manifest),
        "artifact_parts_checked_before_after": True,
        "artifact_parts_trust": "Reused main artifacts are pinned to the prior certificates. Optional split/IR parts are snapshotted from the installed caches and checked unchanged; this run does not rebuild those caches.",
        "reused_project_artifacts_checked": len(artifacts),
        "reused_external_artifacts_checked": len(external),
        "imported_reused_project_modules": sorted(imported & artifacts.keys()),
        "imported_reused_external_modules": len(imported & external.keys()),
        "certificates_sha256": CERTIFICATES,
        "census_path": str(census_destination.relative_to(ROOT)),
        "census_sha256": census_digest, "checker_sha256": sha(checker),
        "upstream_main_proof_rebuilt": False, "enormous_runtime_instance_executed": False,
        "separate_upstream_reproduction_summary": "verification/upstream-dft-baseline-result.json",
        "separate_upstream_reproduction_summary_sha256": sources["verification/upstream-dft-baseline-result.json"],
    }
    destination = ROOT / "verification/dft-model-components.json"
    temporary = destination.with_suffix(".json.tmp-" + uuid.uuid4().hex)
    temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    temporary.replace(destination)
    print(f"PASS: {len(entries)} closures; {destination}; whole compiler OPEN.", flush=True)


if __name__ == "__main__":
    main()
