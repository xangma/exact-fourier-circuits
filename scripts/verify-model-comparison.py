#!/usr/bin/env python3
"""Fresh, default-limit checks of the model comparison, not of upstream Main."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
BUILD = LEAN / ".lake/build/lib/lean"
MODULES = [
    ("OAI.Computability.FourierCircuit.Core", "OAI/Computability/FourierCircuit/Core.lean", "."),
    ("UniformMachine", "UniformMachine.lean", "."),
    ("OAI.Computability.FourierTransform.RAM", "ModelEquivalenceUpstream/OAI/Computability/FourierTransform/RAM.lean", "ModelEquivalenceUpstream"),
    ("OAI.Computability.FourierTransform.Goal", "ModelEquivalenceUpstream/OAI/Computability/FourierTransform/Goal.lean", "ModelEquivalenceUpstream"),
] + [(name, name + ".lean", ".") for name in [
    "ModelEquivalenceNat", "ModelEquivalenceScalarLowering",
    "ModelEquivalenceInterpreter", "ModelEquivalenceInterpreterFixtures",
    "ModelEquivalenceInterpreterAxioms", "ModelEquivalenceZeroPreservation",
    "ModelEquivalenceCounterexample", "ModelEquivalence",
]]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def output(*args, cwd=LEAN):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def run_logged(args, log):
    print("Checking", log.stem, flush=True)
    with log.open("w") as handle:
        process = subprocess.Popen(args, cwd=LEAN, stdout=handle, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        print(f"  process group {process.pid}; log {log}; stop: kill -TERM -- -{process.pid}", flush=True)
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
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
    if code:
        raise RuntimeError(f"check failed ({code}): {log}")


def main():
    def interrupted(signum, _frame):
        raise SystemExit(128 + signum)

    signal.signal(signal.SIGTERM, interrupted)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "logs/model-comparison")
    args = parser.parse_args()
    logs = args.output.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    print(f"Host: {os.uname().nodename}; cwd: {LEAN}; PID: {os.getpid()}", flush=True)
    print(f"Logs: {logs}; stop: kill -TERM {os.getpid()}", flush=True)

    original = json.loads((LEAN / "UPSTREAM_MANIFEST.json").read_text())
    upstream = json.loads((LEAN / "ModelEquivalenceUpstream/MANIFEST.json").read_text())
    assert (LEAN / "lean-toolchain").read_text().strip() == upstream["lean_toolchain"]
    assert original["mathlib_revision"] == upstream["mathlib_revision"]
    assert output("git", "-C", str(LEAN / ".lake/packages/mathlib"), "rev-parse", "HEAD") == upstream["mathlib_revision"]
    assert len(original["files"]) == 51
    for item in original["files"]:
        assert sha(LEAN / item["path"]) == item["sha256"], item["path"]
    for item in upstream["files"]:
        assert sha(ROOT / item["path"]) == item["sha256"], item["path"]

    sources = {str((LEAN / source).relative_to(ROOT)): sha(LEAN / source)
               for _, source, _ in MODULES}
    configs = ["lean/lean-toolchain", "lean/lakefile.lean", "lean/lake-manifest.json",
               "lean/UPSTREAM_MANIFEST.json", "lean/ModelEquivalenceUpstream/MANIFEST.json",
               "scripts/check-model-equivalence.sh", "scripts/verify-model-comparison.py"]
    source_hashes = sources | {path: sha(ROOT / path) for path in configs}
    for _, source, _ in MODULES:
        if not source.startswith("ModelEquivalence"):
            continue
        text = (LEAN / source).read_text()
        # Every comparison source uses only the ordinary autoImplicit setting.
        options = re.findall(r"^set_option\s+(.+)$", text, re.M)
        assert all(option == "autoImplicit false" for option in options), source
        assert not re.search(r"^\s*(axiom\b|.*\b(?:sorry|admit|native_decide)\b)",
                             text, re.M), source

    baseline_path = ROOT / "verification/uniform-final-algorithm.json"
    baseline = json.loads(baseline_path.read_text())
    assert baseline["passed"] and baseline["standard_axioms_only"]
    compiler = Path(output("lake", "env", "which", "lean"))
    assert sha(compiler) == baseline["compiler_sha256"]
    lean_path = output("lake", "env", "printenv", "LEAN_PATH")
    search_paths = [Path(p) if Path(p).is_absolute() else LEAN / p
                    for p in lean_path.split(os.pathsep)]
    external = {}
    for module, certified in baseline["external_artifact_sha256"].items():
        relative = Path(module.replace(".", "/") + ".olean")
        path = next((p / relative for p in search_paths if (p / relative).is_file()), None)
        assert path is not None, module
        assert sha(path) == certified["sha256"], module
        external[module] = path
    print(f"Verified {len(external)} certified external artifacts; fresh project build next.", flush=True)

    for module, source, package_root in MODULES:
        target = BUILD / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        run_logged(["lake", "env", "lean", "-R", package_root, "-o", str(target), source],
                   logs / (module + ".log"))

    modules = [module for module, _, _ in MODULES]
    # Defining-module filtering includes private and generated declarations.
    census = """import ModelEquivalence
import ModelEquivalenceInterpreterFixtures
import ModelEquivalenceInterpreterAxioms
import Lean
example : ¬∃ compile : ExactFourierCircuits.UniformMachine.Program →
    OAI.PowerSaving.RAM.Prog false OAI.PowerSaving.dftInKind OAI.PowerSaving.dftOutKind,
    ∀ p, ExactFourierCircuits.ModelEquivalence.PreservesAtOne p (compile p) :=
  ExactFourierCircuits.ModelEquivalence.no_interface_preserving_compiler
#print axioms ExactFourierCircuits.ModelEquivalence.no_interface_preserving_compiler
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
 logInfo m!"Audited {entries.size} defining-module closures"
""".replace("MODULES", json.dumps(modules)).replace("CENSUS", json.dumps(str(logs / "census.json"))).replace("IMPORTS", json.dumps(str(logs / "imports.json")))
    checker = logs / "Census.lean"
    checker.write_text(census)
    run_logged(["lake", "env", "lean", "-R", str(logs), str(checker)], logs / "census.log")
    entries = json.loads((logs / "census.json").read_text())
    assert {e["module"] for e in entries} >= set(modules) - {"ModelEquivalenceInterpreterAxioms"}
    imported = json.loads((logs / "imports.json").read_text())
    assert set(imported) <= set(modules) | set(external), set(imported) - set(modules) - set(external)
    for path, digest in source_hashes.items():
        assert sha(ROOT / path) == digest, f"Source changed: {path}"
    for module, path in external.items():
        assert sha(path) == baseline["external_artifact_sha256"][module]["sha256"], module
    receipt = {
        "schema": "machine-model-comparison/v1", "passed": True,
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "No equivalence under the declared DFT data interface; positive primitive translations and a specific linear-cost fresh-tape update. Not a whole-language compiler or an arbitrary-encoding impossibility proof.",
        "fresh_project_modules": len(MODULES), "declaration_closures": len(entries),
        "private_closures": sum(e["name"].startswith("_private.") for e in entries),
        "standard_axioms_only": True, "default_limits": True,
        "target": "ExactFourierCircuits.ModelEquivalence.no_interface_preserving_compiler",
        "equivalence_proved": False, "interface_preserving_compiler_refuted": True,
        "original_upstream_sources_unchanged": 51,
        "upstream_definition_revision": upstream["revision"],
        "upstream_main_proof_rebuilt": False,
        "compiler_sha256": sha(compiler), "source_sha256": source_hashes,
        "project_artifact_sha256": {module: sha(BUILD / (module.replace(".", "/") + ".olean")) for module in modules},
        "certified_external_artifacts_checked": len(external),
        "external_certificate_sha256": sha(baseline_path),
        "axioms": sorted({ax for e in entries for ax in e["axioms"]}),
        "checker_sha256": sha(checker), "census_sha256": sha(logs / "census.json"),
    }
    dump(ROOT / "verification/model-comparison.json", receipt)
    print(f"PASS: {len(entries)} closures; receipt verification/model-comparison.json", flush=True)


if __name__ == "__main__":
    main()
