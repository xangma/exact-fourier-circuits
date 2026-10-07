#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
project="$root/lean"
log_dir="$root/logs"
mkdir -p "$log_dir"
cd "$project"
exec > >(tee "$log_dir/lean-verification.log") 2>&1
printf 'Host: %s\nCwd: %s\nPID: %s\nCommand: %s\nLog: %s\n' "$(hostname)" "$project" "$$" "$root/scripts/verify-lean.sh $*" "$log_dir/lean-verification.log"
printf 'Stop: terminate child processes of PID %s, then kill -TERM %s\n' "$$" "$$"

# Fail if the vendored theorem differs from its recorded upstream source.
python3 - <<'PY'
from pathlib import Path
import hashlib, json
manifest = json.loads(Path('UPSTREAM_MANIFEST.json').read_text())
assert manifest['local_import_closure_count'] == len(manifest['files']) == 51
for item in manifest['files']:
    path = Path(item['path'])
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != item['sha256']:
        raise SystemExit(f'Upstream source changed: {path}')
print('Verified 51 unmodified upstream modules.')
PY

if [[ ! -f lake-manifest.json ]]; then
  lake update
fi
if [[ "${1:-}" != "--skip-cache" ]]; then
  lake exe cache get
fi
python3 - <<'PY_CHECK_PIN'
from pathlib import Path
import json, subprocess
expected = json.loads(Path('UPSTREAM_MANIFEST.json').read_text())['mathlib_revision']
actual = subprocess.check_output(
    ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True
).strip()
if actual != expected:
    raise SystemExit(f'Mathlib revision mismatch: {actual} != {expected}')
print(f'Mathlib revision verified: {actual}')
PY_CHECK_PIN
lean --version
lake build OAI KernelIdentities
lake env lean CheckAxioms.lean | tee "$log_dir/lean-axioms.log"
python3 - "$log_dir/lean-axioms.log" <<'PY'
from pathlib import Path
import re, sys
text = Path(sys.argv[1]).read_text()
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
expected = {
    'OAI.ExactFourier.finite_win',
    'OAI.ExactFourier.main_theorem',
    'OAI.ExactFourier.main_liminf',
}
results = {}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? depends on axioms:\s*\[([^\]]*)\]", text):
    name, names = match.groups()
    results[name] = {a.strip() for a in names.split(',') if a.strip()}
if set(results) != expected:
    raise SystemExit(f'Missing or unexpected axiom reports: {set(results)}')
for name, axioms in results.items():
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f'{name}: forbidden axioms {sorted(unexpected)}')
    print(f'{name}: permitted axioms only {sorted(axioms)}')
print('PASS: original proofs compile and their transitive axiom closures are permitted.')
PY

lake env lean CheckKernelAxioms.lean | tee "$log_dir/lean-kernel-axioms.log"
python3 - "$log_dir/lean-kernel-axioms.log" <<'PY_KERNEL_AXIOMS'
from pathlib import Path
import re, sys
text = Path(sys.argv[1]).read_text()
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
expected = {
    'ExactFourierCircuits.C_square',
    'ExactFourierCircuits.C_inverse',
    'ExactFourierCircuits.Hprime_eq_H',
    'ExactFourierCircuits.K_formula',
    'ExactFourierCircuits.upper_shear_formula',
}
results = {}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? depends on axioms:\s*\[([^\]]*)\]", text):
    name, names = match.groups()
    results[name] = {a.strip() for a in names.split(',') if a.strip()}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? does not depend on any axioms", text):
    results[match.group(1)] = set()
if set(results) != expected:
    raise SystemExit(f'Missing or unexpected kernel axiom reports: {set(results)}')
for name, axioms in results.items():
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f'{name}: forbidden axioms {sorted(unexpected)}')
    print(f'{name}: permitted axioms only {sorted(axioms)}')
print('PASS: all five exact kernel/shear identities compile with permitted axiom closures.')
PY_KERNEL_AXIOMS
