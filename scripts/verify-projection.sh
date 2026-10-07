#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log_dir="$root/logs"
mkdir -p "$log_dir"
cd "$root/lean"
exec > >(tee "$log_dir/lean-projection-verification.log") 2>&1
printf 'Host: %s\nCwd: %s\nPID: %s\nCommand: %s\nLog: %s\n' "$(hostname)" "$PWD" "$$" "$root/scripts/verify-projection.sh" "$log_dir/lean-projection-verification.log"
printf 'Stop: terminate child processes of PID %s, then kill -TERM %s\n' "$$" "$$"
python3 - <<'PY_PIN'
from pathlib import Path
import json, subprocess
expected = json.loads(Path('UPSTREAM_MANIFEST.json').read_text())['mathlib_revision']
actual = subprocess.check_output(
    ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True
).strip()
if actual != expected:
    raise SystemExit(f'Mathlib revision mismatch: {actual} != {expected}')
print(f'Mathlib revision verified: {actual}')
PY_PIN
lean --version
lake build ProjectionIdentities
lake env lean CheckProjectionAxioms.lean | tee "$log_dir/lean-projection-axioms.log"
python3 - "$log_dir" <<'PY_AXIOMS'
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, sys
log_dir = Path(sys.argv[1])
text = (log_dir / 'lean-projection-axioms.log').read_text()
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
namespace = 'ExactFourierCircuits.Projection.'
expected = {namespace + name for name in (
    'pullback_translate', 'pullback_directionalC', 'pullback_inverseDirectionalC',
    'directionalC_inverse', 'pullback_injective',
    'pullback_pointwise', 'intertwines_comp', 'intertwines_runWord',
    'frame_telescoping', 'eightRows_identity', 'scalar_exchange',
)}
results = {}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? depends on axioms:\s*\[([^\]]*)\]", text):
    name, names = match.groups()
    results[name] = {a.strip() for a in names.split(',') if a.strip()}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? does not depend on any axioms", text):
    results[match.group(1)] = set()
if set(results) != expected:
    raise SystemExit(f'Missing or unexpected projection axiom reports: {set(results)}')
for name, axioms in results.items():
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f'{name}: forbidden axioms {sorted(unexpected)}')
    print(f'{name}: permitted axioms only {sorted(axioms)}')
files = ('ProjectionIdentities.lean', 'CheckProjectionAxioms.lean',
         'KernelIdentities.lean', 'lean-toolchain', 'lakefile.lean')
receipt = {
    'schema': 'lean-projection-verification/v1',
    'passed': True,
    'finished_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
    'mathlib_revision': subprocess.check_output(
        ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True
    ).strip(),
    'source_sha256': {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in files},
    'axioms': {name: sorted(axioms) for name, axioms in results.items()},
    'scope': 'General algebraic identities; not a certificate of the complete GF(2) combinatorial network or saving budget.',
}
receipt_path = log_dir / 'lean-projection-receipt.json'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: all eleven projection/network algebra identities use permitted axiom closures.')
print(f'Receipt: {receipt_path}')
PY_AXIOMS
