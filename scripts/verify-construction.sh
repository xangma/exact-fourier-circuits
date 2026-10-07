#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log_dir="$root/logs"
mkdir -p "$log_dir"
cd "$root/lean"
exec > >(tee "$log_dir/lean-construction-verification.log") 2>&1
printf 'Host: %s\nCwd: %s\nPID: %s\nCommand: %s\nLog: %s\n' "$(hostname)" "$PWD" "$$" "$root/scripts/verify-construction.sh" "$log_dir/lean-construction-verification.log"
printf 'Stop: terminate child processes of PID %s, then kill -TERM %s\n' "$$" "$$"
python3 - <<'PY_PIN'
from pathlib import Path
import hashlib, json, subprocess
manifest = json.loads(Path('UPSTREAM_MANIFEST.json').read_text())
if len(manifest['files']) != 51:
    raise SystemExit('Unexpected upstream import closure')
for item in manifest['files']:
    if hashlib.sha256(Path(item['path']).read_bytes()).hexdigest() != item['sha256']:
        raise SystemExit(f"Upstream source changed: {item['path']}")
if Path('lean-toolchain').read_text().strip() != manifest['lean_toolchain']:
    raise SystemExit('Lean toolchain pin changed')
actual = subprocess.check_output(
    ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True
).strip()
if actual != manifest['mathlib_revision']:
    raise SystemExit(f'Mathlib revision mismatch: {actual}')
print('Verified toolchain pins and 51 unmodified upstream modules.')
PY_PIN
lean --version
mapfile_modules=()
while IFS= read -r module; do mapfile_modules+=("$module"); done < <(
  python3 -c "import json; print('\n'.join(json.load(open('CONSTRUCTION_CHECKS.json'))['modules']))"
)
lake build "${mapfile_modules[@]}"
: > "$log_dir/lean-construction-axioms.log"
for module in "${mapfile_modules[@]}"; do
  lake env lean "Check${module}Axioms.lean" | tee -a "$log_dir/lean-construction-axioms.log"
done
python3 - "$log_dir" <<'PY_AXIOMS'
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, sys
log_dir = Path(sys.argv[1])
text = (log_dir / 'lean-construction-axioms.log').read_text()
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
registry = json.loads(Path('CONSTRUCTION_CHECKS.json').read_text())
groups = registry['modules']
expected = {name for names in groups.values() for name in names}
certificates = registry['construction_certificates']
if not set(certificates) <= expected:
    raise SystemExit('Missing closed construction certificates in declaration registry')
for module, declarations in groups.items():
    checker = Path(f'Check{module}Axioms.lean').read_text()
    if re.findall(r'^#print axioms (\S+)', checker, re.M) != declarations:
        raise SystemExit(f'Checker differs from declaration registry: {module}')
results = {}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? depends on axioms:\s*\[([^\]]*)\]", text):
    name, names = match.groups()
    results[name] = {a.strip() for a in names.split(',') if a.strip()}
for match in re.finditer(r"'?([A-Za-z0-9_.]+)'? does not depend on any axioms", text):
    results[match.group(1)] = set()
if set(results) != expected:
    raise SystemExit(f'Missing/unexpected axiom reports: {expected ^ set(results)}')
for name, axioms in results.items():
    if axioms - allowed:
        raise SystemExit(f'{name}: forbidden axioms {sorted(axioms - allowed)}')
files = ['KernelIdentities.lean', 'ProjectionIdentities.lean',
         'CONSTRUCTION_CHECKS.json', 'lean-toolchain', 'lakefile.lean',
         'UPSTREAM_MANIFEST.json', 'lake-manifest.json']
for group in groups:
    files.extend((f'{group}.lean', f'Check{group}Axioms.lean'))
receipt = {
    'schema': 'lean-exact-construction/v3',
    'passed': True,
    'finished_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
    'mathlib_revision': subprocess.check_output(
        ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True
    ).strip(),
    'upstream_files_verified': 51,
    'source_sha256': {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in files},
    'verification_script_sha256': hashlib.sha256(Path('../scripts/verify-construction.sh').read_bytes()).hexdigest(),
    'axioms': {name: sorted(axioms) for name, axioms in results.items()},
    'construction_certificates': certificates,
    'lean_construction_verified': True,
    'python_producer_verified': False,
    'scope': 'The literal Lean h=100 saving word has its exact tensor identity and strict forward-C-call count proved together, yielding closed FiniteWinStatement and MainStatement via the unchanged upstream Fourier transfer. This certifies the Lean mathematical word, not the Python producer or floating-point accuracy.',
}
receipt_path = log_dir / 'lean-construction-receipt.json'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(f'PASS: {len(results)} construction declarations use permitted axiom closures.')
print(f'Receipt: {receipt_path}')
PY_AXIOMS
