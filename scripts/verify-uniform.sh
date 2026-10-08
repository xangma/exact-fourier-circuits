#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log_dir="$root/logs"
mkdir -p "$log_dir"
cd "$root/lean"
exec > >(tee "$log_dir/lean-uniform-verification.log") 2>&1
printf 'Host: %s\nCwd: %s\nPID: %s\nCommand: %s\nLog: %s\n' "$(hostname)" "$PWD" "$$" "$root/scripts/verify-uniform.sh" "$log_dir/lean-uniform-verification.log"
printf 'Stop: terminate child processes of PID %s, then kill -TERM %s\n' "$$" "$$"
python3 - <<'PY_PIN'
from pathlib import Path
import hashlib, json, re, subprocess
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
registry = json.loads(Path('UNIFORM_CHECKS.json').read_text())
files = {'UNIFORM_CHECKS.json', 'lean-toolchain', 'lakefile.lean',
         'UPSTREAM_MANIFEST.json', 'lake-manifest.json', '../scripts/verify-uniform.sh'}
pending = [f'{m}.lean' for m in registry['modules']]
pending += [f'Check{m}Axioms.lean' for m in registry['modules']]
while pending:
    name = pending.pop()
    if name in files:
        continue
    files.add(name)
    source = Path(name).read_text()
    for line in re.findall(r'^import (.+)$', source, re.M):
        for module in line.split():
            imported = Path(module.replace('.', '/') + '.lean')
            if imported.is_file():
                pending.append(str(imported))
hashes = {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in sorted(files)}
Path('../logs/lean-uniform-inputs.json').write_text(json.dumps(hashes, indent=2) + '\n')
PY_PIN
lean --version
mapfile_modules=()
while IFS= read -r module; do mapfile_modules+=("$module"); done < <(
  python3 -c "import json; print('\n'.join(json.load(open('UNIFORM_CHECKS.json'))['modules']))"
)
lake build "${mapfile_modules[@]}"
: > "$log_dir/lean-uniform-axioms.log"
for module in "${mapfile_modules[@]}"; do
  lake env lean "Check${module}Axioms.lean" | tee -a "$log_dir/lean-uniform-axioms.log"
done
python3 - "$log_dir" <<'PY_AXIOMS'
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, sys
log_dir = Path(sys.argv[1])
text = (log_dir / 'lean-uniform-axioms.log').read_text()
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
registry = json.loads(Path('UNIFORM_CHECKS.json').read_text())
groups = registry['modules']
expected = {name for names in groups.values() for name in names}
environment_checks = registry.get('environment_checks', {})
if set(environment_checks) - set(groups):
    raise SystemExit('Environment checks name an unregistered module')
for module, names in environment_checks.items():
    prefix = f'_private.{module}.'
    checker = Path(f'Check{module}Axioms.lean').read_text()
    if (len(names) != len(set(names)) or set(names) & expected or
            any(not name.startswith(prefix) for name in names) or
            f'"{prefix}".isPrefixOf name.toString' not in checker or
            'collectAxioms name' not in checker):
        raise SystemExit(f'Invalid explicit environment audit: {module}')
    expected.update(names)
if registry['closed_uniform_algorithm'] is not None:
    raise SystemExit('This component verifier does not certify the final uniform algorithm')
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
hashes = json.loads((log_dir / 'lean-uniform-inputs.json').read_text())
for name, digest in hashes.items():
    if hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Source changed during verification: {name}; rerun on stable sources')
receipt = {
    'schema': 'lean-uniform-components/v1',
    'passed': True,
    'finished_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
    'mathlib_revision': subprocess.check_output(
        ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True
    ).strip(),
    'upstream_files_verified': 51,
    'source_sha256': hashes,
    'verification_script_sha256': hashlib.sha256(Path('../scripts/verify-uniform.sh').read_bytes()).hexdigest(),
    'axioms': {name: sorted(axioms) for name, axioms in results.items()},
    'components_verified': True,
    'uniform_algorithm_verified': False,
    'scope': registry['scope'],
}
receipt_path = log_dir / 'lean-uniform-receipt.json'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
verification = Path('../verification')
verification.mkdir(exist_ok=True)
(verification / 'uniform-components.json').write_text(json.dumps(receipt, indent=2) + '\n')
(verification / 'uniform-components-axioms.txt').write_text(text)
print(f'PASS: {len(results)} component declarations use permitted axiom closures; full uniform algorithm remains unproved.')
print(f'Receipt: {receipt_path}')
PY_AXIOMS
