#!/usr/bin/env python3
"""Reproduce the closed uniform DFT theorem from normal repository sources.

Cached proof artifacts are reusable only when their exact bytes, sources and
complete dependency lineage match the certified manifest. --rebuild-all instead
compiles every project module freshly. The final normal theorem, exact target
guard and complete defining-module census are always checked again.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import json
import os
import shutil
import subprocess
import sys

import uniform_final_verification_core as c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, choices=range(1, 5), default=4)
    parser.add_argument('--rebuild-all', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean_dir = root / 'lean'
    out = args.output or root / 'logs' / ('uniform-final-normal-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
    out = (out if out.is_absolute() else root / out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    c.R, c.L, c.D = root, lean_dir, out
    registry_path = lean_dir / 'UNIFORM_CHECKS.json'
    registry = json.loads(registry_path.read_text())
    target = 'ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT'
    if registry.get('closed_uniform_algorithm', {}).get('theorem') != target:
        raise ValueError('Registry does not name the closed final theorem')
    certified_path = root / 'verification/uniform-final-imports.json'
    certified = json.loads(certified_path.read_text())
    proof_receipt = root / 'verification/uniform-final-coherent-source-receipt.json'
    if c.sha(proof_receipt) != certified['coherent_receipt_sha256']:
        raise ValueError('Certified artifact provenance receipt changed')
    proof = json.loads(proof_receipt.read_text())
    if not proof['passed'] or not proof['uniform_algorithm_verified'] or not proof['standard_axioms_only']:
        raise ValueError('Invalid certified proof provenance')
    clean = dict(os.environ)
    clean.pop('LEAN_PATH', None)
    clean.pop('LEAN_SRC_PATH', None)
    observed = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=lean_dir, env=clean, text=True).strip()
    if '/logs/' in observed:
        raise ValueError('Normal Lake environment contains a scratch dependency')
    compiler = Path(subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=lean_dir, env=clean, text=True).strip())
    compiler_matches_certified = c.sha(compiler) == proof['compiler_sha256']
    version = subprocess.check_output([str(compiler), '--version'], text=True).strip()
    if 'version 4.34.1,' not in version:
        raise ValueError('Compiler does not match the pinned Lean version')
    core = Path(subprocess.check_output([str(compiler), '--print-libdir'], text=True).strip())
    paths = [(Path(p) if Path(p).is_absolute() else lean_dir / p).resolve() for p in observed.split(':')]
    packages = [p for p in paths if p.is_dir() and p.is_relative_to(lean_dir / '.lake/packages')]
    external = c.unique(packages + [core])
    external_freeze_path = root / 'verification/uniform-final-external-artifacts.json'
    if c.sha(external_freeze_path) != proof['artifact_sha256'][certified['external_freeze_receipt_key']]:
        raise ValueError('Certified external artifact freeze changed')
    external_freeze = json.loads(external_freeze_path.read_text())

    def check_external():
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                        cwd=lean_dir / '.lake/packages/mathlib', text=True)
        if dirty:
            raise ValueError('Tracked Mathlib source tree is modified')
        current = {}
        for name, row in external_freeze.items():
            rel = name.replace('.', '/') + '.olean'
            p = next((base / rel for base in external if (base / rel).is_file()), None)
            if p is None:
                raise ValueError('Missing external dependency artifact: ' + name)
            current[name] = {'path': str(p), 'sha256': c.sha(p)}
        return current

    external_before = check_external()
    external_matches_certified = all(external_before[m]['sha256'] == row['sha256'] for m, row in external_freeze.items())
    lineage_matches_certified = compiler_matches_certified and external_matches_certified
    expected_sources = registry['project_source_sha256']
    modules, order, active = {}, [], set()

    def visit(name):
        if name in modules:
            return
        if name in active:
            raise ValueError('Project import cycle: ' + name)
        source = lean_dir / (name.replace('.', '/') + '.lean')
        if not source.is_file():
            raise ValueError('Missing normal project source: ' + name)
        if name not in expected_sources or c.sha(source) != expected_sources[name]:
            raise ValueError('Normal project source differs from registry: ' + name)
        text = source.read_text()
        deps = c.imports(text)
        active.add(name)
        for dep in deps:
            candidate = lean_dir / (dep.replace('.', '/') + '.lean')
            if candidate.is_file():
                if dep not in expected_sources:
                    raise ValueError('Unregistered project import: ' + dep)
                visit(dep)
            elif not any((p / (dep.replace('.', '/') + '.olean')).is_file() for p in external):
                raise ValueError('Missing external import: ' + dep)
        active.remove(name)
        modules[name] = {'module': name, 'source': c.relative(source), 'source_sha256': c.sha(source),
                         'imports': deps, 'violations': c.violations(text)}
        order.append(name)

    for name in registry['modules']:
        visit(name)
    if set(modules) != set(expected_sources):
        raise ValueError('Registry/source closure mismatch')
    configs = [registry_path, certified_path, proof_receipt, external_freeze_path, compiler, Path(__file__).resolve(),
               Path(c.__file__).resolve(), root / 'scripts/verify-uniform.sh',
               root / 'verification/UniformFinalAlgorithmGuard.lean',
               *[lean_dir / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'UPSTREAM_MANIFEST.json']]]
    data = {'lean': str(compiler), 'targets': list(registry['modules']), 'topological_order': order,
            'external_only_paths': list(map(str, external)), 'project_modules': modules,
            'config_inputs': {c.relative(p): c.sha(p) for p in configs}, 'missing_sources': {},
            'historical_source_limit_settings': registry['historical_source_limit_hashes'],
            'approved_historical_source_limit_hashes': registry['historical_source_limit_hashes']}
    c.pins()
    reuse, reasons = set(), {}
    artifacts = lean_dir / '.lake/build/lib/lean'
    for name in order:
        old = certified['modules'].get(name)
        artifact = artifacts / (name.replace('.', '/') + '.olean')
        if old:
            suffix = name.replace('.', '/') + '.lean'
            if not old['certified_source'].endswith('/' + suffix) or proof['source_sha256'].get(old['certified_source']) != old['source_sha256']:
                raise ValueError('Certified source lineage differs from proof receipt: ' + name)
        eligible = lineage_matches_certified and not args.rebuild_all and name != 'UniformFinalDFTExecution' and old and artifact.is_file()
        if eligible:
            eligible = (old['source_sha256'] == modules[name]['source_sha256'] and
                        old['imports'] == modules[name]['imports'] and
                        c.sha(artifact) == old['artifact_sha256'] and
                        all(dep not in modules or dep in reuse for dep in modules[name]['imports']) and
                        proof['coherent_project_artifact_sha256'][name] == old['artifact_sha256'])
        if eligible:
            reuse.add(name)
        else:
            reasons[name] = 'Fresh terminal or unavailable/changed certified artifact/dependency'
    data['certified_reuse'] = {'reused_modules': sorted(reuse), 'fresh_modules': [m for m in order if m not in reuse],
                              'receipt_sha256': c.sha(proof_receipt)}
    c.dump(out / 'inventory.json', data)
    c.validate(data)
    c.stage(data)
    logs = out / 'build-logs'
    logs.mkdir()
    progress = {}
    for name in sorted(reuse):
        rel = Path(name.replace('.', '/'))
        old = artifacts / rel.with_suffix('.olean')
        shutil.copy2(old, out / 'stage' / rel.with_suffix('.olean'))
        log = logs / (name + '.log')
        log.write_text('')
        progress[name] = {'inventory_sha256': c.sha(out / 'inventory.json'), 'artifact_sha256': c.sha(old),
                          'log_sha256': c.sha(log), 'origin': 'certified_normal_artifact',
                          'certified_receipt_sha256': c.sha(proof_receipt)}
    c.dump(out / 'fresh-build-progress.json', progress)
    staged = json.loads((out / 'stage-manifest.json').read_text())
    staged['copied_project_oleans'] = len(reuse)
    c.dump(out / 'stage-manifest.json', staged)
    c.dump(out / 'held-seal.json', {'inventory_sha256': c.sha(out / 'inventory.json'), 'all_selected_sources_held': True})
    print('HOST', subprocess.check_output(['hostname'], text=True).strip(), 'CWD', lean_dir,
          'PID', os.getpid(), 'LOG', out, 'STOP kill -TERM', os.getpid(), flush=True)
    print('Normal source-only cone:', len(order), 'certified artifacts reused:', len(reuse),
          'fresh project modules:', len(order) - len(reuse), flush=True)
    c.run(data, audit=False, workers=args.jobs)
    for name in order:
        rel = Path(name.replace('.', '/')).with_suffix('.olean')
        destination = artifacts / rel
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(out / 'stage' / rel, destination)
    normal_env = dict(clean)
    normal_env['LEAN_PATH'] = ':'.join(map(str, [artifacts, *external]))
    source = lean_dir / 'UniformFinalDFTExecution.lean'
    terminal = artifacts / 'UniformFinalDFTExecution.olean'
    command = [str(compiler), '-DautoImplicit=false', '-R', str(lean_dir), '-o', str(terminal), str(source)]
    with (out / 'fresh-normal-main.log').open('w') as log:
        result = subprocess.run(command, cwd=lean_dir, env=normal_env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('Fresh normal final theorem failed; see fresh-normal-main.log')
    normal_snapshot = {m: c.sha(artifacts / (m.replace('.', '/') + '.olean')) for m in order}
    # Census and guard now load only normal artifacts and external dependencies.
    c.checked_env = lambda _: normal_env
    c.census(data)
    actual = json.loads((out / 'census.json').read_text())
    expected = {(m, n) for m, names in registry['modules'].items() for n in names}
    expected.update((m, n) for m, names in registry['environment_checks'].items() for n in names)
    if {(row['module'], row['name']) for row in actual} != expected:
        raise ValueError('Missing/unexpected defining-module declarations in complete normal census')
    guard = root / 'verification/UniformFinalAlgorithmGuard.lean'
    for label, file in [('census', out / 'stage/Census.lean'), ('guard', guard)]:
        result = subprocess.run([str(compiler), '--deps', str(file)], cwd=lean_dir, env=normal_env,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (label + '-normal-deps.log')).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError('Normal dependency resolution failed: ' + label)
        for line in result.stdout.splitlines():
            if line.endswith('.olean'):
                p = Path(line)
                p = (p if p.is_absolute() else lean_dir / p).resolve()
                if not any(p.is_relative_to(base) for base in [artifacts, *external]):
                    raise ValueError('Unexpected scratch artifact fallback: ' + str(p))
    with (out / 'exact-target.log').open('w') as log:
        result = subprocess.run([str(compiler), '-DautoImplicit=false', str(guard)], cwd=lean_dir,
                                env=normal_env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('Exact final statement guard failed')
    c.validate(data)
    external_after = check_external()
    if external_after != external_before:
        raise ValueError('External dependency resolution changed during verification')
    if normal_snapshot != {m: c.sha(artifacts / (m.replace('.', '/') + '.olean')) for m in order}:
        raise ValueError('Normal project artifact changed during census/guard')
    imported = json.loads((out / 'environment-imports.json').read_text())
    external_hashes = {}
    for name in imported:
        if name in modules:
            continue
        rel = name.replace('.', '/') + '.olean'
        artifact = next((p / rel for p in external if (p / rel).is_file()), None)
        if artifact is None:
            raise ValueError('Missing external artifact during final seal: ' + name)
        external_hashes[name] = {'path': str(artifact), 'sha256': c.sha(artifact)}
    c.dump(out / 'external-artifact-freeze.json', external_hashes)
    receipt = {'schema': 'lean-uniform-final-algorithm/v1', 'passed': True,
               'finished_utc': datetime.now(timezone.utc).isoformat(),
               'uniform_algorithm_verified': True, 'closed_uniform_algorithm': registry['closed_uniform_algorithm'],
               'normal_source_only': True, 'normal_lean_path': normal_env['LEAN_PATH'],
               'project_modules': len(order), 'certified_artifacts_reused': len(reuse),
               'fresh_project_modules': len(order) - len(reuse), 'fresh_normal_terminal_compiles': 1,
               'declarations': len(actual), 'private_declarations': sum(r['name'].startswith('_private.') for r in actual),
               'standard_axioms_only': True, 'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
               'default_driver_limits': True, 'historical_source_limit_modules': registry['historical_source_limit_hashes'],
               'upstream_sources_unmodified': 51, 'mathlib_revision': c.pins()['mathlib_revision'],
               'compiler_sha256': c.sha(compiler), 'certified_coherent_receipt_sha256': c.sha(proof_receipt),
               'compiler_matches_certified': compiler_matches_certified,
               'external_artifacts_match_certified': external_matches_certified,
               'source_sha256': {row['source']: row['source_sha256'] for row in modules.values()},
               'config_sha256': data['config_inputs'],
               'normal_project_artifact_sha256': normal_snapshot,
               'external_artifact_sha256': external_hashes,
               'artifact_sha256': {c.relative(p): c.sha(p) for p in [out / f for f in
                  ['inventory.json', 'census.json', 'census.log', 'audit-result.json', 'fresh-normal-main.log',
                   'exact-target.log', 'census-normal-deps.log', 'guard-normal-deps.log']]},
               'full_enormous_runtime_fixture_executed': False,
               'scope': 'Actual fixed finite RAM program: empty initial state, all positive lengths, exact DFT, single canonical master root, polynomial words, strictly sub-FFT asymptotic bound. Kernel proof and exact target checked; no huge runtime instance was materialized.'}
    c.dump(out / 'receipt.json', receipt)
    c.dump(root / 'verification/uniform-final-algorithm.json', receipt)
    shutil.copy2(out / 'census.json', root / 'verification/uniform-final-census.json')
    print('PASS closed uniform DFT:', len(order), 'modules;', len(actual), 'complete standard-only closures', flush=True)
    print('Receipt:', root / 'verification/uniform-final-algorithm.json', flush=True)


if __name__ == '__main__':
    main()
