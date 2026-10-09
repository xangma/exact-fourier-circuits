"""Source-only verification primitives copied from the independently tested coherent audit driver.
No scratch-source discovery or baseline artifact loader is included.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
D = Path(__file__).resolve().parent
R = D.parent
L = R / 'lean'

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(path: Path) -> str:
    return str(path.relative_to(R)) if path.is_relative_to(R) else str(path)

def dump(path: Path, data) -> None:
    path.write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')

def unique(paths):
    return list(dict.fromkeys(paths))

def strip_comments(source: str) -> str:
    """Retain line structure and strings; remove nested Lean block/line comments."""
    out, i, depth, string = ([], 0, 0, False)
    while i < len(source):
        pair = source[i:i + 2]
        ch = source[i]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if ch == '\n' else ' ')
                i += 1
        elif string:
            out.append(ch)
            i += 1
            if ch == '\\' and i < len(source):
                out.append(source[i])
                i += 1
            elif ch == '"':
                string = False
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        else:
            out.append(ch)
            string = ch == '"'
            i += 1
    if depth:
        raise ValueError('unterminated Lean comment')
    return ''.join(out)

def imports(source: str) -> list[str]:
    code = strip_comments(source)
    result = []
    for line in code.splitlines():
        if not line.strip() or line.strip() in {'prelude', 'module'}:
            continue
        match = re.fullmatch('\\s*(?:(?:public|meta)\\s+)?import\\s+(.+?)\\s*', line)
        if not match:
            break
        for name in match.group(1).split():
            if not re.fullmatch("[A-Za-z_][A-Za-z_0-9'.]*", name):
                raise ValueError('unsupported Lean import syntax: ' + name)
            result.append(name)
    return unique(result)

def violations(source: str) -> list[str]:
    code = strip_comments(source)
    code = re.sub('"(?:\\\\.|[^"\\\\])*"', '""', code)
    patterns = {'admission': '\\b(?:sorry|admit|native_decide)\\b', 'axiom_declaration': '(?m)^\\s*(?:(?:private|public|protected)\\s+)*axiom\\s', 'raised_proof_limit': '\\bset_option\\s+(?:maxHeartbeats|maxRecDepth|synthInstance.maxHeartbeats)\\b'}
    return [name for name, pattern in patterns.items() if re.search(pattern, code)]

def pins() -> dict:
    manifest = json.loads((L / 'UPSTREAM_MANIFEST.json').read_text())
    if len(manifest['files']) != 51:
        raise ValueError('upstream closure must have exactly 51 pinned sources')
    for row in manifest['files']:
        path = L / row['path']
        if sha(path) != row['sha256']:
            raise ValueError('upstream source drift: ' + str(path))
    if (L / 'lean-toolchain').read_text().strip() != manifest['lean_toolchain']:
        raise ValueError('Lean toolchain pin drift')
    mathlib = L / '.lake/packages/mathlib'
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib, text=True).strip()
    if revision != manifest['mathlib_revision']:
        raise ValueError('Mathlib revision drift')
    return manifest

def validate(data: dict):
    pins()
    for path, digest in data['config_inputs'].items():
        if sha(R / path) != digest:
            raise ValueError('configuration drift: ' + path)
    for row in data['project_modules'].values():
        if sha(R / row['source']) != row['source_sha256']:
            raise ValueError('source drift: ' + row['source'])
        unacceptable = set(row['violations'])
        if data['approved_historical_source_limit_hashes'].get(row['module']) == row['source_sha256']:
            unacceptable.discard('raised_proof_limit')
        if unacceptable:
            raise ValueError('source proof-policy violation: ' + row['module'] + repr(sorted(unacceptable)))
    if data['missing_sources']:
        raise ValueError('unresolved project import sources')

def stage(data: dict):
    validate(data)
    out = D / 'stage'
    if out.exists():
        raise ValueError('stage already exists; keep this packet immutable or explicitly remove only own stage')
    out.mkdir()
    for name in data['topological_order']:
        row = data['project_modules'][name]
        dest = out / (name.replace('.', '/') + '.lean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(R / row['source'], dest)
    dump(D / 'stage-manifest.json', {'inventory_sha256': sha(D / 'inventory.json'), 'sources': {name.replace('.', '/') + '.lean': data['project_modules'][name]['source_sha256'] for name in data['topological_order']}, 'copied_project_oleans': len(data.get('baseline', {}).get('reused_modules', []))})
    print('Staged', len(data['topological_order']), 'sources; verified baseline artifacts', len(data.get('baseline', {}).get('reused_modules', [])))

def checked_env(data: dict):
    env = dict(os.environ)
    env['LEAN_PATH'] = ':'.join([str(D / 'stage'), *data['external_only_paths']])
    env.pop('LEAN_SRC_PATH', None)
    return env

def run(data: dict, audit: bool, workers: int=1):
    validate(data)
    seal = json.loads((D / 'held-seal.json').read_text())
    if seal['inventory_sha256'] != sha(D / 'inventory.json'):
        raise ValueError('held seal does not cover current inventory')
    manifest = json.loads((D / 'stage-manifest.json').read_text())
    if manifest['inventory_sha256'] != seal['inventory_sha256']:
        raise ValueError('staged sources do not match held inventory')
    for rel, digest in manifest['sources'].items():
        if sha(D / 'stage' / rel) != digest:
            raise ValueError('stage source drift: ' + rel)
    build_dir = D / 'build-logs'
    build_dir.mkdir(exist_ok=True)
    env = checked_env(data)
    dump(D / 'isolated-build-env.json', {'LEAN_PATH': env['LEAN_PATH'], 'lean': data['lean'], 'flags': ['-DautoImplicit=false'], 'copied_project_oleans': len(data.get('certified_reuse', {}).get('reused_modules', [])), 'baseline_receipt_sha256': data.get('certified_reuse', {}).get('receipt_sha256')})
    print('DRIVER', os.getpid(), flush=True)
    progress_file = D / 'fresh-build-progress.json'
    progress = json.loads(progress_file.read_text()) if progress_file.is_file() else {}
    order = data['topological_order']
    if not set(progress) <= set(order):
        raise ValueError('progress contains a module outside the sealed cone')
    for index, name in enumerate(order):
        src = D / 'stage' / (name.replace('.', '/') + '.lean')
        log = build_dir / (name + '.log')
        if name in progress:
            if progress[name]['inventory_sha256'] != seal['inventory_sha256'] or not src.with_suffix('.olean').is_file() or sha(src.with_suffix('.olean')) != progress[name]['artifact_sha256'] or (not log.is_file()) or (sha(log) != progress[name]['log_sha256']):
                raise ValueError('fresh-build progress/artifact drift: ' + name)
            print('RESUME', index + 1, name, flush=True)
            continue
        if src.with_suffix('.olean').exists():
            raise ValueError('unrecorded cached artifact in fresh stage: ' + name)
    done = set(progress)
    pending = [name for name in order if name not in done]
    active = {}
    rss_cap_kib = 80 * 1024 * 1024

    def record_active():
        dump(D / 'active-job.json', {'driver_pid': os.getpid(), 'workers': workers, 'cwd': str(L), 'jobs': [{'module': name, 'child_pid': p.pid, 'log': str(log)} for name, (p, log, handle) in active.items()], 'stop': 'kill -TERM ' + str(os.getpid())})

    def terminate_owned(signum=None, frame=None):
        for proc, _, _ in active.values():
            if proc.poll() is None:
                proc.terminate()
        if signum is not None:
            raise SystemExit(128 + signum)
    previous_handlers = {s: signal.signal(s, terminate_owned) for s in [signal.SIGTERM, signal.SIGINT]}

    def lean_rss_kib():
        rows = subprocess.check_output(['ps', '-axo', 'rss,command'], text=True).splitlines()
        return sum((int(row.split(None, 1)[0]) for row in rows[1:] if '/bin/lean ' in row and row.split(None, 1)[0].isdigit()))

    def launch(name):
        src = D / 'stage' / (name.replace('.', '/') + '.lean')
        row = data['project_modules'][name]
        if sha(src) != row['source_sha256'] or sha(R / row['source']) != row['source_sha256']:
            raise ValueError('source drift before compilation: ' + name)
        log = build_dir / (name + '.log')
        args = [data['lean'], '-DautoImplicit=false', '-R', str(D / 'stage'), '-o', str(src.with_suffix('.olean')), str(src)]
        deps = subprocess.run([data['lean'], '--deps', str(src)], cwd=L, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (build_dir / (name + '.deps.log')).write_text(deps.stdout)
        if deps.returncode:
            raise RuntimeError('Lean dependency resolution failed: ' + name)
        for line in deps.stdout.splitlines():
            if line.endswith('.olean'):
                dependency = Path(line)
                dependency = (dependency if dependency.is_absolute() else L / dependency).resolve()
                if not any((dependency.is_relative_to(Path(p)) for p in [str(D / 'stage'), *data['external_only_paths']])):
                    raise RuntimeError('historical project artifact fallback: ' + line)
        handle = log.open('w')
        proc = subprocess.Popen(args, cwd=L, env=env, stdout=handle, stderr=subprocess.STDOUT)
        active[name] = (proc, log, handle)
        print('BUILD', len(done) + len(active), '/', len(order), name, 'PID', proc.pid, 'LOG', log, flush=True)
        record_active()
    try:
        while pending or active:
            for name, (proc, log, handle) in list(active.items()):
                status = proc.poll()
                if status is None:
                    continue
                handle.close()
                del active[name]
                if status:
                    raise RuntimeError('default Lean failed: ' + name + ' (' + str(log) + ')')
                src = D / 'stage' / (name.replace('.', '/') + '.lean')
                progress[name] = {'inventory_sha256': seal['inventory_sha256'], 'artifact_sha256': sha(src.with_suffix('.olean')), 'log_sha256': sha(log)}
                done.add(name)
                dump(progress_file, progress)
                print('PASS', len(done), '/', len(order), name, flush=True)
                record_active()
            ready = [name for name in pending if all((dep not in data['project_modules'] or dep in done for dep in data['project_modules'][name]['imports']))]
            while ready and len(active) < workers:
                if lean_rss_kib() + 12 * 1024 * 1024 > rss_cap_kib:
                    break
                name = ready.pop(0)
                pending.remove(name)
                launch(name)
            if pending and (not active) and (not ready):
                raise ValueError('dependency deadlock in sealed source cone')
            if pending or active:
                time.sleep(0.2)
        validate(data)
    finally:
        terminate_owned()
        for proc, _, handle in active.values():
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            handle.close()
        for signum, previous in previous_handlers.items():
            signal.signal(signum, previous)
    (D / 'active-job.json').unlink(missing_ok=True)
    dump(D / 'build-result.json', {'passed': True, 'finished_utc': datetime.now(timezone.utc).isoformat(), 'inventory_sha256': seal['inventory_sha256'], 'fresh_project_modules': len(data.get('certified_reuse', {}).get('fresh_modules', data['topological_order'])), 'reused_baseline_project_modules': len(data.get('certified_reuse', {}).get('reused_modules', [])), 'project_artifacts': {name: sha(D / 'stage' / (name.replace('.', '/') + '.olean')) for name in data['topological_order']}, 'default_driver_limits': True, 'historical_source_limit_settings': data['historical_source_limit_settings'], 'uniform_algorithm_verified': False})
    if audit:
        census(data)

def census(data: dict):
    if not (D / 'build-result.json').is_file():
        raise ValueError('fresh coherent build required before census')
    source = '\n'.join(('import ' + m for m in data['targets'])) + '\nimport Lean\n'
    source += 'open Lean Elab Command in\nrun_cmd do\n let env ← getEnv\n'
    dump(D / 'census-modules.json', data['topological_order'])
    source += ' let raw ← liftIO <| IO.FS.readFile ' + json.dumps(str(D / 'census-modules.json')) + '\n'
    source += ' let names : Array String ← match Json.parse raw >>= fromJson? with\n  | .ok names => pure names\n  | .error message => throwError "{message}"\n let mut mods : Std.HashSet String := {}\n for name in names do mods := mods.insert name\n'
    source += ' let mut entries : Array Json := #[]\n for (name, _) in env.constants.toList do\n  let origin := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx]!.toString)\n  if origin.any (fun m => mods.contains m) then\n   let axs ← collectAxioms name\n   for ax in axs do\n    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do\n     throwError m!"Nonstandard axiom {ax} in {name}"\n   entries := entries.push (Json.mkObj [("name", toJson name.toString), ("module", toJson origin),\n     ("axioms", toJson (axs.toList.map toString))])\n'
    source += ' liftIO <| IO.FS.writeFile ' + json.dumps(str(D / 'census.json')) + ' (Json.compress (.arr entries))\n'
    source += ' liftIO <| IO.FS.writeFile ' + json.dumps(str(D / 'environment-imports.json')) + ' (Json.compress (toJson (env.header.moduleNames.toList.map toString)))\n'
    source += ' logInfo m!"Audited {entries.size} defining-module closures"\n'
    path = D / 'stage/Census.lean'
    path.write_text(source)
    with (D / 'census.log').open('w') as handle:
        result = subprocess.run([data['lean'], '-DautoImplicit=false', '-R', str(D / 'stage'), str(path)], cwd=L, env=checked_env(data), stdout=handle, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('census failed; see census.log')
    entries = sorted(json.loads((D / 'census.json').read_text()), key=lambda e: (e['module'], e['name']))
    dump(D / 'census.json', entries)
    public = sorted((e['name'] for e in entries if not e['name'].startswith('_private.')))
    private = sorted((e['name'] for e in entries if e['name'].startswith('_private.')))
    dump(D / 'public-declarations.json', public)
    dump(D / 'private-environment-declarations.json', private)
    imported = set(json.loads((D / 'environment-imports.json').read_text()))
    if not set(data['topological_order']) <= imported:
        raise ValueError('source modules missing from final imported environment')
    validate(data)
    dump(D / 'audit-result.json', {'passed': True, 'closures': len(entries), 'public_generated': len(public), 'private': len(private), 'standard_axioms_only': True, 'uniform_algorithm_verified': False, 'inventory_sha256': sha(D / 'inventory.json')})
    print('CENSUS PASS', len(entries), 'public/generated', len(public), 'private', len(private))
