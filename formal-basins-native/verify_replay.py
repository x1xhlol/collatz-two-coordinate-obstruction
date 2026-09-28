#!/usr/bin/env python3
"""Check the pinned joint-scale native basin source closure in a separate output directory."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from replay_audit_helpers import lean_code, audit_output


def sha(data):
    return hashlib.sha256(data).hexdigest()


def validate_reuse_pins(record_path, reuse, manifest):
    if reuse.get('status') != 'PASS':
        raise ValueError('Reuse record is not a passing check: ' + str(record_path))
    for key in ('lean_version', 'mathlib_revision'):
        if reuse.get(key) != manifest[key]:
            raise ValueError('Reuse record toolchain pin mismatch (' + key + '): ' + str(record_path))
    package_keys = ('mathlib_lake_manifest_sha256', 'dependency_revisions')
    present = [key in reuse for key in package_keys]
    if any(present):
        if not all(present):
            raise ValueError('Reuse record has incomplete package pins: ' + str(record_path))
        pins = reuse
        provenance = {'mode': 'record_fields'}
    else:
        command = reuse.get('audit', {}).get('command')
        if not isinstance(command, list) or not command or not isinstance(command[-1], str):
            raise ValueError('Legacy reuse record lacks its original RootAudit command: ' + str(record_path))
        audit_path = Path(command[-1])
        if not audit_path.is_absolute() or audit_path.name != 'RootAudit.lean':
            raise ValueError('Legacy reuse record has no absolute RootAudit source path: ' + str(record_path))
        original_manifest = audit_path.parent.parent / 'replay-manifest.json'
        if not original_manifest.is_file():
            raise ValueError('Legacy reuse original bundle manifest is unavailable: ' + str(original_manifest))
        data = original_manifest.read_bytes()
        if sha(data) != reuse.get('manifest_sha256'):
            raise ValueError('Legacy reuse original manifest hash mismatch: ' + str(original_manifest))
        pins = json.loads(data)
        provenance = {'mode': 'legacy_original_manifest', 'manifest': str(original_manifest),
                      'manifest_sha256': sha(data)}
    for key in ('lean_version', 'mathlib_revision', *package_keys):
        if pins.get(key) != manifest[key]:
            raise ValueError('Reuse package pin mismatch (' + key + '): ' + str(record_path))
    return provenance


def find_reuse_object(record_path, reuse, old, name):
    relative = Path(name.replace('.', '/') + '.olean')
    candidates = []
    for value in (old.get('object_path'),
                  str(Path(reuse['object_directory']) / relative) if reuse.get('object_directory') else None,
                  str(record_path.parent / 'modules' / relative), old.get('origin')):
        if value is None:
            continue
        if not isinstance(value, str) or not value:
            raise ValueError('Invalid reuse object path: ' + name)
        path = Path(value)
        path = (path if path.is_absolute() else record_path.parent / path).resolve()
        if path not in candidates:
            candidates.append(path)
    for path in candidates:
        if not path.exists():
            continue
        if not path.is_file() or sha(path.read_bytes()) != old.get('olean_sha256'):
            raise ValueError('Reuse object mismatch: ' + name + ' at ' + str(path))
        return path
    return None


def existing_object_directories(builds):
    directories = []
    for name, item in builds.items():
        path = Path(item['object_path']).resolve()
        directory = path
        for _ in name.split('.'):
            directory = directory.parent
        if directory / (name.replace('.', '/') + '.olean') != path:
            raise ValueError('Existing object is not at its module path: ' + name)
        if directory not in directories:
            directories.append(directory)
    for name, item in builds.items():
        relative = Path(name.replace('.', '/') + '.olean')
        actual = next((directory / relative for directory in directories if (directory / relative).exists()), None)
        if actual is None or not actual.is_file() or sha(actual.read_bytes()) != item['olean_sha256']:
            raise ValueError('Existing object search path would shadow the checked object: ' + name)
    return directories


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--reuse-record', type=Path, action='append', default=[],
                        help='Optional exact source/dependency/object-checked replay record; repeat for disjoint checked closures. Default rebuilds all bundled modules.')
    parser.add_argument('--audit-existing', action='store_true',
                        help='With --reuse-record, validate every existing object without copying it, then freshly compile only RootAudit.')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    if args.audit_existing and len(args.reuse_record) != 1:
        parser.error('--audit-existing requires exactly one --reuse-record')
    bundle = Path(__file__).resolve().parent
    source = bundle / 'source'
    manifest_data = (bundle / 'replay-manifest.json').read_bytes()
    manifest = json.loads(manifest_data)
    output = args.output.resolve()
    if output.exists():
        raise ValueError('Output directory must be new: ' + str(output))
    mathlib, lean = args.mathlib.resolve(), args.lean.resolve()
    lake = lean.with_name('lake')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib, text=True).strip()
    if version != manifest['lean_version'] or revision != manifest['mathlib_revision']:
        raise ValueError('Lean or mathlib pin mismatch')
    lake_manifest = (mathlib / 'lake-manifest.json').read_bytes()
    if sha(lake_manifest) != manifest['mathlib_lake_manifest_sha256']:
        raise ValueError('Mathlib dependency manifest mismatch')
    for name, expected in manifest['dependency_revisions'].items():
        package = mathlib / '.lake/packages' / name
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=package, text=True).strip()
        if actual != expected:
            raise ValueError('Mathlib dependency revision mismatch: ' + name)
    sources, deps = {}, {}

    def visit(name):
        if name in sources:
            return
        data = (source / (name.replace('.', '/') + '.lean')).read_bytes()
        if sha(data) != manifest['source_hashes'].get(name):
            raise ValueError('Source hash mismatch: ' + name)
        code = lean_code(data.decode())
        if re.search(r'\b(?:sorry|admit)\b|^\s*axiom\s', code, re.M) and name != manifest['unused_registry_module']:
            raise ValueError('Unfinished or axiomatic source: ' + name)
        imports = re.findall(r'^import ([A-Za-z0-9_.]+)\s*$', code, re.M)
        if len(imports) != len(re.findall(r'\bimport\b', code)):
            raise ValueError('Unparsed import: ' + name)
        sources[name] = data
        deps[name] = [d for d in imports if (source / (d.replace('.', '/') + '.lean')).exists()]
        for dep in deps[name]:
            visit(dep)

    visit(manifest['top_module'])
    if set(sources) != set(manifest['source_hashes']) or deps != manifest['dependencies']:
        raise ValueError('Source closure or imports differ from the pinned manifest')

    @lru_cache(None)
    def fingerprint(name):
        return sha(json.dumps([name, sha(sources[name]), [(d, fingerprint(d)) for d in deps[name]]],
                              separators=(',', ':')).encode())

    if any(fingerprint(n) != manifest['dependency_fingerprints'][n] for n in sources):
        raise ValueError('Dependency fingerprint mismatch')
    audit_source = (source / 'RootAudit.lean').read_bytes()
    if sha(audit_source) != manifest['root_audit_source_sha256']:
        raise ValueError('Root audit source mismatch')
    reuses = [(path.resolve(), json.loads(path.read_text())) for path in args.reuse_record]
    reuse_pin_checks = {str(path): validate_reuse_pins(path, reuse, manifest) for path, reuse in reuses}
    modules, logs = output / 'modules', output / 'build-logs'
    modules.mkdir(parents=True)
    logs.mkdir()
    env = os.environ.copy()
    library = subprocess.check_output([str(lake), 'env', 'printenv', 'LEAN_PATH'], cwd=mathlib, env=env, text=True).strip()
    env['LEAN_PATH'] = str(modules) + os.pathsep + library
    record = dict(status='RUNNING', source_hashes=manifest['source_hashes'],
                  dependency_fingerprints=manifest['dependency_fingerprints'],
                  lean_version=version, mathlib_revision=revision,
                  mathlib_lake_manifest_sha256=manifest['mathlib_lake_manifest_sha256'],
                  dependency_revisions=manifest['dependency_revisions'],
                  manifest_sha256=sha(manifest_data),
                  audit_existing=args.audit_existing,
                  object_directory=None if args.audit_existing else str(modules),
                  reuse_records={str(path): sha(path.read_bytes()) for path, _ in reuses},
                  reuse_pin_checks=reuse_pin_checks, builds={})

    def save():
        temporary = output / 'replay-record.tmp'
        temporary.write_text(json.dumps(record, indent=2))
        temporary.replace(output / 'replay-record.json')

    def copy_validated(name):
        for record_path, reuse in reuses:
            old = reuse.get('builds', {}).get(name)
            if not old or old.get('exit_code') != 0 or old.get('dependency_fingerprint') != fingerprint(name):
                continue
            if reuse.get('source_hashes', {}).get(name) != sha(sources[name]):
                continue
            origin = find_reuse_object(record_path, reuse, old, name)
            if origin is None:
                continue
            if not args.audit_existing:
                target = modules / (name.replace('.', '/') + '.olean')
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(origin, target)
                if sha(target.read_bytes()) != old['olean_sha256']:
                    raise ValueError('Copied object mismatch: ' + name)
            return dict(exit_code=0, mode='validated_exact_dependency_closure',
                        dependency_fingerprint=fingerprint(name), source_sha256=sha(sources[name]),
                        olean_sha256=old['olean_sha256'], origin=str(origin),
                        object_path=str(origin if args.audit_existing else target),
                        reuse_record=str(record_path))
        if args.audit_existing:
            raise ValueError('Existing record is incomplete or differs from the required closure: ' + name)
        return None

    def compile_one(name):
        if args.audit_existing and name != 'RootAudit':
            raise ValueError('Existing-object audit cannot compile dependency modules')
        path = source / (name.replace('.', '/') + '.lean')
        before = path.read_bytes()
        target = modules / (name.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), '-j1', '--root=' + str(source), '-o', str(target), str(path)]
        started = time.monotonic()
        result = subprocess.run(command, cwd=source, env=env, text=True, capture_output=True, timeout=1800)
        log = logs / (name + '.log')
        log.write_text(result.stdout + result.stderr)
        if path.read_bytes() != before:
            raise ValueError('Source changed during compilation: ' + name)
        if result.returncode:
            raise RuntimeError('Lean failed: ' + name + '\n' + log.read_text())
        item = dict(exit_code=0, mode='compiled_fresh', source_sha256=sha(before),
                    object_path=str(target),
                    olean_sha256=sha(target.read_bytes()), log_sha256=sha(log.read_bytes()),
                    elapsed_seconds=time.monotonic() - started, command=command)
        if name in sources:
            item['dependency_fingerprint'] = fingerprint(name)
        return item

    try:
        pending, running = set(sources), {}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while pending or running:
                ready = sorted(n for n in pending if set(deps[n]) <= record['builds'].keys())
                for name in ready:
                    reused = copy_validated(name)
                    if reused:
                        pending.remove(name)
                        record['builds'][name] = reused
                    elif len(running) < args.jobs:
                        pending.remove(name)
                        running[pool.submit(compile_one, name)] = name
                save()
                if not running:
                    if pending and not ready:
                        raise ValueError('Dependency cycle')
                    continue
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    name = running.pop(future)
                    record['builds'][name] = future.result()
                    print(f'{len(record["builds"])}/{len(sources)} {name}', flush=True)
        if args.audit_existing:
            directories = existing_object_directories(record['builds'])
            record['object_directories'] = [str(path) for path in directories]
            env['LEAN_PATH'] = os.pathsep.join([*(str(path) for path in directories), library])
        record['audit'] = compile_one('RootAudit')
        record['axioms'] = audit_output((logs / 'RootAudit.log').read_text(), manifest['declarations'])
        if (bundle / 'replay-manifest.json').read_bytes() != manifest_data:
            raise ValueError('Manifest changed during replay')
        if any((source / (n.replace('.', '/') + '.lean')).read_bytes() != data for n, data in sources.items()):
            raise ValueError('Source changed during replay')
        if (source / 'RootAudit.lean').read_bytes() != audit_source:
            raise ValueError('Audit source changed during replay')
        record['status'] = 'PASS'
        print(json.dumps(dict(status='PASS', modules=len(sources), audited_roots=len(record['axioms']))), flush=True)
    except Exception as error:
        record['status'] = 'FAILED'
        record['error'] = str(error)
        raise
    finally:
        save()


if __name__ == '__main__':
    main()
