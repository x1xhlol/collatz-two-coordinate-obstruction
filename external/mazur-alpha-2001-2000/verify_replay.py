#!/usr/bin/env python3
"""Check the pinned alpha=2001/2000 source closure in a separate output directory."""
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--reuse-record', type=Path,
                        help='Optional exact source/dependency/object-checked replay record; default rebuilds all first-party modules.')
    parser.add_argument('--audit-existing', action='store_true',
                        help='With --reuse-record, validate every existing object without copying it, then freshly compile only RootAudit.')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    if args.audit_existing and not args.reuse_record:
        parser.error('--audit-existing requires --reuse-record')
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
    reuse = json.loads(args.reuse_record.read_text()) if args.reuse_record else None
    if reuse and (reuse.get('status') != 'PASS' or reuse.get('lean_version') != version or
                  reuse.get('mathlib_revision') != revision):
        raise ValueError('Reuse record is not a passing check of the pinned toolchain')
    modules, logs = output / 'modules', output / 'build-logs'
    modules.mkdir(parents=True)
    logs.mkdir()
    env = os.environ.copy()
    library = subprocess.check_output([str(lake), 'env', 'printenv', 'LEAN_PATH'], cwd=mathlib, env=env, text=True).strip()
    audited_modules = args.reuse_record.resolve().parent / 'modules' if args.audit_existing else modules
    env['LEAN_PATH'] = str(audited_modules) + os.pathsep + library
    record = dict(status='RUNNING', source_hashes=manifest['source_hashes'],
                  dependency_fingerprints=manifest['dependency_fingerprints'],
                  lean_version=version, mathlib_revision=revision,
                  manifest_sha256=sha(manifest_data),
                  audit_existing=args.audit_existing, builds={})

    def save():
        temporary = output / 'replay-record.tmp'
        temporary.write_text(json.dumps(record, indent=2))
        temporary.replace(output / 'replay-record.json')

    def copy_validated(name):
        if not reuse:
            return None
        old = reuse.get('builds', {}).get(name)
        if not old or old.get('exit_code') != 0 or old.get('dependency_fingerprint') != fingerprint(name):
            if args.audit_existing:
                raise ValueError('Existing record is incomplete or has a different dependency closure: ' + name)
            return None
        if reuse.get('source_hashes', {}).get(name) != sha(sources[name]):
            if args.audit_existing:
                raise ValueError('Existing record source mismatch: ' + name)
            return None
        origin = args.reuse_record.resolve().parent / 'modules' / (name.replace('.', '/') + '.olean')
        if not origin.is_file() or sha(origin.read_bytes()) != old.get('olean_sha256'):
            raise ValueError('Reuse object mismatch: ' + name)
        if not args.audit_existing:
            target = modules / (name.replace('.', '/') + '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(origin, target)
            if sha(target.read_bytes()) != old['olean_sha256']:
                raise ValueError('Copied object mismatch: ' + name)
        return dict(exit_code=0, mode='validated_exact_dependency_closure',
                    dependency_fingerprint=fingerprint(name), source_sha256=sha(sources[name]),
                    olean_sha256=old['olean_sha256'], origin=str(origin))

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
        record['audit'] = compile_one('RootAudit')
        record['axioms'] = audit_output((logs / 'RootAudit.log').read_text(), [manifest['declaration']])
        if (bundle / 'replay-manifest.json').read_bytes() != manifest_data:
            raise ValueError('Manifest changed during replay')
        if any((source / (n.replace('.', '/') + '.lean')).read_bytes() != data for n, data in sources.items()):
            raise ValueError('Source changed during replay')
        if (source / 'RootAudit.lean').read_bytes() != audit_source:
            raise ValueError('Audit source changed during replay')
        record['status'] = 'PASS'
        print(json.dumps(dict(status='PASS', modules=len(sources), axioms=record['axioms'])), flush=True)
    except Exception as error:
        record['status'] = 'FAILED'
        record['error'] = str(error)
        raise
    finally:
        save()


if __name__ == '__main__':
    main()
