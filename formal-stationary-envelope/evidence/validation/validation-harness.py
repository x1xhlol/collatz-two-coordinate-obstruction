#!/usr/bin/env python3
"""Verify a completed envelope replay from fresh processes and a relocated copy."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import time

PIN = 'c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def safe_path(root, name):
    parts = PurePosixPath(name)
    require(not parts.is_absolute() and '..' not in parts.parts and '\\' not in name,
            'Invalid relative path')
    path = root / name
    require(path.resolve().is_relative_to(root.resolve()), 'Path escapes bundle')
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', required=True, type=Path)
    parser.add_argument('--toolchain', required=True, type=Path)
    parser.add_argument('--mathlib', required=True, type=Path)
    parser.add_argument('--private-output', required=True, type=Path)
    parser.add_argument('--relocated-bundle', required=True, type=Path)
    parser.add_argument('--publication-additions', required=True, type=Path)
    args = parser.parse_args()
    bundle, toolchain, mathlib = args.bundle.resolve(), args.toolchain.resolve(), args.mathlib.resolve()
    private, relocated = args.private_output.resolve(), args.relocated_bundle.resolve()
    additions = args.publication_additions.resolve()
    require(not private.exists() and not relocated.exists(), 'Validation destinations must be fresh')
    destinations = [private, relocated, additions]
    for target in destinations:
        for protected in [bundle, toolchain, mathlib]:
            require(not target.is_relative_to(protected) and not protected.is_relative_to(target),
                    'Validation destination overlaps a protected root')
    for i, target in enumerate(destinations):
        for other in destinations[i + 1:]:
            require(not target.is_relative_to(other) and not other.is_relative_to(target),
                    'Validation destinations overlap')
    require(sha(bundle / 'source-manifest.json') == PIN, 'Unexpected execution manifest')
    manifest = json.loads((bundle / 'source-manifest.json').read_text())
    require(manifest['status'] == 'FROZEN', 'Execution bundle is not frozen')
    replay_path = bundle / '.replay/replay-record.json'
    replay_hash = sha(replay_path)
    replay = json.loads(replay_path.read_text())
    require(replay['status'] == 'PASS' and replay['manifest_sha256'] == PIN,
            'The complete source replay must pass before validation')
    require(len(replay['commands']) == manifest['planned_successful_commands'] and
            all(row['exit_code'] == 0 for row in replay['commands']), 'Incomplete source replay')
    baseline = sha(bundle / '.replay/input-state-before.json')
    require(baseline == sha(bundle / '.replay/input-state-after.json'), 'Replay input states differ')
    private.mkdir(parents=True)
    public = additions / 'evidence/validation'
    public.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(Path(__file__), public / 'validation-harness.py')
    record = {'status': 'RUNNING', 'manifest_sha256': PIN, 'replay_record_sha256': replay_hash,
        'input_state_sha256': baseline, 'validation_driver_sha256': sha(Path(__file__)),
        'setup_sha256': sha(bundle / 'scripts/setup.py'),
        'replay_driver_sha256': sha(bundle / 'scripts/replay.py'), 'python_version': sys.version,
        'checks': [], 'reused_setup_pass': False, 'fresh_process_verify_pass': False,
        'relocated_verify_pass': False, 'fresh_external_download_exercised': False,
        'scope': 'Actual setup using existing installations and two new-process verifications. Relocation copies the completed internal artifacts and reuses the same external libraries; it is not another source compilation or a source rebuild of external caches.',
        'path_normalization': 'Public commands and output use BUNDLE, RELOCATED_BUNDLE, TOOLCHAIN, MATHLIB and PYTHON. Raw output and setup-result.json remain private.'}

    def portable(text):
        for root, label in [(bundle, 'BUNDLE'), (relocated, 'RELOCATED_BUNDLE'),
                            (toolchain, 'TOOLCHAIN'), (mathlib, 'MATHLIB')]:
            text = text.replace(str(root), label)
        return text.replace(sys.executable, 'PYTHON')

    def execute(label, command, cwd):
        print(json.dumps({'check': label, 'status': 'STARTED'}), flush=True)
        started = datetime.now(timezone.utc).isoformat(timespec='seconds')
        tick = time.monotonic()
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
        raw = result.stdout + result.stderr
        raw_path = private / (label + '.raw.log')
        raw_path.write_text(raw)
        public_log = public / (label + '.log')
        public_log.write_text(portable(raw))
        row = {'check': label, 'command': [portable(arg) for arg in command],
            'cwd': portable(str(cwd)), 'started_utc': started,
            'elapsed_seconds': time.monotonic() - tick, 'exit_code': result.returncode,
            'raw_log_sha256': sha(raw_path), 'public_log': public_log.relative_to(additions).as_posix(),
            'public_log_sha256': sha(public_log)}
        record['checks'].append(row)
        write_json(private / 'validation-progress.json', record)
        require(result.returncode == 0, 'Validation failed: ' + label)
        print(json.dumps({'check': label, 'status': 'PASS',
                          'elapsed_seconds': row['elapsed_seconds']}), flush=True)
        return raw

    roots = ['--toolchain', str(toolchain), '--mathlib', str(mathlib)]
    pin_args = ['--expected-manifest-sha256', PIN]
    execute('setup-reuse', [sys.executable, str(bundle / 'scripts/setup.py'), *pin_args, *roots], bundle)
    require(sha(bundle / 'preflight-input-state.json') == baseline, 'Setup preflight changed baseline')
    setup = json.loads((bundle / 'setup-result.json').read_text())
    require(setup == {'status': 'PASS', 'source_manifest_sha256': PIN,
        'toolchain': str(toolchain), 'mathlib': str(mathlib),
        'reused_toolchain': True, 'reused_mathlib': True}, 'Unexpected setup record')
    shutil.copyfile(bundle / 'setup-result.json', private / 'setup-result.json')
    record['reused_setup_pass'] = True
    options = [*pin_args, *roots, '--verify-only']
    raw = execute('fresh-process-verify',
        [sys.executable, str(bundle / 'scripts/replay.py'), *options], bundle)
    summary = json.loads(raw)
    require(summary['status'] == 'PASS' and summary['record_sha256'] == replay_hash,
            'Unexpected verification summary')
    record['fresh_process_verify_pass'] = True
    record['verify_summary'] = summary

    require(shutil.disk_usage(relocated.parent).free >= 1024 ** 3,
            'At least 1 GiB free is required for the relocated artifact copy')
    relocated.mkdir()
    selected = {'source-manifest.json', *manifest['pinned_files'],
                *(entry['source'] for entry in manifest['modules'].values())}
    for name in sorted(selected):
        source, target = safe_path(bundle, name), safe_path(relocated, name)
        require(source.is_file() and not source.is_symlink(), 'Invalid relocation input')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        require(sha(source) == sha(target), 'Relocation input copy mismatch')
    shutil.copytree(bundle / '.replay', relocated / '.replay')
    require(not (relocated / '.external').exists(), 'Unexpected external artifacts in relocation')
    raw = execute('relocated-verify',
        [sys.executable, str(relocated / 'scripts/replay.py'), *options], relocated)
    moved_summary = json.loads(raw)
    require(moved_summary == summary, 'Relocated verification differs')
    require(sha(replay_path) == replay_hash and
            sha(relocated / '.replay/replay-record.json') == replay_hash,
            'Replay record changed during validation')
    require(sha(bundle / 'preflight-input-state.json') == baseline, 'Preflight state changed')
    record.update(status='PASS', relocated_verify_pass=True, relocated_verify_summary=moved_summary)
    write_json(public / 'validation-record.json', record)
    write_json(private / 'validation-progress.json', record)
    print(json.dumps({'status': 'PASS', 'validation_record_sha256': sha(public / 'validation-record.json'),
                      'replay_record_sha256': replay_hash}), flush=True)


if __name__ == '__main__':
    main()
