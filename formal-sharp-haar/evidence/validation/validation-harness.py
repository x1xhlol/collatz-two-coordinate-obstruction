#!/usr/bin/env python3
"""Record actual reuse and verification checks without publishing local path values."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time

PIN = '84022bcbca17d9797d5578900b4fd109748ea8e7788b84e47d5c37deb48d0a69'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', required=True, type=Path)
    parser.add_argument('--toolchain', required=True, type=Path)
    parser.add_argument('--mathlib', required=True, type=Path)
    parser.add_argument('--private-output', required=True, type=Path)
    parser.add_argument('--relocated-bundle', required=True, type=Path)
    args = parser.parse_args()
    bundle, toolchain, mathlib = args.bundle.resolve(), args.toolchain.resolve(), args.mathlib.resolve()
    private, relocated = args.private_output.resolve(), args.relocated_bundle.resolve()
    assert not private.exists() and not relocated.exists()
    for destination in [private, relocated]:
        for protected in [bundle, toolchain, mathlib]:
            assert not destination.is_relative_to(protected) and not protected.is_relative_to(destination)
    assert not private.is_relative_to(relocated) and not relocated.is_relative_to(private)
    assert sha(bundle / 'source-manifest.json') == PIN
    replay_path = bundle / '.replay/replay-record.json'
    replay_hash = sha(replay_path)
    replay = json.loads(replay_path.read_text())
    assert replay['status'] == 'PASS' and replay['manifest_sha256'] == PIN
    assert len(replay['commands']) == 726 and all(x['exit_code'] == 0 for x in replay['commands'])
    baseline = sha(bundle / '.replay/input-state-before.json')
    assert baseline == sha(bundle / '.replay/input-state-after.json')
    private.mkdir(parents=True)
    public = bundle / 'evidence/validation'
    public.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(Path(__file__), public / 'validation-harness.py')
    record = {'status': 'RUNNING', 'manifest_sha256': PIN, 'replay_record_sha256': replay_hash,
              'input_state_sha256': baseline, 'validation_driver_sha256': sha(Path(__file__)),
              'setup_sha256': sha(bundle / 'scripts/setup.py'), 'replay_driver_sha256': sha(bundle / 'scripts/replay.py'),
              'python_version': sys.version, 'checks': [],
              'reused_setup_pass': False, 'fresh_process_verify_pass': False,
              'relocated_verify_pass': False, 'fresh_external_download_exercised': False,
              'scope': 'Actual existing-installation setup and two new-process verifications, including a relocated bundle with copied internal replay artifacts. All checks reuse the same read-only external libraries. This is not a second source compilation or an external-cache source rebuild.',
              'path_normalization': 'Public command and stdout roots are replaced by BUNDLE, RELOCATED_BUNDLE, TOOLCHAIN and MATHLIB; the current Python executable is labeled PYTHON. Raw command output and setup-result.json remain private.'}

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
        log = public / (label + '.log')
        log.write_text(portable(raw))
        row = {'check': label, 'command': [portable(x) for x in command], 'cwd': portable(str(cwd)),
               'started_utc': started, 'elapsed_seconds': time.monotonic() - tick,
               'exit_code': result.returncode, 'raw_log_sha256': sha(raw_path),
               'public_log': log.relative_to(bundle).as_posix(), 'public_log_sha256': sha(log)}
        record['checks'].append(row)
        write_json(private / 'validation-progress.json', record)
        assert result.returncode == 0, label
        print(json.dumps({'check': label, 'status': 'PASS', 'seconds': row['elapsed_seconds']}), flush=True)
        return raw

    roots = ['--toolchain', str(toolchain), '--mathlib', str(mathlib)]
    execute('setup-reuse', [sys.executable, str(bundle / 'scripts/setup.py'), *roots], bundle)
    assert sha(bundle / 'preflight-input-state.json') == baseline
    setup = json.loads((bundle / 'setup-result.json').read_text())
    assert setup == {'status': 'PASS', 'source_manifest_sha256': PIN, 'toolchain': str(toolchain),
                     'mathlib': str(mathlib), 'reused_toolchain': True, 'reused_mathlib': True}
    shutil.copyfile(bundle / 'setup-result.json', private / 'setup-result.json')
    record['reused_setup_pass'] = True
    options = ['--expected-manifest-sha256', PIN, *roots, '--verify-only']
    raw = execute('fresh-process-verify', [sys.executable, str(bundle / 'scripts/replay.py'), *options], bundle)
    summary = json.loads(raw)
    assert summary['status'] == 'PASS' and summary['record_sha256'] == replay_hash
    record['fresh_process_verify_pass'] = True
    record['verify_summary'] = summary
    assert shutil.disk_usage(relocated.parent).free >= 1024 ** 3
    relocated.mkdir()
    for name in ['source', 'scripts', 'licenses', 'provenance', '.replay']:
        shutil.copytree(bundle / name, relocated / name, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    for name in ['source-manifest.json', 'dependency-pins.json', 'lean-toolchain', 'README.md']:
        shutil.copyfile(bundle / name, relocated / name)
    assert not (relocated / '.external').exists()
    raw = execute('relocated-verify', [sys.executable, str(relocated / 'scripts/replay.py'), *options], relocated)
    moved_summary = json.loads(raw)
    assert moved_summary == summary
    assert sha(replay_path) == replay_hash and sha(relocated / '.replay/replay-record.json') == replay_hash
    assert sha(bundle / 'preflight-input-state.json') == baseline
    record['relocated_verify_pass'] = True
    record['relocated_verify_summary'] = moved_summary
    record['status'] = 'PASS'
    write_json(public / 'validation-record.json', record)
    write_json(private / 'validation-progress.json', record)
    print(json.dumps({'status': 'PASS', 'validation_record_sha256': sha(public / 'validation-record.json'),
                      'replay_record_sha256': replay_hash}), flush=True)


if __name__ == '__main__':
    main()
