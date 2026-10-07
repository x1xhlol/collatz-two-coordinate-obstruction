from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import py_compile
import shutil
import subprocess
import sys
import tempfile

STAGE = Path(__file__).resolve().parent.parent
NATIVE_BUNDLE = Path('/home/ubuntu/collatz-two-coordinate-obstruction/formal-basins-native')
NATIVE_BUILD = Path('/home/ubuntu/collatz-native-basin-notice-build')
RAW_BUNDLE = Path('/home/ubuntu/collatz-two-coordinate-obstruction/formal-raw-occupation')
RAW_BUILD = STAGE.parent / 'formal-raw-occupation-oct3/raw-occupation-portable-replay-hardened'
LEAN_BIN = Path('/dev/shm/collatz-mazur-rebuild/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
MATHLIB = Path('/dev/shm/collatz-mazur-rebuild/mathlib4')
NATIVE_RECORD = '260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c'
RAW_RECORD = '739e2c98cbc0632b5d889b13249e66b03427cb70a36a484aef25107f196daf00'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def fixture_build(original, target, changed_module=None, module_names=()):
    target.mkdir()
    shutil.copyfile(original / 'replay-record.json', target / 'replay-record.json')
    for folder in ['source', 'logs']:
        if (original / folder).exists():
            (target / folder).symlink_to(original / folder, target_is_directory=True)
    if changed_module is None:
        (target / 'modules').symlink_to(original / 'modules', target_is_directory=True)
        return
    (target / 'modules').mkdir()
    for name in module_names:
        rel = Path(name.replace('.', '/') + '.olean')
        p = target / 'modules' / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        if name == changed_module:
            p.write_bytes((original / 'modules' / rel).read_bytes() + b'CORRUPTED_TEST_OBJECT')
        else:
            p.symlink_to(original / 'modules' / rel)

def run_packet(packet):
    root = STAGE / packet
    manifest = json.loads((root / 'bundle-manifest.json').read_text())
    frozen = {'bundle_manifest_sha256': sha(root / 'bundle-manifest.json'),
              'driver_sha256': sha(root / 'verify.py'),
              'source_hashes': {name: sha(root / 'source' / (name + '.lean')) for name in manifest['modules']}}
    checks = {}
    with tempfile.TemporaryDirectory(prefix=packet + '-negative-controls-') as temporary:
        tmp = Path(temporary)
        existing = tmp / 'existing-output'
        existing.mkdir()
        common = {
            '--native-bundle': str(NATIVE_BUNDLE), '--native-build': str(NATIVE_BUILD),
            '--native-record-sha256': NATIVE_RECORD, '--raw-bundle': str(RAW_BUNDLE),
            '--raw-build': str(RAW_BUILD), '--raw-record-sha256': RAW_RECORD,
            '--lean-bin': str(LEAN_BIN), '--mathlib': str(MATHLIB), '--output': str(existing),
        }

        def check(name, expected, *, copied_root=None, changes=None, omit=(), package_only=False):
            args = common | (changes or {})
            command = [sys.executable, str((copied_root or root) / 'verify.py')]
            if package_only:
                command.append('--verify-package-only')
            else:
                for flag, value in args.items():
                    if flag not in omit:
                        command.extend([flag, value])
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            output = result.stdout + result.stderr
            ok = result.returncode != 0 and expected in output
            checks[name] = {'passed': ok, 'exit_code': result.returncode, 'expected_diagnostic': expected,
                            'output_sha256': hashlib.sha256(output.encode()).hexdigest()}
            if not ok:
                raise AssertionError(f'{packet}/{name}: expected rejection {expected!r}; got {output}')

        check('missing_explicit_native_record_pin', '--native-record-sha256 is required',
              omit={'--native-record-sha256'})
        check('missing_explicit_raw_record_pin', '--raw-record-sha256 is required',
              omit={'--raw-record-sha256'})
        check('wrong_native_record_pin', 'Native replay-record pin mismatch',
              changes={'--native-record-sha256': '0' * 64})
        check('wrong_raw_record_pin', 'Raw replay-record pin mismatch',
              changes={'--raw-record-sha256': '0' * 64})

        changed_source = tmp / 'changed-source'
        shutil.copytree(root, changed_source)
        app_source = changed_source / 'source' / (manifest['entry_modules'][0] + '.lean')
        app_source.write_bytes(app_source.read_bytes() + b'\n-- negative control\n')
        check('changed_application_source', 'Package file missing or changed: source/',
              copied_root=changed_source, package_only=True)

        extra_source = tmp / 'extra-source'
        shutil.copytree(root, extra_source)
        (extra_source / 'source/ExtraNegativeControl.lean').write_text('theorem extra_control : True := True.intro\n')
        check('extra_application_source', 'Package Lean source inventory mismatch',
              copied_root=extra_source, package_only=True)

        mixed_build = tmp / 'mixed-native-raw-build'
        fixture_build(RAW_BUILD, mixed_build)
        mixed_record = json.loads((mixed_build / 'replay-record.json').read_text())
        mixed_record['dependency_record_pins']['native'] = '0' * 64
        (mixed_build / 'replay-record.json').write_text(json.dumps(mixed_record))
        check('raw_replay_bound_to_different_native_record', 'Raw-occupation replay used a different native replay',
              changes={'--raw-build': str(mixed_build), '--raw-record-sha256': sha(mixed_build / 'replay-record.json')})

        changed_raw_bundle = tmp / 'changed-raw-source'
        changed_raw_bundle.mkdir()
        shutil.copyfile(RAW_BUNDLE / 'bundle-manifest.json', changed_raw_bundle / 'bundle-manifest.json')
        shutil.copytree(RAW_BUNDLE / 'source', changed_raw_bundle / 'source')
        raw_name = manifest['required_raw_modules'][0]
        raw_source = changed_raw_bundle / 'source' / (raw_name + '.lean')
        raw_source.write_bytes(raw_source.read_bytes() + b'\n-- negative control\n')
        check('changed_raw_dependency_source', 'Raw-occupation source mismatch: ' + raw_name,
              changes={'--raw-bundle': str(changed_raw_bundle)})

        changed_raw_build = tmp / 'changed-raw-object'
        fixture_build(RAW_BUILD, changed_raw_build, raw_name, manifest['required_raw_modules'])
        check('changed_raw_dependency_object', 'Raw-occupation object mismatch: ' + raw_name,
              changes={'--raw-build': str(changed_raw_build)})

        native_name = manifest['required_native_modules'][0]
        changed_native_build = tmp / 'changed-native-object'
        fixture_build(NATIVE_BUILD, changed_native_build, native_name, manifest['required_native_modules'])
        check('changed_native_dependency_object', 'Native object mismatch: ' + native_name,
              changes={'--native-build': str(changed_native_build)})

        cached = tmp / 'cached-helper'
        shutil.copytree(root, cached)
        helper = cached / 'audit_helpers.py'
        good_bytes = helper.read_bytes()
        payload = b'raise RuntimeError("STALE_HELPER_FIXTURE_EXECUTED")\n'
        payload += b'#' + b' ' * (len(good_bytes) - len(payload) - 2) + b'\n'
        assert len(payload) == len(good_bytes)
        helper.write_bytes(payload)
        stamp = helper.stat()
        pyc = Path(py_compile.compile(str(helper), doraise=True,
                   invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP))
        helper.write_bytes(good_bytes)
        os.utime(helper, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        ordinary = subprocess.run([sys.executable, '-c',
            'import importlib.util,sys; s=importlib.util.spec_from_file_location("helper_fixture",sys.argv[1]); '
            'm=importlib.util.module_from_spec(s); s.loader.exec_module(m)', str(helper)],
            capture_output=True, text=True, timeout=30)
        ordinary_text = ordinary.stdout + ordinary.stderr
        assert ordinary.returncode != 0 and 'STALE_HELPER_FIXTURE_EXECUTED' in ordinary_text
        checks['stale_helper_bytecode_fixture_executes_under_ordinary_import'] = {
            'passed': True, 'pyc_sha256': sha(pyc), 'restored_helper_sha256': sha(helper),
            'matching_source_size': len(good_bytes), 'source_timestamp_seconds': int(stamp.st_mtime)}
        hardened = subprocess.run([sys.executable, str(cached / 'verify.py'), '--verify-package-only'],
                                  capture_output=True, text=True, timeout=30)
        hardened_text = hardened.stdout + hardened.stderr
        assert hardened.returncode == 0 and 'Package integrity PASS:' in hardened_text
        assert 'STALE_HELPER_FIXTURE_EXECUTED' not in hardened_text
        checks['verified_byte_loader_bypasses_stale_helper_bytecode'] = {'passed': True, 'exit_code': 0}
        helper.write_bytes(good_bytes + b'\nraise RuntimeError("UNVERIFIED_HELPER_EXECUTED")\n')
        check('changed_helper_source_rejected_before_exec', 'Source-inventory helper hash mismatch',
              copied_root=cached, package_only=True)

    assert sha(root / 'bundle-manifest.json') == frozen['bundle_manifest_sha256']
    assert sha(root / 'verify.py') == frozen['driver_sha256']
    assert {n: sha(root / 'source' / (n + '.lean')) for n in manifest['modules']} == frozen['source_hashes']
    result = {'status': 'PASS', 'packet': packet, 'checks': checks,
              'successful_checks': len(checks), **frozen,
              'negative_control_script_sha256': sha(Path(__file__)),
              'scope': 'Isolated-copy rejection controls and a validated stale-bytecode fixture. No accepted bundle, source, object, or replay record was modified. An already-existing output directory prevents accidental compilation if a negative guard fails.'}
    output = STAGE / 'control-results' / (packet + '.json')
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'packet': packet, 'status': 'PASS', 'checks': len(checks),
                      'result': str(output), 'result_sha256': sha(output)}), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', choices=['formal-inverse-doob-clock', 'formal-raw-divergent-excess'])
    run_packet(parser.parse_args().packet)
