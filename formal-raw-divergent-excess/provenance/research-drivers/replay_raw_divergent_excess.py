"""Authenticated fresh additive replay of the raw divergent-excess supplement."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import types

ROOT = Path(__file__).resolve().parent
NATIVE = Path('/home/ubuntu/collatz-two-coordinate-obstruction/formal-basins-native')
NATIVE_BUILD = Path('/home/ubuntu/collatz-native-basin-notice-build')
RAW_ROOT = ROOT.parent / 'formal-raw-occupation-oct3'
RAW_BUILD = RAW_ROOT / 'raw-occupation-fresh-replay'
OUT = ROOT / 'raw-divergent-excess-fresh-replay'
BINS = Path('/dev/shm/collatz-mazur-rebuild/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
MATHLIB = Path('/dev/shm/collatz-mazur-rebuild/mathlib4')
SOURCE_MANIFEST_PIN = 'f153366e6f779c3669b1d904467925c8ba62e296207a1b70910296a37328471c'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    script_pin = sha(Path(__file__))
    records = {
        NATIVE / 'replay-manifest.json':
            'efc8bc1226fb158341a4626eeafaf5c97b9284da1a2d137de38b7db035cbb230',
        NATIVE_BUILD / 'replay-record.json':
            '260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c',
        RAW_BUILD / 'replay-record.json':
            'f2852527b47fbdefde5e669ef974cd5dd0bfecabc35fd2ea75a6cd6908a9a814',
        RAW_ROOT / 'raw-source-manifest.json':
            '2c5c5d27182beb062d73e81448281715e0315726066b8d19e7bf3d8f810239e1',
    }
    for path, expected in records.items():
        require(sha(path) == expected, f'Record changed: {path}')
    native = json.loads((NATIVE_BUILD / 'replay-record.json').read_text())
    manifest = json.loads((NATIVE / 'replay-manifest.json').read_text())
    raw = json.loads((RAW_BUILD / 'replay-record.json').read_text())
    require(native['status'] == raw['status'] == 'PASS', 'Dependency replay did not pass')
    version = subprocess.check_output([str(BINS / 'lean'), '--version'], text=True).strip()
    require('commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc' in version,
            'Unexpected Lean revision')
    mathlib_revision = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip()
    require(mathlib_revision == '5450b53e5ddc75d46418fabb605edbf36bd0beb6',
            'Unexpected Mathlib revision')

    def authenticate():
        for folder, revision in [(MATHLIB, manifest['mathlib_revision'])] + [
                (MATHLIB / '.lake/packages' / name, revision)
                for name, revision in manifest['dependency_revisions'].items()]:
            require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=folder,
                    text=True).strip() == revision, f'Library revision changed: {folder}')
            require(not subprocess.check_output(
                    ['git', 'status', '--porcelain', '--untracked-files=no'], cwd=folder,
                    text=True).strip(), f'Tracked library changes: {folder}')
        require(sha(MATHLIB / 'lake-manifest.json') == manifest['mathlib_lake_manifest_sha256'],
                'Mathlib package manifest changed')
        for m, expected in native['source_hashes'].items():
            rel = Path(m.replace('.', '/'))
            require(sha(NATIVE / 'source' / rel.with_suffix('.lean')) == expected,
                    f'Native source changed: {m}')
            require(sha(NATIVE_BUILD / 'modules' / rel.with_suffix('.olean')) ==
                    native['builds'][m]['olean_sha256'], f'Native object changed: {m}')
        for module, result in raw['results'].items():
            require(sha(RAW_BUILD / 'source' / (module + '.lean')) == result['source_sha256'],
                    f'Raw upstream copied source changed: {module}')
            require(sha(RAW_BUILD / 'modules' / (module + '.olean')) == result['object_sha256'],
                    f'Raw upstream object changed: {module}')
        for module, expected in raw['source_hashes'].items():
            require(sha(RAW_ROOT / (module + '.lean')) == expected,
                    f'Frozen raw upstream source changed: {module}')
        require(sha(RAW_ROOT / 'replay_raw_occupation.py') == raw['script_sha256'],
                'Raw upstream replay driver changed')
        for path, expected in records.items():
            require(sha(path) == expected, f'Record changed: {path}')

    authenticate()
    source_manifest_path = ROOT / 'excess-source-manifest.json'
    require(sha(source_manifest_path) == SOURCE_MANIFEST_PIN, 'Source manifest changed')
    source_manifest = json.loads(source_manifest_path.read_text())
    MODULES = source_manifest['modules']
    SOURCE_PINS = source_manifest['source_hashes']
    require(len(MODULES) == len(set(MODULES)) and set(MODULES) == set(SOURCE_PINS),
            'Duplicate or unpinned source module')
    helper_bytes = (ROOT / 'audit_helpers.py').read_bytes()
    require(hashlib.sha256(helper_bytes).hexdigest() == source_manifest['audit_helpers_sha256'],
            'Source audit helper changed')
    audit_helpers = types.ModuleType("raw_divergent_excess_source_audit")
    audit_helpers.__file__ = str(ROOT / "audit_helpers.py")
    exec(compile(helper_bytes, audit_helpers.__file__, "exec"),
         vars(audit_helpers))
    audit_helpers.ROOT = ROOT
    inventory = {m: audit_helpers.source_inventory(m) for m in MODULES}
    seen = set()
    for m in MODULES:
        clean = audit_helpers.scrub_lean((ROOT / (m + '.lean')).read_text())
        require(not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|trustLevel)\b', clean),
                f'Forbidden source bypass token: {m}')
        require(not inventory[m]['anonymous_instance_lines'], f'Uninventoried anonymous instance: {m}')
        for imported in inventory[m]['imports']:
            require(imported in seen or imported in raw['source_hashes'] or imported in native['source_hashes'] or
                    imported.split('.')[0] in {'Lean', 'Init', 'Std', 'Mathlib', 'Batteries', 'Qq', 'Aesop', 'ProofWidgets', 'Plausible', 'ImportGraph', 'LeanSearchClient'},
                    f'Unreplayed or out-of-order import {m} -> {imported}')
        seen.add(m)
    source_hashes = {m: sha(ROOT / (m + '.lean')) for m in MODULES}
    require(source_hashes == SOURCE_PINS, 'Frozen source pins missing or changed')
    require(not OUT.exists(), 'Fresh output already exists')
    for part in ['source', 'modules', 'logs']:
        (OUT / part).mkdir(parents=True)
    for m in MODULES:
        shutil.copyfile(ROOT / (m + '.lean'), OUT / 'source' / (m + '.lean'))
        require(sha(OUT / 'source' / (m + '.lean')) == source_hashes[m],
                f'Copy changed: {m}')
    wanted = ', '.join('"' + m + '"' for m in MODULES)
    imports = '\n'.join('import ' + m for m in MODULES)
    audit = f'''{imports}
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if [{wanted}].contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{{mod.toString}}|{{name.toString}}|{{visibility}}|{{names}}"
'''
    (OUT / 'source' / 'RawDivergentExcessAudit.lean').write_text(audit)
    library_path = [str(MATHLIB / '.lake/packages' / name / '.lake/build/lib/lean')
                    for name in manifest['dependency_revisions']]
    library_path += [str(MATHLIB / '.lake/build/lib/lean'), str(BINS.parent / 'lib/lean')]
    env = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_PLUGIN_PATH']:
        env.pop(key, None)
    env['PATH'] = str(BINS) + ':' + env.get('PATH', '')
    env['LEAN_PATH'] = ':'.join([str(OUT / 'modules'), str(RAW_BUILD / 'modules'),
                               str(NATIVE_BUILD / 'modules'), *library_path])
    results = {}
    for module in [*MODULES, 'RawDivergentExcessAudit']:
        if module in source_hashes:
            require(sha(OUT / 'source' / (module + '.lean')) == source_hashes[module],
                    f'Copied source changed before compilation: {module}')
        command = [str(BINS / 'lean'), '-j1', '--root=' + str(OUT / 'source'),
                   '-o', str(OUT / 'modules' / (module + '.olean')),
                   str(OUT / 'source' / (module + '.lean'))]
        start = time.monotonic()
        run = subprocess.run(command, cwd=OUT / 'source', env=env, text=True, capture_output=True)
        log = OUT / 'logs' / (module + '.compile.log')
        log.write_text(run.stdout + run.stderr)
        require(run.returncode == 0, log.read_text())
        require('sorryAx' not in log.read_text(), 'Unexpected sorry axiom')
        require('warning:' not in log.read_text(), f'Unexpected compiler warning: {module}')
        result = {'compile_exit_code': run.returncode, 'compile_seconds': time.monotonic() - start,
                  'source_sha256': sha(OUT / 'source' / (module + '.lean')),
                  'object_sha256': sha(OUT / 'modules' / (module + '.olean')),
                  'compile_log_sha256': sha(log)}
        start = time.monotonic()
        run = subprocess.run([str(BINS / 'leanchecker'), module], cwd=OUT / 'source', env=env,
                             text=True, capture_output=True)
        log = OUT / 'logs' / (module + '.kernel.log')
        log.write_text(run.stdout + run.stderr)
        require(run.returncode == 0, log.read_text())
        require('warning:' not in log.read_text(), f'Unexpected kernel warning: {module}')
        result.update(kernel_exit_code=run.returncode, kernel_seconds=time.monotonic() - start,
                      kernel_log_sha256=sha(log))
        results[module] = result
        print(json.dumps({'module': module, 'status': 'PASS'}), flush=True)
    audited = {}
    audit_log = (OUT / 'logs' / 'RawDivergentExcessAudit.compile.log').read_text()
    for module, name, visibility, values in re.findall(
            r'^AUDIT_AXIOMS\|([^|\n]+)\|([^|\n]+)\|(public|private)\|([^\n]*)$', audit_log, re.M):
        require(module in MODULES and name not in audited, 'Unexpected audit entry')
        axioms = [value for value in values.split(',') if value]
        require(set(axioms) <= ALLOWED, f'Nonstandard axiom in {name}: {axioms}')
        audited[name] = {'module': module, 'visibility': visibility, 'axioms': axioms}
    for m in MODULES:
        require(any(v['module'] == m for v in audited.values()), f'Missing module audit: {m}')
        for declaration in inventory[m]['named_declarations']:
            require(declaration['name'] in audited and audited[declaration['name']]['module'] == m,
                    f'Missing named declaration: {m}.{declaration["name"]}')
        for declaration in inventory[m]['private_declarations']:
            require(any(v['module'] == m and v['visibility'] == 'private' and
                        name.endswith('.' + declaration['name']) for name, v in audited.items()),
                    f'Missing private declaration: {m}.{declaration["name"]}')
    authenticate()
    require(sha(source_manifest_path) == SOURCE_MANIFEST_PIN, 'Source manifest changed during replay')
    require(sha(ROOT / 'audit_helpers.py') == source_manifest['audit_helpers_sha256'],
            'Source audit helper changed during replay')
    for m, expected in source_hashes.items():
        require(sha(ROOT / (m + '.lean')) == expected, f'Source changed during replay: {m}')
        require(sha(OUT / 'source' / (m + '.lean')) == expected, f'Copy changed during replay: {m}')
    for m, result in results.items():
        for folder, suffix, key in [
                ('source', '.lean', 'source_sha256'),
                ('modules', '.olean', 'object_sha256'),
                ('logs', '.compile.log', 'compile_log_sha256'),
                ('logs', '.kernel.log', 'kernel_log_sha256')]:
            require(sha(OUT / folder / (m + suffix)) == result[key],
                    f'Fresh output changed during replay: {m} {suffix}')
    require(sha(Path(__file__)) == script_pin, 'Replay driver changed during execution')
    record = {
        'status': 'PASS', 'modules': MODULES, 'results': results,
        'source_hashes': source_hashes, 'declarations': audited, 'allowed_axioms': sorted(ALLOWED),
        'audited_constant_count': len(audited),
        'audited_private_constant_count': sum(v['visibility'] == 'private' for v in audited.values()),
        'record_pins': {str(p): s for p, s in records.items()},
        'source_manifest_sha256': SOURCE_MANIFEST_PIN,
        'audit_helpers_sha256': source_manifest['audit_helpers_sha256'],
        'source_inventory': inventory,
        'named_declaration_count': sum(len(v['named_declarations']) for v in inventory.values()),
        'private_declaration_count': sum(len(v['private_declarations']) for v in inventory.values()),
        'authenticated_native_source_and_object_count': len(native['source_hashes']),
        'authenticated_raw_source_module_count': len(raw['source_hashes']),
        'authenticated_raw_source_and_object_unit_count': len(raw['results']),
        'lean_path': env['LEAN_PATH'], 'lean_version': version, 'mathlib_revision': mathlib_revision,
        'dependency_revisions': manifest['dependency_revisions'],
        'mathlib_lake_manifest_sha256': manifest['mathlib_lake_manifest_sha256'],
        'script_sha256': script_pin,
        'scope': 'Eight supplementary research modules and their all-constant audit were freshly compiled and individually kernel-replayed. The previously replayed sixteen raw-occupation source modules and generated audit objects, all live frozen raw source pins, and 1602 native source/object pairs were authenticated before and after. Pinned clean Mathlib/package source revisions and package manifest were checked before and after. Authenticated upstream objects and Mathlib/Lean caches were reused; this is an additive replay, not a complete upstream rebuild. No live raw development object directory, floor, cylinder-energy, or public application object directory was in LEAN_PATH. For an odd root with injective shortcut orbit, the final theorem gives every eventual raw-trace lower comparison below 1/clockDrift + actualFirstHitDensity u/(wholeOrbitCorrection u*log(3/2)); the excess is positive when u is a unit modulo three. This does not assert existence of such an injective root, a raw upper bound, capped saturation, uniform integrability, or universal eventual periodicity.'
    }
    (OUT / 'replay-record.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'record': str(OUT / 'replay-record.json'),
                      'audited_constant_count': len(audited)}))


if __name__ == '__main__':
    main()
