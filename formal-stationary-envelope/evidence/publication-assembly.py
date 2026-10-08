#!/usr/bin/env python3
"""Assemble a source-only publication tree after the replay and validation pass."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

PIN = 'c3a623f8f06ec66824099ca3b4e40e5448533c0dfb0ce389cee70e52879dc28c'
FORBIDDEN_PARTS = {'.replay', '.external', '__pycache__'}
COMPILED_ENDINGS = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig', '.so', '.pyc')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(root, name):
    parts = PurePosixPath(name)
    require(not parts.is_absolute() and '..' not in parts.parts and '\\' not in name,
            'Invalid relative publication path')
    path = root / name
    require(path.resolve().is_relative_to(root.resolve()), 'Publication path escapes root')
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', required=True, type=Path)
    parser.add_argument('--publication-additions', required=True, type=Path)
    parser.add_argument('--destination', required=True, type=Path)
    parser.add_argument('--preparation', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    bundle, additions = args.bundle.resolve(), args.publication_additions.resolve()
    destination, preparation = args.destination.resolve(), args.preparation.resolve()
    require(not destination.exists(), 'Publication staging directory must be fresh')
    for protected in [bundle, additions, preparation]:
        require(not destination.is_relative_to(protected) and not protected.is_relative_to(destination),
                'Publication destination overlaps an input tree')
    require(sha(bundle / 'source-manifest.json') == PIN, 'Unexpected frozen execution manifest')
    manifest = json.loads((bundle / 'source-manifest.json').read_text())
    output = bundle / '.replay'
    replay_path = output / 'replay-record.json'
    replay_bytes = replay_path.read_bytes()
    replay_hash = hashlib.sha256(replay_bytes).hexdigest()
    replay = json.loads(replay_bytes)
    require(replay['status'] == 'PASS' and replay['manifest_sha256'] == PIN and
            replay['modules'] == manifest['modules_in_topological_order'], 'Incomplete or wrong source replay')
    commands = manifest['planned_successful_commands']
    require(len(replay['commands']) == commands and all(row['exit_code'] == 0 for row in replay['commands']),
            'Replay command count or status mismatch')
    require(len(replay['results']) == manifest['source_count'] + 1 and
            replay['audit_module'] == 'IntegerEnvelopeCompleteAudit', 'Replay result count mismatch')
    validation_path = additions / 'evidence/validation/validation-record.json'
    validation_bytes = validation_path.read_bytes()
    validation_hash = hashlib.sha256(validation_bytes).hexdigest()
    validation = json.loads(validation_bytes)
    require(validation['status'] == 'PASS' and validation['manifest_sha256'] == PIN and
            validation['replay_record_sha256'] == replay_hash, 'Missing completed validation')
    require(all(validation[key] for key in
        ['reused_setup_pass', 'fresh_process_verify_pass', 'relocated_verify_pass']), 'Incomplete validation checks')
    require(validation['fresh_external_download_exercised'] is False,
            'Guide scope must be reviewed for a different external setup mode')
    require(sha(additions / 'evidence/validation/validation-harness.py') ==
            validation['validation_driver_sha256'], 'Changed validation harness')
    for row in validation['checks']:
        require(row['exit_code'] == 0 and sha(safe_path(additions, row['public_log'])) == row['public_log_sha256'],
                'Changed or failed validation log')
    require(len(validation['checks']) == 3, 'Unexpected validation scope')
    license_bytes = (additions / 'provenance/envelope-license-review.json').read_bytes()
    license_hash = hashlib.sha256(license_bytes).hexdigest()
    licenses = json.loads(license_bytes)
    require(licenses['execution_manifest_sha256'] == PIN and
            set(licenses['modules']) == set(manifest['modules']), 'Wrong combined license scope')
    for module, entry in manifest['modules'].items():
        require(sha(bundle / entry['source']) == entry['sha256'] == licenses['modules'][module]['sha256'],
                'Changed source or license mapping')
    for name, expected in manifest['pinned_files'].items():
        require(sha(safe_path(bundle, name)) == expected, 'Changed frozen bundled input: ' + name)
    for name, expected in replay['input_states'].items():
        require(sha(output / name) == expected, 'Changed replay input state')
    require(sha(output / 'input-state-before.json') == sha(output / 'input-state-after.json'),
            'Before/after input states differ')
    progress_bytes = (output / 'progress.json').read_bytes()
    progress_hash = hashlib.sha256(progress_bytes).hexdigest()
    require(json.loads(progress_bytes)['status'] == 'PASS', 'Unfinished progress record')
    expected_logs = {row['module'] + '.' + row['stage'] + '.log': row['log_sha256']
                     for row in replay['commands']}
    require(len(expected_logs) == commands and
            {path.name for path in (output / 'logs').glob('*.log')} == set(expected_logs),
            'Wrong replay log set')
    for name, expected in expected_logs.items():
        require(sha(output / 'logs' / name) == expected, 'Changed replay command log')

    destination.mkdir(parents=True)
    selected = set()

    def put(name, data):
        require(not any(part in FORBIDDEN_PARTS for part in PurePosixPath(name).parts) and
                not name.endswith(COMPILED_ENDINGS), 'Compiled/private artifact in publication selection')
        target = safe_path(destination, name)
        require(not target.exists(), 'Duplicate publication target: ' + name)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        selected.add(name)

    def copy(source, name):
        require(source.is_file() and not source.is_symlink(), 'Missing or linked publication source')
        put(name, source.read_bytes())
        require(sha(source) == sha(destination / name), 'Publication copy mismatch')

    frozen = {'source-manifest.json', *manifest['pinned_files'],
              *(entry['source'] for entry in manifest['modules'].values())}
    for name in sorted(frozen):
        copy(safe_path(bundle, name), name)
    require(sha(destination / 'source-manifest.json') == PIN, 'Copied execution manifest changed')
    for entry in manifest['modules'].values():
        require(sha(safe_path(destination, entry['source'])) == entry['sha256'],
                'Copied source differs from execution manifest')
    for name, expected in manifest['pinned_files'].items():
        require(sha(safe_path(destination, name)) == expected,
                'Copied bundled input differs from execution manifest: ' + name)
    for path in sorted(additions.rglob('*')):
        if path.is_file():
            name = path.relative_to(additions).as_posix()
            require(name not in frozen, 'Publication appendix replaces frozen input: ' + name)
            copy(path, name)
    for name in ['replay-record.json', 'progress.json', 'input-state-before.json', 'input-state-after.json']:
        copy(output / name, 'evidence/reference-replay/' + name)
    audit_source = 'source/' + replay['audit_module'] + '.lean'
    expected_audit_source = replay['results'][replay['audit_module']]['source_sha256']
    require(sha(output / audit_source) == expected_audit_source, 'Changed generated audit source')
    copy(output / audit_source, 'evidence/reference-replay/' + audit_source)
    require(sha(destination / 'evidence/reference-replay' / audit_source) == expected_audit_source,
            'Copied generated audit source differs from replay')
    for name in sorted(expected_logs):
        copy(output / 'logs' / name, 'evidence/reference-replay/logs/' + name)
    reference = destination / 'evidence/reference-replay'
    require(sha(reference / 'replay-record.json') == validation['replay_record_sha256'] == replay_hash,
            'Copied replay record differs from completed validation')
    require(sha(reference / 'progress.json') == progress_hash, 'Copied progress record changed')
    for name, expected in replay['input_states'].items():
        require(sha(safe_path(reference, name)) == expected, 'Copied replay input state changed')
    for name, expected in expected_logs.items():
        require(sha(reference / 'logs' / name) == expected, 'Copied replay command log changed')
    require(sha(destination / 'evidence/validation/validation-record.json') == validation_hash,
            'Copied validation record changed')
    require(sha(destination / 'evidence/validation/validation-harness.py') ==
            validation['validation_driver_sha256'], 'Copied validation harness changed')
    for row in validation['checks']:
        require(sha(safe_path(destination, row['public_log'])) == row['public_log_sha256'],
                'Copied validation log changed')
    require(sha(destination / 'provenance/envelope-license-review.json') == license_hash,
            'Copied source-license inventory changed')

    audit = replay['audit']
    external_count = validation['verify_summary']['external_objects']
    paragraph = (
        f"The reference replay completed on {replay['finished_utc'][:10]}: all {manifest['source_count']:,} "
        f"source modules and the generated audit passed all {commands:,} strict compilation and official "
        f"kernel-check commands. The audit covered {audit['audited_constant_rows']:,} module-header rows "
        f"over {audit['audited_distinct_names']:,} distinct internal constants, including "
        f"{audit['audited_private_rows']:,} rows with encoded private names. Header membership and actual "
        "owner modules are recorded separately. Every audited declaration uses only the permitted "
        f"standard axioms. The identical before/after states include {external_count:,} external compiled objects.\n\n"
        "Setup using existing installations, new-process verification and relocated verification also passed. "
        "The relocation check copied completed internal replay artifacts and reused the same external libraries; "
        "it did not compile the sources again. See [the validation record](evidence/validation/validation-record.json) "
        "and [preserved execution evidence](evidence/README.md).\n\n"
        f"The [reference replay record](evidence/reference-replay/replay-record.json) has SHA-256 `{replay_hash}`."
    )
    guide = (preparation / 'REPLAY-GUIDE-corrected.template.md').read_text()
    require(guide.count('{{REFERENCE_VERIFICATION}}') == 1, 'Unexpected guide template')
    guide = guide.replace('{{REFERENCE_VERIFICATION}}', paragraph)
    require('{{' not in guide, 'Unfilled guide placeholder')
    put('REPLAY-GUIDE.md', guide.encode())
    copy(preparation / 'EVIDENCE-README-corrected.template.md', 'evidence/README.md')
    copy(Path(__file__), 'evidence/publication-assembly.py')
    files = {name: {'sha256': sha(destination / name), 'bytes': (destination / name).stat().st_size}
             for name in sorted(selected)}
    publication = {'schema': 1, 'status': 'SEALED_SOURCE_AND_TEXTUAL_EVIDENCE',
        'execution_manifest_sha256': PIN, 'replay_record_sha256': replay_hash,
        'validation_record_sha256': validation_hash, 'files': files,
        'file_count': len(files), 'total_bytes': sum(row['bytes'] for row in files.values()),
        'scope': 'Exactly selected source, execution scripts, scoped licenses/provenance, publication documentation and textual replay evidence. No internal compiled artifacts or external libraries are distributed. External cache source correspondence is not asserted.'}
    (destination / 'publication-manifest.json').write_text(json.dumps(publication, indent=2, sort_keys=True) + '\n')
    files['publication-manifest.json'] = {
        'sha256': sha(destination / 'publication-manifest.json'),
        'bytes': (destination / 'publication-manifest.json').stat().st_size}
    plan = {'schema': 1, 'status': 'READY_FOR_PARENT_REVIEW',
        'destination_directory': 'formal-stationary-envelope', 'source_root_label': 'PUBLICATION_STAGE',
        'execution_manifest_sha256': PIN, 'publication_manifest_sha256': sha(destination / 'publication-manifest.json'),
        'files': files, 'file_count': len(files), 'total_bytes': sum(row['bytes'] for row in files.values()),
        'largest_file': max(files, key=lambda name: files[name]['bytes']),
        'largest_file_bytes': max(row['bytes'] for row in files.values()),
        'excluded': ['.replay/**', '.external/**', '**/__pycache__/**', 'all compiled artifacts',
                     'raw local setup outputs', 'unselected preparation files', 'distribution-plan.json'],
        'publication_action': 'Parent may copy exactly these reviewed relative files to formal-stationary-envelope. This script only creates a private staging tree and performs no public repository mutation.'}
    (destination / 'distribution-plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': plan['status'], 'files': plan['file_count'], 'bytes': plan['total_bytes'],
        'publication_manifest_sha256': plan['publication_manifest_sha256'],
        'distribution_plan_sha256': sha(destination / 'distribution-plan.json')}))


if __name__ == '__main__':
    main()
