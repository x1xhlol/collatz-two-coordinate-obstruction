from pathlib import Path
import argparse
import hashlib
import json
import re

STAGE = Path(__file__).resolve().parent.parent
EXPECTED = {
    'formal-inverse-doob-clock': {
        'manifest': '5286334a072368bed6565dea18e22b81eade8b2722c983b6d828b05814cc4a25',
        'source_modules': 26, 'constants': 307, 'private_constants': 0,
        'named_declarations': 195, 'private_declarations': 0, 'native': 1496, 'raw': 4,
    },
    'formal-raw-divergent-excess': {
        'manifest': '4fe085b3d2694aa8eb9ab592dc6a6623da5a3d4149dd9c2ccf8202b99ba0dabf',
        'source_modules': 8, 'constants': 63, 'private_constants': 5,
        'named_declarations': 26, 'private_declarations': 4, 'native': 1528, 'raw': 15,
    },
}
DRIVER = '53bfa15414a8578d80e4f4b4ef2cf55055c6a92ce8768a9310aea9c2348051d9'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise AssertionError(message)

def read(path):
    return json.loads(path.read_text())

def check(packet):
    root, out, exp = STAGE / packet, STAGE / 'replays' / packet, EXPECTED[packet]
    require(sha(root / 'bundle-manifest.json') == exp['manifest'], 'Frozen bundle manifest changed')
    require(sha(root / 'verify.py') == DRIVER, 'Approved verifier changed')
    package = read(root / 'bundle-manifest.json')
    rpath = out / 'replay-record.json'
    record_sha = sha(rpath)
    record = read(rpath)
    research = read(root / 'provenance/research-replays' / (packet + '.json'))
    require(record['status'] == 'PASS', 'Replay did not pass')
    require(record['bundle_manifest_sha256'] == exp['manifest'], 'Replay used a different package')
    require(record['module_order'] == package['module_order'], 'Replay source order')
    require(len(record['module_order']) == exp['source_modules'], 'Source count')
    require(record['toolchain'] == package['toolchain'], 'Toolchain provenance')
    for relative, expected in package['files'].items():
        require(sha(root / relative) == expected, 'Package pin: ' + relative)
    expected_units = set(package['modules']) | {package['audit_module']}
    require(set(record['builds']) == set(record['kernel_replays']) == expected_units, 'Build/kernel unit inventory')
    require({p.stem for p in (out / 'source').glob('*.lean')} == expected_units, 'Fresh source file inventory')
    require({p.stem for p in (out / 'modules').glob('*.olean')} == expected_units, 'Fresh object file inventory')
    for name, build in record['builds'].items():
        require(build['exit_code'] == 0 and not build['warnings'], 'Compile status: ' + name)
        kernel = record['kernel_replays'][name]
        require(kernel['exit_code'] == 0, 'Kernel status: ' + name)
        for folder, suffix, expected in [('source', '.lean', build['source_sha256']),
                                         ('modules', '.olean', build['object_sha256']),
                                         ('logs', '.log', build['log_sha256']),
                                         ('logs', '.kernel.log', kernel['log_sha256'])]:
            require(sha(out / folder / (name + suffix)) == expected, 'Fresh artifact pin: ' + name + suffix)
        for suffix in ['.log', '.kernel.log']:
            text = (out / 'logs' / (name + suffix)).read_text()
            require(not re.search(r'warning:|error:|\bsorryAx\b', text), 'Unexpected diagnostic: ' + name)
        if name in package['modules']:
            require(not build['generated_audit_harness'], 'Application flagged as generated: ' + name)
            require(build['source_sha256'] == research['source_hashes'][name] ==
                    package['modules'][name]['source_sha256'] == sha(root / 'source' / (name + '.lean')),
                    'Research/source/replay byte identity: ' + name)
        else:
            require(build['generated_audit_harness'], 'Audit harness flag')
    declarations = {}
    for module, items in record['declarations'].items():
        require(module in package['modules'], 'Unexpected audited module')
        for name, item in items.items():
            require(name not in declarations and set(item['axioms']) <= ALLOWED, 'Duplicate/nonstandard audited constant')
            declarations[name] = {'module': module, **item}
    require(declarations == research['declarations'], 'Compiled constant/axiom inventory differs from research replay')
    audit_log = (out / 'logs' / (package['audit_module'] + '.log')).read_text()
    parsed = {}
    for line in audit_log.splitlines():
        match = re.fullmatch(r'AUDIT_AXIOMS\|([^|]+)\|([^|]+)\|(public|private)\|([^\n]*)', line)
        require(match is not None, 'Invalid audit line')
        module, name, visibility, values = match.groups()
        require(name not in parsed, 'Duplicate audit line')
        parsed[name] = {'module': module, 'visibility': visibility,
                        'axioms': values.split(',') if values else []}
    require(parsed == declarations, 'Audit log/record discrepancy')
    require(len(declarations) == exp['constants'] == record['audited_constant_count'], 'Constant count')
    require(sum(x['visibility'] == 'private' for x in declarations.values()) ==
            exp['private_constants'] == record['audited_private_constant_count'], 'Private constant count')
    named, private = 0, 0
    for module, inventory in record['source_inventories'].items():
        require(inventory['imports'] == package['modules'][module]['imports'], 'Source import inventory')
        require(inventory['sha256'] == package['modules'][module]['source_sha256'], 'Source inventory pin')
        require(not inventory['anonymous_instance_lines'], 'Anonymous source instance')
        for declaration in inventory['named_declarations']:
            require(declaration['name'] in record['declarations'][module], 'Named source declaration omitted')
        for declaration in inventory['private_declarations']:
            require(any(name.endswith('.' + declaration['name']) and item['visibility'] == 'private'
                        for name, item in record['declarations'][module].items()), 'Private declaration omitted')
        named += len(inventory['named_declarations'])
        private += len(inventory['private_declarations'])
    require(named == exp['named_declarations'] and private == exp['private_declarations'], 'Source declaration counts')
    paths = record['paths']
    nr = read(Path(paths['native_build']) / 'replay-record.json')
    rr = read(Path(paths['raw_build']) / 'replay-record.json')
    require(sha(Path(paths['native_build']) / 'replay-record.json') ==
            record['dependency_record_pins']['native'] == '260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c', 'Native accepted record')
    require(sha(Path(paths['raw_build']) / 'replay-record.json') ==
            record['dependency_record_pins']['raw'] == '739e2c98cbc0632b5d889b13249e66b03427cb70a36a484aef25107f196daf00', 'Raw accepted record')
    for group in ['native', 'raw']:
        dependencies = record['authenticated_dependencies'][group]
        require(sorted(dependencies) == package[f'required_{group}_modules'], 'Dependency module set: ' + group)
        require(len(dependencies) == exp[group], 'Dependency count: ' + group)
        exposed = out / ('authenticated-' + group)
        require({str(p.relative_to(exposed)) for p in exposed.rglob('*.olean')} ==
                {n.replace('.', '/') + '.olean' for n in dependencies}, 'Exposed dependency inventory')
        for name, item in dependencies.items():
            rel = Path(name.replace('.', '/'))
            require(sha(Path(paths[group + '_bundle']) / 'source' / rel.with_suffix('.lean')) ==
                    item['source_sha256'], 'Dependency canonical source pin: ' + name)
            require(sha(Path(paths[group + '_build']) / 'modules' / rel.with_suffix('.olean')) ==
                    sha(exposed / rel.with_suffix('.olean')) == item['object_sha256'], 'Dependency object/link pin: ' + name)
            require((exposed / rel.with_suffix('.olean')).is_symlink(), 'Expected isolated object link')
            if group == 'native':
                require(item['source_sha256'] == nr['source_hashes'][name] and
                        item['object_sha256'] == nr['builds'][name]['olean_sha256'] and
                        item['native_dependency_fingerprint'] == nr['dependency_fingerprints'][name], 'Native accepted provenance')
            else:
                require(item['source_sha256'] == rr['builds'][name]['source_sha256'] and
                        item['object_sha256'] == rr['builds'][name]['object_sha256'], 'Raw accepted provenance')
    import_paths = record['lean_path'].split(':')
    require(import_paths[:3] == [str(out / 'modules'), str(out / 'authenticated-raw'), str(out / 'authenticated-native')], 'Isolated LEAN_PATH prefix')
    require(str(root) not in import_paths and str(STAGE) not in import_paths, 'Live application object path exposed')
    require(sha(rpath) == record_sha, 'Replay record changed during artifact audit')
    controls_path = STAGE / 'control-results' / (packet + '.json')
    controls = read(controls_path)
    require(controls['status'] == 'PASS' and controls['successful_checks'] == 13 and
            all(item['passed'] for item in controls['checks'].values()), 'Negative controls did not pass')
    require(controls['bundle_manifest_sha256'] == exp['manifest'] and controls['driver_sha256'] == DRIVER, 'Negative controls used a different verifier/package')
    result = {
        'status': 'PASS', 'packet': packet,
        'review_kind': 'Post-replay artifact and provenance verification; driver was separately reviewed by root before execution',
        'replay_record_sha256': record_sha, 'bundle_manifest_sha256': exp['manifest'], 'verifier_sha256': DRIVER,
        'source_modules_byte_identical_to_research': exp['source_modules'],
        'fresh_build_and_kernel_units': len(expected_units), 'successful_compile_and_kernel_commands': 2 * len(expected_units),
        'audited_constants': exp['constants'], 'audited_private_constants': exp['private_constants'],
        'named_source_declarations': named, 'private_source_declarations': private,
        'authenticated_native_pairs_and_exposed_links': exp['native'], 'authenticated_raw_pairs_and_exposed_links': exp['raw'],
        'all_constant_audit_exactly_matches_research': True,
        'compiler_or_kernel_warnings': False, 'nonstandard_axioms': False,
        'negative_control_count': 13, 'negative_control_record_sha256': sha(controls_path),
        'artifact_check_script_sha256': sha(Path(__file__)),
        'scope': 'Every manifest-pinned package file, fresh source/object/compile/kernel log, source inventory, compiled audit entry, accepted dependency record, selected upstream source/object pair, and exposed object link was rechecked. The replay is additive and does not rebuild the native, raw, or Mathlib dependencies.',
    }
    target = STAGE / 'artifact-check-results' / (packet + '.json')
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2))
    print('Artifact certificate SHA256:', sha(target))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', choices=EXPECTED)
    check(parser.parse_args().packet)
