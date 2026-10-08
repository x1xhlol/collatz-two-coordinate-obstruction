#!/usr/bin/env python3
"""Prepare, inventory, and freeze a source-only integer-envelope replay bundle."""
from __future__ import annotations

import argparse
from collections import Counter
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil

HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
RESEARCH = CANDIDATE.parent
SHARP = RESEARCH / 'formal-fair-haar-energy-oct8/full-sharp-replay-corrected'
NATIVE = Path('/home/ubuntu/collatz-two-coordinate-obstruction/formal-basins-native')
FLOOR = Path('/home/ubuntu/collatz-periodic-census-portable-replay-oct3')
PERIODIC = RESEARCH / 'formal-periodic-census-floor-oct3'
PRIOR_INVENTORY = CANDIDATE / 'provisional-closure-inventory.json'
SOURCE_ORDER = ['new-envelope', 'expanded-compatibility', 'envelope-compatibility', 'weighted-source',
                'high-trace', 'gamma-free', 'periodic-census', 'sharp-frozen', 'native']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def copy(source, destination):
    require(source.is_file() and not source.is_symlink(), 'Missing or linked source: ' + str(source))
    destination.parent.mkdir(parents=True, exist_ok=True)
    require(not destination.exists(), 'Destination already exists: ' + str(destination))
    shutil.copyfile(source, destination)
    require(sha(source) == sha(destination), 'Copy mismatch')


def load_helper():
    path = SHARP / 'scripts/source_inventory.py'
    require(sha(path) == '1446f49676bf270ef9291843d760e1cb2e273645521b97092a5059a03b0703a5',
            'Changed reviewed source-inventory helper')
    spec = importlib.util.spec_from_file_location('envelope_source_inventory', path)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return helper


def combined_compatibility():
    initial_path = HERE / 'envelope-compatibility-overrides.json'
    expanded_path = HERE / 'expanded-compatibility-overrides.json'
    initial = json.loads(initial_path.read_text())
    expanded = json.loads(expanded_path.read_text())
    require(not (set(initial['patches']) & set(expanded['patches'])), 'Overlapping compatibility ledgers')
    for module, entry in expanded['patches'].items():
        result = entry.get('strict_diagnostic', {})
        require(result.get('exit_code') == 0 and result.get('source_sha256') == entry['candidate_sha256'],
                'Missing strict candidate check: ' + module)
        require(sha(entry['candidate_source']) == entry['candidate_sha256'] and
                sha(entry['patch']) == entry['patch_sha256'] and
                sha(result['log']) == result['log_sha256'], 'Changed compatibility artifact')
        require(not any(token in Path(result['log']).read_text() for token in ['warning:', 'error:', 'sorryAx']),
                'Unclean strict candidate log')
    return {'patches': {**initial['patches'], **expanded['patches']}}, {
        str(initial_path): sha(initial_path), str(expanded_path): sha(expanded_path)}


def input_catalog():
    prior = json.loads(PRIOR_INVENTORY.read_text())
    for path, expected in prior['input_record_pins'].items():
        require(sha(path) == expected, 'Changed prior source record: ' + path)
    catalog = {}

    def add(group, root, hashes, record):
        for module, expected in hashes.items():
            path = root / Path(*module.split('.')).with_suffix('.lean')
            require(path.is_file() and not path.is_symlink() and sha(path) == expected,
                    'Changed catalog source: ' + str(path))
            catalog.setdefault(module, []).append({'group': group, 'path': str(path),
                'sha256': expected, 'record': str(record) if record else None})

    new_hashes = {'.'.join(path.relative_to(CANDIDATE / 'source').with_suffix('').parts): sha(path)
                  for path in (CANDIDATE / 'source').rglob('*.lean')}
    add('new-envelope', CANDIDATE / 'source', new_hashes, None)
    compatibility, compatibility_pins = combined_compatibility()
    expanded = json.loads((HERE / 'expanded-compatibility-overrides.json').read_text())
    add('expanded-compatibility', HERE / 'expanded-compatibility-source',
        {module: entry['candidate_sha256'] for module, entry in expanded['patches'].items()},
        HERE / 'expanded-compatibility-overrides.json')
    initial = json.loads((HERE / 'envelope-compatibility-overrides.json').read_text())
    add('envelope-compatibility', HERE / 'compatibility-source',
        {module: entry['candidate_sha256'] for module, entry in initial['patches'].items()},
        HERE / 'envelope-compatibility-overrides.json')
    for group, folder in [('weighted-source', 'weighted-source-fresh-replay'),
                          ('high-trace', 'high-trace-and-capped-moment-fresh-replay'),
                          ('gamma-free', 'gamma-free-first-hit-coefficient-fresh-replay')]:
        root = PERIODIC / folder
        record = root / 'replay-record.json'
        add(group, root / 'source', json.loads(record.read_text())['source_hashes'], record)
    record = FLOOR / 'replay-record.json'
    add('periodic-census', FLOOR / 'source',
        {module: inv['sha256'] for module, inv in json.loads(record.read_text())['source_inventories'].items()}, record)
    record = SHARP / 'source-manifest.json'
    add('sharp-frozen', SHARP / 'source',
        {module: entry['sha256'] for module, entry in json.loads(record.read_text())['modules'].items()}, record)
    record = NATIVE / 'replay-manifest.json'
    add('native', NATIVE / 'source', json.loads(record.read_text())['source_hashes'], record)
    return catalog, {**prior['input_record_pins'], **compatibility_pins}, compatibility


def inventory(specification):
    helper = load_helper()
    catalog, records, compatibility = input_catalog()
    patches = json.loads((SHARP / 'provenance/native-linter-patches.json').read_text())['patches']
    wiki = json.loads((SHARP / 'provenance/wikipedia-shard.json').read_text())
    allowed_variants = {module: {entry['original_sha256'], entry['candidate_sha256']}
                        for module, entry in patches.items()}
    allowed_variants['FormalConjectures.Wikipedia.CollatzConjecture'] = {
        wiki['original']['sha256'], wiki['reviewed']['sha256']}
    allowed_variants.update({module: {entry['original_sha256'], entry['candidate_sha256']}
                            for module, entry in compatibility['patches'].items()})
    order, active, modules, variants = [], set(), {}, {}

    def visit(module):
        require(module in catalog, 'Missing internal source: ' + module)
        if module in modules:
            return
        require(module not in active, 'Cyclic source import: ' + module)
        active.add(module)
        candidates = catalog[module]
        chosen = candidates[0]
        hashes = {entry['sha256'] for entry in candidates}
        if len(hashes) > 1:
            require(module in allowed_variants and hashes == allowed_variants[module],
                    'Unreviewed source variation: ' + module)
            require(chosen['group'] in {'sharp-frozen', 'envelope-compatibility', 'expanded-compatibility'},
                    'Unexpected override selection: ' + module)
            variants[module] = candidates
        inv = helper.source_inventory(Path(chosen['path']), module)
        require(not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|trustLevel)\b',
                              helper.scrub_lean(Path(chosen['path']).read_text())),
                'Forbidden proof-bypass token: ' + module)
        for imported in inv['imports']:
            if imported in catalog:
                visit(imported)
            else:
                require(imported == 'Lean' or imported.startswith(('Mathlib.', 'Lean.', 'Std.', 'Init.')),
                        'Unrecognized external import: ' + imported)
        modules[module] = {**chosen, 'imports': inv['imports'], 'inventory': inv, 'candidates': candidates}
        order.append(module)
        active.remove(module)

    for endpoint in specification['endpoints']:
        visit(endpoint)
    new = {module: entry['sha256'] for module, entry in modules.items() if entry['group'] == 'new-envelope'}
    if 'required_new_source_hashes' in specification:
        require(new == specification['required_new_source_hashes'], 'Changed reviewed new-source closure')
    all_names = {declaration['name'] for entry in modules.values()
                 for declaration in entry['inventory']['named_declarations']}
    require(set(specification['endpoint_declarations']) <= all_names, 'Missing named endpoint declaration')
    external = sorted({name for entry in modules.values() for name in entry['imports'] if name not in modules})
    return {'status': 'INVENTORIED; NOT A REPLAY RESULT', 'source_count': len(order),
        'source_bytes': sum(Path(entry['path']).stat().st_size for entry in modules.values()),
        'selected_groups': dict(Counter(entry['group'] for entry in modules.values())),
        'source_tier_order': SOURCE_ORDER, 'endpoints': specification['endpoints'],
        'endpoint_declarations': specification['endpoint_declarations'],
        'modules_in_topological_order': order, 'modules': modules,
        'external_direct_imports': external, 'conflicting_source_variants': variants,
        'input_record_pins': records, 'required_new_source_hashes': new}


def prepare_harness(destination, reviewed_driver_pin):
    require(not destination.exists(), 'Bundle destination already exists')
    failed = CANDIDATE / 'full-envelope-replay'
    require(sha(failed / 'source-manifest.json') ==
            '26e04c96f13fe01ae260f4a3db96c9ad629d4cb4504211d205a918255efa2565',
            'Changed preserved first-attempt manifest')
    retained = json.loads((failed / 'source-manifest.json').read_text())
    for name in ['scripts/source_inventory.py', 'scripts/replay.py', 'scripts/setup.py',
                 'dependency-pins.json', 'lean-toolchain']:
        require(sha(failed / name) == retained['pinned_files'][name],
                'Changed first-attempt replay input: ' + name)
    candidate = HERE / 'replay_parallel_candidate.py'
    require(candidate.is_file() and not candidate.is_symlink(), 'Missing reviewed replay driver candidate')
    require(bool(re.fullmatch(r'[0-9a-f]{64}', reviewed_driver_pin or '')) and
            sha(candidate) == reviewed_driver_pin, 'Missing or changed independently reviewed driver pin')
    destination.mkdir(parents=True)
    for name in ['source_inventory.py', 'replay.py', 'setup.py']:
        original = failed / 'scripts' / name
        source = candidate if name == 'replay.py' else original
        target = destination / 'scripts' / name
        copy(source, target)
        diff = ''.join(difflib.unified_diff(original.read_text().splitlines(True),
            target.read_text().splitlines(True), fromfile='preserved-first-attempt/scripts/' + name,
            tofile='scripts/' + name))
        if diff:
            (destination / 'scripts' / (name + '.patch')).write_text(diff)
    for name in ['dependency-pins.json', 'lean-toolchain']:
        copy(failed / name, destination / name)
    write_json(destination / 'harness-provenance.json', {
        'status': 'PREPARED; NOT FROZEN OR REPLAYED',
        'base_source_manifest_sha256': sha(failed / 'source-manifest.json'),
        'independently_reviewed_driver_sha256': reviewed_driver_pin,
        'scripts': {name: {'original_sha256': sha(failed / 'scripts' / name),
                           'candidate_sha256': sha(destination / 'scripts' / name)}
                    for name in ['source_inventory.py', 'replay.py', 'setup.py']},
        'changes': ['Optional bounded dependency scheduler; a dependent waits for strict compilation and official kernel replay of every internal dependency.',
                    'Default sequential behavior and complete source, object, import, input and axiom verification are retained.'],
        'object_policy': 'No internal compiled objects are copied or reused.'})


def freeze(destination, inv, specification_path, patch_review_path, patch_review_pin):
    require(destination.is_dir() and not (destination / 'source-manifest.json').exists(),
            'Missing prepared harness or bundle already frozen')
    require(not (destination / 'source').exists() and not (destination / '.replay').exists(),
            'Fresh source-only destination required')
    diagnostic_path = CANDIDATE / 'diagnostic-full-closure/diagnostic-record.json'
    diagnostic = json.loads(diagnostic_path.read_text())
    require(diagnostic['status'] == 'COMPLETED_NONFINAL_DIAGNOSTIC' and not diagnostic['failures'],
            'Full warning diagnostic is not complete')
    expanded = json.loads((HERE / 'expanded-compatibility-overrides.json').read_text())
    require(set(diagnostic['warning_modules']) == set(expanded['patches']),
            'Expanded patches do not exactly cover diagnosed warning modules')
    require(patch_review_path is not None and patch_review_path.is_file() and
            not patch_review_path.is_symlink() and
            bool(re.fullmatch(r'[0-9a-f]{64}', patch_review_pin or '')) and
            sha(patch_review_path) == patch_review_pin, 'Missing or changed independent patch review')
    patch_review = json.loads(patch_review_path.read_text())
    require(str(patch_review.get('status', '')).startswith('PASS') and
            patch_review.get('expanded_compatibility_ledger_sha256') ==
            sha(HERE / 'expanded-compatibility-overrides.json'),
            'Patch review does not approve the exact final expanded ledger')
    specification = json.loads(specification_path.read_text())
    require('required_new_source_hashes' in specification, 'Final reviewed new-source pins are required')
    provenance = json.loads((destination / 'harness-provenance.json').read_text())
    require(provenance['independently_reviewed_driver_sha256'] == sha(destination / 'scripts/replay.py'),
            'Reviewed replay driver pin changed')
    for name, entry in provenance['scripts'].items():
        require(sha(destination / 'scripts' / name) == entry['candidate_sha256'],
                'Prepared harness changed before freezing: ' + name)
    # Recompute immediately before copying, then compare the complete selected-source inventory.
    require(inventory(specification) == inv, 'Source inputs changed during preparation')
    modules = {}
    for module in inv['modules_in_topological_order']:
        entry = inv['modules'][module]
        relative = 'source/' + Path(*module.split('.')).with_suffix('.lean').as_posix()
        copy(Path(entry['path']), destination / relative)
        modules[module] = {'source': relative, 'sha256': entry['sha256'],
            'imports': entry['imports'], 'inventory': entry['inventory'],
            'lean_options': {'warningAsError': True}}
    for tree in ['licenses', 'provenance']:
        for path in sorted((SHARP / tree).rglob('*')):
            if path.is_file():
                copy(path, destination / tree / path.relative_to(SHARP / tree))
    for name in ['LICENSE-MIT', 'LICENSE-UPSTREAM', 'NOTICE-UPSTREAM', 'SOURCE-LICENSES.md',
                 'source-origins.json', 'provenance-hashes.json']:
        copy(NATIVE / name, destination / 'provenance/retained-native' / name)
    for path in sorted((NATIVE / 'provenance').rglob('*')):
        if path.is_file():
            copy(path, destination / 'provenance/retained-native/provenance' / path.relative_to(NATIVE / 'provenance'))
    census_license = Path('/home/ubuntu/collatz-two-coordinate-obstruction/formal-periodic-census')
    for name in ['LICENSE-MIT', 'NOTICE', 'SOURCE-LICENSES.txt']:
        copy(census_license / name, destination / 'provenance/retained-periodic-census' / name)
    compatibility, _compatibility_pins = combined_compatibility()
    portable_patches = {}
    for module, entry in compatibility['patches'].items():
        if module not in modules:
            continue
        patch = 'provenance/envelope-linter-patches/' + module + '.patch'
        copy(Path(entry['patch']), destination / patch)
        portable_patches[module] = {key: entry[key] for key in
            ['original_sha256', 'candidate_sha256', 'patch_sha256', 'adaptation']}
        portable_patches[module].update(patch=patch, source=modules[module]['source'])
    write_json(destination / 'provenance/envelope-linter-patches.json', {'patches': portable_patches,
        'diagnostic_record_sha256': sha(diagnostic_path),
        'diagnostic_scope': 'Nonfinal warning collection only. No diagnostic object is accepted by the fresh replay.'})
    copy(HERE / 'first-full-replay-failure.json', destination / 'provenance/first-full-replay-failure.json')
    copy(patch_review_path, destination / 'provenance/envelope-expanded-compatibility-independent-review.json')
    copy(HERE / 'expanded-compatibility-overrides.json',
         destination / 'provenance/envelope-expanded-compatibility-development-record.json')
    write_json(destination / 'provenance/envelope-source-origins.json', {
        'scope': 'Authoritative combined selection ledger. Retained sharp/native/census ledgers apply only to their named source groups.',
        'source_tier_order': SOURCE_ORDER, 'modules': inv['modules'],
        'prior_source_record_pins': inv['input_record_pins'],
        'known_source_variants': inv['conflicting_source_variants'],
        'object_policy': 'Prior object paths are not proof inputs. Every internal module is rebuilt from this selected source closure.'})
    copy(specification_path, destination / 'provenance/endpoint-specification.json')
    copy(Path(__file__), destination / 'provenance/prepare_envelope_replay.py')
    (destination / 'README.md').write_text(
        '# Canonical integer-envelope source replay\n\n'
        'This private candidate contains the exact internal source closure of the endpoint modules '
        'listed in source-manifest.json. Its claims concern the canonical stationary measure, its '
        'lower semicontinuous envelope and positive integer trace, uniform cylinder lower bounds, '
        'and the explicitly named consequences. It makes no Collatz convergence claim.\n\n'
        'Run scripts/setup.py with --expected-manifest-sha256 and optionally --toolchain and --mathlib '
        'to prepare or verify the pinned external dependencies. Then run scripts/replay.py with those '
        'same three arguments and --run, optionally adding --jobs 4 for bounded dependency parallelism. '
        'The destination .replay must be fresh. Use --verify-only '
        'afterwards to check all recorded source/object/log/import hashes and the complete constant '
        'audit again. External Mathlib and toolchain objects are pinned and inventoried, not rebuilt.\n\n'
        'The replay accepts only fresh internal objects. Each source is compiled with -j1 and '
        '-DwarningAsError=true, then checked by the official leanchecker. The final audit covers every '
        'constant owned by every internal module, including private and compiler-generated constants, '
        'and permits only propext, Classical.choice, and Quot.sound.\n\n'
        'provenance/envelope-source-origins.json is the combined source selection ledger. Retained '
        'licenses and modification notices preserve their original scopes. The copied sharp source '
        'ledger does not describe the additional native and envelope modules.\n')
    (destination / '.gitignore').write_text('.replay/\n.external/\n__pycache__/\n*.pyc\npreflight-input-state.json\nsetup-result.json\n')
    pinned = {path.relative_to(destination).as_posix(): sha(path)
              for path in sorted(destination.rglob('*')) if path.is_file()
              and not path.is_relative_to(destination / 'source') and '__pycache__' not in path.parts}
    manifest = {'status': 'FROZEN', 'endpoints': inv['endpoints'],
        'endpoint_declarations': inv['endpoint_declarations'],
        'source_count': len(modules), 'source_counts': inv['selected_groups'],
        'modules_in_topological_order': inv['modules_in_topological_order'], 'modules': modules,
        'external_direct_imports': inv['external_direct_imports'],
        'planned_successful_commands': 2 * (len(modules) + 1),
        'source_declaration_counts': {
            'named': sum(len(entry['inventory']['named_declarations']) for entry in modules.values()),
            'private': sum(len(entry['inventory']['private_declarations']) for entry in modules.values()),
            'anonymous_instances': sum(len(entry['inventory']['anonymous_instance_lines']) for entry in modules.values())},
        'helper_sha256': sha(destination / 'scripts/source_inventory.py'), 'pinned_files': pinned,
        'input_scope': 'All selected source files and every pinned file are sealed proof-bundle inputs. No prior internal objects are accepted.',
        'scope': 'Fresh strict compilation and official kernel replay of the exact canonical integer-envelope endpoint source closure. External Mathlib/dependency/toolchain compiled libraries are separately pinned and inventoried before and after, not rebuilt. No Collatz convergence conclusion.'}
    write_json(destination / 'source-manifest.json', manifest)
    print(json.dumps({'status': 'FROZEN; REPLAY NOT STARTED', 'bundle': str(destination),
        'manifest_sha256': sha(destination / 'source-manifest.json'),
        'sources': len(modules), 'planned_commands': manifest['planned_successful_commands']}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', required=True, type=Path)
    parser.add_argument('--specification', type=Path)
    parser.add_argument('--inventory-output', type=Path)
    parser.add_argument('--expected-replay-driver-sha256')
    parser.add_argument('--patch-review', type=Path)
    parser.add_argument('--expected-patch-review-sha256')
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--prepare-harness', action='store_true')
    action.add_argument('--inventory', action='store_true')
    action.add_argument('--freeze', action='store_true')
    args = parser.parse_args()
    if args.prepare_harness:
        prepare_harness(args.destination, args.expected_replay_driver_sha256)
        return
    require(args.specification is not None, 'Endpoint specification required')
    inv = inventory(json.loads(args.specification.read_text()))
    if args.inventory_output:
        write_json(args.inventory_output, inv)
    if args.freeze:
        freeze(args.destination, inv, args.specification, args.patch_review,
               args.expected_patch_review_sha256)
    else:
        print(json.dumps({key: inv[key] for key in ['status', 'source_count', 'source_bytes', 'selected_groups', 'required_new_source_hashes']}))


if __name__ == '__main__':
    main()
