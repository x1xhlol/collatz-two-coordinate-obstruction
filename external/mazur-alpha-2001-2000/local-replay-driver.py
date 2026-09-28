"""Replay the alpha=2001/2000 Prop111 root with a dependency-aware reuse ledger."""
import concurrent.futures
from functools import lru_cache
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

WORK = Path('/home/ubuntu/collatz-global-descent-20260927/mazur-alpha-2001-2000')
SOURCE, MODULES, LOG = (WORK / x for x in ['source', 'modules', 'build-logs'])
BASE = Path('/tmp/collatz-literature/section10-requested-comparison/mazur-natural-ca3dd0d63920')
BASE_WORK = Path('/dev/shm/collatz-mazur-rebuild')
BASE_RECORD = Path('/home/ubuntu/collatz-global-descent-20260927/mazur-natural-local-rebuild.json')
MATHLIB = BASE_WORK / 'mathlib4'
LEAN = BASE_WORK / 'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'
LAKE = LEAN.with_name('lake')
RECORD = WORK / 'rebuild-record.json'
TOP = 'Erdos1135.Tao.Section3.Prop111RealRate'
ROOT = 'Erdos1135.Tao.taoProp111RealFirstPassageStabilizationRate_checked'

spec = importlib.util.spec_from_file_location('audit_helpers', '/home/ubuntu/collatz-two-coordinate-obstruction/verify.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
digest = lambda data: hashlib.sha256(data).hexdigest()

def read_record(path):
    for attempt in range(20):
        try:
            return json.loads(path.read_text())
        except json.JSONDecodeError:
            time.sleep(.05)
    raise ValueError('Concurrent record writer did not yield valid JSON: ' + str(path))

sources, dependencies = {}, {}
def visit(name):
    if name in sources:
        return
    data = (SOURCE / (name.replace('.', '/') + '.lean')).read_bytes()
    code = helpers.lean_code(data.decode())
    if re.search(r'\b(?:sorry|admit)\b|^\s*axiom\s', code, re.M) and name != 'FormalConjectures.Wikipedia.CollatzConjecture':
        raise ValueError('Unfinished or axiomatic source: ' + name)
    sources[name] = data
    imports = re.findall(r'^import ([A-Za-z0-9_.]+)\s*$', code, re.M)
    if len(imports) != len(re.findall(r'\bimport\b', code)):
        raise ValueError('Unparsed import in ' + name)
    dependencies[name] = [n for n in imports if (SOURCE / (n.replace('.', '/') + '.lean')).exists()]
    for dep in dependencies[name]:
        visit(dep)
visit(TOP)

@lru_cache(None)
def key(name):
    return digest(json.dumps([name, digest(sources[name]), [(d, key(d)) for d in dependencies[name]]],
                             separators=(',', ':')).encode())

@lru_cache(None)
def unchanged_tree(name):
    original = BASE / (name.replace('.', '/') + '.lean')
    return original.is_file() and original.read_bytes() == sources[name] and all(
        unchanged_tree(dep) for dep in dependencies[name])

for directory in [MODULES, LOG]:
    directory.mkdir(exist_ok=True)
previous = read_record(RECORD) if RECORD.exists() else {}
env = os.environ.copy()
env['ELAN_HOME'] = str(BASE_WORK / 'elan')
library = subprocess.check_output([str(LAKE), 'env', 'printenv', 'LEAN_PATH'], cwd=MATHLIB, env=env, text=True).strip()
env['LEAN_PATH'] = str(MODULES) + os.pathsep + library
version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
mathlib_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip()
record = {'status': 'RUNNING', 'alpha': '2001/2000', 'source_package': 'ca3dd0d63920411213403092aecc6946619eb082',
          'top_module': TOP, 'declaration': ROOT, 'module_count': len(sources),
          'source_hashes': {n: digest(d) for n, d in sources.items()},
          'dependency_fingerprints': {n: key(n) for n in sources},
          'mathlib_revision': mathlib_revision, 'lean_version': version,
          'baseline_record': str(BASE_RECORD),
          'reuse_rule': 'Only exact source-matching modules whose entire first-party dependency closure is unchanged may be copied from the baseline; artifact and source hashes are checked. Modified closure objects are recompiled or reused only by complete recursive dependency fingerprint from an earlier isolated attempt.',
          'registry_boundary': 'The companion includes the unused open-problem registry theorem with sorry. The selected root must audit without sorryAx.',
          'builds': {}}

def save():
    temporary = RECORD.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2))
    temporary.replace(RECORD)

def try_reuse(name):
    target = MODULES / (name.replace('.', '/') + '.olean')
    old = previous.get('builds', {}).get(name)
    if old and old.get('dependency_fingerprint') == key(name) and target.is_file() and \
            digest(target.read_bytes()) == old.get('olean_sha256') and \
            previous.get('mathlib_revision') == mathlib_revision and previous.get('lean_version') == version:
        return dict(old, reused_from_previous_isolated_attempt=True)
    if not unchanged_tree(name):
        return None
    baseline = read_record(BASE_RECORD)
    item = baseline.get('builds', {}).get(name)
    if not item or item.get('exit_code') != 0:
        return None
    if baseline.get('mathlib_revision') != mathlib_revision or baseline.get('lean_version') != version:
        raise ValueError('Baseline toolchain or mathlib mismatch')
    if baseline['source_hashes'].get(name) != digest(sources[name]):
        raise ValueError('Baseline source hash mismatch: ' + name)
    baseline_source = BASE_WORK / 'source' / (name.replace('.', '/') + '.lean')
    if baseline_source.read_bytes() != sources[name]:
        raise ValueError('Baseline snapshot source mismatch: ' + name)
    origin = BASE_WORK / 'modules' / (name.replace('.', '/') + '.olean')
    if digest(origin.read_bytes()) != item['olean_sha256']:
        raise ValueError('Baseline object hash mismatch: ' + name)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(origin, target)
    if digest(target.read_bytes()) != item['olean_sha256']:
        raise ValueError('Copied object hash mismatch: ' + name)
    return {'exit_code': 0, 'mode': 'baseline_exact_unchanged_dependency_closure',
            'baseline_object': str(origin), 'olean_sha256': item['olean_sha256'],
            'source_sha256': digest(sources[name]), 'dependency_fingerprint': key(name)}

def compile_one(name):
    path = SOURCE / (name.replace('.', '/') + '.lean')
    before = path.read_bytes()
    target = MODULES / (name.replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    command = [str(LEAN), '-j1', '--root=' + str(SOURCE), '-o', str(target), str(path)]
    began = time.monotonic()
    result = subprocess.run(command, cwd=SOURCE, env=env, text=True, capture_output=True, timeout=1800)
    log = LOG / (name + '.log')
    log.write_text(result.stdout + result.stderr)
    item = {'exit_code': result.returncode, 'mode': 'compiled_isolated',
            'elapsed_seconds': time.monotonic() - began, 'command': command,
            'log_path': str(log), 'log_sha256': digest(log.read_bytes()),
            'source_sha256': digest(before)}
    if path.read_bytes() != before:
        raise RuntimeError('Source mutated during compilation: ' + name)
    if result.returncode:
        raise RuntimeError(json.dumps(item) + '\n' + log.read_text())
    item['olean_sha256'] = digest(target.read_bytes())
    if name in sources:
        item['dependency_fingerprint'] = key(name)
    return item

print(json.dumps({'closure': len(sources), 'unchanged_dependency_closures': sum(map(unchanged_tree, sources)),
                  'modified_dependency_closures': sum(not unchanged_tree(n) for n in sources)}), flush=True)
save()
try:
    pending, running = set(sources), {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        while pending or running:
            ready = sorted(n for n in pending if set(dependencies[n]) <= record['builds'].keys())
            for name in ready:
                reused = try_reuse(name)
                if reused:
                    pending.remove(name)
                    record['builds'][name] = reused
                elif len(running) < 2:
                    pending.remove(name)
                    running[pool.submit(compile_one, name)] = name
            save()
            if not running:
                if pending and not ready:
                    raise RuntimeError('Dependency cycle or missing source')
                continue
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                record['builds'][name] = future.result()
                print(json.dumps({'module': name, 'completed': len(record['builds']), 'total': len(sources)}), flush=True)
                save()
    audit = ('import ' + TOP + '\n' +
             'example : Erdos1135.Tao.taoAlpha = (2001 : ℝ) / 2000 := by\n' +
             '  norm_num [Erdos1135.Tao.taoAlpha]\n' + '#print axioms ' + ROOT + '\n')
    (SOURCE / 'RootAudit.lean').write_text(audit)
    record['audit'] = compile_one('RootAudit')
    record['axioms'] = helpers.audit_output((LOG / 'RootAudit.log').read_text(), [ROOT])
    if any((SOURCE / (n.replace('.', '/') + '.lean')).read_bytes() != d for n, d in sources.items()):
        raise RuntimeError('Source changed during replay')
    record['status'] = 'PASS'
except Exception as error:
    record['status'] = 'FAILED'
    record['error'] = str(error)
    raise
finally:
    save()
