#!/usr/bin/env python3
"""Freshly rebuild and audit the paper's Lean proofs with pinned dependencies.

Requires Python 3.10+, Git, and Lean 4.27.0 with the pinned mathlib checkout.
Only Python's standard library is used. No historical verification reports are read.
"""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


LEAN_VERSION = "4.27.0"
LEAN_COMMIT = "db93fe1608548721853390a10cd40580fe7d22ae"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_MANIFEST_SHA256 = "6c24676b690a32627317b1d6dd58cf9318d689c5481e1edc53d07c93c892632f"
DEPENDENCY_REVISIONS = {
    "Cli": "55c37290ff6186e2e965d68cf853a57c0702db82",
    "LeanSearchClient": "5ce7f0a355f522a952a3d678d696bd563bb4fd28",
    "Qq": "bd58c9efe2086d56ca361807014141a860ddbf8c",
    "aesop": "cb837cc26236ada03c81837bebe0acd9c70ced7d",
    "batteries": "b25b36a7caf8e237e7d1e6121543078a06777c8a",
    "importGraph": "8f497d55985a189cea8020d9dc51260af1e41ad2",
    "mathlib": "a3a10db0e9d66acbebf76c5e6a135066525ac900",
    "plausible": "009dc1e6f2feb2c96c081537d80a0905b2c6498f",
    "proofwidgets": "c04225ee7c0585effbd933662b3151f01b600e40"
}
SOURCE_SHA256 = {'AffineDifferenceMeasure': 'd7f207b01e2557c3c19758b49921d876df60dc7e25d37841812dcad6d9b3d79a',
 'AffineFamilySynchronization': '9e001bc3b246dde4effe37753b5bb004c846a66e13e7add74c2e472346c37eb6',
 'CollatzAffineProgressions': '5e28d1b0cae1f601d06983fd37b588498ad5d0f691c7c2ed1064db18ec6d4cf1',
 'FinitePatternCoalescence': '86208b374e1df4c1ecbefcd33270853b3b0a3349fdeb0aad854ae22939729087',
 'FinitePatternConvergence': '74ccd96f004198fbd04c6a5283022cb78414fd0351f49bc4c0ad61fc1c30ffb5',
 'OddAffineParameter': '6ca72b4eaa71f9f0f7c061d8d6e6f88e86fff4dd66a0c42ae3ec5d9767b4d209',
 'PositiveProgressionCoalescence': '9f503a2ea7ca75c8dcdfe8b7de95618eb526b5ee5bea8c5bf69bb8c35396d58f',
 'PowerTwoModuloThree': '5be46eeab995b54ccdeea3b662944dec43cdedc05e58e61b537b6a66cfcc5e30',
 'ProgressionConvergenceSpecialization': 'd2082e3c7d94e2fb2b762e80e02b327657b16ba73f2782e3c7aaf9fbc84acd50'}
TOPS = {'FinitePatternConvergence': {'declarations': {'CollatzPositiveProgression.arbitrarily_long_consecutive_equal_first_hitting_times',
                                               'CollatzPositiveProgression.every_finite_pattern_has_equal_first_hitting_times'},
                              'imports': ['FinitePatternCoalescence',
                                          'ProgressionConvergenceSpecialization']}}
EXPECTED_PUBLIC_DECLARATION_COUNT = 66
EXPECTED_AUDITED_DECLARATION_COUNT = 74
IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_]*"
QUALIFIED = IDENTIFIER + r"(?:\." + IDENTIFIER + r")*"
AXIOM_OUTPUT = re.compile(
    r"'(" + QUALIFIED + r")' "
    r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))"
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def lean_code(source):
    """Erase strings and nested comments, preserving line numbers and token boundaries."""
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\":
                if i + 1 >= len(source):
                    raise ValueError("Unterminated Lean string escape")
                result.extend("\n" if c == "\n" else " " for c in source[i:i + 2])
                i += 2
            else:
                quoted = char != '"'
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.extend(" " * (end - i))
            i = end
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif char == '"':
            quoted = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(result)


def source_inventory(name, data):
    code = lean_code(data.decode("utf-8"))
    if re.search(r"\b(?:sorry|admit|native_decide|axiom|opaque|unsafe)\b", code):
        raise ValueError("Forbidden proof placeholder or declaration in " + name)
    if re.search(r"\b(?:section|private|protected|mutual)\b", code):
        raise ValueError("Unsupported declaration scope in " + name)
    imports = re.findall(r"^import (" + QUALIFIED + r")\s*$", code, re.M)
    if len(imports) != len(re.findall(r"\bimport\b", code)) or len(imports) != len(set(imports)):
        raise ValueError("Unsupported or duplicate import in " + name)
    namespaces, public, definitions, raw_prints = [], [], [], []
    counts = {"namespace": 0, "end": 0, "theorem": 0, "lemma": 0, "def": 0, "print": 0}
    for line in code.splitlines():
        match = re.fullmatch(r"(namespace|end) (" + QUALIFIED + r")\s*", line)
        if match:
            kind, target = match.groups()
            counts[kind] += 1
            if kind == "namespace":
                namespaces.append(target)
            elif not namespaces or namespaces.pop() != target:
                raise ValueError("Unmatched namespace end in " + name)
            continue
        match = re.match(r"(theorem|lemma)\s+(" + QUALIFIED + r")(?=\s|\{|\(|:|$)", line)
        if match:
            kind, target = match.groups()
            if not namespaces:
                raise ValueError("Declaration outside namespace in " + name)
            counts[kind] += 1
            public.append(".".join([*namespaces, target]))
            continue
        match = re.match(r"(?:noncomputable )?def (" + QUALIFIED + r")(?=\s|\{|\(|:|$)", line)
        if match:
            if not namespaces:
                raise ValueError("Definition outside namespace in " + name)
            counts["def"] += 1
            definitions.append(".".join([*namespaces, match.group(1)]))
            continue
        match = re.fullmatch(r"#print axioms (" + QUALIFIED + r")\s*", line)
        if match:
            counts["print"] += 1
            raw_prints.append((".".join(namespaces), match.group(1)))
    if namespaces:
        raise ValueError("Unclosed namespace in " + name)
    for kind in ("namespace", "end", "theorem", "lemma", "def"):
        if counts[kind] != len(re.findall(r"\b" + kind + r"\b", code)):
            raise ValueError("An unsupported " + kind + " command was not inventoried in " + name)
    if counts["print"] != len(re.findall(r"#", code)) or not public:
        raise ValueError("Unsupported diagnostic command or empty declaration inventory in " + name)
    defined = public + definitions
    if len(defined) != len(set(defined)):
        raise ValueError("Duplicate declaration or definition in " + name)
    prints = []
    for namespace, target in raw_prints:
        components = namespace.split(".") if namespace else []
        candidates = [".".join([*components[:size], target])
                      for size in range(len(components), -1, -1)]
        found = next((candidate for candidate in candidates if candidate in defined), None)
        if found is None or found in prints:
            raise ValueError("Unknown or duplicate existing axiom print in " + name + ": " + target)
        prints.append(found)
    return {
        "source_sha256": digest(data), "imports": imports,
        "public_declarations": public, "definitions": definitions,
        "existing_axiom_prints": prints,
        "local_dependencies": [item for item in imports if not item.startswith("Mathlib.")],
    }


def audit_output(output, expected):
    axioms = {}
    for name, entries, no_axioms in AXIOM_OUTPUT.findall(output):
        if name in axioms:
            raise ValueError("Duplicate axiom report: " + name)
        declared = set() if no_axioms else {item.strip() for item in entries.split(",") if item.strip()}
        if not declared <= STANDARD_AXIOMS:
            raise ValueError("Nonstandard axioms: " + name + " " + repr(declared))
        axioms[name] = sorted(declared)
    if set(axioms) != set(expected) or AXIOM_OUTPUT.sub("", output).strip():
        raise ValueError("Wrong axiom coverage or unexpected compiler output:\n" + output)
    return axioms


def compile_module(name, source, output, lean, environment, expected):
    command = [lean, "-j1", "-Dlinter.unusedVariables=false",
               "-Dlinter.unusedSimpArgs=false", "-Dlinter.unnecessarySimpa=false",
               "--root=" + str(source.parent), "-o", str(output), str(source)]
    began = time.monotonic()
    compiled = subprocess.run(command, cwd=source.parent, env=environment, text=True,
                              capture_output=True, timeout=900, check=False)
    record = {
        "command": command, "working_directory": str(source.parent),
        "compiler_exit_code": compiled.returncode, "compiler_stdout": compiled.stdout,
        "compiler_stderr": compiled.stderr, "elapsed_seconds": time.monotonic() - began,
        "source_sha256": sha(source),
    }
    if compiled.returncode or compiled.stderr:
        raise RuntimeError("Lean failed: " + name + "\n" + json.dumps(record, indent=2))
    record["existing_print_declaration_axioms"] = audit_output(compiled.stdout, expected)
    if not output.is_file():
        raise ValueError("Lean did not write a compiled module: " + name)
    record["compiled_module_sha256"] = sha(output)
    return record


def run(arguments, directory):
    result = subprocess.run(arguments, cwd=directory, text=True, capture_output=True,
                            timeout=600, check=False)
    if result.returncode or result.stderr:
        raise RuntimeError(f"Command failed: {arguments!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def audited_revision(directory, expected):
    actual = run(["git", "rev-parse", "HEAD"], directory).strip()
    if actual != expected:
        raise ValueError(f"Unexpected dependency revision in {directory}: {actual}")
    run(["git", "diff", "--exit-code", "HEAD", "--"], directory)
    return actual


def revisions(mathlib, manifest):
    expected = {"mathlib": DEPENDENCY_REVISIONS["mathlib"]}
    for package in manifest["packages"]:
        name = package["name"]
        if (package["type"] != "git" or not re.fullmatch(IDENTIFIER, name)
                or name in expected):
            raise ValueError("Unpinned or duplicate mathlib dependency")
        expected[name] = package["rev"]
    if expected != DEPENDENCY_REVISIONS:
        raise ValueError("The mathlib dependency revisions differ from the embedded pins")
    return {
        name: audited_revision(mathlib if name == "mathlib" else
                               mathlib / ".lake" / "packages" / name, revision)
        for name, revision in expected.items()
    }


def closure(directory):
    sources, inventory, active = {}, {}, set()

    def visit(name):
        if name in active:
            raise ValueError("Cyclic local imports: " + name)
        if name in inventory:
            return
        if name not in SOURCE_SHA256:
            raise ValueError("Unpinned local module: " + name)
        active.add(name)
        data = (directory / (name + ".lean")).read_bytes()
        if digest(data) != SOURCE_SHA256[name]:
            raise ValueError("The published proof source changed: " + name)
        sources[name] = data
        item = source_inventory(name, data)
        for dependency in item["local_dependencies"]:
            visit(dependency)
        active.remove(name)
        inventory[name] = item

    for name, expected in TOPS.items():
        visit(name)
        if (inventory[name]["imports"] != expected["imports"]
                or set(inventory[name]["public_declarations"]) != expected["declarations"]):
            raise ValueError("Unexpected top-level imports or theorems: " + name)
    if sources.keys() != SOURCE_SHA256.keys():
        raise ValueError("The proof closure differs from the embedded source inventory")
    names = [name for item in inventory.values() for name in item["public_declarations"]]
    if len(names) != len(set(names)):
        raise ValueError("A public declaration is repeated across local modules")
    if len(names) != EXPECTED_PUBLIC_DECLARATION_COUNT:
        raise ValueError("The reviewed public declaration count changed")
    defined = names + [name for item in inventory.values() for name in item["definitions"]]
    if len(defined) != len(set(defined)):
        raise ValueError("A declaration or definition repeats across local modules")
    if len(defined) != EXPECTED_AUDITED_DECLARATION_COUNT:
        raise ValueError("The reviewed complete declaration count changed")
    return sources, inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True,
                        help="mathlib checkout at the embedded revision, with dependencies built")
    parser.add_argument("--lake", default="lake", help="Lake executable (default: lake on PATH)")
    parser.add_argument("--build-root", type=Path,
                        help="parent of the temporary build (default: system temporary directory)")
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--report", type=Path,
                        help="new report path (default: verification/rebuild.json)")
    args = parser.parse_args()
    checker = Path(__file__).resolve()
    root = checker.parent
    directory = root / "formal"
    report = (args.report or root / "verification" / "rebuild.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite a report; choose a new path with --report")
    sources, inventory = closure(directory)
    guarded = {"verify.py": (checker, sha(checker))}
    for name, data in sources.items():
        guarded["formal/" + name + ".lean"] = (directory / (name + ".lean"), digest(data))

    mathlib = args.mathlib_root.resolve()
    manifest_path = mathlib / "lake-manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    if digest(manifest_bytes) != MATHLIB_MANIFEST_SHA256:
        raise ValueError("The mathlib manifest differs from the embedded pin")
    manifest = json.loads(manifest_bytes)
    dependency_revisions = revisions(mathlib, manifest)
    lake = shutil.which(args.lake)
    if lake is None:
        raise ValueError("Lake executable not found: " + args.lake)
    lake = str(Path(lake).absolute())
    guarded["toolchain/lake_launcher"] = (Path(lake), sha(Path(lake)))
    lean = run([lake, "env", "which", "lean"], mathlib).strip()
    if not Path(lean).is_absolute() or not Path(lean).is_file():
        raise ValueError("Lake did not identify an absolute Lean executable")
    guarded["toolchain/lean"] = (Path(lean), sha(Path(lean)))
    version = run([lean, "--version"], mathlib).strip()
    if not re.fullmatch(r"Lean \(version " + re.escape(LEAN_VERSION) +
                        r", [^,]+, commit " + LEAN_COMMIT + r", Release\)", version):
        raise ValueError("Unexpected Lean version: " + version)
    reported_library_path = run([lake, "env", "printenv", "LEAN_PATH"], mathlib).strip()
    library_locations, absent_library_locations = [], []
    for entry in reported_library_path.split(os.pathsep):
        location = Path(entry)
        if not entry or not location.is_absolute():
            raise ValueError("Unexpected Lean library path: " + entry)
        if not location.exists():
            absent_library_locations.append(entry)
            continue
        if not location.is_dir():
            raise ValueError("Lean library path is not a directory: " + entry)
        if any((location / (name + ".olean")).exists() for name in sources):
            raise ValueError("A cached local module could shadow the fresh closure: " + entry)
        library_locations.append(entry)
    library_path = os.pathsep.join(library_locations)
    guarded["mathlib/lake-manifest.json"] = (manifest_path, digest(manifest_bytes))
    before = {label: expected for label, (_, expected) in guarded.items()}
    inventory_bytes = json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode()
    public = sorted(name for item in inventory.values() for name in item["public_declarations"])
    declarations = sorted(set(public) | {name for item in inventory.values()
                                         for name in item["definitions"]} |
                          {name for item in inventory.values()
                           for name in item["existing_axiom_prints"]})
    if len(declarations) != EXPECTED_AUDITED_DECLARATION_COUNT:
        raise ValueError("The generated axiom audit differs from the reviewed inventory")
    audit_name = "PublicationAudit"
    audit_source = ("".join("import " + name + "\n" for name in TOPS) + "\n" +
                    "".join("#print axioms " + name + "\n" for name in declarations))
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-proof-", dir=args.build_root) as temporary:
        build = Path(temporary)
        source_dir, module_dir = build / "sources", build / "modules"
        source_dir.mkdir()
        module_dir.mkdir()
        for name, data in sources.items():
            (source_dir / (name + ".lean")).write_bytes(data)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(module_dir) + os.pathsep + library_path
        pending, running = set(sources), {}
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            while pending or running:
                ready = sorted(name for name in pending
                               if set(inventory[name]["local_dependencies"]) <= builds.keys())
                for name in ready[:args.workers - len(running)]:
                    pending.remove(name)
                    future = pool.submit(
                        compile_module, name, source_dir / (name + ".lean"),
                        module_dir / (name + ".olean"), lean, environment,
                        inventory[name]["existing_axiom_prints"])
                    running[future] = name
                if not running:
                    raise ValueError("The local dependency DAG made no progress")
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    name = running.pop(future)
                    builds[name] = future.result()
                    print(json.dumps({"module": name, "status": "PASS",
                                      "completed": len(builds), "total": len(sources)}), flush=True)
        compiled_before = {name: sha(module_dir / (name + ".olean")) for name in sources}
        if any(compiled_before[name] != builds[name]["compiled_module_sha256"]
               for name in sources):
            raise ValueError("A compiled local module changed before the axiom audit")
        audit_path = source_dir / (audit_name + ".lean")
        audit_path.write_text(audit_source)
        audit = compile_module(audit_name, audit_path, module_dir / (audit_name + ".olean"),
                               lean, environment, declarations)
        for name, data in sources.items():
            if (source_dir / (name + ".lean")).read_bytes() != data:
                raise ValueError("A snapshotted source changed during compilation: " + name)
        if audit_path.read_text() != audit_source:
            raise ValueError("The generated audit source changed during compilation")
        compiled_after = {name: sha(module_dir / (name + ".olean")) for name in sources}
        if compiled_after != compiled_before:
            raise ValueError("A compiled local module changed during the axiom audit")
        audit_compiled_after = sha(module_dir / (audit_name + ".olean"))
        if audit_compiled_after != audit["compiled_module_sha256"]:
            raise ValueError("The compiled axiom audit changed")
    after = {label: sha(path) for label, (path, _) in guarded.items()}
    if after != before:
        raise ValueError("A proof source, verifier, compiler, or manifest changed during checking")
    if revisions(mathlib, manifest) != dependency_revisions:
        raise ValueError("A pinned dependency revision changed during checking")
    if any(Path(entry).exists() for entry in absent_library_locations):
        raise ValueError("An excluded absent library directory appeared during checking")
    if any((Path(entry) / (name + ".olean")).exists()
           for entry in library_locations for name in sources):
        raise ValueError("A cached local module appeared in a dependency library")
    after_sources, after_inventory = closure(directory)
    if after_sources != sources or after_inventory != inventory:
        raise ValueError("The complete source/declaration closure changed during checking")
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "top_modules": list(TOPS),
        "top_declarations": sorted(name for item in TOPS.values() for name in item["declarations"]),
        "module_count": len(sources), "public_declaration_count": len(public),
        "audited_declaration_count": len(declarations),
        "additional_audited_definitions": sorted(set(declarations) - set(public)),
        "inventory": inventory, "inventory_sha256": digest(inventory_bytes),
        "builds": builds, "audit": audit, "generated_audit_source": audit_source,
        "all_public_theorems_and_lemmas_audited": True,
        "all_inventoried_definitions_audited": True,
        "compiled_modules_sha256_before_audit": compiled_before,
        "compiled_modules_sha256_after_audit": compiled_after,
        "compiled_audit_sha256_after": audit_compiled_after,
        "all_compiled_modules_match_before_and_after_audit": True,
        "all_local_dependencies_built_in_fresh_directory": True,
        "all_source_snapshots_match_originals_before_and_after": True,
        "guarded_files_sha256_before": before, "guarded_files_sha256_after": after,
        "verifier_sha256": before["verify.py"],
        "lean_version": version, "lean_executable": lean, "lake_executable": lake,
        "lean_reported_library_path": reported_library_path,
        "excluded_absent_library_directories": absent_library_locations,
        "lean_library_path": library_path, "mathlib_manifest_sha256": digest(manifest_bytes),
        "dependency_revisions": dependency_revisions,
        "parallel_lean_workers": args.workers, "threads_per_lean_worker": 1,
        "sat_solver_calls": 0,
        "scope": (
            "For the shortcut Collatz map, every finite set of natural offsets "
            "has a dyadic progression of positive translating integers on which "
            "all trajectories coalesce at a common finite time with equal odd "
            "counts. Power-of-two endpoint specialization gives arbitrarily "
            "large translates that first reach one at a common finite time, "
            "with every earlier iterate greater than one. This includes "
            "consecutive runs of every prescribed length. The result does not "
            "prove convergence from arbitrary prescribed starting values."
        ),
    }
    report.parent.mkdir(parents=True, exist_ok=True)
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "modules": len(sources),
                      "public_declarations": len(public), "audited_declarations": len(declarations),
                      "report_sha256": sha(report), "sat_solver_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
