#!/usr/bin/env python3
"""Freshly rebuild and audit the complete two-coordinate obstruction closure."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from check_reversed_binary_power_closure import (
    MATHLIB_REVISION, STANDARD_AXIOMS, audited_revision, run,
)


TOP = "FullTwoCoordinate"
TOP_DECLARATIONS = {
    "CollatzResearch.FullTwo.forward_all_gaps_zero",
    "CollatzResearch.FullTwo.reversed_all_gaps_zero",
    "CollatzResearch.FullTwo.full_two_coordinate_obstruction",
}
PREVIOUS_REPORTS = {
    "collatz-reversed-real-middle-rank-lean-check.json":
        "971a65e64b3195806b72e1312c6f809d4edc6cd472c4f1e581e0021b81ddf74e",
    "collatz-reversed-real-normalization-lean-check.json":
        "f309af1bd5a854821367a8225e870df54a8320946ace4d0da289a4d0730d55ef",
    "reversed-swap-recurrence-lean-check.json":
        "0b5269001b7e1a7e4ba79cba0d2b8344a8673db82db08dcf2b71c5e93ae1670a",
}
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
    namespaces = list(re.finditer(r"^namespace (" + QUALIFIED + r")\s*$", code, re.M))
    ends = list(re.finditer(r"^end (" + QUALIFIED + r")\s*$", code, re.M))
    # This checker deliberately accepts the retained single-namespace source format only.
    if (len(namespaces) != 1 or len(ends) != 1
            or namespaces[0].group(1) != ends[0].group(1)
            or len(re.findall(r"\bnamespace\b", code)) != 1
            or len(re.findall(r"\bend\b", code)) != 1
            or re.search(r"\b(?:section|private|protected)\b", code)):
        raise ValueError("Unsupported declaration scope in " + name)
    start, end = namespaces[0], ends[0]
    namespace = start.group(1)
    declarations = list(re.finditer(
        r"^(?:theorem|lemma)\s+(" + IDENTIFIER + r")(?=\s|\{|\(|:)", code, re.M))
    if len(declarations) != len(re.findall(r"\b(?:theorem|lemma)\b", code)):
        raise ValueError("A theorem or lemma was not inventoried in " + name)
    if not declarations or any(not start.end() <= item.start() < end.start()
                               for item in declarations):
        raise ValueError("Missing or out-of-namespace declarations in " + name)
    public = [namespace + "." + item.group(1) for item in declarations]
    if len(public) != len(set(public)):
        raise ValueError("Duplicate public declaration in " + name)
    imports = re.findall(r"^import (" + QUALIFIED + r")\s*$", code, re.M)
    if len(imports) != len(re.findall(r"\bimport\b", code)) or len(imports) != len(set(imports)):
        raise ValueError("Unsupported or duplicate import in " + name)
    prints = list(re.finditer(r"^#print axioms (" + QUALIFIED + r")\s*$", code, re.M))
    if len(prints) != len(re.findall(r"#", code)):
        raise ValueError("Unsupported diagnostic command in " + name)
    expected_prints = []
    for item in prints:
        target = item.group(1)
        if "." not in target:
            if not start.end() <= item.start() < end.start():
                raise ValueError("Unqualified print outside namespace in " + name)
            target = namespace + "." + target
        if target not in public or target in expected_prints:
            raise ValueError("Unknown or duplicate existing axiom print in " + name)
        expected_prints.append(target)
    return {
        "source_sha256": digest(data), "namespace": namespace,
        "imports": imports, "public_declarations": public,
        "existing_axiom_prints": expected_prints,
        "local_dependencies": [item for item in imports if not item.startswith("Mathlib.")],
    }


def closure(directory):
    sources, inventory, active = {}, {}, set()

    def visit(name):
        if name in active:
            raise ValueError("Cyclic local imports: " + name)
        if name in inventory:
            return
        if not re.fullmatch(IDENTIFIER, name):
            raise ValueError("Unsupported local module name: " + name)
        active.add(name)
        sources[name] = (directory / (name + ".lean")).read_bytes()
        item = source_inventory(name, sources[name])
        for dependency in item["local_dependencies"]:
            visit(dependency)
        active.remove(name)
        inventory[name] = item

    visit(TOP)
    if inventory[TOP]["imports"] != ["FullTwoTriangular", "FullTwoMatrixReduction"]:
        raise ValueError("Unexpected top-level imports")
    if set(inventory[TOP]["public_declarations"]) != TOP_DECLARATIONS:
        raise ValueError("Unexpected top-level theorem inventory")
    names = [item for entry in inventory.values() for item in entry["public_declarations"]]
    if len(names) != len(set(names)):
        raise ValueError("Public declaration repeated across local modules")
    return sources, inventory


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


def frozen_inputs(directory, sources):
    guarded = {str(directory / Path(__file__).name): sha(Path(__file__))}
    reports, old_sources = {}, {}

    def pin(path, expected):
        actual = sha(path)
        if actual != expected or (str(path) in guarded and guarded[str(path)] != actual):
            raise ValueError("Retained evidence changed: " + str(path))
        guarded[str(path)] = actual

    for filename, expected in PREVIOUS_REPORTS.items():
        path = directory / filename
        pin(path, expected)
        previous = json.loads(path.read_text())
        if previous["status"] != "PASS" or previous["sat_solver_calls"] != 0:
            raise ValueError("Invalid retained dependency report: " + filename)
        reports[filename] = previous
        for module, entry in previous["builds"].items():
            pin(directory / (module + ".lean"), entry["source_sha256"])
            if module in old_sources and old_sources[module] != entry["source_sha256"]:
                raise ValueError("Conflicting retained source pins")
            old_sources[module] = entry["source_sha256"]
        for helper, expected_helper in previous["checker_sources_sha256"].items():
            pin(directory / helper, expected_helper)
    helper = directory / "check_reversed_binary_power_closure.py"
    if str(helper) not in guarded:
        raise ValueError("The revision-audit helper is not pinned by retained evidence")
    for module, data in sources.items():
        if not module.startswith("FullTwo") and old_sources.get(module) != digest(data):
            raise ValueError("Unpinned old local dependency: " + module)
        pin(directory / (module + ".lean"), digest(data))
    return reports, guarded


def revisions(mathlib, manifest):
    result = {"mathlib": audited_revision(mathlib, MATHLIB_REVISION)}
    for package in manifest["packages"]:
        if package["type"] != "git" or package["name"] in result:
            raise ValueError("Unpinned or duplicate mathlib dependency")
        result[package["name"]] = audited_revision(
            mathlib / ".lake" / "packages" / package["name"], package["rev"])
    return result


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path, default=Path("/dev/shm"))
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "full-two-coordinate-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    sources, inventory = closure(directory)
    previous, guarded = frozen_inputs(directory, sources)
    mathlib = args.mathlib_root.resolve()
    manifest_path = mathlib / "lake-manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    dependency_revisions = revisions(mathlib, manifest)
    version = run([args.lake, "env", "lean", "--version"], mathlib).strip()
    if (not version.startswith("Lean (version 4.27.0,")
            or any(version != item["lean_version"] for item in previous.values())
            or any(digest(manifest_bytes) != item["mathlib_manifest_sha256"]
                   for item in previous.values())
            or any(dependency_revisions != item["dependency_revisions"] for item in previous.values())):
        raise ValueError("Pinned Lean/mathlib environment differs from retained evidence")
    lean = run([args.lake, "env", "which", "lean"], mathlib).strip()
    reported_library_path = run([args.lake, "env", "printenv", "LEAN_PATH"], mathlib).strip()
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
    guarded[str(manifest_path)] = digest(manifest_bytes)
    guarded[lean] = sha(Path(lean))
    inventory_bytes = json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode()
    declarations = sorted(name for item in inventory.values() for name in item["public_declarations"])
    audit_source = ("import " + TOP + "\n\n" +
                    "".join("#print axioms " + name + "\n" for name in declarations))
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-full-two-", dir=args.build_root) as temporary:
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
                    raise ValueError("Local dependency DAG made no progress")
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    name = running.pop(future)
                    builds[name] = future.result()
                    print(json.dumps({"module": name, "status": "PASS",
                                      "completed": len(builds), "total": len(sources)}), flush=True)
        audit_path = source_dir / "FullTwoCoordinateAudit.lean"
        audit_path.write_text(audit_source)
        audit = compile_module("FullTwoCoordinateAudit", audit_path,
                               module_dir / "FullTwoCoordinateAudit.olean", lean,
                               environment, declarations)
        for name, data in sources.items():
            if (source_dir / (name + ".lean")).read_bytes() != data:
                raise ValueError("A snapshotted source changed during compilation: " + name)
        if audit_path.read_text() != audit_source:
            raise ValueError("Generated audit source changed during compilation")
    after = {path: sha(Path(path)) for path in guarded}
    if after != guarded:
        raise ValueError("A source, checker, report, compiler, or manifest changed during checking")
    if revisions(mathlib, manifest) != dependency_revisions:
        raise ValueError("Pinned dependency revisions changed during checking")
    if any(Path(entry).exists() for entry in absent_library_locations):
        raise ValueError("An excluded absent library directory appeared during checking")
    # Re-derive the closure, so changes to imports or the declaration inventory cannot be hidden.
    after_sources, after_inventory = closure(directory)
    if after_sources != sources or after_inventory != inventory:
        raise ValueError("The complete source/declaration closure changed during checking")
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "top_module": TOP, "top_declarations": sorted(TOP_DECLARATIONS),
        "module_count": len(sources), "public_declaration_count": len(declarations),
        "inventory": inventory, "inventory_sha256": digest(inventory_bytes),
        "builds": builds, "audit": audit, "generated_audit_source": audit_source,
        "all_public_theorems_and_lemmas_audited": True,
        "all_local_dependencies_built_in_fresh_directory": True,
        "all_source_snapshots_match_originals_before_and_after": True,
        "guarded_files_sha256_before": guarded, "guarded_files_sha256_after": after,
        "previous_reports_sha256": PREVIOUS_REPORTS,
        "checker_sources_sha256": {Path(path).name: value for path, value in guarded.items()
                                   if path.endswith(".py")},
        "lean_version": version, "lean_executable": lean,
        "lean_reported_library_path": reported_library_path,
        "excluded_absent_library_directories": absent_library_locations,
        "lean_library_path": library_path, "mathlib_manifest_sha256": digest(manifest_bytes),
        "dependency_revisions": dependency_revisions,
        "parallel_lean_workers": args.workers, "threads_per_lean_worker": 1,
        "sat_solver_calls": 0,
        "scope": (
            "For seven nonnegative real affine maps in two coordinates, each with first "
            "diagonal matrix entry at least one, all eleven ordinary weak rules in either "
            "orientation force all eleven first-coordinate affine offset gaps to be zero. "
            "No coefficient cap, integrality, triangularity, or invertibility is assumed "
            "in the three final theorems. This is an obstruction to these certificates, "
            "not a proof of the Collatz conjecture."
        ),
    }
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "modules": len(sources),
                      "public_declarations": len(declarations),
                      "report_sha256": sha(report), "sat_solver_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
