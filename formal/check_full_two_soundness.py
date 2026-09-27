#!/usr/bin/env python3
"""Freshly rebuild and audit the fixed-gap soundness lemmas for two coordinates."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import tempfile

from check_full_two_coordinate import (
    IDENTIFIER, compile_module, digest, revisions, sha, source_inventory,
)
from check_reversed_binary_power_closure import run


TOP = "FullTwoSoundness"
TOP_DECLARATIONS = {
    "CollatzResearch.FullTwoSoundness.admissible_preserves_gap",
    "CollatzResearch.FullTwoSoundness.weak_rule_gives_gap",
    "CollatzResearch.FullTwoSoundness.gap_wellFounded",
}
PREVIOUS_REPORT = "full-two-coordinate-lean-check.json"
PREVIOUS_SHA256 = "3e4c23a484105a3f2132e531c8647faf8497847f7724cf684befa75b307f2b55"


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
    if inventory[TOP]["imports"] != ["FullTwoBasic"]:
        raise ValueError("Unexpected top-level imports")
    if set(inventory[TOP]["public_declarations"]) != TOP_DECLARATIONS:
        raise ValueError("Unexpected top-level theorem inventory")
    names = [name for item in inventory.values() for name in item["public_declarations"]]
    if len(names) != len(set(names)):
        raise ValueError("Public declaration repeated across local modules")
    return sources, inventory


def frozen_inputs(directory, sources):
    guarded = {str(Path(__file__).resolve()): sha(Path(__file__))}

    def pin(path, expected):
        actual = sha(path)
        if actual != expected or (str(path) in guarded and guarded[str(path)] != actual):
            raise ValueError("Retained evidence changed: " + str(path))
        guarded[str(path)] = actual

    path = directory / PREVIOUS_REPORT
    pin(path, PREVIOUS_SHA256)
    previous = json.loads(path.read_text())
    if previous["status"] != "PASS" or previous["sat_solver_calls"] != 0:
        raise ValueError("Invalid retained dependency report")
    old_sources = {}
    for module, entry in previous["builds"].items():
        pin(directory / (module + ".lean"), entry["source_sha256"])
        old_sources[module] = entry["source_sha256"]
    for helper, expected in previous["checker_sources_sha256"].items():
        pin(directory / helper, expected)
    for helper in ("check_reversed_binary_power_closure.py", "check_full_two_coordinate.py"):
        if str(directory / helper) not in guarded:
            raise ValueError("An imported checking helper is not pinned: " + helper)
    if {name for name in sources if name not in old_sources} != {TOP}:
        raise ValueError("Only FullTwoSoundness may lack previous Lean evidence")
    for module, data in sources.items():
        if module != TOP and old_sources.get(module) != digest(data):
            raise ValueError("Unpinned or changed old local dependency: " + module)
        pin(directory / (module + ".lean"), digest(data))
    return previous, guarded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path, default=Path("/dev/shm"))
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "full-two-soundness-lean-check.json").resolve()
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
            or version != previous["lean_version"]
            or digest(manifest_bytes) != previous["mathlib_manifest_sha256"]
            or dependency_revisions != previous["dependency_revisions"]):
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
    audit_name = "FullTwoSoundnessAudit"
    audit_source = ("import " + TOP + "\n\n" +
                    "".join("#print axioms " + name + "\n" for name in declarations))
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-full-two-soundness-", dir=args.build_root) as temporary:
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
        audit_path = source_dir / (audit_name + ".lean")
        audit_path.write_text(audit_source)
        audit = compile_module(audit_name, audit_path, module_dir / (audit_name + ".olean"),
                               lean, environment, declarations)
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
    after_sources, after_inventory = closure(directory)
    if after_sources != sources or after_inventory != inventory:
        raise ValueError("The complete source/declaration closure changed during checking")
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "top_module": TOP, "top_declarations": sorted(TOP_DECLARATIONS),
        "new_modules": [TOP], "module_count": len(sources),
        "public_declaration_count": len(declarations),
        "inventory": inventory, "inventory_sha256": digest(inventory_bytes),
        "builds": builds, "audit": audit, "generated_audit_source": audit_source,
        "all_public_theorems_and_lemmas_audited": True,
        "all_old_local_dependencies_pinned_to_retained_evidence": True,
        "all_local_dependencies_built_in_fresh_directory": True,
        "all_source_snapshots_match_originals_before_and_after": True,
        "guarded_files_sha256_before": guarded, "guarded_files_sha256_after": after,
        "previous_reports_sha256": {PREVIOUS_REPORT: PREVIOUS_SHA256},
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
            "Gap(delta,x,y) means y[0]+delta <= x[0] and y[1] <= x[1]. For delta >= 0, "
            "a nonnegative real affine map with first diagonal entry at least one "
            "preserves this relation. A coefficientwise weak affine comparison whose "
            "first offset difference is at least delta gives this gap after evaluation "
            "at any nonnegative vector. For delta > 0, the relation with the smaller "
            "vector first is well-founded on nonnegative vectors, via Nat.floor(x[0]/delta). "
            "These are fixed-gap interpretation soundness lemmas, not a proof of Collatz."
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
