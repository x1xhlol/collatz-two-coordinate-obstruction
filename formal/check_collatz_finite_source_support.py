#!/usr/bin/env python3
"""Rebuild the finite source-support consequence for every reversed binary prefix."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_collatz_rank_growth import MODULES as PREVIOUS_MODULES, audit_output, names, sha
from check_reversed_binary_power_closure import MATHLIB_REVISION, audited_revision, run


MODULES = dict(PREVIOUS_MODULES)
MODULES["CollatzFiniteSourceSupport"] = names("FiniteSourceSupport.", """
    integer_powers_zero_of_first natural_powers_zero_of_first natural_powers_zero_of_window
    affine_iterate_sum observed_affine_iterate_sum observed_iterates_constant_of_zero_tail
    unbounded_iterates_have_finite_source_support reversed_all_prefix_source_support
""")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "collatz-finite-source-support-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    sources = {name: (directory / (name + ".lean")).read_bytes() for name in MODULES}
    for name, data in sources.items():
        source = data.decode()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                     source, flags=re.MULTILINE):
            raise ValueError("Forbidden proof placeholder or declaration in " + name)
        declared = set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE))
        if name == "CollatzReversedNecessaryConditions":
            if not re.search(r"^def ofModel\b", source, re.MULTILINE):
                raise ValueError("Missing audited certificate definition")
            declared.add("ofModel")
        if declared != {entry.split(".")[-1] for entry in MODULES[name]}:
            raise ValueError("Wrong theorem coverage in " + name)
        for imported in re.findall(r"^import\s+(\S+)", source, re.MULTILINE):
            if imported.startswith("Collatz") and imported not in list(MODULES)[:list(MODULES).index(name)]:
                raise ValueError("Local import is not built first: " + imported)
            if not (imported.startswith("Mathlib.") or imported in MODULES):
                raise ValueError("Unexpected import: " + imported)

    previous_path = directory / "collatz-rank-growth-lean-check.json"
    if sha(previous_path) != "050de40bcd68bd96287952af13148261b640e13231dce3baabdf2aa4816311ad":
        raise ValueError("The retained reversed report changed")
    previous = json.loads(previous_path.read_text())
    for name in set(MODULES) & set(PREVIOUS_MODULES):
        if hashlib.sha256(sources[name]).hexdigest() != previous["builds"][name]["source_sha256"]:
            raise ValueError("A retained dependency changed: " + name)
    for name, digest in previous["checker_sources_sha256"].items():
        if sha(directory / name) != digest:
            raise ValueError("A retained verification helper changed: " + name)

    mathlib = args.mathlib_root.resolve()
    revisions = {"mathlib": audited_revision(mathlib, MATHLIB_REVISION)}
    manifest = json.loads((mathlib / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError("Unpinned dependency")
        revisions[package["name"]] = audited_revision(
            mathlib / ".lake" / "packages" / package["name"], package["rev"])
    version = run([args.lake, "env", "lean", "--version"], mathlib).strip()
    if version != previous["lean_version"]:
        raise ValueError("Wrong Lean version")
    lean = run([args.lake, "env", "which", "lean"], mathlib).strip()
    lean_paths = run([args.lake, "env", "printenv", "LEAN_PATH"], mathlib).strip()
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-finite-source-support-", dir=args.build_root) as temporary:
        build = Path(temporary)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(build) + ":" + lean_paths
        for name, expected in MODULES.items():
            output_path = build / (name + ".olean")
            command = [lean, "-o", str(output_path), str(directory / (name + ".lean"))]
            compiled = subprocess.run(command, cwd=directory, env=environment, text=True,
                                      capture_output=True, timeout=600, check=False)
            if compiled.returncode or compiled.stderr:
                raise RuntimeError(f"Lean failed for {name}:\n{compiled.stdout}\n{compiled.stderr}")
            axioms = audit_output(compiled.stdout, expected)
            if not output_path.is_file():
                raise ValueError("Lean did not write a compiled module")
            builds[name] = {
                "command": command, "compiler_exit_code": 0, "compiler_output": compiled.stdout,
                "source_sha256": hashlib.sha256(sources[name]).hexdigest(),
                "compiled_module_sha256": sha(output_path), "declaration_axioms": axioms,
            }
            print(json.dumps({"module": name, "status": "PASS", "declarations": len(axioms)}), flush=True)
    for name, data in sources.items():
        if (directory / (name + ".lean")).read_bytes() != data:
            raise ValueError("A proof source changed during checking")
    helpers = [
        "check_collatz_finite_source_support.py", "check_collatz_rank_growth.py", "check_collatz_odd_blocks.py", "check_collatz_reversed_conditions.py",
        "check_collatz_reversed_certificate.py",
        "check_collatz_forward_certificate.py",
        "check_collatz_certificate_bridge.py", "check_collatz_core.py",
        "check_reversed_binary_power_closure.py",
    ]
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "builds": builds,
        "all_local_dependencies_built_in_fresh_directory": True,
        "lean_version": version, "dependency_revisions": revisions,
        "mathlib_manifest_sha256": sha(mathlib / "lake-manifest.json"),
        "previous_reports_sha256": {previous_path.name: sha(previous_path)},
        "checker_sources_sha256": {name: sha(directory / name) for name in helpers},
        "sat_solver_calls": 0, "unproved_target": "CollatzResearch.CollatzConjecture",
        "missing_witness": "A reversed natural affine certificate satisfying all eleven weak comparisons and at least one of the two strict outer-boundary offset comparisons",
        "scope": (
            "Cayley-Hamilton over integer matrices and the injective natural-number cast show that "
            "a dimension-length window of zero scalar matrix powers forces every later power to vanish. "
            "If the observed affine iterates are unbounded, some power between d and 2d-1 therefore "
            "sees a positive contribution from the sum of the initial vector and the affine offset. "
            "For every reversed natural affine certificate with all eleven weak comparisons and either "
            "eligible strict offset, and every binary word w, there exists d<=k<2d such that "
            "r*M_w*B^k*(gamma+b)>0, with d the dimension and r the actual outer-boundary matrix row. "
            "Both initial and repeated affine sources are retained. No coefficient cap, binary-matrix "
            "order, invertibility, or normalization is assumed. This supplies no matrix certificate "
            "and no proof of the Collatz conjecture."
        ),
    }
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "modules": len(MODULES),
                      "audited_declarations": sum(map(len, MODULES.values())),
                      "proves_collatz_conjecture": False, "sat_solver_calls": 0}))


if __name__ == "__main__":
    main()
