#!/usr/bin/env python3
"""Rebuild the mixed-digit growth and five-map safe-family theorems."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_collatz_support_family import MODULES as PREVIOUS_MODULES, audit_output, names, sha
from check_reversed_binary_power_closure import MATHLIB_REVISION, audited_revision, run


MODULES = dict(PREVIOUS_MODULES)
MODULES["CollatzMixedSupport"] = names("MixedSupport.", """
    scale_pos label_affine label_residue_bound label_pos label_near_power
    interp_digit_le interp_label_le reversed_mixed_b_growth eval_affine observed_eval
    natural_mixed_b_growth natural_mixed_row_growth mixed_source_support matrixWord_append
    reversed_closed_safe_family
""")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "collatz-mixed-support-lean-check.json").resolve()
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

    previous_path = directory / "collatz-support-family-lean-check.json"
    if sha(previous_path) != "1160a6e7d864c2aba0cf272d71619babade5c4ad7f73362199fd02ae5e90bf5f":
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
    with tempfile.TemporaryDirectory(prefix="collatz-mixed-support-", dir=args.build_root) as temporary:
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
        "check_collatz_mixed_support.py", "check_collatz_support_family.py", "check_collatz_finite_source_support.py", "check_collatz_rank_growth.py", "check_collatz_odd_blocks.py", "check_collatz_reversed_conditions.py",
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
            "Every reversed natural affine certificate satisfying all eleven weak comparisons and either "
            "eligible strict offset has a finite family F of coordinate supports. F contains the support "
            "of the actual outer-boundary readout row, is closed under the support successors of all five "
            "digit matrices A, B, E, F, G, and every member meets the support of some B^k*(gamma+b) "
            "for d<=k<2d. "
            "The theorem constructs F from the supports reached by all finite mixed binary/ternary words. "
            "Mixed labels are bounded residues modulo a product of twos and threes. The formally "
            "verified near-power rank estimates imply growth along B-affine iterates after each word. "
            "This formally justifies the existential closed-safe-family search filter without requiring "
            "that a searched family be the least one. No matrix witness or Collatz proof is supplied."
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
