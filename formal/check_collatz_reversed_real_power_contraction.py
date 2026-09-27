#!/usr/bin/env python3
"""Rebuild contraction exclusions for every positive matrix power of a reversed real certificate."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_collatz_reversed_real_dynamics import MODULES as PREVIOUS_MODULES
from check_reversed_binary_power_closure import (
    MATHLIB_REVISION, STANDARD_AXIOMS, audited_revision, run,
)


MODULES = dict(PREVIOUS_MODULES)
MODULES["CollatzReversedRealPowerContraction"] = {
    "RealContraction.nonnegative_matrix_power_mulVec", "RealContraction.matrix_power_sum_telescopes",
    "RealContraction.positive_contraction_of_matrix_power",
    "RealContraction.reversed_real_excludes_positive_power_contraction",
    "RealContraction.reversed_real_second_binary_power_row_sum_bound",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_output(output, expected):
    pattern = (r"'((?:CollatzCertificate|CollatzResearch)\.[A-Za-z0-9_.]+)' "
               r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))")
    axioms = {}
    for name, entries, no_axioms in re.findall(pattern, output):
        if name in axioms:
            raise ValueError("Duplicate axiom report")
        declared = set() if no_axioms else {entry.strip() for entry in entries.split(",") if entry.strip()}
        if not declared <= STANDARD_AXIOMS:
            raise ValueError("Unexpected axioms: " + name)
        axioms[name] = sorted(declared)
    if set(axioms) != expected or re.sub(pattern, "", output).strip():
        raise ValueError("Wrong axiom coverage or unexpected compiler output:\n" + output)
    return axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "collatz-reversed-real-power-contraction-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    sources = {name: (directory / (name + ".lean")).read_bytes() for name in MODULES}
    for name, data in sources.items():
        source = data.decode()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                     source, flags=re.MULTILINE):
            raise ValueError("Forbidden proof placeholder or declaration in " + name)
        declarations = {entry.split(".")[-1] for entry in MODULES[name]}
        if name == "ReversedBinaryPowerClosure":
            declarations.update({"admissible_mul_B", "admissible_zero_gaps"})
        if name == "CollatzReversedNecessaryConditions":
            declarations.remove("ofModel")
            if not re.search(r"^def ofModel\b", source, re.MULTILINE):
                raise ValueError("Missing audited certificate definition")
        if set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE)) != declarations:
            raise ValueError("Wrong theorem coverage in " + name)
        for imported in re.findall(r"^import\s+(\S+)", source, re.MULTILINE):
            if not imported.startswith("Mathlib.") and imported not in list(MODULES)[:list(MODULES).index(name)]:
                raise ValueError("Unexpected or unbuilt local import: " + imported)

    previous_digests = {
        "collatz-reversed-real-dynamics-lean-check.json": "ccf2e072bdc0cbe0f3c1dd17bba74bcd305c7e7c3e985ad3d01381943da57e00",
    }
    previous_reports = {}
    for filename, digest in previous_digests.items():
        path = directory / filename
        if sha(path) != digest:
            raise ValueError("A retained dependency report changed")
        previous = json.loads(path.read_text())
        previous_reports[filename] = previous
        for name, entry in previous["builds"].items():
            if sha(directory / (name + ".lean")) != entry["source_sha256"]:
                raise ValueError("A retained proof dependency changed: " + name)
        for name, expected in previous["checker_sources_sha256"].items():
            if sha(directory / name) != expected:
                raise ValueError("A retained checking helper changed: " + name)

    mathlib = args.mathlib_root.resolve()
    revisions = {"mathlib": audited_revision(mathlib, MATHLIB_REVISION)}
    manifest = json.loads((mathlib / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError("Unpinned dependency")
        revisions[package["name"]] = audited_revision(
            mathlib / ".lake" / "packages" / package["name"], package["rev"])
    version = run([args.lake, "env", "lean", "--version"], mathlib).strip()
    if any(version != previous["lean_version"] for previous in previous_reports.values()):
        raise ValueError("Wrong Lean version")
    lean = run([args.lake, "env", "which", "lean"], mathlib).strip()
    lean_paths = run([args.lake, "env", "printenv", "LEAN_PATH"], mathlib).strip()
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-reversed-real-power-contraction-", dir=args.build_root) as temporary:
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
            namespace = "CollatzCertificate." if name.startswith("Reversed") else "CollatzResearch."
            axioms = audit_output(compiled.stdout, {namespace + item for item in expected})
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
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "builds": builds,
        "all_local_dependencies_built_in_fresh_directory": True,
        "lean_version": version, "dependency_revisions": revisions,
        "mathlib_manifest_sha256": sha(mathlib / "lake-manifest.json"),
        "previous_reports_sha256": previous_digests,
        "checker_sources_sha256": {name: sha(directory / name) for name in {
            "check_collatz_reversed_real_power_contraction.py",
            *(name for previous in previous_reports.values() for name in previous["checker_sources_sha256"]),
        }},
        "sat_solver_calls": 0,
        "scope": (
            "For a nonnegative real square matrix B, if a positive power B^k strictly contracts a "
            "strictly positive vector v in all coordinates, then the positive vector "
            "v + Bv + ... + B^(k-1)v is strictly contracted by B. Under all eleven reversed affine "
            "weak comparisons, nonnegative real coefficients, and an eligible positive offset gap, "
            "this contradicts the previously proved growth obstruction. Therefore every positive "
            "power B^k has some row sum at least one, and for every strictly positive vector v "
            "some coordinate of B^k v is at least the corresponding coordinate of v. All affine "
            "offsets remain unrestricted and nonnegative. No certificate or Collatz proof is supplied."
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
