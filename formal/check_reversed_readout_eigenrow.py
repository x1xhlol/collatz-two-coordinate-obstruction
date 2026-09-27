#!/usr/bin/env python3
"""Freshly rebuild the second-binary readout eigenrow obstruction."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_reversed_binary_power_closure import (
    MATHLIB_REVISION, STANDARD_AXIOMS, THEOREMS, audited_revision, run,
)


MODULES = {
    "ReversedBinaryPowerClosure": THEOREMS,
    "ReversedReadoutEigenrow": {
        "row_order_zero_second_gap", "row_domination_zero_gaps",
        "zero_second_binary_row_gaps", "second_binary_readout_eigenrow_gaps",
        "five_affine_rules_gaps_zero_of_second_eigenrow",
        "five_affine_rules_gaps_zero_of_scalar_second_matrix",
    },
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_output(output, expected):
    pattern = r"'CollatzCertificate\.([A-Za-z0-9_]+)' depends on axioms:\s*\[([^]]*)\]"
    axioms = {}
    for name, entries in re.findall(pattern, output):
        if name in axioms:
            raise ValueError("Duplicate axiom report")
        declared = {entry.strip() for entry in entries.split(",") if entry.strip()}
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
    report = (args.report or directory / "reversed-readout-eigenrow-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    sources = {name: (directory / (name + ".lean")).read_bytes() for name in MODULES}
    for name, data in sources.items():
        source = data.decode()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                     source, flags=re.MULTILINE):
            raise ValueError("Forbidden proof placeholder or declaration in " + name)
        declarations = set(MODULES[name])
        if name == "ReversedBinaryPowerClosure":
            declarations.update({"admissible_mul_B", "admissible_zero_gaps"})
        if set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE)) != declarations:
            raise ValueError("Wrong theorem coverage in " + name)
        for imported in re.findall(r"^import\s+(\S+)", source, re.MULTILINE):
            if not imported.startswith("Mathlib.") and imported not in list(MODULES)[:list(MODULES).index(name)]:
                raise ValueError("Unexpected or unbuilt local import: " + imported)

    previous_path = directory / "reversed-binary-power-closure-lean-check.json"
    if sha(previous_path) != "4e9a83352406e3269b21a76c8fe07ce5cc9ed0826e6b5d8e299d84cc1f8093dc":
        raise ValueError("The retained dependency report changed")
    previous = json.loads(previous_path.read_text())
    if hashlib.sha256(sources["ReversedBinaryPowerClosure"]).hexdigest() != previous["source_sha256"]:
        raise ValueError("The retained proof dependency changed")
    if sha(directory / "check_reversed_binary_power_closure.py") != previous["checker_sha256"]:
        raise ValueError("The retained checking helper changed")

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
    with tempfile.TemporaryDirectory(prefix="reversed-readout-eigenrow-", dir=args.build_root) as temporary:
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
    result = {
        "status": "PASS", "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "builds": builds,
        "all_local_dependencies_built_in_fresh_directory": True,
        "lean_version": version, "dependency_revisions": revisions,
        "mathlib_manifest_sha256": sha(mathlib / "lake-manifest.json"),
        "previous_reports_sha256": {previous_path.name: sha(previous_path)},
        "checker_sources_sha256": {name: sha(directory / name) for name in (
            "check_reversed_readout_eigenrow.py", "check_reversed_binary_power_closure.py")},
        "sat_solver_calls": 0,
        "scope": (
            "Over nonnegative real affine maps in arbitrary finite dimension, five ordinary reversed "
            "weak comparisons force both eligible outer-boundary offset gaps to be zero if the "
            "actual boundary row is a left eigenrow of the second binary matrix with nonnegative "
            "eigenvalue. The zero eigenvalue is included. No eigenrow assumption on the first "
            "binary matrix is needed. A corollary excludes every scalar second binary matrix. "
            "These universal obstructions supply no certificate or proof of Collatz."
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
