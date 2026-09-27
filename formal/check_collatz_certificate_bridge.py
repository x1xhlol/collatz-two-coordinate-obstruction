#!/usr/bin/env python3
"""Rebuild and audit the conditional certificate-to-Collatz bridge in a fresh directory."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_collatz_core import THEOREMS as CORE_THEOREMS
from check_reversed_binary_power_closure import (
    MATHLIB_REVISION, STANDARD_AXIOMS, audited_revision, run,
)


BRIDGE_THEOREMS = {
    "binaryInterp_one", "binaryInterp_even", "binaryInterp_odd",
    "binaryInterp_monotone", "readout_binaryInterp_monotone",
    "ternary_conversion_strict", "root_strict_certificate_implies_collatz",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_output(output, expected):
    if "warning:" in output or "error:" in output:
        raise ValueError("Lean reported a warning or error:\n" + output)
    pattern = (r"'CollatzResearch\.([A-Za-z0-9_]+)' "
               r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))")
    axioms = {}
    for theorem, entries, no_axioms in re.findall(pattern, output):
        if theorem in axioms:
            raise ValueError("Duplicate axiom report: " + theorem)
        declared = set() if no_axioms else {
            entry.strip() for entry in entries.split(",") if entry.strip()
        }
        if not declared <= STANDARD_AXIOMS:
            raise ValueError(f"Unexpected axioms in {theorem}: {declared}")
        axioms[theorem] = sorted(declared)
    if set(axioms) != expected:
        raise ValueError("Wrong theorem axiom-report coverage")
    return axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "collatz-certificate-bridge-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    modules = {"CollatzCore": CORE_THEOREMS, "CollatzCertificateBridge": BRIDGE_THEOREMS}
    sources = {name: (directory / (name + ".lean")).read_bytes() for name in modules}
    for name, data in sources.items():
        source = data.decode()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                     source, flags=re.MULTILINE):
            raise ValueError("Forbidden proof placeholder or declaration in " + name)
        declared = set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE))
        if declared != modules[name]:
            raise ValueError("The declared theorem list differs in " + name)
    core_report = json.loads((directory / "collatz-core-lean-check.json").read_text())
    if (core_report["status"] != "PASS" or core_report["proves_collatz_conjecture"] is not False
            or core_report["source_sha256"] != hashlib.sha256(sources["CollatzCore"]).hexdigest()):
        raise ValueError("The previously checked Collatz core changed")

    mathlib_root = args.mathlib_root.resolve()
    revisions = {"mathlib": audited_revision(mathlib_root, MATHLIB_REVISION)}
    manifest = json.loads((mathlib_root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError("An unpinned dependency is present")
        revisions[package["name"]] = audited_revision(
            mathlib_root / ".lake" / "packages" / package["name"], package["rev"])
    version = run([args.lake, "env", "lean", "--version"], mathlib_root).strip()
    if not version.startswith("Lean (version 4.27.0,"):
        raise ValueError("Unexpected Lean version: " + version)
    lean = run([args.lake, "env", "which", "lean"], mathlib_root).strip()
    lean_paths = run([args.lake, "env", "printenv", "LEAN_PATH"], mathlib_root).strip()
    builds = {}
    with tempfile.TemporaryDirectory(prefix="collatz-bridge-", dir=args.build_root) as temporary:
        build = Path(temporary)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(build) + ":" + lean_paths
        for name, expected in modules.items():
            output_path = build / (name + ".olean")
            command = [lean, "-o", str(output_path), str(directory / (name + ".lean"))]
            compiled = subprocess.run(command, cwd=directory, env=environment, text=True,
                                      capture_output=True, timeout=600, check=False)
            if compiled.returncode or compiled.stderr:
                raise RuntimeError(f"Lean failed for {name}:\n{compiled.stdout}\n{compiled.stderr}")
            axioms = audit_output(compiled.stdout, expected)
            if not output_path.is_file():
                raise ValueError("Lean did not write a compiled module")
            if (directory / (name + ".lean")).read_bytes() != sources[name]:
                raise ValueError("A proof source changed during checking")
            builds[name] = {
                "command": command,
                "compiler_exit_code": 0,
                "compiler_output": compiled.stdout,
                "source_sha256": hashlib.sha256(sources[name]).hexdigest(),
                "compiled_module_sha256": sha(output_path),
                "theorem_axioms": axioms,
            }

    for name, data in sources.items():
        if (directory / (name + ".lean")).read_bytes() != data:
            raise ValueError("A proof source changed before the final audit")

    result = {
        "status": "PASS",
        "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "builds": builds,
        "fresh_dependency_module_built_from_retained_core_source": True,
        "lean_version": version,
        "dependency_revisions": revisions,
        "mathlib_manifest_sha256": sha(mathlib_root / "lake-manifest.json"),
        "core_check_sha256": sha(directory / "collatz-core-lean-check.json"),
        "checker_source_sha256": {name: sha(directory / name) for name in [
            "check_collatz_certificate_bridge.py", "check_collatz_core.py",
            "check_reversed_binary_power_closure.py",
        ]},
        "sat_solver_calls": 0,
        "unproved_target": "CollatzResearch.CollatzConjecture",
        "missing_witness": "A constructed RootStrictCertificate with every field proved in Lean",
        "scope": (
            "A conditional theorem: monotone binary maps and natural-valued readout, "
            "two endpoint comparisons, six swap comparisons, and all three strict "
            "root comparisons imply the standard Collatz conjecture. The conversion "
            "is proved for every positive integer by induction on binary prefixes. "
            "No object satisfying those hypotheses has been constructed. The ongoing "
            "SAT searches require only one eligible strict root comparison; such a "
            "partial candidate would not by itself satisfy this theorem."
        ),
    }
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "bridge_theorems": len(BRIDGE_THEOREMS),
                      "dependency_theorems": len(CORE_THEOREMS),
                      "proves_collatz_conjecture": False, "sat_solver_calls": 0}))


if __name__ == "__main__":
    main()
