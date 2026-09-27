#!/usr/bin/env python3
"""Compile the retained theorem and audit its declared axioms and pinned dependencies."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess


MATHLIB_REVISION = "a3a10db0e9d66acbebf76c5e6a135066525ac900"
THEOREMS = {
    "binary_power_closure",
    "first_gap_zero_of_det_ne_zero",
    "first_gap_zero_of_return_bound",
    "first_gap_zero_of_coordinate_returns",
    "positive_first_gap_has_transient_coordinate",
    "ordered_reversed_gaps_zero_of_det_ne_zero",
    "first_gap_le_BAa",
    "first_gap_zero_of_BA_return_bound",
    "four_affine_rules_gaps_zero_of_det_ne_zero",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(arguments, directory):
    result = subprocess.run(arguments, cwd=directory, text=True, capture_output=True,
                            timeout=600, check=False)
    if result.returncode:
        raise RuntimeError(f"Command failed: {arguments!r}\n{result.stdout}\n{result.stderr}")
    if result.stderr:
        raise RuntimeError(f"Unexpected standard-error output: {arguments!r}\n{result.stderr}")
    return result.stdout


def audited_revision(directory, expected):
    actual = run(["git", "rev-parse", "HEAD"], directory).strip()
    if actual != expected:
        raise ValueError(f"Unexpected revision in {directory}: {actual}")
    run(["git", "diff", "--exit-code", "HEAD", "--"], directory)
    return actual


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    source = directory / "ReversedBinaryPowerClosure.lean"
    report = (args.report or directory / "reversed-binary-power-closure-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    source_bytes = source.read_bytes()
    source_text = source_bytes.decode()
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                 source_text, flags=re.MULTILINE):
        raise ValueError("The source contains a forbidden proof placeholder or declaration")

    mathlib_root = args.mathlib_root.resolve()
    revisions = {"mathlib": audited_revision(mathlib_root, MATHLIB_REVISION)}
    manifest = json.loads((mathlib_root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError("Expected every mathlib dependency to have a pinned Git revision")
        revisions[package["name"]] = audited_revision(
            mathlib_root / ".lake" / "packages" / package["name"], package["rev"])
    version = run([args.lake, "env", "lean", "--version"], mathlib_root).strip()
    if not version.startswith("Lean (version 4.27.0,"):
        raise ValueError(f"Unexpected Lean version: {version}")

    command = [args.lake, "env", "lean", str(source)]
    output = run(command, mathlib_root)
    if "warning:" in output or "error:" in output:
        raise ValueError(f"Lean reported a warning or error:\n{output}")
    axioms = {}
    for theorem, entries in re.findall(
            r"'CollatzCertificate\.([A-Za-z0-9_]+)' depends on axioms:\s*\[([^]]*)\]", output):
        if theorem in axioms:
            raise ValueError(f"Duplicate axiom report: {theorem}")
        declared = {entry.strip() for entry in entries.split(",") if entry.strip()}
        if not declared <= STANDARD_AXIOMS:
            raise ValueError(f"Unexpected axioms in {theorem}: {declared}")
        axioms[theorem] = sorted(declared)
    if set(axioms) != THEOREMS:
        raise ValueError(f"Wrong theorem coverage: {set(axioms) ^ THEOREMS}")
    if source.read_bytes() != source_bytes:
        raise ValueError("The proof source changed during checking")

    result = {
        "status": "PASS",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mathlib_manifest_sha256": hashlib.sha256(
            (mathlib_root / "lake-manifest.json").read_bytes()).hexdigest(),
        "dependency_revisions": revisions,
        "lean_version": version,
        "command": command,
        "working_directory": str(mathlib_root),
        "theorem_axioms": axioms,
        "compiler_output": output,
        "compiler_exit_code": 0,
        "sat_solver_calls": 0,
        "scope": (
            "Universal theorems for real matrices over arbitrary finite coordinate types: "
            "binary-power row closure, positive-power source annihilation, finite row-bound "
            "and coordinate-return exclusions, the transient-coordinate necessity, the "
            "stronger BA row-bound exclusion, and the invertible-matrix exclusion directly "
            "from four affine rewrite comparisons. This does not prove Collatz, graph "
            "path equivalences, or the separate preceding draft theorems."
        ),
    }
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "theorems": len(axioms),
                      "source_sha256": result["source_sha256"], "sat_solver_calls": 0}))


if __name__ == "__main__":
    main()
