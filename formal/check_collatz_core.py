#!/usr/bin/env python3
"""Check the Collatz definitions and partial theorems; never certify the conjecture."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

from check_reversed_binary_power_closure import (
    MATHLIB_REVISION, STANDARD_AXIOMS, audited_revision, run,
)


THEOREMS = {
    "step_pos", "iterate_pos", "reaches_one_of_reachable",
    "collatz_iff_universal_descent", "step_even", "step_odd", "two_steps_odd",
    "power_two_steps", "odd_block_reachable", "collatz_of_rank", "even_descends",
    "three_steps_of_four_mul_add_one", "one_mod_four_descends",
    "non_descending_is_three_mod_four", "universal_descent_iff_three_mod_four",
    "collatz_iff_three_mod_four_descent",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    source = directory / "CollatzCore.lean"
    report = (args.report or directory / "collatz-core-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    source_bytes = source.read_bytes()
    source_text = source_bytes.decode()
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                 source_text, flags=re.MULTILINE):
        raise ValueError("Forbidden proof placeholder or declaration")
    declarations = set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source_text, re.MULTILINE))
    if declarations != THEOREMS:
        raise ValueError("The retained theorem list does not cover exactly the source declarations")

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
    command = [args.lake, "env", "lean", str(source)]
    output = run(command, mathlib_root)
    if "warning:" in output or "error:" in output:
        raise ValueError("Lean reported a warning or error:\n" + output)

    axioms = {}
    pattern = (r"'CollatzResearch\.([A-Za-z0-9_]+)' "
               r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))")
    for theorem, entries, no_axioms in re.findall(pattern, output):
        if theorem in axioms:
            raise ValueError("Duplicate axiom report: " + theorem)
        declared = set() if no_axioms else {
            entry.strip() for entry in entries.split(",") if entry.strip()
        }
        if not declared <= STANDARD_AXIOMS:
            raise ValueError(f"Unexpected axioms in {theorem}: {declared}")
        axioms[theorem] = sorted(declared)
    if set(axioms) != THEOREMS:
        raise ValueError("Wrong theorem axiom-report coverage")
    if source.read_bytes() != source_bytes:
        raise ValueError("The proof source changed during checking")

    result = {
        "status": "PASS",
        "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "checker_source_sha256": {
            "check_collatz_core.py": sha(Path(__file__).resolve()),
            "check_reversed_binary_power_closure.py": sha(
                directory / "check_reversed_binary_power_closure.py"),
        },
        "mathlib_manifest_sha256": sha(mathlib_root / "lake-manifest.json"),
        "dependency_revisions": revisions,
        "lean_version": version,
        "command": command,
        "working_directory": str(mathlib_root),
        "compiler_exit_code": 0,
        "compiler_output": output,
        "theorem_axioms": axioms,
        "sat_solver_calls": 0,
        "unproved_target": "CollatzResearch.CollatzConjecture",
        "remaining_equivalent_obligation": (
            "For every natural n > 1 with n % 4 = 3, some standard Collatz "
            "iterate is positive and strictly smaller than n."
        ),
        "conditional_rank_theorem": (
            "collatz_of_rank requires an actual natural-valued rank together "
            "with universal proofs of both its inequalities. No such rank "
            "and proofs have been supplied."
        ),
        "scope": (
            "Definitions of the standard 3n+1 map and the full positive-integer "
            "conjecture; positivity, reachability composition, exact even/odd "
            "and power-of-two steps, an odd-block identity, equivalence to "
            "universal descent, a conditional ranking criterion, and descent "
            "for even integers and integers congruent to 1 modulo 4. "
            "This is not a proof of the remaining universal descent claim "
            "or of Collatz."
        ),
    }
    with report.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "theorems": len(axioms),
                      "proves_collatz_conjecture": False,
                      "source_sha256": result["source_sha256"], "sat_solver_calls": 0}))


if __name__ == "__main__":
    main()
