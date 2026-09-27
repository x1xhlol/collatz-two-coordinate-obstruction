#!/usr/bin/env python3
"""Rebuild the conditional forward-certificate proof and every local dependency."""

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
from check_collatz_certificate_bridge import BRIDGE_THEOREMS
from check_reversed_binary_power_closure import (
    MATHLIB_REVISION, STANDARD_AXIOMS, audited_revision, run,
)


def names(namespace, declarations):
    return {namespace + declaration for declaration in declarations.split()}


MODULES = {
    "CollatzCore": CORE_THEOREMS,
    "CollatzCertificateBridge": BRIDGE_THEOREMS,
    "CollatzNaturalAffine": names("NatAffine.", """
        eval_comp eval_monotone eval_weak eval_strict_at
        all_rules_and_three_strict_roots_imply_collatz
    """),
    "CollatzWellFoundedBridge": {
        "collatz_of_wellFounded_rank",
        *names("GeneralCertificate.", """
            readout_binaryInterp_monotone ternary_conversion_strict certificate_implies_collatz
        """),
    },
    "CollatzCertificateStages": names("CertificateStages.", """
        rootLeft_prod rootRight_prod rootWeak_prod rootStrict_prod_left
        rootStrict_prod_right complete_implies_collatz three_stage_closure
    """),
    "CollatzNaturalStages": names("NaturalStages.", """
        rootWeak_of_coefficient rootStrict_of_coefficient
    """),
    "CollatzPublishedNaturalResiduals": names("PublishedNaturalResiduals.", """
        ceFirst_common ceFirst_f_weak ceFirst_g_weak ceFirst_f_strict
        ceLast_common ceLast_g_weak ceLast_g_strict
        cfFirst_common cfFirst_e_weak cfFirst_g_weak cfFirst_e_strict
        cfLast_common cfLast_g_weak cfLast_g_strict
        first_ce_certificate_implies_collatz first_cf_certificate_implies_collatz
    """),
    "CollatzPublishedArcticResiduals": names("PublishedArcticResiduals.", """
        inc_monotone firstData first_e_strict first_f_weak lastData last_f_strict
        first_cg_certificate_implies_collatz
    """),
    "CollatzForwardCertificate": {
        "first_eligible_root_implies_collatz", "natural_affine_first_removal_implies_collatz",
    },
}
AUDITED_DEFINITIONS = {"firstData", "lastData"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_output(output, expected):
    if "warning:" in output or "error:" in output:
        raise ValueError("Lean reported a warning or error:\n" + output)
    pattern = (r"'CollatzResearch\.([A-Za-z0-9_.]+)' "
               r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))")
    axioms = {}
    for declaration, entries, no_axioms in re.findall(pattern, output):
        if declaration in axioms:
            raise ValueError("Duplicate axiom report: " + declaration)
        declared = set() if no_axioms else {
            entry.strip() for entry in entries.split(",") if entry.strip()
        }
        if not declared <= STANDARD_AXIOMS:
            raise ValueError(f"Unexpected axioms in {declaration}: {declared}")
        axioms[declaration] = sorted(declared)
    if set(axioms) != expected:
        raise ValueError(f"Wrong declaration coverage: {set(axioms) ^ expected}")
    return axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    report = (args.report or directory / "collatz-forward-certificate-lean-check.json").resolve()
    if report.exists():
        raise ValueError("Refusing to overwrite retained evidence")
    sources = {name: (directory / (name + ".lean")).read_bytes() for name in MODULES}
    for name, data in sources.items():
        source = data.decode()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque|unsafe)\b",
                     source, flags=re.MULTILINE):
            raise ValueError("Forbidden proof placeholder or declaration in " + name)
        declared = set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.MULTILINE))
        if name == "CollatzPublishedArcticResiduals":
            for definition in AUDITED_DEFINITIONS:
                if not re.search(r"^def " + definition + r"\b", source, re.MULTILINE):
                    raise ValueError("Missing audited certificate definition")
            declared |= AUDITED_DEFINITIONS
        if declared != {entry.split(".")[-1] for entry in MODULES[name]}:
            raise ValueError("The declared theorem list differs in " + name)
        imports = re.findall(r"^import\s+(\S+)", source, re.MULTILINE)
        for imported in imports:
            if imported.startswith("Collatz") and imported not in list(MODULES)[:list(MODULES).index(name)]:
                raise ValueError("Local import is not built first: " + imported)
            if not (imported.startswith("Mathlib.") or imported in MODULES):
                raise ValueError("Unexpected import: " + imported)

    core_report = json.loads((directory / "collatz-core-lean-check.json").read_text())
    bridge_report = json.loads((directory / "collatz-certificate-bridge-lean-check.json").read_text())
    if (core_report["status"] != "PASS" or core_report["proves_collatz_conjecture"] is not False
            or core_report["source_sha256"] != hashlib.sha256(sources["CollatzCore"]).hexdigest()):
        raise ValueError("The previously checked Collatz core changed")
    if (bridge_report["status"] != "PASS" or bridge_report["proves_collatz_conjecture"] is not False
            or bridge_report["builds"]["CollatzCertificateBridge"]["source_sha256"]
            != hashlib.sha256(sources["CollatzCertificateBridge"]).hexdigest()):
        raise ValueError("The previously checked certificate bridge changed")

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
    with tempfile.TemporaryDirectory(prefix="collatz-forward-", dir=args.build_root) as temporary:
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
            if (directory / (name + ".lean")).read_bytes() != sources[name]:
                raise ValueError("A proof source changed during checking")
            builds[name] = {
                "command": command,
                "compiler_exit_code": 0,
                "compiler_output": compiled.stdout,
                "source_sha256": hashlib.sha256(sources[name]).hexdigest(),
                "compiled_module_sha256": sha(output_path),
                "declaration_axioms": axioms,
            }
            print(json.dumps({"module": name, "status": "PASS", "declarations": len(axioms)}), flush=True)

    for name, data in sources.items():
        if (directory / (name + ".lean")).read_bytes() != data:
            raise ValueError("A proof source changed before the final audit")
    result = {
        "status": "PASS",
        "proves_collatz_conjecture": False,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "builds": builds,
        "all_local_dependencies_built_in_fresh_directory": True,
        "lean_version": version,
        "dependency_revisions": revisions,
        "mathlib_manifest_sha256": sha(mathlib_root / "lake-manifest.json"),
        "previous_reports_sha256": {name: sha(directory / name) for name in [
            "collatz-core-lean-check.json", "collatz-certificate-bridge-lean-check.json",
        ]},
        "checker_sources_sha256": {name: sha(directory / name) for name in [
            "check_collatz_forward_certificate.py", "check_collatz_certificate_bridge.py",
            "check_collatz_core.py", "check_reversed_binary_power_closure.py",
        ]},
        "residual_transcription_sources_sha256": {
            name: sha(directory.parent / "rewriting-search" / "published-eligible-residuals" / name)
            for name in ["without-09.json", "without-10.json", "without-11.json"]
        },
        "sat_solver_calls": 0,
        "unproved_target": "CollatzResearch.CollatzConjecture",
        "missing_witness": (
            "A concrete first-stage certificate with the eight common comparisons, "
            "all three weak root comparisons, and at least one universally strict root comparison"
        ),
        "scope": (
            "Universal conditional implications from a first eligible forward root removal "
            "to the standard Collatz conjecture. All six residual stage objects and their "
            "required comparisons are proved in Lean; the arctic stages use explicit "
            "natural-number max/conditional-successor functions on vectors with positive "
            "first coordinate. A lexicographic rank combines the stages. The natural affine "
            "interface accepts finite coefficient comparisons for an arbitrary finite index "
            "type. No concrete first-stage witness is supplied. No SAT encoding, external "
            "termination theorem, or numerical Collatz enumeration is assumed as an axiom."
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
