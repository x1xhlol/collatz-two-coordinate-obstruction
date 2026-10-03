#!/usr/bin/env python3
"""Freshly compile and kernel-check the additive finite cylinder-energy extension."""
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Lucas Valbuena

from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

import audit_helpers

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LIBRARY_ROOTS = {
    "Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq",
    "ProofWidgets", "ImportGraph", "LeanSearchClient", "Plausible",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def run_checked(command, *, cwd=None, env=None):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
    require(result.returncode == 0, result.stdout + result.stderr)
    return result.stdout.strip()


def validate_package():
    manifest = read_json(ROOT / "bundle-manifest.json")
    for relative, expected in manifest["files"].items():
        path = ROOT / relative
        require(path.is_file() and sha(path) == expected,
                f"Package file missing or changed: {relative}")
    modules = manifest["modules"]
    actual = {p.stem for p in (ROOT / "source").glob("*.lean")}
    require(actual == set(modules), "Package Lean source inventory mismatch")
    inventories = {name: audit_helpers.source_inventory(name) for name in modules}
    for name, inventory in inventories.items():
        require(inventory["sha256"] == modules[name]["source_sha256"],
                f"Source hash mismatch: {name}")
        require(inventory["imports"] == modules[name]["imports"],
                f"Source import inventory mismatch: {name}")
        clean = audit_helpers.scrub_lean((ROOT / "source" / (name + ".lean")).read_text())
        require(not re.search(r"\b(sorry|admit|native_decide|axiom|implemented_by|extern)\b", clean),
                f"Forbidden proof/axiom bypass in source: {name}")
    ordered, active = [], set()

    def visit(name):
        if name in ordered:
            return
        require(name not in active, f"Local import cycle at {name}")
        active.add(name)
        for dependency in modules[name]["imports"]:
            if dependency in modules:
                visit(dependency)
        active.remove(name)
        ordered.append(name)

    for name in manifest["module_order"]:
        require(name in modules, f"Unknown module in build order: {name}")
        visit(name)
    require(ordered == manifest["module_order"] and set(ordered) == set(modules),
            "Build order is not the complete topological source order")
    return manifest, inventories


def source_imports(path):
    clean = audit_helpers.scrub_lean(path.read_text(encoding="utf-8"))
    return [name for line in clean.splitlines() if line.strip().startswith("import ")
            for name in line.strip().removeprefix("import ").split()]


def digest_json(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def dependency_closure(package, floor, native):
    local = package["modules"]
    floor_modules = floor["modules"]
    native_modules = native["source_hashes"]
    require(not (set(local) & set(floor_modules) or set(local) & set(native_modules)
                 or set(floor_modules) & set(native_modules)),
            "Application module shadows an authenticated dependency")
    found = {"application": set(), "floor": set(), "native": set()}
    active, order, fingerprints = set(), [], {}

    def visit(name):
        if name in fingerprints:
            return fingerprints[name]
        require(name not in active, f"Import cycle at {name}")
        if name in local:
            group, metadata = "application", local[name]
        elif name in floor_modules:
            group, metadata = "floor", floor_modules[name]
        elif name in native_modules:
            group = "native"
            require(name in native["dependencies"], f"Missing native imports: {name}")
            metadata = {"source_sha256": native_modules[name],
                        "imports": native["dependencies"][name]}
        else:
            require(name.split(".")[0] in LIBRARY_ROOTS,
                    f"Import outside authenticated sources and pinned libraries: {name}")
            fingerprints[name] = digest_json({"library_module": name,
                                              "toolchain": package["toolchain"]})
            return fingerprints[name]
        active.add(name)
        found[group].add(name)
        imports = [{"module": dependency, "fingerprint": visit(dependency)}
                   for dependency in metadata["imports"]]
        fingerprints[name] = digest_json({"module": name,
            "source_sha256": metadata["source_sha256"], "imports": imports})
        active.remove(name)
        if group == "application":
            order.append(name)
        return fingerprints[name]

    for name in package["entry_modules"]:
        require(name in local, f"Unknown application endpoint: {name}")
        visit(name)
    require(found["application"] == set(local) and order == package["module_order"],
            "Application inventory is not the minimal endpoint import closure")
    for group in ["floor", "native"]:
        require(sorted(found[group]) == package[f"required_{group}_modules"],
                f"Required {group} closure differs from the frozen inventory")
    for name, metadata in local.items():
        require(fingerprints[name] == metadata["dependency_fingerprint"],
                f"Application dependency fingerprint mismatch: {name}")
    return found, fingerprints


def checked_record_pin(path, override, reference, label):
    expected = override or reference
    require(re.fullmatch(r"[0-9a-f]{64}", expected) is not None,
            f"{label} replay-record pin must be a lowercase SHA-256 digest")
    require(sha(path) == expected, f"{label} replay-record pin mismatch")
    return expected


def authenticate_dependencies(args, package):
    npins, fpins = package["native_base"], package["periodic_census_base"]
    native_manifest_path = args.native_bundle / "replay-manifest.json"
    floor_manifest_path = args.floor_bundle / "bundle-manifest.json"
    require(sha(native_manifest_path) == npins["manifest_sha256"],
            "Native manifest pin mismatch")
    require(sha(floor_manifest_path) == fpins["manifest_sha256"],
            "Periodic-census manifest pin mismatch")
    native_record_sha = checked_record_pin(args.native_build / "replay-record.json",
        args.native_record_sha256, npins["reference_replay_record_sha256"], "Native")
    floor_record_sha = checked_record_pin(args.floor_build / "replay-record.json",
        args.floor_record_sha256, fpins["reference_replay_record_sha256"], "Periodic-census")
    native, floor = read_json(native_manifest_path), read_json(floor_manifest_path)
    nr = read_json(args.native_build / "replay-record.json")
    fr = read_json(args.floor_build / "replay-record.json")
    require(nr.get("status") == fr.get("status") == "PASS", "Dependency record is not PASS")
    require(nr.get("manifest_sha256") == npins["manifest_sha256"],
            "Native record belongs to a different source manifest")
    require(fr.get("bundle_manifest_sha256") == fpins["manifest_sha256"],
            "Periodic-census record belongs to a different source manifest")
    require(fr.get("native_manifest_sha256") == npins["manifest_sha256"] and
            fr.get("native_replay_record_sha256") == native_record_sha,
            "Periodic-census replay used a different native replay")
    require(fr.get("module_order") == floor["module_order"],
            "Periodic-census replay omitted application modules")
    for key in ["lean_version", "mathlib_revision", "mathlib_lake_manifest_sha256",
                "dependency_revisions"]:
        require(nr.get(key) == native[key] == package["toolchain"][key],
                f"Native/toolchain provenance mismatch: {key}")
    require(fr.get("toolchain") == floor["toolchain"] == package["toolchain"],
            "Periodic-census/toolchain provenance mismatch")
    require(nr.get("axioms") and all(set(xs) <= ALLOWED_AXIOMS
            for xs in nr["axioms"].values()), "Native record has unexpected axioms")
    found, fingerprints = dependency_closure(package, floor, native)
    evidence = {"native": {}, "floor": {}}
    for name in sorted(found["native"]):
        relative = name.replace(".", "/")
        source = args.native_bundle / "source" / (relative + ".lean")
        obj = args.native_build / "modules" / (relative + ".olean")
        require(name in nr.get("builds", {}), f"Native replay omitted required module: {name}")
        require(nr["builds"][name].get("exit_code") == 0,
                f"Native required module has no successful build: {name}")
        source_sha, object_sha = sha(source), sha(obj)
        require(source_sha == native["source_hashes"][name]
                == nr["source_hashes"].get(name), f"Native source mismatch: {name}")
        imports = source_imports(source)
        require([dependency for dependency in imports if dependency in native["source_hashes"]]
                == native["dependencies"][name], f"Native source/import mismatch: {name}")
        require(all(dependency in native["source_hashes"] or
                    dependency.split(".")[0] in LIBRARY_ROOTS for dependency in imports),
                f"Native import outside authenticated sources and pinned libraries: {name}")
        fingerprint = native["dependency_fingerprints"][name]
        require(fingerprint == nr["dependency_fingerprints"].get(name),
                f"Native dependency fingerprint mismatch: {name}")
        require(object_sha == nr["builds"][name]["olean_sha256"],
                f"Native object mismatch: {name}")
        evidence["native"][name] = {"source_sha256": source_sha,
            "object_sha256": object_sha, "native_dependency_fingerprint": fingerprint,
            "closure_fingerprint": fingerprints[name]}
    for name in sorted(found["floor"]):
        source = args.floor_bundle / "source" / (name + ".lean")
        obj = args.floor_build / "modules" / (name + ".olean")
        metadata = floor["modules"][name]
        build = fr.get("builds", {}).get(name, {})
        require(build.get("exit_code") == 0 and
                fr.get("kernel_replays", {}).get(name, {}).get("exit_code") == 0,
                f"Periodic-census module lacks successful build/kernel replay: {name}")
        require(fr.get("declarations", {}).get(name) and all(
                set(item["axioms"]) <= ALLOWED_AXIOMS
                for item in fr["declarations"][name].values()),
                f"Periodic-census module lacks a valid all-constant audit: {name}")
        source_sha, object_sha = sha(source), sha(obj)
        require(source_sha == metadata["source_sha256"] == build.get("source_sha256"),
                f"Periodic-census source mismatch: {name}")
        require(source_imports(source) == metadata["imports"] ==
                fr["source_inventories"][name]["imports"],
                f"Periodic-census source/import mismatch: {name}")
        require(object_sha == build.get("object_sha256"),
                f"Periodic-census object mismatch: {name}")
        evidence["floor"][name] = {"source_sha256": source_sha,
            "object_sha256": object_sha, "closure_fingerprint": fingerprints[name]}
    for name, item in fr["authenticated_native_dependencies"].items():
        if name in evidence["native"]:
            current = evidence["native"][name]
            require(item["source_sha256"] == current["source_sha256"] and
                    item["object_sha256"] == current["object_sha256"] and
                    item["dependency_fingerprint"] == current["native_dependency_fingerprint"],
                    f"Periodic-census/native cached provenance mismatch: {name}")
    return evidence, {"native": native_record_sha, "floor": floor_record_sha}


def authenticate_toolchain(args, package):
    pins = package["toolchain"]
    lean = args.lean_bin / "lean"
    require(run_checked([str(lean), "--version"]) == pins["lean_version"],
            "Lean version/commit mismatch")
    require((args.lean_bin / "leanchecker").is_file(), "leanchecker is required")
    require(sha(args.mathlib / "lake-manifest.json") == pins["mathlib_lake_manifest_sha256"],
            "Mathlib package manifest mismatch")
    repositories = [("Mathlib", args.mathlib, pins["mathlib_revision"])]
    repositories += [(name, args.mathlib / ".lake/packages" / name, revision)
                     for name, revision in pins["dependency_revisions"].items()]
    for name, path, revision in repositories:
        require(run_checked(["git", "rev-parse", "HEAD"], cwd=path) == revision,
                f"Dependency source revision mismatch: {name}")
        require(not run_checked(["git", "status", "--porcelain", "--untracked-files=no"], cwd=path),
                f"Dependency tracked sources are dirty: {name}")
    prefix = Path(run_checked([str(lean), "--print-prefix"]))
    libraries = [args.mathlib / ".lake/packages" / name / ".lake/build/lib/lean"
                 for name in pins["dependency_revisions"]]
    libraries += [args.mathlib / ".lake/build/lib/lean", prefix / "lib/lean"]
    cli_cache = args.mathlib / ".lake/packages/Cli/.lake/build/lib/lean"
    require(all(path.is_dir() for path in libraries if path != cli_cache),
            "Built pinned library caches are required")
    # Cli is a pinned Lake dependency, but this application closure imports no Cli module.
    return [path for path in libraries if path.is_dir()]


def audit_source(modules):
    wanted = ", ".join(json.dumps(name) for name in modules)
    return "".join(f"import {name}\n" for name in modules) + f"""import Lean

open Lean Elab Command in
run_cmd do
  let wanted : Array String := #[{wanted}]
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{{mod.toString}}|{{name.toString}}|{{visibility}}|{{names}}"
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-package-only", action="store_true")
    parser.add_argument("--native-bundle", type=Path)
    parser.add_argument("--native-build", type=Path)
    parser.add_argument("--floor-bundle", type=Path)
    parser.add_argument("--floor-build", type=Path)
    parser.add_argument("--floor-record-sha256",
                        help="Explicit pin for an independently verified periodic-census replay.")
    parser.add_argument("--native-record-sha256",
                        help="Explicit pin for a separately verified native replay record; "
                             "defaults to the recorded reference replay pin.")
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--output", type=Path,
                        help="A new output directory; default is a fresh system temporary directory.")
    args = parser.parse_args()
    package, inventories = validate_package()
    manifest_sha = sha(ROOT / "bundle-manifest.json")
    print(f"Package integrity PASS: {len(package['modules'])} frozen sources", flush=True)
    if args.verify_package_only:
        return
    for flag in ["native_bundle", "native_build", "floor_bundle", "floor_build", "lean_bin", "mathlib"]:
        require(getattr(args, flag) is not None, f"--{flag.replace('_', '-')} is required")
        setattr(args, flag, getattr(args, flag).resolve())
    before, record_pins = authenticate_dependencies(args, package)
    libraries = authenticate_toolchain(args, package)
    print(f"Authenticated {len(before['native'])} native and {len(before['floor'])} periodic-census source/object pairs", flush=True)
    if args.output:
        output = args.output.resolve()
        require(not output.exists(), "Output must be a new directory; existing builds are never reused")
        output.mkdir(parents=True)
    else:
        output = Path(tempfile.mkdtemp(prefix="collatz-cylinder-energy-"))
    source_dir, module_dir = output / "source", output / "modules"
    log_dir, native_dir = output / "logs", output / "authenticated-native"
    floor_dir = output / "authenticated-periodic-census"
    for directory in [source_dir, module_dir, log_dir, native_dir, floor_dir]:
        directory.mkdir()
    for name in package["module_order"]:
        shutil.copyfile(ROOT / "source" / (name + ".lean"), source_dir / (name + ".lean"))
    # Expose only the authenticated upstream objects needed by the endpoint closure.
    for group, directory, build in [("native", native_dir, args.native_build),
                                    ("floor", floor_dir, args.floor_build)]:
        for name in before[group]:
            relative = Path(name.replace(".", "/") + ".olean")
            destination = directory / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.symlink_to(build / "modules" / relative)
    env = os.environ.copy()
    for key in ["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"]:
        env.pop(key, None)
    env["PATH"] = str(args.lean_bin) + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = os.pathsep.join(map(str, [module_dir, floor_dir, native_dir] + libraries))
    builds, kernels = {}, {}

    def compile_module(name, *, generated=False):
        source, obj = source_dir / (name + ".lean"), module_dir / (name + ".olean")
        require(not obj.exists(), f"Fresh object unexpectedly present: {name}")
        if not generated:
            require(sha(source) == package["modules"][name]["source_sha256"],
                    f"Fresh source copy changed before compilation: {name}")
        start = time.monotonic()
        result = subprocess.run([str(args.lean_bin / "lean"), "-j1", "--root=" + str(source_dir),
                                 "-o", str(obj), str(source)], cwd=source_dir, env=env,
                                capture_output=True, text=True)
        text = result.stdout + result.stderr
        log = log_dir / (name + ".log")
        log.write_text(text)
        require(result.returncode == 0 and obj.is_file() and obj.stat().st_size > 0,
                f"Compilation failed for {name}:\n{text}")
        require("sorryAx" not in text and "error:" not in text,
                f"Proof error/bypass in {name}:\n{text}")
        warnings = re.findall(r"^.*warning:.*$", text, re.M)
        require(not warnings, f"Unexpected compiler warning in {name}:\n{text}")
        builds[name] = {"source_sha256": sha(source), "object_sha256": sha(obj),
                        "log_sha256": sha(log), "exit_code": result.returncode,
                        "seconds": time.monotonic() - start, "warnings": warnings,
                        "generated_audit_harness": generated}
        print(f"{name}: fresh compilation PASS", flush=True)
        return text

    def kernel_check(name):
        start = time.monotonic()
        result = subprocess.run([str(args.lean_bin / "leanchecker"), name],
                                cwd=source_dir, env=env, capture_output=True, text=True)
        log = log_dir / (name + ".kernel.log")
        log.write_text(result.stdout + result.stderr)
        require(result.returncode == 0, f"Kernel replay failed for {name}:\n{log.read_text()}")
        kernels[name] = {"exit_code": result.returncode, "log_sha256": sha(log),
                         "seconds": time.monotonic() - start}
        print(f"{name}: kernel replay PASS", flush=True)

    for name in package["module_order"]:
        compile_module(name)
        kernel_check(name)
    audit_name = "CylinderEnergyAllDeclarationsAudit"
    (source_dir / (audit_name + ".lean")).write_text(audit_source(package["module_order"]))
    audit_log = compile_module(audit_name, generated=True)
    kernel_check(audit_name)
    declarations = {name: {} for name in package["module_order"]}
    for module, name, visibility, values in re.findall(
            r"^AUDIT_AXIOMS\|([^|\n]+)\|([^|\n]+)\|(public|private)\|([^\n]*)$", audit_log, re.M):
        require(module in declarations and name not in declarations[module],
                "Unexpected or duplicated declaration audit entry")
        axioms = [value for value in values.split(",") if value]
        require(set(axioms) <= ALLOWED_AXIOMS, f"Nonstandard axiom in {name}: {axioms}")
        declarations[module][name] = {"visibility": visibility, "axioms": axioms}
    for module, inventory in inventories.items():
        require(declarations[module], f"No declarations audited for {module}")
        named = {item["name"] for item in inventory["named_declarations"]}
        require(named <= set(declarations[module]),
                f"Named source declarations missing from compiled audit: {module}")
        for item in inventory["private_declarations"]:
            require(any(name.endswith("." + item["name"]) and value["visibility"] == "private"
                        for name, value in declarations[module].items()),
                    f"Private source declaration missing from audit: {module}.{item['name']}")
    after, final_record_pins = authenticate_dependencies(args, package)
    authenticate_toolchain(args, package)
    require(before == after and record_pins == final_record_pins,
            "Upstream dependencies changed during the replay")
    require(sha(ROOT / "bundle-manifest.json") == manifest_sha, "Bundle manifest changed during replay")
    validate_package()
    for name, build in builds.items():
        require(sha(source_dir / (name + ".lean")) == build["source_sha256"],
                f"Fresh source copy changed during replay: {name}")
        require(sha(module_dir / (name + ".olean")) == build["object_sha256"],
                f"Fresh object changed during replay: {name}")
        require(sha(log_dir / (name + ".log")) == build["log_sha256"] and
                sha(log_dir / (name + ".kernel.log")) == kernels[name]["log_sha256"],
                f"Fresh log changed during replay: {name}")
    count = sum(map(len, declarations.values()))
    private_count = sum(item["visibility"] == "private"
                        for module in declarations.values() for item in module.values())
    record = {
        "status": "PASS", "bundle_manifest_sha256": manifest_sha,
        "scope": "All 17 bundled application modules and their generated whole-module audit "
                 "were freshly compiled and individually kernel-replayed. All application constants, "
                 "including private and generated constants, were audited. Required periodic-census "
                 "(40) and native (1566) objects were reused after pinned source/object/import and "
                 "dependency-fingerprint authentication before and after. Pinned Mathlib/Lean caches "
                 "were reused; this is not a fresh rebuild of the entire upstream closure.",
        "native_manifest_sha256": package["native_base"]["manifest_sha256"],
        "periodic_census_manifest_sha256": package["periodic_census_base"]["manifest_sha256"],
        "dependency_record_pins": record_pins, "toolchain": package["toolchain"],
        "paths": {"native_bundle": str(args.native_bundle), "native_build": str(args.native_build),
                  "floor_bundle": str(args.floor_bundle), "floor_build": str(args.floor_build),
                  "lean_bin": str(args.lean_bin), "mathlib": str(args.mathlib), "output": str(output)},
        "authenticated_dependencies": before, "module_order": package["module_order"],
        "builds": builds, "kernel_replays": kernels, "declarations": declarations,
        "audited_constant_count": count, "audited_private_constant_count": private_count,
        "source_inventories": inventories,
    }
    (output / "replay-record.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"PASS: {len(package['modules'])} source modules; {count} constants ({private_count} private); "
          f"{len(before['floor'])} periodic-census and {len(before['native'])} native modules reused", flush=True)
    print(f"Replay record: {output / 'replay-record.json'}", flush=True)


if __name__ == "__main__":
    main()
