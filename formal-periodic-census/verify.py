#!/usr/bin/env python3
"""Freshly compile and kernel-check the additive periodic-census extension."""
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


def native_closure(package, native_manifest):
    local = set(package["modules"])
    native = set(native_manifest["source_hashes"])
    require(not local & native, "Extension module shadows a native base module")
    closure = set()

    def visit(name):
        if name in local or name in closure:
            return
        if name not in native:
            require(name.split(".")[0] in LIBRARY_ROOTS,
                    f"Import is outside authenticated sources and pinned libraries: {name}")
            return
        closure.add(name)
        require(name in native_manifest["dependencies"], f"Missing native imports: {name}")
        for dependency in native_manifest["dependencies"][name]:
            visit(dependency)

    for module in package["modules"].values():
        for dependency in module["imports"]:
            visit(dependency)
    require(sorted(closure) == package["required_native_modules"],
            "Required native source closure differs from the frozen inventory")
    return sorted(closure)


def authenticate_native(args, package):
    pins = package["native_base"]
    manifest_path = args.native_bundle / "replay-manifest.json"
    record_path = args.native_build / "replay-record.json"
    require(sha(manifest_path) == pins["manifest_sha256"], "Native manifest pin mismatch")
    expected_record = args.native_record_sha256 or pins["reference_replay_record_sha256"]
    require(re.fullmatch(r"[0-9a-f]{64}", expected_record) is not None,
            "Native replay-record pin must be a lowercase SHA-256 digest")
    require(sha(record_path) == expected_record, "Native replay-record pin mismatch")
    manifest, record = read_json(manifest_path), read_json(record_path)
    require(record.get("status") == "PASS", "Native replay record is not PASS")
    require(record.get("manifest_sha256") == pins["manifest_sha256"],
            "Native replay record belongs to a different source manifest")
    for key in ["lean_version", "mathlib_revision", "mathlib_lake_manifest_sha256",
                "dependency_revisions"]:
        require(record.get(key) == manifest[key] == package["toolchain"][key],
                f"Native/toolchain provenance mismatch: {key}")
    require(record.get("axioms") and all(set(xs) <= ALLOWED_AXIOMS
            for xs in record["axioms"].values()), "Native record has unexpected axioms")
    evidence = {}
    for name in native_closure(package, manifest):
        relative = name.replace(".", "/")
        source = args.native_bundle / "source" / (relative + ".lean")
        obj = args.native_build / "modules" / (relative + ".olean")
        require(name in record.get("builds", {}), f"Native replay omitted required module: {name}")
        require(record["builds"][name].get("exit_code") == 0,
                f"Native required module has no successful build: {name}")
        source_sha, object_sha = sha(source), sha(obj)
        require(source_sha == manifest["source_hashes"][name]
                == record["source_hashes"].get(name), f"Native source mismatch: {name}")
        fingerprint = manifest["dependency_fingerprints"][name]
        require(fingerprint == record["dependency_fingerprints"].get(name),
                f"Native dependency fingerprint mismatch: {name}")
        require(object_sha == record["builds"][name]["olean_sha256"],
                f"Native object mismatch: {name}")
        evidence[name] = {"source_sha256": source_sha, "object_sha256": object_sha,
                          "dependency_fingerprint": fingerprint}
    return evidence, expected_record


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
    for flag in ["native_bundle", "native_build", "lean_bin", "mathlib"]:
        require(getattr(args, flag) is not None, f"--{flag.replace('_', '-')} is required")
        setattr(args, flag, getattr(args, flag).resolve())
    before, record_sha = authenticate_native(args, package)
    libraries = authenticate_toolchain(args, package)
    print(f"Authenticated {len(before)} required native source/object pairs", flush=True)
    if args.output:
        output = args.output.resolve()
        require(not output.exists(), "Output must be a new directory; existing builds are never reused")
        output.mkdir(parents=True)
    else:
        output = Path(tempfile.mkdtemp(prefix="collatz-periodic-census-"))
    source_dir, module_dir = output / "source", output / "modules"
    log_dir, native_dir = output / "logs", output / "authenticated-native"
    for directory in [source_dir, module_dir, log_dir, native_dir]:
        directory.mkdir()
    for name in package["module_order"]:
        shutil.copyfile(ROOT / "source" / (name + ".lean"), source_dir / (name + ".lean"))
    # Only authenticated native objects are exposed on the import path.
    for name in before:
        relative = Path(name.replace(".", "/") + ".olean")
        destination = native_dir / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.symlink_to(args.native_build / "modules" / relative)
    env = os.environ.copy()
    for key in ["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"]:
        env.pop(key, None)
    env["PATH"] = str(args.lean_bin) + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = os.pathsep.join(map(str, [module_dir, native_dir] + libraries))
    builds, kernels = {}, {}

    def compile_module(name, *, generated=False):
        source, obj = source_dir / (name + ".lean"), module_dir / (name + ".olean")
        require(not obj.exists(), f"Fresh object unexpectedly present: {name}")
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
        if warnings:
            require(name == "Tejonas" and all("deprecated" in line for line in warnings),
                    f"Unexpected compiler warning in {name}:\n{text}")
        builds[name] = {"source_sha256": sha(source), "object_sha256": sha(obj),
                        "log_sha256": sha(log), "exit_code": result.returncode,
                        "seconds": time.monotonic() - start, "warnings": warnings,
                        "generated_audit_harness": generated}
        print(f"{name}: fresh compilation PASS", flush=True)
        return text

    for name in package["module_order"]:
        compile_module(name)
        start = time.monotonic()
        result = subprocess.run([str(args.lean_bin / "leanchecker"), name],
                                cwd=source_dir, env=env, capture_output=True, text=True)
        log = log_dir / (name + ".kernel.log")
        log.write_text(result.stdout + result.stderr)
        require(result.returncode == 0, f"Kernel replay failed for {name}:\n{log.read_text()}")
        kernels[name] = {"exit_code": result.returncode, "log_sha256": sha(log),
                         "seconds": time.monotonic() - start}
        print(f"{name}: kernel replay PASS", flush=True)
    audit_name = "PeriodicCensusAllDeclarationsAudit"
    (source_dir / (audit_name + ".lean")).write_text(audit_source(package["module_order"]))
    audit_log = compile_module(audit_name, generated=True)
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
    after, final_record_sha = authenticate_native(args, package)
    authenticate_toolchain(args, package)
    require(before == after and record_sha == final_record_sha,
            "Native dependencies changed during the replay")
    require(sha(ROOT / "bundle-manifest.json") == manifest_sha, "Bundle manifest changed during replay")
    validate_package()
    for name in package["module_order"]:
        require(sha(source_dir / (name + ".lean")) == package["modules"][name]["source_sha256"],
                f"Fresh source copy changed during replay: {name}")
        require(sha(module_dir / (name + ".olean")) == builds[name]["object_sha256"],
                f"Fresh object changed during replay: {name}")
    count = sum(map(len, declarations.values()))
    private_count = sum(item["visibility"] == "private"
                        for module in declarations.values() for item in module.values())
    record = {
        "status": "PASS", "bundle_manifest_sha256": manifest_sha,
        "scope": "All 51 bundled application modules freshly compiled and individually kernel-replayed; "
                 "all their compiled constants, including private and generated constants, audited. "
                 "Required native objects reused after pinned source/object/fingerprint authentication. "
                 "Pinned Mathlib/Lean caches reused. No fresh rebuild of the entire native or library closure.",
        "native_manifest_sha256": package["native_base"]["manifest_sha256"],
        "native_replay_record_sha256": record_sha, "toolchain": package["toolchain"],
        "paths": {"native_bundle": str(args.native_bundle), "native_build": str(args.native_build),
                  "lean_bin": str(args.lean_bin), "mathlib": str(args.mathlib), "output": str(output)},
        "authenticated_native_dependencies": before, "module_order": package["module_order"],
        "builds": builds, "kernel_replays": kernels, "declarations": declarations,
        "audited_constant_count": count, "audited_private_constant_count": private_count,
        "source_inventories": inventories,
    }
    (output / "replay-record.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"PASS: 51 source modules; {count} constants ({private_count} private); "
          f"{len(before)} authenticated reused native modules", flush=True)
    print(f"Replay record: {output / 'replay-record.json'}", flush=True)


if __name__ == "__main__":
    main()
