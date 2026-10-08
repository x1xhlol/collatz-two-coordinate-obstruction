#!/usr/bin/env python3
"""Replay every bundled Lean source using only freshly built bundled objects."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_SHA256 = "210db3b96c3c5a0c2071cd0d468ff852554ea4bd9e38efba40c183764af0a538"
AUDIT = "GrowingDeficitCompleteAudit"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OBJECT_ENDINGS = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig", ".so")
ORIGINAL_RECOVERY_FILES = {
    "replay.py": "dd446a3a3878a0fbb9fb24707aae0bcfaa5af1448dbd234b430f082d69cd9b24",
    "progress.json": "d81a3d311250abb6f640c524a2671c6b3b94afab9cf28503256f26ffb8c3a0f3",
    "GrowingDeficitCompleteAudit.lean": "184b48a9cfa1aa6ac6e1bbafbb994cbabca682d9f5786ff8c20eec4c42cb886b",
    "GrowingDeficitCompleteAudit.compile.log": "fdb6a308ce08f4a06e0daa5c415a54eab25e0c02a131080d069b38ec645af336",
    "source-manifest.json": MANIFEST_SHA256,
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def rel(module, extension=".olean"):
    require(bool(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", module)),
            "Invalid module name: " + module)
    return Path(*module.split(".")).with_suffix(extension)


def safe_path(base, name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in name,
            "Nonportable path: " + name)
    result = base / name
    require(result.resolve().is_relative_to(base.resolve()), "Path escapes its root: " + name)
    return result


def clean_env(toolchain, roots=()):
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("LEAN_", "ELAN_")) and key not in {"LD_PRELOAD", "LD_LIBRARY_PATH"}}
    env.update(PATH=str(toolchain / "bin") + ":/usr/bin:/bin", LEAN_NUM_THREADS="1")
    if roots:
        env["LEAN_PATH"] = ":".join(map(str, roots))
    return env


def symbolic(path, toolchain):
    path = Path(path).absolute()
    if path.is_relative_to(ROOT):
        return "BUNDLE/" + path.relative_to(ROOT).as_posix()
    require(path.is_relative_to(toolchain), "Unapproved absolute path")
    return "TOOLCHAIN/" + path.relative_to(toolchain).as_posix()


def unsymbolic(value, toolchain):
    if value.startswith("BUNDLE/"):
        return safe_path(ROOT, value.removeprefix("BUNDLE/"))
    require(value.startswith("TOOLCHAIN/"), "Unapproved symbolic path")
    return safe_path(toolchain, value.removeprefix("TOOLCHAIN/"))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def input_state(toolchain):
    manifest_path = ROOT / "source-manifest.json"
    require(sha(manifest_path) == MANIFEST_SHA256, "Changed or unfrozen source manifest")
    manifest = json.loads(manifest_path.read_text())
    require(manifest["status"] == "FROZEN", "Source inputs are not frozen")
    pinned = manifest["pinned_files"]
    for name, expected in pinned.items():
        require(sha(safe_path(ROOT, name)) == expected, "Changed bundled input: " + name)
    spec = importlib.util.spec_from_file_location("source_inventory", ROOT / "scripts/source_inventory.py")
    inventory_helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inventory_helper)
    modules = manifest["modules_in_topological_order"]
    require(len(modules) == len(set(modules)) == 357 and set(modules) == set(manifest["modules"]),
            "Wrong source closure")
    actual_files = {path.relative_to(ROOT).as_posix() for path in (ROOT / "source").rglob("*.lean")}
    require(actual_files == {entry["source"] for entry in manifest["modules"].values()}, "Source set changed")
    inventories, available = {}, set()
    for module in modules:
        entry = manifest["modules"][module]
        require(entry["source"] == "source/" + rel(module, ".lean").as_posix(), "Source/module mismatch")
        path = safe_path(ROOT, entry["source"])
        require(not path.is_symlink() and sha(path) == entry["sha256"], "Changed source: " + module)
        inventory = inventory_helper.source_inventory(path, module)
        require(inventory == entry["inventory"], "Changed source inventory: " + module)
        clean = inventory_helper.scrub_lean(path.read_text())
        require(not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|trustLevel)\b", clean),
                "Forbidden source bypass token: " + module)
        require(inventory["imports"] == entry["imports"], "Import inventory mismatch")
        for imported in inventory["imports"]:
            require(imported not in manifest["modules"] or imported in available, "Non-topological source order")
        inventories[module] = inventory
        available.add(module)
    deps = json.loads((ROOT / "dependency-pins.json").read_text())
    require((ROOT / "lean-toolchain").read_text().strip() == deps["lean_toolchain"], "Toolchain pin mismatch")
    for name, expected in deps["official_tool_runtime_sha256"].items():
        require(sha(safe_path(toolchain, name)) == expected, "Changed official tool/runtime: " + name)
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], env=clean_env(toolchain), text=True).strip()
    require(version == deps["lean_version"], "Unexpected Lean version")
    lake = json.loads((ROOT / "lake-manifest.json").read_text())
    require(lake["packages"] == deps["packages"] and len(lake["packages"]) == 9, "Package manifest mismatch")
    libraries, package_state = [], {}
    for package in deps["packages"]:
        path = safe_path(ROOT, ".lake/packages/" + package["name"])
        require(path.is_dir() and not path.is_symlink(), "Missing or linked package: " + package["name"])
        require((path / ".git").is_dir(), "Package must be a standalone checkout")
        commit = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        require(commit == package["rev"] and not dirty, "Changed package checkout: " + package["name"])
        library = safe_path(path, ".lake/build/lib/lean")
        require(library.is_dir(), "Missing external library objects: " + package["name"])
        libraries.append(library)
        package_state[package["name"]] = {"revision": commit, "tracked_tree_clean": True}
    libraries.append(safe_path(toolchain, "lib/lean"))
    require(len({str(p.resolve()) for p in libraries}) == len(libraries), "Duplicate external roots")
    object_hashes = {}
    for library in libraries:
        for path in sorted(library.rglob("*")):
            if path.is_file() and str(path).endswith(OBJECT_ENDINGS):
                require(not path.is_symlink() and path.resolve().is_relative_to(library.resolve()),
                        "Linked external object")
                object_hashes[symbolic(path, toolchain)] = sha(path)
    require(object_hashes, "Empty external object inventory")
    return manifest, inventories, libraries, {"lean_version": version, "packages": package_state,
        "external_object_sha256": object_hashes, "official_tool_runtime_sha256": deps["official_tool_runtime_sha256"]}


def resolve(module, roots):
    for root in roots:
        candidate = root / rel(module)
        if candidate.is_file():
            require(not candidate.is_symlink() and candidate.resolve().is_relative_to(root.resolve()),
                    "Linked or escaped import: " + module)
            return candidate
    raise RuntimeError("Unresolved import: " + module)


def audit_source(modules):
    imports = "\n".join("import " + module for module in modules)
    wanted = ", ".join('"' + module + '"' for module in modules)
    return f'''{imports}
import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if [{wanted}].contains mod.toString then
      unless env.header.modules[i]!.importAll do
        throwError m!"Missing import-all visibility for {{mod}}"
      let constants := env.header.moduleData[i]!.constNames
      logInfo m!"AUDIT_MODULE|{{mod.toString}}|{{constants.size}}"
      for name in constants do
        unless ((env.setExporting false).checked.get.find? name).isSome do
          throwError m!"Missing checked constant {{name}} in {{mod}}"
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{{mod.toString}}|{{name.toString}}|{{visibility}}|{{names}}"
'''


def parse_audit(log, modules, inventories):
    counts, rows = {}, {}
    for module, value in re.findall(r"^AUDIT_MODULE\|([^|\n]+)\|(\d+)$", log, re.M):
        require(module in modules and module not in counts, "Invalid audit module marker")
        counts[module] = int(value)
    for module, name, visibility, values in re.findall(
            r"^AUDIT_AXIOMS\|([^|\n]+)\|([^|\n]+)\|(public|private)\|([^\n]*)$", log, re.M):
        key, axioms = module + "|" + name, [v for v in values.split(",") if v]
        require(module in modules and key not in rows and set(axioms) <= ALLOWED, "Unacceptable axiom audit row")
        rows[key] = {"module": module, "name": name, "visibility": visibility, "axioms": axioms}
    require(set(counts) == set(modules), "Missing audited module")
    for module in modules:
        require(sum(row["module"] == module for row in rows.values()) == counts[module], "Incomplete constant enumeration")
        for declaration in inventories[module]["named_declarations"]:
            require(module + "|" + declaration["name"] in rows, "Unaudited named declaration: " + declaration["name"])
        for declaration in inventories[module]["private_declarations"]:
            require(any(row["module"] == module and row["visibility"] == "private" and
                        row["name"].endswith("." + declaration["name"]) for row in rows.values()),
                    "Unaudited private declaration: " + declaration["name"])
    return counts, rows


def command_arguments(module, stage, out, options, toolchain):
    if stage == "compile":
        flags = ["-D" + key + "=" + (str(value).lower() if isinstance(value, bool) else str(value))
                 for key, value in options.items()]
        return [str(toolchain / "bin/lean"), "-j1", *flags, "--root=" + str(out / "source"),
                str(out / "source" / rel(module, ".lean")), "-o", str(out / "modules" / rel(module))]
    return [str(toolchain / "bin/leanchecker"), "--verbose", module]


def symbolic_command(arguments, toolchain):
    return ["--root=" + symbolic(arg.removeprefix("--root="), toolchain) if arg.startswith("--root=")
            else symbolic(arg, toolchain) if arg.startswith("/") else arg for arg in arguments]


def original_recovery_prefix(out, toolchain):
    original = out / "recovery/original"
    actual_files = {p.name for p in original.iterdir()}
    require(actual_files == set(ORIGINAL_RECOVERY_FILES), "Changed original recovery file set")
    identities = {}
    for name, expected in ORIGINAL_RECOVERY_FILES.items():
        path = original / name
        require(not path.is_symlink() and sha(path) == expected, "Changed original recovery evidence: " + name)
        identities[symbolic(path, toolchain)] = expected
    progress = json.loads((original / "progress.json").read_text())
    require(sha(out / "progress.json") == ORIGINAL_RECOVERY_FILES["progress.json"],
            "Original canonical progress was changed")
    require(progress["status"] == "RUNNING" and len(progress["commands"]) == 715 and
            len(progress["results"]) == 357, "Wrong interrupted-run prefix")
    require(all(command["exit_code"] == 0 for command in progress["commands"][:-1]),
            "Original proof prefix was unsuccessful")
    failed = progress["commands"][-1]
    require(failed["module"] == AUDIT and failed["stage"] == "compile" and failed["exit_code"] == 1 and
            failed["log_sha256"] == ORIGINAL_RECOVERY_FILES[AUDIT + ".compile.log"], "Wrong preserved failure")
    require(failed["arguments"] == symbolic_command(command_arguments(AUDIT, "compile", out,
            {"warningAsError": True}, toolchain), toolchain) and
            failed["cwd"] == symbolic(out / "source", toolchain) and
            failed["log"] == symbolic(out / "logs" / (AUDIT + ".compile.log"), toolchain),
            "Changed original failed command")
    return progress, identities


def verify_recovery(record, out, toolchain, manifest, inventories, state, script_pin):
    recovery = record.get("recovery")
    require((recovery is not None) == (out / "recovery").exists(), "Recovery directory/record mismatch")
    if recovery is None:
        return 0
    require(recovery["status"] == "PASS" and recovery["kind"] == "audit_harness_recovery_with_complete_kernel_recheck",
            "Unknown recovery evidence")
    require(recovery["original_external_inventory_preserved"] is False and
            recovery["dependency_inventory_scope"] == "persisted before and revalidated after recovery only",
            "Incorrect original dependency-state claim")
    progress, identities = original_recovery_prefix(out, toolchain)
    require(recovery["original_files"] == identities and recovery["original_failed_command"] == progress["commands"][-1],
            "Changed original evidence linkage")
    require(record["commands"][:714] == progress["commands"][:714] and
            {module: record["results"][module] for module in manifest["modules"]} == progress["results"],
            "Recovered proof prefix changed")
    require(recovery["original_driver_sha256"] == ORIGINAL_RECOVERY_FILES["replay.py"] and
            recovery["corrected_driver_sha256"] == script_pin, "Wrong recovery driver lineage")
    baseline_path = out / "recovery/input-state.json"
    require(recovery["input_state"] == symbolic(baseline_path, toolchain) and
            sha(baseline_path) == recovery["input_state_sha256"], "Changed persisted recovery baseline")
    baseline = json.loads(baseline_path.read_text())
    require(baseline["source_manifest_sha256"] == MANIFEST_SHA256 and baseline["corrected_driver_sha256"] == script_pin and
            baseline["original_progress_sha256"] == ORIGINAL_RECOVERY_FILES["progress.json"] and
            baseline["dependency_state"] == state and baseline["source_inventory"] == inventories,
            "Recovery baseline differs from authenticated inputs")
    executor = out / "recovery/recover_replay.py"
    require(recovery["executor"] == symbolic(executor, toolchain) and sha(executor) == recovery["executor_sha256"] and
            baseline["executor_sha256"] == recovery["executor_sha256"], "Changed recovery executor")
    modules, commands = manifest["modules_in_topological_order"], recovery["kernel_commands"]
    require(len(commands) == len(modules) == 357 and recovery["kernel_workers"] == 3,
            "Incomplete recovery kernel scope")
    logs = out / "recovery/kernel-logs"
    require({p.name for p in logs.iterdir()} == {module + ".kernel.log" for module in modules},
            "Changed recovery log set")
    for module, command in zip(modules, commands):
        log = logs / (module + ".kernel.log")
        require(command["module"] == module and command["stage"] == "kernel" and command["exit_code"] == 0 and
                command["arguments"] == symbolic_command(command_arguments(module, "kernel", out, {}, toolchain), toolchain) and
                command["cwd"] == symbolic(out / "source", toolchain), "Changed recovery kernel command")
        require(command["log"] == symbolic(log, toolchain) and command["log_sha256"] == sha(log) and
                not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]),
                "Changed or unsuccessful recovery kernel log")
        require("replaying " + module + "\n" in log.read_text(), "Missing recovery kernel target marker")
    require(recovery["successful_command_count"] == len(record["commands"]) + len(commands) == 1073 and
            recovery["failed_command_count"] == 1, "Wrong recovery command accounting")
    kernel_progress = json.loads((out / "recovery/kernel-progress.json").read_text())
    require(kernel_progress == {"status": "PASS", "commands": commands}, "Changed completed recovery progress")
    expected_files = {"input-state.json", "recover_replay.py", "kernel-progress.json"}
    expected_files.update("original/" + name for name in ORIGINAL_RECOVERY_FILES)
    expected_files.update("kernel-logs/" + module + ".kernel.log" for module in modules)
    files = {p.relative_to(out / "recovery").as_posix(): p for p in (out / "recovery").rglob("*") if p.is_file()}
    require(set(files) == expected_files and
            {symbolic(path, toolchain): sha(path) for path in files.values()} == recovery["evidence_files"],
            "Changed recovery artifact set or hashes")
    return len(commands)


def verify_record(out, toolchain, manifest, inventories, libraries, state, script_pin):
    record = json.loads((out / "replay-record.json").read_text())
    modules = manifest["modules_in_topological_order"]
    require(record["status"] == "PASS" and record["modules"] == modules and record["audit_module"] == AUDIT,
            "Invalid replay scope")
    require(record["source_manifest_sha256"] == MANIFEST_SHA256 and record["script_sha256"] == script_pin,
            "Replay input identity changed")
    require(record["dependency_state"] == state and record["source_inventory"] == inventories, "Replay dependencies changed")
    roots = [out / "modules", *libraries]
    require(record["lean_path"] == [symbolic(root, toolchain) for root in roots], "Search path changed")
    expected_units = [*modules, AUDIT]
    require(not any(path.is_symlink() for path in out.rglob("*")), "Linked replay artifact")
    require({path.relative_to(out / "modules") for path in (out / "modules").rglob("*.olean")} ==
            {rel(module) for module in expected_units}, "Unexpected compiled module set")
    require({path.relative_to(out / "source") for path in (out / "source").rglob("*.lean")} ==
            {rel(module, ".lean") for module in expected_units}, "Unexpected replay source set")
    require(set(record["results"]) == set(expected_units) and len(record["commands"]) == 2 * len(expected_units),
            "Incomplete replay commands")
    require((out / "source" / rel(AUDIT, ".lean")).read_text() == audit_source(modules), "Audit source changed")
    direct = {}
    for index, module in enumerate(expected_units):
        result = record["results"][module]
        source, obj = out / "source" / rel(module, ".lean"), out / "modules" / rel(module)
        require(result["source"] == symbolic(source, toolchain) and result["object"] == symbolic(obj, toolchain),
                "Unexpected output path")
        require(sha(source) == result["source_sha256"] and sha(obj) == result["object_sha256"], "Changed replay artifact")
        if module != AUDIT:
            require(result["source_sha256"] == manifest["modules"][module]["sha256"], "Replayed source mismatch")
        parts = {symbolic(path, toolchain): sha(path) for path in sorted(obj.parent.glob(obj.stem + ".*")) if path.is_file()}
        require(parts == result["object_parts"], "Changed output companions")
        options = manifest["modules"][module]["lean_options"] if module != AUDIT else {"warningAsError": True}
        for offset, stage in enumerate(["compile", "kernel"]):
            command = record["commands"][2 * index + offset]
            log = out / "logs" / (module + "." + stage + ".log")
            require(command["module"] == module and command["stage"] == stage and command["exit_code"] == 0,
                    "Command order or status changed")
            require(command["arguments"] == symbolic_command(command_arguments(module, stage, out, options, toolchain), toolchain)
                    and command["cwd"] == symbolic(out / "source", toolchain), "Command vector changed")
            require(command["log"] == symbolic(log, toolchain) and command["log_sha256"] == sha(log), "Changed command log")
            require(not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]), "Replay diagnostic")
        for imported in inventories.get(module, {}).get("imports", []):
            actual = resolve(imported, roots)
            if imported in manifest["modules"]:
                require(actual == out / "modules" / rel(imported), "External object shadows bundled module")
            else:
                require(symbolic(actual, toolchain) in state["external_object_sha256"], "Uninventoried external import")
            direct[module + " -> " + imported] = {"object": symbolic(actual, toolchain), "sha256": sha(actual)}
    require(direct == record["direct_import_resolutions"], "Direct import resolutions changed")
    counts, rows = parse_audit((out / "logs" / (AUDIT + ".compile.log")).read_text(), modules, inventories)
    require(counts == record["module_constant_counts"] and rows == record["declarations"], "Audit transcript changed")
    require(record["allowed_axioms"] == sorted(ALLOWED) and record["audited_constant_count"] == len(rows), "Audit count changed")
    require(record["audited_distinct_constant_name_count"] == len({row["name"] for row in rows.values()}) and
            record["audited_private_constant_count"] == sum(row["visibility"] == "private" for row in rows.values()),
            "Audit secondary counts changed")
    recovery_commands = verify_recovery(record, out, toolchain, manifest, inventories, state, script_pin)
    return {"status": "PASS", "record_sha256": sha(out / "replay-record.json"), "modules": len(modules),
            "commands": len(record["commands"]), "recovery_kernel_commands": recovery_commands,
            "successful_commands": len(record["commands"]) + recovery_commands,
            "audited_constants": len(rows), "external_objects": len(state["external_object_sha256"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", required=True, type=Path, help="Exact official Linux x86_64 Lean installation")
    parser.add_argument("--preflight", action="store_true", help="Authenticate inputs without compiling")
    parser.add_argument("--verify-only", action="store_true", help="Authenticate an existing full replay")
    args = parser.parse_args()
    require(not (args.preflight and args.verify_only), "Choose one operation")
    toolchain, out = args.toolchain.resolve(), ROOT / ".replay"
    script_pin = sha(Path(__file__))
    manifest, inventories, libraries, state = input_state(toolchain)
    if args.preflight:
        print(json.dumps({"status": "PASS", "modules": len(inventories), "external_objects": len(state["external_object_sha256"])}))
        return
    if args.verify_only:
        print(json.dumps(verify_record(out, toolchain, manifest, inventories, libraries, state, script_pin)))
        return
    require(not out.exists(), "Fresh output already exists; move it aside before a new replay")
    started = utc()
    for name in ["source", "modules", "logs"]:
        (out / name).mkdir(parents=True)
    modules = manifest["modules_in_topological_order"]
    for module in modules:
        target = out / "source" / rel(module, ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / manifest["modules"][module]["source"], target)
    (out / "source" / rel(AUDIT, ".lean")).write_text(audit_source(modules))
    roots = [out / "modules", *libraries]
    env = clean_env(toolchain, roots)
    commands, results, direct = [], {}, {}
    for module in [*modules, AUDIT]:
        source, obj = out / "source" / rel(module, ".lean"), out / "modules" / rel(module)
        obj.parent.mkdir(parents=True, exist_ok=True)
        if module != AUDIT:
            require(sha(source) == manifest["modules"][module]["sha256"], "Copied source changed")
        for imported in inventories.get(module, {}).get("imports", []):
            actual = resolve(imported, roots)
            if imported in manifest["modules"]:
                require(imported in results and actual == out / "modules" / rel(imported) and
                        sha(actual) == results[imported]["object_sha256"], "Wrong fresh import: " + imported)
            else:
                key = symbolic(actual, toolchain)
                require(key in state["external_object_sha256"] and sha(actual) == state["external_object_sha256"][key],
                        "Wrong external import: " + imported)
            direct[module + " -> " + imported] = {"object": symbolic(actual, toolchain), "sha256": sha(actual)}
        options = manifest["modules"][module]["lean_options"] if module != AUDIT else {"warningAsError": True}
        for stage in ["compile", "kernel"]:
            arguments = command_arguments(module, stage, out, options, toolchain)
            start, wall = utc(), time.monotonic()
            run = subprocess.run(arguments, cwd=out / "source", env=env, text=True, capture_output=True)
            log = out / "logs" / (module + "." + stage + ".log")
            log.write_text(run.stdout + run.stderr)
            commands.append({"module": module, "stage": stage, "arguments": symbolic_command(arguments, toolchain),
                "cwd": symbolic(out / "source", toolchain), "start_utc": start, "elapsed_seconds": time.monotonic() - wall,
                "exit_code": run.returncode, "log": symbolic(log, toolchain), "log_sha256": sha(log)})
            write_json(out / "progress.json", {"status": "RUNNING", "commands": commands, "results": results})
            require(run.returncode == 0, "Replay failed: " + log.read_text())
            require(not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]), "Replay diagnostic")
        results[module] = {"source": symbolic(source, toolchain), "object": symbolic(obj, toolchain),
            "source_sha256": sha(source), "object_sha256": sha(obj),
            "object_parts": {symbolic(path, toolchain): sha(path) for path in sorted(obj.parent.glob(obj.stem + ".*")) if path.is_file()}}
        print(json.dumps({"module": module, "status": "PASS", "completed": len(results), "total": len(modules) + 1}), flush=True)
    counts, rows = parse_audit((out / "logs" / (AUDIT + ".compile.log")).read_text(), modules, inventories)
    require(input_state(toolchain) == (manifest, inventories, libraries, state), "Inputs changed during replay")
    require(sha(Path(__file__)) == script_pin, "Replay driver changed during execution")
    record = {"status": "PASS", "started_utc": started, "finished_utc": utc(), "modules": modules, "audit_module": AUDIT,
        "commands": commands, "results": results, "source_manifest_sha256": MANIFEST_SHA256, "script_sha256": script_pin,
        "source_inventory": inventories, "dependency_state": state, "lean_path": [symbolic(root, toolchain) for root in roots],
        "direct_import_resolutions": direct, "allowed_axioms": sorted(ALLOWED), "module_constant_counts": counts,
        "declarations": rows, "audited_constant_count": len(rows), "declaration_key_format": "module|constant_name",
        "visibility_label_meaning": "private identifies Lean encoded private names; public means not encoded private and is not a complete module export-visibility classification",
        "audited_distinct_constant_name_count": len({row["name"] for row in rows.values()}),
        "audited_private_constant_count": sum(row["visibility"] == "private" for row in rows.values()),
        "scope": manifest["scope"], "external_library_policy": "Exact pinned external package source checkouts; cached Mathlib and package objects hash-inventoried, not rebuilt by this replay. Every bundled Subspace/application module is rebuilt and checked with the official leanchecker."}
    write_json(out / "replay-record.json", record)
    print(json.dumps(verify_record(out, toolchain, manifest, inventories, libraries, state, script_pin)), flush=True)


if __name__ == "__main__":
    main()
