#!/usr/bin/env python3
"""Portable fresh source replay for the canonical sharp Lp and energy endpoints."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import time

from source_inventory import source_inventory, scrub_lean

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "source-manifest.json"
AUDIT = "SharpHaarCompleteAudit"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ENDINGS = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig", ".so")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def rel(module, extension=".olean"):
    require(bool(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", module)),
            "Invalid module name")
    return Path(*module.split(".")).with_suffix(extension)


def safe_path(root, name):
    lexical = PurePosixPath(name)
    require(not lexical.is_absolute() and ".." not in lexical.parts and "\\" not in name,
            "Invalid relative path: " + name)
    path = root / name
    require(path.resolve().is_relative_to(root.resolve()), "Path escapes its root")
    return path


def clean_env(toolchain, roots=()):
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("LEAN_", "ELAN_")) and key not in {"LD_PRELOAD", "LD_LIBRARY_PATH"}}
    env.update(PATH=str(toolchain / "bin") + ":/usr/bin:/bin", LEAN_NUM_THREADS="1")
    if roots:
        env["LEAN_PATH"] = ":".join(map(str, roots))
    return env


def symbolic(path, toolchain, mathlib):
    path = Path(path).absolute()
    for prefix, root in [("TOOLCHAIN", toolchain), ("MATHLIB", mathlib), ("BUNDLE", ROOT)]:
        if path.is_relative_to(root):
            tail = path.relative_to(root).as_posix()
            return prefix if tail == "." else prefix + "/" + tail
    raise RuntimeError("Unapproved absolute path: " + str(path))


def symbolic_command(arguments, toolchain, mathlib):
    return ["--root=" + symbolic(arg.removeprefix("--root="), toolchain, mathlib) if arg.startswith("--root=")
            else symbolic(arg, toolchain, mathlib) if arg.startswith("/") else arg for arg in arguments]


def load_manifest(expected):
    require(sha(MANIFEST) == expected, "Changed or unexpected source manifest")
    manifest = json.loads(MANIFEST.read_text())
    require(manifest["status"] == "FROZEN", "Source bundle is not frozen")
    modules = manifest["modules_in_topological_order"]
    require(len(modules) == len(set(modules)) == manifest["source_count"] > 0, "Wrong source count")
    require(set(modules) == set(manifest["modules"]) and manifest["planned_successful_commands"] == 2 * (len(modules) + 1),
            "Wrong replay scope")
    reachable = set()
    def visit(module):
        require(module in manifest["modules"], "Missing endpoint or internal import")
        if module in reachable:
            return
        reachable.add(module)
        for imported in manifest["modules"][module]["imports"]:
            if imported in manifest["modules"]:
                visit(imported)
    for endpoint in manifest["endpoints"]:
        visit(endpoint)
    require(reachable == set(modules), "Source set is not the exact endpoint closure")
    actual_sources = {path.relative_to(ROOT).as_posix() for path in (ROOT / "source").rglob("*.lean")}
    require(actual_sources == {entry["source"] for entry in manifest["modules"].values()}, "Changed source file set")
    for name, expected_hash in manifest["pinned_files"].items():
        path = safe_path(ROOT, name)
        require(path.is_file() and not path.is_symlink() and sha(path) == expected_hash, "Changed bundled input: " + name)
    require(sha(ROOT / "scripts/source_inventory.py") == manifest["helper_sha256"], "Changed source inventory helper")
    return manifest


def input_state(manifest, manifest_pin, toolchain, mathlib):
    available, inventories = set(), {}
    for module in manifest["modules_in_topological_order"]:
        entry = manifest["modules"][module]
        require(entry["source"] == "source/" + rel(module, ".lean").as_posix(), "Source/module mismatch")
        source = safe_path(ROOT, entry["source"])
        require(not source.is_symlink() and sha(source) == entry["sha256"], "Changed source: " + module)
        inventory = source_inventory(source, module)
        require(inventory == entry["inventory"] and inventory["imports"] == entry["imports"], "Changed source inventory")
        require(entry["lean_options"] == {"warningAsError": True}, "Changed compilation options")
        require(not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|trustLevel)\b",
                              scrub_lean(source.read_text())), "Forbidden source bypass token: " + module)
        require(all(name not in manifest["modules"] or name in available for name in inventory["imports"]),
                "Non-topological source order")
        inventories[module] = inventory
        available.add(module)
    counts = {"named": sum(len(value["named_declarations"]) for value in inventories.values()),
              "private": sum(len(value["private_declarations"]) for value in inventories.values()),
              "anonymous_instances": sum(len(value["anonymous_instance_lines"]) for value in inventories.values())}
    require(counts == manifest["source_declaration_counts"], "Changed source declaration counts")
    deps = json.loads((ROOT / "dependency-pins.json").read_text())
    require(tuple(deps["external_object_endings"]) == ENDINGS, "Changed external inventory policy")
    require((ROOT / "lean-toolchain").read_text().strip() == deps["lean_toolchain"], "Changed toolchain pin")
    runtime = {}
    for name, expected in deps["official_tool_runtime_sha256"].items():
        path = safe_path(toolchain, name)
        require(not path.is_symlink() and sha(path) == expected, "Changed official tool/runtime: " + name)
        runtime[symbolic(path, toolchain, mathlib)] = expected
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"],
                                      env=clean_env(toolchain), text=True).strip()
    require(version == deps["lean_version"], "Unexpected Lean version")
    require(sha(mathlib / "lake-manifest.json") == deps["mathlib"]["lake_manifest_sha256"] and
            sha(mathlib / "lean-toolchain") == deps["mathlib"]["lean_toolchain_sha256"], "Changed Mathlib metadata")
    require(json.loads((mathlib / "lake-manifest.json").read_text())["packages"] == deps["packages"], "Changed package pins")
    packages, libraries = {}, []
    package_specs = [{"name": "mathlib", "rev": deps["mathlib"]["revision"]}, *deps["packages"]]
    for item in package_specs:
        path = mathlib if item["name"] == "mathlib" else mathlib / ".lake/packages" / item["name"]
        require(path.is_dir() and not path.is_symlink(), "Missing or linked external package")
        revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        require(revision == item["rev"] and not dirty, "Changed external package: " + item["name"])
        library = path / ".lake/build/lib/lean"
        if library.exists():
            require(library.is_dir() and not library.is_symlink(), "Invalid external library")
            libraries.append(library)
        packages[item["name"]] = {"revision": revision, "tracked_tree_clean": True,
                                   "library": symbolic(library, toolchain, mathlib) if library.exists() else None}
    libraries.append(toolchain / "lib/lean")
    require(len({str(path.resolve()) for path in libraries}) == len(libraries), "Duplicate external roots")
    objects = {}
    for library in libraries:
        require(library.is_dir() and not library.is_symlink(), "Missing or linked external root")
        resolved_library = library.resolve()
        for module in manifest["modules"]:
            require(not (library / rel(module)).exists(), "Internal module exists in external root")
        for path in sorted(library.rglob("*")):
            if path.is_file() and str(path).endswith(ENDINGS):
                require(not path.is_symlink() and path.resolve().is_relative_to(resolved_library), "Linked external object")
                objects[symbolic(path, toolchain, mathlib)] = sha(path)
    require(objects, "Empty external inventory")
    external_imports = {}
    for imported in manifest["external_direct_imports"]:
        path = resolve(imported, libraries)
        key = symbolic(path, toolchain, mathlib)
        require(key in objects and sha(path) == objects[key], "Uninventoried external import")
        external_imports[imported] = {"object": key, "sha256": objects[key]}
    state = {"manifest_sha256": manifest_pin, "driver_sha256": sha(Path(__file__)),
             "helper_sha256": sha(ROOT / "scripts/source_inventory.py"), "source_inventory": inventories,
             "lean_version": version, "runtime_sha256": runtime, "packages": packages,
             "external_object_sha256": objects, "external_direct_imports": external_imports,
             "external_roots": [symbolic(path, toolchain, mathlib) for path in libraries]}
    return state, libraries


def resolve(module, roots):
    for root in roots:
        path = root / rel(module)
        if path.is_file():
            require(not path.is_symlink() and path.resolve().is_relative_to(root.resolve()), "Linked import object")
            return path
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
  let env := (← getEnv).setExporting false
  let wanted : List String := [{wanted}]
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if wanted.contains mod.toString then
      unless env.header.modules[i]!.importAll do
        throwError m!"Missing import-all visibility for {{mod}}"
      let constants := env.header.moduleData[i]!.constNames
      logInfo m!"AUDIT_MODULE|{{mod.toString}}|{{constants.size}}"
      for name in constants do
        unless (env.checked.get.find? name).isSome do
          throwError m!"Missing checked constant {{name}} in {{mod}}"
        let axioms ← collectAxioms name
        let visibility := if isPrivateName name then "private" else "public"
        let names := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT_AXIOMS|{{mod.toString}}|{{name.toString}}|{{visibility}}|{{names}}"
  let owned := env.checked.get.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | none => names
    | some i =>
      if wanted.contains env.header.modules[i.toNat]!.module.toString then
        names.push (i.toNat, name)
      else names
  for (i, name) in owned do
    let mod := env.header.modules[i]!.module
    unless env.header.moduleData[i]!.constNames.contains name do
      throwError m!"Owned constant absent from module header: {{mod}} / {{name}}"
    logInfo m!"AUDIT_OWNER|{{mod.toString}}|{{name.toString}}"
'''


def parse_audit(log, plan):
    modules, counts, rows, owners = plan["modules"], {}, {}, {}
    for module, count in re.findall(r"^AUDIT_MODULE\|([^|\n]+)\|(\d+)$", log, re.M):
        require(module in modules and module not in counts, "Invalid audit module row")
        counts[module] = int(count)
    for module, name, visibility, values in re.findall(
            r"^AUDIT_AXIOMS\|([^|\n]+)\|([^|\n]+)\|(public|private)\|([^\n]*)$", log, re.M):
        key, axioms = module + "|" + name, [value for value in values.split(",") if value]
        require(module in modules and key not in rows and set(axioms) <= ALLOWED, "Unacceptable axiom row")
        rows[key] = {"module": module, "name": name, "visibility": visibility, "axioms": axioms}
    for module, name in re.findall(r"^AUDIT_OWNER\|([^|\n]+)\|([^|\n]+)$", log, re.M):
        require(module in modules and name not in owners and module + "|" + name in rows, "Invalid owner row")
        owners[name] = module
    require(set(counts) == set(modules), "Missing audited module")
    require(set(owners) == {row["name"] for row in rows.values()}, "Header/environment owner coverage differs")
    for row in rows.values():
        row["owner_module"] = owners[row["name"]]
    for module, entry in modules.items():
        require(sum(row["module"] == module for row in rows.values()) == counts[module], "Missing module constants")
        inventory = entry["inventory"]
        for declaration in inventory["named_declarations"]:
            require(module + "|" + declaration["name"] in rows, "Missing named declaration: " + declaration["name"])
        for declaration in inventory["private_declarations"]:
            require(any(row["module"] == module and row["visibility"] == "private" and
                        row["name"].endswith("." + declaration["name"]) for row in rows.values()),
                    "Missing private declaration: " + declaration["name"])
    return {"module_constant_counts": counts, "declarations": rows, "constant_owners": owners,
            "audited_constant_rows": len(rows), "audited_distinct_names": len(owners),
            "audited_private_rows": sum(row["visibility"] == "private" for row in rows.values()),
            "header_owner_mismatch_rows": sum(row["module"] != row["owner_module"] for row in rows.values()),
            "row_module_field": "module identifies the containing module header; owner_module records Lean checked-environment ownership"}


def command_arguments(out, module, stage, toolchain):
    if stage == "compile":
        return [str(toolchain / "bin/lean"), "-j1", "-DwarningAsError=true", "--root=" + str(out / "source"),
                str(out / "source" / rel(module, ".lean")), "-o", str(out / "modules" / rel(module))]
    return [str(toolchain / "bin/leanchecker"), "--verbose", module]


def import_resolutions(manifest, out, state, libraries, toolchain, mathlib):
    roots, answer = [out / "modules", *libraries], {}
    for module in [*manifest["modules_in_topological_order"], AUDIT]:
        imports = manifest["modules"][module]["imports"] if module != AUDIT else [*manifest["modules_in_topological_order"], "Lean"]
        for imported in imports:
            actual = resolve(imported, roots)
            if imported in manifest["modules"]:
                require(actual == out / "modules" / rel(imported), "Internal import is not fresh")
            else:
                require(state["external_object_sha256"].get(symbolic(actual, toolchain, mathlib)) == sha(actual),
                        "Changed external import")
            answer[module + " -> " + imported] = {"object": symbolic(actual, toolchain, mathlib), "sha256": sha(actual)}
    return answer


def verify(out, manifest, manifest_pin, state, libraries, toolchain, mathlib):
    record = json.loads((out / "replay-record.json").read_text())
    units = [*manifest["modules_in_topological_order"], AUDIT]
    require(record["status"] == "PASS" and record["modules"] == units[:-1] and record["audit_module"] == AUDIT,
            "Wrong replay record scope")
    require(record["manifest_sha256"] == manifest_pin and record["driver_sha256"] == sha(Path(__file__)), "Changed replay identities")
    require(record["allowed_axioms"] == sorted(ALLOWED) and record["scope"] == manifest["scope"], "Changed scope or axiom policy")
    roots = [out / "modules", *libraries]
    require(record["lean_path"] == [symbolic(path, toolchain, mathlib) for path in roots], "Changed search path")
    for name in ["input-state-before.json", "input-state-after.json"]:
        require(sha(out / name) == record["input_states"][name] and json.loads((out / name).read_text()) == state,
                "Changed or mismatched persisted input state")
    require(set(record["results"]) == set(units) and len(record["commands"]) == manifest["planned_successful_commands"],
            "Incomplete replay")
    require(not any(path.is_symlink() for path in out.rglob("*")), "Linked replay artifact")
    require({path.relative_to(out / "source") for path in (out / "source").rglob("*.lean")} ==
            {rel(module, ".lean") for module in units}, "Changed replay source set")
    require({path.relative_to(out / "modules") for path in (out / "modules").rglob("*.olean")} ==
            {rel(module) for module in units}, "Changed compiled module set")
    require((out / "source" / rel(AUDIT, ".lean")).read_text() == audit_source(units[:-1]), "Changed audit source")
    for index, module in enumerate(units):
        result = record["results"][module]
        source, obj = out / "source" / rel(module, ".lean"), out / "modules" / rel(module)
        require(result["source_sha256"] == sha(source) and result["object_sha256"] == sha(obj), "Changed output artifact")
        if module != AUDIT:
            require(sha(source) == manifest["modules"][module]["sha256"], "Wrong replayed source")
        parts = {symbolic(path, toolchain, mathlib): sha(path)
                 for path in sorted(obj.parent.glob(obj.stem + ".*")) if path.is_file()}
        require(parts == result["object_parts"], "Changed object companions")
        for offset, stage in enumerate(["compile", "kernel"]):
            command, log = record["commands"][2 * index + offset], out / "logs" / (module + "." + stage + ".log")
            require(command["module"] == module and command["stage"] == stage and command["exit_code"] == 0 and
                    command["arguments"] == symbolic_command(command_arguments(out, module, stage, toolchain), toolchain, mathlib) and
                    command["cwd"] == symbolic(out / "source", toolchain, mathlib) and
                    command["log"] == symbolic(log, toolchain, mathlib), "Changed command vector")
            require(command["log_sha256"] == sha(log) and
                    not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]), "Changed or failed log")
            if stage == "kernel":
                require("replaying " + module + "\n" in log.read_text(), "Missing kernel target marker")
    require(record["direct_import_resolutions"] == import_resolutions(manifest, out, state, libraries, toolchain, mathlib),
            "Changed import resolutions")
    audit = parse_audit((out / "logs" / (AUDIT + ".compile.log")).read_text(), manifest)
    require(record["audit"] == audit, "Changed audit transcript")
    for endpoint in manifest["endpoint_declarations"]:
        require(endpoint in audit["constant_owners"], "Missing named endpoint")
    return {"status": "PASS", "record_sha256": sha(out / "replay-record.json"), "source_modules": manifest["source_count"],
            "successful_commands": manifest["planned_successful_commands"], "audited_constant_rows": audit["audited_constant_rows"],
            "audited_distinct_names": audit["audited_distinct_names"], "audited_private_rows": audit["audited_private_rows"],
            "external_objects": len(state["external_object_sha256"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--toolchain", required=True, type=Path)
    parser.add_argument("--mathlib", required=True, type=Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--preflight", action="store_true")
    action.add_argument("--run", action="store_true")
    action.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    require(bool(re.fullmatch(r"[0-9a-f]{64}", args.expected_manifest_sha256)), "Invalid expected manifest SHA256")
    pin, toolchain, mathlib = args.expected_manifest_sha256, args.toolchain.resolve(), args.mathlib.resolve()
    require(toolchain != mathlib and not ROOT.is_relative_to(toolchain) and not ROOT.is_relative_to(mathlib),
            "External root contains the bundle")
    manifest = load_manifest(pin)
    state, libraries = input_state(manifest, pin, toolchain, mathlib)
    out = ROOT / ".replay"
    if args.preflight:
        write_json(ROOT / "preflight-input-state.json", state)
        print(json.dumps({"status": "PASS", "modules": manifest["source_count"],
                          "external_objects": len(state["external_object_sha256"]),
                          "baseline_sha256": sha(ROOT / "preflight-input-state.json")}))
        return
    if args.verify_only:
        print(json.dumps(verify(out, manifest, pin, state, libraries, toolchain, mathlib)))
        return
    require(not out.exists(), "Fresh output exists; preserve it before any subsequent replay")
    require(shutil.disk_usage(ROOT).free >= 1024 ** 3, "Less than 1 GiB free before fresh replay")
    started = utc()
    for name in ["source", "modules", "logs"]:
        (out / name).mkdir(parents=True)
    write_json(out / "input-state-before.json", state)
    for module in manifest["modules_in_topological_order"]:
        target = out / "source" / rel(module, ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / manifest["modules"][module]["source"], target)
    (out / "source" / rel(AUDIT, ".lean")).write_text(audit_source(manifest["modules_in_topological_order"]))
    roots, commands, results = [out / "modules", *libraries], [], {}
    env = clean_env(toolchain, roots)
    for module in [*manifest["modules_in_topological_order"], AUDIT]:
        require(shutil.disk_usage(ROOT).free >= 512 * 1024 ** 2, "Less than 512 MiB free during replay; artifacts preserved")
        source, obj = out / "source" / rel(module, ".lean"), out / "modules" / rel(module)
        obj.parent.mkdir(parents=True, exist_ok=True)
        if module != AUDIT:
            require(sha(source) == manifest["modules"][module]["sha256"], "Copied source changed")
        imports = manifest["modules"][module]["imports"] if module != AUDIT else [*manifest["modules_in_topological_order"], "Lean"]
        for imported in imports:
            actual = resolve(imported, roots)
            if imported in manifest["modules"]:
                require(imported in results and actual == out / "modules" / rel(imported) and
                        sha(actual) == results[imported]["object_sha256"], "Wrong fresh internal dependency")
            else:
                require(state["external_object_sha256"].get(symbolic(actual, toolchain, mathlib)) == sha(actual),
                        "Wrong external dependency")
        for stage in ["compile", "kernel"]:
            arguments = command_arguments(out, module, stage, toolchain)
            start, wall = utc(), time.monotonic()
            run = subprocess.run(arguments, cwd=out / "source", env=env, capture_output=True, text=True)
            log = out / "logs" / (module + "." + stage + ".log")
            log.write_text(run.stdout + run.stderr)
            commands.append({"module": module, "stage": stage,
                             "arguments": symbolic_command(arguments, toolchain, mathlib),
                             "cwd": symbolic(out / "source", toolchain, mathlib),
                             "started_utc": start, "elapsed_seconds": time.monotonic() - wall,
                             "exit_code": run.returncode, "log": symbolic(log, toolchain, mathlib), "log_sha256": sha(log)})
            write_json(out / "progress.json", {"status": "RUNNING", "commands": commands, "results": results})
            require(run.returncode == 0 and not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]),
                    "Replay command failed: " + str(log))
            if stage == "kernel":
                require("replaying " + module + "\n" in log.read_text(), "Missing kernel target marker")
        results[module] = {"source_sha256": sha(source), "object_sha256": sha(obj),
                           "object_parts": {symbolic(path, toolchain, mathlib): sha(path)
                                            for path in sorted(obj.parent.glob(obj.stem + ".*")) if path.is_file()}}
        write_json(out / "progress.json", {"status": "RUNNING", "commands": commands, "results": results})
        print(json.dumps({"module": module, "status": "PASS", "completed": len(results),
                          "total": manifest["source_count"] + 1}), flush=True)
    audit = parse_audit((out / "logs" / (AUDIT + ".compile.log")).read_text(), manifest)
    after, after_libraries = input_state(load_manifest(pin), pin, toolchain, mathlib)
    write_json(out / "input-state-after.json", after)
    require(after == state and after_libraries == libraries, "Inputs changed during replay")
    record = {"status": "PASS", "started_utc": started, "finished_utc": utc(), "manifest_sha256": pin,
              "driver_sha256": state["driver_sha256"], "modules": manifest["modules_in_topological_order"],
              "audit_module": AUDIT, "commands": commands, "results": results, "allowed_axioms": sorted(ALLOWED),
              "input_states": {name: sha(out / name) for name in ["input-state-before.json", "input-state-after.json"]},
              "lean_path": [symbolic(path, toolchain, mathlib) for path in roots],
              "direct_import_resolutions": import_resolutions(manifest, out, state, libraries, toolchain, mathlib),
              "audit": audit, "scope": manifest["scope"],
              "visibility_label_meaning": "private identifies encoded private names; public means not encoded private, not full export visibility"}
    write_json(out / "replay-record.json", record)
    summary = verify(out, manifest, pin, after, libraries, toolchain, mathlib)
    write_json(out / "progress.json", {"status": "PASS", "commands": commands, "results": results})
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
