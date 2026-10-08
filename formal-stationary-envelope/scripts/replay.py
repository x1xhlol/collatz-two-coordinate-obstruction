#!/usr/bin/env python3
"""Portable fresh source replay for the canonical integer-envelope endpoints."""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import threading
import time

from source_inventory import source_inventory, scrub_lean

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "source-manifest.json"
AUDIT = "IntegerEnvelopeCompleteAudit"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ENDINGS = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig", ".so")
MIN_AVAILABLE_BYTES = 4 * 1024 ** 3
EXCLUSIVE_SOURCE_BYTES = 50000


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


def available_memory():
    """Linux MemAvailable, reduced by a visible cgroup-v2 memory limit."""
    match = re.search(r"^MemAvailable:\s+(\d+) kB$", Path("/proc/meminfo").read_text(), re.M)
    require(match is not None, "Cannot measure available RAM")
    host = int(match[1]) * 1024
    limits = []
    cgroup_root = Path("/sys/fs/cgroup")
    cgroup_lines = Path("/proc/self/cgroup").read_text().splitlines()
    require(all(len(line.split(":", 2)) == 3 for line in cgroup_lines), "Malformed cgroup membership")
    require(not any("memory" in line.split(":", 2)[1].split(",") for line in cgroup_lines),
            "Cgroup-v1 memory control is unsupported; cannot measure effective available RAM")
    cgroup_line = next((line[3:] for line in cgroup_lines
                       if line.startswith("0::")), None)
    if cgroup_line is not None:
        # Containers may expose their own cgroup as the mount root.
        leaf = cgroup_root / cgroup_line.lstrip("/")
        if not leaf.is_dir():
            leaf = cgroup_root
        require(leaf.resolve().is_relative_to(cgroup_root.resolve()), "Invalid cgroup memory path")
        for directory in [leaf, *leaf.parents]:
            if not directory.is_relative_to(cgroup_root):
                break
            maximum, current = directory / "memory.max", directory / "memory.current"
            if maximum.is_file():
                value = maximum.read_text().strip()
                if value != "max":
                    limits.append({"path": str(directory), "limit_bytes": int(value),
                                   "used_bytes": int(current.read_text().strip())})
                    require(limits[-1]["limit_bytes"] >= 0 and limits[-1]["used_bytes"] >= 0,
                            "Negative cgroup memory telemetry")
    available = min([host, *[max(0, row["limit_bytes"] - row["used_bytes"]) for row in limits]])
    return {"available_bytes": available, "host_mem_available_bytes": host, "cgroup_v2_limits": limits}


def scheduling_policy(jobs):
    return {"version": 1, "jobs": jobs, "minimum_available_bytes": MIN_AVAILABLE_BYTES,
            "exclusive_source_bytes": EXCLUSIVE_SOURCE_BYTES,
            "clock": "seconds since scheduler start, time.monotonic",
            "command_order": "topological module order, compile then kernel",
            "launch_policy": "atomic pair reservations, at most jobs submitted and unaccepted pairs; no executor backlog",
            "failure_policy": "stop new reservations at failure latch; drain every already-reserved compile/kernel pair",
            "memory_policy": "Linux MemAvailable capped by visible cgroup-v2 ancestor limits"}


def run_schedule(units, dependencies, sizes, run_pair, publish, jobs, memory_probe=available_memory):
    """Coordinator owns acceptance; workers own one complete compile/kernel pair."""
    require(type(jobs) is int and 1 <= jobs <= 4, "Jobs must be between 1 and 4")
    origin, stopped, launch_lock = time.monotonic(), threading.Event(), threading.Lock()
    results, completed, runs, active = {}, {}, {}, {}
    pending, errors = list(units), []
    scheduling = {"policy": scheduling_policy(jobs), "module_runs": runs, "first_failure_seconds": None}

    def ordered_commands():
        return [command for module in units for command in completed.get(module, {}).get("commands", [])]

    def emit(status):
        publish({"status": status, "commands": ordered_commands(), "results": dict(results),
                 "scheduling": scheduling, "errors": list(errors)})

    def latch_failure():
        with launch_lock:
            if not stopped.is_set():
                scheduling["first_failure_seconds"] = time.monotonic() - origin
            stopped.set()

    def worker(module, accepted):
        try:
            outcome = run_pair(module, accepted, origin, latch_failure)
            require(outcome.get("status") in {"PASS", "FAILED"}, "Invalid worker outcome")
        except Exception as error:
            outcome = {"status": "FAILED", "error": str(error), "commands": []}
        if outcome["status"] != "PASS":
            latch_failure()
        return outcome

    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or active:
            # Accept all completed pairs before considering any new launch.
            for future in list(active):
                if not future.done():
                    continue
                module = active.pop(future)
                outcome = future.result()
                completed[module] = outcome
                runs[module]["finished_seconds"] = outcome.get("finished_seconds", time.monotonic() - origin)
                runs[module]["accepted_seconds"] = time.monotonic() - origin
                runs[module]["status"] = outcome["status"]
                if outcome["status"] == "PASS":
                    results[module] = outcome["result"]
                else:
                    errors.append({"module": module, "error": outcome.get("error", "Module pair failed")})
                emit("FAILED" if stopped.is_set() else "RUNNING")
            if stopped.is_set():
                if active:
                    wait(active, return_when=FIRST_COMPLETED)
                    continue
                break
            launched = False
            while pending and len(active) < jobs:
                ready = next((module for module in pending if all(dep in results for dep in dependencies[module])), None)
                require(ready is not None or bool(active), "No ready module in dependency schedule")
                if ready is None:
                    break
                exclusive = ready == AUDIT or sizes[ready] >= EXCLUSIVE_SOURCE_BYTES
                if active and (exclusive or any(runs[module]["exclusive"] for module in active.values())):
                    break
                try:
                    memory = memory_probe()
                    if memory["available_bytes"] < MIN_AVAILABLE_BYTES:
                        require(bool(active), "Less than 4 GiB available RAM with no active pair; artifacts preserved")
                        break
                    with launch_lock:
                        if stopped.is_set():
                            break
                        runs[ready] = {"module": ready, "launch_index": len(runs),
                                       "dependencies": dependencies[ready], "source_bytes": sizes[ready],
                                       "exclusive": exclusive, "memory_before_launch": memory,
                                       "launched_utc": utc(), "launched_seconds": time.monotonic() - origin,
                                       "status": "RUNNING"}
                        future = executor.submit(worker, ready, dict(results))
                        active[future] = ready
                        pending.remove(ready)
                    launched = True
                    emit("RUNNING")
                except Exception as error:
                    latch_failure()
                    errors.append({"module": ready, "error": str(error)})
                    emit("FAILED")
                    break
                if exclusive:
                    break
            if active:
                wait(active, return_when=FIRST_COMPLETED)
            elif pending and not stopped.is_set() and not launched:
                raise RuntimeError("Dependency scheduler made no progress")
    emit("FAILED" if stopped.is_set() else "RUNNING")
    require(not stopped.is_set() and set(results) == set(units), "Replay pair failed; artifacts preserved")
    return ordered_commands(), results, scheduling


def verify_memory_sample(memory):
    host, caps = memory["host_mem_available_bytes"], memory["cgroup_v2_limits"]
    require(type(host) is int and host >= 0 and isinstance(caps, list), "Invalid RAM sample")
    for cap in caps:
        require(isinstance(cap["path"], str) and type(cap["limit_bytes"]) is int and cap["limit_bytes"] >= 0 and
                type(cap["used_bytes"]) is int and cap["used_bytes"] >= 0, "Invalid cgroup RAM sample")
    require(type(memory["available_bytes"]) is int and memory["available_bytes"] ==
            min([host, *[max(0, cap["limit_bytes"] - cap["used_bytes"]) for cap in caps]]) and
            memory["available_bytes"] >= MIN_AVAILABLE_BYTES, "Insufficient recorded available RAM")


def verify_schedule(record, out, manifest):
    units = [*manifest["modules_in_topological_order"], AUDIT]
    schedule = record["scheduling"]
    require(schedule["first_failure_seconds"] is None, "Successful schedule contains a failure latch")
    jobs = schedule["policy"]["jobs"]
    require(type(jobs) is int and 1 <= jobs <= 4 and schedule["policy"] == scheduling_policy(jobs),
            "Changed scheduling policy")
    runs = schedule["module_runs"]
    require(set(runs) == set(units), "Incomplete scheduling evidence")
    by_launch, events = {}, []
    for index, module in enumerate(units):
        row = runs[module]
        size = (out / "source" / rel(module, ".lean")).stat().st_size
        dependencies = [name for name in manifest["modules"][module]["imports"] if name in manifest["modules"]] if module != AUDIT else units[:-1]
        require(row["module"] == module and row["status"] == "PASS" and row["source_bytes"] == size and
                row["dependencies"] == dependencies and row["exclusive"] == (module == AUDIT or size >= EXCLUSIVE_SOURCE_BYTES),
                "Changed module scheduling evidence")
        launch_index = row["launch_index"]
        require(type(launch_index) is int and 0 <= launch_index < len(units) and launch_index not in by_launch,
                "Invalid scheduling launch index")
        by_launch[launch_index] = module
        start, finish, accepted = [row[name] for name in ["launched_seconds", "finished_seconds", "accepted_seconds"]]
        require(all(type(value) in {int, float} and math.isfinite(value) for value in [start, finish, accepted]) and
                0 <= start <= finish <= accepted, "Invalid scheduling times")
        verify_memory_sample(row["memory_before_launch"])
        require(all(runs[dep]["accepted_seconds"] <= start for dep in dependencies), "Dependency pair accepted after launch")
        stages = record["commands"][2 * index:2 * index + 2]
        previous = start
        for command in stages:
            first, last = command["started_seconds"], command["finished_seconds"]
            require(all(type(value) in {int, float} and math.isfinite(value) for value in [first, last, command["elapsed_seconds"]]) and
                    previous <= first <= last <= finish and
                    math.isclose(command["elapsed_seconds"], last - first, abs_tol=1e-9), "Invalid pair command times")
            verify_memory_sample(command["memory_before_start"])
            previous = last
        events.extend([(start, 1, module), (accepted, -1, module)])
    ordered = [by_launch[index] for index in range(len(units))]
    require(ordered[-1] == AUDIT and (jobs != 1 or ordered == units), "Changed sequential or audit launch order")
    require(all(runs[ordered[index]]["launched_seconds"] <= runs[ordered[index + 1]]["launched_seconds"]
                for index in range(len(ordered) - 1)), "Launch indexes disagree with actual times")
    active = set()
    for _, change, module in sorted(events):
        if change == -1:
            require(module in active, "Invalid schedule completion")
            active.remove(module)
        else:
            require(module not in active and len(active) < jobs and
                    (not active or (not runs[module]["exclusive"] and not any(runs[name]["exclusive"] for name in active))),
                    "Concurrency or exclusive-module policy violated")
            active.add(module)
    require(not active, "Unfinished scheduling interval")


def compile_module_pair(module, accepted, origin, latch_failure, out, manifest, state, roots, env, toolchain, mathlib):
    commands = []
    progress = out / "module-progress" / (module + ".json")
    try:
        require(shutil.disk_usage(ROOT).free >= 512 * 1024 ** 2, "Less than 512 MiB free during replay; artifacts preserved")
        source, obj = out / "source" / rel(module, ".lean"), out / "modules" / rel(module)
        obj.parent.mkdir(parents=True, exist_ok=True)
        if module != AUDIT:
            require(sha(source) == manifest["modules"][module]["sha256"], "Copied source changed")
        imports = manifest["modules"][module]["imports"] if module != AUDIT else [*manifest["modules_in_topological_order"], "Lean"]
        for imported in imports:
            actual = resolve(imported, roots)
            if imported in manifest["modules"]:
                require(imported in accepted and actual == out / "modules" / rel(imported) and
                        sha(actual) == accepted[imported]["object_sha256"], "Wrong fresh internal dependency")
            else:
                require(state["external_object_sha256"].get(symbolic(actual, toolchain, mathlib)) == sha(actual),
                        "Wrong external dependency")
        for stage in ["compile", "kernel"]:
            arguments = command_arguments(out, module, stage, toolchain)
            memory = available_memory()
            require(memory["available_bytes"] >= MIN_AVAILABLE_BYTES, "Less than 4 GiB available RAM before command start")
            start, wall = utc(), time.monotonic() - origin
            run = subprocess.run(arguments, cwd=out / "source", env=env, capture_output=True, text=True)
            finish = time.monotonic() - origin
            transcript = run.stdout + run.stderr
            successful = run.returncode == 0 and not any(token in transcript for token in ["warning:", "error:", "sorryAx"])
            kernel_marker = stage != "kernel" or "replaying " + module + "\n" in transcript
            if not successful or not kernel_marker:
                latch_failure()
            log = out / "logs" / (module + "." + stage + ".log")
            log.write_text(transcript)
            commands.append({"module": module, "stage": stage,
                             "arguments": symbolic_command(arguments, toolchain, mathlib),
                             "cwd": symbolic(out / "source", toolchain, mathlib),
                             "started_utc": start, "started_seconds": wall, "finished_seconds": finish,
                             "elapsed_seconds": finish - wall, "memory_before_start": memory,
                             "exit_code": run.returncode, "log": symbolic(log, toolchain, mathlib), "log_sha256": sha(log)})
            write_json(progress, {"status": "RUNNING", "module": module, "commands": commands})
            require(successful, "Replay command failed: " + str(log))
            require(kernel_marker, "Missing kernel target marker")
        result = {"source_sha256": sha(source), "object_sha256": sha(obj),
                  "object_parts": {symbolic(path, toolchain, mathlib): sha(path)
                                   for path in sorted(obj.parent.glob(obj.stem + ".*")) if path.is_file()}}
        outcome = {"status": "PASS", "module": module, "commands": commands, "result": result,
                   "finished_seconds": time.monotonic() - origin}
    except Exception as error:
        latch_failure()
        outcome = {"status": "FAILED", "module": module, "commands": commands, "error": str(error),
                   "finished_seconds": time.monotonic() - origin}
    write_json(progress, outcome)
    return outcome


def verify(out, manifest, manifest_pin, state, libraries, toolchain, mathlib, pending=False):
    record = json.loads((out / "replay-record.json").read_text())
    units = [*manifest["modules_in_topological_order"], AUDIT]
    require(record["status"] == ("VERIFYING" if pending else "PASS") and record["modules"] == units[:-1] and record["audit_module"] == AUDIT,
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
    verify_schedule(record, out, manifest)
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
    parser.add_argument("--jobs", type=int, choices=range(1, 5), default=1,
                        help="concurrent dependency-ready compile/kernel pairs (default: 1)")
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
    for name in ["source", "modules", "logs", "module-progress"]:
        (out / name).mkdir(parents=True)
    write_json(out / "input-state-before.json", state)
    for module in manifest["modules_in_topological_order"]:
        target = out / "source" / rel(module, ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / manifest["modules"][module]["source"], target)
    (out / "source" / rel(AUDIT, ".lean")).write_text(audit_source(manifest["modules_in_topological_order"]))
    roots, commands, results = [out / "modules", *libraries], [], {}
    env = clean_env(toolchain, roots)
    units = [*manifest["modules_in_topological_order"], AUDIT]
    dependencies = {module: [name for name in manifest["modules"][module]["imports"] if name in manifest["modules"]]
                    for module in units[:-1]}
    dependencies[AUDIT] = units[:-1]
    sizes = {module: (out / "source" / rel(module, ".lean")).stat().st_size for module in units}

    def pair(module, accepted, origin, latch_failure):
        return compile_module_pair(module, accepted, origin, latch_failure, out, manifest, state, roots, env, toolchain, mathlib)

    last_completed = 0
    def publish(progress):
        nonlocal last_completed
        write_json(out / "progress.json", progress)
        if len(progress["results"]) != last_completed:
            last_completed = len(progress["results"])
            print(json.dumps({"status": progress["status"], "completed": last_completed,
                              "total": len(units), "jobs": args.jobs}), flush=True)

    commands, results, scheduling = run_schedule(units, dependencies, sizes, pair, publish, args.jobs)
    try:
        audit = parse_audit((out / "logs" / (AUDIT + ".compile.log")).read_text(), manifest)
        after, after_libraries = input_state(load_manifest(pin), pin, toolchain, mathlib)
        write_json(out / "input-state-after.json", after)
        require(after == state and after_libraries == libraries, "Inputs changed during replay")
        record = {"status": "VERIFYING", "started_utc": started, "finished_utc": utc(), "manifest_sha256": pin,
                  "driver_sha256": state["driver_sha256"], "modules": manifest["modules_in_topological_order"],
                  "audit_module": AUDIT, "commands": commands, "results": results, "scheduling": scheduling,
                  "allowed_axioms": sorted(ALLOWED),
                  "input_states": {name: sha(out / name) for name in ["input-state-before.json", "input-state-after.json"]},
                  "lean_path": [symbolic(path, toolchain, mathlib) for path in roots],
                  "direct_import_resolutions": import_resolutions(manifest, out, state, libraries, toolchain, mathlib),
                  "audit": audit, "scope": manifest["scope"],
                  "visibility_label_meaning": "private identifies encoded private names; public means not encoded private, not full export visibility"}
        write_json(out / "replay-record.json", record)
    except Exception as error:
        write_json(out / "progress.json", {"status": "FAILED", "commands": commands, "results": results,
                                           "scheduling": scheduling, "post_schedule_error": str(error)})
        raise
    try:
        summary = verify(out, manifest, pin, after, libraries, toolchain, mathlib, pending=True)
    except Exception as error:
        record["status"], record["verification_error"] = "FAILED", str(error)
        write_json(out / "replay-record.json", record)
        write_json(out / "progress.json", {"status": "FAILED", "commands": commands, "results": results,
                                           "scheduling": scheduling, "verification_error": str(error)})
        raise
    record["status"] = "PASS"
    write_json(out / "replay-record.json", record)
    summary["record_sha256"] = sha(out / "replay-record.json")
    write_json(out / "progress.json", {"status": "PASS", "commands": commands, "results": results, "scheduling": scheduling})
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
