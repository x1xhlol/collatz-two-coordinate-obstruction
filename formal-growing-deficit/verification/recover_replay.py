#!/usr/bin/env python3
"""Recover the recorded 357-module proof prefix after its audit-header failure."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import threading
import time
import types


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def authenticate_proof_prefix(replay, out, toolchain, manifest, inventories, libraries, state, progress):
    modules = manifest["modules_in_topological_order"]
    require(set(progress["results"]) == set(modules), "Wrong original proof result set")
    require(not any(p.is_symlink() for p in out.rglob("*")), "Linked replay artifact")
    require({p.relative_to(out / "modules") for p in (out / "modules").rglob("*.olean")} ==
            {replay.rel(module) for module in modules}, "Unexpected original compiled module set")
    require({p.relative_to(out / "source") for p in (out / "source").rglob("*.lean")} ==
            {replay.rel(module, ".lean") for module in [*modules, replay.AUDIT]}, "Unexpected original source set")
    roots, available, direct = [out / "modules", *libraries], set(), {}
    for index, module in enumerate(modules):
        result = progress["results"][module]
        source, obj = out / "source" / replay.rel(module, ".lean"), out / "modules" / replay.rel(module)
        require(result["source"] == replay.symbolic(source, toolchain) and
                result["object"] == replay.symbolic(obj, toolchain), "Changed original artifact path")
        require(sha(source) == result["source_sha256"] == manifest["modules"][module]["sha256"] and
                sha(obj) == result["object_sha256"], "Changed original proof artifact")
        parts = {replay.symbolic(p, toolchain): sha(p) for p in sorted(obj.parent.glob(obj.stem + ".*")) if p.is_file()}
        require(parts == result["object_parts"], "Changed original object companions")
        for offset, stage in enumerate(["compile", "kernel"]):
            command = progress["commands"][2 * index + offset]
            log = out / "logs" / (module + "." + stage + ".log")
            arguments = replay.command_arguments(module, stage, out, manifest["modules"][module]["lean_options"], toolchain)
            require(command["module"] == module and command["stage"] == stage and command["exit_code"] == 0 and
                    command["arguments"] == replay.symbolic_command(arguments, toolchain) and
                    command["cwd"] == replay.symbolic(out / "source", toolchain), "Changed original command")
            require(command["log"] == replay.symbolic(log, toolchain) and command["log_sha256"] == sha(log) and
                    not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]),
                    "Changed original command log")
            if stage == "kernel":
                require("replaying " + module + "\n" in log.read_text(), "Missing original kernel target marker")
        for imported in inventories[module]["imports"]:
            actual = replay.resolve(imported, roots)
            if imported in manifest["modules"]:
                require(imported in available and actual == out / "modules" / replay.rel(imported) and
                        sha(actual) == progress["results"][imported]["object_sha256"], "Wrong preserved local import")
            else:
                key = replay.symbolic(actual, toolchain)
                require(key in state["external_object_sha256"] and sha(actual) == state["external_object_sha256"][key],
                        "Wrong current external import")
            direct[module + " -> " + imported] = {"object": replay.symbolic(actual, toolchain), "sha256": sha(actual)}
        available.add(module)
    return direct


def kernel_recheck(replay, out, toolchain, modules, env):
    logs = out / "recovery/kernel-logs"
    logs.mkdir()
    stopped, lock, active = threading.Event(), threading.Lock(), {}
    completed = {}

    def worker(module):
        arguments = replay.command_arguments(module, "kernel", out, {}, toolchain)
        start, wall = replay.utc(), time.monotonic()
        with lock:
            if stopped.is_set():
                return None
            process = subprocess.Popen(arguments, cwd=out / "source", env=env, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            active[module] = process
        output, _ = process.communicate()
        with lock:
            active.pop(module)
        log = logs / (module + ".kernel.log")
        log.write_text(output)
        command = {"module": module, "stage": "kernel", "arguments": replay.symbolic_command(arguments, toolchain),
                   "cwd": replay.symbolic(out / "source", toolchain), "start_utc": start,
                   "elapsed_seconds": time.monotonic() - wall, "exit_code": process.returncode,
                   "log": replay.symbolic(log, toolchain), "log_sha256": sha(log)}
        valid = process.returncode == 0 and "replaying " + module + "\n" in output and not any(
            token in output for token in ["warning:", "error:", "sorryAx"])
        if not valid:
            with lock:
                stopped.set()
                for running in active.values():
                    running.terminate()
        return command, valid

    pool = ThreadPoolExecutor(max_workers=3)
    futures = [pool.submit(worker, module) for module in modules]
    try:
        for future in as_completed(futures):
            result = future.result()
            if result is None:
                continue
            command, valid = result
            completed[command["module"]] = command
            ordered = [completed[module] for module in modules if module in completed]
            replay.write_json(out / "recovery/kernel-progress.json",
                              {"status": "RUNNING" if valid else "FAIL", "commands": ordered})
            require(valid, "Recovery kernel check failed: " + command["module"])
            print(json.dumps({"phase": "recovery_kernel", "module": command["module"], "status": "PASS",
                              "completed": len(completed), "total": len(modules)}), flush=True)
    except BaseException:
        with lock:
            stopped.set()
            for running in active.values():
                running.terminate()
        for future in futures:
            future.cancel()
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    require(set(completed) == set(modules), "Incomplete recovery kernel pass")
    commands = [completed[module] for module in modules]
    replay.write_json(out / "recovery/kernel-progress.json", {"status": "PASS", "commands": commands})
    return commands


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", required=True, type=Path)
    parser.add_argument("--toolchain", required=True, type=Path)
    parser.add_argument("--preserved-run", required=True, type=Path)
    parser.add_argument("--expected-driver-sha256", required=True)
    args = parser.parse_args()
    root, toolchain = args.bundle.resolve(), args.toolchain.resolve()
    out, driver = root / ".replay", root / "scripts/replay.py"
    require(sha(driver) == args.expected_driver_sha256, "Wrong corrected driver")
    require(not (out / "replay-record.json").exists() and not (out / "recovery").exists(), "Recovery output exists")
    executor_pin = sha(Path(__file__))
    replay = types.ModuleType("corrected_replay")
    replay.__file__ = str(driver)
    exec(compile(driver.read_bytes(), str(driver), "exec"), vars(replay))
    require(replay.ROOT == root, "Corrected driver uses wrong root")
    recovery_root = out / "recovery"
    original = recovery_root / "original"
    original.mkdir(parents=True)
    inputs = {
        "replay.py": args.preserved_run / "replay.py",
        "progress.json": args.preserved_run / "replay/progress.json",
        "source-manifest.json": args.preserved_run / "source-manifest.json",
        replay.AUDIT + ".lean": args.preserved_run / "replay/source" / (replay.AUDIT + ".lean"),
        replay.AUDIT + ".compile.log": args.preserved_run / "replay/logs" / (replay.AUDIT + ".compile.log"),
    }
    for name, source in inputs.items():
        require(not source.is_symlink() and sha(source) == replay.ORIGINAL_RECOVERY_FILES[name], "Changed preserved input")
        shutil.copyfile(source, original / name)
    shutil.copyfile(Path(__file__), recovery_root / "recover_replay.py")
    require(sha(recovery_root / "recover_replay.py") == executor_pin, "Executor copy mismatch")
    progress, original_files = replay.original_recovery_prefix(out, toolchain)
    require(sha(out / "source" / (replay.AUDIT + ".lean")) == replay.ORIGINAL_RECOVERY_FILES[replay.AUDIT + ".lean"] and
            sha(out / "logs" / (replay.AUDIT + ".compile.log")) == replay.ORIGINAL_RECOVERY_FILES[replay.AUDIT + ".compile.log"],
            "Original failed audit artifacts were already changed")
    manifest, inventories, libraries, state = replay.input_state(toolchain)
    direct = authenticate_proof_prefix(replay, out, toolchain, manifest, inventories, libraries, state, progress)
    started = replay.utc()
    baseline = {"created_utc": started, "source_manifest_sha256": replay.MANIFEST_SHA256,
                "corrected_driver_sha256": args.expected_driver_sha256, "executor_sha256": executor_pin,
                "original_progress_sha256": replay.ORIGINAL_RECOVERY_FILES["progress.json"],
                "dependency_state": state, "source_inventory": inventories}
    baseline_path = recovery_root / "input-state.json"
    replay.write_json(baseline_path, baseline)
    baseline_pin = sha(baseline_path)
    print(json.dumps({"phase": "persisted_recovery_baseline", "status": "PASS", "sha256": baseline_pin,
                      "external_objects": len(state["external_object_sha256"])}), flush=True)
    roots = [out / "modules", *libraries]
    env = replay.clean_env(toolchain, roots)
    modules = manifest["modules_in_topological_order"]
    kernel_commands = kernel_recheck(replay, out, toolchain, modules, env)
    require(sha(baseline_path) == baseline_pin, "Recovery baseline changed during kernel pass")
    source, obj = out / "source" / (replay.AUDIT + ".lean"), out / "modules" / (replay.AUDIT + ".olean")
    source.write_text(replay.audit_source(modules))
    commands = list(progress["commands"][:714])
    for stage in ["compile", "kernel"]:
        arguments = replay.command_arguments(replay.AUDIT, stage, out, {"warningAsError": True}, toolchain)
        start, wall = replay.utc(), time.monotonic()
        run = subprocess.run(arguments, cwd=out / "source", env=env, text=True, capture_output=True)
        log = out / "logs" / (replay.AUDIT + "." + stage + ".log")
        log.write_text(run.stdout + run.stderr)
        commands.append({"module": replay.AUDIT, "stage": stage,
                         "arguments": replay.symbolic_command(arguments, toolchain),
                         "cwd": replay.symbolic(out / "source", toolchain), "start_utc": start,
                         "elapsed_seconds": time.monotonic() - wall, "exit_code": run.returncode,
                         "log": replay.symbolic(log, toolchain), "log_sha256": sha(log)})
        require(run.returncode == 0 and not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]),
                "Corrected audit failed: " + log.read_text())
        if stage == "kernel":
            require("replaying " + replay.AUDIT + "\n" in log.read_text(), "Missing corrected audit kernel marker")
        print(json.dumps({"phase": "corrected_audit", "stage": stage, "status": "PASS"}), flush=True)
    results = dict(progress["results"])
    results[replay.AUDIT] = {"source": replay.symbolic(source, toolchain), "object": replay.symbolic(obj, toolchain),
                            "source_sha256": sha(source), "object_sha256": sha(obj),
                            "object_parts": {replay.symbolic(p, toolchain): sha(p) for p in
                                             sorted(obj.parent.glob(obj.stem + ".*")) if p.is_file()}}
    counts, rows = replay.parse_audit((out / "logs" / (replay.AUDIT + ".compile.log")).read_text(), modules, inventories)
    require(replay.input_state(toolchain) == (manifest, inventories, libraries, state), "Inputs changed during recovery")
    require(sha(baseline_path) == baseline_pin and sha(driver) == args.expected_driver_sha256 and
            sha(Path(__file__)) == executor_pin, "Recovery recipe or baseline changed")
    recovery = {"status": "PASS", "kind": "audit_harness_recovery_with_complete_kernel_recheck",
                "started_utc": started, "finished_utc": replay.utc(), "original_files": original_files,
                "original_failed_command": progress["commands"][-1], "original_external_inventory_preserved": False,
                "dependency_inventory_scope": "persisted before and revalidated after recovery only",
                "original_driver_sha256": replay.ORIGINAL_RECOVERY_FILES["replay.py"],
                "corrected_driver_sha256": args.expected_driver_sha256,
                "input_state": replay.symbolic(baseline_path, toolchain), "input_state_sha256": baseline_pin,
                "executor": replay.symbolic(recovery_root / "recover_replay.py", toolchain), "executor_sha256": executor_pin,
                "kernel_workers": 3, "kernel_commands": kernel_commands, "successful_command_count": 1073,
                "failed_command_count": 1,
                "evidence_files": {replay.symbolic(p, toolchain): sha(p) for p in sorted(recovery_root.rglob("*")) if p.is_file()},
                "scope": "The original 357 source compilations and 357 kernel checks are retained unchanged. After an audit-header failure, all 357 preserved proof objects were checked again against the persisted recovery dependency state, and the corrected complete audit was compiled and checked. The original pre-run external inventory was not persisted."}
    record = {"status": "PASS", "started_utc": progress["commands"][0]["start_utc"], "finished_utc": replay.utc(),
              "started_utc_basis": "first preserved command timestamp", "modules": modules, "audit_module": replay.AUDIT,
              "commands": commands, "results": results, "source_manifest_sha256": replay.MANIFEST_SHA256,
              "script_sha256": args.expected_driver_sha256, "source_inventory": inventories, "dependency_state": state,
              "lean_path": [replay.symbolic(path, toolchain) for path in roots], "direct_import_resolutions": direct,
              "allowed_axioms": sorted(replay.ALLOWED), "module_constant_counts": counts, "declarations": rows,
              "audited_constant_count": len(rows), "declaration_key_format": "module|constant_name",
              "audited_distinct_constant_name_count": len({row["name"] for row in rows.values()}),
              "audited_private_constant_count": sum(row["visibility"] == "private" for row in rows.values()),
              "visibility_label_meaning": "private identifies Lean encoded private names; public means not encoded private and is not a complete module export-visibility classification",
              "scope": manifest["scope"], "recovery": recovery,
              "external_library_policy": "Exact pinned external source checkouts. Cached external objects were hash-inventoried before and after recovery, which kernel-checked every preserved bundled proof object. The original pre-run external inventory was not persisted. External libraries were not rebuilt."}
    replay.write_json(out / "replay-record.json", record)
    print(json.dumps(replay.verify_record(out, toolchain, manifest, inventories, libraries, state,
                                         args.expected_driver_sha256)), flush=True)


if __name__ == "__main__":
    main()
