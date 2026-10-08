#!/usr/bin/env python3
"""Authenticate a relocated full replay and rebuild/check its three public entry modules."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import time
import types

DRIVER_PIN = "037df5d809679c2cebe76d430035ff5dd27029156e640db1440e40980d1c8ebf"
MANIFEST_PIN = "210db3b96c3c5a0c2071cd0d468ff852554ea4bd9e38efba40c183764af0a538"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", required=True, type=Path)
    parser.add_argument("--toolchain", required=True, type=Path)
    parser.add_argument("--full-record-sha256", required=True)
    args = parser.parse_args()
    root, toolchain = args.bundle.resolve(), args.toolchain.resolve()
    out, full = root / ".relocation-smoke", root / ".replay"
    driver, manifest_path = root / "scripts/replay.py", root / "source-manifest.json"
    require(sha(driver) == DRIVER_PIN and sha(manifest_path) == MANIFEST_PIN, "Changed replay input")
    require(sha(full / "replay-record.json") == args.full_record_sha256, "Wrong full replay record")
    script_pin = sha(Path(__file__))
    require(not out.exists(), "Smoke output already exists")
    for part in ["source", "modules", "logs"]:
        (out / part).mkdir(parents=True)
    replay = types.ModuleType("portable_replay")
    replay.__file__ = str(driver)
    exec(compile(driver.read_bytes(), str(driver), "exec"), vars(replay))
    require(replay.ROOT == root, "Imported driver has wrong bundle root")
    manifest = json.loads(manifest_path.read_text())
    modules = manifest["entry_modules"]
    require(modules == ["TrapUnconditionalDeficit", "TrapMicrocanonicalMassFloor", "TrapCentralMicrocanonical"],
            "Unexpected endpoint set")
    record = json.loads((full / "replay-record.json").read_text())
    libraries = [replay.unsymbolic(value, toolchain) for value in record["lean_path"][1:]]
    require(record["lean_path"][0] == "BUNDLE/.replay/modules", "Wrong original fresh module root")
    roots = [out / "modules", full / "modules", *libraries]
    env = replay.clean_env(toolchain, roots)
    commands, authentication, results, direct = [], [], {}, {}

    def authenticate(stage):
        start = time.monotonic()
        run = subprocess.run(["python3", str(driver), "--toolchain", str(toolchain), "--verify-only"],
                             cwd=root, env=replay.clean_env(toolchain), text=True, capture_output=True)
        log = out / "logs" / (stage + ".verify.log")
        log.write_text(run.stdout + run.stderr)
        require(run.returncode == 0, "Relocated record authentication failed: " + log.read_text())
        summary = json.loads(run.stdout)
        require(summary["status"] == "PASS" and summary["record_sha256"] == args.full_record_sha256,
                "Wrong authenticated record")
        authentication.append({"stage": stage, "arguments": ["python3", "BUNDLE/scripts/replay.py", "--toolchain", "TOOLCHAIN/", "--verify-only"],
            "cwd": "BUNDLE/", "exit_code": run.returncode, "elapsed_seconds": time.monotonic() - start,
            "log": replay.symbolic(log, toolchain), "log_sha256": sha(log), "result": summary})

    authenticate("before")
    for module in modules:
        entry = manifest["modules"][module]
        source, obj = out / "source" / replay.rel(module, ".lean"), out / "modules" / replay.rel(module)
        source.parent.mkdir(parents=True, exist_ok=True)
        obj.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / entry["source"], source)
        require(sha(source) == entry["sha256"], "Changed copied endpoint source")
        for imported in entry["imports"]:
            actual = replay.resolve(imported, roots)
            expected = (out / "modules" / replay.rel(imported) if imported in results
                        else full / "modules" / replay.rel(imported) if imported in manifest["modules"] else None)
            if expected:
                require(actual == expected, "Wrong relocated local import")
                expected_hash = results[imported]["object_sha256"] if imported in results else record["results"][imported]["object_sha256"]
            else:
                key = replay.symbolic(actual, toolchain)
                require(key in record["dependency_state"]["external_object_sha256"], "Uninventoried external import")
                expected_hash = record["dependency_state"]["external_object_sha256"][key]
            require(sha(actual) == expected_hash, "Changed relocated import")
            direct[module + " -> " + imported] = {"path": replay.symbolic(actual, toolchain), "sha256": expected_hash}
        for stage in ["compile", "kernel"]:
            arguments = replay.command_arguments(module, stage, out, entry["lean_options"], toolchain)
            start = time.monotonic()
            run = subprocess.run(arguments, cwd=out / "source", env=env, text=True, capture_output=True)
            log = out / "logs" / (module + "." + stage + ".log")
            log.write_text(run.stdout + run.stderr)
            commands.append({"module": module, "stage": stage, "arguments": replay.symbolic_command(arguments, toolchain),
                "cwd": replay.symbolic(out / "source", toolchain), "exit_code": run.returncode,
                "elapsed_seconds": time.monotonic() - start, "log": replay.symbolic(log, toolchain), "log_sha256": sha(log)})
            require(run.returncode == 0 and not any(token in log.read_text() for token in ["warning:", "error:", "sorryAx"]),
                    "Relocated endpoint check failed: " + log.read_text())
            if stage == "compile":
                require(replay.resolve(module, roots) == obj and not obj.is_symlink(), "Checker would select a stale endpoint")
        results[module] = {"source": replay.symbolic(source, toolchain), "object": replay.symbolic(obj, toolchain),
            "source_sha256": sha(source), "object_sha256": sha(obj),
            "object_parts": {replay.symbolic(path, toolchain): sha(path) for path in sorted(obj.parent.glob(obj.stem + ".*")) if path.is_file()}}
        print(json.dumps({"module": module, "status": "PASS"}), flush=True)
    authenticate("after")
    require(sha(driver) == DRIVER_PIN and sha(manifest_path) == MANIFEST_PIN and sha(Path(__file__)) == script_pin,
            "Driver or metadata changed during smoke check")
    require(sha(full / "replay-record.json") == args.full_record_sha256, "Full replay record changed")
    require(not any(path.is_symlink() for path in out.rglob("*")), "Linked smoke artifact")
    require({path.relative_to(out / "modules") for path in (out / "modules").rglob("*.olean")} ==
            {replay.rel(module) for module in modules}, "Unexpected smoke module set")
    for command in [*commands, *authentication]:
        require(sha(replay.unsymbolic(command["log"], toolchain)) == command["log_sha256"], "Changed smoke log")
    for module, result in results.items():
        require(sha(replay.unsymbolic(result["source"], toolchain)) == result["source_sha256"], "Changed smoke source")
        for name, expected in result["object_parts"].items():
            require(sha(replay.unsymbolic(name, toolchain)) == expected, "Changed smoke object companion")
    final = {"status": "PASS", "modules": modules, "commands": commands, "authentication_commands": authentication,
        "results": results, "direct_import_resolutions": direct, "lean_path": [replay.symbolic(path, toolchain) for path in roots],
        "full_replay_record_sha256": args.full_record_sha256, "portable_replay_driver_sha256": DRIVER_PIN,
        "source_manifest_sha256": MANIFEST_PIN, "script_sha256": script_pin,
        "official_tool_runtime_sha256": record["dependency_state"]["official_tool_runtime_sha256"],
        "scope": "Second-path authentication of the copied full replay and fresh compilation plus official kernel checks of three entry modules; not a second full closure replay."}
    replay.write_json(out / "relocation-record.json", final)
    print(json.dumps({"status": "PASS", "record_sha256": sha(out / "relocation-record.json"), "endpoint_commands": len(commands)}))


if __name__ == "__main__":
    main()
