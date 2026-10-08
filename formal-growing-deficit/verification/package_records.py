#!/usr/bin/env python3
"""Package authenticated replay records and their exact logs without binary objects."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import shutil
import tarfile


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def create_archive(paths, target):
    expected = {}
    for name, path in paths.items():
        require(not Path(name).is_absolute() and ".." not in Path(name).parts and "\\" not in name,
                "Nonportable archive member")
        require(path.is_file() and not path.is_symlink(), "Non-file or linked archive input")
        expected[name] = {"sha256": sha(path), "bytes": path.stat().st_size}
    with target.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w") as archive:
            for name in sorted(expected):
                path = paths[name]
                info = tarfile.TarInfo(name)
                info.size = path.stat().st_size
                info.mode = 0o644
                info.mtime = 0
                with path.open("rb") as source:
                    archive.addfile(info, source)
    with tarfile.open(target, mode="r:gz") as archive:
        members = archive.getmembers()
        require(len(members) == len(expected) and {m.name for m in members} == set(expected), "Archive name mismatch")
        for member in members:
            require(member.isfile(), "Non-file archive member")
            data = archive.extractfile(member).read()
            entry = expected[member.name]
            require(hashlib.sha256(data).hexdigest() == entry["sha256"] and len(data) == entry["bytes"],
                    "Archive round-trip mismatch")
    return expected


def archive_logs(bundle, commands, stage, target):
    log_root = bundle / stage / "logs"
    expected = {}
    prefix = "BUNDLE/" + stage + "/logs/"
    for command in commands:
        symbolic = command["log"]
        require(symbolic.startswith(prefix), "Unexpected recorded log path")
        name = symbolic.removeprefix(prefix)
        require(name and "/" not in name and "\\" not in name and name not in {".", ".."}, "Nonportable log name")
        path = log_root / name
        require(name not in expected and not path.is_symlink(), "Duplicate or linked log")
        require(command["exit_code"] == 0 and sha(path) == command["log_sha256"], "Changed log")
        expected[name] = path
    require({p.name for p in log_root.iterdir()} == set(expected), "Unexpected log directory contents")
    members = create_archive({"logs/" + name: path for name, path in expected.items()}, target)
    return {"archive_member_prefix": "logs/", "recorded_log_prefix": prefix,
            "files": {name.removeprefix("logs/"): entry for name, entry in members.items()}}


def archive_recovery(bundle, recovery, target):
    prefix, root = "BUNDLE/.replay/recovery/", bundle / ".replay/recovery"
    expected = {}
    for symbolic, digest in recovery["evidence_files"].items():
        require(symbolic.startswith(prefix), "Unexpected recovery path")
        name = symbolic.removeprefix(prefix)
        require(name and not Path(name).is_absolute() and ".." not in Path(name).parts and "\\" not in name,
                "Nonportable recovery path")
        path = root / name
        require(name not in expected and not path.is_symlink() and sha(path) == digest, "Changed recovery evidence")
        require(not any(name.endswith(extension) for extension in
                        (".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig", ".so", ".pyc")),
                "Compiled object in recovery evidence")
        expected[name] = path
    require({p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()} == set(expected) and
            not any(p.is_symlink() for p in root.rglob("*")), "Changed recovery evidence set")
    members = create_archive({"recovery/" + name: path for name, path in expected.items()}, target)
    return {"archive_member_prefix": "recovery/", "recorded_file_prefix": prefix,
            "files": {name.removeprefix("recovery/"): entry for name, entry in members.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-bundle", type=Path, required=True)
    parser.add_argument("--relocated-bundle", type=Path, required=True)
    parser.add_argument("--full-record-sha256", required=True)
    parser.add_argument("--relocation-record-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    full_path = args.full_bundle / ".replay/replay-record.json"
    relocation_path = args.relocated_bundle / ".relocation-smoke/relocation-record.json"
    require(sha(full_path) == args.full_record_sha256, "Wrong full record")
    require(sha(relocation_path) == args.relocation_record_sha256, "Wrong relocation record")
    full, relocation = json.loads(full_path.read_text()), json.loads(relocation_path.read_text())
    require(full["status"] == relocation["status"] == "PASS", "Unsuccessful replay")
    require(len(full["commands"]) == 716 and len(full["modules"]) == 357, "Wrong full replay scope")
    recovery = full["recovery"]
    require(recovery["status"] == "PASS" and len(recovery["kernel_commands"]) == 357 and
            recovery["successful_command_count"] == 1073 and recovery["failed_command_count"] == 1,
            "Wrong recovery scope")
    require(len(relocation["commands"]) == 6 and len(relocation["authentication_commands"]) == 2,
            "Wrong relocation scope")
    require(relocation["full_replay_record_sha256"] == args.full_record_sha256, "Unlinked relocation record")
    require(not args.output.exists(), "Evidence output already exists")
    args.output.mkdir(parents=True)
    shutil.copyfile(full_path, args.output / "replay-record.json")
    shutil.copyfile(relocation_path, args.output / "relocation-record.json")
    archives = {
        "full-replay-logs.tar.gz": archive_logs(args.full_bundle, full["commands"], ".replay",
                                               args.output / "full-replay-logs.tar.gz"),
        "relocation-logs.tar.gz": archive_logs(args.relocated_bundle,
                                              relocation["commands"] + relocation["authentication_commands"],
                                              ".relocation-smoke", args.output / "relocation-logs.tar.gz"),
    }
    recovery_archive = archive_recovery(args.full_bundle, recovery, args.output / "recovery-evidence.tar.gz")
    audit_name = full["audit_module"]
    audit = args.full_bundle / ".replay/source" / (audit_name + ".lean")
    require(not audit.is_symlink() and sha(audit) == full["results"][audit_name]["source_sha256"],
            "Changed generated audit source")
    shutil.copyfile(audit, args.output / "generated-audit.lean")
    files = {p.name: {"sha256": sha(p), "bytes": p.stat().st_size} for p in sorted(args.output.iterdir())}
    index = {
        "status": "PASS",
        "files": files,
        "log_archives": archives,
        "recovery_archive": {"name": "recovery-evidence.tar.gz", **recovery_archive},
        "scope": "Exact historical records, generated audit source, original failure evidence, persisted recovery baseline, recovery executor, and recorded logs. No compiled objects are included. Archives use relative member names, zero timestamps, and fixed permissions. The preserved raw failed compiler diagnostic retains its original source path.",
        "full_commands": len(full["commands"]),
        "recovery_kernel_commands": len(recovery["kernel_commands"]),
        "successful_proof_and_audit_commands": recovery["successful_command_count"],
        "preserved_failed_commands": recovery["failed_command_count"],
        "relocation_endpoint_commands": len(relocation["commands"]),
        "relocation_authentication_commands": len(relocation["authentication_commands"]),
        "packager_sha256": sha(Path(__file__)),
    }
    output = args.output / "evidence-index.json"
    output.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "index_sha256": sha(output), "files": files}))


if __name__ == "__main__":
    main()
