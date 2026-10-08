#!/usr/bin/env python3
"""Prepare pinned external dependencies or verify existing installations without changing them."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PIN = "96500e070b6dcdc730975638029d0f7aa31ba40db2ecb46282f76c91175af5b9"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run(command, *, cwd, env):
    print("Running:", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, env=env, check=True)


def clone_pinned(url, revision, destination, env):
    require(not destination.exists(), "Fresh checkout destination already exists: " + str(destination))
    destination.mkdir(parents=True)
    run(["git", "init", "--quiet", str(destination)], cwd=ROOT, env=env)
    run(["git", "remote", "add", "origin", url], cwd=destination, env=env)
    run(["git", "fetch", "--depth=1", "origin", revision], cwd=destination, env=env)
    run(["git", "checkout", "--quiet", "--detach", revision], cwd=destination, env=env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path,
                        help="Reuse the exact official Linux x86_64 toolchain, read-only")
    parser.add_argument("--mathlib", type=Path,
                        help="Reuse an exact Mathlib checkout with its eight dependencies and caches, read-only")
    parser.add_argument("--external-dir", type=Path, default=ROOT / ".external",
                        help="Location for fresh downloads and checkouts; default: BUNDLE/.external")
    args = parser.parse_args()
    require(platform.system() == "Linux" and platform.machine() == "x86_64",
            "This recipe pins the official Linux x86_64 distribution")
    require(sys.version_info >= (3, 9), "Python 3.9 or later is required")
    require(sha(ROOT / "source-manifest.json") == MANIFEST_PIN, "Unexpected source manifest")
    manifest = json.loads((ROOT / "source-manifest.json").read_text())
    for name, expected in manifest["pinned_files"].items():
        require(sha(ROOT / name) == expected, "Changed bundled input: " + name)
    for entry in manifest["modules"].values():
        require(sha(ROOT / entry["source"]) == entry["sha256"], "Changed source: " + entry["source"])
    deps = json.loads((ROOT / "dependency-pins.json").read_text())
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("LEAN_", "ELAN_", "MATHLIB_CACHE_"))
           and key not in {"LD_PRELOAD", "LD_LIBRARY_PATH"}}
    env["PATH"] = "/usr/bin:/bin"
    require(shutil.which("git", path=env["PATH"]), "Git must be available in /usr/bin or /bin")
    if not args.mathlib:
        require(shutil.which("curl", path=env["PATH"]), "Fresh Mathlib cache preparation requires curl >= 7.81")
        curl_version = subprocess.check_output(["curl", "--version"], env=env, text=True)
        match = re.match(r"curl (\d+)\.(\d+)", curl_version)
        require(match and tuple(map(int, match.groups())) >= (7, 81),
                "Fresh Mathlib cache preparation requires curl >= 7.81")
    external = args.external_dir.resolve()
    if not args.toolchain or not args.mathlib:
        external.mkdir(parents=True, exist_ok=True)
        require(shutil.disk_usage(external).free >= 15 * 1024 ** 3,
                "Fresh external setup requires at least 15 GiB of free disk space")
    if args.toolchain:
        toolchain = args.toolchain.resolve()
    else:
        require(shutil.which("tar", path=env["PATH"]) and shutil.which("zstd", path=env["PATH"]),
                "Fresh toolchain extraction requires tar and zstd in /usr/bin or /bin")
        archive_spec = deps["lean_archive"]
        archive = external / archive_spec["name"]
        if not archive.exists():
            temporary = archive.with_suffix(archive.suffix + ".partial")
            urllib.request.urlretrieve(archive_spec["url"], temporary)
            require(temporary.stat().st_size == archive_spec["bytes"] and
                    sha(temporary) == archive_spec["sha256"], "Official archive checksum or size mismatch")
            temporary.replace(archive)
        require(archive.stat().st_size == archive_spec["bytes"] and
                sha(archive) == archive_spec["sha256"], "Official archive checksum or size mismatch")
        toolchain = external / archive_spec["directory"]
        require(not toolchain.exists(), "Toolchain destination already exists; reuse it with --toolchain")
        run(["tar", "--zstd", "-xf", str(archive), "-C", str(external)], cwd=ROOT, env=env)
    for name, expected in deps["official_tool_runtime_sha256"].items():
        require(sha(toolchain / name) == expected, "Official tool/runtime checksum mismatch: " + name)
    env.update(PATH=str(toolchain / "bin") + ":/usr/bin:/bin", LEAN_NUM_THREADS="1")
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], env=env, text=True).strip()
    require(version == deps["lean_version"], "Unexpected Lean version")
    if args.mathlib:
        mathlib = args.mathlib.resolve()
    else:
        mathlib = external / "mathlib4"
        cache = external / "mathlib-cache"
        require(not cache.exists(), "Fresh Mathlib download cache already exists: " + str(cache))
        cache.mkdir()
        env["MATHLIB_CACHE_DIR"] = str(cache)
        clone_pinned(deps["mathlib"]["url"], deps["mathlib"]["revision"], mathlib, env)
        for package in deps["packages"]:
            clone_pinned(package["url"], package["rev"], mathlib / ".lake/packages" / package["name"], env)
        require(sha(mathlib / "lake-manifest.json") == deps["mathlib"]["lake_manifest_sha256"],
                "Unexpected Mathlib Lake manifest")
        # Cache preparation uses only the new checkout and the fresh cache directory.
        run([str(toolchain / "bin/lake"), "exe", "cache", "get"], cwd=mathlib, env=env)
        require(sha(mathlib / "lake-manifest.json") == deps["mathlib"]["lake_manifest_sha256"],
                "Lake changed the pinned dependency manifest")
    run([sys.executable, str(ROOT / "scripts/replay.py"), "--expected-manifest-sha256", MANIFEST_PIN,
         "--toolchain", str(toolchain), "--mathlib", str(mathlib), "--preflight"], cwd=ROOT, env=env)
    record = {"status": "PASS", "source_manifest_sha256": MANIFEST_PIN,
              "toolchain": str(toolchain), "mathlib": str(mathlib),
              "reused_toolchain": bool(args.toolchain), "reused_mathlib": bool(args.mathlib)}
    (ROOT / "setup-result.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("Setup complete. Use the toolchain and Mathlib paths in setup-result.json for the replay.")


if __name__ == "__main__":
    main()
