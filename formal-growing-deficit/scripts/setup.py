#!/usr/bin/env python3
"""Fetch the exact official Linux toolchain and the nine pinned external packages."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = "lean-4.35.0-rc3-linux.tar.zst"
URL = "https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/" + ARCHIVE


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, help="Reuse an exact official installation instead of downloading")
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("This reproduction recipe pins the official Linux x86_64 distribution")
    deps = json.loads((ROOT / "dependency-pins.json").read_text())
    if args.toolchain:
        toolchain = args.toolchain.resolve()
    else:
        cache = ROOT / ".toolchain"
        cache.mkdir(exist_ok=True)
        archive = cache / ARCHIVE
        if not archive.exists():
            temporary = cache / (ARCHIVE + ".partial")
            urllib.request.urlretrieve(URL, temporary)
            if sha(temporary) != deps["lean_archive_sha256"]:
                raise RuntimeError("Official archive checksum mismatch")
            temporary.rename(archive)
        if sha(archive) != deps["lean_archive_sha256"]:
            raise RuntimeError("Official archive checksum mismatch")
        toolchain = cache / "lean-4.35.0-rc3-linux"
        if not toolchain.exists():
            subprocess.run(["tar", "--zstd", "-xf", str(archive), "-C", str(cache)], check=True)
    for name, expected in deps["official_tool_runtime_sha256"].items():
        if sha(toolchain / name) != expected:
            raise RuntimeError("Official tool/runtime checksum mismatch: " + name)
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("LEAN_", "ELAN_")) and key not in {"LD_PRELOAD", "LD_LIBRARY_PATH"}}
    env.update(PATH=str(toolchain / "bin") + ":/usr/bin:/bin", LEAN_NUM_THREADS="1")
    lake = str(toolchain / "bin/lake")
    manifest_pin = sha(ROOT / "lake-manifest.json")
    subprocess.run([lake, "env", "lean", "--version"], cwd=ROOT, env=env, check=True)
    subprocess.run([lake, "exe", "cache", "get"], cwd=ROOT, env=env, check=True)
    subprocess.run([lake, "build", "Cli", "Mathlib.Analysis.Normed.Group.Tannery"], cwd=ROOT, env=env, check=True)
    if sha(ROOT / "lake-manifest.json") != manifest_pin:
        raise RuntimeError("Lake changed the pinned package manifest")
    subprocess.run(["python3", str(ROOT / "scripts/replay.py"), "--toolchain", str(toolchain), "--preflight"],
                   cwd=ROOT, env=env, check=True)
    print("Setup complete. Run scripts/replay.py with the same --toolchain argument.")


if __name__ == "__main__":
    main()
