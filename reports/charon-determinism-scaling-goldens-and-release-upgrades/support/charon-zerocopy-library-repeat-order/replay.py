#!/usr/bin/env python3
"""Replay three offline, one-job Charon runs in an absent scratch directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
EXPECTED = json.loads((HERE / "observations.json").read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def free_percent():
    p = subprocess.run(["/usr/bin/memory_pressure", "-Q"], capture_output=True,
                       text=True, timeout=5)
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", p.stdout)
    if not match:
        raise RuntimeError("cannot read memory pressure; fail closed")
    return int(match.group(1))


def group_rss_kib(group):
    p = subprocess.run(["/bin/ps", "-axo", "pid=,pgid=,rss="], capture_output=True,
                       text=True, timeout=5)
    return sum(int(parts[2]) for line in p.stdout.splitlines()
               if len(parts := line.split()) == 3 and parts[1] == str(group))


def guard(work):
    if shutil.disk_usage(work).free < 15 * (1 << 30):
        raise RuntimeError("less than 15 GiB free disk")
    if free_percent() < 25:
        raise RuntimeError("less than 25% free memory")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path, help="google/zerocopy checkout")
    ap.add_argument("--tools", required=True, type=Path, help="cached .anneal-local-tools")
    ap.add_argument("--work", required=True, type=Path, help="absent scratch directory")
    args = ap.parse_args()
    repo, tools, work = (x.resolve() for x in (args.repo, args.tools, args.work))
    if work.exists():
        raise SystemExit("--work must be absent; no existing data will be removed")
    if shutil.disk_usage(work.parent).free < 15 * (1 << 30):
        raise SystemExit("less than 15 GiB free disk")
    if free_percent() < 25:
        raise SystemExit("less than 25% free memory")
    actual_tree = subprocess.check_output(["git", "-C", str(repo), "rev-parse",
                                           "HEAD:zerocopy"], text=True).strip()
    if actual_tree != EXPECTED["subject"]["zerocopy_tree_git_oid"]:
        raise SystemExit("source Git tree differs from retained subject")
    if subprocess.check_output(["git", "-C", str(repo), "status", "--porcelain", "--",
                                "zerocopy"], text=True).strip():
        raise SystemExit("source subtree is dirty")
    source = repo / "zerocopy"
    for rel, expected in EXPECTED["input_sha256"].items():
        if sha(source / rel) != expected:
            raise SystemExit(f"input hash mismatch: {rel}")
    binpath = tools / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
    libpath = binpath.parent / "lib"
    charon = tools / "bin/charon"
    binaries = {"charon": charon, "charon_driver": tools / "aeneas-release/charon-driver",
                "cargo": binpath / "cargo", "rustc": binpath / "rustc",
                "aeneas": tools / "aeneas-release/aeneas"}
    for name, path in binaries.items():
        if sha(path) != EXPECTED["tool_sha256"][name]:
            raise SystemExit(f"tool hash mismatch: {name}")
    work.mkdir()
    copied = work / "source"
    shutil.copytree(source, copied, ignore=shutil.ignore_patterns("target", ".git"))
    for n in (1, 2, 3):
        guard(work)
        run = work / f"run{n}"
        run.mkdir()
        dest = run / "zerocopy.llbc"
        env = dict(os.environ)
        env.update({"RUSTUP_HOME": str(tools / "rustup"),
                    "CARGO_HOME": str(tools / "cargo"),
                    "CARGO_TARGET_DIR": str(run / "target"),
                    "CARGO_BUILD_JOBS": "1", "CARGO_INCREMENTAL": "0",
                    "RAYON_NUM_THREADS": "1", "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                    "PATH": os.pathsep.join([str(binpath), str(tools / "bin"), env.get("PATH", "")]),
                    "DYLD_LIBRARY_PATH": os.pathsep.join([
                        str(libpath), str(libpath / "rustlib/aarch64-apple-darwin/lib")])})
        cmd = [str(charon), "cargo", "--preset", "aeneas", "--dest-file", str(dest),
               "--", "--manifest-path", str(copied / "Cargo.toml"),
               "--package", "zerocopy", "--lib", "--offline", "--locked", "-v"]
        with (run / "stdout.txt").open("wb") as stdout, (run / "stderr.txt").open("wb") as stderr:
            proc = subprocess.Popen(cmd, cwd=copied, env=env, stdin=subprocess.DEVNULL,
                                    stdout=stdout, stderr=stderr, start_new_session=True)
            started, max_rss, min_free, reason = time.monotonic(), 0, 100, None
            while proc.poll() is None:
                time.sleep(1)
                rss, free = group_rss_kib(proc.pid), free_percent()
                max_rss, min_free = max(max_rss, rss), min(min_free, free)
                if time.monotonic() - started > 180:
                    reason = "180-second timeout"
                elif rss > 3_500_000:
                    reason = "process-group RSS over 3.5 GiB"
                elif free < 15:
                    reason = "system free memory below 15%"
                elif shutil.disk_usage(work).free < 15 * (1 << 30):
                    reason = "disk free below 15 GiB"
                if reason:
                    os.killpg(proc.pid, signal.SIGKILL)
                    break
            code = proc.wait()
        (run / "result.json").write_text(json.dumps({"exit": code, "stop_reason": reason,
            "max_process_group_rss_kib": max_rss,
            "min_system_free_memory_percent": min_free,
            "llbc_bytes": dest.stat().st_size if dest.exists() else None,
            "llbc_sha256": sha(dest) if dest.exists() else None}, indent=2) + "\n")
        print(f"run{n}: exit={code}, stop={reason}, RSS KiB={max_rss}, free%={min_free}")
        if code != 0 or reason or not dest.exists():
            raise SystemExit(f"run{n} did not produce an accepted LLBC")
    subprocess.run([sys.executable, str(HERE / "compare.py"), str(work), "--expected",
                    str(HERE / "comparison.json")], check=True)


if __name__ == "__main__":
    main()
