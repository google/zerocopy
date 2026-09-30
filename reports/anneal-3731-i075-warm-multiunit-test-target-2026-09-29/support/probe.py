#!/usr/bin/env python3
"""Guarded, offline Charon baseline and warm repeat of a multi-unit test target."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture"
WORK = Path("/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/i075-warm-test-target")
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON, CARGO, RUSTC = TOOLS / "bin/charon", RUST / "cargo", RUST / "rustc"
MIN_MEMORY_PERCENT, MIN_DISK_BYTES = 20, 10 * 1024**3
MAX_RSS_KIB, MAX_OWNED_BYTES, MAX_SECONDS = 1024 * 1024, 100 * 1024**2, 60

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def size(root):
    return sum(p.stat().st_size for p in root.rglob("*") if p.is_file()) if root.exists() else 0

def headroom():
    vm = subprocess.check_output(["/usr/bin/vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    pages = {n: int(re.search(rf"Pages {n}:\s+(\d+)\.", vm).group(1))
             for n in ("free", "inactive", "speculative")}
    physical = int(subprocess.check_output(["/usr/sbin/sysctl", "-n", "hw.memsize"], text=True))
    return {"memory_estimate_percent": round(page * sum(pages.values()) * 100 / physical, 3),
            "free_disk_bytes": shutil.disk_usage(WORK.parent).free,
            "owned_scratch_bytes": size(WORK)}

def rss(pgid):
    total = 0
    for line in subprocess.check_output(["/bin/ps", "-axo", "pgid=,rss=,state="], text=True).splitlines():
        f = line.split()
        if len(f) == 3 and int(f[0]) == pgid and not f[2].startswith("Z"):
            total += int(f[1])
    return total

def reason(sample):
    if sample["memory_estimate_percent"] < MIN_MEMORY_PERCENT: return "memory"
    if sample["free_disk_bytes"] < MIN_DISK_BYTES: return "disk"
    if sample["owned_scratch_bytes"] > MAX_OWNED_BYTES: return "owned_scratch"
    if sample.get("rss_kib", 0) > MAX_RSS_KIB: return "rss"
    if sample.get("seconds", 0) > MAX_SECONDS: return "timeout"
    return None

def run(label, env):
    before = headroom()
    assert not reason(before), ("preflight", before)
    dest = WORK / f"{label}.llbc"
    assert not dest.exists()
    cmd = [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(dest), "--",
           "--manifest-path", str(WORK / "fixture/Cargo.toml"), "--test", "check",
           "--offline", "--locked", "-j", "1", "-v"]
    start = time.monotonic()
    p = subprocess.Popen(cmd, cwd=WORK / "fixture", env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, start_new_session=True)
    samples, stopped = [], None
    try:
        while True:
            sample = {"seconds": round(time.monotonic()-start, 4), **headroom(), "rss_kib": rss(p.pid)}
            samples.append(sample)
            stopped = reason(sample)
            if stopped or p.poll() is not None: break
            time.sleep(.1)
    finally:
        if stopped or p.poll() is None:
            os.killpg(p.pid, signal.SIGTERM)
            try: p.wait(timeout=2)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait(timeout=2)
    stdout, stderr = p.communicate(timeout=3)
    (HERE / "raw" / f"{label}.stdout").write_text(stdout)
    (HERE / "raw" / f"{label}.stderr").write_text(stderr)
    data = {"label": label, "argv": cmd, "cwd": str(WORK / "fixture"),
            "environment": {k: env.get(k) for k in ("RUSTUP_HOME", "CARGO_HOME", "CARGO_TARGET_DIR",
              "CARGO_NET_OFFLINE", "CARGO_BUILD_JOBS", "CARGO_INCREMENTAL", "RAYON_NUM_THREADS",
              "CHARON_TOOLCHAIN_IS_IN_PATH", "RUSTFLAGS")},
            "preflight": before, "samples": samples, "guard_stop": stopped,
            "exit_code": p.returncode, "elapsed_seconds": round(time.monotonic()-start, 4),
            "stdout_sha256": sha(HERE / "raw" / f"{label}.stdout"),
            "stderr_sha256": sha(HERE / "raw" / f"{label}.stderr"),
            "dest_path": str(dest), "dest_exists": dest.exists(),
            "dest_sha256": sha(dest) if dest.exists() else None,
            "driver_crates": re.findall(r"charon-driver rustc --crate-name ([^\s]+)", stderr)}
    if dest.exists():
        raw = json.loads(dest.read_text())
        data["crate_name"] = raw["translated"]["crate_name"]
        data["has_errors"] = raw.get("has_errors")
        shutil.copyfile(dest, HERE / "artifacts" / f"{label}.llbc")
    return data

def main():
    assert WORK.parent.is_dir() and not WORK.exists()
    assert all(p.exists() for p in (CHARON, CARGO, RUSTC, FIXTURE / "Cargo.lock"))
    WORK.mkdir()
    for name in ("raw", "artifacts"): (HERE / name).mkdir(exist_ok=True)
    shutil.copytree(FIXTURE, WORK / "fixture")
    assert not reason(headroom()), ("preflight", headroom())
    env = dict(os.environ)
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"):
        env.pop(key, None)
    env.update(RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
      CARGO_TARGET_DIR=str(WORK / "target"), CARGO_NET_OFFLINE="true", CARGO_BUILD_JOBS="1",
      CARGO_INCREMENTAL="0", RAYON_NUM_THREADS="1", CHARON_TOOLCHAIN_IS_IN_PATH="1",
      PATH=os.pathsep.join((str(RUST), str(TOOLS / "bin"), env.get("PATH", ""))),
      DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent / "lib"),
       str(RUST.parent / "lib/rustlib/aarch64-apple-darwin/lib"), env.get("DYLD_LIBRARY_PATH", ""))))
    result = {"tools": {name: {"path": str(path), "sha256": sha(path)} for name, path in
                       (("charon", CHARON), ("cargo", CARGO), ("rustc", RUSTC))},
              "fixture": {str(p.relative_to(FIXTURE)): sha(p) for p in FIXTURE.rglob("*") if p.is_file()},
              "parent_reference_head": "71fc3a50aadd50902bbbd22743ce884218af391e",
              "runs": []}
    try:
        for label in ("baseline", "warm_repeat"):
            cell = run(label, env)
            result["runs"].append(cell)
            (HERE / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
            if cell["guard_stop"] or cell["exit_code"] != 0: break
    finally:
        result["owned_scratch_bytes_before_cleanup"] = size(WORK)
        shutil.rmtree(WORK)
        result["work_removed"] = not WORK.exists()
        (HERE / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"runs": [{k:r[k] for k in ("label","exit_code","guard_stop","dest_sha256","crate_name","driver_crates")} for r in result["runs"]],
                      "owned_scratch_bytes_before_cleanup": result["owned_scratch_bytes_before_cleanup"]}))

if __name__ == "__main__": main()
