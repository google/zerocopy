#!/usr/bin/env python3
"""One guarded offline Charon extraction of an independently retained generated file."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture"
WORK = HERE / "work"
OUT = HERE / "generated.llbc"
GENERATED = HERE / "generated.rs"
RESULT = HERE / "results.json"
RAW = HERE / "raw"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
CARGO = RUST / "cargo"
RUSTC = RUST / "rustc"
PINS = {
    "charon": "51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b",
    "cargo": "71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1",
    "rustc": "2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc",
}
MIN_ADMIT_RECLAIMABLE_PERCENT = 30.0
MIN_LIVE_RECLAIMABLE_PERCENT = 20.0
MIN_DISK_BYTES = 10 * 1024**3
MAX_PROCESS_GROUP_RSS_KIB = 512 * 1024
MAX_SCRATCH_BYTES = 100 * 1024**2
TIMEOUT_SECONDS = 15.0


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def headroom():
    raw = subprocess.check_output(["/usr/bin/vm_stat"], text=True, timeout=5)
    page_size = int(re.search(r"page size of (\d+) bytes", raw).group(1))
    pages = {name: int(re.search(rf"Pages {name}:\s+(\d+)\.", raw).group(1))
             for name in ("free", "inactive", "speculative")}
    physical = int(subprocess.check_output(
        ["/usr/sbin/sysctl", "-n", "hw.memsize"], text=True, timeout=5))
    return {"estimated_reclaimable_percent": round(
                100 * page_size * sum(pages.values()) / physical, 4),
            "free_disk_bytes": shutil.disk_usage(HERE).free,
            "page_size": page_size, "pages": pages,
            "physical_memory_bytes": physical}


def group_rss_kib(pgid):
    raw = subprocess.check_output(
        ["/bin/ps", "-axo", "pgid=,rss=,state="], text=True, timeout=5)
    return sum(int(cols[1]) for line in raw.splitlines()
               if len(cols := line.split()) == 3 and cols[0] == str(pgid)
               and not cols[2].startswith("Z"))


def scratch_bytes():
    if not WORK.exists():
        return 0
    return sum(path.stat().st_size for path in WORK.rglob("*") if path.is_file())


def sample(pgid, start):
    host = headroom()
    row = {"elapsed_seconds": round(time.monotonic() - start, 4),
           "host": host, "process_group_rss_kib": group_rss_kib(pgid) if pgid else 0,
           "scratch_bytes": scratch_bytes()}
    reason = None
    if host["estimated_reclaimable_percent"] < MIN_LIVE_RECLAIMABLE_PERCENT:
        reason = "memory_guard"
    elif host["free_disk_bytes"] < MIN_DISK_BYTES:
        reason = "disk_guard"
    elif row["process_group_rss_kib"] > MAX_PROCESS_GROUP_RSS_KIB:
        reason = "rss_guard"
    elif row["scratch_bytes"] > MAX_SCRATCH_BYTES:
        reason = "scratch_guard"
    return row, reason


def stop_group(proc):
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait(timeout=2)


def main():
    if any(path.exists() for path in (WORK, OUT, GENERATED, RESULT, RAW)):
        raise RuntimeError("work/output/generated/results/raw must be absent for one-shot run")
    binaries = {"charon": CHARON, "cargo": CARGO, "rustc": RUSTC}
    actual = {name: sha(path) for name, path in binaries.items()}
    if actual != PINS:
        raise RuntimeError(f"pinned tool hash mismatch: {actual}")
    fixture_hashes = {str(path.relative_to(FIXTURE)): sha(path)
                      for path in sorted(FIXTURE.rglob("*")) if path.is_file()}
    if set(fixture_hashes) != {"Cargo.toml", "Cargo.lock", "build.rs",
                               "generated_template.rs", "src/lib.rs"}:
        raise RuntimeError("fixture file set mismatch")
    preflight, admission_reason = sample(None, time.monotonic())
    if not admission_reason and preflight["host"]["estimated_reclaimable_percent"] <= MIN_ADMIT_RECLAIMABLE_PERCENT:
        admission_reason = "admission_memory"
    if admission_reason:
        result = {"schema": 1, "status": "admission_denied", "reason": admission_reason,
                  "observed_utc": datetime.now(timezone.utc).isoformat(),
                  "preflight": preflight, "tool_sha256": actual,
                  "fixture_sha256": fixture_hashes, "commands_launched": 0}
        RESULT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"status": result["status"], "reason": result["reason"]}))
        return
    shutil.copytree(FIXTURE, WORK)
    RAW.mkdir()
    env = dict(os.environ)
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER",
                "RUSTC_WORKSPACE_WRAPPER"):
        env.pop(key, None)
    env.update({
        "RUSTUP_HOME": str(TOOLS / "rustup"),
        "CARGO_HOME": str(TOOLS / "cargo"),
        "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
        "CARGO_NET_OFFLINE": "true", "CARGO_BUILD_JOBS": "1",
        "CARGO_INCREMENTAL": "0", "RAYON_NUM_THREADS": "1",
        "CARGO_TARGET_DIR": str(WORK / "target"),
        "PATH": os.pathsep.join((str(RUST), str(TOOLS / "bin"), env.get("PATH", ""))),
        "DYLD_LIBRARY_PATH": os.pathsep.join((str(RUST.parent / "lib"),
            str(RUST.parent / "lib/rustlib/aarch64-apple-darwin/lib"),
            env.get("DYLD_LIBRARY_PATH", ""))),
    })
    argv = [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(OUT), "--",
            "--manifest-path", str(WORK / "Cargo.toml"), "--package",
            "generated_span_probe", "--lib", "--offline", "--locked", "-v", "-j", "1"]
    selected_env = {key: env.get(key) for key in (
        "RUSTUP_HOME", "CARGO_HOME", "CHARON_TOOLCHAIN_IS_IN_PATH", "CARGO_NET_OFFLINE",
        "CARGO_BUILD_JOBS", "CARGO_INCREMENTAL", "RAYON_NUM_THREADS", "CARGO_TARGET_DIR",
        "RUSTFLAGS", "PATH", "DYLD_LIBRARY_PATH")}
    result = {"schema": 1, "status": "running", "observed_utc":
              datetime.now(timezone.utc).isoformat(), "tool_sha256": actual,
              "fixture_sha256": fixture_hashes, "preflight": preflight,
              "limits": {"minimum_admission_reclaimable_percent": MIN_ADMIT_RECLAIMABLE_PERCENT,
                         "minimum_live_reclaimable_percent": MIN_LIVE_RECLAIMABLE_PERCENT,
                         "minimum_free_disk_bytes": MIN_DISK_BYTES,
                         "maximum_process_group_rss_kib": MAX_PROCESS_GROUP_RSS_KIB,
                         "maximum_scratch_bytes": MAX_SCRATCH_BYTES,
                         "timeout_seconds": TIMEOUT_SECONDS},
              "command": {"argv": argv, "cwd": str(WORK), "environment": selected_env},
              "samples": [], "stop_reason": None, "output": None, "generated_source": None}
    proc = None
    start = time.monotonic()
    try:
        second_preflight, reason = sample(None, start)
        result["command_preflight"] = second_preflight
        if reason or second_preflight["host"]["estimated_reclaimable_percent"] <= MIN_ADMIT_RECLAIMABLE_PERCENT:
            result["status"] = "admission_denied"
            result["stop_reason"] = reason or "admission_memory"
        else:
            result["command"]["started_utc"] = datetime.now(timezone.utc).isoformat()
            result["command"]["start_monotonic_ns"] = time.monotonic_ns()
            proc = subprocess.Popen(argv, cwd=WORK, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, text=True, start_new_session=True)
            result["command"]["pid"] = proc.pid
            while True:
                row, reason = sample(proc.pid, start)
                result["samples"].append(row)
                if not reason and row["elapsed_seconds"] > TIMEOUT_SECONDS:
                    reason = "timeout"
                if reason or proc.poll() is not None:
                    break
                time.sleep(0.025)
            if reason:
                result["stop_reason"] = reason
                stop_group(proc)
            stdout, stderr = proc.communicate(timeout=3)
            stdout_path, stderr_path = RAW / "charon.stdout", RAW / "charon.stderr"
            stdout_path.write_text(stdout)
            stderr_path.write_text(stderr)
            result["command"].update({
                "ended_utc": datetime.now(timezone.utc).isoformat(),
                "end_monotonic_ns": time.monotonic_ns(), "exit": proc.returncode,
                "stdout_sha256": sha(stdout_path), "stderr_sha256": sha(stderr_path),
                "stdout_bytes": stdout_path.stat().st_size,
                "stderr_bytes": stderr_path.stat().st_size,
                "driver_lines": [line for line in stderr.splitlines()
                                 if "charon-driver rustc" in line],
            })
            result["status"] = "completed" if proc.returncode == 0 and not reason else "guard_or_command_failed"
        generated = list((WORK / "target").rglob("generated.rs"))
        result["generated_candidates"] = [str(path) for path in generated]
        if len(generated) == 1:
            shutil.copy2(generated[0], GENERATED)
            result["generated_source"] = {"sha256": sha(GENERATED), "bytes": GENERATED.stat().st_size,
                                          "original_path": str(generated[0])}
        if OUT.exists():
            result["output"] = {"sha256": sha(OUT), "bytes": OUT.stat().st_size}
    except Exception as exc:
        result["status"] = "error"
        result["error"] = repr(exc)
        if proc is not None:
            stop_group(proc)
    finally:
        result["postrun_host"] = headroom()
        result["postrun_process_group_rss_kib"] = group_rss_kib(proc.pid) if proc else 0
        shutil.rmtree(WORK, ignore_errors=True)
        result["cleanup"] = {"work_exists": WORK.exists()}
        RESULT.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    print(json.dumps({"status": result["status"], "stop_reason": result["stop_reason"],
                      "generated_source": result["generated_source"], "output": result["output"]},
                     indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
