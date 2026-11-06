#!/usr/bin/env python3
"""Run the single Nix build with recorded resource guards and a hard timeout."""

import os
import re
import signal
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
LOG = HERE / "rust_build.log"
WORKDIR = Path.cwd()
NIX_PROFILE = "/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh"
BUILD_COMMAND = (
    f"source {NIX_PROFILE} && "
    "nix --extra-experimental-features 'nix-command flakes' build "
    ".#rust-toolchain --no-link --max-jobs 1 --cores 1"
)


def now():
    return datetime.now(timezone.utc).isoformat()


def capture(log, label, command):
    proc = subprocess.run(command, cwd=WORKDIR, text=True, capture_output=True)
    log.write(f"\n[{now()}] {label}: {' '.join(command)}\n")
    log.write(proc.stdout)
    log.write(proc.stderr)
    log.write(f"exit={proc.returncode}\n")
    log.flush()
    return proc


def health(log, label):
    df_h = capture(log, f"{label} disk", ["df", "-h", "/nix"])
    df_k = capture(log, f"{label} disk kilobytes", ["df", "-k", "/nix"])
    mem = capture(log, f"{label} memory", ["memory_pressure"])
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", mem.stdout)
    lines = df_k.stdout.strip().splitlines()
    try:
        available_kib = int(lines[-1].split()[3])
    except (IndexError, ValueError):
        available_kib = -1
    free_pct = int(match.group(1)) if match else -1
    log.write(f"resource_summary: memory_free={free_pct}% disk_available_kib={available_kib}\n")
    log.flush()
    return df_h.returncode == df_k.returncode == mem.returncode == 0, free_pct, available_kib


with LOG.open("w") as log:
    log.write(f"started_utc={now()}\nworkdir={WORKDIR}\n")
    log.write(f"command=/bin/bash -c {BUILD_COMMAND!r}\n")
    okay, free, disk = health(log, "before Rust build")
    if not okay or free < 35 or disk < 20 * 1024 * 1024:
        log.write("RESULT=SKIPPED_RESOURCE_GUARD\n")
        print("SKIPPED_RESOURCE_GUARD")
        raise SystemExit(2)

    log.write(f"\n[{now()}] BUILD BEGIN\n")
    log.flush()
    process = subprocess.Popen(
        ["/bin/bash", "-c", BUILD_COMMAND],
        cwd=WORKDIR,
        stdout=log,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    try:
        code = process.wait(timeout=300)
        timed_out = False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        code = process.returncode
        timed_out = True
    log.write(f"\n[{now()}] BUILD END exit={code} timed_out={timed_out}\n")
    okay, free, disk = health(log, "after Rust build")
    result = "TIMEOUT" if timed_out else ("BUILT" if code == 0 else "FAILED")
    if not okay or free < 30 or disk < 20 * 1024 * 1024:
        result += "_STOP_RESOURCE_GUARD"
    log.write(f"RESULT={result}\n")
    print(result)
    raise SystemExit(0 if result == "BUILT" else 1)
