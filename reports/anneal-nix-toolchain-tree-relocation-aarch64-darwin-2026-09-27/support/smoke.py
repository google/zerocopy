#!/usr/bin/env python3
"""Bounded version and compile/run smoke probes from copied toolchain trees."""

import os
import re
import signal
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUST = HERE / "relocated_rust"
LEAN = HERE / "relocated_lean"
(HERE / "smoke.rs").write_text('fn main() { println!("relocated rust ok"); }\n')
(HERE / "Smoke.lean").write_text('def main : IO Unit := IO.println "relocated lean ok"\n')


def now():
    return datetime.now(timezone.utc).isoformat()


def command(log, argv, timeout=60):
    log.write(f"\n[{now()}] COMMAND: {' '.join(map(str, argv))}\n")
    log.flush()
    began = time.monotonic()
    process = subprocess.Popen(
        [str(x) for x in argv], cwd=HERE, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, start_new_session=True,
    )
    try:
        output, _ = process.communicate(timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            output, _ = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            output, _ = process.communicate()
        timed_out = True
    log.write(output)
    log.write(f"exit={process.returncode} timeout={timed_out} elapsed_sec={time.monotonic()-began:.3f}\n")
    log.flush()
    return process.returncode == 0 and not timed_out


def health(log, label):
    dfh = subprocess.run(["df", "-h", "/nix"], text=True, capture_output=True)
    dfk = subprocess.run(["df", "-k", "/nix"], text=True, capture_output=True)
    mem = subprocess.run(["memory_pressure"], text=True, capture_output=True)
    log.write(f"\n[{now()}] {label}: df -h /nix\n{dfh.stdout}{dfh.stderr}")
    log.write(f"\n[{now()}] {label}: df -k /nix\n{dfk.stdout}{dfk.stderr}")
    log.write(f"\n[{now()}] {label}: memory_pressure\n{mem.stdout}{mem.stderr}")
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", mem.stdout)
    try:
        disk = int(dfk.stdout.strip().splitlines()[-1].split()[3])
    except (IndexError, ValueError):
        disk = -1
    memory = int(match.group(1)) if match else -1
    log.write(f"resource_summary: memory_free={memory}% disk_available_kib={disk}\n")
    log.flush()
    return dfh.returncode == dfk.returncode == mem.returncode == 0, memory, disk


stages = [
    ("rust", [
        [RUST / "bin" / "rustc", "--version"],
        [RUST / "bin" / "cargo", "--version"],
        [RUST / "bin" / "rustc", "smoke.rs", "-o", "smoke_rust"],
        [HERE / "smoke_rust"],
    ]),
    ("lean", [
        [LEAN / "bin" / "lean", "--version"],
        [LEAN / "bin" / "lake", "--version"],
        [LEAN / "bin" / "lean", "--run", "Smoke.lean"],
    ]),
]

for name, commands in stages:
    with (HERE / f"smoke_{name}.log").open("w") as log:
        log.write(f"started_utc={now()}\n")
        okay, memory, disk = health(log, f"before {name} smoke")
        if not okay or memory < 35 or disk < 20 * 1024 * 1024:
            log.write("RESULT=SKIPPED_RESOURCE_GUARD\n")
            print(f"{name}: SKIPPED_RESOURCE_GUARD")
            break
        outcomes = [command(log, argv) for argv in commands]
        okay, memory, disk = health(log, f"after {name} smoke")
        result = "PASS" if all(outcomes) else "FAIL"
        if not okay or memory < 30 or disk < 20 * 1024 * 1024:
            result += "_STOP_RESOURCE_GUARD"
        log.write(f"RESULT={result}\n")
        print(f"{name}: {result}")
        if result.endswith("STOP_RESOURCE_GUARD"):
            break
