#!/usr/bin/env python3
"""Relocate immutable toolchain outputs sequentially with resource checks."""

import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
STAGES = [
    (
        "lean",
        Path("/nix/store/wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2"),
        HERE / "relocated_lean",
    ),
    (
        "rust",
        Path("/nix/store/ms2vns33wg2qxzqdfdw37w6g9xay9jjc-rust-toolchain-aarch64-darwin-2026-05-31"),
        HERE / "relocated_rust",
    ),
]


def now():
    return datetime.now(timezone.utc).isoformat()


def capture(log, label, command):
    p = subprocess.run(command, text=True, capture_output=True)
    log.write(f"\n[{now()}] {label}: {' '.join(map(str, command))}\n")
    log.write(p.stdout)
    log.write(p.stderr)
    log.write(f"exit={p.returncode}\n")
    log.flush()
    return p


def health(log, label):
    dh = capture(log, label, ["df", "-h", "/nix"])
    dk = capture(log, label, ["df", "-k", "/nix"])
    mm = capture(log, label, ["memory_pressure"])
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", mm.stdout)
    try:
        disk = int(dk.stdout.strip().splitlines()[-1].split()[3])
    except (IndexError, ValueError):
        disk = -1
    memory = int(match.group(1)) if match else -1
    log.write(f"resource_summary: memory_free={memory}% disk_available_kib={disk}\n")
    log.flush()
    return dh.returncode == dk.returncode == mm.returncode == 0, memory, disk


for name, source, target in STAGES:
    with (HERE / f"copy_{name}.log").open("w") as log:
        log.write(f"started_utc={now()}\nsource={source}\ntarget={target}\n")
        okay, memory, disk = health(log, f"before {name} copy")
        if not okay or memory < 35 or disk < 20 * 1024 * 1024:
            log.write("RESULT=SKIPPED_RESOURCE_GUARD\n")
            print(f"{name}: SKIPPED_RESOURCE_GUARD")
            break
        if target.exists():
            log.write("RESULT=SKIPPED_TARGET_EXISTS\n")
            print(f"{name}: SKIPPED_TARGET_EXISTS")
            break
        log.write(f"\n[{now()}] COPY BEGIN: cp -a {source} {target}\n")
        log.flush()
        with subprocess.Popen(["cp", "-a", str(source), str(target)], stdout=log, stderr=subprocess.STDOUT) as p:
            code = p.wait()
        log.write(f"\n[{now()}] COPY END exit={code}\n")
        okay, memory, disk = health(log, f"after {name} copy")
        result = "COPIED" if code == 0 else "FAILED"
        if not okay or memory < 30 or disk < 20 * 1024 * 1024:
            result += "_STOP_RESOURCE_GUARD"
        log.write(f"RESULT={result}\n")
        print(f"{name}: {result}")
        if result != "COPIED":
            break
