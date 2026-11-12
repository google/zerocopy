#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Run empirical Linux subprocess-tree supervision and reproduce.py signal probes."""

import fcntl
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time


HERE = Path(__file__).resolve().parent


def is_pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    status_path = Path(f"/proc/{pid}/status")
    if status_path.is_file():
        for line in status_path.read_text().splitlines():
            if line.startswith("State:") and "Z" in line:
                return False
    return True


def is_file_locked(path: Path) -> bool:
    if not path.exists():
        return False
    fd = os.open(path, os.O_RDWR)
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        fcntl.flock(fd, fcntl.LOCK_UN)
        return False
    finally:
        os.close(fd)


def wait_for_pid_file(path: Path, timeout: float = 5.0) -> int:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if path.is_file():
            text = path.read_text().strip()
            if text.isdigit():
                return int(text)
        time.sleep(0.005)
    raise RuntimeError(f"Timed out waiting for PID file {path}")


def cleanup_pid(pid: int) -> None:
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 2.0
    while is_pid_alive(pid) and time.monotonic() < deadline:
        time.sleep(0.005)


def run_reproduce_experiments(probe_bin: Path, work_dir: Path) -> list[dict]:
    results = []

    # Case E1: Unfixed reproduce.py (subprocess.run with timeout, no process_group=0).
    e1_dir = work_dir / "e1"
    e1_dir.mkdir(parents=True, exist_ok=True)
    lock_e1 = e1_dir / "case.lock"
    ready_e1 = e1_dir / "grandchild.pid"
    wrapper_e1 = e1_dir / "reproduce_e1.py"
    wrapper_e1.write_text(
        f"""import subprocess, sys
try:
    subprocess.run(
        [{json.dumps(str(probe_bin))}, "worker-parent", {json.dumps(str(lock_e1))}, {json.dumps(str(ready_e1))}, "0", "0"],
        timeout=0.15,
        stdin=subprocess.DEVNULL,
    )
except subprocess.TimeoutExpired:
    sys.exit(124)
"""
    )
    proc_e1 = subprocess.Popen([sys.executable, str(wrapper_e1)])
    p2_e1 = wait_for_pid_file(ready_e1)
    rc_e1 = proc_e1.wait(timeout=5.0)
    p2_alive_e1 = is_pid_alive(p2_e1)
    locked_e1 = is_file_locked(lock_e1)
    cleanup_pid(p2_e1)
    results.append(
        {
            "case": "E1_unfixed_reproduce_timeout",
            "exit_code": rc_e1,
            "p2_alive_after_exit": p2_alive_e1,
            "lock_held_by_orphan_after_exit": locked_e1,
        }
    )

    # Case E2: Naive process_group=0 reproduce.py WITHOUT SIGINT forwarding when SIGINT hits reproduce.py.
    e2_dir = work_dir / "e2"
    e2_dir.mkdir(parents=True, exist_ok=True)
    lock_e2 = e2_dir / "case.lock"
    ready_e2 = e2_dir / "grandchild.pid"
    p1_file_e2 = e2_dir / "p1.pid"
    wrapper_e2 = e2_dir / "reproduce_e2.py"
    wrapper_e2.write_text(
        f"""import pathlib, subprocess, sys
p = subprocess.Popen(
    [{json.dumps(str(probe_bin))}, "worker-parent", {json.dumps(str(lock_e2))}, {json.dumps(str(ready_e2))}, "0", "0"],
    process_group=0,
    stdin=subprocess.DEVNULL,
)
pathlib.Path({json.dumps(str(p1_file_e2))}).write_text(str(p.pid))
try:
    p.wait(timeout=10.0)
except subprocess.TimeoutExpired:
    sys.exit(124)
"""
    )
    proc_e2 = subprocess.Popen(
        [sys.executable, str(wrapper_e2)],
        process_group=0,
    )
    p2_e2 = wait_for_pid_file(ready_e2)
    p1_e2 = wait_for_pid_file(p1_file_e2)
    time.sleep(0.03)
    # Send SIGINT to reproduce_e2.py's process group (simulating terminal foreground Ctrl-C
    # when child was placed in its own background process group).
    os.killpg(proc_e2.pid, signal.SIGINT)
    rc_e2 = proc_e2.wait(timeout=5.0)
    p1_alive_e2 = is_pid_alive(p1_e2)
    p2_alive_e2 = is_pid_alive(p2_e2)
    locked_e2 = is_file_locked(lock_e2)
    try:
        os.killpg(p1_e2, signal.SIGKILL)
    except ProcessLookupError:
        pass
    cleanup_pid(p1_e2)
    cleanup_pid(p2_e2)
    results.append(
        {
            "case": "E2_pgroup_reproduce_sigint_without_forwarding",
            "exit_code": rc_e2,
            "p1_alive_after_sigint": p1_alive_e2,
            "p2_alive_after_sigint": p2_alive_e2,
            "lock_held_by_orphan_after_sigint": locked_e2,
        }
    )

    # Case E3a & E3b: Fixed reproduce.py with process_group=0, signal forwarding, and killpg on timeout/exit.
    fixed_template = """import os, pathlib, signal, subprocess, sys, time

def kill_tree(pgid):
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 2.0
    while time.monotonic() < deadline:
        try:
            os.killpg(pgid, 0)
        except ProcessLookupError:
            break
        time.sleep(0.002)

p = subprocess.Popen(
    [{probe_bin}, "worker-parent", {lock_file}, {ready_file}, "0", "0"],
    process_group=0,
    stdin=subprocess.DEVNULL,
)
pathlib.Path({p1_file}).write_text(str(p.pid))

def forward_signal(signum, _frame):
    try:
        os.killpg(p.pid, signum)
    except ProcessLookupError:
        pass
    kill_tree(p.pid)
    p.wait()
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)

signal.signal(signal.SIGINT, forward_signal)
signal.signal(signal.SIGTERM, forward_signal)

try:
    rc = p.wait(timeout={timeout})
except subprocess.TimeoutExpired:
    kill_tree(p.pid)
    p.wait()
    sys.exit(124)
finally:
    kill_tree(p.pid)
sys.exit(rc)
"""

    # E3a: Fixed reproduce.py under timeout (0.15s)
    e3a_dir = work_dir / "e3a"
    e3a_dir.mkdir(parents=True, exist_ok=True)
    lock_e3a = e3a_dir / "case.lock"
    ready_e3a = e3a_dir / "grandchild.pid"
    p1_file_e3a = e3a_dir / "p1.pid"
    wrapper_e3a = e3a_dir / "reproduce_e3a.py"
    wrapper_e3a.write_text(
        fixed_template.format(
            probe_bin=json.dumps(str(probe_bin)),
            lock_file=json.dumps(str(lock_e3a)),
            ready_file=json.dumps(str(ready_e3a)),
            p1_file=json.dumps(str(p1_file_e3a)),
            timeout="0.15",
        )
    )
    proc_e3a = subprocess.Popen([sys.executable, str(wrapper_e3a)], process_group=0)
    p2_e3a = wait_for_pid_file(ready_e3a)
    p1_e3a = wait_for_pid_file(p1_file_e3a)
    rc_e3a = proc_e3a.wait(timeout=5.0)
    results.append(
        {
            "case": "E3a_fixed_pgroup_reproduce_timeout",
            "exit_code": rc_e3a,
            "p1_alive_after_exit": is_pid_alive(p1_e3a),
            "p2_alive_after_exit": is_pid_alive(p2_e3a),
            "lock_held_by_orphan_after_exit": is_file_locked(lock_e3a),
        }
    )

    # E3b: Fixed reproduce.py under interactive SIGINT
    e3b_dir = work_dir / "e3b"
    e3b_dir.mkdir(parents=True, exist_ok=True)
    lock_e3b = e3b_dir / "case.lock"
    ready_e3b = e3b_dir / "grandchild.pid"
    p1_file_e3b = e3b_dir / "p1.pid"
    wrapper_e3b = e3b_dir / "reproduce_e3b.py"
    wrapper_e3b.write_text(
        fixed_template.format(
            probe_bin=json.dumps(str(probe_bin)),
            lock_file=json.dumps(str(lock_e3b)),
            ready_file=json.dumps(str(ready_e3b)),
            p1_file=json.dumps(str(p1_file_e3b)),
            timeout="10.0",
        )
    )
    proc_e3b = subprocess.Popen([sys.executable, str(wrapper_e3b)], process_group=0)
    p2_e3b = wait_for_pid_file(ready_e3b)
    p1_e3b = wait_for_pid_file(p1_file_e3b)
    time.sleep(0.03)
    os.killpg(proc_e3b.pid, signal.SIGINT)
    rc_e3b = proc_e3b.wait(timeout=5.0)
    results.append(
        {
            "case": "E3b_fixed_pgroup_reproduce_sigint",
            "exit_code": rc_e3b,
            "p1_alive_after_sigint": is_pid_alive(p1_e3b),
            "p2_alive_after_sigint": is_pid_alive(p2_e3b),
            "lock_held_by_orphan_after_sigint": is_file_locked(lock_e3b),
        }
    )

    return results


def main() -> None:
    rustc = shutil.which("rustc") or "rustc"
    with tempfile.TemporaryDirectory(prefix="anneal-proc-tree-probe-") as tmp:
        tmp_path = Path(tmp)
        probe_bin = tmp_path / "supervisor_probe"
        subprocess.run(
            [rustc, "--edition=2024", "-O", str(HERE / "supervisor_probe.rs"), "-o", str(probe_bin)],
            check=True,
        )
        rust_out = subprocess.run(
            [str(probe_bin), "run-all", str(tmp_path / "work")],
            check=True,
            capture_output=True,
            text=True,
        )
        rust_strategies = json.loads(rust_out.stdout.strip())
        reproduce_cases = run_reproduce_experiments(probe_bin, tmp_path / "repro")

    payload = {
        "rust_supervisor_strategies": rust_strategies,
        "reproduce_py_cases": reproduce_cases,
    }
    (HERE / "results.json").write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
