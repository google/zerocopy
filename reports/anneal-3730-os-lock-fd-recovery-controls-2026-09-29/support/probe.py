#!/usr/bin/env python3
"""Bounded OS lock-cycle and child-only descriptor-exhaustion controls."""
import argparse
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
TIMEOUT = 5.0


def wait_for(path, timeout=TIMEOUT):
    deadline = time.monotonic() + timeout
    while not path.exists():
        if time.monotonic() >= deadline:
            raise TimeoutError(f"missing marker {path.name}")
        time.sleep(0.01)


def lock_child(args):
    with open(args.first, "a+") as first, open(args.second, "a+") as second:
        fcntl.flock(first, fcntl.LOCK_EX)
        Path(args.first_marker).write_text("held\n")
        wait_for(Path(args.go))
        Path(args.attempt_marker).write_text("attempting\n")
        fcntl.flock(second, fcntl.LOCK_EX)
        Path(args.second_marker).write_text("held\n")
    return 0


def spawn_lock(root, label, first, second, go):
    stem = root / label
    cmd = [sys.executable, __file__, "lock-child", str(first), str(second),
           str(stem) + ".first", str(stem) + ".attempt", str(stem) + ".second", str(go)]
    return subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE), {
        "first": Path(str(stem) + ".first"),
        "attempt": Path(str(stem) + ".attempt"),
        "second": Path(str(stem) + ".second"),
    }


def terminate(process):
    if process.poll() is None:
        process.kill()
    process.communicate(timeout=TIMEOUT)


def lock_cycle(root):
    prep, pub = root / "prepare.lock", root / "publish.lock"
    go = root / "cycle.go"
    a, ma = spawn_lock(root, "cycle-a", prep, pub, go)
    b, mb = spawn_lock(root, "cycle-b", pub, prep, go)
    try:
        wait_for(ma["first"])
        wait_for(mb["first"])
        go.write_text("go\n")
        wait_for(ma["attempt"])
        wait_for(mb["attempt"])
        time.sleep(0.2)
        blocked = a.poll() is None and b.poll() is None and not ma["second"].exists() and not mb["second"].exists()
        if not blocked:
            raise AssertionError("expected two-process lock-order cycle was absent")
        b.kill()
        b.communicate(timeout=TIMEOUT)
        wait_for(ma["second"])
        a.communicate(timeout=TIMEOUT)
        return {
            "both_first_locks_held": True,
            "both_second_locks_attempted": True,
            "both_blocked_before_kill": blocked,
            "victim_exit": b.returncode,
            "survivor_exit": a.returncode,
            "survivor_acquired_after_victim_kill": ma["second"].exists(),
        }
    finally:
        terminate(a)
        terminate(b)


def ordered_control(root):
    prep, pub = root / "ordered-prepare.lock", root / "ordered-publish.lock"
    go = root / "ordered.go"
    a, ma = spawn_lock(root, "ordered-a", prep, pub, go)
    b = None
    try:
        wait_for(ma["first"])
        b, mb = spawn_lock(root, "ordered-b", prep, pub, go)
        time.sleep(0.1)
        b_waited = not mb["first"].exists() and b.poll() is None
        go.write_text("go\n")
        a.communicate(timeout=TIMEOUT)
        b.communicate(timeout=TIMEOUT)
        return {
            "second_waited_for_first": b_waited,
            "first_acquired_both": ma["second"].exists(),
            "second_acquired_both": mb["second"].exists(),
            "exits": [a.returncode, b.returncode],
        }
    finally:
        terminate(a)
        if b is not None:
            terminate(b)


def fd_child(root):
    root = Path(root)
    limit = 32
    _, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    resource.setrlimit(resource.RLIMIT_NOFILE, (min(limit, hard), hard))
    current = root / "current"
    a = root / "A"
    b = root / "B"
    a.write_bytes(b"last-good-A\n")
    current.write_text("A\n")
    handles = []
    while True:
        try:
            handles.append(open(os.devnull, "rb"))
        except OSError as error:
            if error.errno != errno.EMFILE:
                raise
            break
    emfile_stage = False
    try:
        with open(b, "wb") as out:
            out.write(b"candidate-B\n")
    except OSError as error:
        emfile_stage = error.errno == errno.EMFILE
        if not emfile_stage:
            raise
    # A read would also require a descriptor, so inspect the already-known
    # pointer path after releasing descriptors; the attempted publish had no
    # opportunity to modify it.
    for handle in handles:
        handle.close()
    pointer_after_failure = current.read_text().strip()
    b.write_bytes(b"candidate-B\n")
    temporary = root / "current.tmp"
    temporary.write_text("B\n")
    os.replace(temporary, current)
    result = {
        "soft_nofile": resource.getrlimit(resource.RLIMIT_NOFILE)[0],
        "opened_extra_descriptors": len(handles),
        "stage_failed_emfile": emfile_stage,
        "pointer_after_failure": pointer_after_failure,
        "last_good_sha256": hashlib.sha256(a.read_bytes()).hexdigest(),
        "pointer_after_retry": current.read_text().strip(),
        "retry_artifact_sha256": hashlib.sha256(b.read_bytes()).hexdigest(),
    }
    print(json.dumps(result, sort_keys=True))
    return 0


def run():
    scratch = Path(os.environ.get("ANNEAL_PROBE_SCRATCH", tempfile.gettempdir()))
    if not scratch.is_dir() or not os.access(scratch, os.W_OK):
        raise RuntimeError("scratch directory is missing or unwritable")
    with tempfile.TemporaryDirectory(prefix="anneal-lock-fd-", dir=scratch) as temp:
        root = Path(temp)
        cycle = lock_cycle(root)
        ordered = ordered_control(root)
        fd_root = root / "fd"
        fd_root.mkdir()
        fd = subprocess.run([sys.executable, __file__, "fd-child", str(fd_root)],
                            capture_output=True, text=True, timeout=TIMEOUT, check=True)
        descriptor = json.loads(fd.stdout)
    assert cycle["both_blocked_before_kill"] and cycle["victim_exit"] == -signal.SIGKILL
    assert cycle["survivor_exit"] == 0 and cycle["survivor_acquired_after_victim_kill"]
    assert ordered["second_waited_for_first"] and ordered["exits"] == [0, 0]
    assert ordered["first_acquired_both"] and ordered["second_acquired_both"]
    assert descriptor["stage_failed_emfile"] and descriptor["pointer_after_failure"] == "A"
    assert descriptor["pointer_after_retry"] == "B"
    result = {
        "platform": sys.platform,
        "python": sys.version.split()[0],
        "lock_order_cycle": cycle,
        "consistent_order": ordered,
        "fd_exhaustion": descriptor,
    }
    (HERE / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", nargs="?", default="run", choices=("run", "lock-child", "fd-child"))
    parser.add_argument("first", nargs="?")
    parser.add_argument("second", nargs="?")
    parser.add_argument("first_marker", nargs="?")
    parser.add_argument("attempt_marker", nargs="?")
    parser.add_argument("second_marker", nargs="?")
    parser.add_argument("go", nargs="?")
    args = parser.parse_args()
    if args.mode == "lock-child":
        sys.exit(lock_child(args))
    if args.mode == "fd-child":
        sys.exit(fd_child(args.first))
    run()
