#!/usr/bin/env python3
"""Two independent reader-owned leases over the retained real A/B model families."""
import fcntl
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent.parent
sys.path.insert(0, str(PARENT / "anneal-3731-real-generation-gc-lease-v4-30-0-rc2" / "support"))
import publication_probe as P

SCRATCH = Path(os.environ.get(
    "I121_READER_SCRATCH",
    "/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/reader-owned-lease-run",
))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def family(path):
    return {rel: sha(path / rel) for rel in P.FILES if (path / rel).is_file()}


def classify(path):
    files = family(path)
    label = next((g for g in "AB" if files == P.EXPECTED[g]), "missing-or-mixed")
    return {"classification": label, "generation_id": P.IDS.get(label), "files": files}


def event(path, value):
    path.write_text(json.dumps({"time_ns": time.time_ns(), **value}, sort_keys=True) + "\n")


def await_event(path, process):
    deadline = time.monotonic() + 120
    while not path.exists():
        if process.poll() is not None:
            out, err = process.communicate()
            raise RuntimeError(f"reader exited before {path.name}: {process.returncode}: {out} {err}")
        if time.monotonic() > deadline:
            raise TimeoutError(str(path))
        time.sleep(.01)
    return json.loads(path.read_text())


def await_release(path):
    deadline = time.monotonic() + 120
    while not path.exists():
        if time.monotonic() > deadline:
            raise TimeoutError(str(path))
        time.sleep(.01)


def oracle(root, value, name):
    outcome = P.oracle(root / "generations/A", value, root / name)
    exact = classify(root / "generations/A")
    outcome["generation_classification"] = exact["classification"]
    outcome["generation_id"] = exact["generation_id"]
    return outcome


def reader(root, name):
    a = root / "generations/A"
    fd = os.open(a / "lease.lock", os.O_RDONLY)
    fcntl.flock(fd, fcntl.LOCK_SH)
    try:
        acquired = {"reader_pid": os.getpid(), "name": name, "lease_path": str(a / "lease.lock"), "shared_lock_acquired": True, "family": classify(a)}
        event(root / "gates" / f"{name}.acquired", acquired)
        await_release(root / "gates" / f"{name}.run")
        outcomes = [oracle(root, value, f"{name}-proof-{value}") for value in (1, 2)]
        result = {**acquired, "selected_after_publish": classify((root / "current").resolve(strict=True)), "oracles": outcomes}
        event(root / "gates" / f"{name}.done", result)
        await_release(root / "gates" / f"{name}.exit")
        print(json.dumps(result), flush=True)
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def gc_child(root):
    a = root / "generations/A"
    before = sum(p.stat().st_size for p in a.rglob("*") if p.is_file())
    selected = classify((root / "current").resolve(strict=True))
    fd = os.open(a / "lease.lock", os.O_RDONLY)
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            outcome, acquired = "deferred-reader-lease", False
        else:
            acquired = True
            if selected["classification"] == "B":
                shutil.rmtree(a)
                outcome = "removed"
            else:
                outcome = "deferred-selected"
            fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)
    after = sum(p.stat().st_size for p in a.rglob("*") if p.is_file()) if a.exists() else 0
    print(json.dumps({"time_ns": time.time_ns(), "gc_pid": os.getpid(), "selected": selected, "exclusive_lock_acquired": acquired, "outcome": outcome, "a_exists": a.exists(), "bytes_before": before, "bytes_after": after}), flush=True)


def gc(root):
    cmd = [sys.executable, str(Path(__file__).resolve()), "--gc", str(root)]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    assert p.returncode == 0, p.stderr
    return {"argv": cmd, "rc": p.returncode, "stdout": p.stdout, "stderr": p.stderr, **json.loads(p.stdout)}


def setup(root):
    if root.exists():
        shutil.rmtree(root)
    (root / "generations").mkdir(parents=True)
    (root / "gates").mkdir()
    for g in "AB":
        shutil.copytree(P.INPUTS / g, root / "generations" / g)
        assert classify(root / "generations" / g)["classification"] == g
    (root / "generations/A/lease.lock").touch()
    (root / "current").symlink_to("generations/A")


def run():
    assert set(P.FILES) == set(P.EXPECTED["A"]) == set(P.EXPECTED["B"])
    SCRATCH.mkdir(parents=True, exist_ok=True)
    root = SCRATCH / "two-readers"
    setup(root)
    initial = classify((root / "current").resolve(strict=True))
    readers = {}
    try:
        for name in ("reader-one", "reader-two"):
            cmd = [sys.executable, str(Path(__file__).resolve()), "--reader", str(root), name]
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, close_fds=True)
            readers[name] = (proc, cmd)
        acquired = {name: await_event(root / "gates" / f"{name}.acquired", readers[name][0]) for name in readers}
        assert acquired["reader-one"]["reader_pid"] != acquired["reader-two"]["reader_pid"]
        link = root / "current.next"
        link.symlink_to("generations/B")
        os.replace(link, root / "current")
        selected_b = classify((root / "current").resolve(strict=True))
        published_time_ns = time.time_ns()
        assert selected_b["classification"] == "B"
        gc_both = gc(root)
        assert gc_both["outcome"] == "deferred-reader-lease"
        one, one_cmd = readers["reader-one"]
        one.kill()
        one_out, one_err = one.communicate(timeout=10)
        killed_time_ns = time.time_ns()
        assert one.returncode == -signal.SIGKILL
        gc_after_kill = gc(root)
        assert gc_after_kill["outcome"] == "deferred-reader-lease"
        event(root / "gates/reader-two.run", {"released_by_pid": os.getpid()})
        two, two_cmd = readers["reader-two"]
        done = await_event(root / "gates/reader-two.done", two)
        assert done["oracles"][0]["rc"] == 0 and done["oracles"][1]["rc"] != 0
        gc_after_import = gc(root)
        assert gc_after_import["outcome"] == "deferred-reader-lease"
        event(root / "gates/reader-two.exit", {"released_by_pid": os.getpid()})
        two_out, two_err = two.communicate(timeout=15)
        assert two.returncode == 0, two_err
        gc_after_exit = gc(root)
        assert gc_after_exit["outcome"] == "removed"
        b_proof = P.oracle(root / "generations/B", 2, root / "after-b-new")
        assert b_proof["rc"] == 0
        result = {"reference_head": "c89f1410d4f1cfbd9b654ea5268b38f5c81e115e", "tool": {"lean": str(P.LEAN), "lean_sha256": sha(P.LEAN), "python": sys.version, "scratch": str(SCRATCH)}, "expected": P.EXPECTED, "generation_ids": P.IDS, "initial": initial, "acquired": acquired, "published_time_ns": published_time_ns, "selected_b": selected_b, "gc_both": gc_both, "killed_reader": {"argv": one_cmd, "pid": one.pid, "rc": one.returncode, "stdout": one_out, "stderr": one_err, "completed_time_ns": killed_time_ns}, "gc_after_kill": gc_after_kill, "reader_two_done": done, "gc_after_import": gc_after_import, "reader_two_exit": {"argv": two_cmd, "pid": two.pid, "rc": two.returncode, "stdout": two_out, "stderr": two_err}, "gc_after_exit": gc_after_exit, "b_proof_after_gc": b_proof, "a_exists_after_gc": (root / "generations/A").exists()}
        (HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({"outcomes": [result[k]["outcome"] for k in ("gc_both", "gc_after_kill", "gc_after_import", "gc_after_exit")], "generation_ids": P.IDS}))
    finally:
        for proc, _ in readers.values():
            if proc.poll() is None:
                proc.kill()
                proc.communicate(timeout=10)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--reader":
        reader(Path(sys.argv[2]), sys.argv[3])
    elif len(sys.argv) > 1 and sys.argv[1] == "--gc":
        gc_child(Path(sys.argv[2]))
    else:
        run()
