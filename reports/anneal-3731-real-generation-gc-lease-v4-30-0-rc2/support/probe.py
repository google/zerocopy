#!/usr/bin/env python3
"""Disposable cooperative GC over the retained real A/B model family."""
import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import publication_probe as P

HERE = Path(__file__).resolve().parent
SCRATCH = Path(os.environ.get("I121_SCRATCH", "/Users/josh/Codex/Meta/Data/20260929-142500-live-generation-gc-lease/run"))


def family(root):
    return {rel: P.sha(root / rel) for rel in P.FILES if (root / rel).is_file()}


def classify(root):
    files = family(root)
    label = next((x for x in "AB" if files == P.EXPECTED[x]), "missing-or-mixed")
    return {"path": str(root), "classification": label, "generation_id": P.IDS.get(label), "files": files}


def lean_oracle(model, value, work):
    outcome = P.oracle(model, value, work)
    snapshot = classify(model)
    outcome["generation_classification"] = snapshot["classification"]
    outcome["generation_id"] = snapshot["generation_id"]
    return outcome


def selected(root):
    target = (root / "current").resolve(strict=True)
    return classify(target)


def logical_bytes(root):
    return sum(p.stat().st_size for p in root.rglob("*") if p.is_file()) if root.exists() else 0


def setup(root):
    if root.exists():
        shutil.rmtree(root)
    (root / "generations").mkdir(parents=True)
    (root / "gates").mkdir()
    shutil.copytree(P.INPUTS / "A", root / "generations/A")
    shutil.copytree(P.INPUTS / "B", root / "generations/B")
    (root / "generations/A/lease.lock").touch()
    (root / "current").symlink_to("generations/A")
    assert selected(root)["classification"] == "A"
    assert classify(root / "generations/B")["classification"] == "B"


def publish_b(root):
    before = selected(root)
    tmp = root / "current.next"
    tmp.symlink_to("generations/B")
    os.replace(tmp, root / "current")
    after = selected(root)
    assert before["classification"] == "A" and after["classification"] == "B"
    return {"before": before, "after": after, "pointer": os.readlink(root / "current")}


def gate_wait(root, name, proc):
    marker = root / "gates" / (name + ".entered")
    deadline = time.monotonic() + 120
    while not marker.exists():
        if proc.poll() is not None:
            raise RuntimeError(f"reader exited before gate: {proc.returncode}")
        if time.monotonic() > deadline:
            raise TimeoutError(name)
        time.sleep(.01)


def gate_release(root, name):
    (root / "gates" / (name + ".release")).write_text(name)


def reader_child(root, label):
    gate = root / "gates" / (label + ".entered")
    gate.write_text(json.dumps({"wrapper_pid": os.getpid(), "status": "before Lean start"}))
    release = root / "gates" / (label + ".release")
    deadline = time.monotonic() + 120
    while not release.exists():
        if time.monotonic() > deadline:
            raise TimeoutError(label)
        time.sleep(.01)
    model = root / "generations/A"
    outcomes = [lean_oracle(model, value, root / f"{label}-proof-{value}") for value in (1, 2)]
    print(json.dumps({"wrapper_pid": os.getpid(), "gate": label, "generation_path": str(model), "observed_family": classify(model), "oracles": outcomes}), flush=True)


def gc_child(root):
    target = root / "generations/A"
    before = logical_bytes(target)
    selected_before = selected(root)
    fd = os.open(target / "lease.lock", os.O_RDONLY)
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            outcome = "deferred-lease-held"
            acquired = False
        else:
            acquired = True
            if selected_before["classification"] != "B":
                outcome = "deferred-selected"
            else:
                shutil.rmtree(target)
                outcome = "removed"
            fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)
    after = logical_bytes(target)
    print(json.dumps({"gc_pid": os.getpid(), "target": str(target), "selected_before": selected_before, "exclusive_lock_acquired": acquired, "outcome": outcome, "logical_bytes_before": before, "logical_bytes_after": after, "logical_bytes_reclaimed": before - after, "target_exists_after": target.exists()}), flush=True)


def gc(root):
    cmd = [sys.executable, str(Path(__file__).resolve()), "--gc", str(root)]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    assert p.returncode == 0, p.stderr
    return {"argv": cmd, "rc": p.returncode, "stderr": p.stderr, **json.loads(p.stdout)}


def run_case(label, leased):
    root = SCRATCH / label
    setup(root)
    a = root / "generations/A"
    initial = {"selected": selected(root), "old": lean_oracle(a, 1, root / "initial-old"), "new": lean_oracle(a, 2, root / "initial-new")}
    assert initial["old"]["rc"] == 0 and initial["new"]["rc"] != 0
    lease_fd = os.open(a / "lease.lock", os.O_RDONLY) if leased else None
    if leased:
        fcntl.flock(lease_fd, fcntl.LOCK_SH)
    lease = {"holder_pid": os.getpid(), "path": str(a / "lease.lock"), "acquired_shared": leased}
    server = P.Server(root / "server-old", a)
    first_goal = server.goal(open_file=True)
    assert first_goal.get("result", {}).get("rendered") == "no goals", first_goal
    child_cmd = [sys.executable, str(Path(__file__).resolve()), "--reader", str(root), "late-A"]
    reader = subprocess.Popen(child_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    gate_wait(root, "late-A", reader)
    gate_record = json.loads((root / "gates/late-A.entered").read_text())
    publication = publish_b(root)
    b = root / "generations/B"
    fresh_b_before_gc = {"old": lean_oracle(b, 1, root / "b-old"), "new": lean_oracle(b, 2, root / "b-new")}
    assert fresh_b_before_gc["old"]["rc"] != 0 and fresh_b_before_gc["new"]["rc"] == 0
    first_gc = gc(root)
    assert first_gc["outcome"] == ("deferred-lease-held" if leased else "removed")
    gate_release(root, "late-A")
    reader_out, reader_err = reader.communicate(timeout=120)
    assert reader.returncode == 0, reader_err
    late = {"argv": child_cmd, "pid": reader.pid, "rc": reader.returncode, "stderr": reader_err, **json.loads(reader_out)}
    late["selected_generation_at_release"] = P.IDS["B"]
    late["current_for_selected"] = False
    if leased:
        assert late["observed_family"]["classification"] == "A"
        assert late["oracles"][0]["rc"] == 0 and late["oracles"][1]["rc"] != 0
    else:
        assert late["observed_family"]["classification"] == "missing-or-mixed"
        assert late["oracles"][0]["rc"] != 0 and late["oracles"][1]["rc"] != 0
    try:
        post_goal = {"response": server.goal(), "error": None}
    except Exception as e:
        post_goal = {"response": None, "error": repr(e)}
    server_record = server.close()
    server_record["pinned_generation_id"] = P.IDS["A"]
    server_record["current_for_selected_after_publication"] = False
    if leased:
        fcntl.flock(lease_fd, fcntl.LOCK_UN)
        os.close(lease_fd)
    lease["released_after_server_exit"] = leased
    second_gc = gc(root) if leased else None
    if leased:
        assert second_gc["outcome"] == "removed"
    after = {"a_exists": a.exists(), "selected": selected(root), "fresh_a_old": lean_oracle(a, 1, root / "after-a-old"), "fresh_b_new": lean_oracle(b, 2, root / "after-b-new")}
    assert not after["a_exists"] and after["selected"]["classification"] == "B"
    assert after["fresh_a_old"]["rc"] != 0 and after["fresh_b_new"]["rc"] == 0
    return {"case": label, "initial": initial, "lease": lease, "open_server_initial_goal": first_goal, "gated_reader": gate_record, "publication": publication, "fresh_b_before_gc": fresh_b_before_gc, "first_gc": first_gc, "late_a_reader": late, "open_server_after_publication_and_gc": post_goal, "open_server": server_record, "second_gc": second_gc, "after": after}


def main():
    assert P.EXPECTED["A"] != P.EXPECTED["B"]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    result = {"tool": {"python": sys.version, "lean": str(P.LEAN), "lean_sha256": P.sha(P.LEAN), "scratch": str(SCRATCH)}, "expected": P.EXPECTED, "generation_ids": P.IDS, "leased": run_case("leased", True), "unleased": run_case("unleased", False)}
    (HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"leased_first_gc": result["leased"]["first_gc"]["outcome"], "leased_second_gc": result["leased"]["second_gc"]["outcome"], "unleased_first_gc": result["unleased"]["first_gc"]["outcome"], "generation_ids": P.IDS}))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--reader":
        reader_child(Path(sys.argv[2]), sys.argv[3])
    elif len(sys.argv) > 1 and sys.argv[1] == "--gc":
        gc_child(Path(sys.argv[2]))
    else:
        main()
