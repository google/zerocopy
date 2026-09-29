#!/usr/bin/env python3
"""Controlled APFS capture and subprocess stage-protocol experiments.

This is a research fixture, not Anneal implementation code. Run from any cwd:
python3 support/probe.py
"""

import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time


OUT = Path(__file__).with_name("raw-results.json")


def sha(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def atomic_link(directory, target):
    temp = directory / "next"
    if temp.is_symlink():
        temp.unlink()
    temp.symlink_to(target, target_is_directory=True)
    os.replace(temp, directory / "current")


def capture_probe(root):
    root.mkdir()
    for name, value in (("A", "0"), ("B", "1")):
        generation = root / name
        generation.mkdir()
        (generation / "left.txt").write_text("left-" + value)
        (generation / "right.txt").write_text("right-" + value)
    atomic_link(root, "A")
    left = (root / "current/left.txt").read_text()
    atomic_link(root, "B")
    right = (root / "current/right.txt").read_text()
    # Negative control without ABA: the changed left file is detected.
    changed_left = (root / "current/left.txt").read_text()
    assert changed_left != left
    # An adversarial A/B/A/B schedule makes sequential per-file validation pass.
    atomic_link(root, "A")
    validated_left = (root / "current/left.txt").read_text()
    atomic_link(root, "B")
    validated_right = (root / "current/right.txt").read_text()
    false_accept = left == validated_left and right == validated_right
    assert false_accept and (left, right) == ("left-0", "right-1")
    assert all([(root / g / p).read_text() for p in ("left.txt", "right.txt")] != [left, right]
               for g in ("A", "B"))
    # A single resolution gives a coherent directory across a later swap.
    atomic_link(root, "A")
    pinned = (root / "current").resolve(strict=True)
    pinned_left = (pinned / "left.txt").read_text()
    atomic_link(root, "B")
    pinned_right = (pinned / "right.txt").read_text()
    assert (pinned_left, pinned_right) == ("left-0", "right-0")
    return {
        "generations": {g: [(root / g / p).read_text() for p in ("left.txt", "right.txt")] for g in ("A", "B")},
        "mixed_read": [left, right],
        "no_aba_validation_detected_change": changed_left != left,
        "aba_revalidation": [validated_left, validated_right],
        "aba_false_accept": false_accept,
        "pinned_read_after_pointer_swap": [pinned_left, pinned_right],
        "pinned_generation": pinned.name,
    }


def backend(request_path, result_path, gate_path, mode):
    request = json.loads(Path(request_path).read_text())
    print("diagnostic-looking stdout: ERROR old-generation", flush=True)
    print("progress-looking stderr: 100%", file=sys.stderr, flush=True)
    Path(str(gate_path) + ".ready").write_text("ready")
    deadline = time.monotonic() + 15
    while not Path(gate_path).exists():
        if time.monotonic() > deadline:
            return 70
        time.sleep(0.005)
    if mode == "fail":
        Path(result_path).write_text('{"partial":true')
        return 23
    if mode == "malformed":
        Path(result_path).write_text('{"partial":true')
        return 0
    payload = {
        "request": request,
        "semantic_digest": sha(json.dumps(request["semantic"], sort_keys=True)),
        "status": "ok",
    }
    Path(result_path).write_text(json.dumps(payload, sort_keys=True))
    return 0


def start_stage(root, label, request, mode="ok"):
    path = root / label
    path.mkdir()
    req, result, gate = path / "request.json", path / "result.json", path / "gate"
    req.write_text(json.dumps(request, sort_keys=True))
    proc = subprocess.Popen(
        [sys.executable, str(Path(__file__).resolve()), "backend", str(req), str(result), str(gate), mode],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    deadline = time.monotonic() + 10
    while not Path(str(gate) + ".ready").exists():
        if proc.poll() is not None or time.monotonic() > deadline:
            raise RuntimeError("backend failed to become ready: " + label)
        time.sleep(0.005)
    return {"label": label, "proc": proc, "request": request, "result": result, "gate": gate}


def finish_stage(job):
    job["gate"].write_text("go")
    stdout, stderr = job["proc"].communicate(timeout=10)
    code = job["proc"].returncode
    raw_result = job["result"].read_text() if job["result"].exists() else None
    event = {"label": job["label"], "exit_code": code, "stdout": stdout,
             "stderr": stderr, "raw_result": raw_result}
    if code != 0:
        return event, None, "process-failed"
    try:
        parsed = json.loads(raw_result)
    except (TypeError, json.JSONDecodeError):
        return event, None, "invalid-result"
    if (parsed.get("request") != job["request"] or parsed.get("status") != "ok"
            or parsed.get("semantic_digest") != sha(json.dumps(job["request"]["semantic"], sort_keys=True))):
        return event, None, "invalid-result"
    return event, parsed, "ok"


class Engine:
    def __init__(self):
        self.epoch = 0
        self.published = None
        self.consumers = {}

    def begin(self, semantic, owners):
        self.epoch += 1
        self.consumers[self.epoch] = set(owners)
        return {"epoch": self.epoch, "semantic": semantic}

    def cancel(self, epoch, owner):
        self.consumers[epoch].discard(owner)

    def accept(self, parsed, status):
        if status != "ok":
            return "stage-error"
        request = parsed["request"]
        epoch = request["epoch"]
        if not self.consumers.get(epoch):
            return "no-consumers"
        if epoch != self.epoch:
            return "stale-generation"
        self.published = parsed
        return "published"


def jobs_probe(root):
    root.mkdir()
    events = []
    engine = Engine()
    semantics = {"subject": "cargo-target-X", "source": sha("Rust A"),
                 "model": sha("Lean model A"), "imports": sha("olean A"),
                 "proof": sha("by\n  rfl")}

    # Shared work: one client's cancellation must not kill another's job.
    shared = engine.begin(semantics, {"editor", "agent"})
    job = start_stage(root, "shared", shared)
    engine.cancel(shared["epoch"], "editor")
    event, parsed, status = finish_stage(job)
    disposition = engine.accept(parsed, status)
    assert disposition == "published" and engine.consumers[shared["epoch"]] == {"agent"}
    events.append({**event, "adapter_status": status, "disposition": disposition,
                   "remaining_consumers": sorted(engine.consumers[shared["epoch"]])})

    # Last consumer cancels, but the subprocess ignores cancellation and finishes.
    all_cancelled = engine.begin(semantics, {"editor", "agent"})
    job = start_stage(root, "all-cancelled", all_cancelled)
    engine.cancel(all_cancelled["epoch"], "editor")
    engine.cancel(all_cancelled["epoch"], "agent")
    event, parsed, status = finish_stage(job)
    disposition = engine.accept(parsed, status)
    assert disposition == "no-consumers"
    events.append({**event, "adapter_status": status, "disposition": disposition})

    # New model wins even when old worker completes last. Naive assignment loses.
    old = engine.begin(semantics, {"agent"})
    old_job = start_stage(root, "old-late", old)
    newer_semantics = {**semantics, "model": sha("Lean model B")}
    new = engine.begin(newer_semantics, {"agent"})
    new_job = start_stage(root, "new-first", new)
    new_event, new_result, new_status = finish_stage(new_job)
    new_disposition = engine.accept(new_result, new_status)
    old_event, old_result, old_status = finish_stage(old_job)
    old_disposition = engine.accept(old_result, old_status)
    naive_last_result = old_result
    assert new_disposition == "published" and old_disposition == "stale-generation"
    assert engine.published == new_result and naive_last_result != engine.published
    events.extend([{**new_event, "adapter_status": new_status, "disposition": new_disposition},
                   {**old_event, "adapter_status": old_status, "disposition": old_disposition}])

    # Process failure and malformed structured output never publish, despite logs.
    for label, mode, expected in (("failed-stage", "fail", "process-failed"),
                                  ("malformed-stage", "malformed", "invalid-result")):
        request = engine.begin(semantics, {"editor"})
        job = start_stage(root, label, request, mode)
        event, parsed, status = finish_stage(job)
        disposition = engine.accept(parsed, status)
        assert status == expected and disposition == "stage-error"
        events.append({**event, "adapter_status": status, "disposition": disposition})

    # Same structured engine for a one-shot batch and a fresh live query.
    batch_engine = Engine()
    live_engine = Engine()
    paired = []
    for shell, e in (("batch", batch_engine), ("live", live_engine)):
        request = e.begin(semantics, {shell})
        job = start_stage(root, shell, request)
        event, parsed, status = finish_stage(job)
        disposition = e.accept(parsed, status)
        assert disposition == "published"
        paired.append(parsed["semantic_digest"])
        events.append({**event, "adapter_status": status, "disposition": disposition})
    assert paired[0] == paired[1]
    return {"events": events, "out_of_order": {
        "new_epoch": new["epoch"], "old_epoch": old["epoch"],
        "fenced_published_digest": engine.published["semantic_digest"],
        "naive_last_digest": naive_last_result["semantic_digest"],
        "naive_wrong": naive_last_result != engine.published,
    }, "paired_batch_live_semantic_digests": paired}


def main():
    with tempfile.TemporaryDirectory(prefix="anneal-snapshot-probe-", dir=Path(__file__).parent) as scratch:
        root = Path(scratch)
        output = {
            "environment": {"python": sys.version, "platform": platform.platform(),
                            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
            "capture": capture_probe(root / "capture"),
            "jobs": jobs_probe(root / "jobs"),
        }
    OUT.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"capture_aba_false_accept": output["capture"]["aba_false_accept"],
                      "stale_completion_rejected": output["jobs"]["out_of_order"]["naive_wrong"],
                      "events": len(output["jobs"]["events"])}, sort_keys=True))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "backend":
        sys.exit(backend(*sys.argv[2:]))
    main()
