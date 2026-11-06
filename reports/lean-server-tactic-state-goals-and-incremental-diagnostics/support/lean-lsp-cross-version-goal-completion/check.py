#!/usr/bin/env python3
"""Offline assertions for the three retained direct Lean wire transcripts."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED_LEAN = "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
sources = {k: (ROOT / "work" / f"{k}.lean").read_text() for k in ("V1", "V2")}
hashes = {k: hashlib.sha256(v.encode()).hexdigest() for k, v in sources.items()}


def first(events, predicate):
    hits = [(i, e) for i, e in enumerate(events) if predicate(e)]
    assert len(hits) == 1, ("unique event", len(hits))
    return hits[0]


def client(method, request_id=None):
    return lambda e: e["kind"] == "client" and e.get("message", {}).get("method") == method and (request_id is None or e["message"].get("id") == request_id)


def response(request_id):
    return lambda e: e["kind"] == "server" and e.get("message", {}).get("id") == request_id and "method" not in e["message"]


for run in (1, 2, 3):
    events = json.loads((ROOT / f"transcript-run{run}.json").read_text())
    assert len(events) >= 35
    assert all(events[i]["ns"] <= events[i + 1]["ns"] for i in range(len(events) - 1))
    subject = first(events, lambda e: e["kind"] == "subject")[1]
    assert subject["binary_sha256"] == EXPECTED_LEAN
    assert "4.30.0-rc2" in subject["version"] and "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc" in subject["version"]
    for label in ("V1", "V2"):
        assert subject[label.lower() + "_sha256"] == hashes[label]
        batch = first(events, lambda e: e["kind"] == "batch" and e["label"] == label)[1]
        assert batch["source_sha256"] == hashes[label]
        assert batch["exit"] == (0 if label == "V1" else 1)
        assert batch["stderr"] == ""
        if label == "V1":
            assert batch["stdout"] == ""
        else:
            assert "Elab.synthPlaceholder" in batch["stdout"] and "Tactic.unsolvedGoals" in batch["stdout"]

    open_i, opened = first(events, client("textDocument/didOpen"))
    assert opened["message"]["params"]["textDocument"]["text"] == sources["V1"]
    assert opened["message"]["params"]["textDocument"]["version"] == 1
    wait1_i, wait1 = first(events, client("textDocument/waitForDiagnostics", 10))
    gate_i, _ = first(events, lambda e: e["kind"] == "marker" and e["name"] == "v1.entered")
    old_goal_i, old_goal = first(events, client("$/lean/plainGoal", 20))
    edit_i, edit = first(events, client("textDocument/didChange"))
    wait2_i, wait2 = first(events, client("textDocument/waitForDiagnostics", 11))
    marker2_i, _ = first(events, lambda e: e["kind"] == "marker" and e["name"] == "v2.entered")
    v2_diag_i, v2_diag = first(events, lambda e: e["kind"] == "server" and
        e.get("message", {}).get("method") == "textDocument/publishDiagnostics" and
        e["message"]["params"].get("version") == 2 and
        len(e["message"]["params"]["diagnostics"]) == 2)
    wait2_reply_i, wait2_reply = first(events, response(11))
    fresh_goal_i, fresh_goal = first(events, client("$/lean/plainGoal", 21))
    fresh_reply_i, fresh_reply = first(events, response(21))
    fresh_barrier_i, _ = first(events, lambda e: e["kind"] == "v2_goal_before_v1_release")
    release_i, release = first(events, lambda e: e["kind"] == "v1_released")
    wait1_reply_i, wait1_reply = first(events, response(10))
    old_reply_i, old_reply = first(events, response(20))
    old_late_wait_i, old_late_wait = first(events, client("textDocument/waitForDiagnostics", 12))
    old_late_reply_i, old_late_reply = first(events, response(12))
    assert open_i < wait1_i < gate_i < old_goal_i < edit_i < wait2_i < marker2_i < v2_diag_i < wait2_reply_i < fresh_goal_i < fresh_reply_i < fresh_barrier_i < release_i < wait1_reply_i < old_reply_i < old_late_wait_i < old_late_reply_i
    assert wait1["message"]["params"]["version"] == 1 and wait2["message"]["params"]["version"] == 2
    assert edit["message"]["params"]["textDocument"]["version"] == 2
    assert edit["message"]["params"]["contentChanges"] == [{"text": sources["V2"]}]
    assert old_goal["message"]["params"]["position"] == fresh_goal["message"]["params"]["position"]
    assert fresh_goal["message"]["params"]["textDocument"]["version"] == 1
    assert release["v2_marked_before_release"] is True
    assert all(x["message"].get("result") == {} for x in (wait2_reply, wait1_reply, old_late_reply))
    assert old_late_wait["message"]["params"]["version"] == 1
    assert old_reply["message"]["result"]["goals"] == ["⊢ True"]
    assert fresh_reply["message"]["result"]["goals"] == ["⊢ False"]
    assert "⊢ False" in v2_diag["message"]["params"]["diagnostics"][0]["message"]
    assert "unsolved goals" in v2_diag["message"]["params"]["diagnostics"][1]["message"]
    assert first(events, response(99))[1]["message"]["result"] is None
    assert first(events, lambda e: e["kind"] == "server_exit")[1]["exit"] == 0
    assert not any(e["kind"] in ("forced_exit", "response_timeout", "marker_timeout") for e in events)

print("PASS: three V2-marker/wait/current-goal barriers precede V1 wait and goal replies; batch controls and clean exits")
