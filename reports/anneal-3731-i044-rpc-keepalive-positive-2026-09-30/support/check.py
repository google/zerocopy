#!/usr/bin/env python3
"""Offline assertions over the retained positive run and published idle control."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
load = lambda name: json.loads((HERE / name).read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
oracle = load("oracle.json")
result = load("results.json")
baseline = load("baseline-expiry-results.json")

assert result["status"] == "completed" and result["stop_reason"] is None
assert result["oracle_prelaunch_sha256"] == sha((HERE / "oracle.json").read_bytes())
assert result["baseline_results_sha256"] == oracle["baseline_results_sha256"] == sha(
    (HERE / "baseline-expiry-results.json").read_bytes()
)
assert result["lean_sha256"] == oracle["lean_sha256"] == baseline["subject"]["lean_sha256"]
assert result["harness_sha256"] == baseline["subject"]["harness_sha256"]
assert sha(oracle["source"].encode()) == oracle["source_sha256"] == baseline["source_sha256"]
assert baseline["source"] == oracle["source"]
assert baseline["idle_seconds"] >= 42
assert baseline["expired"]["error"]["code"] == -32900
assert baseline["reference"] == result["reference"] == {"p": "0"}
old_events = baseline["wire_events"]
assert all(e["seq"] == i for i, e in enumerate(old_events))
old_before = next(i for i, e in enumerate(old_events) if e["kind"] == "server" and
                  e.get("message") == baseline["before"])
old_call = next(i for i, e in enumerate(old_events) if e["kind"] == "client" and
                e.get("message", {}).get("id") == 1004)
old_expired = next(i for i, e in enumerate(old_events) if e["kind"] == "server" and
                   e.get("message") == baseline["expired"])
assert old_before < old_call < old_expired
assert not any(e["kind"] == "client" for e in old_events[old_before + 1:old_call])
old_sid = baseline["connect"]["result"]["sessionId"]
assert old_events[old_call]["message"]["params"]["sessionId"] == old_sid
assert old_events[old_call]["message"]["params"]["params"] == baseline["reference"]
assert old_events[old_call]["message"]["params"]["method"] == oracle["rpc_method"]
assert old_events[old_call]["ms"] - old_events[old_before]["ms"] >= 42000

events = result["events"]
assert all(e["seq"] == i for i, e in enumerate(events))
client = [(i, e["message"]) for i, e in enumerate(events) if e["kind"] == "client"]
server = [(i, e["message"]) for i, e in enumerate(events) if e["kind"] == "server"]
def client_method(method, rid=None):
    matches = [(i, m) for i, m in client if m.get("method") == method and (rid is None or m.get("id") == rid)]
    assert len(matches) == 1, (method, rid, matches)
    return matches[0]
def server_id(rid):
    matches = [(i, m) for i, m in server if m.get("id") == rid and ("result" in m or "error" in m)]
    assert len(matches) == 1, (rid, matches)
    return matches[0]

uri = result["uri"]
sid = result["session_id"]
assert uri.startswith("file://") and uri.endswith("/work/Proof.lean")
_, did_open = client_method("textDocument/didOpen")
assert did_open["params"]["textDocument"] == {
    "uri": uri, "languageId": "lean", "version": 1, "text": oracle["source"]
}
for rid, method, stored in ((1000, "textDocument/waitForDiagnostics", "wait"),
                             (1001, "$/lean/rpc/connect", "connect"),
                             (1002, "$/lean/rpc/call", "rich"),
                             (1003, "$/lean/rpc/call", "before"),
                             (1004, "$/lean/rpc/call", "after")):
    ci, cm = client_method(method, rid)
    si, sm = server_id(rid)
    assert ci < si and sm == result[stored]
assert result["connect"]["result"]["sessionId"] == sid
assert result["rich"]["result"]["goals"][0]["hyps"][0]["type"]["tag"][0]["info"] == result["reference"]
for rid in (1003, 1004):
    _, call = client_method("$/lean/rpc/call", rid)
    params = call["params"]
    assert params == {"textDocument": {"uri": uri}, "position": {"line": 1, "character": 8},
                      "sessionId": sid, "method": oracle["rpc_method"], "params": result["reference"]}
assert result["before"]["result"]["exprExplicit"]["text"] == "Nat"
assert result["after"]["result"]["exprExplicit"]["text"] == "Nat"
assert "error" not in result["after"]

lo = result["interval_start_event_index"]
hi = result["interval_end_event_index"]
assert lo < hi and hi - lo == len(oracle["keepalive_schedule_seconds"]) == 5
assert events[hi]["kind"] == "client" and events[hi]["message"]["id"] == 1004
for event, kept, scheduled in zip(events[lo:hi], result["keepalives"], oracle["keepalive_schedule_seconds"]):
    assert event["kind"] == "client"
    assert event["message"] == {"jsonrpc": "2.0", "method": oracle["keepalive_notification"],
                                "params": {"uri": uri, "sessionId": sid}}
    assert kept["scheduled_seconds"] == scheduled
    assert scheduled <= kept["elapsed_seconds"] < scheduled + 1
assert result["interval_elapsed_seconds"] >= oracle["minimum_observation_seconds"] > baseline["idle_seconds"]
assert result["interval_elapsed_seconds"] < result["limits"]["maximum_total_seconds"]
assert all(b["elapsed_seconds"] - a["elapsed_seconds"] < 10 for a, b in zip(result["keepalives"], result["keepalives"][1:]))
assert result["interval_elapsed_seconds"] - result["keepalives"][-1]["elapsed_seconds"] < 10
assert not any(m.get("method") in {"textDocument/didChange", "textDocument/didClose", "textDocument/didOpen", "$/lean/rpc/release"}
               for i, m in client if lo <= i < hi)

before = result["tree_before_idle"]
after = result["tree_after_idle"]
assert before["count"] == after["count"] == 2
assert {p["pid"] for p in before["processes"]} == {p["pid"] for p in after["processes"]}
assert result["server_pid"] in {p["pid"] for p in after["processes"]}
assert result["server_exit_before_cleanup"] is None
assert result["server_exit_after_cleanup"] == 0
assert result["poststop_tree"]["count"] == 0
assert result["cleanup"]["work_exists_after"] is False
assert all(s["host"]["estimated_reclaimable_percent"] >= result["limits"]["minimum_live_reclaimable_percent"] and
           s["host"]["free_disk_bytes"] >= result["limits"]["minimum_disk_bytes"] and
           s["tree"]["rss_bytes"] <= result["limits"]["maximum_tree_rss_bytes"] and
           s["scratch_bytes"] <= result["limits"]["maximum_scratch_bytes"] and
           s["elapsed_seconds"] <= result["limits"]["maximum_total_seconds"]
           for s in result["samples"])
assert result["initial_preflight"]["estimated_reclaimable_percent"] > result["limits"]["minimum_start_reclaimable_percent"]
assert result["initial_preflight"]["free_disk_bytes"] > result["limits"]["minimum_disk_bytes"]

print(json.dumps({"status": "pass", "keepalives": len(result["keepalives"]),
                  "final_dereference_seconds": result["interval_elapsed_seconds"],
                  "baseline_expired_seconds": baseline["idle_seconds"],
                  "minimum_reclaimable_percent": min(s["host"]["estimated_reclaimable_percent"] for s in result["samples"]),
                  "maximum_tree_rss_bytes": max(s["tree"]["rss_bytes"] for s in result["samples"])}))
