#!/usr/bin/env python3
"""Check the Lake I038 protocol transcript without launching Lean or Lake."""
import hashlib
import json
from pathlib import Path

events = json.loads((Path(__file__).resolve().parent / "transcript.json").read_text())


def one(kind, label=None):
    xs = [e for e in events if e["kind"] == kind and (label is None or e.get("label") == label)]
    assert len(xs) == 1, (kind, label, len(xs))
    return xs[0]


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


assert "version 4.30.0-rc2" in one("lean_version")["value"]
assert "commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc" in one("lean_version")["value"]
assert "Lean version 4.30.0-rc2" in one("lake_version")["value"]
preflight = one("preflight")
assert preflight["memory_free_percent"] >= 25
assert preflight["disk_free_bytes"] >= 2 * 1024**3
assert one("server_start")["argv"] == ["$LAKE_BIN", "--keep-toolchain", "--no-cache", "serve"]
assert one("server_start")["cwd"] == "$FIXTURE"
assert one("fixture")["lean_toolchain"] == "leanprover/lean4:v4.30.0-rc2\n"
assert "lean_lib Dep" in one("fixture")["lakefile"]
assert "lean_lib Consumer" in one("fixture")["lakefile"]

old = one("artifact", "build_old_dependency")
new = one("artifact", "build_new_dependency")
unsaved = one("unsaved_producer_state")
materialized = one("materialized_state")
assert old["source_sha256"] == sha("def sharedValue : Nat := 3\n")
assert new["source_sha256"] == sha("def sharedValue : Nat := 4\n")
assert old["olean_sha256"] != new["olean_sha256"]
assert unsaved["disk_sha256"] == old["source_sha256"]
assert unsaved["buffer_sha256"] == new["source_sha256"]
assert unsaved["olean_sha256"] == old["olean_sha256"]
assert materialized["disk_sha256"] == materialized["buffer_sha256"] == new["source_sha256"]
assert materialized["olean_sha256"] == new["olean_sha256"]
assert materialized["proof_sha256"] == unsaved["proof_sha256"] == sha("import Dep\ntheorem current : sharedValue = 3 := by\n  rfl\n")

messages = [e["message"] for e in events if e["kind"] == "client_message"]
changes = [m for m in messages if m.get("method") == "textDocument/didChange"]
assert len(changes) == 1
assert changes[0]["params"]["textDocument"]["uri"].endswith("/Dep.lean")
assert changes[0]["params"]["textDocument"]["version"] == 2
assert changes[0]["params"]["contentChanges"] == [{"text": "def sharedValue : Nat := 4\n"}]
assert not any(m.get("method") == "textDocument/didSave" for m in messages)

# Match every labeled goal to its actual request and reply. Server-initiated
# requests can reuse client numeric IDs, so a reply must have no method.
def at(kind, label=None):
    return next(i for i, e in enumerate(events) if e["kind"] == kind and
                (label is None or e.get("label") == label))


goal_documents = {
    "consumer_before_unsaved_edit": ("Consumer.lean", 1),
    "consumer_after_unsaved_edit": ("Consumer.lean", 1),
    "new_consumer_while_producer_unsaved": ("FreshWhileProducerUnsaved.lean", 1),
    "old_consumer_after_materialization": ("Consumer.lean", 1),
    "new_consumer_after_materialization": ("FreshAfterMaterialization.lean", 1),
    "reopened_consumer_after_materialization": ("Consumer.lean", 2),
}
goal_events = [e for e in events if e["kind"] == "goal"]
assert {e["label"] for e in goal_events} == set(goal_documents)
assert len(goal_events) == len(goal_documents)
for e in goal_events:
    rid = e["response"]["id"]
    requests = [(i, row["message"]) for i, row in enumerate(events)
                if row["kind"] == "client_message" and
                row["message"].get("method") == "$/lean/plainGoal" and
                row["message"].get("id") == rid]
    replies = [(i, row["message"]) for i, row in enumerate(events)
               if row["kind"] == "server_message" and
               row["message"].get("id") == rid and "method" not in row["message"]]
    assert len(requests) == len(replies) == 1
    request_i, request = requests[0]
    reply_i, reply = replies[0]
    assert request_i < reply_i < at("goal", e["label"])
    assert reply == e["response"]
    basename, version = goal_documents[e["label"]]
    assert request["params"] == {
        "textDocument": {"uri": f"file://$FIXTURE/{basename}", "version": version},
        "position": {"line": 2, "character": 5}}


def message_at(method, basename=None):
    return next(i for i, e in enumerate(events) if e["kind"] == "client_message" and
                e["message"].get("method") == method and
                (basename is None or e["message"]["params"]["textDocument"]["uri"].endswith("/" + basename)))


watched_i = message_at("workspace/didChangeWatchedFiles")
assert events[watched_i]["message"]["params"] == {
    "changes": [{"uri": "file://$FIXTURE/Dep.lean", "type": 2}]}
assert at("artifact", "build_old_dependency") < at("goal", "consumer_before_unsaved_edit")
assert at("goal", "consumer_before_unsaved_edit") < message_at("textDocument/didChange") < at("unsaved_producer_state")
assert at("unsaved_producer_state") < at("goal", "consumer_after_unsaved_edit") < message_at("textDocument/didOpen", "FreshWhileProducerUnsaved.lean")
assert at("goal", "new_consumer_while_producer_unsaved") < at("command", "batch_with_old_artifact") < at("artifact", "build_new_dependency")
assert at("artifact", "build_new_dependency") < at("materialized_state") < watched_i < at("goal", "old_consumer_after_materialization")
assert at("goal", "old_consumer_after_materialization") < message_at("textDocument/didOpen", "FreshAfterMaterialization.lean") < at("goal", "new_consumer_after_materialization")
assert at("goal", "new_consumer_after_materialization") < at("command", "batch_with_new_artifact") < message_at("textDocument/didClose", "Consumer.lean")
assert message_at("textDocument/didClose", "Consumer.lean") < at("goal", "reopened_consumer_after_materialization")
barriers = [e for e in events if e["kind"] == "barrier"]
assert barriers and all(e["response"].get("result") == {} for e in barriers)

goals = {e["label"]: e["response"]["result"] for e in events if e["kind"] == "goal"}
for label in ("consumer_before_unsaved_edit", "consumer_after_unsaved_edit", "new_consumer_while_producer_unsaved", "old_consumer_after_materialization"):
    assert goals[label] == {"goals": [], "rendered": "no goals"}, label
for label in ("new_consumer_after_materialization", "reopened_consumer_after_materialization"):
    assert goals[label]["goals"] == ["⊢ sharedValue = 3"], label

for label in ("build_old_dependency", "batch_with_old_artifact", "build_new_dependency"):
    assert one("command", label)["exit_code"] == 0, label
for label in ("build_old_dependency", "build_new_dependency"):
    assert one("command", label)["argv"] == ["$LAKE_BIN", "--keep-toolchain", "--no-cache", "build", "Dep"]
batch_new = one("command", "batch_with_new_artifact")
assert batch_new["exit_code"] == 1
assert "Tactic `rfl` failed" in batch_new["stdout"]
for label in ("batch_with_old_artifact", "batch_with_new_artifact"):
    assert one("command", label)["argv"] == ["$LAKE_BIN", "--keep-toolchain", "--no-cache", "env", "lean", "--json", "Consumer.lean"]

diagnostics = [e["message"]["params"] for e in events if e["kind"] == "server_message" and e["message"].get("method") == "textDocument/publishDiagnostics"]
assert any(p["uri"].endswith("/Consumer.lean") and any("Imports are out of date" in d["message"] for d in p["diagnostics"]) for p in diagnostics)
assert any(p["uri"].endswith("/FreshAfterMaterialization.lean") and any("Tactic `rfl` failed" in d["message"] for d in p["diagnostics"]) for p in diagnostics)
outdated_i = next(i for i, e in enumerate(events) if e["kind"] == "server_message" and
                  e["message"].get("method") == "textDocument/publishDiagnostics" and
                  e["message"]["params"]["uri"].endswith("/Consumer.lean") and
                  any("Imports are out of date" in d["message"] for d in e["message"]["params"]["diagnostics"]))
fresh_error_i = next(i for i, e in enumerate(events) if e["kind"] == "server_message" and
                     e["message"].get("method") == "textDocument/publishDiagnostics" and
                     e["message"]["params"]["uri"].endswith("/FreshAfterMaterialization.lean") and
                     any("Tactic `rfl` failed" in d["message"] for d in e["message"]["params"]["diagnostics"]))
assert watched_i < outdated_i < at("goal", "old_consumer_after_materialization")
assert message_at("textDocument/didOpen", "FreshAfterMaterialization.lean") < fresh_error_i < at("goal", "new_consumer_after_materialization")
assert one("server_exit")["exit_code"] == 0
assert not any(e["kind"] == "fatal" for e in events)
print("Lake I038 transcript assertions passed")
