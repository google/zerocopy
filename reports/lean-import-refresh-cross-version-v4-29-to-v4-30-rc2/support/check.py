#!/usr/bin/env python3
"""Read-only retained-evidence check for the two direct Lean versions."""
import hashlib
import json
from pathlib import Path

support = Path(__file__).resolve().parent
root = support.parent
v429 = support / "v429"
v430 = support / "v430"
prior_v430 = root.parent / "lean-same-server-dependency-generation-v4-30-0-rc2/support"
meta = json.loads((root / "REPORT.json").read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for subject in meta["subjects"][:2]:
    identity = subject["identity"]
    binary = Path(identity["local_executable"])
    assert sha(binary) == identity["executable_sha256"]
assert sha(v429 / "probe.py") == meta["subjects"][2]["identity"]["v429_probe_sha256"]
assert sha(v430 / "probe.py") == meta["subjects"][2]["identity"]["v430_probe_sha256"]
assert sha(v429 / "probe.py") == sha(v430 / "probe.py")

def inspect(folder, version, revision, preserve_old):
    d = json.loads((folder / "transcript.json").read_text())
    events = d["events"]
    kinds = lambda kind: [e for e in events if e["kind"] == kind]
    order = lambda kind: next(i for i, e in enumerate(events) if e["kind"] == kind)
    assert version in d["lean_version"] and revision in d["lean_version"]
    builds = kinds("build_dependency")
    assert [e["value"] for e in builds] == [3, 4]
    assert all(e["returncode"] == 0 for e in builds)
    assert d["old_olean_sha256"] == builds[0]["olean_sha256"]
    assert d["new_olean_sha256"] == builds[1]["olean_sha256"]
    assert d["old_olean_sha256"] != d["new_olean_sha256"]
    assert sha(folder / "fixture/Dep.olean") == d["new_olean_sha256"]
    if preserve_old:
        assert sha(folder / "fixture/Dep.old.olean") == d["old_olean_sha256"]
    assert sha(folder / "fixture/Dep.lean") == builds[1]["source_sha256"]
    proof = b"import Dep\ntheorem current : sharedValue = 3 := by\n  rfl\n"
    for name in ("OldOpen.lean", "NewOpen.lean"):
        assert (folder / "fixture" / name).read_bytes() == proof
    assert d["old_worker_goal_before"]["result"]["goals"] == []
    assert d["old_worker_goal_after"]["result"]["goals"] == []
    for key in ("new_worker_goal_same_server", "reopened_worker_goal_same_server"):
        assert d[key]["result"]["goals"] == ["⊢ sharedValue = 3"]
    for name, document_version in (("NewOpen.lean", 1), ("OldOpen.lean", 2)):
        assert any(batch["uri"].endswith("/" + name)
                   and batch.get("version") == document_version
                   and any("Tactic `rfl` failed" in item.get("message", "")
                           for item in batch["diagnostics"])
                   for batch in d["diagnostics"])
    assert d["fresh_batch_returncode"] == 1
    assert "Tactic `rfl` failed" in kinds("fresh_batch_after_dependency_rebuild")[0]["stdout"]
    assert len(kinds("server_start")) == len(kinds("server_exit")) == 1
    assert kinds("server_exit")[0]["returncode"] == 0
    assert order("old_worker_before_change") < order("artifact_changed") < order("old_worker_after_dependency_rebuild")
    assert order("old_worker_after_dependency_rebuild") < order("new_worker_same_server_after_dependency_rebuild")
    assert order("new_worker_same_server_after_dependency_rebuild") < order("closed_reopened_worker_after_dependency_rebuild")
    assert any(e.get("message", {}).get("method") == "workspace/didChangeWatchedFiles"
               for e in events[order("artifact_changed"):order("old_worker_after_dependency_rebuild")])
    if preserve_old:
        key = "old_worker_goal_after_new_worker_ready_and_delay"
        assert d[key]["result"]["goals"] == []
        assert order("new_worker_same_server_after_dependency_rebuild") < order("old_worker_after_new_worker_ready_and_delay")
        assert order("old_worker_after_new_worker_ready_and_delay") < order("closed_reopened_worker_after_dependency_rebuild")
        late = kinds("old_worker_after_new_worker_ready_and_delay")[0]
        assert late["delay_seconds"] == .5 and late["barrier"]["result"] == {}
    return d

inspect(v429, "4.29.0", "98dc76e3c0a9b856c9b98726b713fb04fab16740", True)
inspect(v430, "4.30.0-rc2", "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc", True)
inspect(prior_v430, "4.30.0-rc2", "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc", False)
print("PASS: identical pinned 4.29/4.30 scripts, old/new artifacts, delayed old-document queries, diagnostics and batch failure")
