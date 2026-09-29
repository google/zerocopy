#!/usr/bin/env python3
"""Validate the retained evidence without starting Lean."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
events = json.loads((HERE / "transcript.json").read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
assert [e["seq"] for e in events] == list(range(len(events)))
assert not [e for e in events if e["kind"] == "fatal"]
one = lambda kind: next(e for e in events if e["kind"] == kind)
subject = one("subject")
assert "4.30.0-rc2" in subject["version"]
assert subject["binary_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
disk = (HERE / "Nested.lean").read_bytes()
assert subject["disk_sha256"] == sha(disk)
assert one("stop")["returncode"] == 0 and one("stop")["stderr"] == ""
assert one("completed")["seq"] < one("stop")["seq"]

batches = {e["version"]: e for e in events if e["kind"] == "batch"}
assert sorted(batches) == [1, 2, 3]
assert [batches[v]["returncode"] for v in (1, 2, 3)] == [0, 1, 1]
assert batches[1]["sha256"] == sha(disk)
for v, label in ((1, "valid"), (2, "syntax"), (3, "unknown")):
    source = (HERE / "variants" / f"{v}-{label}.lean").read_bytes()
    assert batches[v]["sha256"] == sha(source)
assert "unexpected token ')'" in batches[2]["stdout"]
assert "unknown tactic" in batches[3]["stdout"]
assert batches[1]["stdout"] == batches[1]["stderr"] == ""

ready = {e["version"]:e for e in events if e["kind"] == "ready"}
assert sorted(ready) == [1, 2, 3, 4]
assert all(e["response"]["result"] == {} for e in ready.values())
assert [ready[v]["sha256"] for v in (1, 2, 3, 4)] == [
    batches[1]["sha256"], batches[2]["sha256"], batches[3]["sha256"], batches[1]["sha256"]]
assert len([e for e in events if e["kind"] == "start"]) == 1
changes = [e["message"] for e in events if e["kind"] == "send"
           and e["message"].get("method") == "textDocument/didChange"]
assert [m["params"]["textDocument"]["version"] for m in changes] == [2, 3, 4]
assert [sha(m["params"]["contentChanges"][0]["text"].encode()) for m in changes] == [
    batches[2]["sha256"], batches[3]["sha256"], batches[1]["sha256"]]
assert (HERE / "Nested.lean").read_bytes() == (HERE / "variants" / "1-valid.lean").read_bytes()

diagnostics = {}
for e in events:
    if e["kind"] == "recv" and e["message"].get("method") == "textDocument/publishDiagnostics":
        p = e["message"]["params"]
        diagnostics.setdefault(p["version"], []).append(p["diagnostics"])
assert sorted(diagnostics) == [1, 2, 3, 4]
assert diagnostics[1][-1] == diagnostics[4][-1] == []
assert any("unexpected token ')'" in d["message"] for d in diagnostics[2][-1])
assert any("unknown tactic" in d["message"] for d in diagnostics[3][-1])
assert all(d["severity"] == 1 for v in (2, 3) for d in diagnostics[v][-1])

goals = {(e["version"], e["name"]):e for e in events if e["kind"] == "goal"}
names = {"nested_before", "nested_mid", "nested_end", "outer_exact", "tail_before", "tail_after", "eof"}
assert len(goals) == 28 and all({n for v,n in goals if v == version} == names for version in (1,2,3,4))
assert all("error" not in e["response"] for e in goals.values())
def g(v,n):
    result = goals[v,n]["response"]["result"]
    return None if result is None else result["goals"]
outer = "n : Nat\nh : n = 0\n⊢ n + 0 = 0"
inner = "n : Nat\nh : n = 0\n⊢ n = 0"
with_hz = "n : Nat\nh : n = 0\nhz : n + 0 = 0\n⊢ n + 0 = 0"
for v in (1,4):
    assert [g(v,n) for n in ("nested_before","nested_mid","nested_end","outer_exact")] == [
        [outer],[inner],[],[with_hz]]
    assert goals[v,"nested_before"]["position"] == {"line":4,"character":4}
assert all(g(2,n) is None for n in ("nested_before","nested_mid","nested_end","outer_exact"))
assert goals[2,"nested_before"]["position"] == {"line":4,"character":4}
assert goals[2,"nested_end"]["position"] == {"line":4,"character":5}
assert [g(3,n) for n in ("nested_before","nested_mid","nested_end","outer_exact")] == [
    [outer],[outer],[outer],None]
for v in (1,2,3,4):
    assert [g(v,n) for n in ("tail_before","tail_after","eof")] == [["⊢ True"],[],[]]
print("PASS: 3 batch controls; 4 same-URI unsaved versions; 28 exact positions; diagnostics; clean server exit")
