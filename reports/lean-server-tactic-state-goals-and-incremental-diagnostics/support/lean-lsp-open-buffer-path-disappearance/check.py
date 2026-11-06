#!/usr/bin/env python3
"""Offline check of three direct Lean open-buffer/path-lifecycle records."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HASH = "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
source = {n: (ROOT / "work" / f"Batch-{n}.lean").read_text() for n in (1, 2, 3)}
digest = {n: hashlib.sha256(text.encode()).hexdigest() for n, text in source.items()}


def one(events, predicate):
    hits = [(i, e) for i, e in enumerate(events) if predicate(e)]
    assert len(hits) == 1, len(hits)
    return hits[0]


for run in (1, 2, 3):
    data = (ROOT / f"transcript-run{run}.json").read_text()
    assert "/Users/" not in data and "$WORK" in data
    events = json.loads(data)
    assert len(events) >= 90
    assert all(events[i]["ns"] <= events[i + 1]["ns"] for i in range(len(events) - 1))
    subject = one(events, lambda e: e["kind"] == "subject")[1]
    assert subject["binary_sha256"] == HASH
    assert "4.30.0-rc2" in subject["version"]
    assert subject["source_sha256"] == {str(n): digest[n] for n in source}
    for n in source:
        e = one(events, lambda e, n=n: e["kind"] == "batch" and e["label"] == f"source-{n}")[1]
        assert e["source_sha256"] == digest[n] and e["exit"] == 1
        assert f"⊢ {n} = {n}" in e["stdout"]
    deleted = one(events, lambda e: e["kind"] == "batch" and e["label"] == "deleted-path")[1]
    assert deleted["source_sha256"] is None and deleted["exit"] != 0 and "no such file or directory" in deleted["stderr"]
    recreated = one(events, lambda e: e["kind"] == "batch" and e["label"] == "recreated-C")[1]
    assert recreated["source_sha256"] == digest[3] and recreated["exit"] == 1 and "⊢ 3 = 3" in recreated["stdout"]

    states = {e["label"]: (i, e) for i, e in enumerate(events) if e["kind"] == "disk_state"}
    assert len(states) == 8
    expected = [
        ("initial", True, 1), ("unsaved-B-disk-A", True, 1),
        ("external-C-no-watcher", True, 3), ("saved-B-over-C", True, 2),
        ("renamed-old-absent", False, None), ("renamed-new-B", True, 2),
        ("deleted-open-new-uri", False, None), ("recreated-C", True, 3),
    ]
    assert [states[label][0] for label, _, _ in expected] == sorted(states[label][0] for label, _, _ in expected)
    for label, exists, n in expected:
        e = states[label][1]
        assert e["exists"] is exists and e["sha256"] == (digest[n] if n else None)
    assert states["external-C-no-watcher"][1]["intended_buffer_version"] == 2
    assert states["deleted-open-new-uri"][1]["intended_buffer_version"] == 1

    sent = [(i, e["message"]) for i, e in enumerate(events) if e["kind"] == "client"]
    got = {e["message"]["id"]: (i, e["message"]) for i, e in enumerate(events) if e["kind"] == "server" and "id" in e.get("message", {})}
    def sent_one(method, rid=None):
        hits = [(i, m) for i, m in sent if m.get("method") == method and (rid is None or m.get("id") == rid)]
        assert len(hits) == 1, (method, rid, len(hits))
        return hits[0]
    opens = [(i, m) for i, m in sent if m.get("method") == "textDocument/didOpen"]
    assert len(opens) == 3
    assert [(m["params"]["textDocument"]["version"], m["params"]["textDocument"]["text"]) for _, m in opens] == [(1, source[1]), (1, source[2]), (2, source[3])]
    edit_i, edit = sent_one("textDocument/didChange")
    assert edit["params"]["textDocument"]["version"] == 2 and edit["params"]["contentChanges"] == [{"text": source[2]}]
    save_i, _ = sent_one("textDocument/didSave")
    assert states["external-C-no-watcher"][0] < save_i < states["saved-B-over-C"][0]
    watched = [(i, m) for i, m in sent if m.get("method") == "workspace/didChangeWatchedFiles"]
    assert len(watched) == 3
    assert [[c["type"] for c in m["params"]["changes"]] for _, m in watched] == [[2], [3, 1], [3]]
    assert states["external-C-no-watcher"][0] < got[22][0] < watched[0][0] < got[23][0]
    assert states["renamed-old-absent"][0] < watched[1][0] < got[25][0]
    assert states["deleted-open-new-uri"][0] < watched[2][0] < got[28][0]
    for rid, target in {20: 1, 21: 2, 22: 2, 23: 2, 24: 2, 25: 2, 27: 2, 28: 2, 30: 3}.items():
        assert got[rid][1]["result"]["goals"] == [f"⊢ {target} = {target}"]
    for rid in (26, 29):
        assert got[rid][1]["error"]["code"] == -32801
    for rid in range(10, 19):
        assert got[rid][1]["result"] == {}
    assert got[25][0] < got[26][0] < opens[1][0] < got[27][0] < got[28][0] < got[29][0] < opens[2][0] < got[30][0]
    diags = [e["message"]["params"] for e in events if e["kind"] == "server" and e.get("message", {}).get("method") == "textDocument/publishDiagnostics"]
    for suffix, version, target in (("Open.lean", 1, 1), ("Open.lean", 2, 2), ("Renamed.lean", 1, 2), ("Renamed.lean", 2, 3)):
        assert any(d["uri"].endswith(suffix) and d.get("version") == version and len(d["diagnostics"]) == 2 and f"⊢ {target} = {target}" in d["diagnostics"][0]["message"] for d in diags)
    assert not any(d["uri"].endswith("Open.lean") and d.get("version") == 2 and any("⊢ 3 = 3" in z["message"] for z in d["diagnostics"]) for d in diags)
    assert got[99][1]["result"] is None
    assert one(events, lambda e: e["kind"] == "wire_drain_complete")[0] > got[99][0]
    assert one(events, lambda e: e["kind"] == "server_exit")[1]["exit"] == 0
    assert not any(e["kind"] in ("fatal", "forced_exit") for e in events)

print("PASS: three open-buffer overwrite/save/rename/delete/reopen traces, exact disk and batch controls, clean exits")
