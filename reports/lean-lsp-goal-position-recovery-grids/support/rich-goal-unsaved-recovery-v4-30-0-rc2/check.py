#!/usr/bin/env python3
"""Check the retained direct Lean protocol transcript without running Lean."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = json.loads((HERE / "results.json").read_text())
events = json.loads((HERE / "transcript.json").read_text())

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

def pretty_text(value):
    if isinstance(value, list):
        return "".join(pretty_text(v) for v in value)
    if isinstance(value, dict):
        return value.get("text", "") + pretty_text(value.get("append", [])) + pretty_text(value.get("tag", []))
    return ""

assert len(data["cases"]) == 4
assert [(c["version"], c["label"]) for c in data["cases"]] == [
    (1, "valid"), (2, "syntax"), (3, "unknown"), (4, "recovered")]
assert data["subject"]["binary_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert data["disk_sha256"] == sha((HERE / "Nested.lean").read_text())
for case in data["cases"]:
    name = "Batch-" + ("valid" if case["label"] == "recovered" else case["label"]) + ".lean"
    assert case["source_sha256"] == sha((HERE / name).read_text())
    assert case["wait"].get("result") == {}
assert {key: value["rc"] for key, value in data["batch"].items()} == {
    "valid": 0, "syntax": 1, "unknown": 1}
assert "unexpected token" in data["batch"]["syntax"]["stdout"]
assert "unknown tactic" in data["batch"]["unknown"]["stdout"]

counts = {"target": 0, "empty": 0, "null": 0}
for case in data["cases"]:
    assert set(case["samples"]) == set(data["positions"])
    for name, pair in case["samples"].items():
        plain, rich = pair["plain"], pair["rich"]
        assert "error" not in plain and "error" not in rich, (case["label"], name)
        a, b = plain["result"], rich["result"]
        assert (a is None) == (b is None), (case["label"], name)
        if a is None:
            counts["null"] += 1
        else:
            assert len(a["goals"]) == len(b["goals"]), (case["label"], name)
            if not a["goals"]:
                counts["empty"] += 1
            else:
                assert len(a["goals"]) == 1
                assert a["goals"][0].split("⊢ ")[-1] == pretty_text(b["goals"][0]["type"])
                counts["target"] += 1

def shape(case, name):
    result = case["samples"][name]["plain"]["result"]
    return "null" if result is None else ("target" if result["goals"] else "empty")

valid, syntax, unknown, recovered = data["cases"]
assert all(shape(valid, name) == shape(recovered, name) for name in data["positions"])
assert all(valid["samples"][name]["plain"]["result"] ==
           recovered["samples"][name]["plain"]["result"] for name in data["positions"])
assert [shape(syntax, name) for name in data["positions"]] == [
    "target", "null", "null", "null", "null", "target"]
assert [shape(unknown, name) for name in data["positions"]] == [
    "target", "target", "target", "target", "null", "target"]
assert shape(valid, "inner_end") == "empty"
assert shape(valid, "inner_inside") == "target"

sent = [e["message"] for e in events if e["kind"] == "send"]
received = [e["message"] for e in events if e["kind"] == "recv"]
plain_calls = [m for m in sent if m.get("method") == "$/lean/plainGoal"]
rich_calls = [m for m in sent if m.get("method") == "$/lean/rpc/call"]
connections = [m for m in sent if m.get("method") == "$/lean/rpc/connect"]
assert len(plain_calls) == len(rich_calls) == 24
assert len(connections) == 1
assert len({m["params"]["sessionId"] for m in rich_calls}) == 1
replies = {m["id"]: m for m in received if "id" in m}
assert all(m["id"] in replies for m in plain_calls + rich_calls)
for case in data["cases"]:
    for name, pair in case["samples"].items():
        for method in ("plain", "rich"):
            response = pair[method]
            assert response == replies[response["id"]], (case["label"], name, method)
assert [m["params"]["textDocument"]["version"] for m in sent
        if m.get("method") == "textDocument/didChange"] == [2, 3, 4]
diagnostics = {}
for m in received:
    if m.get("method") == "textDocument/publishDiagnostics":
        diagnostics[m["params"]["version"]] = m["params"]["diagnostics"]
assert {version: len(rows) for version, rows in diagnostics.items()} == {1: 0, 2: 3, 3: 3, 4: 0}
assert "unexpected token" in diagnostics[2][0]["message"]
assert "unknown tactic" in diagnostics[3][0]["message"]
assert [e["rc"] for e in events if e["kind"] == "stop"] == [0]
print(json.dumps(dict(pairs=len(plain_calls), outcomes=counts, diagnostics={
    version: len(rows) for version, rows in diagnostics.items()}, server_exit=0), sort_keys=True))
