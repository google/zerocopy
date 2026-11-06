#!/usr/bin/env python3
"""Offline checker for retained C03 proof-resend result."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
r = json.loads((root / "results.json").read_text())
assert all(b["rc"] == 0 for b in r["builds"])
assert r["artifact7_sha256"] != r["artifact9_sha256"]
assert r["proof_sha256"] == hashlib.sha256(
    b"import Dep\n#eval selected\ntheorem checked : selected = 7 := by\n  rfl\n").hexdigest()
o = r["observations"]
for name in ("initial", "after_watched", "same_text_v2", "whitespace_v3"):
    assert o[name]["goal"]["result"]["rendered"] == "no goals", name
for name in ("reopened", "fresh"):
    assert o[name]["goal"]["result"]["goals"] == ["⊢ selected = 7"], name
    assert any("Tactic `rfl` failed" in d["message"]
               for d in o[name]["diagnostics"]["diagnostics"]), name
assert r["batch"]["rc"] == 1
assert '"data":"9"' in r["batch"]["stdout"]
assert "Tactic `rfl` failed" in r["batch"]["stdout"]
transcript = r["transcript"]
changes = [e["message"] for e in transcript if e["kind"] == "client"
           and e["message"].get("method") == "textDocument/didChange"]
assert [e["params"]["textDocument"]["version"] for e in changes] == [2, 3]
assert changes[1]["params"]["contentChanges"][0]["text"] == changes[0]["params"]["contentChanges"][0]["text"] + "\n"
assert any(e["kind"] == "client" and e["message"].get("method") == "workspace/didChangeWatchedFiles"
           for e in transcript)
assert len([e for e in transcript if e["kind"] == "stop" and e["rc"] == 0]) == 2
assert "unknown module prefix" in json.dumps(json.loads((root / "attempt1-invalid-path.json").read_text()))
print("PASS: old worker stale through watched/resend/whitespace; reopen/fresh/batch see import 9")
