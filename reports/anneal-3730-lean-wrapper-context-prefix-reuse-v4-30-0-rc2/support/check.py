#!/usr/bin/env python3
"""Validate preserved observations without re-running Lean."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
data = json.loads((root / "raw.json").read_text())
assert data["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
for name, case in data["context"].items():
    assert hashlib.sha256(case["source"].encode()).hexdigest() == case["source_sha256"], name

c = data["context"]
assert [c[n]["exit"] for n in ("instance_in_scope", "instance_omitted",
                                 "macro_left", "macro_right", "macro_missing",
                                 "option_strict", "option_permissive")] == [0, 1, 0, 0, 1, 1, 0]
assert "does not depend on any axioms" in c["instance_in_scope"]["stdout"]
assert "sorryAx" in c["instance_omitted"]["stdout"]
assert "N.proof : 0 = 0" in c["macro_left"]["stdout"]
assert "N.proof : 1 = 1" in c["macro_right"]["stdout"]
assert "N.proof : ∀ {later : Nat}, later = 1" in c["option_permissive"]["stdout"]

steps = data["prefix"]["steps"]
expected = {
    "base": list("ABCDE"), "late_tactic": ["E"], "reset_late": ["E"],
    "definition": list("DE"), "reset_definition": list("DE"),
    "option": list("CDE"), "reset_option": list("CDE"),
    "namespace": list("BCDE"), "reset_namespace": list("BCDE"),
    "import": list("ABCDE"), "reset_import": list("ABCDE"),
}
assert len(steps) == len(expected)
for i, step in enumerate(steps, 1):
    assert step["version"] == i
    assert step["new_ticks"] == expected[step["name"]], step["name"]
    assert step["wait"].get("result") == {}, step["name"]
    source = next(s["source"] for s in data["prefix"]["sources"] if s["name"] == step["name"])
    assert hashlib.sha256(source.encode()).hexdigest() == step["normalized_source_sha256"]
assert any(e.get("message", {}).get("method") == "textDocument/publishDiagnostics" and
           e["message"].get("params", {}).get("version") == 4 and
           any(d.get("severity") == 1 and "false" in d.get("message", "")
               for d in e["message"]["params"].get("diagnostics", []))
           for e in data["prefix"]["events"])
assert data["prefix"]["events"][-1]["code"] == 0
print("PASS: seven batch context controls, eleven exact-version prefix controls, diagnostics, hashes, clean server exit")
