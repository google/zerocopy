#!/usr/bin/env python3
"""Check the retained Lake ablation results without running Lake."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
assert hashlib.sha256((root / "results.json").read_bytes()).hexdigest() == (
    "2b566c7e04e1cf94a270e64b35a3ddc17f3b49ca1c768a87beaf63d97dfda23e")
data = json.loads((root / "results.json").read_text())
runs = {r["label"]: r for r in data["runs"]}
names = ("fresh_full", "no_source", "no_trace", "no_hash", "no_setup", "no_config")
assert len(runs) == len(data["runs"]) == 4 + 3 * len(names)
assert set(data["cells"]) == set(names)
assert data["preflight"]["disk_free_bytes"] >= 10 * 1024**3
assert data["preflight"]["memory_free_percent"] >= 20
assert data["tools"] == {
    "lake_sha256": "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
    "lean_sha256": "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997",
}
assert [r["label"] for r in data["runs"]] == [
    "clean-build", "clean-batch", "clean-first-goal", "seed-build",
    *[label for name in names for label in (name + "-no-build", name + "-batch", name + "-first-goal")],
]

artifact_paths = (
    ".lake/build/lib/lean/Dep.olean",
    ".lake/build/lib/lean/Dep.ilean",
    ".lake/build/ir/Dep.c",
)
expected_hashes = (
    "cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b",
    "ee34578f6077d4f2019dca615b30d0de14340a9d0d36cdb2870f3285adeb00e5",
    "36383e740367044dc594c872922b0c37356a7c73a35f72ff5cdc252e829e052e",
)
for path, digest in zip(artifact_paths, expected_hashes):
    assert data["clean"]["producer"][path] == data["seed"]["producer"][path] == digest
    assert data["cells"]["fresh_full"]["after"][path] == digest
assert "Built Dep" in runs["clean-build"]["stdout"]
assert "Built Generated" in runs["clean-build"]["stdout"]
assert "Built Dep" in runs["seed-build"]["stdout"]
assert "Built Generated" in runs["seed-build"]["stdout"]
assert runs["clean-build"]["exit"] == runs["seed-build"]["exit"] == 0

expected = {
    "fresh_full": (0, "Fetched Dep", "Fetched Generated", {
        ".lake/build/ir/Dep.c", ".lake/build/ir/Dep.c.hash",
        ".lake/build/lib/lean/Dep.ilean", ".lake/build/lib/lean/Dep.ilean.hash",
        ".lake/build/lib/lean/Dep.olean", ".lake/build/lib/lean/Dep.olean.hash",
        ".lake/build/lib/lean/Dep.trace"}),
    "no_source": (1, "bad import 'Dep'", "Dep.lean", set()),
    "no_trace": (0, "Fetched Dep", "Fetched Generated", {
        ".lake/build/lib/lean/Dep.trace", ".lake/config/probe_dep/lakefile.olean.trace"}),
    "no_hash": (0, "Replayed Dep", "Fetched Generated", {
        ".lake/build/ir/Dep.c.hash", ".lake/build/lib/lean/Dep.ilean.hash",
        ".lake/build/lib/lean/Dep.olean.hash"}),
    "no_setup": (0, "Replayed Dep", "Fetched Generated", set()),
    "no_config": (0, "Replayed Dep", "Fetched Generated", {
        ".lake/config/probe_dep/lakefile.olean", ".lake/config/probe_dep/lakefile.olean.trace"}),
}

def batch_messages(row):
    return [json.loads(line).get("data") for line in row["stdout"].splitlines() if line.startswith("{")]

for name in ("clean", *names):
    batch = runs[name + "-batch"]
    first = runs[name + "-first-goal"]
    assert batch["exit"] == first["exit"] == 0
    assert "'generatedEq' does not depend on any axioms" in batch_messages(batch)
    assert "8" in batch_messages(batch)
    assert first["wait"]["result"] == {}
    assert first["goal"]["id"] == 3
    goal = first["goal"]["result"]
    if name == "no_source":
        assert goal is None
        diagnostics = [d["message"] for n in first["notifications"]
                       if n.get("method") == "textDocument/publishDiagnostics"
                       for d in n["params"]["diagnostics"]]
        assert any("no such file or directory" in d for d in diagnostics)
        assert any("producer/Dep.lean" in d for d in diagnostics)
        assert any("bad import 'Dep'" in d for d in diagnostics)
    else:
        assert goal["goals"] == ["⊢ depValue + 1 = 8"]

for name, (code, action1, action2, created) in expected.items():
    cell, build = data["cells"][name], runs[name + "-no-build"]
    assert build["exit"] == cell["build_exit"] == code
    assert cell["batch_exit"] == cell["goal_exit"] == 0
    assert action1 in build["stdout"] and action2 in build["stdout"]
    assert build["command"][-3:] == ["--no-build", "build", "Generated"]
    assert cell["cache_unchanged"] is True
    before, after = cell["before"], cell["after"]
    assert set(after) - set(before) == created
    assert set(before) - set(after) == set()
    assert all(before[p] == after[p] for p in before)

assert data["cells"]["no_source"]["removed"] == ["Dep.lean"]
assert data["cells"]["no_setup"]["removed"] == [".lake/build/ir/Dep.setup.json"]
assert data["cells"]["no_trace"]["removed"] == sorted(expected["no_trace"][3])
assert set(data["cells"]["no_hash"]["removed"]) == expected["no_hash"][3]
assert data["cells"]["no_config"]["removed"] == [".lake/config/"]
assert data["cells"]["fresh_full"]["removed"] == [".lake/build/"]
assert hashlib.sha256((root / "probe.py").read_bytes()).hexdigest() == (
    "0b5dc8abace2ac483cf64f7cf783ce3bc878eabcf7b142c8d2c8b4e6b9e5d491")
print("Lake fresh-cache matrix assertions passed")
