#!/usr/bin/env python3
"""Offline structural and semantic checks for the retained rich term-goal run."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
S = ROOT / "support"
R = json.loads((S / "results.json").read_text())
META = json.loads((ROOT / "REPORT.json").read_text())

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def render(node):
    if isinstance(node, list):
        return "".join(map(render, node))
    if isinstance(node, dict):
        if "text" in node:
            return node["text"]
        for key in ("tag", "append"):
            if key in node:
                return render(node[key])
    return ""

assert set(META) == {"topics", "subjects", "observed_at"}
assert META["observed_at"] == "2026-09-30"
assert META["subjects"][0]["identity"]["revision"] == "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
assert R["tools"]["lake_sha256"] == "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
assert R["tools"]["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
for name in ("Dep.lean", "Proof.lean"):
    assert (S / "fixture" / name).read_text() == R["source"][name]
    assert digest(S / "fixture" / name) == R["source"]["sha256"][name]
for name in ("dep-lakefile.lean", "project-lakefile.lean", "lake-manifest.json",
             "dep-lean-toolchain", "project-lean-toolchain"):
    assert (S / "fixture" / name).is_file()
assert R["build"]["exit"] == R["setup"]["exit"] == R["batches"]["nested_term"]["exit"] == R["stop"]["exit"] == 0
assert R["artifacts"]["Dep.olean"] and R["artifacts"]["Proof.olean"]
batch = [json.loads(line) for line in R["batches"]["nested_term"]["stdout"].splitlines()]
assert any("does not depend on any axioms" in m["data"] for m in batch)
assert any(m["data"] == "7" for m in batch)
assert R["waits"]["nested_term"]["result"] == {}
assert R["connect"]["result"]["sessionId"]
assert all(d.get("severity") != 1 for wave in R["diagnostics"]["nested_term"] for d in wave)
assert R["preflight"]["memory_free_percent"] >= 20
assert R["preflight"]["disk_free_bytes"] >= 10 * 1024**3
assert 0 < R["resources"]["peak_process_group_rss_kib"] < 1400 * 1024
assert R["resources"]["samples"] >= 10
assert R["resources"]["elapsed_seconds"] < 300

expected = {
    "exact_start": (2, None, None),
    "trans_start": (8, "depValue = depValue", (8, 54)),
    "trans_inside": (11, "depValue = depValue", (8, 54)),
    "first_refl": (18, "depValue = depValue", (18, 34)),
    "first_argument": (26, "Nat", (26, 34)),
    "between_terms": (35, "depValue = depValue", (17, 35)),
    "second_refl": (37, "depValue = depValue", (37, 53)),
    "second_argument": (45, "Nat", (45, 53)),
    "term_end": (54, "depValue = depValue", (36, 54)),
    "next_line": (0, None, None),
    "eof": (0, None, None),
}
live = R["live"]["nested_term"]
assert set(live) == set(expected)
for label, (column, target, span) in expected.items():
    row = live[label]
    assert row["position"] == {"line": 3 if label not in ("next_line", "eof") else (4 if label == "next_line" else 6), "character": column}
    for api in ("plain", "rich", "term", "rich_term"):
        assert "error" not in row[api], (label, api)
    plain, rich = row["term"]["result"], row["rich_term"]["result"]
    assert (plain is None) == (rich is None)
    if target is None:
        assert plain is rich is None
    else:
        assert plain["goal"] == "⊢ " + target
        assert render(rich["type"]) == target
        assert plain["range"] == rich["range"]
        assert (plain["range"]["start"]["character"], plain["range"]["end"]["character"]) == span
        assert plain["range"]["start"]["line"] == plain["range"]["end"]["line"] == 3
        assert set(rich["term"]) == {"p"} and set(rich["ctx"]) == {"p"}
    tactic_plain, tactic_rich = row["plain"]["result"], row["rich"]["result"]
    assert (tactic_plain is None) == (tactic_rich is None)
    if tactic_plain is not None:
        assert len(tactic_plain["goals"]) == len(tactic_rich["goals"])

calls = [e["message"] for e in R["events"] if e["direction"] == "client" and e["message"].get("method") == "$/lean/rpc/call"]
assert sum(c["params"]["method"] == "Lean.Widget.getInteractiveTermGoal" for c in calls) == len(expected)
assert sum(c["params"]["method"] == "Lean.Widget.getInteractiveGoals" for c in calls) == len(expected)
print("PASS: metadata, exact fixture, build/batch, 11 paired term-goal positions, transcript, resources")
