#!/usr/bin/env python3
"""Read-only, relocation-safe validation of the retained I147 fixture."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(name):
    return json.loads((ROOT / name).read_text())

manifest = load("evidence-manifest.json")
for name, expected in manifest.items():
    path = ROOT / name
    assert path.is_file(), name
    data = path.read_bytes()
    assert len(data) == expected["bytes"], name
    assert sha(data) == expected["sha256"], name

baseline = (ROOT / "baseline-Dep.lean").read_bytes()
edited = (ROOT / "edited-Dep.lean").read_bytes()
assert baseline == b"def selected : Nat := 7\n"
assert edited == b"def selected:Nat := 0x7\n"
assert len(baseline) == len(edited) and baseline != edited
assert (ROOT / "work/direct-source/Dep.lean").read_bytes() == edited

olean_before = (ROOT / "baseline-Dep.olean").read_bytes()
olean_after = (ROOT / "edited-Dep.olean").read_bytes()
assert olean_before == olean_after == (ROOT / "final-Dep.olean").read_bytes()
assert (ROOT / "baseline-Dep.ilean").read_bytes() != (ROOT / "edited-Dep.ilean").read_bytes()
trace_before = (ROOT / "baseline-Dep.trace").read_bytes()
trace_after = (ROOT / "edited-Dep.trace").read_bytes()
assert trace_before != trace_after
tb, ta = json.loads(trace_before), json.loads(trace_after)
assert tb["outputs"]["o"] == ta["outputs"]["o"]
assert tb["outputs"]["i"] != ta["outputs"]["i"]

events = load("transcript.json")
assert [e["seq"] for e in events] == list(range(len(events)))
assert events[-1]["kind"] == "completed"
assert not any(e["kind"] == "fatal" for e in events)
change_index = next(i for i, e in enumerate(events) if e["kind"] == "source_only_change")
rebuild_indices = [i for i, e in enumerate(events) if e["kind"] == "server"
                   and e["message"].get("method") == "textDocument/publishDiagnostics"
                   and any("Built Dep" in d.get("message", "")
                           for d in e["message"]["params"]["diagnostics"])]
new_sample_index = next(i for i, e in enumerate(events)
                        if e["kind"] == "sample" and e["phase"] == "new-open")
assert len(rebuild_indices) == 1 and change_index < rebuild_indices[0] < new_sample_index
assert events[rebuild_indices[0]]["message"]["params"]["uri"] == "$WORK_URI/direct-source/New.lean"
subject = next(e for e in events if e["kind"] == "subject")
assert subject["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert subject["lake_sha256"] == "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
assert subject["rss_cap_bytes"] == int(1.5 * 1024**3)
assert subject["scratch_cap_bytes"] == 1024**3
guards = [e for e in events if e["kind"] == "guard"]
assert guards and min(e["free_percent"] for e in guards) >= 20
assert max(e["tree_rss_bytes"] for e in guards) <= subject["rss_cap_bytes"]
assert max(e["scratch_bytes"] for e in guards) < subject["scratch_cap_bytes"]
assert events[-1]["ms"] <= 300000

samples = {e["phase"]: e for e in events if e["kind"] == "sample"}
assert set(samples) == {"baseline", "old-open", "new-open", "old-after-new", "reopened", "fresh-server"}
for phase, s in samples.items():
    assert s["artifact"]["sha256"] == sha(olean_before), phase
    assert s["goals"]["rfl-end"]["result"]["rendered"] == "no goals", phase
    assert s["goals"]["exact-end"]["result"]["goals"] == ["⊢ selected = 7"], phase
    assert s["diagnostics"] is not None, phase
    assert [d["message"] for d in s["diagnostics"]["diagnostics"]] == [
        "7", "don't know how to synthesize placeholder\ncontext:\n⊢ selected = 7",
        "unsolved goals\n⊢ selected = 7"], phase
assert samples["baseline"]["source_sha256"] == sha(baseline)
assert all(samples[p]["source_sha256"] == sha(edited) for p in samples if p != "baseline")
for phase in ("baseline", "new-open", "reopened", "fresh-server"):
    assert samples[phase]["wait"].get("result") == {}, phase
assert samples["new-open"]["artifact"]["mtime_ns"] != samples["baseline"]["artifact"]["mtime_ns"]

for phase in ("batch_before", "batch_after"):
    e = next(e for e in events if e["kind"] == phase)
    assert e["rc"] == 0 and not e["stderr"]
    lines = [json.loads(line) for line in e["stdout"].splitlines()]
    assert [line["data"] for line in lines] == ["7"]
assert any(e["kind"] == "setup_file" and e["rc"] == 0 for e in events)

candidates = load("candidate-results.json")
by_name = {r["name"]: r for r in candidates}
assert set(by_name) == {"baseline", "unicode_nat", "hex_literal", "type_ascription", "hex_equal_length", "paren_equal_length"}
assert by_name["unicode_nat"]["rc"] != 0
assert all(r["free_percent"] >= 20 for r in candidates)
for name, row in by_name.items():
    assert sha(row["source"].encode()) == row["source_sha256"], name
    if row["rc"] == 0:
        data = (ROOT / f"candidate-{name}.olean").read_bytes()
        assert len(data) == row["olean_bytes"] and sha(data) == row["olean_sha256"], name
assert len(by_name["baseline"]["source"].encode()) == len(by_name["hex_equal_length"]["source"].encode())
assert len(by_name["baseline"]["source"].encode()) == len(by_name["paren_equal_length"]["source"].encode())
base_hash = by_name["baseline"]["olean_sha256"]
assert by_name["hex_equal_length"]["olean_sha256"] == base_hash
assert by_name["paren_equal_length"]["olean_sha256"] == base_hash
assert by_name["hex_literal"]["olean_sha256"] != base_hash
assert by_name["type_ascription"]["olean_sha256"] != base_hash
assert (ROOT / "candidate-baseline.olean").read_bytes() == (ROOT / "candidate-hex_equal_length.olean").read_bytes()

attempt = load("attempt-parentheses/transcript.json")
assert attempt[-1]["kind"] == "completed"
assert (ROOT / "attempt-parentheses/edited-Dep.lean").read_bytes() == b"def selected : Nat := (7)\n"
attempt_olean = (ROOT / "attempt-parentheses/edited-Dep.olean").read_bytes()
assert len(attempt_olean) == len(olean_before)
assert sum(a != b for a, b in zip(attempt_olean, olean_before)) == 2
assert (ROOT / "attempt-parentheses/edited-Dep.trace").read_bytes() != (ROOT / "baseline-Dep.trace").read_bytes()

print("I147 syntax-equivalent rebuild evidence: OK")
