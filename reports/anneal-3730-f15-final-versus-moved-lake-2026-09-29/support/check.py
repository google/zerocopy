#!/usr/bin/env python3
"""Offline checker for the retained F15 paired-location result."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
report = json.loads((root.parent / "REPORT.json").read_text())
raw = json.loads((root / "results.json").read_text())
assert hashlib.sha256((root / "probe.py").read_bytes()).hexdigest() == \
       report["subjects"][1]["identity"]["probe_sha256"]
assert hashlib.sha256((root / "results.json").read_bytes()).hexdigest() == \
       report["subjects"][1]["identity"]["results_sha256"]
assert raw["subject"]["lean_sha256"] == report["subjects"][0]["identity"]["lean_sha256"]
assert raw["subject"]["lake_sha256"] == report["subjects"][0]["identity"]["lake_sha256"]
assert raw["subject"]["toolchain"] == "leanprover/lean4:v4.30.0-rc2"
assert raw["subject"]["network"] == "sandbox-exec deny network*"
assert raw["subject"]["jobs"] == 1  # One Lean library module; Lake reports three internal jobs.
assert raw["subject"]["sources_sha256"]["Proof.lean"] == hashlib.sha256(
    b"import Dep\n#eval selected\ntheorem checked : selected = 7 := by\n  rfl\n#print axioms checked\n").hexdigest()

direct, moved = raw["direct"], raw["staged_moved"]
for name, side in (("direct", direct), ("moved", moved)):
    assert side["build"]["rc"] == 0, name
    assert side["oracle"]["setup"]["rc"] == 0, name
    setup = json.loads(side["oracle"]["setup"]["stdout"])
    assert setup["importArts"]["Dep"] == ["<SCRATCH>/final/.lake/build/lib/lean/Dep.olean"], name
    server = side["oracle"]["server"]
    assert server["goal"]["result"]["rendered"] == "no goals", name
    assert server["goal"]["result"]["goals"] == [], name
    messages = [x["message"] for x in server["diagnostics"]["diagnostics"]]
    assert messages == ["7", "'checked' does not depend on any axioms"], name
    assert side["oracle"]["batch"]["rc"] == 0, name
    assert '"data":"7"' in side["oracle"]["batch"]["stdout"], name
    assert "does not depend on any axioms" in side["oracle"]["batch"]["stdout"], name
    assert side["no_build_check"]["rc"] == 0, name
    assert "All targets up-to-date" in side["no_build_check"]["stdout"], name

def keyed(rows):
    return {row["path"]: row for row in rows}

db, da = keyed(direct["before_oracle"]), keyed(direct["after_oracle"])
sb = keyed(moved["at_stage"])
mb, ma = keyed(moved["at_final_before_oracle"]), keyed(moved["after_oracle"])
assert len(db) == len(da) == len(sb) == len(mb) == len(ma) == 10
assert db == da and sb == mb == ma  # setup/server/no-build did not rewrite artifacts
assert set(db) == set(sb)
different = {name for name in db if db[name]["sha256"] != sb[name]["sha256"]}
assert different == {".lake/build/lib/lean/Dep.trace"}, different
assert db[".lake/build/lib/lean/Dep.trace"]["path_occurrences"] == {"final": 7}
assert sb[".lake/build/lib/lean/Dep.trace"]["path_occurrences"] == {"stage": 7}
assert db[".lake/build/lib/lean/Dep.olean"]["sha256"] == sb[".lake/build/lib/lean/Dep.olean"]["sha256"]
starts = [x for x in raw["transcript"] if x["kind"] == "launch"]
stops = [x for x in raw["transcript"] if x["kind"] == "stop"]
assert len(starts) == len(stops) == 2
assert all(x["mode"] == "lake-serve" for x in starts)
assert all(x["rc"] == 0 for x in stops)
assert moved["build"]["cwd"] == "<SCRATCH>/stage"
assert moved["oracle"]["setup"]["cwd"] == "<SCRATCH>/final"
print("PASS: both final-path oracles agree; moved Lake trace retains 7 staging paths")
