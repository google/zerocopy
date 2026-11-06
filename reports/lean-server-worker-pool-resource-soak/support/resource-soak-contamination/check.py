#!/usr/bin/env python3
"""Validate preserved R05 evidence without starting Lean."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
events=json.loads((ROOT/"transcript.json").read_text())
assert [x["seq"] for x in events]==list(range(len(events)))
assert not any(x["kind"]=="fatal" for x in events)
one=lambda k:next(x for x in events if x["kind"]==k)
setup=one("setup"); compiled=one("compile_import")
assert setup["lean_version"].startswith("Lean (version 4.30.0-rc2,")
assert compiled["rc"]==0
work=ROOT/"support"/"work"
assert hashlib.sha256((work/"Dep.lean").read_bytes()).hexdigest()==compiled["source_sha256"]
assert hashlib.sha256((work/"Dep.olean").read_bytes()).hexdigest()==compiled["olean_sha256"]
cells={x["workers"]:x for x in events if x["kind"]=="cell"}
assert set(cells)=={1,2,4}
for n in [1,2,4]:
    cell=cells[n]
    assert cell["status"]=="completed"
    assert len(cell["checks"])==n*3+(n-(0 if n==1 else (1 if n==2 else 2)))
    assert all(c["goal_ok"] and "error" not in c["goal"] for c in cell["checks"])
    for c in cell["checks"]:
        i=c["file"]
        assert f"probe{i} = {7+2*i}" in json.dumps(c["goal"])
assert any(x["kind"]=="four_worker_admission" and x["allowed"] for x in events)
for e in events:
    if e["kind"]=="guard":
        assert not e["reasons"]
        assert e["tree"]["summed_rss_bytes"]<=setup["limits"]["rss_bytes"]
        assert e["tree"]["count"]<=setup["limits"]["processes"]
        assert e["inventory"]["blocks_bytes"]<=setup["limits"]["disk_bytes"]
        assert e["free_percent"]>=setup["limits"]["free_percent"]
last=[x for x in events if x["kind"]=="resource" and x["phase"]=="after_stop"][-1]
assert last["tree"]["count"]==0
assert events[-1]["kind"]=="finished"
print(f"OK: {len(events)} events; 1/2/4 completed; 25 sentinel queries; guards and cleanup passed")
