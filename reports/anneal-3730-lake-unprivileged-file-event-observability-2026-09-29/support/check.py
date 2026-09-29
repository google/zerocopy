#!/usr/bin/env python3
"""Offline validation of the retained selected libc-event record."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
data = json.loads((here / "results.json").read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(here / "observe.c") == data["subject"]["source_sha256"]
assert len(data["subject"]["interposer_sha256"]) == 64
assert data["subject"]["compile_cmd"][0] == "/usr/bin/clang"
assert data["subject"]["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert data["subject"]["lake_sha256"] == "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
run = {r["name"]: r for r in data["runs"]}
assert list(run) == ["cold", "warm", "changed_nobuild", "changed_build",
                     "post_warm", "unhooked_postwarm", "fresh_batch"]
assert [run[k]["exit"] for k in run] == [0, 0, 3, 0, 0, 0, 0]
for r in data["runs"]:
    assert r["event_count"] == len(r["events"])
    assert all(e["path"].startswith("$WORK") for e in r["events"])
    assert sorted(set(e["pid"] for e in r["events"])) == r["pids"]

def process_pair(r):
    found = {e["op"]: e for e in r["events"] if e["op"].startswith("process-")}
    assert set(found) == {"process-lake", "process-lean"}
    assert found["process-lean"]["result"] == found["process-lake"]["pid"]
    return found

cold = run["cold"]
process_pair(cold)
assert "Built Dep" in cold["stdout"]
assert any(e["op"] == "open" and e["path"] == "$WORK/Dep.lean" for e in cold["events"])
assert any(e["op"] == "rename-to" and e["path"].endswith("/Dep.olean")
           for e in cold["events"])
assert cold["net_changes"]

warm = run["warm"]
assert "Replayed Dep" in warm["stdout"] and not warm["net_changes"]
assert {e["op"] for e in warm["events"] if e["op"].startswith("process-")} == {"process-lake"}
assert any(e["op"] == "open" and e["path"] == "$WORK/Dep.lean" for e in warm["events"])
assert any(e["op"] == "read" and e["result"] > 0 and e["path"].endswith("lakefile.olean")
           for e in warm["events"])

nb = run["changed_nobuild"]
assert "out-of-date" in nb["stdout"]
assert ".lake/build/lib/lean/Dep.trace.nobuild" in nb["net_changes"]
assert {e["op"] for e in nb["events"] if e["op"].startswith("process-")} == {"process-lake"}

build = run["changed_build"]
proc = process_pair(build)
assert "Built Dep" in build["stdout"]
assert any(e["op"] == "rename-from" and e["path"].endswith(f"Dep.olean.tmp.{proc['process-lean']['pid']}")
           for e in build["events"])
assert any(e["op"] == "rename-to" and e["path"].endswith("/Dep.olean")
           for e in build["events"])
assert ".lake/build/lib/lean/Dep.olean" in build["net_changes"]

for name in ("post_warm", "unhooked_postwarm"):
    assert "Replayed Dep" in run[name]["stdout"] and not run[name]["net_changes"]
assert run["unhooked_postwarm"]["events"] == []
assert '"data":"9"' in run["fresh_batch"]["stdout"]
assert hashlib.sha256(b"def value : Nat := 9\n").hexdigest() == data["mutation"]["source_sha256"]
print("PASS: private libc events, parent-child witness, cold/replay/no-build/rebuild, transient artifact, unhooked replay, fresh Lean value")
