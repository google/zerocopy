#!/usr/bin/env python3
"""Offline verifier of retained R447 batch-only evidence; never launches Lean."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def files(root):
    return {str(p.relative_to(root)):{"sha256":sha(p),"bytes":p.stat().st_size}
            for p in sorted(root.rglob("*")) if p.is_file() and not p.is_symlink()}
x=json.loads((ROOT/"results.json").read_text())
ident=json.loads((ROOT/"support/toolchain-identities.json").read_text())
assert x["status"]=="completed" and x["schema"]==1 and len(x["calls"])==60
assert all(sha(ROOT/"fixture"/name)==h for name,h in x["fixture_sha256"].items())
versions=("v4.29.0","v4.30.0-rc2","v4.34.1")
for v in versions:
    assert ident[v]["lean"]["sha256"]==x["identities"][v]["lean_sha256"]
    assert ident[v]["lake"]["sha256"]==x["identities"][v]["lake_sha256"]
    assert v.lstrip("v") in ident[v]["lean"]["version"]
    assert v.lstrip("v") in ident[v]["lake"]["version"]
def call(v,label):
    hits=[a for a in x["calls"] if a["version"]==v and a["label"]==label]
    assert len(hits)==1,(v,label)
    return hits[0]
def messages(c):
    return [{k:m.get(k) for k in ("severity","kind","pos","endPos","data")}
            for line in c["stdout"].splitlines() if line.startswith("{")
            for m in [json.loads(line)] if "severity" in m]
for v in versions:
    q=x["versions"][v];cells=q["build_cells"]
    assert set(cells)=={"clean-1","clean-2","cache-seed","cache-reuse-1","cache-reuse-2"}
    assert all(cells[k]["build_returncode"]==0 for k in cells)
    assert cells["clean-1"]["artifacts"]==cells["clean-2"]["artifacts"]==q["materialized_artifacts"]
    assert cells["cache-reuse-1"]["artifacts"]==cells["cache-reuse-2"]["artifacts"]
    assert len(cells["clean-1"]["artifacts"])==len(cells["cache-seed"]["artifacts"])==16
    assert len(cells["cache-reuse-1"]["artifacts"])==6
    assert not any(p.endswith(".olean") for p in cells["cache-reuse-1"]["artifacts"])
    diff=[p for p,a in cells["clean-1"]["artifacts"].items() if a!=cells["cache-seed"]["artifacts"].get(p)]
    assert diff==["ir/Probe.setup.json"],(v,diff)
    tag=v.replace(".","_").replace("-","_")
    for label in cells:
        assert files(ROOT/"runs"/tag/"artifacts"/label)==cells[label]["artifacts"]
    assert files(ROOT/"runs"/tag/"artifacts/materialized")==q["materialized_artifacts"]
    assert call(v,"clean-1-probe-json")["returncode"]==0
    assert call(v,"cache-reuse-1")["returncode"]==call(v,"cache-reuse-2")["returncode"]==0
    for label in ("cache-reuse-1-probe-json","cache-reuse-2-probe-json","cache-goal-json"):
        c=call(v,label)
        assert c["returncode"]==1 and "does not exist" in c["stdout"]
    assert call(v,"materialized-probe-json")["returncode"]==0
    assert call(v,"materialized-goal-v1-json")["returncode"]==1
    assert call(v,"materialized-goal-v2-json")["returncode"]==0
    assert messages(call(v,"materialized-goal-v2-json"))==[]
    for mode in ("clean-1","cache-reuse-1"):
        out=json.loads(call(v,mode+"-setup")["stdout"])
        arts=out["importArts"]["Probe.Base"]
        assert len(arts)==1
        if v=="v4.34.1": assert isinstance(arts[0],list) and len(arts[0])==1 and isinstance(arts[0][0],str)
        else: assert isinstance(arts[0],str)
        path=arts[0][0] if isinstance(arts[0],list) else arts[0]
        assert ("/cache/artifacts/" in path)==(mode=="cache-reuse-1")
    if v=="v4.34.1": assert "Fetched Probe" not in call(v,"cache-reuse-1")["stdout"]
    else: assert "Fetched Probe.Base" in call(v,"cache-reuse-1")["stdout"]
for label in ("materialized-probe-json","materialized-goal-v1-json","materialized-goal-v2-json"):
    assert messages(call(versions[0],label))==messages(call(versions[1],label))==messages(call(versions[2],label))
for old in versions[:2]:
    a=x["versions"][old]["build_cells"]["clean-1"]["artifacts"]
    b=x["versions"][versions[2]]["build_cells"]["clean-1"]["artifacts"]
    assert len([p for p in a if a[p]==b.get(p)])==5
samples=[s for c in x["calls"] for s in [c["admission"]]+c["live_samples"]]
assert all(c["abort"] is None for c in x["calls"])
assert all(c["admission"]["reclaimable_fraction"]>.20 and c["admission"]["disk_free_bytes"]>10*1024**3 for c in x["calls"])
assert all(s["reclaimable_fraction"]>=.18 and s["disk_free_bytes"]>10*1024**3 and s["scratch_bytes"]<=100*1024**2 for s in samples)
assert all(s.get("group_rss_kib",0)<=1200*1024 for s in samples)
assert round(100*min(s["reclaimable_fraction"] for s in samples),2)==19.89
assert min(s["disk_free_bytes"] for s in samples)==13336137728
assert max(s.get("group_rss_kib",0) for s in samples)==1099904
print("PASS: fixture, 60 batch calls, retained artifacts, setup shape, diagnostics, guards")
