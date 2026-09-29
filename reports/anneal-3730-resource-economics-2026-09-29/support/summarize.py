#!/usr/bin/env python3
"""Validate this resource probe's bounded outcomes, not production capacity."""
import hashlib
import json
import statistics
from pathlib import Path

ROOT=Path(__file__).resolve().parent
a=json.loads((ROOT/"transcript.json").read_text())
def one(kind,label=None,phase=None):
    xs=[x for x in a if x["kind"]==kind and (label is None or x.get("label")==label)
        and (phase is None or x.get("phase")==phase)]
    assert len(xs)==1,(kind,label,phase,len(xs))
    return xs[0]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

subject=one("subject")
assert subject["host"]["hw_mem_bytes"]==8589934592
assert "APFS" in subject["host"]["filesystem"]
assert subject["host"]["pressure_start"]["free_percent"]>=30
names=["cold-serial-a","cold-serial-b","cold-parallel-two","warm-parallel-two",
       "proof-edit-parallel-two","warm-after-edit-two"]
g={name:one("group",name) for name in names}
for name,x in g.items():
    assert x["aborted"] is None,name
    assert all(r["rc"]==0 and r["olean_sha256"] for r in x["results"]),name
    assert x["peak"]["rss_bytes"]<subject["rss_guard_bytes"],name
    assert x["min_free_percent_sampled"] is None or x["min_free_percent_sampled"]>=subject["free_floor_percent"]
    assert x["peak_blocks_bytes"]>=sum(r["inventory"]["blocks_bytes"] for r in x["results"])
    assert x["peak_files"]>=sum(r["inventory"]["files"] for r in x["results"])
    assert not x["temp_seen"]
    for r in x["results"]:
        v=7 if r["root"].endswith("a") else 9
        assert f"info: Generated.lean:3:0: {v}" in r["stdout"] or "up to date" in r["stdout"].lower()
        assert r["inventory"]["files"]==r["inventory"]["unique_inodes"]==15
        assert r["inventory"]["blocks_bytes"]==159744
        if name=="warm-after-edit-two":
            index=0 if r["root"].endswith("a") else 1
            assert sha(ROOT/"work"/r["root"]/".lake/build/lib/lean/Generated.olean") == g[name]["results"][index]["olean_sha256"]
assert g["cold-serial-a"]["consumers"]==g["cold-serial-b"]["consumers"]==1
assert all(g[n]["consumers"]==2 for n in names[2:])
assert g["cold-parallel-two"]["peak"]["count"]==4
assert g["warm-parallel-two"]["peak"]["count"]==2
for i,serial in enumerate(names[:2]):
    coldhash=g[serial]["results"][0]["olean_sha256"]
    assert coldhash==g["cold-parallel-two"]["results"][i]["olean_sha256"]
    assert coldhash==g["warm-parallel-two"]["results"][i]["olean_sha256"]
    changed=g["proof-edit-parallel-two"]["results"][i]["olean_sha256"]
    assert changed!=coldhash
    assert changed==g["warm-after-edit-two"]["results"][i]["olean_sha256"]

sentinels=[x for x in a if x["kind"]=="sentinel"]
soak=[x for x in a if x["kind"]=="soak"]
assert len(sentinels)==4 and len(soak)==8
for x in sentinels+soak:
    v=7 if x["label"]=="a" else 9
    assert x["expected"]==v
    assert x["goal"]["result"]["goals"]==[f"⊢ selected = {v}"]
    if x["kind"]=="sentinel":
        assert any(d.get("message")==str(v) for d in x["diagnostics"]["diagnostics"])
resources={x["phase"]:x for x in a if x["kind"]=="server_resource"}
for phase in ["initial","edit-1","edit-2","edit-3","edit-4","reopen"]:
    assert resources[phase]["tree"]["count"]==4
assert resources["after-stop"]["tree"]["rss_bytes"]==0
for phase in ["initial","reopen"]:
    assert len(resources[phase]["footprints"])==4
    assert all(f.get("phys_footprint_bytes",0)>0 and f.get("rc")==0 for f in resources[phase]["footprints"])
assert len([x for x in a if x["kind"]=="server_stop" and x["rc"]==0])==2
assert one("completed")["seq"]==len(a)-1
assert not any(x["kind"]=="fatal" for x in a)
latencies={method:[x["ms_elapsed"] for x in a if x["kind"]=="latency" and x["method"]==method]
           for method in ["textDocument/waitForDiagnostics","$/lean/plainGoal"]}
assert len(latencies["textDocument/waitForDiagnostics"])==12
assert len(latencies["$/lean/plainGoal"])==12

result=dict(status="bounded assertions passed",events=len(a),
    probe_sha256=sha(ROOT/"probe.py"),transcript_sha256=sha(ROOT/"transcript.json"),
    lean_sha256=subject["lean_sha256"],lake_sha256=subject["lake_sha256"],
    host_ram_bytes=subject["host"]["hw_mem_bytes"],
    start_free_percent=subject["host"]["pressure_start"]["free_percent"],
    end_free_percent=one("host_end")["pressure"]["free_percent"],
    groups={n:dict(consumers=x["consumers"],elapsed_ms=x["elapsed_ms"],
        peak_rss_bytes=x["peak"]["rss_bytes"],sampled_peak_processes=x["peak"]["count"],
        peak_blocks_bytes=x["peak_blocks_bytes"],peak_files=x["peak_files"],
        temp_seen=x["temp_seen"],olean_sha256=[r["olean_sha256"] for r in x["results"]])
        for n,x in g.items()},
    servers={phase:dict(summed_rss_bytes=resources[phase]["tree"]["rss_bytes"],
       process_count=resources[phase]["tree"]["count"],
       summed_phys_footprint_bytes=(sum(f["phys_footprint_bytes"] for f in resources[phase]["footprints"])
          if "footprints" in resources[phase] else None))
       for phase in ["initial","edit-1","edit-2","edit-3","edit-4","reopen","after-stop"]})
result["server_latencies_ms"]={method:dict(count=len(values),minimum=min(values),
    median=statistics.median(values),maximum=max(values)) for method,values in latencies.items()}
result["server_open_ms"]=[x["elapsed_ms"] for x in a if x["kind"]=="server_open"]
(ROOT/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
