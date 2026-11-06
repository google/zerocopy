#!/usr/bin/env python3
"""Offline raw-byte checker for two staggered Charon reader/collision pairs."""
import hashlib
import json
from pathlib import Path
import probe

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/"results.json").read_text())
EXPECTED={"release":{"unit_key_probe::profile_value":["11"],"unit_key_probe::config_value":["23"]},
          "cfg_alt":{"unit_key_probe::profile_value":["7"],"unit_key_probe::config_value":["29"]}}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def literals(obj):
    out={}
    for decl in obj["translated"]["fun_decls"]:
        if decl["item_meta"]["is_local"]:
            name="::".join(y["Ident"][0] for y in decl["item_meta"]["name"] if "Ident" in y)
            out[name]=list(probe.scalar_literals(decl["body"]))
    return out
def parsed(path):
    text=path.read_text()
    obj,end=json.JSONDecoder().raw_decode(text)
    return obj,end,text[end:]
def check_embedded(obj,dest):
    translated=obj["translated"]
    assert translated["crate_name"]=="unit_key_probe"
    assert translated["options"]["dest_file"]==dest
    assert len(translated["files"])==1
    assert hashlib.sha256(translated["files"][0]["contents"].encode()).hexdigest()==probe.PINS["fixture_source"]
def destination(row):
    a=row["argv"];return a[a.index("--dest-file")+1]

assert x["schema"]==1 and x["status"]=="completed"
assert x["input_sha256"]==probe.PINS
for name,path in {"charon":probe.CHARON,"cargo":probe.CARGO,"rustc":probe.RUSTC,
                  "fixture_source":HERE/"fixture/src/lib.rs",
                  "control_release":HERE/"controls/release.llbc",
                  "control_cfg_alt":HERE/"controls/cfg_alt.llbc"}.items():
    assert digest(path)==probe.PINS[name],name
assert x["control_models"]=={k:{"sha256":probe.PINS["control_"+k],
                                      "selected_literals":EXPECTED[k]} for k in EXPECTED}
assert x["initial_preflight"]["host"]["estimated_reclaimable_percent"]>25
assert x["initial_preflight"]["host"]["free_disk_bytes"]>10*1024**3
assert x["limits"]=={"minimum_admission_reclaimable_percent":25.0,
                     "minimum_live_reclaimable_percent":20.0,
                     "minimum_free_disk_bytes":10*1024**3,
                     "maximum_combined_process_group_rss_kib":256*1024,
                     "maximum_scratch_kib":100*1024,
                     "pair_timeout_seconds":15.0}
assert [p["name"] for p in x["pairs"]]==["release-first","cfg-first"]
all_read_hashes={}
for pair,order in zip(x["pairs"],(("release","cfg_alt"),("cfg_alt","release"))):
    name=pair["name"];run=pair["run"];rows=run["commands"]
    assert pair["launch_order"]==list(order) and pair["stagger_seconds"]==.03
    assert pair["initial_destination_absent"] is True
    assert run["guard_reason"] is None and run["elapsed_seconds"]<15
    assert run["preflight"]["host"]["estimated_reclaimable_percent"]>25
    assert run["preflight"]["host"]["free_disk_bytes"]>10*1024**3
    assert len(rows)==2 and [r["label"] for r in rows]==[f"{name}-{z}" for z in order]
    assert all(r["exit"]==0 and len(r["driver_lines"])==1 for r in rows)
    assert 0.025<(rows[1]["start_monotonic_ns"]-rows[0]["start_monotonic_ns"])/1e9<.09
    assert pair["collection_intervals_overlap"] is True
    assert max(r["start_monotonic_ns"] for r in rows) < min(r["end_monotonic_ns"] for r in rows)
    assert len({r["pid"] for r in rows})==2
    assert destination(rows[0])==destination(rows[1])
    assert len({r["environment"]["CARGO_TARGET_DIR"] for r in rows})==2
    for r in rows:
        env=r["environment"];argv=r["argv"]
        assert argv[0]==str(probe.CHARON) and argv[1:4]==["cargo","--preset","aeneas"]
        assert "--lib" in argv and "--offline" in argv and "--locked" in argv and "-j" in argv
        assert env["CARGO_NET_OFFLINE"]=="true" and env["CARGO_BUILD_JOBS"]=="1"
        assert env["CARGO_INCREMENTAL"]=="0" and env["RAYON_NUM_THREADS"]=="1"
        assert r["cwd"]==str(HERE/"fixture") or r["cwd"].endswith("/i076-live-reader-collision/fixture")
        for suffix in ("stdout","stderr"):
            path=HERE/"raw"/f"{r['label']}.{suffix}"
            assert digest(path)==r[f"{suffix}_sha256"]
            assert path.stat().st_size==r[f"{suffix}_bytes"]
        if r["label"].endswith("-release"):
            assert "--release" in argv and env["RUSTFLAGS"] is None
            assert "-C opt-level=3" in r["driver_lines"][0]
        else:
            assert "--release" not in argv and env["RUSTFLAGS"]=="--cfg probe_alt"
            assert "--cfg probe_alt" in r["driver_lines"][0]
    assert run["samples"]
    simultaneous=0
    for s in run["samples"]:
        assert s["host"]["estimated_reclaimable_percent"]>=20
        assert s["host"]["free_disk_bytes"]>=10*1024**3
        assert s["combined_rss_kib"]<=256*1024 and s["scratch_kib"]<=100*1024
        if all(s["process_group_rss_kib"][str(r["pid"])]>0 for r in rows):simultaneous+=1
    assert simultaneous>0
    assert all(v==0 for v in pair["postrun_process_group_rss_kib"].values())
    assert run["reader_errors"]==[] and run["reader_truncated"] is False
    obs=run["reader_observations"];assert obs and obs[0]["state"]=="absent_or_disappeared"
    assert all(a["monotonic_ns"]<=b["monotonic_ns"] for a,b in zip(obs,obs[1:]))
    seen=set()
    for o in obs:
        if o["state"]=="read":
            assert o["double_read_equal"] is True
            assert o["first_size"]==o["second_size"] and o["first_sha256"]==o["second_sha256"]
            assert o["first_inode"]==o["second_inode"]
            seen.add(o["first_sha256"])
        else:
            assert o["state"]=="absent_or_disappeared"
    retained={z["sha256"] for z in run["snapshot_files"]}
    assert seen==retained
    for z in run["snapshot_files"]:
        file=HERE/"artifacts"/Path(z["path"]).name
        assert digest(file)==z["sha256"] and file.stat().st_size==z["bytes"]
    all_read_hashes[name]=seen
    final=pair["final_destination"];assert final is not None
    path=HERE/"artifacts"/f"{name}-final.llbc"
    assert digest(path)==final["sha256"] and path.stat().st_size==final["bytes"]
    assert digest(HERE/"work"/name/"shared.llbc")==final["sha256"]
    assert final["sha256"] in seen
    assert final["decoded"]["dest_file"]==destination(rows[0]) if final["parseable"] else True
# Exact retained byte states, not a generalized atomicity claim.
a=x["pairs"][0]["final_destination"]
assert a["sha256"]=="a3142ee67648b21c8b1703c3ee135bdff03d97116ff1413806332c239473b099"
assert a["bytes"]==5520 and a["parseable"] is False
path=HERE/"artifacts/release-first-final.llbc"
obj,end,tail=parsed(path)
assert end==5518 and tail=="e}" and obj["has_errors"] is False
check_embedded(obj,destination(x["pairs"][0]["run"]["commands"][0]))
assert literals(obj)==EXPECTED["cfg_alt"]
try:json.loads(path.read_bytes())
except json.JSONDecodeError as e:assert e.pos==5518
else:raise AssertionError("release-first final unexpectedly parses")
b=x["pairs"][1]["final_destination"]
assert b["sha256"]=="15757df7f92055ccb8b41b7c7bcc806dd83de8b566f4719ec15f13c4b01d062a"
assert b["bytes"]==5516 and b["parseable"] is True
assert probe.decode(HERE/"artifacts/cfg-first-final.llbc")==b["decoded"]
assert b["decoded"]["files"][0]["contents_sha256"]==probe.PINS["fixture_source"]
assert {k:v["u32_literals"] for k,v in b["decoded"]["local_bodies"].items()}==EXPECTED["release"]
assert all_read_hashes["release-first"]=={a["sha256"]}
assert all_read_hashes["cfg-first"]=={
    "4183b22754037b1ccc355d7f498ed09e3aed036740ada3140928f5ef91f48932",
    b["sha256"]}
ordered=[o["first_sha256"] for o in x["pairs"][1]["run"]["reader_observations"] if o["state"]=="read"]
assert ordered and ordered[0]=="4183b22754037b1ccc355d7f498ed09e3aed036740ada3140928f5ef91f48932"
assert b["sha256"] in ordered
assert all(h==ordered[0] for h in ordered[:ordered.index(b["sha256"])])
assert all(h==b["sha256"] for h in ordered[ordered.index(b["sha256"]):])
mid=HERE/"artifacts/cfg-first-observed-4183b22754037b1ccc355d7f498ed09e3aed036740ada3140928f5ef91f48932.llbc"
obj,end,tail=parsed(mid)
assert end==5514 and tail=="" and literals(obj)==EXPECTED["cfg_alt"]
check_embedded(obj,destination(x["pairs"][1]["run"]["commands"][0]))
assert x["scratch_kib"]<=100*1024
metadata=json.loads((HERE/"REPORT.json").read_text())
assert metadata["observed_at"]=="2026-09-30"
print("PASS: two guarded staggered pairs, raw snapshots, malformed and complete final LLBCs")
