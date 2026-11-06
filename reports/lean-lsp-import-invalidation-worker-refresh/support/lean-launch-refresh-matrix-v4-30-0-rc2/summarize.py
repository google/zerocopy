#!/usr/bin/env python3
"""Validate only the bounded launch/refresh observations in REPORT.md."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
a=json.loads((ROOT/"transcript.json").read_text())
def one(kind,label=None,phase=None,name=None):
    xs=[x for x in a if x["kind"]==kind and (label is None or x.get("label")==label)
        and (phase is None or x.get("phase")==phase) and (name is None or x.get("name")==name)]
    assert len(xs)==1,(kind,label,phase,name,len(xs))
    return xs[0]
def goal(sample,key):
    result=sample["goals"][key].get("result")
    return result.get("goals") if isinstance(result,dict) else result
def texts(sample):
    return [d.get("message","") for d in (sample["diagnostics"] or {}).get("diagnostics",[])]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

subject=one("subject")
assert subject["host_ram_bytes"]==8589934592
assert subject["free_percent"]>=25
assert one("pressure_end")["free_percent"]>=25
assert all(x["free_percent"]>=25 for x in a if x["kind"]=="pressure_before_session")
assert not any(x["kind"] in ("fatal","cleanup_kill","stop_error") for x in a)
assert len([x for x in a if x["kind"]=="stop" and x["rc"]==0])==9
assert one("completed")["seq"]==len(a)-1

pre7=[x for x in a if x["kind"]=="prebuilt" and x["value"]==7][0]
pre9=[x for x in a if x["kind"]=="prebuilt" and x["value"]==9][0]
assert pre7["source_sha256"]!=pre9["source_sha256"]
matrix={}
baseline_sha=None;rebuilt_sha=None
for mode in ("direct","lake-env","lake-serve"):
    matrix[mode]={}
    for variant in ("source","olean"):
        label=mode+"-"+variant
        b=one("sample",label,"baseline")
        old=one("sample",label,"old-open")
        new=one("sample",label,"new-open")
        old_after_new=one("sample",label,"old-after-new")
        reopened=one("sample",label,"reopened")
        if baseline_sha is None:baseline_sha=b["artifact"]["sha256"]
        assert b["artifact"]["sha256"]==baseline_sha
        assert b["source_sha256"]==pre7["source_sha256"]
        assert "7" in texts(b) and goal(b,"rfl-end")==[]
        assert "7" in texts(old) and goal(old,"rfl-end")==[]
        assert "7" in texts(old_after_new) and goal(old_after_new,"rfl-end")==[]
        assert old_after_new["artifact"]["sha256"]==new["artifact"]["sha256"]
        for x in (new,reopened):
            assert "9" in texts(x)
            assert any("Tactic `rfl` failed" in t for t in texts(x))
            assert goal(x,"rfl-end")==["⊢ selected = 7"]
            assert x["wait"]["result"]=={}
        for x in (b,old,new,old_after_new,reopened):
            assert goal(x,"rfl-start")==goal(x,"exact-start")==["⊢ selected = 7"]
            assert goal(x,"exact-inside")==goal(x,"exact-end")==goal(x,"eof")==["⊢ selected = 7"]
            assert x["tree"]["rss_bytes"]<subject["rss_cap_bytes"]
        if variant=="source":
            change=one("source_only_change",label)
            assert change["artifact"]["sha256"]==baseline_sha
            assert change["source_sha256"]==pre9["source_sha256"]
            assert old["artifact"]["sha256"]==baseline_sha
            if rebuilt_sha is None:rebuilt_sha=new["artifact"]["sha256"]
            assert new["artifact"]["sha256"]==reopened["artifact"]["sha256"]==rebuilt_sha
            assert rebuilt_sha!=baseline_sha
            assert new["source_sha256"]==pre9["source_sha256"]
        else:
            change=one("olean_only_change",label)
            assert change["artifact"]["sha256"]==pre9["artifact_sha256"]
            assert change["source_sha256"]==pre7["source_sha256"]
            assert change["artifact"]["mtime_ns"]<b["artifact"]["mtime_ns"]
            assert change["artifact"]["hash_sidecar"]==b["artifact"]["hash_sidecar"]
            assert old["artifact"]["sha256"]==new["artifact"]["sha256"]==reopened["artifact"]["sha256"]==pre9["artifact_sha256"]
            assert new["source_sha256"]==pre7["source_sha256"]
            missing=one("sample",label,"missing-import")
            assert missing["wait"]["result"]=={}
            assert any("unknown module prefix 'Missing'" in t for t in texts(missing))
            assert all(goal(missing,k) is None for k in missing["goals"])
            fresh=one("sample",label+"-fresh","fresh-server")
            assert "9" in texts(fresh) and goal(fresh,"rfl-end")==["⊢ selected = 7"]
            assert fresh["artifact"]["sha256"]==pre9["artifact_sha256"]
            setup_bad=one("setup_file",label,name="Bad.lean")
            assert setup_bad["rc"]==0 and json.loads(setup_bad["stdout"])["importArts"]=={}
            override=one("setup_file_header_override",label)
            assert override["rc"]==0 and json.loads(override["stdout"])["importArts"]=={}
            assert override["before"]["sha256"]==override["after"]["sha256"]==pre9["artifact_sha256"]
            rehash=one("setup_file_rehash",label)
            assert rehash["rc"]==0 and rehash["before"]["sha256"]==rehash["after"]["sha256"]==pre9["artifact_sha256"]
        setup=one("setup_file",label,name="Proof.lean")
        assert setup["rc"]==0 and "Dep" in json.loads(setup["stdout"])["importArts"]
        assert setup["before"]["sha256"]==setup["after"]["sha256"]
        batch=one("batch_after",label)
        assert batch["rc"]==1 and '"data":"9"' in batch["stdout"]
        assert batch["artifact"]["sha256"]==(rebuilt_sha if variant=="source" else pre9["artifact_sha256"])
        matrix[mode][variant]=dict(baseline_olean=b["artifact"]["sha256"],
            old_open_olean=old["artifact"]["sha256"],new_open_olean=new["artifact"]["sha256"],
            old_after_new_olean=old_after_new["artifact"]["sha256"],
            reopened_olean=reopened["artifact"]["sha256"],
            old_open_eval=7,new_open_eval=9,old_after_new_eval=7,reopened_eval=9,
            max_sampled_rss_bytes=max(x["tree"]["rss_bytes"] for x in (b,old,new,old_after_new,reopened)))

assert baseline_sha!=rebuilt_sha!=pre9["artifact_sha256"]
result=dict(status="bounded matrix passed",events=len(a),
    probe_sha256=sha(ROOT/"probe.py"),transcript_sha256=sha(ROOT/"transcript.json"),
    lean_sha256=subject["lean_sha256"],lake_sha256=subject["lake_sha256"],
    baseline_olean_sha256=baseline_sha,rebuilt_source9_olean_sha256=rebuilt_sha,
    prebuilt9_olean_sha256=pre9["artifact_sha256"],
    free_percent_start=subject["free_percent"],free_percent_end=one("pressure_end")["free_percent"],
    max_sampled_rss_bytes=max(x["tree"]["rss_bytes"] for x in a if x["kind"]=="sample"),
    matrix=matrix)
(ROOT/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
