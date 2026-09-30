#!/usr/bin/env python3
"""Offline checker for one preseeded valid Lake server and denied next admission."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent
x=json.loads((ROOT/"results.json").read_text())
pre=json.loads((ROOT/"preseed.json").read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def frames(raw):
    out=[];rest=raw
    while rest:
        assert b"\r\n\r\n" in rest
        h,b=rest.split(b"\r\n\r\n",1)
        m=re.search(rb"Content-Length:\s*(\d+)",h,re.I);assert m
        n=int(m.group(1));assert len(b)>=n
        out.append(json.loads(b[:n]));rest=b[n:]
    return out
def inv(root):
    return {p.relative_to(root).as_posix():sha(p.read_bytes()) for p in root.rglob("*") if p.is_file()}
assert x["schema"]==2 and x["status"]=="stopped"
assert x["error"]=="malformed-server:fresh_admission_denied"
assert len(x["runs"])==1 and x["runs"][0]["label"]=="valid-server"
assert set(x["server_admissions"])=={"valid-server","malformed-server"}
assert x["admission"]["memory"]["fraction"]>.30 and x["admission"]["disk_free"]>10*1024**3
assert x["server_admissions"]["valid-server"]["memory"]["fraction"]>.30
assert x["server_admissions"]["malformed-server"]["memory"]["fraction"]<=.30
assert all(z["disk_free"]>10*1024**3 for z in x["server_admissions"].values())
assert x["lake_sha256"]=="9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
assert x["lean_sha256"]=="b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert x["preseed_sha256"]==sha((ROOT/"preseed.json").read_bytes())
assert pre["work_file_count"]==36 and pre["source_package"]=="anneal-3731-i092-malformed-manifest-preflight-2026-09-30"
assert len(pre["work_sha256"])==36
prior_candidates=(ROOT.parent/pre["source_package"],
                  ROOT.parent/"i092-malformed-manifest-preflight")
prior=next((p for p in prior_candidates if (p/"work").is_dir()),None)
assert prior is not None and sha((prior/"results.json").read_bytes())==pre["source_results_sha256"]
assert inv(prior/"work")==pre["work_sha256"]
work=ROOT/"work"
assert pre["work_sha256"]["producer/.lake/build/lib/lean/Dep.olean"]=="cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b"
assert pre["work_sha256"]["consumer/lake-manifest.json"]=="4cf0c1b12e990e08af5075710832c08e1df761220ab141edb2da7211cb2fd230"
assert pre["work_sha256"]["producer/Dep.lean"]==x["producer_source_sha256"]=="15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2"
assert pre["work_sha256"]["consumer/Generated.lean"]==x["consumer_source_sha256"]=="086270efb5c0dc2ec7d11571e0fa6499c90f8132dda90119258e77947f58e702"
assert (work/"producer/Dep.lean").read_bytes()==b"def depValue : Nat := 7\n"
source=b"import Dep\ntheorem generatedEq : depValue = 7 := by rfl\n#eval depValue\n"
assert (work/"consumer/Generated.lean").read_bytes()==source
good=ROOT/"fixtures/valid-lake-manifest.json"
bad=ROOT/"fixtures/malformed-lake-manifest.json"
sem=ROOT/"fixtures/semantic-no-dependency-lake-manifest.json"
assert good.is_file() and bad.read_bytes()==b"{\n" and sem.is_file()
assert sha(good.read_bytes())==x["manifest_sha256"]["valid"]=="4cf0c1b12e990e08af5075710832c08e1df761220ab141edb2da7211cb2fd230"
assert sha(bad.read_bytes())==x["manifest_sha256"]["malformed"]
assert json.loads(sem.read_text())["packages"]==[]
r=x["runs"][0]
assert r["exit"]==0 and r["abort"] is None and r["client_errors"]==[]
assert r["elapsed"]<30 and r["readiness_quiescent"] is True and r["first_diagnostic_observed"] is True
assert 0<r["diagnostic_wait_seconds"]<8
assert Path(r["argv"][0]).is_file() and sha(Path(r["argv"][0]).read_bytes())==x["lake_sha256"]
assert r["argv"][1:]==["--keep-toolchain","--no-ansi","--no-build","--no-cache","serve"]
recorded_work=Path(r["cwd"]).parent
assert Path(r["cwd"]).is_absolute() and Path(r["cwd"]).name=="consumer"
assert recorded_work.name=="work" and recorded_work.parent.name=="i092-preseeded-server-readiness"
assert r["cwd"]==str(recorded_work/"consumer")
for key, name in (("HOME","home"),("XDG_CACHE_HOME","xdg"),("LAKE_CACHE_DIR","cache")):
    assert r["env_overrides"][key]==str(recorded_work/name)
    assert pre["source_package"] not in r["env_overrides"][key]
assert r["env_overrides"]["LEAN_PATH"] is None
assert r["env_overrides"]["LAKE_NO_NET"]=="1" and r["env_overrides"]["LAKE_NO_CACHE"]=="1"
assert r["env_overrides"]["LAKE_ARTIFACT_CACHE"]=="false"
assert r["before"]==r["after"]
assert {k:v["sha256"] for k,v in r["before"].items()}==pre["work_sha256"]
assert x["phases"]["valid"]["producer_before"]==x["phases"]["valid"]["producer_after"]
assert x["phases"]["valid"]["cache_before"]==x["phases"]["valid"]["cache_after"]
assert "producer_after" not in x["phases"]["malformed"] and "semantic-no-dependency" not in x["phases"]
for s in r["resource_samples"]:
    assert s["reclaimable"]>=.20 and s["disk_free"]>=10*1024**3
    assert s["group_rss_kib"]<=1200*1024 and s["scratch_bytes"]<=100*1024**2
samples=r["resource_samples"]
assert len(samples)==78
assert abs(min(s["reclaimable"] for s in samples)-0.27396583557128906)<1e-12
assert min(s["disk_free"] for s in samples)==18765172736
assert max(s["group_rss_kib"] for s in samples)==949024
assert max(s["scratch_bytes"] for s in samples)==235464
for suffix in ("stdout","stderr"):
    raw=(ROOT/"raw"/f"valid-server.{suffix}").read_bytes()
    assert sha(raw)==r[f"{suffix}_sha256"]
messages=frames((ROOT/"raw/valid-server.stdout").read_bytes())
assert messages==r["decoded_messages"]==[e["message"] for e in r["received_events"]]
sent=[e["message"] for e in r["sent_events"]]
assert [m["method"] for m in sent]==["initialize","initialized","textDocument/didOpen",
                                   "$/lean/plainGoal","shutdown","exit"]
assert sent[0]["id"]==1 and sent[0]["params"]["rootUri"]==Path(r["cwd"]).as_uri()
uri=Path(r["cwd"],"Generated.lean").as_uri()
assert sent[2]["params"]["textDocument"]=={"uri":uri,"languageId":"lean4","version":1,"text":source.decode()}
assert sent[3]["id"]==2 and sent[3]["params"]=={"textDocument":{"uri":uri},"position":{"line":1,"character":40}}
assert sent[4]["id"]==3
assert any(m.get("id")==1 and "result" in m for m in messages)
assert any(m.get("id")==3 and "result" in m for m in messages)
goals=[m for m in messages if m.get("id")==2 and "result" in m]
assert len(goals)==1 and goals[0]==r["goal_response"]
assert goals[0]["result"]["goals"]==["⊢ depValue = 7"]
diag=[m for m in messages if m.get("method")=="textDocument/publishDiagnostics"
      and m.get("params",{}).get("uri")==uri]
assert diag and any(any(d.get("message")=="7" and d.get("severity")==3
                             for d in m["params"]["diagnostics"]) for m in diag)
prog=[m for m in messages if m.get("method")=="$/lean/fileProgress"
      and m.get("params",{}).get("textDocument",{}).get("uri")==uri]
assert prog and prog[-1]["params"]["processing"]==[]
assert x["phases"]["malformed"]["manifest_sha256"]==sha(bad.read_bytes())
current=inv(work)
assert current.keys()==pre["work_sha256"].keys()
assert {k for k in current if current[k]!=pre["work_sha256"][k]}=={"consumer/lake-manifest.json"}
assert current["consumer/lake-manifest.json"]==sha(bad.read_bytes())
assert x["final_scratch_bytes"]<=100*1024**2
meta=json.loads((ROOT/"REPORT.json").read_text())
assert meta["observed_at"]=="2026-09-30"
print("PASS: preseeded valid server goal and bounded malformed-admission denial; no malformed server")
