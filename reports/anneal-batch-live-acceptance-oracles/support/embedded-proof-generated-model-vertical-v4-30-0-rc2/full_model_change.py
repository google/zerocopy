#!/usr/bin/env python3
"""Disposable real-model I138 schedule over the I137 fixture.

Charon/Aeneas and Lean execute; source authority, selection, and fencing are
fixture-local Python. No Anneal runtime or publication service is invoked.
"""
import hashlib
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

import probe

HERE=Path(__file__).resolve().parent
ROOT=Path(os.environ["I137_WORK_ROOT"]).resolve()
WORK=ROOT/"full-model-change"
CHARON=probe.TOOLS/"bin/charon"
RUSTBIN=probe.TOOLS/"rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
E=probe.EVENTS
def sha(x):return hashlib.sha256(x).hexdigest()
def bundle(model):
    return {p.relative_to(model).as_posix():probe.filehash(p) for p in sorted(model.rglob("*")) if p.is_file()}
def proof(value):
    return f"import Current\ntheorem obl_inc : golden_vertical.inc 0#u32 = .ok {value}#u32 := by\n  rfl\n"
def query(server,work,name,text,version):
    uri=(work/name).as_uri()
    server.send({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":uri,"languageId":"lean","version":version,"text":text}}})
    wait=server.request("textDocument/waitForDiagnostics",{"uri":uri,"version":version})
    goal=server.request("$/lean/plainGoal",{"textDocument":{"uri":uri},"position":{"line":2,"character":len(text.splitlines()[2])}})
    return {"uri":uri,"version":version,"wait":wait,"goal":goal}
def batch(label,work,text,value):
    env=probe.env_for(work)
    src=work/(label+".lean");src.write_text(text)
    checked=probe.command(label+":batch",[probe.LEAN,"--json",src],work,env)
    if checked.returncode!=0:return {"proof_sha256":probe.filehash(src),"batch_rc":checked.returncode,"oracle_rc":None}
    artifact=work/(label+".olean")
    compiled=probe.command(label+":compile",[probe.LEAN,"--json","-o",artifact,src],work,env)
    assert compiled.returncode==0
    oracle=work/(label+"Oracle.lean")
    oracle.write_text(f"import {label}\nexample : golden_vertical.inc 0#u32 = .ok {value}#u32 := obl_inc\n#print axioms obl_inc\n")
    check=probe.command(label+":oracle",[probe.LEAN,"--json",oracle],work,env)
    return {"proof_sha256":probe.filehash(src),"batch_rc":checked.returncode,"compiled_olean_sha256":probe.filehash(artifact),"oracle_rc":check.returncode,"oracle_stdout":check.stdout}
def authority_advance(authority,expected_rev,expected_sha,new_source,label):
    ok=authority["rev"]==expected_rev and sha(authority["source"])==expected_sha
    if ok:authority.update(rev=expected_rev+1,source=new_source)
    probe.record("authority_cas",label=label,accepted=ok,expected_rev=expected_rev,actual_rev=authority["rev"],expected_sha256=expected_sha,actual_sha256=sha(authority["source"]))
    return ok
def publish(selected,authority,candidate,label):
    ok=(candidate["rev"]==authority["rev"] and candidate["host_sha256"]==sha(authority["source"]) and candidate["model_files_sha256"]==bundle(candidate["model_path"]) and all(k in candidate["model_files_sha256"] for k in ["Current.olean","Current/Funs.olean","Current/Types.olean"]) and (not selected or candidate["rev"]>selected["rev"]))
    if ok:
        selected.clear();selected.update({k:v for k,v in candidate.items() if k!="model_path"})
    probe.record("publication",label=label,accepted=ok,candidate_rev=candidate["rev"],candidate_generation_id=candidate["generation_id"],current_host_rev=authority["rev"],selected_rev=selected.get("rev"),selected_generation_id=selected.get("generation_id"))
    return ok
def main():
    assert ROOT.is_dir()
    E.clear();probe.START=time.monotonic()
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    old_host=(HERE/"unsaved-host-after.rs").read_bytes()
    changed_source=(HERE/"changed-lib.rs").read_bytes()
    new_host=changed_source+b"\n// anneal: theorem obl_inc : golden_vertical.inc 0#u32 = .ok 2#u32 := by\n// anneal:   rfl\n"
    failed_source=changed_source+b"\npub fn unfinished( -> u32 {\n"
    authority={"rev":0,"source":old_host}
    selected={}
    old_work=WORK/"old";old_work.mkdir();shutil.copytree(HERE/"model",old_work/"model")
    old_model=bundle(old_work/"model")
    old_generation=sha(json.dumps({"host_base":probe.filehash(HERE/"base-lib.rs"),"model":old_model},sort_keys=True).encode())
    old_candidate={"rev":1,"host_sha256":sha(old_host),"generation_id":old_generation,"model_files_sha256":old_model,"model_path":old_work/"model"}
    assert authority_advance(authority,0,sha(old_host),old_host,"select-old-host")
    assert publish(selected,authority,old_candidate,"old-A")
    old_text=proof(1)
    old_server=probe.Server(old_work,probe.env_for(old_work))
    late_proc=None
    child=None
    try:
        before=query(old_server,old_work,"LiveOld.lean",old_text,1)
        probe.record("query_before",state="selected-old",selected_generation_id=selected["generation_id"],host_rev=authority["rev"],result=before)
        assert before["goal"]["result"]["rendered"]=="no goals"
        old_batch=batch("OldCaptured",old_work,old_text,1)
        assert old_batch["batch_rc"]==old_batch["oracle_rc"]==0
        probe.record("fresh_old",**old_batch,selected_generation_id=selected["generation_id"])
        # Start a real old-context compiler and hold it at a Lean tactic gate.
        late=WORK/"late-old";late.mkdir();shutil.copytree(HERE/"model",late/"model")
        late_text='import Current\ntheorem obl_inc : golden_vertical.inc 0#u32 = .ok 1#u32 := by\n  run_tac do\n    IO.FS.writeFile "gate.entered" "1"\n    while !(← (System.FilePath.mk "gate.release").pathExists) do\n      IO.sleep 10\n  rfl\n'
        (late/"LateOld.lean").write_text(late_text)
        late_proc=subprocess.Popen([str(probe.LEAN),"--json",str(late/"LateOld.lean")],cwd=late,env=probe.env_for(late),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        probe.record("late_old_started",pid=late_proc.pid,revision=1,generation_id=old_generation,proof_sha256=sha(late_text.encode()))
        deadline=time.monotonic()+20
        while not (late/"gate.entered").exists() and time.monotonic()<deadline:time.sleep(.01)
        assert (late/"gate.entered").exists()
        probe.record("late_old_gate_entered",pid=late_proc.pid)
        assert authority_advance(authority,1,sha(old_host),failed_source,"old-to-failing-F")
        # Actual Charon/Cargo failure over invalid intermediate Rust source.
        failed=WORK/"failed";crate=failed/"crate";(crate/"src").mkdir(parents=True)
        (crate/"Cargo.toml").write_text('[package]\nname = "golden_vertical"\nversion = "0.1.0"\nedition = "2021"\n')
        (crate/"src/lib.rs").write_bytes(failed_source)
        rustenv=os.environ.copy();rustenv.update(RUSTUP_HOME=str(probe.TOOLS/"rustup"),CARGO_HOME=str(probe.TOOLS/"cargo"),CHARON_TOOLCHAIN_IS_IN_PATH="1",CARGO_BUILD_JOBS="1",CARGO_INCREMENTAL="0",CARGO_NET_OFFLINE="true",CARGO_TARGET_DIR=str(failed/"target"),PATH=os.pathsep.join([str(RUSTBIN),str(probe.TOOLS/"bin"),rustenv.get("PATH","")]))
        lock=probe.command("failed:lock",[RUSTBIN/"cargo","generate-lockfile","--offline"],crate,rustenv);assert lock.returncode==0
        failed_llbc=failed/"failed.llbc"
        failure=probe.command("failed:charon",[CHARON,"cargo","--preset","aeneas","--dest-file",failed_llbc,"--","--manifest-path",crate/"Cargo.toml","--package","golden_vertical","--lib","--offline","--locked"],failed,rustenv)
        assert failure.returncode!=0 and not failed_llbc.exists()
        provisional={"host_rev":authority["rev"],"host_sha256":sha(authority["source"]),"status":"failed-preparation","selected_last_good_rev":selected["rev"],"selected_last_good_generation_id":selected["generation_id"],"failed_charon_rc":failure.returncode}
        probe.record("provisional_failure",**provisional)
        during=old_server.request("$/lean/plainGoal",{"textDocument":{"uri":before["uri"]},"position":{"line":2,"character":len(old_text.splitlines()[2])}})
        probe.record("query_during",state="last-known-good-old; stale-for-current-host",selected_generation_id=selected["generation_id"],host_rev=authority["rev"],result=during)
        assert during["result"]["rendered"]=="no goals"
        assert authority_advance(authority,2,sha(failed_source),new_host,"failing-F-to-new-B")
        # Hold the real B pipeline after Charon and before Aeneas. Query the old
        # server while a new model is pending, then release preparation.
        model_gate=WORK/"model-gate"
        child_env=os.environ.copy();child_env.update(I137_WORK_ROOT=str(ROOT),I137_MODEL_GATE_DIR=str(model_gate))
        child=subprocess.Popen(["python3",str(HERE/"mutate_model.py")],cwd=HERE,env=child_env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        deadline=time.monotonic()+60
        while not (model_gate/"entered").exists() and child.poll() is None and time.monotonic()<deadline:time.sleep(.01)
        assert (model_gate/"entered").exists() and child.poll() is None
        probe.record("new_model_gate_entered",pid=child.pid,host_rev=authority["rev"],selected_rev=selected["rev"],selected_generation_id=selected["generation_id"])
        pending=old_server.request("$/lean/plainGoal",{"textDocument":{"uri":before["uri"]},"position":{"line":2,"character":len(old_text.splitlines()[2])}})
        probe.record("query_during_new_preparation",state="pending-new; old-selected-stale-for-current-host",host_rev=authority["rev"],selected_rev=selected["rev"],selected_generation_id=selected["generation_id"],child_alive=child.poll() is None,result=pending)
        assert pending["result"]["rendered"]=="no goals" and child.poll() is None
        (model_gate/"release").write_text("release")
        probe.record("new_model_gate_released",pid=child.pid)
        child_out,child_err=child.communicate(timeout=300)
        probe.record("real_new_model_pipeline",rc=child.returncode,stdout=child_out,stderr=child_err)
        assert child.returncode==0,child_err
        mutation=json.loads((HERE/"mutation-transcript.json").read_text())
        new_work=WORK/"new";new_work.mkdir();(new_work/"model/Current").mkdir(parents=True)
        generated_consumer=ROOT/"mutation/consumer"
        for rel in ["Current.lean","Current.olean","Current/Types.lean","Current/Types.olean","Current/Funs.lean","Current/Funs.olean"]:
            shutil.copyfile(generated_consumer/rel,new_work/"model"/rel)
        new_model=bundle(new_work/"model")
        assert new_model["Current/Funs.olean"]!=old_model["Current/Funs.olean"]
        assert new_model["Current.olean"]==old_model["Current.olean"]
        new_generation=sha(json.dumps({"source":mutation["source_changed_sha256"],"llbc":mutation["llbc_changed_sha256"],"model":new_model},sort_keys=True).encode())
        new_text=proof(2)
        new_batch=batch("NewCaptured",new_work,new_text,2)
        assert new_batch["batch_rc"]==new_batch["oracle_rc"]==0
        old_on_new=batch("OldOnNew",new_work,old_text,1)
        assert old_on_new["batch_rc"]!=0
        new_on_old=batch("NewOnOld",old_work,new_text,2)
        assert new_on_old["batch_rc"]!=0
        probe.record("fresh_comparison",old_under_old=old_batch,new_under_new=new_batch,old_under_new=old_on_new,new_under_old=new_on_old,old_generation_id=old_generation,new_generation_id=new_generation)
        new_candidate={"rev":3,"host_sha256":sha(new_host),"generation_id":new_generation,"model_files_sha256":new_model,"model_path":new_work/"model"}
        assert publish(selected,authority,new_candidate,"new-B")
        assert not authority_advance(authority,1,sha(old_host),old_host,"stale-old-host-edit")
        new_server=probe.Server(new_work,probe.env_for(new_work))
        try:
            after=query(new_server,new_work,"LiveNew.lean",new_text,1)
            stale=query(new_server,new_work,"LiveOldOnNew.lean",old_text,1)
            probe.record("query_after",state="selected-new",selected_generation_id=selected["generation_id"],host_rev=authority["rev"],fresh=after,old_proof_on_new=stale)
            assert after["goal"]["result"]["rendered"]=="no goals"
            assert stale["goal"]["result"]["rendered"]!="no goals"
        finally:new_server.close()
        # The actual old compiler completes only after B is selected.
        (late/"gate.release").write_text("release")
        probe.record("late_old_gate_released",after_selected_rev=selected["rev"])
        late_out,late_err=late_proc.communicate(timeout=30)
        probe.record("late_old_finished",rc=late_proc.returncode,stdout=late_out,stderr=late_err,old_generation_id=old_generation)
        assert late_proc.returncode==0
        assert not publish(selected,authority,old_candidate,"late-old-A")
        probe.record("final_state",host_rev=authority["rev"],host_sha256=sha(authority["source"]),selected_rev=selected["rev"],selected_generation_id=selected["generation_id"],selected_model_files_sha256=selected["model_files_sha256"],old_generation_id=old_generation,failed_host_sha256=sha(failed_source),new_generation_id=new_generation)
        assert selected["rev"]==3 and selected["generation_id"]==new_generation
        (HERE/"failed-lib.rs").write_bytes(failed_source)
        (HERE/"new-unsaved-host.rs").write_bytes(new_host)
        (HERE/"full-model-change-old-Proof.lean").write_text(old_text)
        (HERE/"full-model-change-new-Proof.lean").write_text(new_text)
    finally:
        old_server.close()
        if child is not None and child.poll() is None:
            (WORK/"model-gate/release").write_text("release")
            child.kill();child.wait()
        if late_proc is not None and late_proc.poll() is None:
            (WORK/"late-old/gate.release").write_text("release")
            late_proc.kill();late_proc.wait()
    transcript=json.dumps(E,indent=2,ensure_ascii=False)+"\n"
    transcript=transcript.replace(str(ROOT),"$WORK").replace(str(probe.TOOLS),"$TOOLS")
    (HERE/"full-model-change-transcript.json").write_text(transcript)
    print(json.dumps({"events":len(E),"old_generation_id":old_generation,"new_generation_id":new_generation,"selected_rev":selected["rev"],"failed_charon_rc":failure.returncode,"late_old_rc":late_proc.returncode}))
if __name__=="__main__":main()
