#!/usr/bin/env python3
"""Optional Charon/Aeneas source/model delta for the I137 fixture.

This is one completed mutation, not I138's full failed/late generation sequence.
"""
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS = Path(os.environ.get("I137_TOOLS", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools"))
RUSTBIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON, AENEAS = TOOLS / "bin/charon", TOOLS / "bin/aeneas"
LEANROOT = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LEAN = LEANROOT / "bin/lean"
BACKEND = TOOLS / "aeneas-release/backends/lean"
PACKAGES = ["Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient", "plausible", "mathlib"]
EVENTS = []
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(label, args, cwd, env, timeout=180):
    p = subprocess.run([str(a) for a in args], cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    EVENTS.append({"label":label,"argv":[str(a) for a in args],"cwd":str(cwd),"rc":p.returncode,"stdout":p.stdout,"stderr":p.stderr})
    return p

def main():
    root = Path(os.environ.get("I137_WORK_ROOT", tempfile.mkdtemp(prefix="i137-mutate-"))).resolve()
    root.mkdir(parents=True,exist_ok=True)
    work=root/"mutation"
    if work.exists(): shutil.rmtree(work)
    crate=work/"crate"
    (crate/"src").mkdir(parents=True)
    (crate/"Cargo.toml").write_text('[package]\nname = "golden_vertical"\nversion = "0.1.0"\nedition = "2021"\n')
    base=(HERE/"base-lib.rs").read_text()
    changed=base.replace("wrapping_add(1)","wrapping_add(2)")
    assert changed != base and changed.count("wrapping_add(2)") == 1
    (crate/"src/lib.rs").write_text(changed)
    rustenv=os.environ.copy()
    rustenv.update(RUSTUP_HOME=str(TOOLS/"rustup"),CARGO_HOME=str(TOOLS/"cargo"),CHARON_TOOLCHAIN_IS_IN_PATH="1",CARGO_BUILD_JOBS="1",CARGO_INCREMENTAL="0",CARGO_NET_OFFLINE="true",CARGO_TARGET_DIR=str(work/"target"),PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/"bin"),rustenv.get("PATH","")]))
    assert run("cargo-lock",[RUSTBIN/"cargo","generate-lockfile","--offline"],crate,rustenv).returncode == 0
    llbc=work/"current.llbc"
    assert run("charon-cargo",[CHARON,"cargo","--preset","aeneas","--dest-file",llbc,"--","--manifest-path",crate/"Cargo.toml","--package","golden_vertical","--lib","--offline","--locked"],work,rustenv,300).returncode == 0
    gate_dir=os.environ.get("I137_MODEL_GATE_DIR")
    if gate_dir:
        gate=Path(gate_dir);gate.mkdir(parents=True,exist_ok=True)
        (gate/"entered").write_text("Charon complete; Aeneas pending\n")
        deadline=time.monotonic()+60
        while not (gate/"release").exists() and time.monotonic()<deadline:time.sleep(.01)
        assert (gate/"release").exists(),"model gate was not released"
    generated=work/"generated";generated.mkdir()
    assert run("aeneas",[AENEAS,"-backend","lean","-no-progress-bar","-sequential","-split-files","-gen-lib-entry","-dest",generated,llbc],work,os.environ.copy()).returncode == 0
    consumer=work/"consumer";(consumer/"Current").mkdir(parents=True)
    for rel in ["Current.lean","Types.lean","Funs.lean"]:
        dest=consumer/rel if rel == "Current.lean" else consumer/"Current"/rel
        shutil.copyfile(generated/rel,dest)
    paths=[consumer]
    paths += [BACKEND/".lake/packages"/p/".lake/build/lib/lean" for p in PACKAGES]
    paths += [BACKEND/".lake/build/lib/lean",LEANROOT/"lib/lean"]
    leanenv=os.environ.copy();leanenv.update(LEAN_PATH=os.pathsep.join(str(p) for p in paths if p.is_dir()),LEAN_NUM_THREADS="1")
    for module in ["Current/Types","Current/Funs","Current"]:
        assert run("compile-"+module,[LEAN,"--json","-o",consumer/(module+".olean"),consumer/(module+".lean")],consumer,leanenv).returncode == 0
    old=(HERE/"captured-Proof.lean").read_text()
    (consumer/"OldProof.lean").write_text(old)
    oldcheck=run("old-proof-under-new-model",[LEAN,"--json",consumer/"OldProof.lean"],consumer,leanenv)
    assert oldcheck.returncode != 0 and "rfl" in oldcheck.stdout
    new=old.replace(".ok 1#u32", ".ok 2#u32")
    (consumer/"NewProof.lean").write_text(new)
    newcheck=run("new-proof-under-new-model",[LEAN,"--json",consumer/"NewProof.lean"],consumer,leanenv)
    assert newcheck.returncode == 0
    base_manifest=json.loads((HERE/"model-manifest.json").read_text())
    result={"source_base_sha256":hashlib.sha256(base.encode()).hexdigest(),"source_changed_sha256":sha(crate/"src/lib.rs"),"llbc_changed_sha256":sha(llbc),"base_llbc_sha256":base_manifest["llbc_sha256"],"generated_changed_sha256":{p.name:sha(p) for p in sorted(generated.glob("*.lean"))},"base_generated_sha256":base_manifest["generated_files_sha256"],"new_model_artifacts_sha256":{p.relative_to(consumer).as_posix():sha(p) for p in sorted(consumer.rglob("*.olean"))},"base_model_artifacts_sha256":{k:v for k,v in base_manifest["files"].items() if k.endswith(".olean")},"old_proof_rc":oldcheck.returncode,"new_proof_rc":newcheck.returncode,"old_proof_sha256":sha(consumer/"OldProof.lean"),"new_proof_sha256":sha(consumer/"NewProof.lean"),"charon_sha256":sha(CHARON),"aeneas_sha256":sha(AENEAS),"rustc_sha256":sha(RUSTBIN/"rustc"),"lean_sha256":sha(LEAN)}
    assert result["source_base_sha256"] != result["source_changed_sha256"]
    assert result["generated_changed_sha256"]["Funs.lean"] != result["base_generated_sha256"]["Funs.lean"]
    assert result["new_model_artifacts_sha256"]["Current/Funs.olean"] != result["base_model_artifacts_sha256"]["Current/Funs.olean"]
    result["commands"]=EVENTS
    text=json.dumps(result,indent=2,ensure_ascii=False)+"\n"
    text=text.replace(str(root),"$WORK").replace(str(TOOLS),"$TOOLS")
    (HERE/"mutation-transcript.json").write_text(text)
    (HERE/"changed-lib.rs").write_text(changed)
    (HERE/"changed-Funs.lean").write_bytes((generated/"Funs.lean").read_bytes())
    (HERE/"new-Proof.lean").write_text(new)
    print(json.dumps({"old_proof_rc":oldcheck.returncode,"new_proof_rc":newcheck.returncode,"changed_funs_sha256":result["generated_changed_sha256"]["Funs.lean"]}))

if __name__ == "__main__":main()
