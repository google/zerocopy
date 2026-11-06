#!/usr/bin/env python3
"""Offline consistency checks for retained I137/I138-partial evidence."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
def sha(data): return hashlib.sha256(data).hexdigest()
def filehash(name): return sha((HERE/name).read_bytes())
def single(events,kind):
    matches=[e for e in events if e["kind"]==kind]
    assert len(matches)==1,(kind,len(matches))
    return matches[0]
def main():
    manifest=json.loads((HERE/"model-manifest.json").read_text())
    actual={p.relative_to(HERE/"model").as_posix():sha(p.read_bytes()) for p in sorted((HERE/"model").rglob("*")) if p.is_file()}
    assert actual==manifest["files"]
    generation=sha(json.dumps(manifest,sort_keys=True).encode())
    events=json.loads((HERE/"transcript.json").read_text())
    assert [e["seq"] for e in events]==list(range(len(events)))
    context=single(events,"context")
    assert context["generation_id"]==generation
    assert context["source_base_sha256"]==filehash("base-lib.rs")
    assert context["model_files_sha256"]==actual
    before,after=(HERE/"unsaved-host-before.rs").read_bytes(),(HERE/"unsaved-host-after.rs").read_bytes()
    captured=(HERE/"captured-Proof.lean").read_bytes()
    start,end=single(events,"projection_initial"),single(events,"projection_edited")
    assert start["host_sha256"]==sha(before) and end["host_sha256"]==sha(after)
    assert start["projected_sha256"]==sha(start["text"].encode())
    assert end["projected_sha256"]==sha(captured)==sha(end["text"].encode())
    patch=single(events,"mapped_proof_patch")
    hs,he=patch["host_byte_range"];ps,pe=patch["projected_byte_range"]
    assert before[hs:he]==b"exact ?_" and start["text"].encode()[ps:pe]==b"exact ?_"
    assert before[:hs]+b"rfl"+before[he:]==after
    sends=[e["message"] for e in events if e["kind"]=="lsp_client"]
    opens=[m for m in sends if m.get("method")=="textDocument/didOpen"]
    changes=[m for m in sends if m.get("method")=="textDocument/didChange"]
    assert len(opens)==len(changes)==1
    assert opens[0]["params"]["textDocument"]["version"]==1
    assert opens[0]["params"]["textDocument"]["text"].encode()==start["text"].encode()
    assert changes[0]["params"]["textDocument"]["version"]==2
    assert changes[0]["params"]["contentChanges"][0]["text"].encode()==captured
    first,second=single(events,"initial_query"),single(events,"edited_query")
    assert "⊢" in first["goal"]["result"]["rendered"]
    assert second["goal"]["result"]["rendered"]=="no goals"
    assert first["disk_shadow_sha256"]==second["disk_shadow_sha256"]
    cas=[e for e in events if e["kind"]=="host_patch_cas"]
    assert [e["accepted"] for e in cas]==[True,False,False]
    commands={e["label"]:e for e in events if e["kind"]=="command"}
    assert set(commands)=={"fresh-batch-captured","compile-captured","fixed-proposition-and-axioms"}
    assert all(e["rc"]==0 for e in commands.values())
    assert "sorryAx" not in commands["fixed-proposition-and-axioms"]["stdout"]
    assert "propext" in commands["fixed-proposition-and-axioms"]["stdout"]
    result=single(events,"result")
    assert result["accepted"] and result["generation_id"]==generation
    assert result["captured_sha256"]==sha(captured)
    assert result["imported_model_olean_sha256"]==actual["Current.olean"]
    assert result["host_disk_sha256"]==filehash("base-lib.rs")
    mutation=json.loads((HERE/"mutation-transcript.json").read_text())
    assert mutation["source_changed_sha256"]==filehash("changed-lib.rs")
    assert mutation["generated_changed_sha256"]["Funs.lean"]==filehash("changed-Funs.lean")
    assert mutation["new_proof_sha256"]==filehash("new-Proof.lean")
    assert mutation["old_proof_sha256"]==sha(captured)
    assert mutation["old_proof_rc"]!=0 and mutation["new_proof_rc"]==0
    assert mutation["base_model_artifacts_sha256"]["Current/Funs.olean"] != mutation["new_model_artifacts_sha256"]["Current/Funs.olean"]
    assert mutation["base_model_artifacts_sha256"]["Current.olean"] == mutation["new_model_artifacts_sha256"]["Current.olean"]
    calls={e["label"]:e for e in mutation["commands"]}
    assert calls["charon-cargo"]["rc"]==calls["aeneas"]["rc"]==0
    assert calls["old-proof-under-new-model"]["rc"]!=0
    assert calls["new-proof-under-new-model"]["rc"]==0
    full=json.loads((HERE/"full-model-change-transcript.json").read_text())
    assert [e["seq"] for e in full]==list(range(len(full)))
    def one(kind):
        return single(full,kind)
    old_model=actual
    old_generation=sha(json.dumps({"host_base":filehash("base-lib.rs"),"model":old_model},sort_keys=True).encode())
    new_model=dict(mutation["new_model_artifacts_sha256"])
    new_model.update({"Current.lean":mutation["generated_changed_sha256"]["Current.lean"],"Current/Funs.lean":mutation["generated_changed_sha256"]["Funs.lean"],"Current/Types.lean":mutation["generated_changed_sha256"]["Types.lean"]})
    retained_new={p.relative_to(HERE/"new-model").as_posix():sha(p.read_bytes()) for p in sorted((HERE/"new-model").rglob("*")) if p.is_file()}
    assert retained_new==new_model
    new_manifest=json.loads((HERE/"new-model-manifest.json").read_text())
    assert new_manifest["files_sha256"]==new_model
    assert new_manifest["llbc_sha256"]==filehash("new-current.llbc")==mutation["llbc_changed_sha256"]
    assert new_manifest["source_sha256"]==filehash("changed-lib.rs")
    new_generation=sha(json.dumps({"source":mutation["source_changed_sha256"],"llbc":mutation["llbc_changed_sha256"],"model":new_model},sort_keys=True).encode())
    assert old_generation!=new_generation
    assert filehash("failed-lib.rs")==one("provisional_failure")["host_sha256"]
    assert filehash("new-unsaved-host.rs")==one("final_state")["host_sha256"]
    assert filehash("full-model-change-old-Proof.lean")==one("fresh_comparison")["old_under_old"]["proof_sha256"]
    assert filehash("full-model-change-new-Proof.lean")==one("fresh_comparison")["new_under_new"]["proof_sha256"]
    publications=[e for e in full if e["kind"]=="publication"]
    assert [(e["label"],e["accepted"],e["selected_rev"]) for e in publications]==[("old-A",True,1),("new-B",True,3),("late-old-A",False,3)]
    assert publications[0]["selected_generation_id"]==old_generation
    assert publications[1]["selected_generation_id"]==publications[2]["selected_generation_id"]==new_generation
    cas=[e for e in full if e["kind"]=="authority_cas"]
    assert [e["accepted"] for e in cas]==[True,True,True,False]
    failure=one("provisional_failure")
    assert failure["host_rev"]==2 and failure["status"]=="failed-preparation"
    assert failure["selected_last_good_rev"]==1 and failure["selected_last_good_generation_id"]==old_generation
    full_commands={e["label"]:e for e in full if e["kind"]=="command"}
    assert full_commands["failed:charon"]["rc"]!=0 and full_commands["failed:charon"]["rc"]==failure["failed_charon_rc"]
    assert one("real_new_model_pipeline")["rc"]==0
    assert one("query_before")["result"]["goal"]["result"]["rendered"]=="no goals"
    assert one("query_during")["result"]["result"]["rendered"]=="no goals"
    assert one("query_during")["host_rev"]==2
    assert "stale-for-current-host" in one("query_during")["state"]
    assert one("query_during")["selected_generation_id"]==old_generation
    pending=one("query_during_new_preparation")
    assert pending["host_rev"]==3 and pending["selected_rev"]==1
    assert pending["selected_generation_id"]==old_generation and pending["child_alive"]
    assert "old-selected-stale-for-current-host" in pending["state"]
    assert pending["result"]["result"]["rendered"]=="no goals"
    after_query=one("query_after")
    assert after_query["fresh"]["goal"]["result"]["rendered"]=="no goals"
    assert after_query["old_proof_on_new"]["goal"]["result"]["rendered"]!="no goals"
    assert after_query["selected_generation_id"]==new_generation
    compare=one("fresh_comparison")
    assert compare["old_generation_id"]==old_generation and compare["new_generation_id"]==new_generation
    assert (compare["old_under_old"]["batch_rc"],compare["old_under_old"]["oracle_rc"])==(0,0)
    assert (compare["new_under_new"]["batch_rc"],compare["new_under_new"]["oracle_rc"])==(0,0)
    assert compare["old_under_new"]["batch_rc"]!=0 and compare["new_under_old"]["batch_rc"]!=0
    order={e["kind"]:e["seq"] for e in full if e["kind"] in ["late_old_gate_entered","provisional_failure","query_during","new_model_gate_entered","query_during_new_preparation","new_model_gate_released","real_new_model_pipeline","fresh_comparison","query_after","late_old_gate_released","late_old_finished","final_state"]}
    assert order["late_old_gate_entered"]<order["provisional_failure"]<order["query_during"]<order["new_model_gate_entered"]<order["query_during_new_preparation"]<order["new_model_gate_released"]<order["real_new_model_pipeline"]<order["fresh_comparison"]<publications[1]["seq"]<order["query_after"]<order["late_old_gate_released"]<order["late_old_finished"]<publications[2]["seq"]<order["final_state"]
    assert one("late_old_gate_released")["after_selected_rev"]==3
    assert one("late_old_finished")["rc"]==0
    final=one("final_state")
    assert final["host_rev"]==final["selected_rev"]==3
    assert final["old_generation_id"]==old_generation and final["new_generation_id"]==final["selected_generation_id"]==new_generation
    assert final["selected_model_files_sha256"]==new_model
    print(f"evidence check passed: {len(events)} I137 events, {len(full)} I138 events, {len(calls)} mutation commands")
if __name__=="__main__":main()
