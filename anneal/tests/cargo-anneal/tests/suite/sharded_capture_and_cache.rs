// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Cyclic Tarjan SCC sharding, cross-shard DAG imports, `Proof.IdTree`, and
//! incremental `OleanCache` end-to-end verification.

use std::{
    collections::BTreeMap,
    ffi::OsStr,
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use anneal_testkit::{Invocation, assertions::assert_outcome_exit};
use serde_json::{Value, json};

use crate::helpers::{
    expect_failed, expect_verified, lean_module_source, new_workspace, run_verify_inv,
    verify_invocation, with_host_cargo_env, workspace_tools,
};

mod cross_shard_dag;

struct NodeProof {
    tree_expr: String,
    bodies_eq: String,
    size_val: usize,
    size_eq: String,
    wf_proof: String,
    uniq_proof: String,
    ver_proof: String,
}

fn build_balanced_root_node(slice: &[&Value]) -> NodeProof {
    if slice.len() == 1 {
        let s_idx = slice[0]["shard_idx"].as_u64().unwrap() as usize;
        let count = slice[0]["num_bodies"].as_u64().unwrap() as usize;
        return NodeProof {
            tree_expr: format!("Proof.Shard_{s_idx:03}.shardTree"),
            bodies_eq: format!("Proof.Shard_{s_idx:03}.shardBodies_eq"),
            size_val: count,
            size_eq: format!("Proof.Shard_{s_idx:03}.shardSize"),
            wf_proof: format!("Proof.Shard_{s_idx:03}.shardWf"),
            uniq_proof: format!("Proof.Shard_{s_idx:03}.shardUniq"),
            ver_proof: format!("Proof.Shard_{s_idx:03}.shardVerified"),
        };
    }
    let mid = slice.len() / 2;
    let l = build_balanced_root_node(&slice[..mid]);
    let r = build_balanced_root_node(&slice[mid..]);
    let half = l.size_val;
    NodeProof {
        tree_expr: format!("(.branch {half} {} {})", l.tree_expr, r.tree_expr),
        bodies_eq: format!(
            "(BinChunkTree.toList_branch {half} {} {} {} {})",
            l.tree_expr, r.tree_expr, l.bodies_eq, r.bodies_eq
        ),
        size_val: l.size_val + r.size_val,
        size_eq: format!(
            "(BinChunkTree.size_branch {half} {} {} {} {} rfl)",
            l.tree_expr, r.tree_expr, l.size_eq, r.size_eq
        ),
        wf_proof: format!(
            "(BinChunkTree.wf_branch (by rw [{}]) {} {})",
            l.size_eq, l.wf_proof, r.wf_proof
        ),
        uniq_proof: format!(
            "(BinChunkTree.allIdx_branch rfl {} {})",
            l.uniq_proof, r.uniq_proof
        ),
        ver_proof: format!("(And.intro {} {})", l.ver_proof, r.ver_proof),
    }
}

fn collect_oleans(dir: &Path, out: &mut BTreeMap<PathBuf, std::time::SystemTime>) {
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() {
                collect_oleans(&p, out);
            } else if p.extension().is_some_and(|e| e == "olean") {
                out.insert(p, entry.metadata().unwrap().modified().unwrap());
            }
        }
    }
}

fn render_shard_proof(shard: &Value, cycle_idx: usize, caller_idx: usize, leaf_00_ret: u64) -> String {
    let s_idx = shard["shard_idx"].as_u64().unwrap() as usize;
    let ids = shard["identities"].as_array().unwrap();
    let offset = shard["global_def_id_range"][0].as_u64().unwrap();
    let mut imports = format!(
        "public import Anneal.MirWp\npublic import Anneal.SccSharding\n\
         public import Captured.Shard_{s_idx:03}\npublic import Proof.IdTree\npublic import Spec"
    );
    if s_idx == caller_idx {
        let _ = write!(imports, "\npublic import Proof.Shard_{cycle_idx:03}");
    }
    let mut body = format!(
        "@[expose] public section\n\nnamespace Proof.Shard_{s_idx:03}\n\
         open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.SccSharding\n\
         open Captured.Shard_{s_idx:03}\n\n"
    );
    let tree_expr = if ids.len() == 1 {
        ".leaf body_0"
    } else {
        ".branch 1 (.leaf body_0) (.leaf body_1)"
    };
    let uniq_proof = if ids.len() == 1 {
        "BinChunkTree.allIdx_leaf rfl"
    } else {
        "BinChunkTree.allIdx_branch rfl \
         (BinChunkTree.allIdx_leaf rfl) \
         (BinChunkTree.allIdx_leaf rfl)"
    };
    let _ = writeln!(
        body,
        concat!(
            "def shardTree : BinChunkTree Body := {tree}\n",
            "theorem shardBodies_eq : shard_bodies = BinChunkTree.toList shardTree := rfl\n",
            "theorem shardSize : BinChunkTree.size shardTree = {count} := rfl\n",
            "theorem shardWf : BinChunkTree.wf shardTree = true := rfl\n",
            "theorem shardUniq : BinChunkTree.allIdx\n",
            "    (checkBodyIdentityAt Proof.IdTree.idDecisionTree) shardTree {offset} = true :=\n",
            "  {uniq}",
        ),
        tree = tree_expr,
        count = ids.len(),
        offset = offset,
        uniq = uniq_proof,
    );
    if ids.iter().any(|v| {
        let s = v.as_str().unwrap();
        s.ends_with("::cycle_a") || s.ends_with("::cycle_b")
    }) {
        body.push_str(concat!(
            "private theorem safeFrom_cycle2 {body : Body} {s0 s1 : State}\n",
            "    (h0 : evalStep (bodyProg body) 0 s0 = .step s1)\n",
            "    (h1 : evalStep (bodyProg body) 0 s1 = .step s0) :\n",
            "    SafeFrom body s0 := by\n",
            "  refine safeFrom_invariant (fun st => st = s0 ∨ st = s1) (Or.inl rfl) ?_ ?_\n",
            "  · intro before after hb ht\n",
            "    cases hb with\n",
            "    | inl e =>\n",
            "      subst e; rw [h0] at ht; injection ht with ha; exact Or.inr ha.symm\n",
            "    | inr e =>\n",
            "      subst e; rw [h1] at ht; injection ht with ha; exact Or.inl ha.symm\n",
            "  · intro st hst reason hf\n",
            "    cases hst with\n",
            "    | inl e => subst e; rw [h0] at hf; cases hf\n",
            "    | inr e => subst e; rw [h1] at hf; cases hf\n",
            "private def reachesCycle2 (body : Body) : Nat → State → Prop\n",
            "  | 0, s =>\n",
            "    match evalStep (bodyProg body) 0 s with\n",
            "    | .step s1 => evalStep (bodyProg body) 0 s1 = .step s\n",
            "    | _ => False\n",
            "  | n + 1, s =>\n",
            "    match evalStep (bodyProg body) 0 s with\n",
            "    | .step s' => reachesCycle2 body n s'\n",
            "    | _ => False\n",
            "private theorem safeFrom_reachesCycle2 (body : Body) :\n",
            "    ∀ (n : Nat) (s : State), reachesCycle2 body n s → SafeFrom body s\n",
            "  | 0, s, h => by\n",
            "    rw [reachesCycle2.eq_1] at h\n",
            "    cases h0 : evalStep (bodyProg body) 0 s with\n",
            "    | fault _ => rw [h0] at h; exact False.elim h\n",
            "    | done _ => rw [h0] at h; exact False.elim h\n",
            "    | step s1 => rw [h0] at h; exact safeFrom_cycle2 h0 h\n",
            "  | n + 1, s, h => by\n",
            "    rw [reachesCycle2.eq_2] at h\n",
            "    cases hStep : evalStep (bodyProg body) 0 s with\n",
            "    | fault _ => rw [hStep] at h; exact False.elim h\n",
            "    | done _ => rw [hStep] at h; exact False.elim h\n",
            "    | step s' =>\n",
            "      rw [hStep] at h\n",
            "      exact safeFrom_next hStep (safeFrom_reachesCycle2 body n s' h)\n",
        ));
    }
    let mut loc_names = Vec::new();
    for (local_i, id_val) in ids.iter().enumerate() {
        let ident = id_val.as_str().unwrap();
        let loc = format!("loc_{local_i}");
        if ident.ends_with("::cycle_a") || ident.ends_with("::cycle_b") {
            let _ = writeln!(
                body,
                concat!(
                    "private theorem {loc} : LocalBodyVerified body_{i}\n",
                    "    (Spec.specs.safety body_{i}.identity) := by\n",
                    "  refine localBodyVerified_intro rfl (fun args hValid hReq => ?_)\n",
                    "  have hEq : args = [.bool true] := (hReq rfl).2\n",
                    "  subst hEq\n",
                    "  exact safeFrom_reachesCycle2 body_{i} 4\n",
                    "    (mkState 0 0 (initLocalsLoop body_{i} [.bool true] 0 body_{i}.locals)) rfl",
                ),
                loc = loc,
                i = local_i,
            );
        } else if ident.ends_with("::top_caller") {
            let _ = writeln!(
                body,
                concat!(
                    "private theorem {loc} : LocalBodyVerified body_{i}\n",
                    "    (Spec.specs.safety body_{i}.identity) := by\n",
                    "  have _callee_shard_dep : BinChunkTree.size Proof.Shard_{cyc:03}.shardTree = 2 :=\n",
                    "    Proof.Shard_{cyc:03}.shardSize\n",
                    "  refine localBodyVerified_intro rfl (fun args hValid hReq => ?_)\n",
                    "  have hEq : args = [.bool true] := (hReq rfl).2\n",
                    "  subst hEq\n",
                    "  have hRuns : Runs body_{i} 16 [.bool true]\n",
                    "      (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩) := rfl\n",
                    "  exact (run_initial_success hRuns).1",
                ),
                loc = loc,
                i = local_i,
                cyc = cycle_idx,
            );
        } else {
            let ret_n = if ident.ends_with("::leaf_00") { leaf_00_ret } else { 0 };
            let _ = writeln!(
                body,
                concat!(
                    "private theorem {loc} : LocalBodyVerified body_{i}\n",
                    "    (Spec.specs.safety body_{i}.identity) := by\n",
                    "  have hRuns : Runs body_{i} 2 []\n",
                    "      (.scalar ⟨.i64, false, BitVec.ofNat 128 {ret}⟩) := rfl\n",
                    "  exact localBodyVerified_of_runs0 rfl rfl hRuns",
                ),
                loc = loc,
                i = local_i,
                ret = ret_n,
            );
        }
        loc_names.push(loc);
    }
    let ver_term = if loc_names.len() == 1 {
        loc_names[0].clone()
    } else {
        format!("⟨{}, {}⟩", loc_names[0], loc_names[1])
    };
    let _ = writeln!(
        body,
        "\ntheorem shardVerified : TreeLocalVerified Spec.specs shardTree := {ver_term}\n\
         end Proof.Shard_{s_idx:03}\n\nend"
    );
    lean_module_source(&imports, &body)
}

#[test]
fn sharding_is_transparent_to_unsharded_module_mode_proofs() {
    let tools = workspace_tools();
    let cli = tools.cli.as_deref().expect("workspace cli binary");
    let _capture = tools.capture.as_deref().expect("workspace capture binary");

    let staged = new_workspace("anneal-sharded-transparent-mod-").stage().unwrap();
    let work = staged.work_dir();
    let crate_dir = work.join("crate");
    let proof_dir = work.join("proof");
    let manifest_path = crate_dir.join("Cargo.toml");

    fs::create_dir_all(crate_dir.join("src")).unwrap();
    fs::create_dir_all(&proof_dir).unwrap();
    fs::write(
        &manifest_path,
        "[package]\nname = \"sharded_transparent\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(
        crate_dir.join("src/lib.rs"),
        "pub fn f0() -> u64 { 0 }\npub fn f1() -> u64 { 1 }\npub fn f2() -> u64 { 2 }\n",
    )
    .unwrap();

    // Standard `module`-mode `Spec.lean` + `Proof.lean` without
    // `Proof/Shard_*.lean` (same layout as `cargo anneal init` and `01..04`
    // proofs) must verify cleanly when sharding activates
    // (`3 > --shard-min-bodies 2`).
    fs::write(
        proof_dir.join("Spec.lean"),
        lean_module_source(
            "public import Trusted.MirSemantics",
            concat!(
                "@[expose] public section\n\n",
                "namespace Spec\n",
                "open Trusted.MirAst Trusted.MirSemantics\n",
                "def specs : Specs where\n",
                "  safety := fun _ _ => True\n",
                "  property := fun p => p.bodies.length = 3\n",
                "end Spec\n\n",
                "end",
            ),
        ),
    )
    .unwrap();
    fs::write(
        proof_dir.join("Proof.lean"),
        lean_module_source(
            "public import Expected\nimport Anneal.MirWp",
            concat!(
                "namespace Proof\n",
                "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp\n",
                "private theorem wf_at (k : Nat)\n",
                "    (h : execProg (entryProgForBody Captured.program k) 2 { args := [] }\n",
                "      (fun _ => True)) :\n",
                "    WellFormed (entryProgForBody Captured.program k) { args := [] } :=\n",
                "  (wellFormed_and_spec_of_wp _ _ 2 _ (wpProg_of_execProg h)).1.1\n",
                "public theorem verify : Expected.claim := by\n",
                "  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩\n",
                "  intro id body found\n",
                "  match id with\n",
                "  | 0 =>\n",
                "    have same : Captured.program.bodies[0] = body := Option.some.inj found\n",
                "    subst body; refine ⟨found, rfl, fun args valid _ => ?_⟩\n",
                "    cases args with | nil => exact wf_at 0 trivial | cons _ _ => cases valid\n",
                "  | 1 =>\n",
                "    have same : Captured.program.bodies[1] = body := Option.some.inj found\n",
                "    subst body; refine ⟨found, rfl, fun args valid _ => ?_⟩\n",
                "    cases args with | nil => exact wf_at 1 trivial | cons _ _ => cases valid\n",
                "  | 2 =>\n",
                "    have same : Captured.program.bodies[2] = body := Option.some.inj found\n",
                "    subst body; refine ⟨found, rfl, fun args valid _ => ?_⟩\n",
                "    cases args with | nil => exact wf_at 2 trivial | cons _ _ => cases valid\n",
                "  | _ + 3 => cases found\n",
                "end Proof",
            ),
        ),
    )
    .unwrap();

    let artifacts_dir = work.join("transparent-artifacts");
    let inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest_path.as_os_str(),
            OsStr::new("--proof-dir"),
            proof_dir.as_os_str(),
            OsStr::new("--shard-min-bodies"),
            OsStr::new("2"),
            OsStr::new("--shard-max-bodies"),
            OsStr::new("2"),
            OsStr::new("--artifacts"),
            artifacts_dir.as_os_str(),
        ]),
    );
    let run = run_verify_inv(&staged, &inv);
    let ok = expect_verified(&run, "crate_verified", true);
    let shards_val = ok.shards.as_ref().expect("sharding must be active");
    assert_eq!(shards_val["total_bodies"], json!(3), "{shards_val}");
    assert_eq!(shards_val["total_shards"], json!(2), "{shards_val}");
    assert_eq!(shards_val["is_lean_module"], json!(true), "{shards_val}");

    let receipt_path = work.join("transparent_receipt.json");
    fs::write(&receipt_path, &run.process.stdout).unwrap();
    let inspect_out = Command::new(cli)
        .args([
            "inspect",
            receipt_path.to_str().unwrap(),
            "--verify-artifacts",
            artifacts_dir.to_str().unwrap(),
            "--require-exact-artifacts",
            "--unknown-fields",
            "deny",
        ])
        .output()
        .expect("run cargo anneal inspect on transparent sharded receipt");
    assert!(
        inspect_out.status.success(),
        "transparent sharded inspect failed: code={:?}\nstdout={}\nstderr={}",
        inspect_out.status.code(),
        String::from_utf8_lossy(&inspect_out.stdout),
        String::from_utf8_lossy(&inspect_out.stderr)
    );
}
