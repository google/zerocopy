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
fn sharded_cyclic_crate_verifies_cross_shard_dag_id_tree_and_incremental_cache() {
    let tools = workspace_tools();
    let cli = tools.cli.as_deref().expect("workspace cli binary");
    let capture = tools.capture.as_deref().expect("workspace capture binary");

    let mut rust_src = String::from(
        "pub unsafe fn cycle_a(ok: bool) -> ! {\n\
             if ok { loop {} } else { unsafe { cycle_b(ok) } }\n\
         }\n\
         pub unsafe fn cycle_b(ok: bool) -> ! {\n\
             if ok { loop {} } else { unsafe { cycle_a(ok) } }\n\
         }\n\
         pub unsafe fn top_caller(ok: bool) -> u64 {\n\
             if ok { 1 } else { unsafe { cycle_a(false) } }\n\
         }\n",
    );
    for idx in 0..21usize {
        let _ = writeln!(rust_src, "pub fn leaf_{idx:02}() -> u64 {{ 0 }}");
    }

    let staged = new_workspace("anneal-sharded-cyclic-").stage().unwrap();
    let work = staged.work_dir();
    let crate_dir = work.join("crate");
    let proof_dir = work.join("proof");
    // The per-user cache lives outside the working directory (`work`), since
    // step 5 also names it as an explicit cache root, which must not overlap
    // the checkout.
    let cache_dir = staged.root_dir().join("olean-cache");
    let plan_path = work.join("anneal-shards.json");
    let manifest_path = crate_dir.join("Cargo.toml");

    fs::create_dir_all(crate_dir.join("src")).unwrap();
    fs::write(
        &manifest_path,
        "[package]\nname = \"sharded_cyclic\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(crate_dir.join("src/lib.rs"), &rust_src).unwrap();

    // 1. Generate static-DAG `anneal-shards.json` plan with max_bodies=2.
    let plan_inv = with_host_cargo_env(
        &staged,
        Invocation::new(
            cli,
            &["shard-plan", "--shard-min-bodies", "2", "--shard-max-bodies", "2", "--write"],
        )
        .arg(&plan_path)
        .arg("--manifest-path")
        .arg(&manifest_path)
        .arg("--capture")
        .arg(capture)
        .arg("--sysroot")
        .arg(&tools.sysroot),
    );
    let plan_run = staged.exec(&plan_inv).unwrap();
    assert_outcome_exit(&plan_run.process, 0).unwrap();
    let plan: Value = serde_json::from_slice(&fs::read(&plan_path).unwrap()).unwrap();
    assert_eq!(plan["sharded"], json!(true), "{plan}");
    assert_eq!(plan["total_bodies"], json!(24), "{plan}");
    let shards = plan["shards"].as_array().unwrap();
    assert!(shards.len() >= 10, "expected >=10 shards for max_bodies=2: {plan}");

    let cycle_shard = shards
        .iter()
        .find(|s| {
            s["identities"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v.as_str().unwrap().ends_with("::cycle_a"))
        })
        .expect("cycle_a shard must exist");
    let cycle_idx = cycle_shard["shard_idx"].as_u64().unwrap() as usize;
    assert_eq!(cycle_shard["has_cycle"], json!(true), "{cycle_shard}");
    assert_eq!(cycle_shard["num_bodies"], json!(2), "{cycle_shard}");
    assert!(
        cycle_shard["identities"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v.as_str().unwrap().ends_with("::cycle_b")),
        "cycle_a and cycle_b must share one cyclic SCC shard: {cycle_shard}"
    );

    let caller_shard = shards
        .iter()
        .find(|s| {
            s["identities"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v.as_str().unwrap().ends_with("::top_caller"))
        })
        .expect("top_caller shard must exist");
    let caller_idx = caller_shard["shard_idx"].as_u64().unwrap() as usize;
    assert!(
        caller_idx > cycle_idx,
        "top_caller shard {caller_idx} must follow cycle shard {cycle_idx}: {plan}"
    );
    assert!(
        caller_shard["callee_shards"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v.as_u64() == Some(cycle_idx as u64)),
        "top_caller shard must list cycle shard {cycle_idx} in callee_shards: {caller_shard}"
    );

    // 2. Author `Spec.lean`, `Proof/Shard_*.lean`, and root `Proof.lean`.
    fs::create_dir_all(proof_dir.join("Proof")).unwrap();
    fs::write(
        proof_dir.join("Spec.lean"),
        lean_module_source(
            "public import Trusted.MirSemantics",
            concat!(
                "@[expose] public section\n\n",
                "namespace Spec\n",
                "open Trusted.MirAst Trusted.MirSemantics\n\n",
                "def cycleAId : String := \"rust-path-v1::cycle_a\"\n",
                "def cycleBId : String := \"rust-path-v1::cycle_b\"\n",
                "def topId : String := \"rust-path-v1::top_caller\"\n\n",
                "def safetyPre (id : String) (args : List Val) : Prop :=\n",
                "  (id = cycleAId ∨ id = cycleBId ∨ id = topId) ∧ args = [.bool true]\n\n",
                "def specs : Specs where\n",
                "  safety := safetyPre\n",
                "  property := fun p => p.bodies.length = 24\n",
                "end Spec\n\n",
                "end",
            ),
        ),
    )
    .unwrap();

    let mut leaf_00_shard = None;
    for shard in shards {
        let s_idx = shard["shard_idx"].as_u64().unwrap() as usize;
        if shard["identities"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v.as_str().unwrap().ends_with("::leaf_00"))
        {
            leaf_00_shard = Some(shard.clone());
        }
        fs::write(
            proof_dir.join(format!("Proof/Shard_{s_idx:03}.lean")),
            render_shard_proof(shard, cycle_idx, caller_idx, 0),
        )
        .unwrap();
    }
    let leaf_00_shard = leaf_00_shard.expect("leaf_00 shard must exist");
    let leaf_00_idx = leaf_00_shard["shard_idx"].as_u64().unwrap() as usize;

    let shard_refs: Vec<&Value> = shards.iter().collect();
    let root_node = build_balanced_root_node(&shard_refs);
    let mut root_imports =
        String::from("public import Expected\nimport Anneal.SccSharding\nimport Proof.IdTree");
    for s_idx in 0..shards.len() {
        let _ = write!(root_imports, "\nimport Proof.Shard_{s_idx:03}");
    }
    let root_body = format!(
        concat!(
            "namespace Proof\nopen Trusted.MirAst Trusted.MirSemantics Anneal.SccSharding\n",
            "private def rootTree : BinChunkTree Body := {tree}\n",
            "private theorem bodies_eq : Captured.program.bodies = BinChunkTree.toList rootTree :=\n",
            "  {beq}\n",
            "private theorem root_size : BinChunkTree.size rootTree = 24 :=\n",
            "  {seq}\n",
            "private theorem tree_wf : BinChunkTree.wf rootTree = true :=\n",
            "  {wf}\n",
            "private theorem tree_uniq :\n",
            "    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree) rootTree 0 = true :=\n",
            "  {uniq}\n",
            "public theorem verify : Expected.claim := by\n",
            "  have hLen : Captured.program.bodies.length = 24 := by\n",
            "    rw [bodies_eq, BinChunkTree.toList_length, root_size]\n",
            "  have hEntry : Nat.blt Captured.program.entryDefId (BinChunkTree.size rootTree) = true := by\n",
            "    rw [root_size]; rfl\n",
            "  have hPos : Nat.blt 0 (BinChunkTree.size rootTree) = true := by\n",
            "    rw [root_size]; rfl\n",
            "  exact crateTheorem_of_shardedTree Proof.IdTree.idDecisionTree\n",
            "    rfl bodies_eq rfl rfl tree_wf hEntry hPos tree_uniq\n",
            "    {ver} hLen\n",
            "end Proof",
        ),
        tree = root_node.tree_expr,
        beq = root_node.bodies_eq,
        seq = root_node.size_eq,
        wf = root_node.wf_proof,
        uniq = root_node.uniq_proof,
        ver = root_node.ver_proof,
    );
    fs::write(proof_dir.join("Proof.lean"), lean_module_source(&root_imports, &root_body)).unwrap();

    // 3. First full sharded verification (`XDG_CACHE_HOME` cold) with retained
    //    artifacts, then verify the live sharded receipt and retained tree
    //    via `cargo anneal inspect --verify-artifacts --unknown-fields=deny`.
    let artifacts_dir = work.join("retained-artifacts");
    let first_verify = with_host_cargo_env(
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
            OsStr::new("--verify-shard-plan"),
            plan_path.as_os_str(),
            OsStr::new("--artifacts"),
            artifacts_dir.as_os_str(),
        ]),
    )
    .env("XDG_CACHE_HOME", &cache_dir);
    let verify_run = run_verify_inv(&staged, &first_verify);
    let ok = expect_verified(&verify_run, "crate_verified", true);
    let shards_val = ok.shards.as_ref().expect("shards metadata in receipt");
    assert_eq!(shards_val["total_bodies"], json!(24), "{shards_val}");
    assert_eq!(shards_val["is_lean_module"], json!(true), "{shards_val}");
    assert!(ok.capture_shards_sha256.is_some());

    let first_receipt_path = work.join("first_receipt.json");
    fs::write(&first_receipt_path, &verify_run.process.stdout).unwrap();
    for fmt in ["human", "ledger", "markdown", "json"] {
        let inspect_out = Command::new(cli)
            .args([
                "inspect",
                first_receipt_path.to_str().unwrap(),
                "--verify-artifacts",
                artifacts_dir.to_str().unwrap(),
                "--require-exact-artifacts",
                "--unknown-fields",
                "deny",
                "--format",
                fmt,
                "--color",
                "never",
            ])
            .output()
            .expect("run cargo anneal inspect on sharded receipt");
        assert!(
            inspect_out.status.success(),
            "sharded inspect ({fmt}) failed: code={:?}\nstdout={}\nstderr={}",
            inspect_out.status.code(),
            String::from_utf8_lossy(&inspect_out.stdout),
            String::from_utf8_lossy(&inspect_out.stderr)
        );
    }
    // Tampering retained `generated/Proof/IdTree.lean` or
    // `capture/capture_shards.json` must fail `inspect --verify-artifacts`.
    let id_tree_path = artifacts_dir.join("generated/Proof/IdTree.lean");
    let orig_id_tree = fs::read(&id_tree_path).unwrap();
    fs::write(&id_tree_path, b"-- tampered\n").unwrap();
    let bad_id_tree = Command::new(cli)
        .args([
            "inspect",
            first_receipt_path.to_str().unwrap(),
            "--verify-artifacts",
            artifacts_dir.to_str().unwrap(),
            "--unknown-fields",
            "deny",
        ])
        .output()
        .expect("run inspect with tampered Proof.IdTree");
    assert_eq!(bad_id_tree.status.code(), Some(1));
    fs::write(&id_tree_path, &orig_id_tree).unwrap();

    let shards_json_path = artifacts_dir.join("capture/capture_shards.json");
    let orig_shards_json = fs::read(&shards_json_path).unwrap();
    fs::write(&shards_json_path, b"{\"tampered\":true}").unwrap();
    let bad_shards_json = Command::new(cli)
        .args([
            "inspect",
            first_receipt_path.to_str().unwrap(),
            "--verify-artifacts",
            artifacts_dir.to_str().unwrap(),
            "--unknown-fields",
            "deny",
        ])
        .output()
        .expect("run inspect with tampered capture_shards.json");
    assert_eq!(bad_shards_json.status.code(), Some(1));
    fs::write(&shards_json_path, &orig_shards_json).unwrap();

    let mut cache_before = BTreeMap::new();
    collect_oleans(&cache_dir, &mut cache_before);
    assert!(!cache_before.is_empty(), "expected target shards in OleanCache");

    // 4. Reject authored `Proof.IdTree` shadow when sharding is active.
    let authored_id_tree = proof_dir.join("Proof/IdTree.lean");
    fs::write(&authored_id_tree, "-- shadow\n").unwrap();
    let shadow_inv = with_host_cargo_env(
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
        ]),
    )
    .env("XDG_CACHE_HOME", &cache_dir);
    let shadow_run = run_verify_inv(&staged, &shadow_inv);
    expect_failed(&shadow_run, 1, "unsupported", Some("proof"), "reserved proof module");
    fs::remove_file(&authored_id_tree).unwrap();

    // 5. Edit 1 body (`leaf_00` returns 42) and check OleanCache reuse. This
    //    run points `XDG_CACHE_HOME` at an empty directory and
    //    `ANNEAL_OLEAN_CACHE_DIR` at another one, then names the populated
    //    per-user cache with `--olean-cache-dir`, so it only reuses entries
    //    if the flag is wired through and overrides the environment variable.
    std::thread::sleep(std::time::Duration::from_millis(50));
    let edited_rust = rust_src.replacen(
        "pub fn leaf_00() -> u64 { 0 }",
        "pub fn leaf_00() -> u64 { 42 }",
        1,
    );
    fs::write(crate_dir.join("src/lib.rs"), &edited_rust).unwrap();
    fs::write(
        proof_dir.join(format!("Proof/Shard_{leaf_00_idx:03}.lean")),
        render_shard_proof(&leaf_00_shard, cycle_idx, caller_idx, 42),
    )
    .unwrap();
    let decoy_xdg = work.join("decoy-xdg");
    let decoy_env_cache = work.join("decoy-env-olean-cache");
    fs::create_dir_all(&decoy_xdg).unwrap();
    fs::create_dir_all(&decoy_env_cache).unwrap();
    let populated_cache = cache_dir.join("anneal/olean-cache");
    assert!(populated_cache.join("v2").is_dir(), "{}", populated_cache.display());
    let flag_inv = with_host_cargo_env(
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
            OsStr::new("--verify-shard-plan"),
            plan_path.as_os_str(),
            OsStr::new("--olean-cache-dir"),
            populated_cache.as_os_str(),
        ]),
    )
    .env("XDG_CACHE_HOME", &decoy_xdg)
    .env("ANNEAL_OLEAN_CACHE_DIR", &decoy_env_cache);
    let inc_run = run_verify_inv(&staged, &flag_inv);
    expect_verified(&inc_run, "crate_verified", true);
    let mut decoy_entries = BTreeMap::new();
    collect_oleans(&decoy_xdg, &mut decoy_entries);
    collect_oleans(&decoy_env_cache, &mut decoy_entries);
    assert!(decoy_entries.is_empty(), "decoy caches must stay unused: {decoy_entries:?}");

    let inc_receipt_path = work.join("inc_receipt.json");
    fs::write(&inc_receipt_path, &inc_run.process.stdout).unwrap();
    let diff_out = Command::new(cli)
        .args([
            "inspect",
            "--diff",
            first_receipt_path.to_str().unwrap(),
            inc_receipt_path.to_str().unwrap(),
            "--unknown-fields",
            "deny",
            "--format",
            "json",
        ])
        .output()
        .expect("run cargo anneal inspect --diff on sharded receipts");
    assert!(
        diff_out.status.success(),
        "sharded inspect --diff failed: code={:?}\nstdout={}\nstderr={}",
        diff_out.status.code(),
        String::from_utf8_lossy(&diff_out.stdout),
        String::from_utf8_lossy(&diff_out.stderr)
    );
    let diff_json: Value = serde_json::from_slice(&diff_out.stdout).unwrap();
    assert!(
        diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "capture_shards_sha256" && c["tier"] == "tier_b"),
        "{diff_json}"
    );

    let mut cache_after = BTreeMap::new();
    collect_oleans(&cache_dir, &mut cache_after);
    // Untouched shards keep their exact cached `.olean` entries untouched, and
    // editing `leaf_00` creates strictly the 2 replacement entries
    // (`Captured.Shard_<leaf>` + `Proof.Shard_<leaf>`).
    assert_eq!(
        cache_after.len(),
        cache_before.len() + 2,
        "expected exactly 2 new OleanCache entries on 1-body edit (before={}, after={})",
        cache_before.len(),
        cache_after.len()
    );
    let untouched = cache_before
        .iter()
        .filter(|(p, t)| cache_after.get(*p) == Some(*t))
        .count();
    assert_eq!(
        untouched,
        cache_before.len(),
        "expected all existing OleanCache entries preserved untouched"
    );

    // 6. `ANNEAL_OLEAN_CACHE_DIR` alone (no flag) also selects the shared
    //    cache: with `XDG_CACHE_HOME` pointing at yet another empty directory,
    //    the unchanged rerun verifies without writing anything there.
    let env_decoy_xdg = work.join("env-decoy-xdg");
    fs::create_dir_all(&env_decoy_xdg).unwrap();
    let env_inv = with_host_cargo_env(
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
            OsStr::new("--verify-shard-plan"),
            plan_path.as_os_str(),
        ]),
    )
    .env("XDG_CACHE_HOME", &env_decoy_xdg)
    .env("ANNEAL_OLEAN_CACHE_DIR", &populated_cache);
    let env_run = run_verify_inv(&staged, &env_inv);
    expect_verified(&env_run, "crate_verified", true);
    let mut env_decoy_entries = BTreeMap::new();
    collect_oleans(&env_decoy_xdg, &mut env_decoy_entries);
    assert!(env_decoy_entries.is_empty(), "XDG cache must stay unused: {env_decoy_entries:?}");
    let mut cache_final = BTreeMap::new();
    collect_oleans(&cache_dir, &mut cache_final);
    assert_eq!(cache_final, cache_after, "the unchanged rerun must only hit the shared cache");

    // 7. An explicit `--prebuilt-dir` must match the run. A bundle whose
    //    `TrustedBoundary` inspector entry was built from other inputs fails
    //    verification instead of recompiling the inspector, while a bundle
    //    that lists nothing defers to the shared cache, which stays unchanged.
    let bundle = staged.root_dir().join("prebuilt");
    fs::create_dir_all(&bundle).unwrap();
    let zeros = "0".repeat(64);
    let stale_manifest = json!({
        "schema_version": 2,
        "entries": [{
            "kind": "inspector",
            "module": "TrustedBoundary",
            "lean_sha256": zeros,
            "sysroot_manifest_sha256": zeros,
            "source_sha256": zeros,
            "is_module": false,
            "flags": [],
            "imports": [],
            "parts": [{ "suffix": "olean", "path": "TrustedBoundary.olean", "sha256": zeros }]
        }]
    });
    let prebuilt_inv = || {
        with_host_cargo_env(
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
                OsStr::new("--verify-shard-plan"),
                plan_path.as_os_str(),
                OsStr::new("--olean-cache-dir"),
                populated_cache.as_os_str(),
                OsStr::new("--prebuilt-dir"),
                bundle.as_os_str(),
            ]),
        )
    };
    fs::write(bundle.join("manifest.json"), serde_json::to_vec(&stale_manifest).unwrap()).unwrap();
    let stale_run = run_verify_inv(&staged, &prebuilt_inv());
    expect_failed(&stale_run, 2, "tool_failed", Some("audit"), "built from different inputs");
    fs::write(bundle.join("manifest.json"), br#"{"schema_version":2,"entries":[]}"#).unwrap();
    let empty_bundle_run = run_verify_inv(&staged, &prebuilt_inv());
    expect_verified(&empty_bundle_run, "crate_verified", true);
    // On runners whose Lean toolchain ships `share/anneal/prebuilt`, steps 1-6
    // read bundled modules from that toolchain bundle rather than populating
    // `cache_dir`; `empty_bundle_run` above replaces it and warms `cache_dir`,
    // so a repeat run with the empty bundle must leave `cache_dir` untouched.
    let mut cache_after_empty = BTreeMap::new();
    collect_oleans(&cache_dir, &mut cache_after_empty);
    assert!(!cache_after_empty.is_empty(), "empty bundle run must populate the shared cache");
    let empty_bundle_rerun = run_verify_inv(&staged, &prebuilt_inv());
    expect_verified(&empty_bundle_rerun, "crate_verified", true);
    let mut cache_prebuilt = BTreeMap::new();
    collect_oleans(&cache_dir, &mut cache_prebuilt);
    assert_eq!(
        cache_prebuilt, cache_after_empty,
        "an empty bundle must defer to the shared cache on repeat runs"
    );

    // Build a real populated `--prebuilt-dir` bundle containing the bundled
    // `Trusted.*`, `Anneal.*`, and inspector entries from `populated_cache`
    // (excluding crate-local `Captured`/`Proof` shards that have pre-edit and
    // post-edit versions), and verify against a fresh empty `--olean-cache-dir`
    // that none of the bundle's modules are recompiled or written to disk.
    let populated_bundle = staged.root_dir().join("prebuilt-populated");
    fs::create_dir_all(&populated_bundle).unwrap();
    let mut bundle_entries = Vec::new();
    let mut bundled_keys = std::collections::BTreeSet::new();
    let v2_root = populated_cache.join("v2");
    let mut entry_dirs: Vec<PathBuf> = fs::read_dir(&v2_root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("metadata.json").is_file())
        .collect();
    entry_dirs.sort();
    for entry_dir in entry_dirs {
        let key_name = entry_dir.file_name().unwrap().to_string_lossy().into_owned();
        let meta: serde_json::Value =
            serde_json::from_slice(&fs::read(entry_dir.join("metadata.json")).unwrap()).unwrap();
        let kind = meta["input"]["kind"].as_str().unwrap();
        let module = meta["input"]["module"].as_str().unwrap();
        let is_bundled = kind == "inspector"
            || module == "Trusted"
            || module.starts_with("Trusted.")
            || module == "Anneal"
            || module.starts_with("Anneal.");
        if !is_bundled {
            continue;
        }
        bundled_keys.insert(key_name.clone());
        let mut entry_obj = meta["input"].as_object().unwrap().clone();
        let mut new_parts = Vec::new();
        for part in meta["parts"].as_array().unwrap() {
            let rel_src = part["path"].as_str().unwrap();
            let rel_dst = format!("{key_name}/{rel_src}");
            let dst = populated_bundle.join(&rel_dst);
            fs::create_dir_all(dst.parent().unwrap()).unwrap();
            fs::copy(entry_dir.join(rel_src), &dst).unwrap();
            new_parts.push(json!({
                "suffix": part["suffix"],
                "path": rel_dst,
                "sha256": part["sha256"],
            }));
        }
        entry_obj.insert("parts".to_owned(), serde_json::Value::Array(new_parts));
        bundle_entries.push(serde_json::Value::Object(entry_obj));
    }
    assert!(
        bundle_entries.iter().any(|e| e["kind"] == "inspector"),
        "expected inspector entry in populated bundle: {bundle_entries:?}"
    );
    fs::write(
        populated_bundle.join("manifest.json"),
        serde_json::to_vec(&json!({
            "schema_version": 2,
            "entries": bundle_entries,
        }))
        .unwrap(),
    )
    .unwrap();
    let fresh_cache = staged.root_dir().join("fresh-olean-cache");
    let populated_inv = with_host_cargo_env(
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
            OsStr::new("--verify-shard-plan"),
            plan_path.as_os_str(),
            OsStr::new("--olean-cache-dir"),
            fresh_cache.as_os_str(),
            OsStr::new("--prebuilt-dir"),
            populated_bundle.as_os_str(),
        ]),
    );
    let populated_run = run_verify_inv(&staged, &populated_inv);
    expect_verified(&populated_run, "crate_verified", true);
    let fresh_v2 = fresh_cache.join("v2");
    for key in &bundled_keys {
        assert!(
            !fresh_v2.join(key).exists(),
            "bundled entry {key} must hit --prebuilt-dir rather than compiling into fresh disk cache"
        );
    }
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
