// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
};

use super::*;
use crate::ir::{Block, Body, IntTy, IntWidth, Scope, Statement, Terminator, Ty};

fn synth_body(identity: &str, nop_count: usize, callees: &[&str]) -> Body {
    let u8_ty = Ty::Int(IntTy {
        width: IntWidth::I8,
        signed: false,
    });
    Body::try_new_with_callees(
        0,
        false,
        vec![u8_ty],
        vec![Block {
            statements: vec![Statement::Nop; nop_count],
            terminator: Terminator::Ret,
        }],
        identity.to_owned(),
        callees.iter().map(|s| (*s).to_owned()).collect(),
    )
    .unwrap()
}

fn dummy_manifest(bodies: Vec<Body>) -> ir::Manifest {
    let selected = bodies
        .iter()
        .enumerate()
        .map(|(idx, b)| ir::SelectedBody {
            def_id: idx as u32,
            path: b.identity().trim_start_matches("rust-path-v1::").to_owned(),
            body_index: idx,
        })
        .collect();
    ir::Manifest {
        schema_version: ir::SCHEMA_VERSION,
        compiler: ir::Compiler {
            commit: ir::COMPILER_COMMIT,
            version: ir::COMPILER_VERSION,
            sysroot: "/sysroot".into(),
            rustc_sha256: "0".repeat(64),
            driver: ir::DriverIdentity {
                linkage: ir::DriverLinkage::StaticExe,
                driver_sha256: "0".repeat(64),
                dso_digests: BTreeMap::new(),
            },
        },
        configuration: ir::Configuration {
            crate_root: "/lib.rs".into(),
            crate_name: "demo".into(),
            crate_type: ir::CrateType::Lib,
            panic: ir::PanicStrategy::Unwind,
            edition: "2024".into(),
            target: "x86_64-unknown-linux-gnu".into(),
            cfg: Vec::new(),
            env: BTreeMap::new(),
            opt_level: 0,
            debug_assertions: false,
            overflow_checks: false,
            mir_preserve_ub: true,
            pointer_bits: 64,
            endian: "little",
            declared_source_files: Vec::new(),
            stdlib_crate: None,
            allowed_unstable_features: Vec::new(),
            observed_unstable_features: Vec::new(),
            incomplete_observed_unstable_features: Vec::new(),
            stabilized_features_present: Vec::new(),
        },
        source_files: Vec::new(),
        census: Vec::new(),
        selected,
        unsupported: Vec::new(),
        program: ir::Program::try_new(Scope::Crate, bodies).unwrap(),
    }
}

#[test]
fn tarjan_scc_is_permutation_invariant_and_preserves_cyclic_components() {
    // Leaf `z_leaf` called by 2-cycle `(m_even <-> m_odd)`, called by
    // 3-cycle `(a_ring0 -> a_ring1 -> a_ring2 -> a_ring0)`. Lexical order
    // puts `a_ring*` before `z_leaf`, so callee-first order MUST place
    // `z_leaf` < `{m_even, m_odd}` < `{a_ring0..2}` across SCCs 0..2.
    let forward = vec![
        synth_body("rust-path-v1::a_ring0", 1, &["rust-path-v1::a_ring1", "rust-path-v1::m_even"]),
        synth_body("rust-path-v1::a_ring1", 1, &["rust-path-v1::a_ring2"]),
        synth_body("rust-path-v1::a_ring2", 1, &["rust-path-v1::a_ring0"]),
        synth_body("rust-path-v1::m_even", 1, &["rust-path-v1::m_odd", "rust-path-v1::z_leaf"]),
        synth_body("rust-path-v1::m_odd", 1, &["rust-path-v1::m_even"]),
        synth_body("rust-path-v1::z_leaf", 1, &[]),
    ];
    let mut reversed = forward.clone();
    reversed.reverse();

    let cfg = ShardConfig {
        shard_min_bodies: 2,
        shard_max_bodies: 2,
        shard_max_ast_nodes: 2_500,
    };
    let mut m1 = dummy_manifest(forward);
    let mut m2 = dummy_manifest(reversed);
    let p1 = maybe_shard_manifest(&mut m1, cfg).unwrap().unwrap();
    let p2 = maybe_shard_manifest(&mut m2, cfg).unwrap().unwrap();

    assert_eq!(p1.manifest, p2.manifest);
    assert_eq!(p1.root_lean, p2.root_lean);
    assert_eq!(p1.shard_sources, p2.shard_sources);

    // Check 3-shard layout, cycle containment, and oversized 3-cycle flag.
    assert_eq!(p1.manifest.total_sccs, 3);
    assert_eq!(p1.manifest.cyclic_sccs, 2);
    assert_eq!(p1.manifest.total_shards, 3);

    assert_eq!(p1.manifest.shards[0].identities, vec!["rust-path-v1::z_leaf"]);
    assert!(!p1.manifest.shards[0].has_cycle);
    assert!(!p1.manifest.shards[0].oversized_scc);
    assert!(p1.manifest.shards[0].callee_shards.is_empty());

    assert_eq!(
        p1.manifest.shards[1].identities,
        vec!["rust-path-v1::m_even", "rust-path-v1::m_odd"]
    );
    assert!(p1.manifest.shards[1].has_cycle);
    assert!(!p1.manifest.shards[1].oversized_scc);
    assert_eq!(p1.manifest.shards[1].callee_shards, vec![0]);

    assert_eq!(
        p1.manifest.shards[2].identities,
        vec![
            "rust-path-v1::a_ring0",
            "rust-path-v1::a_ring1",
            "rust-path-v1::a_ring2"
        ]
    );
    assert!(p1.manifest.shards[2].has_cycle);
    assert!(p1.manifest.shards[2].oversized_scc);
    assert_eq!(p1.manifest.shards[2].callee_shards, vec![1]);

    // Check selected body_index remapping matches reordered program.bodies.
    for sel in &m1.selected {
        assert_eq!(
            m1.program.bodies()[sel.body_index].identity(),
            format!("rust-path-v1::{}", sel.path)
        );
    }
}

#[test]
fn small_crates_at_or_below_min_bodies_stay_unsharded() {
    let bodies: Vec<Body> = (0..20)
        .map(|i| synth_body(&format!("rust-path-v1::fn_{i:02}"), 1, &[]))
        .collect();
    let mut m = dummy_manifest(bodies);
    assert!(
        maybe_shard_manifest(&mut m, ShardConfig::default())
            .unwrap()
            .is_none()
    );
}

#[test]
fn shard_plan_verification_accepts_implementation_edits_and_rejects_topology_drift() {
    let tmp = tempfile::tempdir().unwrap();
    let plan_path = tmp.path().join("anneal-shards.json");

    let bodies_v1: Vec<Body> = (0..25)
        .map(|i| synth_body(&format!("rust-path-v1::fn_{i:02}"), 2, &[]))
        .collect();
    let mut m1 = dummy_manifest(bodies_v1);
    let cfg = ShardConfig::default();
    let s1 = maybe_shard_manifest(&mut m1, cfg).unwrap().unwrap();
    let plan1 = ShardPlan::from_sharded(&s1.manifest, cfg);
    fs::write(&plan_path, serde_json::to_vec_pretty(&plan1).unwrap()).unwrap();

    // Editing fn_05's implementation statements (2 -> 10 Nops) changes
    // capture_sha256 and ast_nodes, while keeping ShardPlan identical!
    let bodies_v2: Vec<Body> = (0..25)
        .map(|i| {
            synth_body(
                &format!("rust-path-v1::fn_{i:02}"),
                if i == 5 { 10 } else { 2 },
                &[],
            )
        })
        .collect();
    let mut m2 = dummy_manifest(bodies_v2);
    let s2 = maybe_shard_manifest(&mut m2, cfg).unwrap().unwrap();
    assert_ne!(
        s1.manifest.shards[0].capture_sha256,
        s2.manifest.shards[0].capture_sha256
    );
    let plan2 = ShardPlan::from_sharded(&s2.manifest, cfg);
    verify_shard_plan_file(&plan_path, &plan2).unwrap();

    // Adding a cross-shard edge (`fn_22` -> `fn_01`) alters `callee_shards`
    // and must fail closed with regeneration instructions.
    let bodies_v3: Vec<Body> = (0..25)
        .map(|i| {
            let callees: &[&str] = if i == 22 { &["rust-path-v1::fn_01"] } else { &[] };
            synth_body(&format!("rust-path-v1::fn_{i:02}"), 2, callees)
        })
        .collect();
    let mut m3 = dummy_manifest(bodies_v3);
    let s3 = maybe_shard_manifest(&mut m3, cfg).unwrap().unwrap();
    let plan3 = ShardPlan::from_sharded(&s3.manifest, cfg);
    let err = verify_shard_plan_file(&plan_path, &plan3).unwrap_err();
    assert!(err.contains("drifted"), "{err}");
    assert!(err.contains("cargo anneal shard-plan --write"), "{err}");
}

#[test]
fn decision_tree_stays_logarithmic_and_long_identity_counts_towards_ast_budget() {
    // Equal-length names each differing at one unique byte position: every
    // single-byte cut is `1:(N-1)` without fallback splits.
    let single_pos: Vec<String> = (0..64)
        .map(|i| {
            let mut s = vec![b'a'; 64];
            s[i] = b'b';
            String::from_utf8(s).unwrap()
        })
        .collect();
    let tree = ByteDecisionTree::build(&single_pos).unwrap();
    assert!(tree.depth() <= 16, "unexpected depth {} for 64 single-diff strings", tree.depth());

    // Equal-checksum collisions forcing `SplitLex` midpoint fallback.
    let mut tag_collide = Vec::with_capacity(24);
    for d in 0..24u8 {
        let b0 = 65 + 2 * d;
        let b1 = 90 - d;
        let s = format!("{}{}", b0 as char, b1 as char);
        assert_eq!(byte_list_tag(s.as_bytes()), Some(245));
        tag_collide.push(s);
    }
    let lex_tree = ByteDecisionTree::build(&tag_collide).unwrap();
    assert!(lex_tree.depth() <= 12, "unexpected depth {}", lex_tree.depth());

    // Long `Body.identity` strings must contribute rendered character +
    // chunk assembly AST nodes to `--shard-max-ast-nodes` and trigger
    // `oversized_scc` isolation.
    let long_id = format!("rust-path-v1::{}", "seg_".repeat(100));
    let tiny_body_long_id = synth_body(&long_id, 1, &[]);
    assert!(
        tiny_body_long_id.ast_nodes() > 800,
        "expected identity AST nodes > 800, got {}",
        tiny_body_long_id.ast_nodes()
    );
    let mut bodies = vec![tiny_body_long_id];
    for i in 0..4 {
        bodies.push(synth_body(&format!("rust-path-v1::small_{i}"), 1, &[]));
    }
    let mut m = dummy_manifest(bodies);
    let cfg = ShardConfig {
        shard_min_bodies: 2,
        shard_max_bodies: 20,
        shard_max_ast_nodes: 500,
    };
    let sharded = maybe_shard_manifest(&mut m, cfg).unwrap().unwrap();
    assert_eq!(sharded.manifest.shards.len(), 2);
    let long_shard = sharded
        .manifest
        .shards
        .iter()
        .find(|s| s.identities.iter().any(|id| id == &long_id))
        .unwrap();
    assert!(long_shard.oversized_scc);
    assert_eq!(long_shard.num_bodies, 1);
}

#[test]
fn sharded_root_remaps_selected_index_and_keeps_canonical_entry_def_id() {
    // Original body `0` calls `leaf_0..leaf_3`; callee-first sharding must
    // relocate `top_caller` (`selected[0]`) to its new index while keeping
    // `entryDefId := 0` canonical and permutation-invariant.
    let mut bodies = vec![synth_body(
        "rust-path-v1::top_caller",
        1,
        &[
            "rust-path-v1::leaf_0",
            "rust-path-v1::leaf_1",
            "rust-path-v1::leaf_2",
            "rust-path-v1::leaf_3",
        ],
    )];
    for i in 0..4 {
        bodies.push(synth_body(&format!("rust-path-v1::leaf_{i}"), 1, &[]));
    }
    let mut m = dummy_manifest(bodies);
    let cfg = ShardConfig {
        shard_min_bodies: 2,
        shard_max_bodies: 2,
        shard_max_ast_nodes: 100_000,
    };
    let sharded = maybe_shard_manifest(&mut m, cfg).unwrap().unwrap();
    let entry_idx = m
        .program
        .bodies()
        .iter()
        .position(|b| b.identity() == "rust-path-v1::top_caller")
        .unwrap();
    assert!(entry_idx > 0, "expected top_caller to reorder after leaves");
    assert_eq!(m.selected[0].body_index, entry_idx);
    assert!(
        sharded.root_lean.contains("entryDefId := 0,"),
        "expected canonical entryDefId := 0 in sharded root:\n{}",
        sharded.root_lean
    );
    assert!(
        sharded.root_lean.contains("overflowChecks := false,"),
        "expected default overflowChecks := false in sharded root:\n{}",
        sharded.root_lean
    );
    assert!(
        sharded.root_lean.contains("panicStrategy := Trusted.MirAst.PanicStrategy.unwind,"),
        "expected default panicStrategy := unwind in sharded root:\n{}",
        sharded.root_lean
    );
    assert!(
        sharded.root_lean.contains("hasLocalPanicHandler := false"),
        "expected default hasLocalPanicHandler := false in sharded root:\n{}",
        sharded.root_lean
    );

    // Verify `overflow_checks`, `panic`, and `has_local_panic_handler`
    // survive body reordering and render into `Captured.program`.
    let mut checked_bodies = vec![synth_body(
        "rust-path-v1::top_caller",
        1,
        &["rust-path-v1::leaf_0", "rust-path-v1::leaf_1"],
    )];
    for i in 0..3 {
        checked_bodies.push(synth_body(&format!("rust-path-v1::leaf_{i}"), 1, &[]));
    }
    let mut checked = dummy_manifest(checked_bodies.clone());
    checked.configuration.overflow_checks = true;
    checked.program = ir::Program::try_new_with_options(
        Scope::Crate,
        true,
        ir::PanicStrategy::Abort,
        true,
        checked_bodies,
    )
    .unwrap();
    let checked_sharded = maybe_shard_manifest(&mut checked, cfg).unwrap().unwrap();
    assert!(checked.program.overflow_checks());
    assert_eq!(checked.program.panic(), ir::PanicStrategy::Abort);
    assert!(checked.program.has_local_panic_handler());
    assert!(
        checked_sharded.root_lean.contains("overflowChecks := true,"),
        "expected overflowChecks := true in sharded root:\n{}",
        checked_sharded.root_lean
    );
    assert!(
        checked_sharded
            .root_lean
            .contains("panicStrategy := Trusted.MirAst.PanicStrategy.abort,"),
        "expected panicStrategy := abort in sharded root:\n{}",
        checked_sharded.root_lean
    );
    assert!(
        checked_sharded.root_lean.contains("hasLocalPanicHandler := true"),
        "expected hasLocalPanicHandler := true in sharded root:\n{}",
        checked_sharded.root_lean
    );
}

#[test]
fn sharding_remaps_intra_crate_call_callee_indices_after_body_reorder() {
    // Original order: `caller` at index 0 calls `z_callee` at index 2 via
    // `Terminator::Call { callee: 2, .. }`. Callee-first sharding moves
    // `z_callee` before `caller`, so `reorder_bodies` must rewrite
    // `callee` to `z_callee`'s new index.
    let u8_ty = Ty::Int(ir::IntTy { width: ir::IntWidth::I8, signed: false });
    let caller = Body::try_new_with_callees(
        0,
        false,
        vec![u8_ty],
        vec![
            Block {
                statements: vec![],
                terminator: Terminator::Call {
                    callee: 2,
                    args: vec![],
                    dst: 0,
                    target: Some(1),
                    unwind: ir::UnwindAction::Continue,
                },
            },
            Block { statements: vec![], terminator: Terminator::Ret },
        ],
        "rust-path-v1::a_caller".into(),
        BTreeSet::from(["rust-path-v1::z_callee".to_owned()]),
    )
    .unwrap();
    let pad = synth_body("rust-path-v1::m_pad", 1, &[]);
    let callee = synth_body("rust-path-v1::z_callee", 1, &[]);
    let mut m = dummy_manifest(vec![caller, pad, callee]);
    let cfg = ShardConfig {
        shard_min_bodies: 2,
        shard_max_bodies: 1,
        shard_max_ast_nodes: 100_000,
    };
    let _ = maybe_shard_manifest(&mut m, cfg).unwrap().unwrap();
    let new_callee_idx = m
        .program
        .bodies()
        .iter()
        .position(|b| b.identity() == "rust-path-v1::z_callee")
        .unwrap();
    let new_caller_idx = m
        .program
        .bodies()
        .iter()
        .position(|b| b.identity() == "rust-path-v1::a_caller")
        .unwrap();
    assert!(new_callee_idx < new_caller_idx);
    match &m.program.bodies()[new_caller_idx].blocks()[0].terminator {
        Terminator::Call { callee, .. } => assert_eq!(*callee, new_callee_idx),
        other => panic!("expected Call terminator, got {other:?}"),
    }
}
