// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Post-shrink 6-pass reduction, standalone `repro_<hash>.rs` + `.mir.lean`
//! emission, canonical deduplication, `K <= 8` SCB replay splitting, and
//! `anneal-itree-semantic-detail/v1` + `anneal-known-bug/v1` telemetry.

use std::{fs, process::Command, time::Duration};

use anneal_itree_diff::{
    CaseReport, DifferentialConfig, DifferentialEngine, DifferentialReport,
    dedup::{
        BugRegistry, BugStatus, CanonicalBugFingerprint, DedupRecordOutcome,
        KNOWN_BUG_RECORD_SCHEMA, KnownBugRecord, MAX_WITNESSES_PER_BUG, ScbReplayVerdict,
        derive_verdict_class, dialect_key_for_mode, normalize_miri_ub_cause,
    },
    evaluate_metamorphic_duality, evaluate_rustc_fast_leg,
    fuzzer::{FuzzArithOp, FuzzProgram, FuzzStep, generate_fuzz_batch},
    lean_trace_runner::{LeanTraceMode, MetamorphicDualityReceipt},
    outcome::{
        AuthorityRunResult, CallerFrameLaw, IntKind, MetamorphicStatus, SpineCompareMode,
        TerminalOutcome, TraceVal, TraceVerdict, UbFaultClass, compute_boundary_mem_digest,
    },
    rustc_runner::RustcDualResult,
    shrink::{
        BoundedLoopInduction, FastLegStrategy, HandleId, ShrinkBudget, ShrinkFailureSignature,
        ShrinkHelper, ShrinkHelperOp, ShrinkInput, ShrinkStep, ShrinkableCase, WitnessArtifact,
        WitnessBundle, all_handles_defined_and_typed, canonical_fuzz_program_skeleton_hash,
        canonical_shrinkable_artifact_id, canonical_shrinkable_case_skeleton_hash,
        canonical_witness_artifact_id, render_standalone_fuzz_repro_rs, render_standalone_mir_lean,
        render_standalone_shrinkable_repro_rs, render_standalone_shrinkable_repro_rs_for_signature,
        shrink_case_two_tier_with_budget, shrink_coupled_pair_with_difference_proxy,
        shrink_env_schedule, shrink_fuzz_program_two_tier_with_budget,
        shrink_fuzz_program_with_budget, shrink_u32_stride_non_monotonic,
        smaller_u32_stride_candidates,
    },
    shrink_and_build_witness_two_tier_with_budget, shrink_and_build_witness_with_budget,
    spec::{
        CaseCategory, ExpectedCaseClass, LeanProgramSpec, ReturnShape, TraceTestCase,
        parse_pre_abort_stdout_with_expected_args, parse_trace_json_stdout_with_expected_args,
        render_standalone_metamorphic_rust_harness,
        render_standalone_metamorphic_rust_harness_with_relations,
    },
    telemetry::{
        ALPHA_BANNER_DEFAULT, BuildFreshness, EvidenceBlockTelemetry, KnownBugsExport,
        SEMANTIC_DETAIL_SCHEMA, SemanticDetailRecord, TRUST_TIER_DEFAULT, TelemetryContext,
        normalize_repo_slug, record_report_telemetry_witnesses, try_normalize_repo_slug,
        verify_head_build_provenance_with,
    },
    trace_observer::{EnvAction, EnvSchedule, ObservableEvent, ObservableSpine},
    workspace_anneal_root,
};

fn hermetic_git_command(cwd: &std::path::Path) -> Command {
    let mut cmd = Command::new("git");
    for var in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    ] {
        cmd.env_remove(var);
    }
    cmd.env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .env("GIT_TERMINAL_PROMPT", "0")
        .arg("-C")
        .arg(cwd)
        .args(["-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null"]);
    cmd
}

fn mk_auth(authority: &str, outcome: TerminalOutcome) -> AuthorityRunResult {
    AuthorityRunResult {
        authority: authority.to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 5,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    }
}

fn mk_ub_case_report(
    case_id: &str,
    miri_detail: &str,
    lean_outcome: TerminalOutcome,
    verdict: TraceVerdict,
) -> CaseReport {
    let miri_leg = mk_auth("miri", TerminalOutcome::FaultUb { detail: miri_detail.to_string() });
    let lean_leg = mk_auth("lean-compositional-itree", lean_outcome);
    CaseReport {
        case_id: case_id.to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict,
        expectation_violation: None,
        rustc_dual: RustcDualResult::skipped_for_ub("Miri UB"),
        miri: Some(miri_leg),
        lean: Some(lean_leg),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    }
}

#[test]
fn shrink_failure_signature_pins_ub_classes_and_blocks_cross_ub_drift() {
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(0),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ptr_ub_rep = mk_ub_case_report(
        "ptr_ub",
        "Undefined Behavior: Tree Borrows: write access through <1234> is forbidden",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let uninit_ub_rep = mk_ub_case_report(
        "uninit_ub",
        "Undefined Behavior: constructing invalid value at .0: encountered 2, expected a boolean",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );

    let sig_ptr = ShrinkFailureSignature::from_case_report(&ptr_ub_rep).unwrap();
    let sig_uninit = ShrinkFailureSignature::from_case_report(&uninit_ub_rep).unwrap();
    assert_eq!(sig_ptr.ref_ub_class, Some(UbFaultClass::PointerOrMemoryAccess));
    assert_eq!(sig_uninit.ref_ub_class, Some(UbFaultClass::InvalidValueOrUninit));
    assert_eq!(sig_ptr.lean_fault_site_kind, "returned");
    assert_ne!(sig_ptr, sig_uninit, "signature must distinguish distinct Miri UB classes");

    // Verify Lean fault site kind distinguishes `unchecked_shift` vs
    // `assign_or_mem_deref`.
    let spurious_shift = CaseReport {
        case_id: "spur_shift".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::ConservativeOverApprox {
            reason: "spurious".to_string(),
            ub_refutation_disallowed: true,
            undeclared_ub_fault: true,
        },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth(
            "lean",
            TerminalOutcome::FaultUb {
                detail: "unchecked shift overflow: Trusted.MirSemantics.FaultKind.undefined"
                    .to_string(),
            },
        )),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let mut spurious_mem = spurious_shift.clone();
    spurious_mem.lean = Some(mk_auth(
        "lean",
        TerminalOutcome::FaultUb {
            detail: "pointer or memory access undefined: Trusted.MirSemantics.FaultKind.undefined"
                .to_string(),
        },
    ));
    let sig_shift = ShrinkFailureSignature::from_case_report(&spurious_shift).unwrap();
    let sig_mem = ShrinkFailureSignature::from_case_report(&spurious_mem).unwrap();
    assert_eq!(sig_shift.lean_ub_class, Some(UbFaultClass::UncheckedShiftOverflow));
    assert_eq!(sig_shift.lean_fault_site_kind, "unchecked_shift");
    assert_eq!(sig_mem.lean_ub_class, Some(UbFaultClass::PointerOrMemoryAccess));
    assert_eq!(sig_mem.lean_fault_site_kind, "assign_or_mem_deref");
    assert_ne!(sig_shift, sig_mem);

    // Verify shrinking blocks drift from PointerOrMemoryAccess into
    // InvalidValueOrUninit!
    let mut prog = generate_fuzz_batch(0x4242, 1)[0].clone();
    prog.input_x = 128;
    prog.input_y = 64;
    prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 },
        FuzzStep::HelperCall { callee_idx: 2, bias: 11 },
    ];
    let (witness, tool_err) = shrink_and_build_witness_with_budget(
        "ub_drift_guard",
        &prog,
        &ptr_ub_rep.verdict,
        &sig_ptr,
        ShrinkBudget::default(),
        |cand| {
            // If `input_x < 16` or `HelperCall` is removed, simulate
            // drifting into a different Miri UB class
            // (`InvalidValueOrUninit`)!
            let has_call = cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }));
            if has_call && cand.input_x >= 16 { ptr_ub_rep.clone() } else { uninit_ub_rep.clone() }
        },
    );
    assert!(tool_err.is_none(), "expected clean convergence: {tool_err:?}");
    assert!(witness.shrink.converged_1_minimal);
    assert_eq!(witness.shrink.minimized.input_x, 16);
    assert_eq!(witness.shrink.minimized.input_y, 0);
    assert_eq!(witness.shrink.minimized.steps.len(), 1);
    assert!(matches!(witness.shrink.minimized.steps[0], FuzzStep::HelperCall { .. }));
    assert_eq!(
        witness.signature.as_ref().and_then(|s| s.ref_ub_class),
        Some(UbFaultClass::PointerOrMemoryAccess)
    );
}

#[test]
fn two_tier_fast_leg_first_short_circuits_and_confirms_final_fixpoint() {
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(1),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let target_rep = mk_ub_case_report(
        "fast_leg",
        "Undefined Behavior: pointer dereference failed: out-of-bounds",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let sig = ShrinkFailureSignature::from_case_report(&target_rep).unwrap();
    assert_eq!(FastLegStrategy::select(&sig, true, true, true), FastLegStrategy::MiriUbFirst);

    let mut prog = generate_fuzz_batch(0x7777, 1)[0].clone();
    prog.input_x = 240;
    prog.input_y = 120;
    prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 19 },
        FuzzStep::BranchMix { then_imm: 7, else_imm: 9 },
        FuzzStep::BoundedLoop { iters: 4, step_imm: 3 },
        FuzzStep::HelperCall { callee_idx: 1, bias: 21 },
    ];

    let mut fast_calls = 0usize;
    let mut full_calls = 0usize;
    let res = shrink_fuzz_program_two_tier_with_budget(
        &prog,
        ShrinkBudget::default(),
        FastLegStrategy::MiriUbFirst,
        |cand| {
            fast_calls += 1;
            // Fast leg (Miri UB) fails unless `input_x >= 32` AND
            // `HelperCall` remains.
            cand.input_x >= 32
                && cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
        },
        |cand| {
            full_calls += 1;
            cand.input_x >= 32
                && cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
        },
    );

    assert!(res.succeeded && res.is_one_minimal && res.converged_1_minimal);
    assert_eq!(res.minimized.input_x, 32);
    assert_eq!(res.minimized.input_y, 0);
    assert_eq!(res.minimized.steps.len(), 1);
    assert!(res.pass_stats.fast_leg_rejections > 0, "expected fast-leg rejections");
    assert!(
        full_calls < fast_calls,
        "expected Tier-2 full oracle calls ({full_calls}) strictly below Tier-1 calls ({fast_calls})"
    );
    assert!(res.pass_stats.final_full_confirmations >= 1);

    // Tier-2 full confirmation must still reject candidates where Tier-1 fast
    // leg accepts (`true`) but Tier-2 full oracle rejects (`false`).
    let two_tier_mismatch = shrink_fuzz_program_two_tier_with_budget(
        &prog,
        ShrinkBudget::default(),
        FastLegStrategy::MiriUbFirst,
        |cand| {
            cand.input_x >= 32
                && cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
        },
        |cand| {
            cand.input_x >= 128
                && cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
        },
    );
    assert!(two_tier_mismatch.succeeded && two_tier_mismatch.is_one_minimal);
    assert_eq!(two_tier_mismatch.minimized.input_x, 128);
}

#[test]
fn six_hierarchical_passes_handle_def_use_stride_diff_proxy_and_alpha_rename() {
    // 1. Stride + coupled-pair difference proxy tests (`Plausible`).
    let stride_cands = smaller_u32_stride_candidates(48, Some(12));
    assert!(stride_cands.contains(&24));
    assert!(stride_cands.contains(&36));
    assert!(stride_cands.contains(&12));
    assert_eq!(
        shrink_u32_stride_non_monotonic(48, Some(12), |v| v >= 24 && v.is_multiple_of(12)),
        24
    );
    assert_eq!(
        shrink_coupled_pair_with_difference_proxy(100, 110, None, |off, len| {
            len == off + 10 && off >= 10
        }),
        (10, 20)
    );
    assert_eq!(
        shrink_coupled_pair_with_difference_proxy(20, 10, None, |a, b| a > b && b >= 10),
        (11, 10)
    );
    assert_eq!(
        shrink_coupled_pair_with_difference_proxy(64, 64, None, |a, b| a == b && a >= 8),
        (8, 8),
        "equal-coordinate invariants (delta == 0) must shrink jointly via Phase A"
    );

    // 2. ScheduleDdmin test.
    let mut sched = EnvSchedule::default();
    sched.global.push_back(EnvAction::Unwind { message: "unused global unwind".to_string() });
    sched.push_callee(
        "unused_callee",
        EnvAction::Abort { reason: "unused abort long message".to_string() },
    );
    sched.push_callee("target_fn", EnvAction::ReturnBytes(vec![0x77, 0xFF, 0x05, 0x22]));
    sched.push_callee(
        "target_fn",
        EnvAction::Unwind { message: "very long unwind error diagnostic".to_string() },
    );
    let min_sched = shrink_env_schedule(&sched, |s| {
        let Some(q) = s.per_callee.get("target_fn") else {
            return false;
        };
        q.iter().any(|a| matches!(a, EnvAction::ReturnBytes(b) if b.len() == 4 && b[2] >= 1))
            && q.iter().any(|a| matches!(a, EnvAction::Unwind { .. }))
    });
    assert!(min_sched.global.is_empty());
    assert!(!min_sched.per_callee.contains_key("unused_callee"));
    let target_q = &min_sched.per_callee["target_fn"];
    assert_eq!(target_q.len(), 2);
    assert_eq!(target_q[0], EnvAction::ReturnBytes(vec![0, 0, 1, 0]));
    assert_eq!(target_q[1], EnvAction::Unwind { message: "u".to_string() });

    // 3. Full 6-pass ShrinkableCase reduction with PropEr handle def-use
    // filter.
    let h0 = HandleId(10);
    let h1 = HandleId(20);
    let h2 = HandleId(30);
    let h3 = HandleId(40);
    let case = ShrinkableCase {
        name: "complex_bug".to_string(),
        scalar_width: anneal_itree_diff::outcome::IntKind::U128,
        inputs: vec![
            ShrinkInput {
                local_id: 9,
                width: anneal_itree_diff::outcome::IntKind::U128,
                value: 200,
                align_hint: Some(8),
            },
            ShrinkInput {
                local_id: 14,
                width: anneal_itree_diff::outcome::IntKind::U128,
                value: 99,
                align_hint: None,
            },
        ],
        struct_fields: vec![
            anneal_itree_diff::outcome::IntKind::U64,
            anneal_itree_diff::outcome::IntKind::U128,
            anneal_itree_diff::outcome::IntKind::U32,
        ],
        slice_len: Some(64),
        slice_align: 8,
        helpers: vec![
            ShrinkHelper {
                helper_id: 7,
                multiplier: 3,
                addend: 1,
                op: ShrinkHelperOp::AffineMulAdd,
            },
            ShrinkHelper {
                helper_id: 8,
                multiplier: 5,
                addend: 2,
                op: ShrinkHelperOp::AffineMulAdd,
            },
        ],
        steps: vec![
            ShrinkStep::IfFalseDecoy {
                block_id: 40,
                body: vec![ShrinkStep::ArithImm { dst_local: 9, op: FuzzArithOp::Xor, imm: 12345 }],
            },
            ShrinkStep::DropGuardWrapper {
                local_id: 50,
                body: vec![ShrinkStep::Alloc { handle: h0, size: 64, align: 8, local_id: 19 }],
            },
            ShrinkStep::Borrow { dst: h1, src: h0, mutable: true, local_id: 21 },
            ShrinkStep::BranchMix {
                block_id: 60,
                cond_local: 9,
                taken_then: true,
                dynamic_even_cond: false,
                then_steps: vec![ShrinkStep::HelperCall {
                    dst_local: 9,
                    helper_id: 7,
                    block_id: 61,
                    bias: 12,
                    rhs_local: None,
                }],
                else_steps: vec![ShrinkStep::ArithImm {
                    dst_local: 9,
                    op: FuzzArithOp::Add,
                    imm: 42,
                }],
            },
            ShrinkStep::BoundedLoop {
                block_id: 70,
                iters: 4,
                induction: None,
                body: vec![ShrinkStep::PairOffsetLen {
                    offset: 104,
                    len: 112,
                    align: 8,
                    local_id: 25,
                }],
            },
            ShrinkStep::SplitAt { left: h2, right: h3, src: h1, mid: 24, len: 64, align: 8 },
            ShrinkStep::UseHandle { handle: h3, offset: 8, len: 16, align: 8, local_id: 31 },
        ],
        env_schedule: sched,
        return_local: 9,
    };

    assert!(all_handles_defined_and_typed(&case.steps, &case.helpers));
    // Removing Alloc(h0) violates handle def-use invariant in < 1 us.
    let broken_steps: Vec<ShrinkStep> = case
        .steps
        .iter()
        .filter(|s| !matches!(s, ShrinkStep::DropGuardWrapper { .. }))
        .cloned()
        .collect();
    assert!(!all_handles_defined_and_typed(&broken_steps, &case.helpers));

    let res = shrink_case_two_tier_with_budget(
        &case,
        ShrinkBudget { max_evals: 512, max_duration: Duration::from_secs(30) },
        FastLegStrategy::MiriUbFirst,
        has_split_and_pair_bug,
        has_split_and_pair_bug,
    );
    assert!(res.succeeded && res.is_one_minimal && res.converged_1_minimal);
    assert!(
        res.pass_stats.def_use_filter_skips > 0,
        "PropEr filter must skip unbound handles: stats={:?}, min={:?}",
        res.pass_stats,
        res.minimized
    );
    assert!(res.pass_stats.schedule_ddmin_reductions > 0);
    assert!(res.pass_stats.call_cfg_collapse_reductions > 0);
    assert!(res.pass_stats.type_layout_narrow_reductions > 0);
    assert!(res.pass_stats.stride_diff_proxy_reductions > 0);
    assert!(res.pass_stats.alpha_rename_applied > 0);

    let m = &res.minimized;
    assert_eq!(m.scalar_width, anneal_itree_diff::outcome::IntKind::U8);
    assert_eq!(m.struct_fields.len(), 1);
    assert_eq!(m.slice_len, Some(8));
    assert!(m.helpers.is_empty(), "unused helpers must be pruned");
    assert!(!m.steps.iter().any(|s| matches!(
        s,
        ShrinkStep::IfFalseDecoy { .. }
            | ShrinkStep::DropGuardWrapper { .. }
            | ShrinkStep::BranchMix { .. }
            | ShrinkStep::BoundedLoop { .. }
            | ShrinkStep::HelperCall { .. }
    )));
    // Extra noncausal input (local_id 14) is pruned, leaving 1 input whose
    // alpha-renamed local ID starts at 0 (`inputs[0].local_id == 0`).
    assert_eq!(m.inputs.len(), 1);
    assert_eq!(m.inputs[0].local_id, 0);
    // Stride-shrunk `SplitAt` (`mid = 24` -> `8`, `align = 8` -> `1`,
    // `len = 64` -> `9`) and `PairOffsetLen` (`offset = 104` -> `8`,
    // `len = 112` -> `16`, `align = 8` -> `1`).
    let split = m
        .steps
        .iter()
        .find_map(|s| match s {
            ShrinkStep::SplitAt { mid, len, align, .. } => Some((*mid, *len, *align)),
            _ => None,
        })
        .expect("SplitAt preserved");
    assert_eq!(split, (8, 9, 1));
    let pair = m
        .steps
        .iter()
        .find_map(|s| match s {
            ShrinkStep::PairOffsetLen { offset, len, align, .. } => Some((*offset, *len, *align)),
            _ => None,
        })
        .expect("PairOffsetLen preserved");
    assert_eq!(pair, (8, 16, 1));

    // Also verify standalone `ShrinkableCase` Rust repro compiles cleanly.
    let skel = canonical_shrinkable_case_skeleton_hash(m);
    let rs_src = render_standalone_shrinkable_repro_rs(m, &skel);
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let rs_path = tmp.path().join(format!("repro_{skel}.rs"));
    let bin_path = tmp.path().join("repro_shrinkable_bin");
    fs::write(&rs_path, &rs_src).expect("write shrinkable repro");
    let out = Command::new(&engine.rustc.rustc_bin)
        .arg("--edition")
        .arg("2021")
        .arg(&rs_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .expect("spawn rustc");
    assert!(
        out.status.success(),
        "render_standalone_shrinkable_repro_rs failed to compile:\n{}\nsource:\n{}",
        String::from_utf8_lossy(&out.stderr),
        rs_src
    );
}

fn any_step_recursive(steps: &[ShrinkStep], pred: &dyn Fn(&ShrinkStep) -> bool) -> bool {
    steps.iter().any(|s| {
        if pred(s) {
            return true;
        }
        match s {
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                any_step_recursive(then_steps, pred) || any_step_recursive(else_steps, pred)
            }
            ShrinkStep::BoundedLoop { body, .. }
            | ShrinkStep::IfFalseDecoy { body, .. }
            | ShrinkStep::DropGuardWrapper { body, .. } => any_step_recursive(body, pred),
            _ => false,
        }
    })
}

fn has_split_and_pair_bug(c: &ShrinkableCase) -> bool {
    let has_sched = c
        .env_schedule
        .per_callee
        .get("target_fn")
        .is_some_and(|q| q.iter().any(|a| matches!(a, EnvAction::Unwind { .. })));
    let has_split = any_step_recursive(&c.steps, &|s| {
        matches!(
            s,
            ShrinkStep::SplitAt { mid, len, align, .. }
                if *mid >= 8 && *len > *mid && mid.is_multiple_of(*align) && len.is_multiple_of(*align)
        )
    });
    let has_pair = any_step_recursive(&c.steps, &|s| {
        matches!(
            s,
            ShrinkStep::PairOffsetLen { offset, len, align, .. }
                if *offset >= 8 && *len >= offset + 8 && offset.is_multiple_of(*align) && len.is_multiple_of(*align)
        )
    });
    let slice_ok = c.slice_len.is_some_and(|l| l >= 8 && l.is_multiple_of(8));
    let struct_ok = !c.struct_fields.is_empty();
    let inputs_ok = !c.inputs.is_empty();
    has_sched && has_split && has_pair && slice_ok && struct_ok && inputs_ok
}

#[test]
fn canonical_alpha_rename_and_skeleton_hash_coalescing() {
    let base = ShrinkableCase {
        name: "one".to_string(),
        scalar_width: anneal_itree_diff::outcome::IntKind::U32,
        inputs: vec![ShrinkInput {
            local_id: 9,
            width: anneal_itree_diff::outcome::IntKind::U32,
            value: 42,
            align_hint: None,
        }],
        struct_fields: vec![],
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 99,
            multiplier: 3,
            addend: 1,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::Alloc { handle: HandleId(77), size: 32, align: 8, local_id: 50 },
            ShrinkStep::HelperCall {
                dst_local: 50,
                helper_id: 99,
                block_id: 12,
                bias: 17,
                rhs_local: None,
            },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 9,
    };
    let mut scrambled = base.clone();
    scrambled.name = "two".to_string();
    scrambled.inputs[0].local_id = 100;
    scrambled.inputs[0].value = 9999;
    scrambled.return_local = 100;
    scrambled.helpers[0] =
        ShrinkHelper { helper_id: 3, multiplier: 11, addend: 7, op: ShrinkHelperOp::AffineMulAdd };
    scrambled.steps = vec![
        ShrinkStep::Alloc { handle: HandleId(5), size: 128, align: 8, local_id: 200 },
        ShrinkStep::HelperCall {
            dst_local: 200,
            helper_id: 3,
            block_id: 88,
            bias: 555,
            rhs_local: None,
        },
    ];
    assert_eq!(
        canonical_shrinkable_case_skeleton_hash(&base),
        canonical_shrinkable_case_skeleton_hash(&scrambled),
        "alpha-renamed, constant-erased skeleton hashes must coalesce"
    );

    let mut p1 = generate_fuzz_batch(111, 2)[0].clone();
    let mut p2 = generate_fuzz_batch(999, 5)[3].clone();
    p1.input_x = 16;
    p1.input_y = 4;
    p1.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 }];
    p2.input_x = 4096;
    p2.input_y = 777;
    p2.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 999 }];
    assert_eq!(
        canonical_fuzz_program_skeleton_hash(&p1, None),
        canonical_fuzz_program_skeleton_hash(&p2, None),
    );

    // Ensure `EnvAction::ReturnBytes` schedules hash non-trivially (never
    // collapsing to `serde_json` error `""` under `#[serde(tag = "action")]`).
    let mut sched_4a = EnvSchedule::default();
    sched_4a.push_callee("ext", EnvAction::ReturnBytes(vec![1, 2, 3, 4]));
    let mut sched_4b = EnvSchedule::default();
    sched_4b.push_callee("ext", EnvAction::ReturnBytes(vec![9, 8, 7, 6]));
    let mut sched_8 = EnvSchedule::default();
    sched_8.push_callee("ext", EnvAction::ReturnBytes(vec![0; 8]));
    assert_eq!(
        canonical_fuzz_program_skeleton_hash(&p1, Some(&sched_4a)),
        canonical_fuzz_program_skeleton_hash(&p2, Some(&sched_4b)),
        "constant-erased ReturnBytes of matching length must coalesce"
    );
    assert_ne!(
        canonical_fuzz_program_skeleton_hash(&p1, Some(&sched_4a)),
        canonical_fuzz_program_skeleton_hash(&p1, Some(&sched_8)),
        "distinct ReturnBytes arities must remain distinct"
    );
}

#[test]
fn canonical_dedup_k8_archive_and_scb_post_patch_replay_split() {
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep1 = mk_ub_case_report(
        "c1",
        "Undefined Behavior: Tree Borrows: write access through <0x7f10> at alloc12 is forbidden",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let rep2 = mk_ub_case_report(
        "c2",
        "Undefined Behavior: Tree Borrows: write access through <0x9a20> at alloc999 is forbidden",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let sig = ShrinkFailureSignature::from_case_report(&rep1).unwrap();

    // Verify BugId ignores addresses/alloc IDs and constant witnesses, AND is
    // order-independent on `mir_construct_sig`.
    let fp1 = CanonicalBugFingerprint::new(
        "main",
        "mir_v1_itree",
        "unsound_accept:missed_ub",
        vec!["term:call_intra".into(), "assign:binop:add".into()],
        "pointer_or_memory_access:tree_borrows_disabled_write",
        "returned",
        "aaaaaaaaaaaa",
    );
    let fp2 = CanonicalBugFingerprint::new(
        "main",
        "mir_v1_itree",
        "unsound_accept:missed_ub",
        vec!["assign:binop:add".into(), "term:call_intra".into(), "assign:binop:add".into()],
        "pointer_or_memory_access:tree_borrows_disabled_write",
        "returned",
        "bbbbbbbbbbbb",
    );
    assert_eq!(fp1.bug_id(), fp2.bug_id());
    assert!(fp1.bug_id().starts_with("ITREE-MISSUB-"));
    assert!(fp1.bug_id().len() <= 32);

    let mut reg = BugRegistry::new("google/zerocopy");

    // Non-1-minimal witness must go to provisional_cases, never buckets!
    let mut p_base = generate_fuzz_batch(0x101, 1)[0].clone();
    p_base.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let provisional_res = shrink_fuzz_program_with_budget(
        &p_base,
        ShrinkBudget { max_evals: 0, max_duration: Duration::from_secs(1) },
        |_| true,
    );
    let provisional_w = WitnessArtifact::from_shrink(
        "prov",
        rep1.verdict.clone(),
        rep1.verdict.clone(),
        provisional_res,
    );
    let prov_out = reg.record_witness(
        &provisional_w,
        &rep1,
        "main",
        true,
        dialect_key_for_mode(LeanTraceMode::CompositionalITree, false),
        "1111111111111111111111111111111111111111",
        None,
    );
    assert!(matches!(prov_out, DedupRecordOutcome::Provisional { .. }));
    assert!(reg.buckets.is_empty());
    assert_eq!(reg.provisional_cases.len(), 1);

    // Insert 10 distinct skeleton shapes with the SAME construct signature:
    // `extract_fuzz_program_construct_tags` deduplicates construct tags, so
    // `[Add]`, `[Add, Add]`, ... all share the same primary `BugId` while
    // getting distinct `minimized_skeleton_hash`es.
    let mut bucket_id = String::new();
    for k in 1..=10 {
        let mut p = p_base.clone();
        p.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: k as u32 }; k];
        let mut shrink_res = shrink_fuzz_program_with_budget(&p, ShrinkBudget::default(), |cand| {
            cand.steps.len() == k
        });
        shrink_res.succeeded = true;
        shrink_res.is_one_minimal = true;
        shrink_res.converged_1_minimal = true;
        let w = WitnessArtifact::from_shrink(
            format!("w_{k}"),
            rep1.verdict.clone(),
            rep1.verdict.clone(),
            shrink_res,
        )
        .with_signature(sig.clone());
        let mut case_rep = if k % 2 == 0 { rep2.clone() } else { rep1.clone() };
        case_rep.case_id = w.case_id.clone();
        let sha = format!("{k:040x}");
        let outcome = reg.record_witness(&w, &case_rep, "main", true, "mir_v1_itree", &sha, None);
        match outcome {
            DedupRecordOutcome::NewBug { bug_id, .. } => {
                assert_eq!(k, 1);
                bucket_id = bug_id;
            }
            DedupRecordOutcome::NewSkeletonAttached { retained_count, .. } => {
                assert!(retained_count <= MAX_WITNESSES_PER_BUG);
            }
            DedupRecordOutcome::DuplicateHit { .. } => {
                assert!(k > MAX_WITNESSES_PER_BUG);
            }
            other => panic!("unexpected outcome at k={k}: {other:?}"),
        }
    }

    assert_eq!(reg.buckets.len(), 1);
    let target_still_failing = {
        let bucket = &reg.buckets[&bucket_id];
        assert_eq!(bucket.witnesses.len(), MAX_WITNESSES_PER_BUG);
        assert_eq!(bucket.hit_count, 10);
        assert_eq!(
            bucket.introduced_sha,
            format!("{:040x}", 1),
            "first-seen IntroducedSha must never be overwritten"
        );
        bucket.witnesses[3].minimized_skeleton_hash.clone()
    };

    // SCB post-patch replay: StillOpen when all fail.
    let still_open = reg
        .classify_post_patch_replay(&bucket_id, "2222222222222222222222222222222222222222", |_| {
            true
        })
        .unwrap();
    assert!(matches!(still_open, ScbReplayVerdict::StillOpen { replayed_count: 8, .. }));
    assert_eq!(reg.buckets[&bucket_id].status, BugStatus::Open);

    // SCB post-patch replay: Split when 7 witnesses pass and 1 witness
    // still fails!
    let split = reg
        .classify_post_patch_replay(&bucket_id, "3333333333333333333333333333333333333333", |w| {
            w.minimized_skeleton_hash == target_still_failing
        })
        .unwrap();
    let ScbReplayVerdict::Split { original_bug_id, split_bugs, fixed_skeletons, .. } = split else {
        panic!("expected SCB Split verdict");
    };
    assert_eq!(original_bug_id, bucket_id);
    assert_eq!(fixed_skeletons.len(), 7);
    assert_eq!(split_bugs.len(), 1);
    let child = &split_bugs[0];
    assert_eq!(child.bug_id, format!("{bucket_id}-{}", &target_still_failing[..6]));
    assert_eq!(child.status, BugStatus::Open);
    assert_eq!(child.fixed_sha, "");
    assert_eq!(reg.buckets[&bucket_id].status, BugStatus::Fixed);
    assert_eq!(reg.buckets[&bucket_id].fixed_sha, "3333333333333333333333333333333333333333");

    // SCB AllFixed on split child.
    let child_id = child.bug_id.clone();
    let all_fixed = reg
        .classify_post_patch_replay(&child_id, "4444444444444444444444444444444444444444", |_| {
            false
        })
        .unwrap();
    assert!(matches!(all_fixed, ScbReplayVerdict::AllFixed { replayed_count: 1, .. }));
    assert_eq!(reg.buckets[&child_id].status, BugStatus::Fixed);

    // Verify vendor-neutral `anneal-known-bug/v1` records pass invariant
    // checks.
    let records = reg.to_known_bug_records().unwrap();
    assert_eq!(records.len(), 2);
    assert!(records.iter().all(|p| {
        p.schema_version == KNOWN_BUG_RECORD_SCHEMA && p.source == "itree_diff_fuzzer"
    }));
}

#[test]
fn live_synthetic_bug_shrink_dedup_bundle_compile_and_telemetry_honesty() {
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(
        anneal_root.clone(),
        Some(tmp.path().join("cache")),
    );
    // Keep this test self-contained and fast (`rustc` real compiler +
    // optional lean/miri); verify standalone `repro_<hash>.rs` compilation
    // with the pinned sysroot `rustc`.
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let mut prog = generate_fuzz_batch(0xC0DE_1234, 2)[1].clone();
    prog.input_x = 144;
    prog.input_y = 72;
    prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 31 },
        FuzzStep::BranchMix { then_imm: 5, else_imm: 9 },
        FuzzStep::BoundedLoop { iters: 3, step_imm: 7 },
        FuzzStep::PaddedRoundTrip { tag_byte: 42 },
        FuzzStep::HelperCall { callee_idx: 2, bias: 19 },
    ];

    // Live rustc dual evaluation paired with an injected synthetic Lean bug
    // where Lean fails to detect UB (or diverges) whenever
    // `HelperCall { callee_idx: 2 }` and `input_x >= 16`, while
    // `input_x == 8` simulates an unrelated UB class!
    let eval_live = |cand: &FuzzProgram| -> CaseReport {
        let case = cand.to_trace_test_case();
        let rustc_dual = engine.rustc.run_dual(&case);
        let has_h2 = cand
            .steps
            .iter()
            .any(|s| matches!(s, FuzzStep::HelperCall { callee_idx, .. } if callee_idx % 3 == 2));
        if has_h2 && cand.input_x >= 16 {
            CaseReport {
                case_id: case.id,
                category: CaseCategory::FuzzGenerated,
                expected_class: ExpectedCaseClass::Agree,
                verdict: TraceVerdict::UnsoundAccept {
                    detail: "miri detected UB while lean accepted".to_string(),
                },
                expectation_violation: None,
                rustc_dual: RustcDualResult::skipped_for_ub("synthetic UB"),
                miri: Some(mk_auth(
                    "miri",
                    TerminalOutcome::FaultUb {
                        detail: "Undefined Behavior: attempting a read access using <alloc1>: borrow stack forbids".to_string(),
                    },
                )),
                lean: Some(mk_auth("lean-compositional-itree", rustc_dual.o0.outcome.clone())),
                lean_strict_probe: None,
                mir_eval: None,
                metamorphic: None,
            }
        } else if cand.input_x == 8 {
            // Distinct UB class (must be blocked by `ShrinkFailureSignature`!)
            CaseReport {
                case_id: case.id,
                category: CaseCategory::FuzzGenerated,
                expected_class: ExpectedCaseClass::Agree,
                verdict: TraceVerdict::UnsoundAccept {
                    detail: "miri detected UB while lean accepted".to_string(),
                },
                expectation_violation: None,
                rustc_dual: RustcDualResult::skipped_for_ub("synthetic UB"),
                miri: Some(mk_auth(
                    "miri",
                    TerminalOutcome::FaultUb {
                        detail: "Undefined Behavior: constructing invalid value: encountered 2, expected a boolean".to_string(),
                    },
                )),
                lean: Some(mk_auth("lean-compositional-itree", rustc_dual.o0.outcome.clone())),
                lean_strict_probe: None,
                mir_eval: None,
                metamorphic: None,
            }
        } else {
            CaseReport {
                case_id: case.id,
                category: CaseCategory::FuzzGenerated,
                expected_class: ExpectedCaseClass::Agree,
                verdict: TraceVerdict::Agree,
                expectation_violation: None,
                rustc_dual,
                miri: None,
                lean: None,
                lean_strict_probe: None,
                mir_eval: None,
                metamorphic: None,
            }
        }
    };

    let init_rep = eval_live(&prog);
    let sig = ShrinkFailureSignature::from_case_report(&init_rep).unwrap();
    let (witness, err) = shrink_and_build_witness_two_tier_with_budget(
        &init_rep.case_id,
        &prog,
        &init_rep.verdict,
        &sig,
        ShrinkBudget::default(),
        FastLegStrategy::MiriUbFirst,
        |cand| {
            cand.input_x >= 16
                && cand.steps.iter().any(
                    |s| matches!(s, FuzzStep::HelperCall { callee_idx, .. } if callee_idx % 3 == 2),
                )
        },
        eval_live,
    );
    assert!(err.is_none(), "unexpected shrink error: {err:?}");
    assert!(witness.shrink.converged_1_minimal);
    assert_eq!(witness.shrink.minimized.input_x, 16);
    assert_eq!(witness.shrink.minimized.input_y, 0);
    assert_eq!(witness.shrink.minimized.steps.len(), 1);
    assert_eq!(
        witness.signature.as_ref().and_then(|s| s.ref_ub_class),
        Some(UbFaultClass::PointerOrMemoryAccess)
    );

    // Persist standalone bundle (`repro_<skel>.rs` +
    // `program_<skel>.mir.lean` + `witness_<skel>.json`).
    let bundle_dir = tmp.path().join("witness_bundle");
    let bundle = WitnessBundle::from_witness(witness.clone(), None);
    let paths = bundle.write_to_dir(&bundle_dir).expect("write witness bundle");
    assert!(paths.repro_rs_path.is_file());
    assert!(paths.mir_lean_path.is_file());
    assert!(paths.witness_json_path.is_file());

    // Compile `repro_<skel>.rs` standalone with real `rustc`!
    let exe_out = tmp.path().join("repro_bin");
    let rustc_out = Command::new(&engine.rustc.rustc_bin)
        .arg("--edition")
        .arg("2021")
        .arg(&paths.repro_rs_path)
        .arg("-o")
        .arg(&exe_out)
        .output()
        .expect("spawn rustc");
    assert!(
        rustc_out.status.success(),
        "repro_<hash>.rs failed to compile with {:?}: {}",
        engine.rustc.rustc_bin,
        String::from_utf8_lossy(&rustc_out.stderr)
    );
    let run_out = Command::new(&exe_out).output().expect("run compiled repro");
    assert!(run_out.status.success());

    // Verify `.mir.lean` contains valid `Trusted.MirAst` program and args.
    let lean_src = fs::read_to_string(&paths.mir_lean_path).expect("read .mir.lean");
    assert!(lean_src.contains("import Trusted.MirAst"));
    assert!(lean_src.contains("def reproProgram : Program"));

    // Record into BugRegistry and emit `anneal-itree-semantic-detail/v1` +
    // `anneal-known-bug/v1`.
    let mut ctx = TelemetryContext::discover(&anneal_root);
    ctx.repo = "google/zerocopy".to_string();
    ctx.branch = "main".to_string();
    ctx.branch_scope = "main".to_string();
    ctx.exposed_on_main = true;

    let min_rep = eval_live(&witness.shrink.minimized);
    let mut reg = BugRegistry::new(&ctx.repo);
    let rec_outcome = reg.record_witness(
        &witness,
        &min_rep,
        &ctx.branch_scope,
        ctx.exposed_on_main,
        "mir_v1_itree",
        &ctx.commit_sha,
        None,
    );
    assert!(matches!(rec_outcome, DedupRecordOutcome::NewBug { .. }));

    let report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![min_rep],
        vec![witness],
    );
    let detail = SemanticDetailRecord::from_report_and_registry(&report, &reg, &ctx).unwrap();
    assert_eq!(detail.schema, "anneal-itree-semantic-detail/v1");
    assert_eq!(detail.alpha_notice, ALPHA_BANNER_DEFAULT);
    assert_eq!(detail.overall_status, "FAIL");
    assert_eq!(detail.known_bugs.len(), 1);
    assert_eq!(
        detail.differential_runs[0].unsound_missed_fault_count
            + detail.differential_runs[0].value_mismatch_count,
        1
    );

    let detail_path = tmp.path().join("semantics-detail.jsonl");
    detail.write_jsonl(&detail_path).unwrap();
    let line = fs::read_to_string(&detail_path).unwrap();
    assert_eq!(line.lines().count(), 1);

    let bugs_json = tmp.path().join("known_bugs.json");
    let bugs_jsonl = tmp.path().join("known_bugs.jsonl");
    let export = KnownBugsExport::from_report_and_registry(&report, &reg, &ctx).unwrap();
    export.write_to_path(&bugs_json).unwrap();
    export.write_to_path(&bugs_jsonl).unwrap();
    let bugs_jsonl_raw = fs::read_to_string(&bugs_jsonl).unwrap();
    assert_eq!(bugs_jsonl_raw.lines().count(), 1);
    assert!(bugs_jsonl_raw.contains("\"schema_version\":\"anneal-known-bug/v1\""));
    assert!(!bugs_jsonl_raw.contains("\"op\":"));
    let bugs_json_raw = fs::read_to_string(&bugs_json).unwrap();
    assert!(bugs_json_raw.contains("\"schema\": \"anneal-known-bugs/v1\""));
    assert!(bugs_json_raw.contains("\"schema_version\": \"anneal-known-bug/v1\""));

    // Honesty gate: non-verified freshness must NEVER report
    // overall_status == "PASS".
    let mut bad_ctx = ctx.clone();
    bad_ctx.build_freshness_override = Some(BuildFreshness::FailedOrOom);
    bad_ctx.build_exit_code_override = Some(137);
    let clean_report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![],
        vec![],
    );
    let bad_detail = SemanticDetailRecord::from_report_and_registry(
        &clean_report,
        &BugRegistry::new("google/zerocopy"),
        &bad_ctx,
    )
    .unwrap();
    assert_eq!(bad_detail.overall_status, "UNVERIFIED");
    let mut forced_pass = bad_detail.clone();
    forced_pass.overall_status = "PASS".to_string();
    assert!(forced_pass.validate_honesty().is_err());
}

#[test]
fn portable_anneal_root_and_seed_corpus_dir_loader() {
    let real_root = anneal_itree_diff::workspace_anneal_root().expect("live anneal root");
    let repo_parent = real_root.parent().expect("repo parent");
    assert_eq!(
        anneal_itree_diff::resolve_anneal_root_with_env(Some(repo_parent), None, None).unwrap(),
        real_root
    );
    assert_eq!(
        anneal_itree_diff::resolve_anneal_root_with_env(None, Some(repo_parent.as_os_str()), None)
            .unwrap(),
        real_root
    );
    assert!(
        anneal_itree_diff::resolve_anneal_root_with_env(
            Some(std::path::Path::new("/nonexistent/anneal/root")),
            None,
            None
        )
        .is_err()
    );

    let tmp = tempfile::tempdir().expect("tempdir");
    assert!(anneal_itree_diff::load_fuzz_seeds_from_dir(tmp.path()).unwrap().is_empty());

    let batch = generate_fuzz_batch(0xDEAD_BEEF, 2);
    fs::write(tmp.path().join("01_single.json"), serde_json::to_string(&batch[0]).unwrap())
        .unwrap();
    fs::write(tmp.path().join("02_list.jsonl"), serde_json::to_string(&batch[1]).unwrap() + "\n")
        .unwrap();
    let loaded = anneal_itree_diff::load_fuzz_seeds_from_dir(tmp.path()).unwrap();
    assert_eq!(loaded.len(), 2);
    assert_eq!(loaded[0].id, batch[0].to_trace_test_case().id);
    assert_eq!(loaded[1].id, batch[1].to_trace_test_case().id);
}

#[test]
fn telemetry_head_build_provenance_rejects_dirty_relocated_and_stale_binaries() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let repo_root = tmp.path().join("repo");
    let anneal_root = repo_root.join("anneal");
    let crate_dir = anneal_root.join("tests/itree_diff");
    let lean_dir = anneal_root.join("trusted/lean");
    fs::create_dir_all(&crate_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(anneal_root.join("Cargo.toml"), "[workspace]\nmembers = []\nresolver = \"2\"\n")
        .unwrap();
    fs::write(lean_dir.join("lean-toolchain"), "leanprover/lean4:v4.34.1\n").unwrap();
    let src_file = crate_dir.join("lib.rs");
    fs::write(&src_file, "pub fn v() -> u32 { 1 }\n").unwrap();

    let git = |args: &[&str]| {
        let status = hermetic_git_command(&repo_root).args(args).status().unwrap();
        assert!(status.success(), "git {args:?} failed");
    };
    git(&["init", "-q"]);
    git(&["config", "user.name", "Test User"]);
    git(&["config", "user.email", "test@example.com"]);
    git(&["add", "."]);
    git(&["commit", "-q", "-m", "initial"]);

    let head_out =
        hermetic_git_command(&repo_root).args(["rev-parse", "--verify", "HEAD"]).output().unwrap();
    let head_sha = String::from_utf8(head_out.stdout).unwrap().trim().to_string();

    // Ensure the executable and `.d` file have mtime >= tracked source files.
    std::thread::sleep(Duration::from_millis(20));
    let bin_dir = tmp.path().join("out");
    fs::create_dir_all(&bin_dir).unwrap();
    let exe_path = bin_dir.join("itree-diff");
    fs::write(&exe_path, b"fake-binary").unwrap();
    let canon_exe = fs::canonicalize(&exe_path).unwrap();
    let canon_src = fs::canonicalize(&src_file).unwrap();
    fs::write(
        bin_dir.join("itree-diff.d"),
        format!("{}: {}\n", canon_exe.display(), canon_src.display()),
    )
    .unwrap();

    // 1. Unattested build (`None, None`) MUST fail closed even on a clean tree
    // with matching manifest root and fresh `.d` + executable mtimes!
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        &crate_dir,
        Some(&exe_path),
        None,
        None,
    ));
    let unattested_ctx = TelemetryContext::discover(&anneal_root);
    assert!(!unattested_ctx.head_provenance_verified);
    assert!(!unattested_ctx.is_verified_for_commit());

    // 2. Unauthenticated compile-time env vars (`ANNEAL_BUILD_COMMIT_SHA` +
    // `ANNEAL_BUILD_TREE_CLEAN="1"`) MUST fail closed even on a clean tree
    // so dirty/unrelated builds later restored cleanly cannot pass.
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        &crate_dir,
        Some(&exe_path),
        Some(&head_sha),
        Some("1"),
    ));

    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let clean_case = CaseReport {
        case_id: "clean_1".to_string(),
        category: CaseCategory::ScalarBitwise,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_val)),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let clean_rep = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![clean_case],
        vec![],
    );
    let unattested_detail = SemanticDetailRecord::from_report_and_registry(
        &clean_rep,
        &BugRegistry::new("google/zerocopy"),
        &unattested_ctx,
    )
    .unwrap();
    assert_eq!(unattested_detail.build_freshness, "stale");
    assert_eq!(unattested_detail.overall_status, "UNVERIFIED");

    // 3. Relocated or copied binary without compile-time attestation fails;
    // with matching SHA + clean="1" succeeds on clean tree, fails on wrong SHA
    // or clean!="1".
    let copied_exe = bin_dir.join("copied-itree-diff");
    fs::write(&copied_exe, b"fake-binary").unwrap();
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        Some(&copied_exe),
        None,
        None,
    ));

    // 4. Explicit unauthenticated compile-time attestation env checks fail
    // closed too.
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        Some(&copied_exe),
        Some(&head_sha),
        Some("1"),
    ));
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        Some(&copied_exe),
        Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"),
        Some("1"),
    ));
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        Some(&copied_exe),
        Some(&head_sha),
        Some("0"),
    ));

    // 5. Dirty tree (untracked file) -> rejected even with matching SHA!
    let untracked = anneal_root.join("dirty_scratch.txt");
    fs::write(&untracked, "dirty").unwrap();
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        &crate_dir,
        Some(&exe_path),
        None,
        None,
    ));
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head_sha),
        &crate_dir,
        Some(&exe_path),
        Some(&head_sha),
        Some("1"),
    ));
    fs::remove_file(&untracked).unwrap();

    // 6. Stale binary after new commit -> prior attested SHA and None rejected!
    std::thread::sleep(Duration::from_millis(20));
    fs::write(&src_file, "pub fn v() -> u32 { 2 }\n").unwrap();
    git(&["add", "."]);
    git(&["commit", "-q", "-m", "advance head"]);
    let head2_out = Command::new("git")
        .args(["-C", repo_root.to_str().unwrap(), "rev-parse", "--verify", "HEAD"])
        .output()
        .unwrap();
    let head2_sha = String::from_utf8(head2_out.stdout).unwrap().trim().to_string();
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head2_sha),
        &crate_dir,
        Some(&exe_path),
        None,
        None,
    ));
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head2_sha),
        &crate_dir,
        Some(&exe_path),
        Some(&head_sha),
        Some("1"),
    ));
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head2_sha),
        &crate_dir,
        Some(&exe_path),
        Some(&head2_sha),
        Some("1"),
    ));

    // 7. Mutating `commit_sha` away from `discovered_head_sha` invalidates
    // `is_verified_for_commit()`.
    let mut tampered_ctx = unattested_ctx;
    tampered_ctx.head_provenance_verified = true;
    tampered_ctx.discovered_head_sha = Some(head_sha.clone());
    tampered_ctx.commit_sha = head_sha;
    assert!(tampered_ctx.is_verified_for_commit());
    tampered_ctx.commit_sha = head2_sha;
    assert!(!tampered_ctx.is_verified_for_commit());
}

#[test]
fn normalize_repo_slug_strips_credentials_schemes_and_hostnames() {
    let cases = [
        ("https://github.com/google/zerocopy.git", "google/zerocopy"),
        ("https://user:ghp_secret_token_99@github.com/org/repo.git", "org/repo"),
        ("ssh://git@github.com/org/repo.git", "org/repo"),
        ("ssh://git@github.com:2222/org/repo.git/", "org/repo"),
        (
            "https://oauth2:pa/ss:word@git.example.com:8443/team/sub/my-org/my.repo.git?tok=leak#f",
            "my-org/my.repo",
        ),
        ("git@github.com:joshlf/anneal.git", "joshlf/anneal"),
        ("deploy:topsecret@host.internal:acme/widget", "acme/widget"),
        ("github.com/acme/widget.git", "acme/widget"),
        ("joshlf/anneal", "joshlf/anneal"),
        ("file:///home/alice/secret/repo.git", "google/zerocopy"),
        ("/local/path/alice/zerocopy.bundle", "google/zerocopy"),
        ("https://user:secret@github.com/", "google/zerocopy"),
        ("", "google/zerocopy"),
    ];
    for (raw, expected) in cases {
        let got = normalize_repo_slug(raw);
        assert_eq!(got, expected, "unexpected slug for {raw:?}");
        assert!(!got.contains('@') && !got.contains(':') && !got.contains("secret"));
    }
}

#[test]
fn telemetry_propagates_expectation_violation_and_executed_legs_per_slice() {
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(1),
        mem_digest: compute_boundary_mem_digest(&[]),
    };

    // Corpus case: expected UB -> host `rustc` skipped, Miri + Lean ran,
    // `mir_eval` absent. Also carries an `expectation_violation` despite
    // `TraceVerdict::Agree`.
    let corpus_ub_mismatch = CaseReport {
        case_id: "corpus_ub_1".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        verdict: TraceVerdict::Agree,
        expectation_violation: Some("Miri UB marker mismatch".to_string()),
        rustc_dual: RustcDualResult::skipped_for_ub("expected UB"),
        miri: Some(mk_auth("miri", TerminalOutcome::FaultUb { detail: "UB".to_string() })),
        lean: Some(mk_auth("lean", TerminalOutcome::FaultUb { detail: "UB".to_string() })),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };

    // Fuzz case: host `rustc` + Miri ran, Lean disabled (`None`), `mir_eval`
    // returned the unexecuted synthetic non-`CapturedRust` skip sentinel.
    let unexecuted_mir_eval = mk_auth(
        "anneal-mir-eval",
        TerminalOutcome::CaptureRefused {
            reason: "anneal-mir-eval only evaluates single-crate CapturedRust captures; multi-call/synthetic Lean AST and EnvSchedule cases are unsupported".to_string(),
        },
    );
    let fuzz_case = CaseReport {
        case_id: "fuzz_1".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::DegradedNoLean { detail: "--no-lean".to_string() },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: None,
        lean_strict_probe: None,
        mir_eval: Some(unexecuted_mir_eval),
        metamorphic: None,
    };

    let report = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "available (/bin/anneal-mir-eval)",
        LeanTraceMode::CompositionalITree,
        vec![corpus_ub_mismatch, fuzz_case],
        vec![],
    );
    assert_eq!(report.counts.expectation_mismatches, 1);

    let mut ctx = TelemetryContext {
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        branch_scope: "main".to_string(),
        exposed_on_main: true,
        commit_sha: "abcdef0123456789abcdef0123456789abcdef01".to_string(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "unit-test".to_string(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some("abcdef0123456789abcdef0123456789abcdef01".to_string()),
    };

    let detail = SemanticDetailRecord::from_report_and_registry(
        &report,
        &BugRegistry::new("google/zerocopy"),
        &ctx,
    )
    .unwrap();
    assert_eq!(detail.overall_status, "FAIL");
    assert_eq!(detail.differential_runs.len(), 2);

    let corpus_run = &detail.differential_runs[0];
    assert_eq!(corpus_run.suite, "itree_diff_corpus");
    assert_eq!(corpus_run.expectation_mismatch_count, 1);
    assert_eq!(corpus_run.overall_status, "FAIL");
    assert_eq!(
        corpus_run.legs,
        vec!["miri_tree_borrows".to_string(), "lean_compositional_itree".to_string()],
        "UB-only slice that skipped rustc_dual must not claim rustc_o0/rustc_o2 evidence"
    );

    let fuzz_run = &detail.differential_runs[1];
    assert_eq!(fuzz_run.suite, "itree_diff_fuzz");
    assert_eq!(fuzz_run.expectation_mismatch_count, 0);
    assert_eq!(fuzz_run.overall_status, "UNVERIFIED");
    assert_eq!(
        fuzz_run.legs,
        vec!["rustc_o0".to_string(), "rustc_o2".to_string(), "miri_tree_borrows".to_string()],
        "unexecuted mir_eval placeholder and disabled lean must not appear in executed legs"
    );

    let mut dishonest = detail.clone();
    dishonest.overall_status = "PASS".to_string();
    assert!(dishonest.validate_honesty().is_err());

    // When `anneal-mir-eval` genuinely executes on a CapturedRust case,
    // `anneal_mir_eval` IS reported in `legs`.
    let real_mir_eval_case = CaseReport {
        case_id: "captured_1".to_string(),
        category: CaseCategory::ScalarBitwise,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: Some(mk_auth("anneal-mir-eval", ret_val)),
        metamorphic: None,
    };
    ctx.profile_v2 = false;
    let rep_me = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "available (/bin/anneal-mir-eval)",
        LeanTraceMode::StrictVerbatim,
        vec![real_mir_eval_case],
        vec![],
    );
    let detail_me = SemanticDetailRecord::from_report_and_registry(
        &rep_me,
        &BugRegistry::new("google/zerocopy"),
        &ctx,
    )
    .unwrap();
    assert_eq!(
        detail_me.differential_runs[0].legs,
        vec![
            "rustc_o0".to_string(),
            "rustc_o2".to_string(),
            "miri_tree_borrows".to_string(),
            "lean_strict_verbatim".to_string(),
            "anneal_mir_eval".to_string(),
        ]
    );
}

#[test]
fn standalone_mir_lean_preserves_fuzz_helper_2_branch_semantics() {
    // Exercise BOTH branches of `fuzz_helper_2(a, b)`:
    // - `a >= b`: `(a - b) + 5` (with `b > 0`, strictly differs from `a + 5`!)
    // - `a < b`:  `(b - a) + 9`
    let mut prog_ge = generate_fuzz_batch(0x5150, 1)[0].clone();
    prog_ge.input_x = 20;
    prog_ge.input_y = 7;
    prog_ge.steps = vec![FuzzStep::HelperCall { callee_idx: 2, bias: 3 }];
    let lean_ge = render_standalone_mir_lean(&prog_ge, None, "deadbeefcafe");
    assert!(lean_ge.contains(".binaryOp .ge"));
    assert!(lean_ge.contains(".switchInt"));
    assert!(lean_ge.contains(".binaryOp .sub"));
    assert!(lean_ge.contains("BitVec.ofNat 128 5"));
    assert!(lean_ge.contains("BitVec.ofNat 128 9"));

    let mut prog_lt = prog_ge.clone();
    prog_lt.input_x = 2;
    prog_lt.input_y = 20;
    prog_lt.steps = vec![FuzzStep::HelperCall { callee_idx: 2, bias: 5 }];
    let lean_lt = render_standalone_mir_lean(&prog_lt, None, "cafefeed1234");

    // Extract the `reproProgram` literal from the standalone `.mir.lean`
    // bundle and run it directly through Lean + `rustc` when Lean is
    // provisioned!
    let extract_prog_expr = |src: &str| -> String {
        let start = src.find("def reproCaller : Body :=").expect("reproCaller");
        let end = src.find("def reproArgs : List Val :=").expect("reproArgs");
        let decls = &src[start..end];
        let caller_rhs = decls
            .split_once("def reproCaller : Body :=\n  ")
            .unwrap()
            .1
            .split_once("\n\ndef reproProgram : Program := ")
            .unwrap();
        let caller_expr = caller_rhs.0.trim();
        caller_rhs.1.trim().replacen("reproCaller", caller_expr, 1)
    };

    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare differential engine");
    if let Some(lean_session) = &engine.lean {
        for (label, prog, lean_bundle, buggy_val) in [
            // a = 20 + 7 = 27, b = 7 + 3 = 10 -> (27 - 10) + 5 = 22, xor
            // sentinel (20 ^ 0xA5A5 = 42417) -> 42407; old buggy `a + 5` gave
            // 32 ^ 42417 = 42385!
            ("a_ge_b", &prog_ge, &lean_ge, (27u32 + 5) ^ (20u32 ^ 0xA5A5u32)),
            // a = 2 + 20 = 22, b = 20 + 5 = 25 -> (25 - 22) + 9 = 12, xor
            // sentinel (2 ^ 0xA5A5 = 42407) -> 42411; old buggy `a + 5` gave
            // 27 ^ 42407 = 42428!
            ("a_lt_b", &prog_lt, &lean_lt, (22u32 + 5) ^ (2u32 ^ 0xA5A5u32)),
        ] {
            let base_case = prog.to_trace_test_case();
            let rustc_res = engine.rustc.run_dual(&base_case);
            assert!(rustc_res.parity_ok, "{label} rustc parity");
            let synth_case = TraceTestCase {
                id: format!("witness_lean_{label}"),
                category: CaseCategory::FuzzGenerated,
                pure_rust_source: base_case.pure_rust_source.clone(),
                traced_rust_source: base_case.traced_rust_source.clone(),
                entry_fn: "fuzz_entry".to_string(),
                rust_arg_exprs: base_case.rust_arg_exprs.clone(),
                lean_args: base_case.lean_args.clone(),
                ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
                lean_program_spec: LeanProgramSpec::SyntheticMirAst {
                    program_lean_expr: extract_prog_expr(lean_bundle),
                    external_callees: Vec::new(),
                },
                metamorphic_inlined_twin: None,
                env_schedule: EnvSchedule::default(),
                fuel: 1024,
                spine_mode: SpineCompareMode::OutcomeOnly,
                expected_class: ExpectedCaseClass::Agree,
                expected_ub: None,
                expected_conservative: None,
                disclosed_gap: None,
            };
            let (lean_res, _) =
                lean_session.run_case(&synth_case, LeanTraceMode::CompositionalITree);
            assert!(
                lean_res.tool_error.is_none(),
                "{label} Lean witness failed: {:?}",
                lean_res.tool_error
            );
            assert!(
                lean_res.outcome.semantically_eq(&rustc_res.o0.outcome),
                "{label} Lean witness outcome {:?} != rustc outcome {:?}",
                lean_res.outcome,
                rustc_res.o0.outcome
            );
            assert_ne!(
                lean_res.outcome,
                TerminalOutcome::Returned {
                    ret: TraceVal::u32(buggy_val),
                    mem_digest: match &lean_res.outcome {
                        TerminalOutcome::Returned { mem_digest, .. } => mem_digest.clone(),
                        _ => String::new(),
                    },
                },
                "{label} must not compute buggy `a + 5` result"
            );
        }
    }
}

#[test]
fn standalone_fuzz_reproducer_preserves_observable_trace_and_drop_guard() {
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Scheduled `ReturnBytes` + `HelperCall` + `PaddedRoundTrip` standalone
    // reproducer.
    let mut prog_sched = generate_fuzz_batch(0x31337, 1)[0].clone();
    prog_sched.input_x = 12;
    prog_sched.input_y = 5;
    prog_sched.steps = vec![
        FuzzStep::PaddedRoundTrip { tag_byte: 9 },
        FuzzStep::HelperCall { callee_idx: 1, bias: 4 },
    ];
    let mut sched = EnvSchedule::default();
    sched.push_callee("fuzz_helper_1", EnvAction::ReturnBytes(777u32.to_le_bytes().to_vec()));
    let src_sched = render_standalone_fuzz_repro_rs(&prog_sched, Some(&sched), "a1b2c3d4e5f6");
    assert!(src_sched.contains("mod anneal_rt"));
    assert!(src_sched.contains("live_carrier"));
    assert!(src_sched.contains("live_ptr"));
    assert!(src_sched.contains("capture_value_bytes"));
    assert!(src_sched.contains("handle_scheduled_call"));
    assert!(src_sched.contains("ScopedCallerWatchGuard::install"));

    let rs_sched = tmp.path().join("repro_sched.rs");
    let bin_sched = tmp.path().join("repro_sched_bin");
    fs::write(&rs_sched, &src_sched).unwrap();
    let comp_sched = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&rs_sched)
        .arg("-o")
        .arg(&bin_sched)
        .output()
        .unwrap();
    assert!(
        comp_sched.status.success(),
        "scheduled standalone repro compile failed:\n{}",
        String::from_utf8_lossy(&comp_sched.stderr)
    );
    let run_sched = Command::new(&bin_sched).output().unwrap();
    assert!(run_sched.status.success());
    let parsed_sched = parse_trace_json_stdout_with_expected_args(
        "standalone-repro",
        &String::from_utf8_lossy(&run_sched.stdout),
        &String::from_utf8_lossy(&run_sched.stderr),
        1,
        Some(2),
    )
    .expect("parse standalone trace JSON");
    assert!(parsed_sched.caller_frame_law.is_satisfied());
    let expected_bits = u128::from(777u32 ^ (12u32 ^ 0xA5A5u32));
    assert!(matches!(
        parsed_sched.outcome,
        TerminalOutcome::Returned { ret: TraceVal::Scalar { bits, .. }, .. } if bits == expected_bits
    ));
    assert!(parsed_sched.spine.events.iter().any(|ev| {
        matches!(ev, ObservableEvent::CallReturn { callee, ret_repr, .. } if callee == "fuzz_helper_1" && ret_repr == "777")
    }));

    // 2. Unwind + `DropGuard` standalone reproducer.
    let mut prog_unwind = prog_sched.clone();
    prog_unwind.steps = vec![
        FuzzStep::HelperCall { callee_idx: 0, bias: 2 },
        FuzzStep::UnwindProbe { trigger_unwind: true },
    ];
    let src_unwind = render_standalone_fuzz_repro_rs(&prog_unwind, None, "f6e5d4c3b2a1");
    assert!(src_unwind.contains("DropGuard_1"));
    assert!(src_unwind.contains("impl Drop for DropGuard_1"));

    let rs_unwind = tmp.path().join("repro_unwind.rs");
    let bin_unwind = tmp.path().join("repro_unwind_bin");
    fs::write(&rs_unwind, &src_unwind).unwrap();
    let comp_unwind = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&rs_unwind)
        .arg("-o")
        .arg(&bin_unwind)
        .output()
        .unwrap();
    assert!(
        comp_unwind.status.success(),
        "unwind standalone repro compile failed:\n{}",
        String::from_utf8_lossy(&comp_unwind.stderr)
    );
    let run_unwind = Command::new(&bin_unwind).output().unwrap();
    assert!(run_unwind.status.success());
    let parsed_unwind = parse_trace_json_stdout_with_expected_args(
        "standalone-unwind",
        &String::from_utf8_lossy(&run_unwind.stdout),
        &String::from_utf8_lossy(&run_unwind.stderr),
        1,
        Some(2),
    )
    .expect("parse unwind trace JSON");
    assert!(parsed_unwind.caller_frame_law.is_satisfied());
    assert!(matches!(parsed_unwind.outcome, TerminalOutcome::Unwound { .. }));
    assert!(parsed_unwind.spine.events.iter().any(|ev| {
        matches!(ev, ObservableEvent::CallUnwind { callee, .. } if callee == "fuzz_ext_unwind")
    }));
}

#[test]
fn dedup_fingerprints_minimized_authority_outcomes_not_preshrink_report() {
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(0),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let preshrink_rep = mk_ub_case_report(
        "min_fp_case",
        "Undefined Behavior: attempting a read access using <alloc1>: borrow stack forbids",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let minimized_rep = mk_ub_case_report(
        "min_fp_case",
        "Undefined Behavior: pointer dereference failed: out-of-bounds",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let sig = ShrinkFailureSignature::from_case_report(&preshrink_rep).unwrap();
    assert_eq!(sig, ShrinkFailureSignature::from_case_report(&minimized_rep).unwrap());

    let mut prog = generate_fuzz_batch(0x9090, 1)[0].clone();
    prog.input_x = 64;
    prog.input_y = 32;
    prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 10 },
        FuzzStep::ArithImm { op: FuzzArithOp::Xor, imm: 3 },
    ];
    let (witness, err) = shrink_and_build_witness_with_budget(
        "min_fp_case",
        &prog,
        &preshrink_rep.verdict,
        &sig,
        ShrinkBudget::default(),
        |cand| {
            if cand.steps.len() >= 2 { preshrink_rep.clone() } else { minimized_rep.clone() }
        },
    );
    assert!(err.is_none());
    assert!(witness.shrink.is_one_minimal);
    assert!(witness.minimized_report.is_some());

    // Even when the pre-shrink `preshrink_rep` is passed as `report`, both
    // `from_1_minimal_witness` and `BugRegistry::record_witness` MUST compute
    // the fingerprint and `BugId` from the retained minimized `CaseReport`!
    let fp_from_preshrink_arg = CanonicalBugFingerprint::from_1_minimal_witness(
        &witness,
        &preshrink_rep,
        "main",
        "mir_v1_itree",
        None,
    )
    .unwrap();
    let fp_from_min_arg = CanonicalBugFingerprint::from_1_minimal_witness(
        &witness,
        &minimized_rep,
        "main",
        "mir_v1_itree",
        None,
    )
    .unwrap();
    assert_eq!(fp_from_preshrink_arg.miri_ub_class, "pointer_or_memory_access:out_of_bounds");
    assert_eq!(fp_from_preshrink_arg, fp_from_min_arg);

    let wrong_preshrink_fp = CanonicalBugFingerprint::new(
        "main",
        "mir_v1_itree",
        fp_from_min_arg.verdict_class.clone(),
        fp_from_min_arg.mir_construct_sig.clone(),
        "pointer_or_memory_access:stacked_borrows_forbidden",
        fp_from_min_arg.lean_fault_or_accept_kind.clone(),
        fp_from_min_arg.minimized_skeleton_hash.clone(),
    );
    assert_ne!(fp_from_preshrink_arg.bug_id(), wrong_preshrink_fp.bug_id());

    let mut reg = BugRegistry::new("google/zerocopy");
    let rec = reg.record_witness(
        &witness,
        &preshrink_rep,
        "main",
        true,
        "mir_v1_itree",
        "1234567890abcdef1234567890abcdef12345678",
        None,
    );
    assert_eq!(
        witness.repro_case_id,
        WitnessBundle::from_witness(witness.clone(), None).repro_case_id
    );
    assert_eq!(
        rec,
        DedupRecordOutcome::NewBug {
            bug_id: fp_from_min_arg.bug_id(),
            repro_case_id: witness.repro_case_id.clone(),
            severity: "P0".to_string(),
        }
    );
}

#[test]
fn rustc_fast_leg_runs_miri_first_and_preserves_rustc_called_vs_inlined() {
    let ret_10 = TerminalOutcome::Returned {
        ret: TraceVal::u32(10),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ret_20 = TerminalOutcome::Returned {
        ret: TraceVal::u32(20),
        mem_digest: compute_boundary_mem_digest(&[]),
    };

    // Part A: Primary `rustc_o0_o2` with `has_miri = true` must ALWAYS run Miri
    // before `rustc`, and NEVER execute UB or Miri-error candidates natively!
    let o0_o2_rep = CaseReport {
        case_id: "o0_o2".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept {
            detail: "rustc O0 vs O2 outcome mismatch".to_string(),
        },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_10.clone()),
            o2: mk_auth("rustc-O2", ret_20.clone()),
            parity_ok: false,
            skipped_for_ub: false,
            mismatch_detail: Some("mismatch".to_string()),
        },
        miri: Some(mk_auth("miri", ret_10.clone())),
        lean: Some(mk_auth("lean", ret_10.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let o0_o2_sig = ShrinkFailureSignature::from_case_report(&o0_o2_rep).unwrap();
    assert_eq!(
        FastLegStrategy::select(&o0_o2_sig, true, true, true),
        FastLegStrategy::RustcDualFirst
    );

    let cand_prog = generate_fuzz_batch(0x1111, 1)[0].clone();
    let cand_case = cand_prog.to_trace_test_case();

    // Candidate introducing UB under Miri -> `run_rustc` must NOT be called!
    let mut rustc_calls_on_ub = 0usize;
    let ub_fast = evaluate_rustc_fast_leg(
        &cand_case,
        &o0_o2_sig,
        true,
        |_| mk_auth("miri", TerminalOutcome::FaultUb { detail: "Undefined Behavior".to_string() }),
        |_| {
            rustc_calls_on_ub += 1;
            o0_o2_rep.rustc_dual.clone()
        },
    );
    assert!(ub_fast.is_none());
    assert_eq!(rustc_calls_on_ub, 0, "native rustc must never run when Miri reports UB");

    // Candidate where Miri reports tool_error -> `run_rustc` must not run!
    let mut rustc_calls_on_err = 0usize;
    let err_fast = evaluate_rustc_fast_leg(
        &cand_case,
        &o0_o2_sig,
        true,
        |_| AuthorityRunResult::tool_error("miri", "timeout"),
        |_| {
            rustc_calls_on_err += 1;
            o0_o2_rep.rustc_dual.clone()
        },
    );
    assert!(err_fast.is_none());
    assert_eq!(rustc_calls_on_err, 0, "native rustc must never run when Miri fails to certify");

    // Part B: Sole failed relation `rustc_called_vs_inlined` where BOTH
    // `called` and `inlined` satisfy `O0 == O2` (`parity_ok == true`), while
    // `called` returns 10 and `inlined` returns 20 when `HelperCall` is
    // present and `input_x >= 16` (and `input_x == 8` introduces UB in twin!).
    let dual_10 = RustcDualResult {
        o0: mk_auth("rustc-O0", ret_10.clone()),
        o2: mk_auth("rustc-O2", ret_10.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let dual_20 = RustcDualResult {
        o0: mk_auth("rustc-O0", ret_20.clone()),
        o2: mk_auth("rustc-O2", ret_20.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let meta_detail = format!(
        "metamorphic_duality: rustc multi-call vs source-inlined mismatch: O0=({ret_10:?} vs {ret_20:?}), O2=({ret_10:?} vs {ret_20:?})"
    );
    let mk_meta_rep = |case_id: &str, diverged: bool| -> CaseReport {
        if diverged {
            CaseReport {
                case_id: case_id.to_string(),
                category: CaseCategory::FuzzGenerated,
                expected_class: ExpectedCaseClass::Agree,
                verdict: TraceVerdict::UnsoundAccept { detail: meta_detail.clone() },
                expectation_violation: None,
                rustc_dual: dual_10.clone(),
                miri: Some(mk_auth("miri", ret_10.clone())),
                lean: Some(mk_auth("lean", ret_10.clone())),
                lean_strict_probe: None,
                mir_eval: None,
                metamorphic: Some(MetamorphicDualityReceipt {
                    called_lean: mk_auth("lean-compositional-itree", ret_10.clone()),
                    inlined_lean: mk_auth("lean-strict-verbatim", ret_10.clone()),
                    inlined_rustc_parity_ok: true,
                    inlined_miri_matched: Some(true),
                    tool_error: None,
                    status: MetamorphicStatus::Failed,
                    duality_holds: false,
                    detail: meta_detail.clone(),
                    failed_relations: vec!["rustc_called_vs_inlined".to_string()],
                    twin_outcome_summary: "called_o0=returned,called_o2=returned,called_miri=returned,inlined_o0=returned,inlined_o2=returned,inlined_miri=returned,called_lean=returned,inlined_lean=returned".to_string(),
                }),
            }
        } else {
            CaseReport {
                case_id: case_id.to_string(),
                category: CaseCategory::FuzzGenerated,
                expected_class: ExpectedCaseClass::Agree,
                verdict: TraceVerdict::Agree,
                expectation_violation: None,
                rustc_dual: dual_10.clone(),
                miri: Some(mk_auth("miri", ret_10.clone())),
                lean: Some(mk_auth("lean", ret_10.clone())),
                lean_strict_probe: None,
                mir_eval: None,
                metamorphic: None,
            }
        }
    };

    let init_meta_rep = mk_meta_rep("meta_init", true);
    let meta_sig = ShrinkFailureSignature::from_case_report(&init_meta_rep).unwrap();
    assert_eq!(meta_sig.metamorphic_relations, vec!["rustc_called_vs_inlined".to_string()]);
    assert_eq!(
        FastLegStrategy::select(&meta_sig, true, true, true),
        FastLegStrategy::RustcDualFirst
    );

    let mut meta_prog = generate_fuzz_batch(0x2222, 1)[0].clone();
    meta_prog.input_x = 128;
    meta_prog.input_y = 64;
    meta_prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 9 },
        FuzzStep::BranchMix { then_imm: 3, else_imm: 5 },
        FuzzStep::HelperCall { callee_idx: 0, bias: 11 },
    ];

    let twin_ub_rustc_runs = std::cell::Cell::new(0usize);
    let (meta_witness, meta_err) = shrink_and_build_witness_two_tier_with_budget(
        "meta_called_vs_inlined",
        &meta_prog,
        &init_meta_rep.verdict,
        &meta_sig,
        ShrinkBudget::default(),
        FastLegStrategy::RustcDualFirst,
        |cand| {
            let tc = cand.to_trace_test_case();
            let has_call = cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }));
            let x = cand.input_x;
            evaluate_rustc_fast_leg(
                &tc,
                &meta_sig,
                true,
                |sub_case| {
                    // Simulate twin introducing UB at `x == 8`.
                    if sub_case.id.ends_with("__inlined_twin") && x == 8 {
                        mk_auth("miri", TerminalOutcome::FaultUb { detail: "twin UB".to_string() })
                    } else {
                        mk_auth("miri", ret_10.clone())
                    }
                },
                |sub_case| {
                    if sub_case.id.ends_with("__inlined_twin") {
                        if x == 8 {
                            twin_ub_rustc_runs.set(twin_ub_rustc_runs.get() + 1);
                        }
                        if has_call && x >= 16 { dual_20.clone() } else { dual_10.clone() }
                    } else {
                        dual_10.clone()
                    }
                },
            )
            .is_some()
        },
        |cand| {
            let has_call = cand.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }));
            mk_meta_rep("cand", has_call && cand.input_x >= 16)
        },
    );
    assert!(meta_err.is_none(), "expected clean metamorphic shrink: {meta_err:?}");
    assert_eq!(twin_ub_rustc_runs.get(), 0, "Miri must block UB twin before host rustc");
    assert!(meta_witness.shrink.converged_1_minimal);
    assert_eq!(meta_witness.shrink.minimized.input_x, 16);
    assert_eq!(meta_witness.shrink.minimized.input_y, 0);
    assert_eq!(meta_witness.shrink.minimized.steps.len(), 1);
    assert!(matches!(
        meta_witness.shrink.minimized.steps[0],
        FuzzStep::HelperCall { callee_idx: 0, bias: 0 }
    ));
}

#[test]
fn bounded_loop_handle_validation_catches_multi_iter_collisions_and_propagates_env() {
    let h0 = HandleId(0);
    let h1 = HandleId(1);
    let h2 = HandleId(2);

    // 1. Allocating the same handle across 2 loop iterations collides on
    // iteration 2!
    let loop_alloc_collision = vec![ShrinkStep::BoundedLoop {
        block_id: 1,
        iters: 2,
        induction: None,
        body: vec![ShrinkStep::Alloc { handle: h0, size: 16, align: 8, local_id: 1 }],
    }];
    assert!(!all_handles_defined_and_typed(&loop_alloc_collision, &[]));

    // 2. Consuming a pre-loop handle via `SplitAt` across 2 loop iterations
    // fails on iteration 2!
    let loop_consume_twice = vec![
        ShrinkStep::Alloc { handle: h0, size: 32, align: 8, local_id: 1 },
        ShrinkStep::BoundedLoop {
            block_id: 1,
            iters: 2,
            induction: None,
            body: vec![ShrinkStep::SplitAt {
                left: h1,
                right: h2,
                src: h0,
                mid: 8,
                len: 32,
                align: 8,
            }],
        },
    ];
    assert!(!all_handles_defined_and_typed(&loop_consume_twice, &[]));

    // 3. Branch-conditional allocation inside a 2-iteration loop collides when
    // the branch repeats!
    let loop_branch_may_collision = vec![ShrinkStep::BoundedLoop {
        block_id: 1,
        iters: 2,
        induction: None,
        body: vec![ShrinkStep::BranchMix {
            block_id: 2,
            cond_local: 0,
            taken_then: true,
            dynamic_even_cond: false,
            then_steps: vec![ShrinkStep::Alloc { handle: h0, size: 8, align: 8, local_id: 1 }],
            else_steps: vec![],
        }],
    }];
    assert!(!all_handles_defined_and_typed(&loop_branch_may_collision, &[]));

    // 4. Using a handle AFTER a 1-iteration loop that consumed it must fail!
    let use_after_loop_consume = vec![
        ShrinkStep::Alloc { handle: h0, size: 32, align: 8, local_id: 1 },
        ShrinkStep::BoundedLoop {
            block_id: 1,
            iters: 1,
            induction: None,
            body: vec![ShrinkStep::SplitAt {
                left: h1,
                right: h2,
                src: h0,
                mid: 8,
                len: 32,
                align: 8,
            }],
        },
        ShrinkStep::UseHandle { handle: h0, offset: 0, len: 8, align: 8, local_id: 2 },
    ];
    assert!(!all_handles_defined_and_typed(&use_after_loop_consume, &[]));

    // 5. Using a guaranteed post-loop handle (`h1` from 1-iteration `SplitAt`)
    // succeeds AND compiles cleanly as a standalone `ShrinkableCase`!
    let valid_post_loop_use = vec![
        ShrinkStep::Alloc { handle: h0, size: 32, align: 8, local_id: 1 },
        ShrinkStep::BoundedLoop {
            block_id: 1,
            iters: 1,
            induction: None,
            body: vec![ShrinkStep::SplitAt {
                left: h1,
                right: h2,
                src: h0,
                mid: 8,
                len: 32,
                align: 8,
            }],
        },
        ShrinkStep::UseHandle { handle: h1, offset: 0, len: 8, align: 8, local_id: 2 },
    ];
    assert!(all_handles_defined_and_typed(&valid_post_loop_use, &[]));

    let sc = ShrinkableCase {
        name: "post_loop_handle".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: vec![],
        slice_len: None,
        slice_align: 1,
        helpers: vec![],
        steps: valid_post_loop_use,
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let rs_src = render_standalone_shrinkable_repro_rs(&sc, "112233445566");
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let rs_path = tmp.path().join("repro_loop_hnd.rs");
    let bin_path = tmp.path().join("repro_loop_hnd_bin");
    fs::write(&rs_path, &rs_src).unwrap();
    let out = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&rs_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "post-loop ShrinkableCase repro failed to compile:\n{}\nsource:\n{}",
        String::from_utf8_lossy(&out.stderr),
        rs_src
    );
}

#[test]
fn itree_diff_cli_help_exposes_portable_root_corpus_and_telemetry_flags() {
    let bin = env!("CARGO_BIN_EXE_itree-diff");
    let out = Command::new(bin).arg("--help").output().expect("run itree-diff --help");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let help = String::from_utf8_lossy(&out.stdout);
    for required in [
        "--anneal-root",
        "--corpus-dir",
        "ANNEAL_CORPUS_DIR",
        "--semantics-detail-out",
        "--known-bugs-out",
        "--env-profile",
        "--witness-dir",
        "--shrink",
    ] {
        assert!(help.contains(required), "itree-diff --help missing `{required}`:\n{help}");
    }
}

#[test]
fn scb_routing_schedule_unwind_branchmix_and_telemetry_honesty_regressions() {
    // 1. SCB post-patch replay fails closed on empty buckets, removes failing
    //    witnesses from Fixed parents, routes split re-observations and unseen
    //    skeletons away from Fixed parents, and reopens Fixed buckets on
    //    regression.
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep = mk_ub_case_report(
        "scb_reg",
        "Undefined Behavior: Tree Borrows: write access through <0x10> is forbidden",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let sig = ShrinkFailureSignature::from_case_report(&rep).unwrap();
    let mut reg = BugRegistry::new("google/zerocopy");
    let mut p_base = generate_fuzz_batch(0xBADC_0FFE, 1)[0].clone();
    let mut witnesses = Vec::new();
    let mut parent_id = String::new();
    for k in 1..=3usize {
        let mut p = p_base.clone();
        p.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: k as u32 }; k];
        let mut sr =
            shrink_fuzz_program_with_budget(&p, ShrinkBudget::default(), |c| c.steps.len() == k);
        sr.succeeded = true;
        sr.is_one_minimal = true;
        sr.converged_1_minimal = true;
        let mut scb_rep = rep.clone();
        scb_rep.case_id = format!("scb_{k}");
        let w = WitnessArtifact::from_shrink(
            scb_rep.case_id.clone(),
            rep.verdict.clone(),
            rep.verdict.clone(),
            sr,
        )
        .with_signature(sig.clone())
        .with_minimized_report(scb_rep.clone());
        witnesses.push(w.clone());
        let sha = format!("{k:040x}");
        let out = reg.record_witness(&w, &scb_rep, "main", true, "mir_v1_itree", &sha, None);
        if k == 1
            && let DedupRecordOutcome::NewBug { bug_id, .. } = out
        {
            parent_id = bug_id;
        }
    }
    let skel2 = witnesses[1].minimized_skeleton_hash.clone();
    let split = reg
        .classify_post_patch_replay(&parent_id, "aaaa000000000000000000000000000000000000", |w| {
            w.minimized_skeleton_hash == skel2
        })
        .unwrap();
    let ScbReplayVerdict::Split { split_bugs, .. } = split else {
        panic!("expected Split");
    };
    let child_id = split_bugs[0].bug_id.clone();
    // Failing witness must be removed from Fixed parent's witnesses!
    assert_eq!(reg.buckets[&parent_id].status, BugStatus::Fixed);
    assert_eq!(reg.buckets[&parent_id].witnesses.len(), 2);
    assert!(
        !reg.buckets[&parent_id].witnesses.iter().any(|w| w.minimized_skeleton_hash == skel2),
        "Fixed parent must not retain split failing witnesses"
    );

    // Re-observing `witnesses[1]` (the split-off failing skeleton) must route
    // to `child_id`, leaving `parent_id` Fixed!
    let mut scb1_rep = rep.clone();
    scb1_rep.case_id = witnesses[1].case_id.clone();
    let reobs = reg.record_witness(
        &witnesses[1],
        &scb1_rep,
        "main",
        true,
        "mir_v1_itree",
        "bbbb000000000000000000000000000000000000",
        None,
    );
    assert!(
        matches!(reobs, DedupRecordOutcome::DuplicateHit { ref bug_id, hit_count: 2, .. } if bug_id == &child_id)
    );
    assert_eq!(reg.buckets[&parent_id].status, BugStatus::Fixed);
    assert_eq!(reg.buckets[&child_id].status, BugStatus::Open);

    // Observing a brand-new unseen 4th skeleton matching `parent_id` while
    // `parent_id` is split+Fixed creates an Open split child rather than
    // attaching an active failure onto Fixed parent.
    p_base.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 4 }; 4];
    let mut sr4 =
        shrink_fuzz_program_with_budget(&p_base, ShrinkBudget::default(), |c| c.steps.len() == 4);
    sr4.succeeded = true;
    sr4.is_one_minimal = true;
    sr4.converged_1_minimal = true;
    let w4 = WitnessArtifact::from_shrink("scb_4", rep.verdict.clone(), rep.verdict.clone(), sr4)
        .with_signature(sig.clone());
    let mut scb4_rep = rep.clone();
    scb4_rep.case_id = w4.case_id.clone();
    let new_child_out = reg.record_witness(
        &w4,
        &scb4_rep,
        "main",
        true,
        "mir_v1_itree",
        "cccc000000000000000000000000000000000000",
        None,
    );
    let DedupRecordOutcome::NewBug { bug_id: child4_id, .. } = new_child_out else {
        panic!("expected Open split child for unseen skeleton under split Fixed parent");
    };
    assert_eq!(reg.buckets[&child4_id].status, BugStatus::Open);
    assert_eq!(reg.buckets[&parent_id].status, BugStatus::Fixed);

    // Regression of `witnesses[0]` (one of parent's Fixed skeletons) MUST
    // reopen `parent_id` and clear `fixed_sha`!
    let mut scb0_rep = rep.clone();
    scb0_rep.case_id = witnesses[0].case_id.clone();
    let _ = reg.record_witness(
        &witnesses[0],
        &scb0_rep,
        "main",
        true,
        "mir_v1_itree",
        "dddd000000000000000000000000000000000000",
        None,
    );
    assert_eq!(reg.buckets[&parent_id].status, BugStatus::Open);
    assert!(reg.buckets[&parent_id].fixed_sha.is_empty());

    // Empty-witness replay must fail closed!
    let mut empty_reg = reg.clone();
    empty_reg.buckets.get_mut(&parent_id).unwrap().witnesses.clear();
    assert!(
        empty_reg
            .classify_post_patch_replay(
                &parent_id,
                "eeee000000000000000000000000000000000000",
                |_| false
            )
            .is_err()
    );

    // 2. `.mir.lean` faithful `fuzz_ext_unwind` trigger handling plus
    //    `Some(schedule)` honoring in `from_1_minimal_witness`,
    //    `WitnessBundle::from_witness`, and `BugRegistry::record_witness`.
    let mut uw_prog = generate_fuzz_batch(0x9911, 1)[0].clone();
    uw_prog.steps = vec![FuzzStep::UnwindProbe { trigger_unwind: true }];
    let uw_lean = render_standalone_mir_lean(&uw_prog, None, "abcd1234abcd");
    assert!(uw_lean.contains("fuzz_ext_unwind"));
    assert!(uw_lean.contains("terminator := .unsupported"));
    assert!(uw_lean.contains("reproExternalCallees : List String := [\"fuzz_ext_unwind\"]"));
    assert!(uw_lean.contains("reproEnvScheduleJson"));

    let mut custom_sched = EnvSchedule::default();
    custom_sched.push_callee("fuzz_ext_unwind", EnvAction::Abort { reason: "custom".to_string() });
    let fp_with_sched = CanonicalBugFingerprint::from_1_minimal_witness(
        &witnesses[0],
        &scb0_rep,
        "main",
        "mir_v1_itree",
        Some(&custom_sched),
    )
    .unwrap();
    let bundle_with_sched = WitnessBundle::from_witness(witnesses[0].clone(), Some(&custom_sched));
    assert_eq!(fp_with_sched.minimized_skeleton_hash, bundle_with_sched.skel_hash);
    assert_ne!(bundle_with_sched.skel_hash, witnesses[0].minimized_skeleton_hash);
    assert!(bundle_with_sched.repro_rust_source.contains("Abort"));

    let mut sched_reg = BugRegistry::new("google/zerocopy");
    let rec_sched = sched_reg.record_witness(
        &witnesses[0],
        &scb0_rep,
        "main",
        true,
        "mir_v1_itree",
        "1234000000000000000000000000000000000000",
        Some(&custom_sched),
    );
    let DedupRecordOutcome::NewBug { repro_case_id, .. } = rec_sched else {
        panic!("expected NewBug with scheduled skeleton");
    };
    assert_eq!(repro_case_id, bundle_with_sched.repro_case_id);

    // 3. Budget exhaustion (`max_evals = 1`) reports `succeeded = true`,
    //    `is_one_minimal = false`, and `budget_exhausted = true`, while
    //    `max_evals = 0` or failing initial eval reports `succeeded = false`.
    let mut fl_prog = p_base.clone();
    fl_prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 2 },
    ];
    let budget_cut_res = shrink_fuzz_program_two_tier_with_budget(
        &fl_prog,
        ShrinkBudget { max_evals: 1, max_duration: Duration::from_secs(10) },
        FastLegStrategy::MiriUbFirst,
        |_| true,
        |_| true,
    );
    assert!(budget_cut_res.succeeded);
    assert!(!budget_cut_res.is_one_minimal);
    assert!(!budget_cut_res.converged_1_minimal);
    assert!(budget_cut_res.budget_exhausted);

    let init_fail_res = shrink_fuzz_program_two_tier_with_budget(
        &fl_prog,
        ShrinkBudget::default(),
        FastLegStrategy::MiriUbFirst,
        |_| false,
        |_| false,
    );
    assert!(!init_fail_res.succeeded);
    assert!(!init_fail_res.is_one_minimal);
    assert!(!init_fail_res.budget_exhausted);

    // 4. `BranchMix` defining a shared handle across both arms and using it
    //    post-branch must compile cleanly under real `rustc`.
    let h0 = HandleId(0);
    let h1 = HandleId(1);
    let h2 = HandleId(2);
    let branch_case = ShrinkableCase {
        name: "branch_shared_handle".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: vec![],
        slice_len: None,
        slice_align: 1,
        helpers: vec![],
        steps: vec![
            ShrinkStep::Alloc { handle: h0, size: 16, align: 4, local_id: 1 },
            ShrinkStep::BranchMix {
                block_id: 1,
                cond_local: 0,
                taken_then: true,
                dynamic_even_cond: false,
                then_steps: vec![ShrinkStep::Borrow {
                    dst: h1,
                    src: h0,
                    mutable: false,
                    local_id: 2,
                }],
                else_steps: vec![ShrinkStep::Borrow {
                    dst: h1,
                    src: h0,
                    mutable: false,
                    local_id: 2,
                }],
            },
            ShrinkStep::UseHandle { handle: h1, offset: 0, len: 8, align: 4, local_id: 3 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    assert!(all_handles_defined_and_typed(&branch_case.steps, &branch_case.helpers));
    let mut bad_branch = branch_case.clone();
    bad_branch.steps.push(ShrinkStep::UseHandle {
        handle: h2,
        offset: 0,
        len: 4,
        align: 4,
        local_id: 4,
    });
    assert!(!all_handles_defined_and_typed(&bad_branch.steps, &bad_branch.helpers));

    let branch_rs = render_standalone_shrinkable_repro_rs(&branch_case, "b0b1b2b3b4b5");
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(
        anneal_root.clone(),
        Some(tmp.path().join("cache")),
    );
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let br_path = tmp.path().join("branch_shared.rs");
    let br_bin = tmp.path().join("branch_shared_bin");
    fs::write(&br_path, &branch_rs).unwrap();
    let comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&br_path)
        .arg("-o")
        .arg(&br_bin)
        .output()
        .unwrap();
    assert!(
        comp.status.success(),
        "BranchMix shared handle repro failed to compile:\n{}\n{branch_rs}",
        String::from_utf8_lossy(&comp.stderr)
    );

    // 5. Non-git fallback sets `exposed_on_main = false`, and `ToolError`
    //    alongside P0 `UnsoundAccept` preserves `overall_status == "FAIL"`.
    let non_git_ctx = TelemetryContext::discover(tmp.path());
    assert_eq!(non_git_ctx.branch, "unknown");
    assert!(!non_git_ctx.exposed_on_main);
    assert!(!non_git_ctx.is_verified_for_commit());

    let tool_err_case = CaseReport {
        case_id: "tool_err_1".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::ToolError {
            authority: "lean".to_string(),
            detail: "timed out after 60s".to_string(),
        },
        expectation_violation: None,
        rustc_dual: RustcDualResult::skipped_for_ub("err"),
        miri: Some(mk_auth("miri", ret_val)),
        lean: None,
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let mixed_report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep, tool_err_case],
        vec![],
    );
    let mixed_detail = SemanticDetailRecord::from_report_and_registry(
        &mixed_report,
        &BugRegistry::new("google/zerocopy"),
        &non_git_ctx,
    )
    .unwrap();
    assert_eq!(mixed_detail.build_freshness, "timed_out");
    assert_eq!(mixed_detail.overall_status, "FAIL");
}

#[test]
fn regression_guards_for_schedules_nesting_arith_seeds_and_split_retarget() {
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(0),
        mem_digest: compute_boundary_mem_digest(&[]),
    };

    // 1. EnvAction::ReturnBytes + global "*" + control-char escaping.
    let mut rb_sched = EnvSchedule::default();
    rb_sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![1, 2, 3, 4]));
    rb_sched.global.push_back(EnvAction::Abort { reason: "ctrl\nmsg".to_string() });
    let batch_prog = generate_fuzz_batch(0xC0DE_0001, 1).pop().unwrap();
    let lean_src = render_standalone_mir_lean(&batch_prog, Some(&rb_sched), "skelrb");
    assert!(
        lean_src.contains("return_bytes")
            && lean_src.contains("[1,2,3,4]")
            && lean_src.contains("\"*\"")
            && lean_src.contains("\\\\n"),
        "ReturnBytes, global '*', & Lean escapes must appear:\n{lean_src}"
    );

    // 2. Render ShrinkableCase ArithImm ops directly onto dst_local.
    let arith_case = ShrinkableCase {
        name: "arith_ops".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput {
            local_id: 0,
            width: IntKind::U32,
            value: 100,
            align_hint: None,
        }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Sub, imm: 30 },
            ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Xor, imm: 0x55 },
            ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::BitAndMask, imm: 7 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let arith_rs = render_standalone_shrinkable_repro_rs(&arith_case, "arith01");
    assert!(arith_rs.contains("l0.wrapping_sub"));
    assert!(arith_rs.contains("l0 ^"));
    assert!(arith_rs.contains("0xFFFFu128"));
    let bin_dir = tempfile::tempdir().expect("bin dir");
    let rs_path = bin_dir.path().join("arith.rs");
    let exe_path = bin_dir.path().join("arith_bin");
    fs::write(&rs_path, &arith_rs).unwrap();
    let arith_root = workspace_anneal_root().expect("locate anneal root");
    let mut arith_cfg =
        DifferentialConfig::for_workspace_with_cache(arith_root, Some(bin_dir.path().join("c")));
    arith_cfg.enable_miri = false;
    arith_cfg.enable_lean = false;
    let arith_engine = DifferentialEngine::prepare(arith_cfg).expect("prepare engine");
    let compiled = Command::new(&arith_engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&rs_path)
        .arg("-o")
        .arg(&exe_path)
        .output()
        .expect("rustc compile");
    assert!(compiled.status.success(), "{}", String::from_utf8_lossy(&compiled.stderr));

    // 3. Recursive shrink strips removable grandchildren inside nested blocks.
    let decoy = ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 999 };
    let nested_case = ShrinkableCase {
        name: "nested".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 7, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::DropGuardWrapper {
            local_id: 0,
            body: vec![ShrinkStep::BranchMix {
                block_id: 1,
                cond_local: 0,
                taken_then: true,
                dynamic_even_cond: false,
                then_steps: vec![ShrinkStep::BoundedLoop {
                    block_id: 2,
                    iters: 2,
                    induction: None,
                    body: vec![
                        ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 },
                        decoy,
                    ],
                }],
                else_steps: vec![ShrinkStep::ArithImm {
                    dst_local: 0,
                    op: FuzzArithOp::Add,
                    imm: 2,
                }],
            }],
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let min_nested = shrink_case_two_tier_with_budget(
        &nested_case,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        |c| {
            // Keep the DropGuard + BranchMix + BoundedLoop wrapper when
            // forced, requiring Add(1) inside the nested loop while
            // DropGuard/else/decoy can collapse/prune selectively.
            fn has_add_one(steps: &[ShrinkStep]) -> bool {
                steps.iter().any(|s| match s {
                    ShrinkStep::ArithImm { imm: 1, .. } => true,
                    ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                        has_add_one(then_steps) || has_add_one(else_steps)
                    }
                    ShrinkStep::BoundedLoop { body, .. }
                    | ShrinkStep::DropGuardWrapper { body, .. }
                    | ShrinkStep::IfFalseDecoy { body, .. } => has_add_one(body),
                    _ => false,
                })
            }
            let wrapped = matches!(
                c.steps.as_slice(),
                [ShrinkStep::BranchMix { .. }] | [ShrinkStep::DropGuardWrapper { .. }]
            );
            wrapped && has_add_one(&c.steps)
        },
    );
    assert!(min_nested.is_one_minimal);
    let min_text = format!("{:?}", min_nested.minimized.steps);
    assert!(!min_text.contains("999"), "nested decoy must be stripped: {min_text}");
    assert!(!min_text.contains("BoundedLoop"), "nested loop must collapse: {min_text}");
    assert!(!min_text.contains("DropGuardWrapper"), "outer wrapper must collapse: {min_text}");

    // 4. Symlink rejection in load_fuzz_seeds_from_dir + --corpus-dir --shrink
    let sdir = tempfile::tempdir().expect("seed dir");
    let w_cli_dir = tempfile::tempdir().expect("cli witness dir");
    let rep_cli_dir = tempfile::tempdir().expect("cli report dir");
    let cli_rep = rep_cli_dir.path().join("rep.json");
    let seed_ok = generate_fuzz_batch(0xC0DE_0002, 1).pop().unwrap();
    fs::write(sdir.path().join("seed.json"), serde_json::to_string(&seed_ok).unwrap()).unwrap();
    assert!(
        anneal_itree_diff::validate_cli_run_plan_with_corpus_dir(
            false, true, None, None, true, true
        )
        .is_ok()
    );
    let cli_seed_out = Command::new(env!("CARGO_BIN_EXE_itree-diff"))
        .args([
            "--corpus-dir",
            sdir.path().to_str().unwrap(),
            "--shrink",
            "--witness-dir",
            w_cli_dir.path().to_str().unwrap(),
            "--no-miri",
            "--no-lean",
            "--json-report",
            cli_rep.to_str().unwrap(),
        ])
        .output()
        .expect("run --corpus-dir --shrink CLI");
    assert!(
        cli_seed_out.status.success(),
        "--corpus-dir --shrink CLI failed: {}",
        String::from_utf8_lossy(&cli_seed_out.stderr)
    );
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(
            sdir.path().join("seed.json"),
            sdir.path().join("bad_link.json"),
        )
        .unwrap();
        assert!(anneal_itree_diff::load_fuzz_seeds_from_dir(sdir.path()).is_err());
        fs::remove_file(sdir.path().join("bad_link.json")).unwrap();
    }

    // 5. Fixed bucket reopens on all-failing replay & retargets on split.
    let p_a = FuzzProgram {
        seed: 1,
        index: 0,
        input_x: 0,
        input_y: 1,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let mut p_b = p_a.clone();
    p_b.steps.push(FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 });
    let sig = ShrinkFailureSignature::from_case_report(&mk_ub_case_report(
        "sig_base",
        "signed arithmetic overflow",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    ))
    .unwrap();
    let build_w = |p: &FuzzProgram, id: &str| {
        let s = shrink_fuzz_program_two_tier_with_budget(
            p,
            ShrinkBudget::default(),
            FastLegStrategy::FullFourWay,
            |_| true,
            |cand| cand.steps == p.steps && cand.input_x == p.input_x && cand.input_y == p.input_y,
        );
        WitnessArtifact::from_shrink(
            id.to_string(),
            TraceVerdict::UnsoundAccept {
                detail: "miri detected UB while lean accepted".to_string(),
            },
            TraceVerdict::UnsoundAccept {
                detail: "miri detected UB while lean accepted".to_string(),
            },
            s,
        )
        .with_signature(sig.clone())
    };
    let w_a = build_w(&p_a, "w_a");
    let w_b = build_w(&p_b, "w_b");
    assert_ne!(w_a.minimized_skeleton_hash, w_b.minimized_skeleton_hash);
    let rep_a = mk_ub_case_report(
        "w_a",
        "signed arithmetic overflow",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let rep_b = mk_ub_case_report(
        "w_b",
        "signed arithmetic overflow",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let mut reg = BugRegistry::new("google/zerocopy");
    let sha_a = "1".repeat(40);
    let sha_b = "2".repeat(40);
    let sha_c = "3".repeat(40);
    let sha_d = "4".repeat(40);
    let bid_a = match reg.record_witness(&w_a, &rep_a, "main", true, "mir_v1", &sha_a, None) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    match reg.record_witness(&w_b, &rep_b, "main", true, "mir_v1", &sha_b, None) {
        DedupRecordOutcome::NewSkeletonAttached { bug_id, .. } => assert_eq!(bug_id, bid_a),
        other => panic!("expected NewSkeletonAttached in same bucket: {other:?}"),
    }
    // Mixed replay: primary w_a still fails, w_b fixed -> parent marked fixed
    // and must retarget repro_case_id/primary_fingerprint away from w_a!
    let split_v = reg
        .classify_post_patch_replay(&bid_a, &sha_c, |w| {
            w.minimized_skeleton_hash == w_a.minimized_skeleton_hash
        })
        .unwrap();
    assert!(matches!(split_v, ScbReplayVerdict::Split { .. }));
    let parent_after_split = reg.buckets.get(&bid_a).unwrap();
    assert_eq!(parent_after_split.status, BugStatus::Fixed);
    assert_eq!(parent_after_split.witnesses.len(), 1);
    assert_eq!(
        parent_after_split.repro_case_id, parent_after_split.witnesses[0].repro_case_id,
        "fixed parent must retarget repro_case_id to retained passing witness"
    );
    assert_eq!(
        parent_after_split.primary_fingerprint, parent_after_split.witnesses[0].fingerprint,
        "fixed parent must retarget primary_fingerprint"
    );
    // Subsequent all-fail replay on the Fixed parent must reopen it!
    let reopen_v = reg.classify_post_patch_replay(&bid_a, &sha_d, |_| true).unwrap();
    assert!(matches!(reopen_v, ScbReplayVerdict::StillOpen { .. }));
    let parent_reopened = reg.buckets.get(&bid_a).unwrap();
    assert_eq!(parent_reopened.status, BugStatus::Open);
    assert!(parent_reopened.fixed_sha.is_empty());

    // 6. Full-pool (K=8) Fixed bucket keeps 9th failing witness on reopen.
    let mut full_reg = BugRegistry::new("google/zerocopy");
    let mut pool_ws = Vec::new();
    let mut pool_id = String::new();
    for i in 0..9usize {
        let mut pw = p_a.clone();
        pw.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }; i + 1];
        let w = build_w(&pw, &format!("pool_{i}"));
        pool_ws.push(w);
    }
    for (i, w) in pool_ws.iter().take(8).enumerate() {
        let rep = mk_ub_case_report(
            &w.case_id,
            "signed arithmetic overflow",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(0),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
            TraceVerdict::UnsoundAccept {
                detail: "miri detected UB while lean accepted".to_string(),
            },
        );
        let pool_sha = format!("{:040x}", 0x5550usize + i);
        let out = full_reg.record_witness(w, &rep, "main", true, "mir_v1", &pool_sha, None);
        if i == 0
            && let DedupRecordOutcome::NewBug { bug_id, .. } = out
        {
            pool_id = bug_id;
        }
    }
    assert!(matches!(
        full_reg.classify_post_patch_replay(&pool_id, &"6".repeat(40), |_| false).unwrap(),
        ScbReplayVerdict::AllFixed { .. }
    ));
    let w9 = &pool_ws[8];
    let rep9 = mk_ub_case_report(
        "pool_8",
        "signed arithmetic overflow",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(0),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    assert!(matches!(
        full_reg.record_witness(w9, &rep9, "main", true, "mir_v1", &"7".repeat(40), None),
        DedupRecordOutcome::NewSkeletonAttached { retained_count: 8, .. }
    ));
    let full_after = full_reg.classify_post_patch_replay(&pool_id, &"8".repeat(40), |w| {
        w.minimized_skeleton_hash == w9.minimized_skeleton_hash
    });
    assert!(matches!(full_after.unwrap(), ScbReplayVerdict::Split { .. }));

    // 7. Re-splitting a split child with shared 6-hex prefix avoids overwrite.
    let mut prefix_reg = BugRegistry::new("google/zerocopy");
    let mut p_pass = p_a.clone();
    p_pass.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
        FuzzStep::ArithImm { op: FuzzArithOp::Sub, imm: 1 },
    ];
    let w_pass = build_w(&p_pass, "w_pass");
    let mut seen_skel6: std::collections::HashMap<String, (FuzzProgram, String)> =
        std::collections::HashMap::new();
    let mut pair_opt = None;
    for code in 1..65_535u32 {
        let has_add = (code & 0xFFFF) != 0xFFFF;
        let has_sub = (code & 0xFFFF) != 0;
        if !has_add || !has_sub {
            continue;
        }
        let mut p = p_a.clone();
        p.steps = (0..16)
            .map(|k| FuzzStep::ArithImm {
                op: if (code >> k) & 1 == 0 { FuzzArithOp::Add } else { FuzzArithOp::Sub },
                imm: 1,
            })
            .collect();
        let skel = canonical_fuzz_program_skeleton_hash(&p, None);
        let skel6 = skel[..6].to_string();
        if let Some((prev_p, prev_skel)) = seen_skel6.get(&skel6) {
            if prev_skel != &skel {
                pair_opt = Some((prev_p.clone(), p));
                break;
            }
        } else {
            seen_skel6.insert(skel6, (p, skel));
        }
    }
    let (p_same6_a, p_same6_b) = pair_opt.expect("found 6-hex skeleton prefix collision");
    let w_same6_a = build_w(&p_same6_a, "w_same6_a");
    let w_same6_b = build_w(&p_same6_b, "w_same6_b");
    let pass_skel = w_pass.minimized_skeleton_hash.clone();
    let same6_b_skel = w_same6_b.minimized_skeleton_hash.clone();
    assert_eq!(&w_same6_a.minimized_skeleton_hash[..6], &same6_b_skel[..6]);
    assert_ne!(w_same6_a.minimized_skeleton_hash, same6_b_skel);
    assert_ne!(&pass_skel[..6], &same6_b_skel[..6]);
    let mut rep_pass = rep_a.clone();
    rep_pass.case_id = w_pass.case_id.clone();
    let mut rep_same6_a = rep_b.clone();
    rep_same6_a.case_id = w_same6_a.case_id.clone();
    let mut rep_same6_b = rep_b.clone();
    rep_same6_b.case_id = w_same6_b.case_id.clone();
    let pfx_sha1 = format!("{:040x}", 0xaaaa111usize);
    let pfx_sha2 = format!("{:040x}", 0xaaaa222usize);
    let pfx_sha3 = format!("{:040x}", 0xbbbb111usize);
    let pfx_sha4 = format!("{:040x}", 0xbbbb222usize);
    let pfx_sha5 = format!("{:040x}", 0xcccc111usize);
    let prefix_root = match prefix_reg
        .record_witness(&w_pass, &rep_pass, "main", true, "mir_v1", &pfx_sha1, None)
    {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected root bug: {other:?}"),
    };
    let _ = prefix_reg.record_witness(
        &w_same6_a,
        &rep_same6_a,
        "main",
        true,
        "mir_v1",
        &pfx_sha2,
        None,
    );
    let first_split = prefix_reg
        .classify_post_patch_replay(&prefix_root, &pfx_sha3, |w| {
            w.minimized_skeleton_hash != pass_skel
        })
        .unwrap();
    let ScbReplayVerdict::Split { split_bugs: sb1, .. } = first_split else {
        panic!("expected first split");
    };
    let child_id = sb1[0].bug_id.clone();
    assert_eq!(prefix_reg.buckets[&child_id].witnesses.len(), 1);
    assert_eq!(prefix_reg.buckets[&child_id].status, BugStatus::Open);

    // Distinct skeleton sharing the 6-hex prefix with an Open split child must
    // isolate into a full-12-hex bucket rather than conflating into `child_id`.
    let sibling_b_id = match prefix_reg.record_witness(
        &w_same6_b,
        &rep_same6_b,
        "main",
        true,
        "mir_v1",
        &pfx_sha4,
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected isolated sibling NewBug for prefix collision, got {other:?}"),
    };
    assert_ne!(sibling_b_id, child_id);
    assert!(sibling_b_id.ends_with(&same6_b_skel), "sibling_b_id={sibling_b_id}");
    assert_eq!(prefix_reg.buckets[&child_id].witnesses.len(), 1);
    assert_eq!(prefix_reg.buckets[&child_id].status, BugStatus::Open);
    let routed_b = prefix_reg.record_witness(
        &w_same6_b,
        &rep_same6_b,
        "main",
        true,
        "mir_v1",
        &pfx_sha5,
        None,
    );
    assert!(
        matches!(routed_b, DedupRecordOutcome::DuplicateHit { ref bug_id, .. } if bug_id == &sibling_b_id)
    );

    // Distinct skeleton sharing the 6-hex prefix with a Fixed single-generation
    // split child must also isolate without reopening the Fixed child, while
    // re-observing the child's exact skeleton still reopens `child_id`.
    let mut fixed_prefix_reg = BugRegistry::new("google/zerocopy");
    let fix_sha1 = format!("{:040x}", 0x1111aaausize);
    let fix_sha2 = format!("{:040x}", 0x2222aaausize);
    let fix_sha3 = format!("{:040x}", 0x3333aaausize);
    let fix_sha4 = format!("{:040x}", 0x4444aaausize);
    let fix_sha5 = format!("{:040x}", 0x5555aaausize);
    let fix_sha6 = format!("{:040x}", 0x6666aaausize);
    let fixed_root = match fixed_prefix_reg
        .record_witness(&w_pass, &rep_pass, "main", true, "mir_v1", &fix_sha1, None)
    {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected root bug: {other:?}"),
    };
    let _ = fixed_prefix_reg.record_witness(
        &w_same6_a,
        &rep_same6_a,
        "main",
        true,
        "mir_v1",
        &fix_sha2,
        None,
    );
    let ScbReplayVerdict::Split { split_bugs: fixed_sb, .. } = fixed_prefix_reg
        .classify_post_patch_replay(&fixed_root, &fix_sha3, |w| {
            w.minimized_skeleton_hash != pass_skel
        })
        .unwrap()
    else {
        panic!("expected split on fixed_prefix_reg");
    };
    let fixed_child_id = fixed_sb[0].bug_id.clone();
    assert!(matches!(
        fixed_prefix_reg.classify_post_patch_replay(&fixed_child_id, &fix_sha4, |_| false).unwrap(),
        ScbReplayVerdict::AllFixed { .. }
    ));
    assert_eq!(fixed_prefix_reg.buckets[&fixed_child_id].status, BugStatus::Fixed);

    let isolated_after_fix = match fixed_prefix_reg.record_witness(
        &w_same6_b,
        &rep_same6_b,
        "main",
        true,
        "mir_v1",
        &fix_sha5,
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected isolated NewBug against Fixed prefix child, got {other:?}"),
    };
    assert_ne!(isolated_after_fix, fixed_child_id);
    assert!(isolated_after_fix.ends_with(&same6_b_skel));
    assert_eq!(fixed_prefix_reg.buckets[&fixed_child_id].status, BugStatus::Fixed);
    assert_eq!(fixed_prefix_reg.buckets[&fixed_child_id].fixed_sha, fix_sha4);

    let reopened_exact = fixed_prefix_reg.record_witness(
        &w_same6_a,
        &rep_same6_a,
        "main",
        true,
        "mir_v1",
        &fix_sha6,
        None,
    );
    assert!(matches!(
        reopened_exact,
        DedupRecordOutcome::DuplicateHit { ref bug_id, .. }
            if bug_id == &fixed_child_id
    ));
    assert_eq!(fixed_prefix_reg.buckets[&fixed_child_id].status, BugStatus::Open);
    assert!(fixed_prefix_reg.buckets[&fixed_child_id].fixed_sha.is_empty());
}

#[test]
fn shrink_scalar_recursion_and_scb_multigeneration_split() {
    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. Pass 5 recurses into nested DropGuardWrapper / BranchMix /
    //    BoundedLoop / IfFalseDecoy and shrinks HelperCall.bias,
    //    BoundedLoop.iters (>= 2), PaddedRoundTrip.tag_byte, and
    //    ShrinkHelper.{multiplier, addend}.
    let nested_scalar_case = ShrinkableCase {
        name: "nested_scalar".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 9, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 7,
            multiplier: 512,
            addend: 256,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::DropGuardWrapper {
                local_id: 0,
                body: vec![ShrinkStep::BranchMix {
                    block_id: 1,
                    cond_local: 0,
                    taken_then: true,
                    dynamic_even_cond: false,
                    then_steps: vec![
                        ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1000 },
                        ShrinkStep::BoundedLoop {
                            block_id: 2,
                            iters: 5,
                            induction: None,
                            body: vec![ShrinkStep::ArithImm {
                                dst_local: 0,
                                op: FuzzArithOp::Add,
                                imm: 777,
                            }],
                        },
                    ],
                    else_steps: vec![ShrinkStep::ArithImm {
                        dst_local: 0,
                        op: FuzzArithOp::Add,
                        imm: 888,
                    }],
                }],
            },
            ShrinkStep::HelperCall {
                dst_local: 0,
                helper_id: 7,
                block_id: 3,
                bias: 999,
                rhs_local: None,
            },
            ShrinkStep::PaddedRoundTrip { local_id: 0, tag_byte: 250 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let scalar_res = shrink_case_two_tier_with_budget(
        &nested_scalar_case,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        |c| {
            // Force wrapper + BranchMix + >=2-iter loop + HelperCall +
            // PaddedRoundTrip to survive Pass 3 so Pass 5 minimizes nested
            // and scalar fields.
            matches!(
                c.steps.as_slice(),
                [
                    ShrinkStep::DropGuardWrapper { body: dg_body, .. },
                    ShrinkStep::HelperCall { .. },
                    ShrinkStep::PaddedRoundTrip { tag_byte, .. },
                ] if *tag_byte >= 3 && matches!(
                    dg_body.as_slice(),
                    [ShrinkStep::BranchMix { then_steps, else_steps, .. }]
                    if !else_steps.is_empty() && matches!(
                        then_steps.as_slice(),
                        [
                            ShrinkStep::ArithImm { imm, .. },
                            ShrinkStep::BoundedLoop { iters, body: lp_body, .. }
                        ] if *imm >= 16 && *iters >= 2 && matches!(
                            lp_body.as_slice(),
                            [ShrinkStep::ArithImm { imm: lp_imm, .. }] if *lp_imm >= 8
                        )
                    )
                )
            ) && c.helpers.first().is_some_and(|h| h.multiplier >= 4 && h.addend >= 2)
        },
    );
    assert!(scalar_res.succeeded && scalar_res.is_one_minimal);
    let min_sc = &scalar_res.minimized;
    assert_eq!(min_sc.helpers[0].multiplier, 4);
    assert_eq!(min_sc.helpers[0].addend, 2);
    let ShrinkStep::DropGuardWrapper { body: dg_body, .. } = &min_sc.steps[0] else {
        panic!("expected DropGuardWrapper: {:?}", min_sc.steps);
    };
    let ShrinkStep::BranchMix { then_steps, else_steps, .. } = &dg_body[0] else {
        panic!("expected BranchMix: {dg_body:?}");
    };
    assert!(matches!(then_steps[0], ShrinkStep::ArithImm { imm: 16, .. }));
    assert!(matches!(
        &then_steps[1],
        ShrinkStep::BoundedLoop { iters: 2, body, .. }
        if matches!(body.as_slice(), [ShrinkStep::ArithImm { imm: 8, .. }])
    ));
    assert!(matches!(else_steps[0], ShrinkStep::ArithImm { imm: 0, .. }));
    assert!(matches!(min_sc.steps[1], ShrinkStep::HelperCall { bias: 0, .. }));
    assert!(matches!(min_sc.steps[2], ShrinkStep::PaddedRoundTrip { tag_byte: 3, .. }));

    // 2. Real memory/slice/volatile operations in
    //    `render_standalone_shrinkable_repro_rs`.
    let h0 = HandleId(0);
    let h1 = HandleId(1);
    let h2 = HandleId(2);
    let h3 = HandleId(3);
    let real_mem_case = ShrinkableCase {
        name: "real_mem_ops".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::Alloc { handle: h0, size: 32, align: 8, local_id: 1 },
            ShrinkStep::Borrow { dst: h1, src: h0, mutable: false, local_id: 2 },
            ShrinkStep::SplitAt { left: h2, right: h3, src: h1, mid: 8, len: 32, align: 8 },
            ShrinkStep::UseHandle { handle: h2, offset: 0, len: 8, align: 8, local_id: 3 },
            ShrinkStep::UseHandle { handle: h3, offset: 8, len: 8, align: 8, local_id: 4 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let mem_src = render_standalone_shrinkable_repro_rs(&real_mem_case, "mem01_abcd");
    assert!(mem_src.contains("std::alloc::alloc_zeroed"));
    assert!(mem_src.contains("std::slice::from_raw_parts"));
    assert!(mem_src.contains("get_unchecked"));
    assert!(mem_src.contains("core::ptr::read_volatile"));
    let mem_rs = tmp.path().join("real_mem.rs");
    let mem_bin = tmp.path().join("real_mem_bin");
    fs::write(&mem_rs, &mem_src).unwrap();
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let mem_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&mem_rs)
        .arg("-o")
        .arg(&mem_bin)
        .output()
        .unwrap();
    assert!(mem_comp.status.success(), "{}", String::from_utf8_lossy(&mem_comp.stderr));
    let mem_run = Command::new(&mem_bin).output().unwrap();
    assert!(mem_run.status.success(), "valid real_mem binary failed: {mem_run:?}");

    // 3. `resolve_anneal_root_with_env` prefers relocated cwd checkout over
    //    compile-time manifest.
    let reloc_repo = tmp.path().join("relocated_repo");
    let reloc_anneal = reloc_repo.join("anneal");
    let reloc_subdir = reloc_anneal.join("tests/itree_diff");
    fs::create_dir_all(reloc_anneal.join("trusted/lean")).unwrap();
    fs::create_dir_all(&reloc_subdir).unwrap();
    fs::write(reloc_anneal.join("Cargo.toml"), "[workspace]\nmembers = []\nresolver = \"2\"\n")
        .unwrap();
    fs::write(reloc_anneal.join("trusted/lean/lean-toolchain"), "leanprover/lean4:v4.34.1\n")
        .unwrap();
    assert_eq!(
        anneal_itree_diff::resolve_anneal_root_with_env(None, None, Some(&reloc_subdir)).unwrap(),
        fs::canonicalize(&reloc_anneal).unwrap()
    );

    // 4. Value-only metamorphic divergences classify under
    //    `value_mismatch_count`, while fault/UB or CallerFrameLaw metamorphic
    //    failures stay in `unsound_missed_fault_count`.
    let ret_10 = TerminalOutcome::Returned {
        ret: TraceVal::u32(10),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ret_20 = TerminalOutcome::Returned {
        ret: TraceVal::u32(20),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let dual_ok = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_10.clone()),
        o2: mk_auth("rustc-o2", ret_10.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let mut meta_val_rep = mk_ub_case_report("meta_val", "", ret_10.clone(), TraceVerdict::Agree);
    meta_val_rep.rustc_dual = dual_ok;
    meta_val_rep.miri = Some(mk_auth("miri", ret_10.clone()));
    meta_val_rep.lean = Some(mk_auth("lean-compositional-itree", ret_20));
    meta_val_rep.verdict = TraceVerdict::UnsoundAccept {
        detail: "metamorphic_duality: lean_called_vs_inlined mismatch (ret=20 vs 10)".to_string(),
    };
    meta_val_rep.metamorphic = Some(MetamorphicDualityReceipt {
        called_lean: mk_auth("lean-compositional-itree", ret_10.clone()),
        inlined_lean: mk_auth("lean-strict-verbatim", ret_10.clone()),
        inlined_rustc_parity_ok: true,
        inlined_miri_matched: Some(true),
        tool_error: None,
        status: MetamorphicStatus::Failed,
        duality_holds: false,
        detail: "Lean multi-call vs source-inlined outcome mismatch: Returned(20) vs Returned(10)"
            .to_string(),
        failed_relations: vec!["lean_called_vs_inlined".to_string()],
        twin_outcome_summary: "called_lean=returned,inlined_lean=returned".to_string(),
    });
    let val_report = DifferentialReport::from_cases(
        "available",
        false,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![meta_val_rep],
        Vec::new(),
    );
    let val_detail = SemanticDetailRecord::from_report_and_registry(
        &val_report,
        &BugRegistry::new("google/zerocopy"),
        &TelemetryContext::discover(tmp.path()),
    )
    .unwrap();
    assert_eq!(val_detail.differential_runs[0].value_mismatch_count, 1);
    assert_eq!(val_detail.differential_runs[0].unsound_missed_fault_count, 0);

    // 5. Metamorphic fuzz reproducer emits BOTH `mod subject` and
    //    `mod subject_inlined`, compiles & succeeds when matching, and panics
    //    loudly when diverging.
    let meta_prog = generate_fuzz_batch(0xC0DE_1234, 1).pop().unwrap();
    let mut meta_case = meta_prog.to_trace_test_case();
    assert!(meta_case.metamorphic_inlined_twin.is_some());
    let dual_repro = render_standalone_fuzz_repro_rs(&meta_prog, None, "meta1234");
    assert!(dual_repro.contains("mod subject_inlined"));
    assert!(dual_repro.contains("ANNEAL_ITREE_INLINED_TWIN_JSON:"));
    let ok_twin_rs = tmp.path().join("meta_ok.rs");
    let ok_twin_bin = tmp.path().join("meta_ok_bin");
    fs::write(&ok_twin_rs, &dual_repro).unwrap();
    let ok_twin_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&ok_twin_rs)
        .arg("-o")
        .arg(&ok_twin_bin)
        .output()
        .unwrap();
    assert!(ok_twin_comp.status.success(), "{}", String::from_utf8_lossy(&ok_twin_comp.stderr));
    let ok_twin_run = Command::new(&ok_twin_bin).output().unwrap();
    assert!(ok_twin_run.status.success(), "matching metamorphic repro must exit 0");

    let twin_mut = meta_case.metamorphic_inlined_twin.as_mut().unwrap();
    twin_mut.pure_rust_source = format!(
        "#![no_std]\npub fn {}(a: u32, b: u32) -> u32 {{ a ^ b ^ 0xFFFF_FFFFu32 }}\n",
        twin_mut.entry_fn
    );
    let div_harness = render_standalone_metamorphic_rust_harness(&meta_case);
    let div_rs = tmp.path().join("meta_div.rs");
    let div_bin = tmp.path().join("meta_div_bin");
    fs::write(
        &div_rs,
        format!("#![allow(dead_code, unused_variables, unused_mut)]\n{div_harness}"),
    )
    .unwrap();
    let div_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&div_rs)
        .arg("-o")
        .arg(&div_bin)
        .output()
        .unwrap();
    assert!(div_comp.status.success(), "{}", String::from_utf8_lossy(&div_comp.stderr));
    let div_run = Command::new(&div_bin).output().unwrap();
    assert!(!div_run.status.success(), "diverging metamorphic twin harness must panic loudly");

    // 6. Identical skeletons with different constants or signatures get
    //    distinct `bundle_id`, `repro_case_id`, and non-clobbering files while
    //    retaining equal `skel_hash`.
    let p_c1 = FuzzProgram {
        seed: 10,
        index: 0,
        input_x: 1,
        input_y: 2,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 }],
        applied_mutators: Vec::new(),
    };
    let mut p_c2 = p_c1.clone();
    p_c2.steps[0] = FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 9 };
    let sr_c1 = shrink_fuzz_program_with_budget(&p_c1, ShrinkBudget::default(), |p| {
        p.steps == p_c1.steps && p.input_x == p_c1.input_x && p.input_y == p_c1.input_y
    });
    let sr_c2 = shrink_fuzz_program_with_budget(&p_c2, ShrinkBudget::default(), |p| {
        p.steps == p_c2.steps && p.input_x == p_c2.input_x && p.input_y == p_c2.input_y
    });
    let ub_rep = mk_ub_case_report(
        "skel_collision",
        "signed arithmetic overflow",
        ret_10,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let sig_ub = ShrinkFailureSignature::from_case_report(&ub_rep).unwrap();
    let mut ub_rep_c1 = ub_rep.clone();
    ub_rep_c1.case_id = "c1".to_string();
    let mut ub_rep_c2 = ub_rep.clone();
    ub_rep_c2.case_id = "c2".to_string();
    let w1 =
        WitnessArtifact::from_shrink("c1", ub_rep.verdict.clone(), ub_rep.verdict.clone(), sr_c1)
            .with_signature(sig_ub.clone())
            .with_minimized_report(ub_rep_c1);
    let w2 =
        WitnessArtifact::from_shrink("c2", ub_rep.verdict.clone(), ub_rep.verdict.clone(), sr_c2)
            .with_signature(sig_ub.clone())
            .with_minimized_report(ub_rep_c2);
    assert_eq!(w1.minimized_skeleton_hash, w2.minimized_skeleton_hash);
    assert_ne!(w1.repro_case_id, w2.repro_case_id);
    let b1 = WitnessBundle::from_witness(w1.clone(), None);
    let b2 = WitnessBundle::from_witness(w2.clone(), None);
    assert_eq!(b1.skel_hash, b2.skel_hash);
    assert_ne!(b1.bundle_id, b2.bundle_id);
    let wdir = tmp.path().join("witnesses_disjoint");
    let paths1 = b1.write_to_dir(&wdir).unwrap();
    let paths2 = b2.write_to_dir(&wdir).unwrap();
    assert_ne!(paths1.repro_rs_path, paths2.repro_rs_path);
    assert_ne!(paths1.mir_lean_path, paths2.mir_lean_path);
    assert_ne!(paths1.witness_json_path, paths2.witness_json_path);
    assert!(paths1.repro_rs_path.is_file() && paths2.repro_rs_path.is_file());
    assert_ne!(
        canonical_witness_artifact_id(&b1.skel_hash, &p_c1, None, Some(&sig_ub), &ub_rep.verdict),
        canonical_witness_artifact_id(&b1.skel_hash, &p_c1, None, None, &TraceVerdict::Agree),
    );
    assert_eq!(
        canonical_shrinkable_artifact_id("abcd", &nested_scalar_case, &sig_ub),
        canonical_shrinkable_artifact_id("abcd", &nested_scalar_case, &sig_ub)
    );
}

#[test]
fn shrink_metamorphic_mir_lean_and_dual_authority_dedup() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };

    // 1. Standalone `.mir.lean` emits `reproInlinedCaller`,
    //    `reproInlinedProgram`, and `reproInlinedRustSource` when non-unwinding
    //    metamorphic twin exists, omits it on unwinding programs, and executes
    //    identically to `reproProgram` in live Lean `StrictVerbatim`.
    let meta_prog = FuzzProgram {
        seed: 0x55AA,
        index: 3,
        input_x: 19,
        input_y: 8,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::BitAndMask, imm: 5 },
            FuzzStep::HelperCall { callee_idx: 0, bias: 2 },
            FuzzStep::HelperCall { callee_idx: 1, bias: 4 },
            FuzzStep::HelperCall { callee_idx: 2, bias: 1 },
            FuzzStep::BranchMix { then_imm: 3, else_imm: 9 },
            FuzzStep::BoundedLoop { iters: 2, step_imm: 3 },
            FuzzStep::PaddedRoundTrip { tag_byte: 11 },
            FuzzStep::UnwindProbe { trigger_unwind: false },
        ],
        applied_mutators: Vec::new(),
    };
    let lean_meta_bundle = render_standalone_mir_lean(&meta_prog, None, "meta55aa");
    assert!(lean_meta_bundle.contains("def reproInlinedCaller : Body :="));
    assert!(lean_meta_bundle.contains("def reproInlinedProgram : Program :="));
    assert!(lean_meta_bundle.contains("def reproInlinedRustSource : String :="));
    assert!(lean_meta_bundle.contains("#check reproInlinedProgram"));

    let mut unwind_prog = meta_prog.clone();
    unwind_prog.steps.push(FuzzStep::UnwindProbe { trigger_unwind: true });
    let lean_uw_bundle = render_standalone_mir_lean(&unwind_prog, None, "uw55aa");
    assert!(!lean_uw_bundle.contains("reproInlinedProgram"));

    let inlined_start = lean_meta_bundle.find("def reproInlinedCaller : Body :=\n  ").unwrap();
    let inlined_tail = &lean_meta_bundle[inlined_start..];
    let inlined_body_block = inlined_tail
        .split_once("def reproInlinedCaller : Body :=\n  ")
        .unwrap()
        .1
        .split_once("\n\ndef reproInlinedProgram : Program := ")
        .unwrap();
    let inlined_prog_rhs = inlined_body_block
        .1
        .split_once("\n\ndef reproInlinedRustSource : String := ")
        .unwrap()
        .0
        .trim()
        .replacen("reproInlinedCaller", inlined_body_block.0.trim(), 1);

    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    if let Some(lean_session) = &engine.lean {
        let called_case = meta_prog.to_trace_test_case();
        let (called_lean, _) =
            lean_session.run_case(&called_case, LeanTraceMode::CompositionalITree);
        assert!(called_lean.tool_error.is_none(), "{:?}", called_lean.tool_error);
        let inlined_case = TraceTestCase {
            id: "r5_inlined_prog".to_string(),
            category: CaseCategory::FuzzGenerated,
            pure_rust_source: called_case
                .metamorphic_inlined_twin
                .as_ref()
                .unwrap()
                .pure_rust_source
                .clone(),
            traced_rust_source: None,
            entry_fn: "fuzz_entry_inlined".to_string(),
            rust_arg_exprs: called_case.rust_arg_exprs.clone(),
            lean_args: called_case.lean_args.clone(),
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::SyntheticMirAst {
                program_lean_expr: inlined_prog_rhs,
                external_callees: Vec::new(),
            },
            metamorphic_inlined_twin: None,
            env_schedule: EnvSchedule::default(),
            fuel: 1024,
            spine_mode: SpineCompareMode::OutcomeOnly,
            expected_class: ExpectedCaseClass::Agree,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        };
        let (inlined_lean, _) = lean_session.run_case(&inlined_case, LeanTraceMode::StrictVerbatim);
        assert!(inlined_lean.tool_error.is_none(), "{:?}", inlined_lean.tool_error);
        assert_eq!(called_lean.outcome, inlined_lean.outcome);
    }

    // 2. Reopening a `Fixed` bucket retargets `repro_case_id`,
    //    `primary_fingerprint`, `summary`, `severity`, `witness_polarity`,
    //    and `KnownBugRecord` across both duplicate- and new-skeleton paths.
    let p_old = FuzzProgram {
        seed: 701,
        index: 0,
        input_x: 1,
        input_y: 2,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 }],
        applied_mutators: Vec::new(),
    };
    let mut p_same_skel_new_const = p_old.clone();
    p_same_skel_new_const.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 9 }];
    let mut p_new_skel = p_old.clone();
    p_new_skel.steps.push(FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 3 });

    let mk_shrink_w = |p: &FuzzProgram, id: &str, verdict: TraceVerdict| {
        let s = shrink_fuzz_program_two_tier_with_budget(
            p,
            ShrinkBudget::default(),
            FastLegStrategy::FullFourWay,
            |_| true,
            |c| c.steps == p.steps && c.input_x == p.input_x && c.input_y == p.input_y,
        );
        WitnessArtifact::from_shrink(id, verdict.clone(), verdict, s)
    };
    let rep_same = mk_ub_case_report(
        "same_skel_w",
        "signed arithmetic overflow",
        ret_ok,
        TraceVerdict::UnsoundAccept {
            detail: "miri detected UB while lean accepted (reopened same skel)".to_string(),
        },
    );
    let sig_p0 = ShrinkFailureSignature::from_case_report(&rep_same).unwrap();
    let w_same = mk_shrink_w(
        &p_same_skel_new_const,
        "same_skel_w",
        TraceVerdict::UnsoundAccept {
            detail: "miri detected UB while lean accepted (reopened same skel)".to_string(),
        },
    )
    .with_signature(sig_p0.clone());

    let mut reg_dup = BugRegistry::new("google/zerocopy");
    let w1_dup = mk_shrink_w(
        &p_old,
        "old_const_w",
        TraceVerdict::UnsoundAccept {
            detail: "miri detected UB while lean accepted (reopened same skel)".to_string(),
        },
    )
    .with_signature(sig_p0.clone());
    assert_eq!(w1_dup.minimized_skeleton_hash, w_same.minimized_skeleton_hash);
    assert_ne!(w1_dup.repro_case_id, w_same.repro_case_id);
    let mut rep_old_dup = rep_same.clone();
    rep_old_dup.case_id = w1_dup.case_id.clone();
    let bid_dup = match reg_dup.record_witness(
        &w1_dup,
        &rep_old_dup,
        "main",
        true,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    let old_summary = reg_dup.buckets[&bid_dup].summary.clone();

    let mut w2_dup = w_same.clone();
    w2_dup.shrink.predicate_evaluations = 77;
    let expected_dup_repro_id = w2_dup.repro_case_id.clone();
    reg_dup
        .classify_post_patch_replay(&bid_dup, "2222222222222222222222222222222222222222", |_| false)
        .unwrap();
    assert_eq!(reg_dup.buckets[&bid_dup].status, BugStatus::Fixed);
    let _ = reg_dup.record_witness(
        &w2_dup,
        &rep_same,
        "main",
        true,
        "mir_v1_itree",
        "3333333333333333333333333333333333333333",
        None,
    );
    let reopened = &reg_dup.buckets[&bid_dup];
    assert_eq!(reopened.status, BugStatus::Open);
    assert!(reopened.fixed_sha.is_empty());
    assert_eq!(reopened.repro_case_id, expected_dup_repro_id);
    assert_ne!(reopened.summary, old_summary);
    assert!(reopened.summary.contains("evals=77"));
    assert_eq!(reopened.witnesses[0].repro_case_id, expected_dup_repro_id);
    assert_eq!(reopened.to_known_bug_record().unwrap().repro_case_id, expected_dup_repro_id);

    reg_dup
        .classify_post_patch_replay(&bid_dup, "3434343434343434343434343434343434343434", |_| false)
        .unwrap();
    assert_eq!(reg_dup.buckets[&bid_dup].status, BugStatus::Fixed);
    let w_new_skel = mk_shrink_w(
        &p_new_skel,
        "new_skel_w",
        TraceVerdict::UnsoundAccept {
            detail: "miri detected UB while lean accepted (reopened new skel)".to_string(),
        },
    )
    .with_signature(sig_p0);
    let new_skel_repro_id = w_new_skel.repro_case_id.clone();
    assert_ne!(new_skel_repro_id, expected_dup_repro_id);
    let mut rep_new_skel = rep_same.clone();
    rep_new_skel.case_id = w_new_skel.case_id.clone();
    rep_new_skel.verdict = w_new_skel.verdict.clone();
    let _ = reg_dup.record_witness(
        &w_new_skel,
        &rep_new_skel,
        "main",
        true,
        "mir_v1_itree",
        "3535353535353535353535353535353535353535",
        None,
    );
    let reopened_new_skel = &reg_dup.buckets[&bid_dup];
    assert_eq!(reopened_new_skel.status, BugStatus::Open);
    assert!(reopened_new_skel.fixed_sha.is_empty());
    assert_eq!(reopened_new_skel.repro_case_id, new_skel_repro_id);
    assert_eq!(reopened_new_skel.severity, "P0");
    assert_eq!(reopened_new_skel.to_known_bug_record().unwrap().repro_case_id, new_skel_repro_id);

    // 3. `ShrinkStep::PaddedRoundTrip` renders a real `ReproPadded` layout
    //    operation (`offset_of!` + volatile field reads) that compiles and
    //    executes cleanly under `rustc`.
    let pad_case = ShrinkableCase {
        name: "padded_roundtrip_repro".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 42, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::PaddedRoundTrip { local_id: 0, tag_byte: 17 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let pad_src = render_standalone_shrinkable_repro_rs(&pad_case, "pad01_abcd");
    assert!(pad_src.contains("struct ReproPadded"));
    assert!(pad_src.contains("core::mem::offset_of!(ReproPadded, tag)"));
    assert!(pad_src.contains("core::mem::offset_of!(ReproPadded, payload)"));
    assert!(pad_src.contains("core::ptr::read_volatile"));
    let pad_rs = tmp.path().join("pad_repro.rs");
    let pad_bin = tmp.path().join("pad_repro_bin");
    fs::write(&pad_rs, &pad_src).unwrap();
    let pad_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&pad_rs)
        .arg("-o")
        .arg(&pad_bin)
        .output()
        .unwrap();
    assert!(pad_comp.status.success(), "{}", String::from_utf8_lossy(&pad_comp.stderr));
    let pad_run = Command::new(&pad_bin).output().unwrap();
    assert!(pad_run.status.success(), "padded roundtrip binary failed: {pad_run:?}");

    // 4. Duplicate corpus `case_id` rejection + non-masking provisional
    //    accounting across two colliding `case_id` instances.
    let dup_dir = tmp.path().join("dup_corpus");
    fs::create_dir_all(&dup_dir).unwrap();
    fs::write(dup_dir.join("a.json"), serde_json::to_string(&p_old).unwrap()).unwrap();
    fs::write(dup_dir.join("b.json"), serde_json::to_string(&p_same_skel_new_const).unwrap())
        .unwrap();
    let dup_err = anneal_itree_diff::load_fuzz_programs_from_dir(&dup_dir).unwrap_err();
    assert!(dup_err.contains("duplicate corpus FuzzProgram case_id"), "{dup_err}");

    let rep_conv = rep_same.clone();
    let rep_budget_cut = CaseReport {
        case_id: "same_skel_w".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept {
            detail: "missed; secondary shrink-witness tool error: budget exhausted".to_string(),
        },
        expectation_violation: None,
        rustc_dual: rep_same.rustc_dual.clone(),
        miri: rep_same.miri.clone(),
        lean: rep_same.lean.clone(),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let w_conv = w_same.clone().with_minimized_report(rep_conv.clone());
    let mut rec_reg = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut rec_reg,
        &[rep_conv.clone(), rep_budget_cut.clone()],
        &[w_conv.clone().with_report_index(0)],
        "main",
        true,
        "mir_v1_itree",
        "4444444444444444444444444444444444444444",
    );
    assert_eq!(rec_reg.buckets.len(), 1);
    assert_eq!(
        rec_reg.provisional_cases.len(),
        1,
        "colliding converged witness must not suppress second unshrunk provisional failure"
    );

    // Legacy `report_index: None` fallback must still leave 1 provisional.
    let mut rec_reg_fallback = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut rec_reg_fallback,
        &[rep_conv, rep_budget_cut.clone()],
        &[w_conv],
        "main",
        true,
        "mir_v1_itree",
        "4444444444444444444444444444444444444444",
    );
    assert_eq!(rec_reg_fallback.buckets.len(), 1);
    assert_eq!(rec_reg_fallback.provisional_cases.len(), 1);

    // 5. `.jsonl`/`.ndjson` known-bugs exports preserve `alpha_notice`,
    //    `commit_sha`, `build_freshness`, `build_exit_code`, and
    //    `provisional_count` on both non-empty and empty/all-provisional runs.
    let rep_for_export = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep_same],
        vec![w_same],
    );
    let mut ctx_stale = TelemetryContext {
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        branch_scope: "main".to_string(),
        exposed_on_main: true,
        commit_sha: "5555555555555555555555555555555555555555".to_string(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "unit-test".to_string(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::Stale),
        build_exit_code_override: Some(0),
        head_provenance_verified: false,
        discovered_head_sha: Some("5555555555555555555555555555555555555555".to_string()),
    };
    let non_empty_jsonl = tmp.path().join("non_empty_bugs.jsonl");
    KnownBugsExport::from_report_and_registry(&rep_for_export, &rec_reg, &ctx_stale)
        .unwrap()
        .write_to_path(&non_empty_jsonl)
        .unwrap();
    let ne_raw = fs::read_to_string(&non_empty_jsonl).unwrap();
    assert_eq!(ne_raw.lines().count(), 1);
    let ne_val: serde_json::Value = serde_json::from_str(ne_raw.trim()).unwrap();
    assert_eq!(ne_val["schema_version"], KNOWN_BUG_RECORD_SCHEMA);
    assert_eq!(ne_val["alpha_notice"], ALPHA_BANNER_DEFAULT);
    assert_eq!(ne_val["commit_sha"], "5555555555555555555555555555555555555555");
    assert_eq!(ne_val["build_freshness"], "stale");
    assert_eq!(ne_val["build_exit_code"], 0);
    assert_eq!(ne_val["provisional_count"], 1);

    let mut only_prov_reg = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut only_prov_reg,
        &[rep_budget_cut],
        &[],
        "main",
        true,
        "mir_v1_itree",
        "5555555555555555555555555555555555555555",
    );
    ctx_stale.build_freshness_override = Some(BuildFreshness::FailedOrOom);
    ctx_stale.build_exit_code_override = Some(137);
    let empty_ndjson = tmp.path().join("only_provisional.ndjson");
    KnownBugsExport::from_report_and_registry(&rep_for_export, &only_prov_reg, &ctx_stale)
        .unwrap()
        .write_to_path(&empty_ndjson)
        .unwrap();
    let em_raw = fs::read_to_string(&empty_ndjson).unwrap();
    assert_eq!(em_raw.lines().count(), 1);
    let em_val: serde_json::Value = serde_json::from_str(em_raw.trim()).unwrap();
    assert_eq!(em_val["schema"], "anneal-known-bugs/v1");
    assert_eq!(em_val["alpha_notice"], ALPHA_BANNER_DEFAULT);
    assert_eq!(em_val["build_freshness"], "failed_or_oom");
    assert_eq!(em_val["build_exit_code"], 137);
    assert_eq!(em_val["provisional_count"], 1);
}

#[test]
fn shrink_schedule_winding_asymmetric_branches_and_metamorphic_slugs() {
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Wrapping arithmetic reproducers advertise and pass under
    //    `--edition 2024 -C overflow-checks=no -C debug-assertions=no` (O0/O2).
    let wrap_prog = FuzzProgram {
        seed: 901,
        index: 0,
        input_x: 0,
        input_y: 0,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Sub, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let wrap_src = render_standalone_fuzz_repro_rs(&wrap_prog, None, "wrap01_abcd");
    assert!(wrap_src.contains(
        "// Compile (O0): rustc --edition 2024 -C overflow-checks=no -C debug-assertions=no"
    ));
    assert!(wrap_src.contains(
        "// Compile (O2): rustc --edition 2024 -C opt-level=2 -C overflow-checks=no -C debug-assertions=no"
    ));
    let wrap_rs = tmp.path().join("wrap_repro.rs");
    fs::write(&wrap_rs, &wrap_src).unwrap();
    for (tag, extra) in [("o0", vec![]), ("o2", vec!["-C", "opt-level=2"])] {
        let bin = tmp.path().join(format!("wrap_bin_{tag}"));
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
            .args(&extra)
            .arg(&wrap_rs)
            .arg("-o")
            .arg(&bin)
            .output()
            .unwrap();
        assert!(
            comp.status.success(),
            "{tag} compile failed: {}",
            String::from_utf8_lossy(&comp.stderr)
        );
        let run = Command::new(&bin).output().unwrap();
        assert!(
            run.status.success(),
            "{tag} wrapping twin panicked unexpectedly: stderr={}",
            String::from_utf8_lossy(&run.stderr)
        );
    }

    // 2. Undeclared locals on PaddedRoundTrip / DropGuardWrapper /
    //    PairOffsetLen + real DropGuard + real memory ops + EnvSchedule
    //    (unwind & abort) all compile and execute cleanly.
    let mut unwind_sched = EnvSchedule::default();
    unwind_sched.push_callee("fuzz_ext_unwind", EnvAction::Unwind { message: "u_r6".to_string() });
    let mut wave2_case = ShrinkableCase {
        name: "wave2_undeclared_locals_and_sched".to_string(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 1, width: IntKind::U32, value: 11, align_hint: None },
            ShrinkInput { local_id: 2, width: IntKind::U32, value: 22, align_hint: None },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::PaddedRoundTrip { local_id: 3, tag_byte: 9 },
            ShrinkStep::DropGuardWrapper {
                local_id: 4,
                body: vec![
                    ShrinkStep::PairOffsetLen { offset: 8, len: 16, align: 8, local_id: 5 },
                    ShrinkStep::UnwindProbe {
                        callee: "fuzz_ext_unwind".to_string(),
                        dst_local: 0,
                        trigger_unwind: false,
                        block_id: 1,
                    },
                ],
            },
        ],
        env_schedule: unwind_sched,
        return_local: 0,
    };
    let w2_src = render_standalone_shrinkable_repro_rs(&wave2_case, "w2_sched_abcd");
    assert!(w2_src.contains("Compile (O0): rustc --edition 2024 -C overflow-checks=no"));
    assert!(w2_src.contains("struct ReproDropGuard_"));
    assert!(w2_src.contains("_repro_pool.alloc(_pair_total_"));
    assert!(w2_src.contains("std::slice::from_raw_parts(_pair_ptr_"));
    assert!(w2_src.contains("ZstAlign8"));
    assert!(w2_src.contains("anneal_rt::handle_scheduled_call"));
    let w2_rs = tmp.path().join("w2_unwind_repro.rs");
    let w2_bin = tmp.path().join("w2_unwind_bin");
    fs::write(&w2_rs, &w2_src).unwrap();
    let w2_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&w2_rs)
        .arg("-o")
        .arg(&w2_bin)
        .output()
        .unwrap();
    assert!(w2_comp.status.success(), "{}", String::from_utf8_lossy(&w2_comp.stderr));
    let w2_run = Command::new(&w2_bin).output().unwrap();
    assert!(w2_run.status.success(), "w2 unwind repro failed: {w2_run:?}");
    let w2_parsed = parse_trace_json_stdout_with_expected_args(
        "repro",
        &String::from_utf8_lossy(&w2_run.stdout),
        &String::from_utf8_lossy(&w2_run.stderr),
        1,
        Some(2),
    )
    .expect("scheduled unwind trace must parse cleanly");
    assert!(
        matches!(w2_parsed.outcome, TerminalOutcome::Unwound { .. }),
        "{:?}",
        w2_parsed.outcome
    );

    let mut abort_sched = EnvSchedule::default();
    abort_sched.push_callee("fuzz_ext_unwind", EnvAction::Abort { reason: "halt_r6".to_string() });
    wave2_case.env_schedule = abort_sched;
    let ab_src = render_standalone_shrinkable_repro_rs(&wave2_case, "w2_abort_abcd");
    let ab_rs = tmp.path().join("w2_abort_repro.rs");
    let ab_bin = tmp.path().join("w2_abort_bin");
    fs::write(&ab_rs, &ab_src).unwrap();
    let ab_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&ab_rs)
        .arg("-o")
        .arg(&ab_bin)
        .output()
        .unwrap();
    assert!(ab_comp.status.success(), "{}", String::from_utf8_lossy(&ab_comp.stderr));
    let ab_run = Command::new(&ab_bin).output().unwrap();
    assert!(!ab_run.status.success(), "scheduled abort binary must abort abnormally");
    let ab_parsed = parse_pre_abort_stdout_with_expected_args(
        "repro",
        &String::from_utf8_lossy(&ab_run.stdout),
        &String::from_utf8_lossy(&ab_run.stderr),
        1,
        Some(2),
    )
    .expect("scheduled abort pre-abort line must parse cleanly");
    assert!(
        matches!(ab_parsed.outcome, TerminalOutcome::Aborted { .. }),
        "{:?}",
        ab_parsed.outcome
    );

    // 3. Asymmetric `BranchMix` handle def-use propagation (`taken_then`
    //    selects post-branch state; untaken arm stays structurally validated).
    let h0 = HandleId(0);
    let h1 = HandleId(1);
    let h_missing = HandleId(99);
    let asym_ok = vec![
        ShrinkStep::Alloc { handle: h0, size: 16, align: 4, local_id: 1 },
        ShrinkStep::BranchMix {
            block_id: 1,
            cond_local: 0,
            taken_then: true,
            dynamic_even_cond: false,
            then_steps: vec![ShrinkStep::Borrow { dst: h1, src: h0, mutable: false, local_id: 2 }],
            else_steps: Vec::new(),
        },
        ShrinkStep::UseHandle { handle: h1, offset: 0, len: 8, align: 4, local_id: 3 },
    ];
    assert!(all_handles_defined_and_typed(&asym_ok, &[]));
    let asym_wrong_arm = vec![
        ShrinkStep::Alloc { handle: h0, size: 16, align: 4, local_id: 1 },
        ShrinkStep::BranchMix {
            block_id: 1,
            cond_local: 0,
            taken_then: false,
            dynamic_even_cond: false,
            then_steps: vec![ShrinkStep::Borrow { dst: h1, src: h0, mutable: false, local_id: 2 }],
            else_steps: Vec::new(),
        },
        ShrinkStep::UseHandle { handle: h1, offset: 0, len: 8, align: 4, local_id: 3 },
    ];
    assert!(!all_handles_defined_and_typed(&asym_wrong_arm, &[]));
    let asym_bad_untaken = vec![
        ShrinkStep::Alloc { handle: h0, size: 16, align: 4, local_id: 1 },
        ShrinkStep::BranchMix {
            block_id: 1,
            cond_local: 0,
            taken_then: true,
            dynamic_even_cond: false,
            then_steps: vec![ShrinkStep::Borrow { dst: h1, src: h0, mutable: false, local_id: 2 }],
            else_steps: vec![ShrinkStep::UseHandle {
                handle: h_missing,
                offset: 0,
                len: 4,
                align: 4,
                local_id: 4,
            }],
        },
        ShrinkStep::UseHandle { handle: h1, offset: 0, len: 8, align: 4, local_id: 3 },
    ];
    assert!(!all_handles_defined_and_typed(&asym_bad_untaken, &[]));

    // 4. `metamorphic_leg_kinds` separates primary BugIds when only twin
    //    authority outcomes differ.
    let mut sig_meta_a = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "metamorphic_duality",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".to_string(),
        metamorphic_relations: vec!["lean_called_vs_inlined".to_string()],
        metamorphic_leg_kinds: "called_lean=returned,inlined_lean=returned".to_string(),
        spine_relation: None,
    };
    let mut sig_meta_b = sig_meta_a.clone();
    sig_meta_b.metamorphic_leg_kinds = "called_lean=returned,inlined_lean=fault_ub".to_string();
    assert_ne!(derive_verdict_class(&sig_meta_a), derive_verdict_class(&sig_meta_b));
    let fp_meta_a = CanonicalBugFingerprint::from_shrinkable_case(
        &wave2_case,
        &sig_meta_a,
        None,
        None,
        None,
        "main",
        "mir_v1_itree",
    );
    let fp_meta_b = CanonicalBugFingerprint::from_shrinkable_case(
        &wave2_case,
        &sig_meta_b,
        None,
        None,
        None,
        "main",
        "mir_v1_itree",
    );
    assert_ne!(fp_meta_a.bug_id(), fp_meta_b.bug_id());

    // Empty `metamorphic_leg_kinds` preserves the relation-only verdict class.
    sig_meta_a.metamorphic_leg_kinds.clear();
    assert_eq!(
        derive_verdict_class(&sig_meta_a),
        "unsound_accept:metamorphic_duality:lean_called_vs_inlined"
    );

    // 5. `normalize_repo_slug` / `try_normalize_repo_slug` reject multi-segment
    //    relative local paths while preserving exact two-segment slugs and URL
    //    hosts.
    assert_eq!(normalize_repo_slug("work/customer/private.git"), "google/zerocopy");
    assert_eq!(normalize_repo_slug("sub/org/repo"), "google/zerocopy");
    assert_eq!(normalize_repo_slug("org/repo.git"), "org/repo");
    assert_eq!(normalize_repo_slug("https://github.com/google/zerocopy.git"), "google/zerocopy");
    assert!(try_normalize_repo_slug("work/customer/private.git").is_err());
    assert!(try_normalize_repo_slug("sub/org/repo").is_err());
    assert!(try_normalize_repo_slug("file:///tmp/private.git").is_err());
    assert!(try_normalize_repo_slug("").is_err());
    assert_eq!(try_normalize_repo_slug("org/repo.git").unwrap(), "org/repo");
    assert_eq!(
        try_normalize_repo_slug("https://github.com/google/zerocopy.git").unwrap(),
        "google/zerocopy"
    );
}

#[test]
fn shrink_bundle_and_provenance_regressions() {
    let tmp = tempfile::tempdir().unwrap();
    let rustc =
        anneal_itree_diff::rustc_runner::RustcRunner::discover(None).ok().map(|r| r.rustc_bin);

    // 1. `canonical_alpha_renamed` remaps `env_schedule.per_callee` helper
    //    keys (`hN`, `fuzz_helper_N`) alongside `HelperCall::helper_id`.
    let mut sched_remap = EnvSchedule::default();
    sched_remap.push_callee("fuzz_helper_7", EnvAction::ReturnBytes(vec![5, 0, 0, 0]));
    sched_remap.push_callee("h9", EnvAction::ReturnBytes(vec![7, 0, 0, 0]));
    sched_remap.push_callee("ext_other", EnvAction::Unwind { message: "u".into() });
    let sc_remap = ShrinkableCase {
        name: "remap".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 2, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![
            ShrinkHelper {
                helper_id: 9,
                multiplier: 1,
                addend: 2,
                op: ShrinkHelperOp::AffineMulAdd,
            },
            ShrinkHelper {
                helper_id: 7,
                multiplier: 3,
                addend: 4,
                op: ShrinkHelperOp::AffineMulAdd,
            },
        ],
        steps: vec![
            ShrinkStep::HelperCall {
                dst_local: 2,
                helper_id: 7,
                block_id: 5,
                bias: 1,
                rhs_local: None,
            },
            ShrinkStep::HelperCall {
                dst_local: 2,
                helper_id: 9,
                block_id: 6,
                bias: 2,
                rhs_local: None,
            },
        ],
        env_schedule: sched_remap,
        return_local: 2,
    };
    let alpha = sc_remap.canonical_alpha_renamed();
    assert!(alpha.env_schedule.per_callee.contains_key("fuzz_helper_0"));
    assert!(alpha.env_schedule.per_callee.contains_key("h1"));
    assert!(alpha.env_schedule.per_callee.contains_key("ext_other"));
    assert!(!alpha.env_schedule.per_callee.contains_key("fuzz_helper_7"));
    assert!(!alpha.env_schedule.per_callee.contains_key("h9"));
    let mut alpha_helpers_only = alpha.clone();
    alpha_helpers_only.env_schedule.per_callee.remove("ext_other");
    let alpha_rs = render_standalone_shrinkable_repro_rs(&alpha_helpers_only, "alpha_sched");
    let orphan_rs = render_standalone_shrinkable_repro_rs(&alpha, "alpha_sched_orphan");
    assert!(alpha_rs.contains("anneal_rt::remaining_schedule_count()"));
    if let Some(rustc_bin) = &rustc {
        for (tag, src, expected_outcome) in [
            ("alpha_remapped_ok", &alpha_rs, "\"outcome_kind\":\"returned\""),
            ("alpha_orphan_uncons", &orphan_rs, "\"outcome_kind\":\"unconsumed_schedule\""),
        ] {
            let rs_p = tmp.path().join(format!("{tag}.rs"));
            let bin_p = tmp.path().join(format!("{tag}_bin"));
            fs::write(&rs_p, src).unwrap();
            let comp = Command::new(rustc_bin)
                .args(["--edition", "2024", "-C", "overflow-checks=no"])
                .arg(&rs_p)
                .arg("-o")
                .arg(&bin_p)
                .output()
                .unwrap();
            assert!(
                comp.status.success(),
                "{tag} compile failed: {}",
                String::from_utf8_lossy(&comp.stderr)
            );
            let run = Command::new(&bin_p).output().unwrap();
            assert!(
                run.status.success(),
                "{tag} run failed: {}",
                String::from_utf8_lossy(&run.stderr)
            );
            let stdout = String::from_utf8_lossy(&run.stdout);
            assert!(stdout.contains(expected_outcome), "{tag} stdout={stdout}");
        }
    }

    // 2. Pass 4 narrows `scalar_width` and each `ShrinkInput` width
    //    independently on heterogeneous typed inputs.
    let het_case = ShrinkableCase {
        name: "het".into(),
        scalar_width: IntKind::U64,
        inputs: vec![
            ShrinkInput { local_id: 0, width: IntKind::U128, value: 9, align_hint: None },
            ShrinkInput { local_id: 1, width: IntKind::U8, value: 3, align_hint: None },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let het_res = shrink_case_two_tier_with_budget(
        &het_case,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |c: &ShrinkableCase| {
            c.inputs.len() >= 2 && c.inputs[1].width == IntKind::U8 && !c.steps.is_empty()
        },
        |c: &ShrinkableCase| {
            c.inputs.len() >= 2 && c.inputs[1].width == IntKind::U8 && !c.steps.is_empty()
        },
    );
    assert!(het_res.succeeded);
    assert_eq!(het_res.minimized.scalar_width, IntKind::U8);
    assert_eq!(het_res.minimized.inputs[0].width, IntKind::U8);
    assert_eq!(het_res.minimized.inputs[1].width, IntKind::U8);

    // 3. Zero-sized allocation preserves alignment (`>= 8`), and
    //    `DropGuardWrapper` observes post-body mutated locals (`Cell::set`
    //    synced across normal exit and unwind).
    let zst_drop_case = ShrinkableCase {
        name: "zst_drop".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 10, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::Alloc { handle: HandleId(0), size: 0, align: 8, local_id: 0 },
            ShrinkStep::UseHandle { handle: HandleId(0), offset: 0, len: 0, align: 8, local_id: 0 },
            ShrinkStep::DropGuardWrapper {
                local_id: 0,
                body: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 5 }],
            },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let zst_drop_rs = render_standalone_shrinkable_repro_rs(&zst_drop_case, "zst_drop_ok");
    assert!(zst_drop_rs.contains("core::ptr::without_provenance_mut(align_p2)"));
    assert!(zst_drop_rs.contains("core::cell::Cell::new(l0)"));
    assert!(zst_drop_rs.contains("_drop_cell_"));
    assert!(zst_drop_rs.contains(".set(l0)"));
    if let Some(rustc_bin) = &rustc {
        let rs = tmp.path().join("zst_drop.rs");
        let bin = tmp.path().join("zst_drop_bin");
        fs::write(&rs, &zst_drop_rs).unwrap();
        let comp = Command::new(rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .arg(&rs)
            .arg("-o")
            .arg(&bin)
            .output()
            .unwrap();
        assert!(
            comp.status.success(),
            "zst_drop compile failed: {}",
            String::from_utf8_lossy(&comp.stderr)
        );
        let run = Command::new(&bin).output().unwrap();
        assert!(run.status.success(), "zst_drop failed: {}", String::from_utf8_lossy(&run.stderr));
    }

    // 4. `WitnessBundle::from_witness` syncs embedded `artifact` metadata, and
    //    scheduled metamorphic witnesses keep `mod subject_inlined` (including
    //    `Abort` subprocess isolation).
    let meta_prog = generate_fuzz_batch(0xBADA_B001, 1).pop().unwrap();
    let mut abort_sched = EnvSchedule::default();
    abort_sched.push_callee("fuzz_helper_2", EnvAction::Abort { reason: "halt".into() });
    let dual_sched_rs =
        render_standalone_fuzz_repro_rs(&meta_prog, Some(&abort_sched), "meta_sched");
    assert!(dual_sched_rs.contains("mod subject_inlined"));
    assert!(dual_sched_rs.contains("--anneal-meta-called"));
    assert!(dual_sched_rs.contains("--anneal-meta-inlined"));
    if let Some(rustc_bin) = &rustc {
        let mut sched_case = meta_prog.to_trace_test_case();
        sched_case.env_schedule = EnvSchedule::default();
        sched_case
            .env_schedule
            .push_callee("fuzz_helper_2", EnvAction::Unwind { message: "ok".into() });
        let harness = render_standalone_metamorphic_rust_harness(&sched_case);
        let mrs = tmp.path().join("meta_sched.rs");
        let mbin = tmp.path().join("meta_sched_bin");
        fs::write(&mrs, format!("#![allow(dead_code, unused_variables, unused_mut)]\n{harness}"))
            .unwrap();
        let comp = Command::new(rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .arg(&mrs)
            .arg("-o")
            .arg(&mbin)
            .output()
            .unwrap();
        assert!(
            comp.status.success(),
            "meta_sched compile failed: {}",
            String::from_utf8_lossy(&comp.stderr)
        );
        let run = Command::new(&mbin).output().unwrap();
        if meta_prog.has_helper_calls() {
            assert!(
                !run.status.success(),
                "scheduled called Unwind vs inlined Return must diverge"
            );
        }

        // Child-process Abort isolation catches a called Abort divergence.
        let mrs_abort = tmp.path().join("meta_abort_div.rs");
        let mbin_abort = tmp.path().join("meta_abort_div_bin");
        fs::write(&mrs_abort, &dual_sched_rs).unwrap();
        let comp_ab = Command::new(rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .arg(&mrs_abort)
            .arg("-o")
            .arg(&mbin_abort)
            .output()
            .unwrap();
        if meta_prog.has_helper_calls() {
            assert!(
                comp_ab.status.success(),
                "meta_abort compile failed: {}",
                String::from_utf8_lossy(&comp_ab.stderr)
            );
            let run_ab = Command::new(&mbin_abort).output().unwrap();
            assert!(!run_ab.status.success(), "called Abort vs inlined Return must diverge loudly");
            let stdout_ab = String::from_utf8_lossy(&run_ab.stdout);
            assert!(
                stdout_ab.contains("ANNEAL_ITREE_PRE_ABORT:"),
                "missing ANNEAL_ITREE_PRE_ABORT in stdout: {stdout_ab}"
            );
            assert!(
                stdout_ab.contains("ANNEAL_ITREE_INLINED_TWIN_JSON:"),
                "missing ANNEAL_ITREE_INLINED_TWIN_JSON in stdout: {stdout_ab}"
            );
            let run_ab_inlined =
                Command::new(&mbin_abort).arg("--anneal-meta-inlined").output().unwrap();
            assert!(
                run_ab_inlined.status.success(),
                "--anneal-meta-inlined child should exit cleanly: {}",
                String::from_utf8_lossy(&run_ab_inlined.stderr)
            );
        }
    }

    let w_orig = WitnessArtifact::from_shrink(
        "sync_c",
        TraceVerdict::UnsoundAccept { detail: "d".into() },
        TraceVerdict::UnsoundAccept { detail: "d".into() },
        shrink_fuzz_program_with_budget(
            &meta_prog,
            ShrinkBudget { max_evals: 4, max_duration: Duration::from_secs(10) },
            |_| true,
        ),
    );
    let synced_bundle = WitnessBundle::from_witness(w_orig.clone(), Some(&abort_sched));
    assert_eq!(
        synced_bundle.bundle_id,
        synced_bundle.artifact.repro_case_id.strip_prefix("repro_").unwrap()
    );
    assert_eq!(synced_bundle.repro_case_id, synced_bundle.artifact.repro_case_id);
    assert_eq!(synced_bundle.skel_hash, synced_bundle.artifact.minimized_skeleton_hash);
    assert_eq!(synced_bundle.repro_rust_source, synced_bundle.artifact.reproducer_rust_source);
    assert_eq!(synced_bundle.artifact.repro_schedule.as_ref(), Some(&abort_sched));
    assert_ne!(synced_bundle.bundle_id, w_orig.repro_case_id.strip_prefix("repro_").unwrap());

    // 5. `verify_head_build_provenance_with` and `TelemetryContext::discover`
    //    always fail closed on unattested binaries across clean/dirty trees
    //    and rewritten Git history (`commit --amend`, `git rm`,
    //    `git reset --hard`), while explicit commit attestation satisfies
    //    `is_verified_for_commit()` iff `commit_sha` matches `HEAD`.
    let repo_root = tmp.path().join("git_prov_r7");
    let anneal_root = repo_root.join("anneal");
    let crate_dir = anneal_root.join("tests/itree_diff");
    let lean_dir = anneal_root.join("trusted/lean");
    fs::create_dir_all(&crate_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(anneal_root.join("Cargo.toml"), "[workspace]\nmembers = []\nresolver = \"2\"\n")
        .unwrap();
    fs::write(lean_dir.join("lean-toolchain"), "leanprover/lean4:v4.34.1\n").unwrap();
    let keep_rs = crate_dir.join("keep.rs");
    let rm_rs = crate_dir.join("remove_me.rs");
    fs::write(&keep_rs, "pub fn keep() -> u32 { 1 }\n").unwrap();
    fs::write(&rm_rs, "pub fn rm() -> u32 { 2 }\n").unwrap();

    let git = |args: &[&str]| {
        let out = hermetic_git_command(&repo_root).args(args).output().unwrap();
        assert!(
            out.status.success(),
            "git {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    };
    // Verify `hermetic_git_command` clears inherited git hook/repo env vars
    // (`GIT_DIR`, `GIT_WORK_TREE`, `GIT_INDEX_FILE`, etc.).
    let env_probe = hermetic_git_command(&repo_root);
    let env_map: std::collections::BTreeMap<_, _> = env_probe
        .get_envs()
        .map(|(k, v)| (k.to_os_string(), v.map(|x| x.to_os_string())))
        .collect();
    for removed in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    ] {
        assert_eq!(env_map.get(std::ffi::OsStr::new(removed)), Some(&None));
    }
    assert_eq!(
        env_map.get(std::ffi::OsStr::new("GIT_CONFIG_GLOBAL")),
        Some(&Some("/dev/null".into()))
    );
    assert_eq!(
        env_map.get(std::ffi::OsStr::new("GIT_CONFIG_SYSTEM")),
        Some(&Some("/dev/null".into()))
    );
    git(&["init", "-q"]);
    git(&["config", "user.name", "Test User"]);
    git(&["config", "user.email", "test@example.com"]);
    git(&["add", "."]);
    git(&["commit", "-q", "-m", "c1"]);

    std::thread::sleep(Duration::from_millis(25));
    let bin_dir = tmp.path().join("bin_r7");
    fs::create_dir_all(&bin_dir).unwrap();
    let exe_path = bin_dir.join("itree-diff");
    fs::write(&exe_path, b"exe").unwrap();
    fs::write(
        bin_dir.join("itree-diff.d"),
        format!(
            "{}: {}\n",
            fs::canonicalize(&exe_path).unwrap().display(),
            fs::canonicalize(&keep_rs).unwrap().display()
        ),
    )
    .unwrap();
    let head1 = git(&["rev-parse", "--verify", "HEAD"]);
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        Some(&head1),
        &crate_dir,
        Some(&exe_path),
        Some(&head1),
        Some("1"),
    ));
    let ctx1 = TelemetryContext::discover(&anneal_root);
    assert!(!ctx1.head_provenance_verified);
    assert!(!ctx1.is_verified_for_commit());
    assert_eq!(ctx1.discovered_head_sha.as_deref(), Some(head1.as_str()));

    let mut verified_ctx = ctx1.clone();
    verified_ctx.head_provenance_verified = true;
    assert!(verified_ctx.is_verified_for_commit());

    // (a) `git commit --amend`: rewritten commit invalidates prior attestation.
    git(&["commit", "--amend", "-m", "c1 amended", "-q"]);
    let head_amend = git(&["rev-parse", "--verify", "HEAD"]);
    assert_ne!(head_amend, head1);
    let mut amend_ctx = TelemetryContext::discover(&anneal_root);
    assert!(!amend_ctx.head_provenance_verified);
    amend_ctx.head_provenance_verified = true;
    amend_ctx.commit_sha = head1.clone();
    assert!(!amend_ctx.is_verified_for_commit());
    amend_ctx.commit_sha = head_amend.clone();
    assert!(amend_ctx.is_verified_for_commit());

    // (b) `git rm && git commit`: deleting tracked source moves HEAD cleanly.
    git(&["rm", "-q", "anneal/tests/itree_diff/remove_me.rs"]);
    git(&["commit", "-q", "-m", "delete only"]);
    let head_rm = git(&["rev-parse", "--verify", "HEAD"]);
    assert_ne!(head_rm, head_amend);
    let mut rm_ctx = TelemetryContext::discover(&anneal_root);
    assert!(!rm_ctx.head_provenance_verified);
    rm_ctx.head_provenance_verified = true;
    rm_ctx.commit_sha = head_amend;
    assert!(!rm_ctx.is_verified_for_commit());
    rm_ctx.commit_sha = head_rm.clone();
    assert!(rm_ctx.is_verified_for_commit());

    // (c) Commit add-only file, then `git reset --hard HEAD~1`: reset reverts
    // `discovered_head_sha` back to `head_rm` cleanly.
    let add_rs = crate_dir.join("added_only.rs");
    fs::write(&add_rs, "pub fn added() -> u32 { 3 }\n").unwrap();
    git(&["add", "."]);
    git(&["commit", "-q", "-m", "add only"]);
    let head_add = git(&["rev-parse", "--verify", "HEAD"]);
    assert_ne!(head_add, head_rm);
    git(&["reset", "--hard", "-q", "HEAD~1"]);
    let mut reset_ctx = TelemetryContext::discover(&anneal_root);
    assert!(!reset_ctx.head_provenance_verified);
    assert_eq!(reset_ctx.discovered_head_sha.as_deref(), Some(head_rm.as_str()));
    reset_ctx.head_provenance_verified = true;
    reset_ctx.commit_sha = head_add;
    assert!(!reset_ctx.is_verified_for_commit());
    reset_ctx.commit_sha = head_rm;
    assert!(reset_ctx.is_verified_for_commit());

    // 6. Full metamorphic comparator compares `boundary_slots` (`mem_digest`)
    //    and `CallerFrameLaw` flags even when `kind` and `ret` match.
    if let Some(rustc_bin) = &rustc {
        let mut slot_div_case = meta_prog.to_trace_test_case();
        slot_div_case.pure_rust_source =
            "pub fn fuzz_entry(x: u32, _y: u32) -> u32 { x }\n".to_string();
        slot_div_case.traced_rust_source = Some(
            "pub fn fuzz_entry(x: u32, _y: u32) -> u32 { \
             crate::anneal_rt::record_boundary_slot(vec![Some(0x77)]); x }\n"
                .to_string(),
        );
        slot_div_case.rust_arg_exprs = vec!["1u32".to_string(), "2u32".to_string()];
        slot_div_case.ret_shape = anneal_itree_diff::spec::ReturnShape::Scalar {
            kind: anneal_itree_diff::outcome::IntKind::U32,
        };
        slot_div_case.env_schedule = EnvSchedule::default();
        if let Some(twin) = slot_div_case.metamorphic_inlined_twin.as_mut() {
            twin.pure_rust_source =
                "pub fn fuzz_entry_inlined(x: u32, _y: u32) -> u32 { x }\n".to_string();
        }
        for (tag, sched_abort) in [("direct", false), ("subprocess", true)] {
            let mut c = slot_div_case.clone();
            if sched_abort {
                // Uncalled abort action isolates variants in child processes.
                c.env_schedule
                    .push_callee("uncalled_abort_callee", EnvAction::Abort { reason: "h".into() });
                c.traced_rust_source = Some(
                    "pub fn fuzz_entry(x: u32, _y: u32) -> u32 { \
                     crate::anneal_rt::record_boundary_slot(vec![Some(0x77)]); \
                     let _ = crate::anneal_rt::pop_action(\"uncalled_abort_callee\"); x }\n"
                        .to_string(),
                );
            }
            let rs_src = format!(
                "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
                render_standalone_metamorphic_rust_harness(&c)
            );
            assert!(rs_src.contains("ANNEAL_ITREE_INLINED_TWIN_JSON:"));
            assert!(rs_src.contains("outcomes_diverge"));
            let rs = tmp.path().join(format!("slot_div_{tag}.rs"));
            let bin = tmp.path().join(format!("slot_div_{tag}_bin"));
            fs::write(&rs, &rs_src).unwrap();
            let comp = Command::new(rustc_bin)
                .args(["--edition", "2024", "-C", "overflow-checks=no"])
                .arg(&rs)
                .arg("-o")
                .arg(&bin)
                .output()
                .unwrap();
            assert!(comp.status.success(), "{tag}: {}", String::from_utf8_lossy(&comp.stderr));
            let run = Command::new(&bin).output().unwrap();
            assert!(
                !run.status.success(),
                "{tag} must reject differing boundary_slots/mem_digest even when ret matches"
            );
        }

        // Agreeing called and inlined variants pass outcome + frame checks.
        let mut slot_ok_case = slot_div_case;
        slot_ok_case.traced_rust_source =
            Some("pub fn fuzz_entry(x: u32, _y: u32) -> u32 { x }\n".to_string());
        let ok_src = format!(
            "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
            render_standalone_metamorphic_rust_harness(&slot_ok_case)
        );
        let ok_rs = tmp.path().join("slot_ok.rs");
        let ok_bin = tmp.path().join("slot_ok_bin");
        fs::write(&ok_rs, &ok_src).unwrap();
        let comp = Command::new(rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .arg(&ok_rs)
            .arg("-o")
            .arg(&ok_bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
        let run = Command::new(&ok_bin).output().unwrap();
        assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));
    }
}

#[test]
fn return_bytes_serde_signature_scoping_o0_o2_repro_slice_layout_and_witness_collision_fixes() {
    let tmp = tempfile::tempdir().unwrap();

    // 1. `EnvAction::ReturnBytes` serializes and deserializes cleanly across
    //    `EnvSchedule`, `ShrinkableCase`, `WitnessArtifact::write_json`,
    //    `WitnessBundle::write_to_dir`, and `BugRegistry`.
    let mut rb_sched = EnvSchedule::default();
    rb_sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![0x11, 0x22, 0x33, 0x44]));
    rb_sched.push_global(EnvAction::Unwind { message: "u".to_string() });
    rb_sched.push_callee("fuzz_helper_1", EnvAction::Abort { reason: "halt".to_string() });

    let sched_json = serde_json::to_string(&rb_sched).expect("serialize EnvSchedule");
    let sched_roundtrip: EnvSchedule =
        serde_json::from_str(&sched_json).expect("deserialize EnvSchedule");
    assert_eq!(sched_roundtrip, rb_sched);

    let mut prog = generate_fuzz_batch(0xC0DE_0001, 1).pop().unwrap();
    prog.steps = vec![FuzzStep::HelperCall { callee_idx: 0, bias: 1 }];
    let mut sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    sr.succeeded = true;
    sr.is_one_minimal = true;
    sr.converged_1_minimal = true;

    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep = mk_ub_case_report(
        "rb_serde",
        "Undefined Behavior: Tree Borrows: write access forbidden",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let sig = ShrinkFailureSignature::from_case_report(&rep).unwrap();
    let artifact = WitnessArtifact::from_shrink_with_schedule(
        "rb_serde",
        rep.verdict.clone(),
        rep.verdict.clone(),
        sr,
        Some(&rb_sched),
    )
    .with_signature(sig.clone())
    .with_minimized_report(rep.clone());
    let witness_path = tmp.path().join("rb_witness.json");
    artifact
        .write_json(&witness_path)
        .expect("WitnessArtifact::write_json must handle ReturnBytes");
    let loaded_artifact: WitnessArtifact =
        serde_json::from_str(&fs::read_to_string(&witness_path).unwrap()).unwrap();
    assert_eq!(loaded_artifact.repro_schedule.as_ref(), Some(&rb_sched));

    let bundle_dir = tmp.path().join("rb_bundle");
    let bundle = WitnessBundle::from_witness(artifact.clone(), Some(&rb_sched));
    let paths = bundle.write_to_dir(&bundle_dir).expect("WitnessBundle::write_to_dir must succeed");
    assert!(paths.witness_json_path.is_file());

    let mut reg = BugRegistry::new("google/zerocopy");
    let rec = reg.record_witness(
        &artifact,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        Some(&rb_sched),
    );
    assert!(matches!(rec, DedupRecordOutcome::NewBug { .. }));
    let reg_json = serde_json::to_string(&reg).expect("BugRegistry with ReturnBytes serializes");
    let reg_back: BugRegistry = serde_json::from_str(&reg_json).unwrap();
    assert_eq!(reg_back.buckets.len(), 1);

    // 2. `ShrinkFailureSignature::from_case_report` scopes metamorphic twin
    //    relations and twin `tool_error` strictly to primary
    //    `metamorphic_duality` failures so non-causal `UnwindProbe` shrinks.
    let mut non_meta_rep = rep.clone();
    non_meta_rep.metamorphic = Some(MetamorphicDualityReceipt {
        called_lean: mk_auth("lean", ret_ok.clone()),
        inlined_lean: mk_auth("lean", ret_ok.clone()),
        inlined_rustc_parity_ok: false,
        inlined_miri_matched: Some(true),
        tool_error: Some(("rustc".into(), "secondary twin error".into())),
        status: MetamorphicStatus::Failed,
        duality_holds: false,
        detail: "metamorphic_duality: source-inlined twin rustc O0 vs O2 mismatch".into(),
        failed_relations: vec!["inlined_rustc_o0_vs_o2".into()],
        twin_outcome_summary: "called_o0=returned,inlined_o0=returned".into(),
    });
    let primary_sig = ShrinkFailureSignature::from_case_report(&non_meta_rep)
        .expect("secondary twin tool_error must not discard primary critical signature");
    assert!(primary_sig.metamorphic_relations.is_empty());
    assert!(primary_sig.metamorphic_leg_kinds.is_empty());

    let unwind_prog = FuzzProgram {
        seed: 0xAA11,
        index: 0,
        input_x: 16,
        input_y: 8,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 3 },
            FuzzStep::UnwindProbe { trigger_unwind: true },
        ],
        applied_mutators: Vec::new(),
    };
    let (shrunk_unwind, shrink_err) = shrink_and_build_witness_with_budget(
        "non_causal_unwind",
        &unwind_prog,
        &rep.verdict,
        &sig,
        ShrinkBudget::default(),
        |cand| {
            let mut r = rep.clone();
            if !cand.has_triggering_unwind() {
                r.metamorphic = Some(MetamorphicDualityReceipt {
                    called_lean: mk_auth("lean", ret_ok.clone()),
                    inlined_lean: mk_auth("lean", ret_ok.clone()),
                    inlined_rustc_parity_ok: true,
                    inlined_miri_matched: Some(false),
                    tool_error: None,
                    status: MetamorphicStatus::Failed,
                    duality_holds: false,
                    detail: "metamorphic_duality: Miri multi-call vs source-inlined mismatch"
                        .into(),
                    failed_relations: vec!["miri_called_vs_inlined".into()],
                    twin_outcome_summary: "called_miri=returned,inlined_miri=fault_ub".into(),
                });
            }
            if cand.steps.iter().any(|s| matches!(s, FuzzStep::ArithImm { .. })) {
                r
            } else {
                CaseReport { verdict: TraceVerdict::Agree, ..r }
            }
        },
    );
    assert!(shrink_err.is_none(), "expected clean convergence: {shrink_err:?}");
    assert!(
        !shrunk_unwind.shrink.minimized.has_triggering_unwind(),
        "non-causal UnwindProbe must shrink away when secondary twin diverges"
    );

    // 3. Cross-mode `O0` vs `O2` comparison for pinned
    //    `called_rustc_o0_vs_o2` / `inlined_rustc_o0_vs_o2` reproducers.
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let mut opt_case = generate_fuzz_batch(0x0902_0001, 1).pop().unwrap().to_trace_test_case();
    opt_case.rust_arg_exprs = vec!["1u32".into(), "2u32".into()];
    opt_case.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    opt_case.env_schedule = EnvSchedule::default();
    opt_case.pure_rust_source = "pub fn fuzz_entry(_x: u32, _y: u32) -> u32 {\n\
         \x20   if cfg!(debug_assertions) { 10 } else { 99 }\n\
         }\n"
    .to_string();
    opt_case.traced_rust_source = None;
    opt_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(_x: u32, _y: u32) -> u32 {\n\
         \x20   if cfg!(debug_assertions) { 10 } else { 99 }\n\
         }\n"
        .to_string();

    let meta_verdict = TraceVerdict::UnsoundAccept {
        detail: "metamorphic_duality: original multi-call rustc O0 vs O2 mismatch".into(),
    };
    let mut o0_o2_meta_sig =
        ShrinkFailureSignature::from_verdict_and_legs(&meta_verdict, None, None).unwrap();
    o0_o2_meta_sig.metamorphic_relations = vec!["called_rustc_o0_vs_o2".into()];
    let mut meta_sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |_| true);
    meta_sr.succeeded = true;
    meta_sr.is_one_minimal = true;
    meta_sr.converged_1_minimal = true;
    let o0_o2_bundle = WitnessBundle::from_witness(
        WitnessArtifact::from_shrink("meta_o0_o2", meta_verdict.clone(), meta_verdict, meta_sr)
            .with_signature(o0_o2_meta_sig),
        None,
    );
    assert!(o0_o2_bundle.repro_rust_source.contains("\"called_rustc_o0_vs_o2\""));
    assert!(o0_o2_bundle.repro_rust_source.contains("--compare-opt"));

    let meta_o0_o2_src = format!(
        "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &opt_case,
            &["called_rustc_o0_vs_o2".to_string()],
        )
    );
    let o0_o2_rs = tmp.path().join("meta_o0_o2.rs");
    let o0_bin = tmp.path().join("meta_o0_o2");
    let o2_bin = tmp.path().join("meta_o0_o2_o2");
    let alt_o2_bin = tmp.path().join("alt_o2_peer");
    fs::write(&o0_o2_rs, &meta_o0_o2_src).unwrap();
    for (extra, out_bin) in [
        (&["-C", "debug-assertions=yes"][..], &o0_bin),
        (&["-C", "opt-level=2", "-C", "debug-assertions=no"][..], &alt_o2_bin),
    ] {
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .args(extra)
            .arg(&o0_o2_rs)
            .arg("-o")
            .arg(out_bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    }
    // Without peer binary, single-mode binary refuses silent zero-exit pass.
    let solo_o0 = Command::new(&o0_bin).output().unwrap();
    assert!(!solo_o0.status.success(), "pinned O0 vs O2 reproducer must not exit 0 alone");
    // `--compare-opt` detects cross-mode divergence between `o0` and `alt_o2`.
    let cmp_div = Command::new(&o0_bin).args(["--compare-opt"]).arg(&alt_o2_bin).output().unwrap();
    assert!(!cmp_div.status.success(), "--compare-opt must catch called_rustc_o0_vs_o2 divergence");
    assert!(
        String::from_utf8_lossy(&cmp_div.stderr).contains("called_rustc_o0_vs_o2"),
        "stderr={}",
        String::from_utf8_lossy(&cmp_div.stderr)
    );
    // Sibling `*_o2` binary triggers automatic cross-mode check on bare run.
    fs::copy(&alt_o2_bin, &o2_bin).unwrap();
    let auto_div = Command::new(&o0_bin).output().unwrap();
    assert!(!auto_div.status.success(), "sibling *_o2 auto-compare must detect divergence");
    // Comparing O0 against itself succeeds because cross-mode outcomes agree.
    let cmp_same = Command::new(&o0_bin).args(["--compare-opt"]).arg(&o0_bin).output().unwrap();
    assert!(
        cmp_same.status.success(),
        "matching cross-mode binaries should pass: {}",
        String::from_utf8_lossy(&cmp_same.stderr)
    );

    // 4. Wave-2 `render_standalone_shrinkable_repro_rs` allocates and reads
    //    retained `slice_len` + `slice_align`, and Pass 4 narrows
    //    `slice_align`.
    let slice_case = ShrinkableCase {
        name: "slice_layout_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 5, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: Some(24),
        slice_align: 16,
        helpers: Vec::new(),
        steps: Vec::new(),
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let slice_res = shrink_case_two_tier_with_budget(
        &slice_case,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |c| c.slice_align >= 4 && c.slice_len.is_some_and(|l| l >= 8),
        |c| c.slice_align >= 4 && c.slice_len.is_some_and(|l| l >= 8),
    );
    assert_eq!(slice_res.minimized.slice_align, 4);
    assert_eq!(slice_res.minimized.slice_len, Some(8));
    let slice_rs = render_standalone_shrinkable_repro_rs(&slice_res.minimized, "slice_repro");
    assert!(slice_rs.contains("_repro_pool.alloc(8usize, 4usize)"));
    assert!(slice_rs.contains("ZstAlign4"));
    let slice_rs_path = tmp.path().join("slice_repro.rs");
    let slice_bin_path = tmp.path().join("slice_repro_bin");
    fs::write(&slice_rs_path, &slice_rs).unwrap();
    let slice_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024"])
        .arg(&slice_rs_path)
        .arg("-o")
        .arg(&slice_bin_path)
        .output()
        .unwrap();
    assert!(slice_comp.status.success(), "{}", String::from_utf8_lossy(&slice_comp.stderr));
    assert!(Command::new(&slice_bin_path).output().unwrap().status.success());

    // 5. `--witness-dir` validation rejects `--corpus-dir` without `--shrink`
    //    and reports `--corpus-dir` in its error, while overlapping seed and
    //    fuzz `(seed, index)` never clobber `.witness.json`.
    let wdir_err = anneal_itree_diff::validate_cli_run_plan_with_corpus_dir(
        false, true, None, None, false, true,
    )
    .unwrap_err();
    assert!(wdir_err.contains("--corpus-dir") && wdir_err.contains("--shrink"), "err={wdir_err}");

    let coll_dir = tmp.path().join("witness_coll");
    let mut seen_stems = std::collections::BTreeSet::new();
    let mut out_witnesses = Vec::new();
    for idx in 0..2usize {
        let mut r = rep.clone();
        r.case_id = "fuzz_s123_i000".to_string();
        let w = artifact.clone().with_report_index(idx);
        anneal_itree_diff::apply_fuzz_shrink_outcome_with_seen(
            &mut r,
            Some(&coll_dir),
            &mut out_witnesses,
            w,
            None,
            Some(&mut seen_stems),
        );
    }
    assert!(coll_dir.join("fuzz_s123_i000.witness.json").is_file());
    assert!(coll_dir.join("fuzz_s123_i000_dup2.witness.json").is_file());
    let coll_prog = generate_fuzz_batch(0xC011_0001, 1).pop().unwrap();
    let bin = env!("CARGO_BIN_EXE_itree-diff");
    let amb_seeds = tmp.path().join("amb_seeds");
    fs::create_dir_all(&amb_seeds).unwrap();
    fs::write(amb_seeds.join("amb.json"), serde_json::to_string(&coll_prog).unwrap()).unwrap();
    let amb_out = Command::new(bin)
        .env("ANNEAL_CORPUS_DIR", &amb_seeds)
        .args(["--filter", "cat1_signed_abs_diff", "--no-miri", "--no-lean"])
        .output()
        .unwrap();
    assert!(
        amb_out.status.success(),
        "ambient ANNEAL_CORPUS_DIR must not break default curated --filter: {}",
        String::from_utf8_lossy(&amb_out.stderr)
    );
}

#[test]
fn dedup_schedule_tags_workspace_root_struct_fields_and_alpha_bijection() {
    let tmp = tempfile::tempdir().unwrap();
    let anneal_root = workspace_anneal_root().expect("live anneal root");

    // 1. `workspace_anneal_root` stays anchored to compile-time
    //    `CARGO_MANIFEST_DIR` even when ambient `ANNEAL_ROOT` and `cwd` point
    //    to another checkout.
    if let Some(expected_root) = std::env::var_os("ANNEAL_R10_EXPECTED_ROOT") {
        assert_eq!(
            std::path::PathBuf::from(expected_root),
            anneal_itree_diff::workspace_anneal_root().unwrap()
        );
        return;
    }
    let alt_repo = tmp.path().join("alt_checkout");
    let alt_anneal = alt_repo.join("anneal");
    fs::create_dir_all(alt_anneal.join("trusted/lean")).unwrap();
    fs::write(alt_anneal.join("Cargo.toml"), "[workspace]\nmembers = []\nresolver = \"2\"\n")
        .unwrap();
    fs::write(alt_anneal.join("trusted/lean/lean-toolchain"), "leanprover/lean4:v4.34.1\n")
        .unwrap();
    assert_eq!(
        anneal_itree_diff::resolve_anneal_root_with_env(
            None,
            Some(alt_repo.as_os_str()),
            Some(&alt_repo),
        )
        .unwrap(),
        fs::canonicalize(&alt_anneal).unwrap()
    );
    let self_exe = std::env::current_exe().unwrap();
    let child = Command::new(self_exe)
        .current_dir(&alt_repo)
        .env("ANNEAL_ROOT", &alt_repo)
        .env("ANNEAL_R10_EXPECTED_ROOT", &anneal_root)
        .args([
            "--exact",
            "dedup_schedule_tags_workspace_root_struct_fields_and_alpha_bijection",
            "--nocapture",
        ])
        .output()
        .unwrap();
    assert!(child.status.success(), "{}", String::from_utf8_lossy(&child.stderr));
    let child_stdout = String::from_utf8_lossy(&child.stdout);
    assert!(
        child_stdout.contains("1 passed"),
        "expected child test execution, stdout={child_stdout}"
    );

    // 2. `CanonicalBugFingerprint::from_1_minimal_witness` honors
    //    `witness.repro_schedule` when `schedule` is `None` and separates
    //    scheduled vs unscheduled `BugId`s via `sched:*` construct tags.
    let mut base_prog = generate_fuzz_batch(0x1010_0001, 1).pop().unwrap();
    base_prog.steps = vec![FuzzStep::HelperCall { callee_idx: 0, bias: 1 }];
    let mut sr = shrink_fuzz_program_with_budget(&base_prog, ShrinkBudget::default(), |_| true);
    sr.succeeded = true;
    sr.is_one_minimal = true;
    sr.converged_1_minimal = true;
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep = mk_ub_case_report(
        "fp_sched",
        "Undefined Behavior: Tree Borrows: write access forbidden",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let mut sched = EnvSchedule::default();
    sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![1, 2, 3, 4]));
    let w_unsched =
        WitnessArtifact::from_shrink("u", rep.verdict.clone(), rep.verdict.clone(), sr.clone());
    let w_sched = WitnessArtifact::from_shrink_with_schedule(
        "s",
        rep.verdict.clone(),
        rep.verdict.clone(),
        sr.clone(),
        Some(&sched),
    );
    let mut rep_u = rep.clone();
    rep_u.case_id = w_unsched.case_id.clone();
    let mut rep_s = rep.clone();
    rep_s.case_id = w_sched.case_id.clone();
    let fp_unsched =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_unsched, &rep_u, "main", "v1", None)
            .unwrap();
    let fp_sched_implicit =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_sched, &rep_s, "main", "v1", None)
            .unwrap();
    let fp_sched_explicit = CanonicalBugFingerprint::from_1_minimal_witness(
        &w_sched,
        &rep_s,
        "main",
        "v1",
        Some(&sched),
    )
    .unwrap();
    assert_eq!(fp_sched_implicit, fp_sched_explicit);
    assert!(fp_sched_implicit.mir_construct_sig.iter().any(|t| t == "sched:return_bytes"));
    assert_ne!(fp_unsched.bug_id(), fp_sched_implicit.bug_id());
    assert_ne!(fp_unsched.minimized_skeleton_hash, fp_sched_implicit.minimized_skeleton_hash);

    // 3. `BugRegistry::record_witness` preserves `PINNED_META_RELATIONS`
    //    when regenerating `repro_rust_source`.
    let meta_verdict = TraceVerdict::UnsoundAccept {
        detail: "metamorphic_duality: original multi-call rustc O0 vs O2 mismatch".into(),
    };
    let mut meta_rep = rep.clone();
    meta_rep.case_id = "meta_regen".into();
    meta_rep.verdict = meta_verdict.clone();
    meta_rep.miri = Some(mk_auth("miri", ret_val.clone()));
    meta_rep.rustc_dual = RustcDualResult {
        o0: mk_auth("rustc-O0", ret_val.clone()),
        o2: mk_auth("rustc-O2", ret_val.clone()),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2".into()),
    };
    meta_rep.metamorphic = Some(MetamorphicDualityReceipt {
        called_lean: mk_auth("lean", ret_val.clone()),
        inlined_lean: mk_auth("lean", ret_val.clone()),
        inlined_rustc_parity_ok: true,
        inlined_miri_matched: Some(true),
        tool_error: None,
        status: MetamorphicStatus::Failed,
        duality_holds: false,
        detail: "metamorphic_duality: original multi-call rustc O0 vs O2 mismatch".into(),
        failed_relations: vec!["called_rustc_o0_vs_o2".into()],
        twin_outcome_summary: "called_o0=returned,called_o2=returned".into(),
    });
    let mut w_meta = WitnessArtifact::from_shrink_with_schedule(
        "meta_regen",
        meta_verdict.clone(),
        meta_verdict,
        sr,
        Some(&sched),
    )
    .with_minimized_report(meta_rep.clone());
    // Clear `reproducer_rust_source` so `record_witness` takes regen path.
    w_meta.reproducer_rust_source.clear();
    let mut reg = BugRegistry::new("google/zerocopy");
    let rec_out = reg.record_witness(
        &w_meta,
        &meta_rep,
        "main",
        true,
        "v1",
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        None,
    );
    let bug_id = match rec_out {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("unexpected outcome: {other:?}"),
    };
    let stored_src = &reg.buckets[&bug_id].witnesses[0].repro_rust_source;
    assert!(stored_src.contains("\"called_rustc_o0_vs_o2\""), "src:\n{stored_src}");
    assert!(stored_src.contains("--compare-opt"));

    // 4. `canonical_alpha_renamed` remaps orphan helper keys without colliding
    //    with newly alpha-renamed live helper IDs (`h7 -> h0`, orphan
    //    `h0 -> h1`).
    let mut coll_sched = EnvSchedule::default();
    coll_sched.push_callee("h7", EnvAction::ReturnBytes(vec![1, 0, 0, 0]));
    coll_sched.push_callee("h0", EnvAction::Unwind { message: "orphan".into() });
    let sc_coll = ShrinkableCase {
        name: "alpha_biject".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 2, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: vec![IntKind::U8, IntKind::U64, IntKind::U16],
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 7,
            multiplier: 2,
            addend: 1,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![ShrinkStep::HelperCall {
            dst_local: 2,
            helper_id: 7,
            block_id: 1,
            bias: 0,
            rhs_local: None,
        }],
        env_schedule: coll_sched,
        return_local: 2,
    };
    let sc_alpha = sc_coll.canonical_alpha_renamed();
    assert_eq!(sc_alpha.env_schedule.per_callee["h0"].len(), 1);
    assert!(matches!(sc_alpha.env_schedule.per_callee["h0"][0], EnvAction::ReturnBytes(_)));
    assert_eq!(sc_alpha.env_schedule.per_callee["h1"].len(), 1);
    assert!(matches!(sc_alpha.env_schedule.per_callee["h1"][0], EnvAction::Unwind { .. }));
    assert_eq!(sc_alpha.canonical_alpha_renamed(), sc_alpha);

    // 5. Retained `struct_fields` compile and run via `ReproRetainedStruct`,
    //    and unmatched schedule actions remain unconsumed
    //    (`unconsumed_schedule`).
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let alpha_rs = render_standalone_shrinkable_repro_rs(&sc_alpha, "alpha_struct_uncons");
    assert!(alpha_rs.contains("struct ReproRetainedStruct"));
    assert!(alpha_rs.contains("offset_of!(ReproRetainedStruct, f1)"));
    assert!(alpha_rs.contains("anneal_rt::remaining_schedule_count()"));
    let rs_path = tmp.path().join("alpha_struct_uncons.rs");
    let bin_path = tmp.path().join("alpha_struct_uncons_bin");
    fs::write(&rs_path, &alpha_rs).unwrap();
    let comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&rs_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .unwrap();
    assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    let run = Command::new(&bin_path).output().unwrap();
    assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(stdout.contains("\"outcome_kind\":\"unconsumed_schedule\""), "stdout:\n{stdout}");
}

#[test]
fn shrink_handle_def_use_metamorphic_and_pair_watch_regression() {
    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. Reject duplicate `ShrinkHelper::helper_id` before shrinking.
    let dup_helpers = vec![
        ShrinkHelper { helper_id: 7, multiplier: 2, addend: 1, op: ShrinkHelperOp::AffineMulAdd },
        ShrinkHelper { helper_id: 7, multiplier: 5, addend: 9, op: ShrinkHelperOp::AffineMulAdd },
    ];
    let dup_steps = vec![ShrinkStep::HelperCall {
        dst_local: 0,
        helper_id: 7,
        block_id: 1,
        bias: 0,
        rhs_local: None,
    }];
    assert!(!all_handles_defined_and_typed(&dup_steps, &dup_helpers));

    let dup_case = ShrinkableCase {
        name: "dup_helpers".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: dup_helpers,
        steps: dup_steps,
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let dup_shrink = shrink_case_two_tier_with_budget(
        &dup_case,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        |_| true,
    );
    assert!(!dup_shrink.succeeded);
    assert_eq!(dup_shrink.predicate_evaluations, 0);
    assert!(dup_shrink.pass_stats.def_use_filter_skips >= 1);

    // 2. Miri-only CallerFrameLaw failure on the source-inlined twin MUST NOT
    //    misclassify as `value_mismatch_count`.
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(10),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let dual_ok = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_val.clone()),
        o2: mk_auth("rustc-o2", ret_val.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let mut twin_miri_bad_frame = mk_auth("miri", ret_val.clone());
    twin_miri_bad_frame.caller_frame_law = CallerFrameLaw {
        caller_locals_preserved: false,
        untouched_alloc_bytes_preserved: true,
        padding_mask_respected: true,
        violations: vec!["twin frame clobbered".into()],
    };
    let miri_frame_rec = evaluate_metamorphic_duality(
        &dual_ok,
        Some(&mk_auth("miri", ret_val.clone())),
        &mk_auth("lean", ret_val.clone()),
        &dual_ok,
        Some(&twin_miri_bad_frame),
        mk_auth("lean", ret_val.clone()),
    );
    assert_eq!(miri_frame_rec.inlined_miri_matched, Some(false));
    assert_eq!(
        miri_frame_rec.failed_relations,
        vec!["metamorphic_caller_frame_law:inlined_miri".to_string()]
    );
    assert!(miri_frame_rec.detail.contains("CallerFrameLaw failed"));

    let mut miri_frame_rep = mk_ub_case_report(
        "miri_inlined_frame",
        "",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: miri_frame_rec.detail.clone() },
    );
    miri_frame_rep.rustc_dual = dual_ok.clone();
    miri_frame_rep.miri = Some(mk_auth("miri", ret_val.clone()));
    miri_frame_rep.lean = Some(mk_auth("lean", ret_val.clone()));
    miri_frame_rep.metamorphic = Some(miri_frame_rec);
    let miri_frame_report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![miri_frame_rep],
        Vec::new(),
    );
    let miri_frame_detail = SemanticDetailRecord::from_report_and_registry(
        &miri_frame_report,
        &BugRegistry::new("google/zerocopy"),
        &TelemetryContext::discover(tmp.path()),
    )
    .unwrap();
    assert_eq!(miri_frame_detail.differential_runs[0].value_mismatch_count, 0);
    assert_eq!(miri_frame_detail.differential_runs[0].unsound_missed_fault_count, 1);

    // 3. Even a manual receipt reporting only `miri_called_vs_inlined` stays
    //    conservatively in `unsound_missed_fault_count`.
    let mut manual_miri_rep = mk_ub_case_report(
        "miri_manual_rel",
        "",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept {
            detail: "metamorphic_duality: Miri multi-call vs source-inlined mismatch".into(),
        },
    );
    manual_miri_rep.rustc_dual = dual_ok;
    manual_miri_rep.miri = Some(mk_auth("miri", ret_val.clone()));
    manual_miri_rep.lean = Some(mk_auth("lean", ret_val.clone()));
    manual_miri_rep.metamorphic = Some(MetamorphicDualityReceipt {
        called_lean: mk_auth("lean", ret_val.clone()),
        inlined_lean: mk_auth("lean", ret_val),
        inlined_rustc_parity_ok: true,
        inlined_miri_matched: Some(false),
        tool_error: None,
        status: MetamorphicStatus::Failed,
        duality_holds: false,
        detail: "metamorphic_duality: Miri multi-call vs source-inlined mismatch".into(),
        failed_relations: vec!["miri_called_vs_inlined".into()],
        twin_outcome_summary: "called_miri=returned,inlined_miri=returned".into(),
    });
    let manual_report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![manual_miri_rep],
        Vec::new(),
    );
    let manual_detail = SemanticDetailRecord::from_report_and_registry(
        &manual_report,
        &BugRegistry::new("google/zerocopy"),
        &TelemetryContext::discover(tmp.path()),
    )
    .unwrap();
    assert_eq!(manual_detail.differential_runs[0].value_mismatch_count, 0);
    assert_eq!(manual_detail.differential_runs[0].unsound_missed_fault_count, 1);

    // 4. `PairOffsetLen` inside `DropGuardWrapper` emits `emit_watch_sync`.
    let pair_watch_case = ShrinkableCase {
        name: "pair_watch".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::DropGuardWrapper {
            local_id: 0,
            body: vec![ShrinkStep::PairOffsetLen { offset: 0, len: 8, align: 4, local_id: 0 }],
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let pair_rs = render_standalone_shrinkable_repro_rs(&pair_watch_case, "pair_watch");
    assert!(
        pair_rs.contains("_drop_cell_0.set(l0);")
            && pair_rs.contains("l0 = l0.wrapping_add((_pair_fold_1"),
        "expected DropGuard watch sync after PairOffsetLen mutation:\n{pair_rs}"
    );
}

#[test]
fn metamorphic_pinned_relations_honesty_and_symlink_dir_regression() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Implicit default unwind schedule parity across fuzz construct tags,
    //    `ShrinkableCase`, and canonical `BugId` derivation.
    let mut unw_prog = generate_fuzz_batch(0x0912_0001, 1).pop().unwrap();
    unw_prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 },
        FuzzStep::UnwindProbe { trigger_unwind: true },
    ];
    let implicit_tags = anneal_itree_diff::shrink::extract_fuzz_program_construct_tags(&unw_prog);
    let default_sched = unw_prog.to_trace_test_case().env_schedule;
    let explicit_tags =
        anneal_itree_diff::shrink::extract_fuzz_program_construct_tags_with_schedule(
            &unw_prog,
            Some(&default_sched),
        );
    let case_tags = ShrinkableCase::from_fuzz_program(&unw_prog, None).extract_mir_construct_tags();
    let case_tags_explicit = ShrinkableCase::from_fuzz_program(&unw_prog, Some(&default_sched))
        .extract_mir_construct_tags();
    assert!(implicit_tags.iter().any(|t| t == "sched:unwind"), "tags={implicit_tags:?}");
    assert_eq!(implicit_tags, explicit_tags);
    assert_eq!(case_tags, case_tags_explicit);
    assert!(case_tags.iter().any(|t| t == "sched:unwind"), "case_tags={case_tags:?}");

    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(1),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let mut unw_rep = mk_ub_case_report(
        "unw_canon",
        "",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "unwind divergence".into() },
    );
    unw_rep.miri = Some(mk_auth("miri", ret_ok.clone()));
    unw_rep.lean = Some(mk_auth(
        "lean",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(2),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
    ));
    let mut unw_sr = shrink_fuzz_program_with_budget(&unw_prog, ShrinkBudget::default(), |p| {
        p.has_triggering_unwind()
    });
    unw_sr.succeeded = true;
    unw_sr.is_one_minimal = true;
    unw_sr.converged_1_minimal = true;
    let min_default_sched = unw_sr.minimized.to_trace_test_case().env_schedule;
    let w_implicit = WitnessArtifact::from_shrink(
        "w_imp",
        unw_rep.verdict.clone(),
        unw_rep.verdict.clone(),
        unw_sr.clone(),
    );
    let w_explicit = WitnessArtifact::from_shrink_with_schedule(
        "w_exp",
        unw_rep.verdict.clone(),
        unw_rep.verdict.clone(),
        unw_sr,
        Some(&min_default_sched),
    );
    let mut rep_imp = unw_rep.clone();
    rep_imp.case_id = w_implicit.case_id.clone();
    let mut rep_exp = unw_rep.clone();
    rep_exp.case_id = w_explicit.case_id.clone();
    let fp_imp =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_implicit, &rep_imp, "main", "v1", None)
            .unwrap();
    let fp_exp =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_explicit, &rep_exp, "main", "v1", None)
            .unwrap();
    assert_eq!(fp_imp.bug_id(), fp_exp.bug_id());
    assert_eq!(w_implicit.minimized_skeleton_hash, w_explicit.minimized_skeleton_hash);

    // 2. Reproducers pinned to Lean or Miri relations MUST
    //    NOT silently pass when run as standalone native `rustc` binaries, yet
    //    still expose `--anneal-meta-{called,inlined}` and pass natively for
    //    `rustc_called_vs_inlined`.
    let mut ok_twin_case = generate_fuzz_batch(0x0912_0002, 1).pop().unwrap().to_trace_test_case();
    ok_twin_case.rust_arg_exprs = vec!["1u32".into(), "2u32".into()];
    ok_twin_case.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    ok_twin_case.env_schedule = EnvSchedule::default();
    ok_twin_case.pure_rust_source = "pub fn fuzz_entry(x: u32, _y: u32) -> u32 { x }\n".into();
    ok_twin_case.traced_rust_source = None;
    ok_twin_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, _y: u32) -> u32 { x }\n".into();

    for rel in ["lean_called_vs_inlined", "called_rustc_vs_lean", "miri_called_vs_inlined"] {
        let src = format!(
            "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
            anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
                &ok_twin_case,
                &[rel.to_string()],
            )
        );
        let rs_p = tmp.path().join(format!("{rel}.rs"));
        let bin_p = tmp.path().join(format!("{rel}_bin"));
        fs::write(&rs_p, &src).unwrap();
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024"])
            .arg(&rs_p)
            .arg("-o")
            .arg(&bin_p)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
        let solo = Command::new(&bin_p).output().unwrap();
        assert!(
            !solo.status.success(),
            "pinned non-rustc relation {rel} must refuse silent exit 0 in native rustc run"
        );
        assert!(
            String::from_utf8_lossy(&solo.stderr).contains(rel),
            "stderr={}",
            String::from_utf8_lossy(&solo.stderr)
        );
        let meta_called = Command::new(&bin_p).arg("--anneal-meta-called").output().unwrap();
        assert!(meta_called.status.success());
    }

    let rust_only_src = format!(
        "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &ok_twin_case,
            &["rustc_called_vs_inlined".to_string()],
        )
    );
    let rust_rs = tmp.path().join("rustc_only.rs");
    let rust_bin = tmp.path().join("rustc_only_bin");
    fs::write(&rust_rs, &rust_only_src).unwrap();
    let rust_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024"])
        .arg(&rust_rs)
        .arg("-o")
        .arg(&rust_bin)
        .output()
        .unwrap();
    assert!(rust_comp.status.success());
    assert!(Command::new(&rust_bin).output().unwrap().status.success());

    // 3. Witness persistence failure withholds the witness
    //    instead of reporting a fake disk-backed witness.
    let bad_witness_dir = tmp.path().join("not_a_dir");
    fs::write(&bad_witness_dir, "blocking regular file").unwrap();
    let mut fail_persist_rep = unw_rep.clone();
    let mut retained = Vec::new();
    anneal_itree_diff::apply_fuzz_shrink_outcome(
        &mut fail_persist_rep,
        Some(&bad_witness_dir),
        &mut retained,
        w_implicit.clone(),
        None,
    );
    assert!(retained.is_empty(), "failed witness persistence must withhold witness");
    assert!(
        matches!(
            &fail_persist_rep.verdict,
            TraceVerdict::UnsoundAccept { detail } if detail.contains("witness-writer")
        ),
        "verdict={:?}",
        fail_persist_rep.verdict
    );

    // 4. `validate_honesty` rejects stale or unverified `PASS` claims on
    //    `evidence_blocks` and `differential_runs`, and
    //    `from_report_and_registry` downgrades stale slice `PASS`.
    let clean_case = mk_ub_case_report("ok_case", "", ret_ok.clone(), TraceVerdict::Agree);
    let mut ok_agree_case = clean_case;
    ok_agree_case.rustc_dual = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth("rustc-o2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    ok_agree_case.miri = Some(mk_auth("miri", ret_ok.clone()));
    ok_agree_case.lean = Some(mk_auth("lean", ret_ok));
    let clean_slice_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![ok_agree_case],
        Vec::new(),
    );
    let mut stale_ctx = TelemetryContext::discover(tmp.path());
    stale_ctx.build_freshness_override = Some(BuildFreshness::Stale);
    let mut stale_rec = SemanticDetailRecord::from_report_and_registry(
        &clean_slice_rep,
        &BugRegistry::new("google/zerocopy"),
        &stale_ctx,
    )
    .unwrap();
    assert_eq!(stale_rec.overall_status, "UNVERIFIED");
    assert_eq!(stale_rec.differential_runs[0].overall_status, "UNVERIFIED");

    stale_rec.evidence_blocks[0].overall_status = "PASS".to_string();
    assert!(stale_rec.validate_honesty().is_err());
    stale_rec.evidence_blocks[0].overall_status = "UNVERIFIED".to_string();
    stale_rec.differential_runs[0].overall_status = "PASS".to_string();
    assert!(stale_rec.validate_honesty().is_err());

    // 5. `needs_pinned_regen` inspects all pinned relations (not only the
    //    first), and `load_fuzz_programs_from_dir` rejects symlinked
    //    directories even with a trailing slash.
    #[cfg(unix)]
    {
        let real_seed_dir = tmp.path().join("real_seeds");
        fs::create_dir_all(&real_seed_dir).unwrap();
        let sym_seed_dir = tmp.path().join("sym_seeds");
        std::os::unix::fs::symlink(&real_seed_dir, &sym_seed_dir).unwrap();
        let trailing = std::path::PathBuf::from(format!("{}/", sym_seed_dir.display()));
        assert!(anneal_itree_diff::load_fuzz_programs_from_dir(&trailing).is_err());
    }

    let non_unw_prog = FuzzProgram {
        seed: 0x0912_0003,
        index: 0,
        input_x: 3,
        input_y: 4,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let mut non_unw_sr =
        shrink_fuzz_program_with_budget(&non_unw_prog, ShrinkBudget::default(), |p| {
            !p.steps.is_empty()
        });
    non_unw_sr.succeeded = true;
    non_unw_sr.is_one_minimal = true;
    non_unw_sr.converged_1_minimal = true;
    let two_rels_verdict = TraceVerdict::UnsoundAccept {
        detail: "metamorphic_duality: original multi-call rustc O0 vs O2 mismatch; source-inlined twin rustc O0 vs O2 mismatch".into(),
    };
    let mut w_missing_second = WitnessArtifact::from_shrink(
        "w_miss2",
        two_rels_verdict.clone(),
        two_rels_verdict.clone(),
        non_unw_sr,
    );
    w_missing_second.reproducer_rust_source = "// \"called_rustc_o0_vs_o2\" only".into();
    let mut meta2_rep = unw_rep;
    let meta_ret_ok = meta2_rep.miri.as_ref().unwrap().outcome.clone();
    meta2_rep.case_id = w_missing_second.case_id.clone();
    meta2_rep.verdict = two_rels_verdict.clone();
    meta2_rep.metamorphic = Some(MetamorphicDualityReceipt {
        called_lean: mk_auth("lean", meta_ret_ok.clone()),
        inlined_lean: mk_auth("lean", meta_ret_ok),
        inlined_rustc_parity_ok: false,
        inlined_miri_matched: Some(true),
        tool_error: None,
        status: MetamorphicStatus::Failed,
        duality_holds: false,
        detail: match &two_rels_verdict {
            TraceVerdict::UnsoundAccept { detail } => detail.clone(),
            _ => String::new(),
        },
        failed_relations: vec!["called_rustc_o0_vs_o2".into(), "inlined_rustc_o0_vs_o2".into()],
        twin_outcome_summary: "called_o0=returned,inlined_o0=returned".into(),
    });
    let mut reg = BugRegistry::new("google/zerocopy");
    let rec2 = reg.record_witness(
        &w_missing_second,
        &meta2_rep,
        "main",
        true,
        "v1",
        "cccccccccccccccccccccccccccccccccccccccc",
        None,
    );
    let bug_id2 = match rec2 {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("unexpected outcome: {other:?}"),
    };
    assert!(
        reg.buckets[&bug_id2].witnesses[0].repro_rust_source.contains("\"inlined_rustc_o0_vs_o2\"")
    );
}

#[test]
fn outcome_fingerprint_helper_separation_miri_isolation_and_shrinkable_lean_regression() {
    let tmp = tempfile::tempdir().unwrap();
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let unwound = TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) };
    let aborted = TerminalOutcome::Aborted { mem_digest: compute_boundary_mem_digest(&[]) };

    // 1. Non-UB `BugId`s separate distinct authority outcomes (`miri`, `o0`,
    //    `o2`, `lean`) across both `WitnessArtifact` and `ShrinkableCase`.
    let base_prog = FuzzProgram {
        seed: 0x1013_0001,
        index: 0,
        input_x: 3,
        input_y: 4,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let mut base_sr = shrink_fuzz_program_with_budget(&base_prog, ShrinkBudget::default(), |p| {
        !p.steps.is_empty()
    });
    base_sr.succeeded = true;
    base_sr.is_one_minimal = true;
    base_sr.converged_1_minimal = true;

    let mut rep_ret = mk_ub_case_report(
        "term_ret",
        "",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".into() },
    );
    rep_ret.rustc_dual = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth("rustc-o2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    rep_ret.miri = Some(mk_auth("miri", ret_ok.clone()));
    rep_ret.lean = Some(mk_auth("lean", unwound.clone()));

    let mut rep_unw = rep_ret.clone();
    rep_unw.case_id = "term_unw".into();
    rep_unw.rustc_dual.o0 = mk_auth("rustc-o0", unwound.clone());
    rep_unw.rustc_dual.o2 = mk_auth("rustc-o2", unwound.clone());
    rep_unw.miri = Some(mk_auth("miri", unwound.clone()));
    rep_unw.lean = Some(mk_auth("lean", ret_ok.clone()));

    let w_ret = WitnessArtifact::from_shrink(
        "w_ret",
        rep_ret.verdict.clone(),
        rep_ret.verdict.clone(),
        base_sr.clone(),
    );
    let w_unw = WitnessArtifact::from_shrink(
        "w_unw",
        rep_unw.verdict.clone(),
        rep_unw.verdict.clone(),
        base_sr.clone(),
    );
    let mut rep_ret_w = rep_ret.clone();
    rep_ret_w.case_id = w_ret.case_id.clone();
    let mut rep_unw_w = rep_unw.clone();
    rep_unw_w.case_id = w_unw.case_id.clone();
    let fp_ret =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_ret, &rep_ret_w, "main", "v1", None)
            .unwrap();
    let fp_unw =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_unw, &rep_unw_w, "main", "v1", None)
            .unwrap();
    assert_ne!(fp_ret.verdict_class, fp_unw.verdict_class);
    assert_ne!(fp_ret.bug_id(), fp_unw.bug_id());

    // `rustc O0 vs O2` defects where O2 aborts vs unwinds get distinct BugIds.
    let mut rep_o2_abort = rep_ret_w.clone();
    rep_o2_abort.verdict = TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".into() };
    rep_o2_abort.rustc_dual.o2 = mk_auth("rustc-o2", aborted.clone());
    rep_o2_abort.rustc_dual.parity_ok = false;
    rep_o2_abort.lean = Some(mk_auth("lean", ret_ok.clone()));

    let mut rep_o2_unwind = rep_o2_abort.clone();
    rep_o2_unwind.rustc_dual.o2 = mk_auth("rustc-o2", unwound.clone());
    let mut w_ret_o2 = w_ret.clone();
    w_ret_o2.verdict = rep_o2_abort.verdict.clone();

    let fp_o2_ab = CanonicalBugFingerprint::from_1_minimal_witness(
        &w_ret_o2,
        &rep_o2_abort,
        "main",
        "v1",
        None,
    )
    .unwrap();
    let fp_o2_un = CanonicalBugFingerprint::from_1_minimal_witness(
        &w_ret_o2,
        &rep_o2_unwind,
        "main",
        "v1",
        None,
    )
    .unwrap();
    assert_ne!(fp_o2_ab.verdict_class, fp_o2_un.verdict_class);
    assert_ne!(fp_o2_ab.bug_id(), fp_o2_un.bug_id());

    // 2. Explicit empty schedule override is preserved across JSON, `.rs`, and
    //    `.mir.lean`, while `None` stores the resolved default unwind schedule.
    let mut unw_prog = base_prog.clone();
    unw_prog.steps = vec![FuzzStep::UnwindProbe { trigger_unwind: true }];
    let mut unw_sr = shrink_fuzz_program_with_budget(&unw_prog, ShrinkBudget::default(), |p| {
        p.has_triggering_unwind()
    });
    unw_sr.succeeded = true;
    unw_sr.is_one_minimal = true;
    unw_sr.converged_1_minimal = true;

    let empty_sched = EnvSchedule::default();
    let w_empty_override = WitnessArtifact::from_shrink_with_schedule(
        "w_empty",
        rep_ret.verdict.clone(),
        rep_ret.verdict.clone(),
        unw_sr.clone(),
        Some(&empty_sched),
    );
    let b_empty = WitnessBundle::from_witness(w_empty_override, Some(&empty_sched));
    assert_eq!(b_empty.artifact.repro_schedule.as_ref(), Some(&empty_sched));
    assert!(
        !b_empty.repro_rust_source.contains("anneal_rt::push_callee_action")
            && !b_empty.repro_rust_source.contains("anneal_rt::push_global_action"),
        "explicit empty schedule must not inject default unwind into repro.rs"
    );
    assert!(
        b_empty.mir_lean_source.contains(
            "def reproEnvScheduleJson : String := \"{\\\"per_callee\\\":{},\\\"global\\\":[]}\""
        ),
        "lean={}",
        b_empty.mir_lean_source
    );

    let w_default_sched = WitnessArtifact::from_shrink_with_schedule(
        "w_default",
        rep_ret.verdict.clone(),
        rep_ret.verdict.clone(),
        unw_sr,
        None,
    );
    assert!(w_default_sched.repro_schedule.is_some());
    let b_default = WitnessBundle::from_witness(w_default_sched, None);
    assert!(
        b_default
            .artifact
            .repro_schedule
            .as_ref()
            .is_some_and(|s| s.per_callee.contains_key("fuzz_ext_unwind"))
    );
    assert!(
        b_default.repro_rust_source.contains("anneal_rt::push_callee_action(\"fuzz_ext_unwind\"")
    );
    assert!(b_default.mir_lean_source.contains("fuzz_ext_unwind"));
    assert_ne!(b_empty.bundle_id, b_default.bundle_id);

    // 3. `record_shrinkable_case` validates handles/helpers/inputs AND emits
    //    real typechecked `Trusted.MirAst.Program` Lean artifacts for lowerable
    //    cases while holding non-lowerable heap/layout cases provisional.
    let mut reg_sc = BugRegistry::new("google/zerocopy");
    let invalid_dup_helper = ShrinkableCase {
        name: "dup_helpers".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 5, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![
            ShrinkHelper {
                helper_id: 0,
                multiplier: 3,
                addend: 1,
                op: ShrinkHelperOp::AffineMulAdd,
            },
            ShrinkHelper {
                helper_id: 0,
                multiplier: 7,
                addend: 2,
                op: ShrinkHelperOp::AffineMulAdd,
            },
        ],
        steps: vec![ShrinkStep::HelperCall {
            dst_local: 3,
            helper_id: 0,
            block_id: 0,
            bias: 1,
            rhs_local: None,
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let sig_sc = ShrinkFailureSignature::from_case_report(&rep_ret).unwrap();
    let inv_out = reg_sc.record_shrinkable_case(
        &invalid_dup_helper,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "dddddddddddddddddddddddddddddddddddddddd",
        1,
        true,
    );
    assert!(matches!(inv_out, DedupRecordOutcome::Provisional { .. }));
    assert!(reg_sc.buckets.is_empty());

    let mut invalid_unbound = invalid_dup_helper.clone();
    invalid_unbound.name = "unbound_handle".into();
    invalid_unbound.helpers = Vec::new();
    invalid_unbound.steps = vec![ShrinkStep::UseHandle {
        handle: HandleId(99),
        offset: 0,
        len: 4,
        align: 1,
        local_id: 3,
    }];
    let unb_out = reg_sc.record_shrinkable_case(
        &invalid_unbound,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "dddddddddddddddddddddddddddddddddddddddd",
        1,
        true,
    );
    assert!(matches!(unb_out, DedupRecordOutcome::Provisional { .. }));

    let mut heap_wave2 = invalid_dup_helper.clone();
    heap_wave2.name = "heap_alloc_case".into();
    heap_wave2.helpers = Vec::new();
    heap_wave2.steps = vec![
        ShrinkStep::Alloc { handle: HandleId(0), size: 8, align: 4, local_id: 3 },
        ShrinkStep::UseHandle { handle: HandleId(0), offset: 0, len: 4, align: 4, local_id: 3 },
    ];
    let heap_out = reg_sc.record_shrinkable_case(
        &heap_wave2,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "dddddddddddddddddddddddddddddddddddddddd",
        1,
        true,
    );
    assert!(
        matches!(heap_out, DedupRecordOutcome::Provisional { .. }),
        "non-Lean-lowerable heap ShrinkableCase must remain Provisional"
    );
    assert!(reg_sc.buckets.is_empty());

    let mut unw_sc_sched = EnvSchedule::default();
    unw_sc_sched.push_callee("fuzz_ext_unwind", EnvAction::Unwind { message: "u".into() });
    let lowerable_sc = ShrinkableCase {
        name: "pure_cfg_helper_unwind".into(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 1, width: IntKind::U32, value: 9, align_hint: None },
            ShrinkInput { local_id: 2, width: IntKind::U8, value: 3, align_hint: None },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 4,
            multiplier: 5,
            addend: 11,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::BitAndMask, imm: 7 },
            ShrinkStep::HelperCall {
                dst_local: 3,
                helper_id: 4,
                block_id: 1,
                bias: 2,
                rhs_local: None,
            },
            ShrinkStep::BranchMix {
                block_id: 2,
                cond_local: 5,
                taken_then: true,
                dynamic_even_cond: false,
                then_steps: vec![ShrinkStep::ArithImm {
                    dst_local: 3,
                    op: FuzzArithOp::Add,
                    imm: 4,
                }],
                else_steps: vec![ShrinkStep::ArithImm {
                    dst_local: 2,
                    op: FuzzArithOp::Add,
                    imm: 1,
                }],
            },
            ShrinkStep::BoundedLoop {
                block_id: 5,
                iters: 2,
                induction: None,
                body: vec![ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Xor, imm: 1 }],
            },
            ShrinkStep::IfFalseDecoy {
                block_id: 8,
                body: vec![ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Sub, imm: 1 }],
            },
            ShrinkStep::UnwindProbe {
                callee: "fuzz_ext_unwind".into(),
                dst_local: 3,
                trigger_unwind: false,
                block_id: 10,
            },
        ],
        env_schedule: unw_sc_sched,
        return_local: 3,
    };
    let ok_out = reg_sc.record_shrinkable_case(
        &lowerable_sc,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "dddddddddddddddddddddddddddddddddddddddd",
        1,
        true,
    );
    let sc_bug_id = match ok_out {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug for lowerable ShrinkableCase, got {other:?}"),
    };
    let lean_src = &reg_sc.buckets[&sc_bug_id].witnesses[0].mir_lean_source;
    assert!(lean_src.contains("import Trusted.MirAst"));
    assert!(lean_src.contains("def reproProgram : Program"));
    assert!(lean_src.contains("#check reproProgram"));
    if let Some(lean_sess) = &engine.lean {
        let sc_lean_file = tmp.path().join("shrinkable_repro.mir.lean");
        fs::write(&sc_lean_file, lean_src).unwrap();
        let lp = lean_sess.lean_path_with(None).unwrap();
        let lean_out = Command::new(&lean_sess.lean_bin)
            .env("LEAN_PATH", lp)
            .arg(&sc_lean_file)
            .output()
            .unwrap();
        assert!(
            lean_out.status.success(),
            "generated ShrinkableCase .mir.lean failed Lean typecheck:\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&lean_out.stdout),
            String::from_utf8_lossy(&lean_out.stderr)
        );
    }

    // 4. `BugId` and `minimized_skeleton_hash` separate `fuzz_helper_{0,1,2}`
    //    while coalescing `callee_idx: 3` (`3 % 3 == 0`) with `fuzz_helper_0`.
    let mk_helper_witness = |id: &str, callee_idx: usize| -> (WitnessArtifact, String) {
        let mut p = base_prog.clone();
        p.steps = vec![FuzzStep::HelperCall { callee_idx, bias: 5 }];
        let target_h = callee_idx % 3;
        let mut sr = shrink_fuzz_program_with_budget(&p, ShrinkBudget::default(), |cand| {
            cand.steps.iter().any(
                |s| matches!(s, FuzzStep::HelperCall { callee_idx: c, .. } if c % 3 == target_h),
            )
        });
        sr.succeeded = true;
        sr.is_one_minimal = true;
        sr.converged_1_minimal = true;
        let w =
            WitnessArtifact::from_shrink(id, rep_ret.verdict.clone(), rep_ret.verdict.clone(), sr);
        let mut h_rep = rep_ret.clone();
        h_rep.case_id = id.to_string();
        let fp = CanonicalBugFingerprint::from_1_minimal_witness(&w, &h_rep, "main", "v1", None)
            .unwrap();
        (w, fp.bug_id())
    };
    let (w_h0, bid_h0) = mk_helper_witness("h0", 0);
    let (w_h1, bid_h1) = mk_helper_witness("h1", 1);
    let (w_h2, bid_h2) = mk_helper_witness("h2", 2);
    let (w_h3, bid_h3) = mk_helper_witness("h3", 3);
    assert_ne!(bid_h0, bid_h1);
    assert_ne!(bid_h0, bid_h2);
    assert_ne!(bid_h1, bid_h2);
    assert_eq!(bid_h0, bid_h3);
    assert_ne!(w_h0.minimized_skeleton_hash, w_h1.minimized_skeleton_hash);
    assert_ne!(w_h0.minimized_skeleton_hash, w_h2.minimized_skeleton_hash);
    assert_ne!(w_h1.minimized_skeleton_hash, w_h2.minimized_skeleton_hash);
    assert_eq!(w_h0.minimized_skeleton_hash, w_h3.minimized_skeleton_hash);

    let mut reg_helpers = BugRegistry::new("google/zerocopy");
    for w in [&w_h0, &w_h1, &w_h2] {
        let mut h_rep = rep_ret.clone();
        h_rep.case_id = w.case_id.clone();
        let out = reg_helpers.record_witness(
            w,
            &h_rep,
            "main",
            true,
            "v1",
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
            None,
        );
        assert!(matches!(out, DedupRecordOutcome::NewBug { .. }));
    }
    assert_eq!(reg_helpers.buckets.len(), 3);

    // 5. Non-aborting `miri_called_vs_inlined` standalone reproducer avoids
    //    unconditional `current_exe()` / `env::var_os` under default Miri
    //    isolation.
    let mut miri_meta_case = base_prog.to_trace_test_case();
    miri_meta_case.rust_arg_exprs = vec!["1u32".into(), "2u32".into()];
    miri_meta_case.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    miri_meta_case.env_schedule = EnvSchedule::default();
    miri_meta_case.pure_rust_source = "pub fn fuzz_entry(x: u32, _y: u32) -> u32 { x }\n".into();
    miri_meta_case.traced_rust_source = None;
    miri_meta_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, _y: u32) -> u32 { x }\n".into();
    let miri_repro_src = format!(
        "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &miri_meta_case,
            &["miri_called_vs_inlined".to_string()],
        )
    );
    let miri_rs = tmp.path().join("miri_non_abort_meta.rs");
    fs::write(&miri_rs, &miri_repro_src).unwrap();
    if let Some(miri_runner) = &engine.miri {
        let dylib_path =
            anneal_itree_diff::rustc_runner::join_dylib_path(&miri_runner.rust_sysroot.join("lib"));
        let miri_out = Command::new(&miri_runner.miri_bin)
            .env("LD_LIBRARY_PATH", dylib_path)
            .args(["--edition=2024", "--target", &miri_runner.target, "--sysroot"])
            .arg(&miri_runner.miri_sysroot)
            .args([
                "-C",
                "opt-level=0",
                "-C",
                "debug-assertions=no",
                "-C",
                "overflow-checks=no",
                "-Zmiri-tree-borrows",
            ])
            .arg(&miri_rs)
            .output()
            .unwrap();
        assert!(
            miri_out.status.success(),
            "non-aborting miri_called_vs_inlined reproducer must pass under strict Miri isolation:\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&miri_out.stdout),
            String::from_utf8_lossy(&miri_out.stderr)
        );
    }

    // 6. Distinct schema constant matches emitted `SemanticDetailRecord`.
    assert_eq!(SEMANTIC_DETAIL_SCHEMA, "anneal-itree-semantic-detail/v1");
}

#[test]
fn shrinkable_schedule_width_identity_alignment_and_two_arg_trace_parity() {
    let tmp = tempfile::tempdir().unwrap();
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let mut rep_ret = mk_ub_case_report(
        "sc_parity",
        "",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".into() },
    );
    rep_ret.miri = Some(mk_auth("miri", ret_ok.clone()));
    rep_ret.lean = Some(mk_auth(
        "lean",
        TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) },
    ));
    let sig_sc = ShrinkFailureSignature::from_case_report(&rep_ret).unwrap();

    // 1. `DropGuardWrapper` cases cannot be faithfully lowered without RAII
    //    cleanup modeling and must remain Provisional in `BugRegistry`.
    let drop_guard_sc = ShrinkableCase {
        name: "drop_guard_sc".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 4, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::DropGuardWrapper {
            local_id: 3,
            body: vec![ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Add, imm: 1 }],
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 3,
    };
    let mut reg = BugRegistry::new("google/zerocopy");
    let dg_out = reg.record_shrinkable_case(
        &drop_guard_sc,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "ffffffffffffffffffffffffffffffffffffffff",
        1,
        true,
    );
    assert!(
        matches!(dg_out, DedupRecordOutcome::Provisional { .. }),
        "DropGuardWrapper ShrinkableCase must remain Provisional: {dg_out:?}"
    );
    assert!(reg.buckets.is_empty());

    // 2. Mixed `fuzz_helper_0` + `h0` schedule keys fail closed (`Err`), while
    //    `fuzz_helper_0` schedule keys emit matching Lean `Body.identity`,
    //    non-64-bit `HelperCall` destination width (`u16`), non-32-bit
    //    `UnwindProbe` return width (`u16`), 2-arg `HelperCall` Rust trace
    //    recording, and exact live `repro.rs` vs `ITreeDriver` parity!
    let mut mixed_sched = EnvSchedule::default();
    mixed_sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![1, 0]));
    mixed_sched.push_callee("h0", EnvAction::ReturnBytes(vec![2, 0]));
    let mixed_sc = ShrinkableCase {
        name: "mixed_keys".into(),
        scalar_width: IntKind::U16,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U16, value: 5, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 3,
            addend: 7,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![ShrinkStep::HelperCall {
            dst_local: 1,
            helper_id: 0,
            block_id: 0,
            bias: 9,
            rhs_local: None,
        }],
        env_schedule: mixed_sched,
        return_local: 1,
    };
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&mixed_sc, "mix").is_err()
    );

    let mut sched_u16 = EnvSchedule::default();
    sched_u16.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![0x34, 0x12]));
    sched_u16.push_callee("fuzz_ext_unwind", EnvAction::ReturnBytes(vec![0x05, 0x00]));
    let sc_u16 = ShrinkableCase {
        name: "u16_sched_parity".into(),
        scalar_width: IntKind::U16,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U16, value: 9, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 3,
            addend: 7,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::HelperCall {
                dst_local: 1,
                helper_id: 0,
                block_id: 0,
                bias: 9,
                rhs_local: None,
            },
            ShrinkStep::UnwindProbe {
                callee: "fuzz_ext_unwind".into(),
                dst_local: 1,
                trigger_unwind: false,
                block_id: 1,
            },
        ],
        env_schedule: sched_u16,
        return_local: 1,
    };
    let rs_u16 = render_standalone_shrinkable_repro_rs(&sc_u16, "u16_parity");
    assert!(rs_u16.contains("capture_value_bytes(&_hc_a_"));
    assert!(rs_u16.contains("capture_value_bytes(&_hc_b_"));

    let rs_path = tmp.path().join("u16_parity.rs");
    let bin_path = tmp.path().join("u16_parity_bin");
    fs::write(&rs_path, &rs_u16).unwrap();
    let comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&rs_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .unwrap();
    assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    let run_rs = Command::new(&bin_path).output().unwrap();
    assert!(run_rs.status.success(), "{}", String::from_utf8_lossy(&run_rs.stderr));
    let parsed_rs = parse_trace_json_stdout_with_expected_args(
        "rustc-repro",
        &String::from_utf8_lossy(&run_rs.stdout),
        &String::from_utf8_lossy(&run_rs.stderr),
        1,
        Some(1),
    )
    .expect("parse u16 shrinkable rust repro trace");
    assert!(
        matches!(
            &parsed_rs.outcome,
            TerminalOutcome::Returned {
                ret: TraceVal::Scalar { kind: IntKind::U16, bits: 0x0005 },
                ..
            }
        ),
        "outcome={:?}",
        parsed_rs.outcome
    );
    let helper_enter = parsed_rs
        .spine
        .events
        .iter()
        .find_map(|ev| match ev {
            ObservableEvent::CallEnter { callee, arg_bytes, arg_reprs }
                if callee == "fuzz_helper_0" =>
            {
                Some((arg_bytes.clone(), arg_reprs.clone()))
            }
            _ => None,
        })
        .expect("scheduled fuzz_helper_0 CallEnter");
    assert_eq!(helper_enter.0.len(), 2, "must record both u64 helper args: {:?}", helper_enter);
    assert_eq!(helper_enter.1, vec!["9".to_string(), "9".to_string()]);
    let unwind_enter_rs = parsed_rs
        .spine
        .events
        .iter()
        .find_map(|ev| match ev {
            ObservableEvent::CallEnter { callee, arg_bytes, .. } if callee == "fuzz_ext_unwind" => {
                Some(arg_bytes.clone())
            }
            _ => None,
        })
        .expect("scheduled fuzz_ext_unwind CallEnter");
    assert_eq!(
        unwind_enter_rs,
        vec![vec![Some(0x34), Some(0x12)], vec![Some(0), Some(0), Some(0), Some(0)]],
        "UnwindProbe must forward current dst_local and trigger args: {:?}",
        unwind_enter_rs
    );

    let rec_u16 = reg.record_shrinkable_case(
        &sc_u16,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "ffffffffffffffffffffffffffffffffffffffff",
        1,
        true,
    );
    let bug_id_u16 = match rec_u16 {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug, got {other:?}"),
    };
    let lean_u16 = &reg.buckets[&bug_id_u16].witnesses[0].mir_lean_source;
    assert!(lean_u16.contains("identity := \"fuzz_helper_0\""));
    assert!(lean_u16.contains(".int .i16 false"));
    if let Some(lean_sess) = &engine.lean {
        let lp = lean_sess.lean_path_with(None).unwrap();
        let mir_p = tmp.path().join("u16_parity.mir.lean");
        fs::write(&mir_p, lean_u16).unwrap();
        let tc =
            Command::new(&lean_sess.lean_bin).env("LEAN_PATH", lp).arg(&mir_p).output().unwrap();
        assert!(tc.status.success(), "{}", String::from_utf8_lossy(&tc.stderr));

        let body_part = lean_u16
            .split("open Trusted.MirAst Trusted.MirSemantics\n\n")
            .nth(1)
            .unwrap()
            .replace("#check reproProgram\n", "");
        let driver_probe = format!(
            "import ITreeDriver\n\
             open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
             {body_part}\n\
             #eval IO.println (ITreeDriver.runTraceChecked reproProgram TraceMode.compositionalITree reproFuel (reproArgs.map Except.ok) \
             [(some \"fuzz_helper_0\", ITreeDriver.DriverEnvAction.returnBytes [52, 18]), \
              (some \"fuzz_ext_unwind\", ITreeDriver.DriverEnvAction.returnBytes [5, 0])] \
             reproExternalCallees)\n"
        );
        let parsed_lean = lean_sess.run_raw_driver_probe(&driver_probe, "lean-shrinkable-repro");
        assert!(parsed_lean.tool_error.is_none(), "{:?}", parsed_lean.tool_error);
        assert_eq!(parsed_lean.outcome, parsed_rs.outcome);
        assert_eq!(parsed_rs.spine.erased_call_spine(), parsed_lean.spine.erased_call_spine());
        assert!(parsed_lean.caller_frame_law.is_satisfied());
        assert!(!parsed_lean.spine.caller_frame_checks().is_empty());
        let unwind_enter_lean = parsed_lean
            .spine
            .events
            .iter()
            .find_map(|ev| match ev {
                ObservableEvent::CallEnter { callee, arg_bytes, .. }
                    if callee == "fuzz_ext_unwind" =>
                {
                    Some(arg_bytes.clone())
                }
                _ => None,
            })
            .expect("Lean fuzz_ext_unwind CallEnter");
        assert_eq!(
            unwind_enter_lean,
            vec![vec![Some(0x34), Some(0x12)], vec![Some(0), Some(0), Some(0), Some(0)]],
        );
    }

    // 2b. Unscheduled `UnwindProbe` lowers in both Rust and Lean with
    //     `dst_local` distinct from `return_local`, running `v.wrapping_add(1)`
    //     on `dst_local` and recording the 2-arg call spine cleanly.
    let unsched_unw = ShrinkableCase {
        name: "unsched_unwind_dst_local".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 40, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Add, imm: 10 },
            ShrinkStep::UnwindProbe {
                callee: "fuzz_ext_unwind".into(),
                dst_local: 3,
                trigger_unwind: false,
                block_id: 0,
            },
            ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Add, imm: 1 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 3,
    };
    let rs_unsched_unw = render_standalone_shrinkable_repro_rs(&unsched_unw, "unsched_unw");
    let rs_unsched_unw_path = tmp.path().join("unsched_unw.rs");
    let bin_unsched_unw_path = tmp.path().join("unsched_unw_bin");
    fs::write(&rs_unsched_unw_path, &rs_unsched_unw).unwrap();
    let comp_uu = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&rs_unsched_unw_path)
        .arg("-o")
        .arg(&bin_unsched_unw_path)
        .output()
        .unwrap();
    assert!(comp_uu.status.success(), "{}", String::from_utf8_lossy(&comp_uu.stderr));
    let run_uu = Command::new(&bin_unsched_unw_path).output().unwrap();
    assert!(run_uu.status.success(), "{}", String::from_utf8_lossy(&run_uu.stderr));
    let parsed_uu_rs = parse_trace_json_stdout_with_expected_args(
        "rustc-unsched-unw",
        &String::from_utf8_lossy(&run_uu.stdout),
        &String::from_utf8_lossy(&run_uu.stderr),
        1,
        Some(1),
    )
    .expect("parse unscheduled UnwindProbe rust trace");
    assert!(
        matches!(
            &parsed_uu_rs.outcome,
            TerminalOutcome::Returned {
                ret: TraceVal::Scalar { kind: IntKind::U32, bits: 12 },
                ..
            }
        ),
        "outcome={:?}",
        parsed_uu_rs.outcome
    );
    let lean_uu =
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&unsched_unw, "uu")
            .expect("lower unscheduled UnwindProbe to Lean");
    if let Some(lean_sess) = &engine.lean {
        let lp = lean_sess.lean_path_with(None).unwrap();
        let mir_p = tmp.path().join("unsched_unw.mir.lean");
        fs::write(&mir_p, &lean_uu).unwrap();
        let tc =
            Command::new(&lean_sess.lean_bin).env("LEAN_PATH", lp).arg(&mir_p).output().unwrap();
        assert!(tc.status.success(), "{}", String::from_utf8_lossy(&tc.stderr));
        let body_part = lean_uu
            .split("open Trusted.MirAst Trusted.MirSemantics\n\n")
            .nth(1)
            .unwrap()
            .replace("#check reproProgram\n", "");
        let driver_probe = format!(
            "import ITreeDriver\n\
             open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
             {body_part}\n\
             #eval IO.println (ITreeDriver.runTraceChecked reproProgram TraceMode.compositionalITree reproFuel (reproArgs.map Except.ok) [] reproExternalCallees)\n"
        );
        let parsed_uu_lean = lean_sess.run_raw_driver_probe(&driver_probe, "lean-unsched-unwind");
        assert!(parsed_uu_lean.tool_error.is_none(), "{:?}", parsed_uu_lean.tool_error);
        assert_eq!(parsed_uu_lean.outcome, parsed_uu_rs.outcome);
        assert_eq!(
            parsed_uu_rs.spine.erased_call_spine(),
            parsed_uu_lean.spine.erased_call_spine()
        );
        assert!(parsed_uu_lean.caller_frame_law.is_satisfied());
    }

    // 2c. Scheduled `UnwindProbe` updates only `dst_local` without perturbing
    //     a distinct `return_local`, matching across Rust and Lean.
    let mut nonret_sched = EnvSchedule::default();
    nonret_sched.push_callee("fuzz_ext_unwind", EnvAction::ReturnBytes(vec![7, 0, 0, 0]));
    let sched_nonret = ShrinkableCase {
        name: "sched_unwind_distinct_dst".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 40, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Add, imm: 10 },
            ShrinkStep::UnwindProbe {
                callee: "fuzz_ext_unwind".into(),
                dst_local: 3,
                trigger_unwind: false,
                block_id: 0,
            },
        ],
        env_schedule: nonret_sched,
        return_local: 1,
    };
    let rs_nonret = render_standalone_shrinkable_repro_rs(&sched_nonret, "sched_nonret");
    let rs_nonret_path = tmp.path().join("sched_nonret.rs");
    let bin_nonret_path = tmp.path().join("sched_nonret_bin");
    fs::write(&rs_nonret_path, &rs_nonret).unwrap();
    let comp_nr = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&rs_nonret_path)
        .arg("-o")
        .arg(&bin_nonret_path)
        .output()
        .unwrap();
    assert!(comp_nr.status.success(), "{}", String::from_utf8_lossy(&comp_nr.stderr));
    let run_nr = Command::new(&bin_nonret_path).output().unwrap();
    assert!(run_nr.status.success(), "{}", String::from_utf8_lossy(&run_nr.stderr));
    let parsed_nr_rs = parse_trace_json_stdout_with_expected_args(
        "rustc-nonret-unw",
        &String::from_utf8_lossy(&run_nr.stdout),
        &String::from_utf8_lossy(&run_nr.stderr),
        1,
        Some(1),
    )
    .expect("parse distinct-dst scheduled UnwindProbe rust trace");
    assert!(
        matches!(
            &parsed_nr_rs.outcome,
            TerminalOutcome::Returned {
                ret: TraceVal::Scalar { kind: IntKind::U32, bits: 40 },
                ..
            }
        ),
        "outcome={:?}",
        parsed_nr_rs.outcome
    );
    let lean_nr =
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&sched_nonret, "nr")
            .expect("lower distinct-dst scheduled UnwindProbe to Lean");
    if let Some(lean_sess) = &engine.lean {
        let body_part = lean_nr
            .split("open Trusted.MirAst Trusted.MirSemantics\n\n")
            .nth(1)
            .unwrap()
            .replace("#check reproProgram\n", "");
        let driver_probe = format!(
            "import ITreeDriver\n\
             open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
             {body_part}\n\
             #eval IO.println (ITreeDriver.runTraceChecked reproProgram TraceMode.compositionalITree reproFuel (reproArgs.map Except.ok) \
             [(some \"fuzz_ext_unwind\", ITreeDriver.DriverEnvAction.returnBytes [7, 0, 0, 0])] \
             reproExternalCallees)\n"
        );
        let parsed_nr_lean =
            lean_sess.run_raw_driver_probe(&driver_probe, "lean-nonret-sched-unwind");
        assert!(parsed_nr_lean.tool_error.is_none(), "{:?}", parsed_nr_lean.tool_error);
        assert_eq!(parsed_nr_lean.outcome, parsed_nr_rs.outcome);
        assert_eq!(
            parsed_nr_rs.spine.erased_call_spine(),
            parsed_nr_lean.spine.erased_call_spine()
        );
        assert!(parsed_nr_lean.caller_frame_law.is_satisfied());
    }

    // 3. `shrink_case_with_budget` narrows step `align` fields on `Alloc`,
    //    `SplitAt`, `UseHandle`, and `PairOffsetLen` to minimal power-of-two
    //    alignments.
    let over_aligned = ShrinkableCase {
        name: "over_aligned_steps".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::Alloc { handle: HandleId(0), size: 32, align: 16, local_id: 1 },
            ShrinkStep::SplitAt {
                left: HandleId(1),
                right: HandleId(2),
                src: HandleId(0),
                mid: 16,
                len: 32,
                align: 16,
            },
            ShrinkStep::UseHandle { handle: HandleId(1), offset: 8, len: 8, align: 8, local_id: 1 },
            ShrinkStep::PairOffsetLen { offset: 16, len: 8, align: 16, local_id: 1 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 1,
    };
    let shrunk = anneal_itree_diff::shrink::shrink_case_with_budget(
        &over_aligned,
        ShrinkBudget::default(),
        |cand| {
            cand.steps.len() == 4
                && matches!(cand.steps[0], ShrinkStep::Alloc { align, .. } if align >= 4)
                && matches!(cand.steps[1], ShrinkStep::SplitAt { align, .. } if align >= 2)
                && matches!(cand.steps[2], ShrinkStep::UseHandle { align, .. } if align >= 2)
                && matches!(cand.steps[3], ShrinkStep::PairOffsetLen { align, .. } if align >= 1)
        },
    );
    assert!(shrunk.is_one_minimal);
    assert!(matches!(shrunk.minimized.steps[0], ShrinkStep::Alloc { align: 4, .. }));
    assert!(matches!(shrunk.minimized.steps[1], ShrinkStep::SplitAt { align: 2, .. }));
    assert!(matches!(shrunk.minimized.steps[2], ShrinkStep::UseHandle { align: 2, .. }));
    assert!(matches!(shrunk.minimized.steps[3], ShrinkStep::PairOffsetLen { align: 1, .. }));

    // 4. Triggering `UnwindProbe { trigger_unwind: true }` is rejected cleanly
    //    from standalone Lean lowering into `Provisional` (with empty or
    //    sibling schedules), never promoting `.unsupported` vs `panic!("u")`.
    let trig_unwind_empty = ShrinkableCase {
        name: "trig_unwind_empty".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 7, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::UnwindProbe {
            callee: "fuzz_ext_unwind".into(),
            dst_local: 1,
            trigger_unwind: true,
            block_id: 0,
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 1,
    };
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
            &trig_unwind_empty,
            "triguw_empty",
        )
        .is_err()
    );
    let trig_out = reg.record_shrinkable_case(
        &trig_unwind_empty,
        &sig_sc,
        Some(&rep_ret.rustc_dual),
        rep_ret.miri.as_ref(),
        rep_ret.lean.as_ref(),
        "main",
        true,
        "v1",
        "ffffffffffffffffffffffffffffffffffffffff",
        1,
        true,
    );
    assert!(
        matches!(trig_out, DedupRecordOutcome::Provisional { .. }),
        "triggering UnwindProbe ShrinkableCase must remain Provisional: {trig_out:?}"
    );
    let mut sibling_sched = EnvSchedule::default();
    sibling_sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![1, 0, 0, 0]));
    let mut trig_unwind_sched = trig_unwind_empty;
    trig_unwind_sched.helpers = vec![ShrinkHelper {
        helper_id: 0,
        multiplier: 2,
        addend: 3,
        op: ShrinkHelperOp::AffineMulAdd,
    }];
    trig_unwind_sched.steps.insert(
        0,
        ShrinkStep::HelperCall {
            dst_local: 1,
            helper_id: 0,
            block_id: 1,
            bias: 1,
            rhs_local: None,
        },
    );
    trig_unwind_sched.env_schedule = sibling_sched;
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
            &trig_unwind_sched,
            "triguw_sched",
        )
        .is_err()
    );

    // 5. Multi-call `HelperCall` keeps `fuzz_helper_0` instrumentation across
    //    per-callee depletion -> `global` action -> empty-queue fallback, and
    //    matches live `ITreeDriver` outcome and `erased_call_spine`.
    let mut deplete_sched = EnvSchedule::default();
    deplete_sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![0x34, 0x12]));
    deplete_sched.push_global(EnvAction::ReturnBytes(vec![0x05, 0x00]));
    let deplete_sc = ShrinkableCase {
        name: "deplete_helper_trace".into(),
        scalar_width: IntKind::U16,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U16, value: 9, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 3,
            addend: 7,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::HelperCall {
                dst_local: 1,
                helper_id: 0,
                block_id: 0,
                bias: 2,
                rhs_local: None,
            },
            ShrinkStep::HelperCall {
                dst_local: 1,
                helper_id: 0,
                block_id: 1,
                bias: 4,
                rhs_local: None,
            },
            ShrinkStep::HelperCall {
                dst_local: 1,
                helper_id: 0,
                block_id: 2,
                bias: 6,
                rhs_local: None,
            },
        ],
        env_schedule: deplete_sched,
        return_local: 1,
    };
    let rs_deplete = render_standalone_shrinkable_repro_rs(&deplete_sc, "deplete_helper");
    assert_eq!(rs_deplete.matches("anneal_rt::handle_scheduled_call(\n").count(), 3);
    assert!(!rs_deplete.contains("\"h0\""));
    assert!(!rs_deplete.contains("l1 = h0("));

    let dep_rs_path = tmp.path().join("deplete_helper.rs");
    let dep_bin_path = tmp.path().join("deplete_helper_bin");
    fs::write(&dep_rs_path, &rs_deplete).unwrap();
    let dep_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&dep_rs_path)
        .arg("-o")
        .arg(&dep_bin_path)
        .output()
        .unwrap();
    assert!(dep_comp.status.success(), "{}", String::from_utf8_lossy(&dep_comp.stderr));
    let dep_run = Command::new(&dep_bin_path).output().unwrap();
    assert!(dep_run.status.success(), "{}", String::from_utf8_lossy(&dep_run.stderr));
    let parsed_dep_rs = parse_trace_json_stdout_with_expected_args(
        "rustc-repro-deplete",
        &String::from_utf8_lossy(&dep_run.stdout),
        &String::from_utf8_lossy(&dep_run.stderr),
        1,
        Some(1),
    )
    .expect("parse depleted helper rust repro trace");
    assert!(
        matches!(
            &parsed_dep_rs.outcome,
            TerminalOutcome::Returned {
                ret: TraceVal::Scalar { kind: IntKind::U16, bits: 28 },
                ..
            }
        ),
        "outcome={:?}",
        parsed_dep_rs.outcome
    );
    let helper_calls_rs = parsed_dep_rs
        .spine
        .events
        .iter()
        .filter(|ev| matches!(ev, ObservableEvent::CallEnter { callee, .. } if callee == "fuzz_helper_0"))
        .count();
    assert_eq!(
        helper_calls_rs, 3,
        "all 3 calls must emit fuzz_helper_0: {:?}",
        parsed_dep_rs.spine
    );

    let lean_dep =
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&deplete_sc, "deplete")
            .expect("lower deplete_sc to Lean");
    if let Some(lean_sess) = &engine.lean {
        let lp = lean_sess.lean_path_with(None).unwrap();
        let mir_p = tmp.path().join("deplete.mir.lean");
        fs::write(&mir_p, &lean_dep).unwrap();
        let tc =
            Command::new(&lean_sess.lean_bin).env("LEAN_PATH", lp).arg(&mir_p).output().unwrap();
        assert!(tc.status.success(), "{}", String::from_utf8_lossy(&tc.stderr));

        let body_part = lean_dep
            .split("open Trusted.MirAst Trusted.MirSemantics\n\n")
            .nth(1)
            .unwrap()
            .replace("#check reproProgram\n", "");
        let driver_probe = format!(
            "import ITreeDriver\n\
             open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
             {body_part}\n\
             #eval IO.println (ITreeDriver.runTraceChecked reproProgram TraceMode.compositionalITree reproFuel (reproArgs.map Except.ok) \
             [(some \"fuzz_helper_0\", ITreeDriver.DriverEnvAction.returnBytes [52, 18]), \
              (none, ITreeDriver.DriverEnvAction.returnBytes [5, 0])] \
             reproExternalCallees)\n"
        );
        let parsed_dep_lean = lean_sess.run_raw_driver_probe(&driver_probe, "lean-deplete-repro");
        assert!(parsed_dep_lean.tool_error.is_none(), "{:?}", parsed_dep_lean.tool_error);
        assert_eq!(parsed_dep_lean.outcome, parsed_dep_rs.outcome);
        assert_eq!(
            parsed_dep_rs.spine.erased_call_spine(),
            parsed_dep_lean.spine.erased_call_spine()
        );
        assert!(parsed_dep_lean.caller_frame_law.is_satisfied());
    }
}

#[test]
fn authority_leg_dedup_telemetry_honesty_helper_tracing_align_hint_and_paths() {
    let tmp = tempfile::tempdir().unwrap();
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Direct `rustc_o0_o2` `record_shrinkable_case` fingerprints distinguish
    //    O2 unwound vs aborted outcomes into separate `BugId`s and buckets.
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let dual_unwound = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) },
        ),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 outcome mismatch".into()),
    };
    let dual_aborted = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Aborted { mem_digest: compute_boundary_mem_digest(&[]) },
        ),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 outcome mismatch".into()),
    };
    let sig_o0_o2 = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "rustc_o0_o2",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let o0_o2_case = ShrinkableCase {
        name: "o0_o2_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let miri_ok = mk_auth("miri", ret_ok.clone());
    let lean_ok = mk_auth("lean", ret_ok.clone());
    let mut reg_dual = BugRegistry::new("google/zerocopy");
    let bid_uw = match reg_dual.record_shrinkable_case(
        &o0_o2_case,
        &sig_o0_o2,
        Some(&dual_unwound),
        Some(&miri_ok),
        Some(&lean_ok),
        "main",
        true,
        "v1",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        1,
        true,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug for O2 unwound: {other:?}"),
    };
    let bid_ab = match reg_dual.record_shrinkable_case(
        &o0_o2_case,
        &sig_o0_o2,
        Some(&dual_aborted),
        Some(&miri_ok),
        Some(&lean_ok),
        "main",
        true,
        "v1",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        1,
        true,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug for O2 aborted: {other:?}"),
    };
    assert_ne!(bid_uw, bid_ab);
    assert_eq!(reg_dual.buckets.len(), 2);

    // 2. Telemetry honesty rejects `UNVERIFIED`/invalid slice statuses under
    //    `PASS` parent and never emits slice `PASS` without both Miri and
    //    Lean (even when all cases are ConservativeOverApprox/DisclosedGap).
    let head_sha = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    let clean_ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: head_sha.into(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "unit-test".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some(head_sha.into()),
    };
    let agree_case = CaseReport {
        case_id: "agree_full".into(),
        category: CaseCategory::ScalarBitwise,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-o0", ret_ok.clone()),
            o2: mk_auth("rustc-o2", ret_ok.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(miri_ok.clone()),
        lean: Some(lean_ok.clone()),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let clean_pass_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![agree_case.clone()],
        Vec::new(),
    );
    let mut pass_rec = SemanticDetailRecord::from_report_and_registry(
        &clean_pass_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    assert_eq!(pass_rec.overall_status, "PASS");
    assert_eq!(pass_rec.differential_runs[0].overall_status, "PASS");

    let mut unverified_slice = pass_rec.clone();
    unverified_slice.differential_runs[0].overall_status = "UNVERIFIED".into();
    assert!(unverified_slice.validate_honesty().is_err());

    let mut bogus_slice = pass_rec.clone();
    bogus_slice.differential_runs[0].overall_status = "UNKNOWN".into();
    assert!(bogus_slice.validate_honesty().is_err());

    let mut missing_miri_leg = pass_rec.clone();
    missing_miri_leg.differential_runs[0].legs.retain(|l| l != "miri_tree_borrows");
    assert!(missing_miri_leg.validate_honesty().is_err());

    let mut no_runs_pass = pass_rec.clone();
    no_runs_pass.differential_runs.clear();
    assert!(no_runs_pass.validate_honesty().is_err());
    let no_runs_path = tmp.path().join("empty_runs_pass.jsonl");
    assert!(no_runs_pass.write_jsonl(&no_runs_path).is_err());
    assert!(!no_runs_path.exists());

    let mut zero_compared_pass = pass_rec.clone();
    zero_compared_pass.differential_runs[0].compared_count = 0;
    assert!(zero_compared_pass.validate_honesty().is_err());

    pass_rec.evidence_blocks[0].overall_status = "FAIL".into();
    pass_rec.overall_status = "FAIL".into();
    assert!(pass_rec.validate_honesty().is_err());

    // Genuine `corpus = PASS` alongside `fuzz = FAIL` validates cleanly.
    let mut fuzz_fail_case = agree_case.clone();
    fuzz_fail_case.case_id = "fuzz_s1_i000".into();
    fuzz_fail_case.category = CaseCategory::FuzzGenerated;
    fuzz_fail_case.verdict = TraceVerdict::UnsoundAccept { detail: "divergence".into() };
    let mixed_slice_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![agree_case.clone(), fuzz_fail_case],
        Vec::new(),
    );
    let mixed_slice_rec = SemanticDetailRecord::from_report_and_registry(
        &mixed_slice_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    assert_eq!(mixed_slice_rec.overall_status, "FAIL");
    assert_eq!(mixed_slice_rec.differential_runs[0].overall_status, "PASS");
    assert_eq!(mixed_slice_rec.differential_runs[1].overall_status, "FAIL");

    // Two-slice `require_miri = true` with `Agree` corpus and `DegradedNoMiri`
    // fuzz emits `corpus = PASS`, `fuzz = FAIL`, and passes `validate_honesty`.
    let mut fuzz_degraded_miri = agree_case.clone();
    fuzz_degraded_miri.case_id = "fuzz_s1_i001".into();
    fuzz_degraded_miri.category = CaseCategory::FuzzGenerated;
    fuzz_degraded_miri.verdict = TraceVerdict::DegradedNoMiri { detail: "miri unavailable".into() };
    fuzz_degraded_miri.miri = None;
    let degraded_fuzz_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![agree_case.clone(), fuzz_degraded_miri],
        Vec::new(),
    );
    let degraded_fuzz_rec = SemanticDetailRecord::from_report_and_registry(
        &degraded_fuzz_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    assert_eq!(degraded_fuzz_rec.overall_status, "FAIL");
    assert_eq!(degraded_fuzz_rec.differential_runs[0].overall_status, "PASS");
    assert_eq!(degraded_fuzz_rec.differential_runs[1].overall_status, "FAIL");

    // `--no-miri` (and `--require-miri` + `--no-miri`) with only
    // `DisclosedGapArtifact` / `ConservativeOverApprox` never emits slice
    // `PASS`.
    let mut no_miri_gap = agree_case.clone();
    no_miri_gap.case_id = "cat2_repr_c_padded_header".into();
    no_miri_gap.verdict = TraceVerdict::DisclosedGapArtifact {
        gap: anneal_itree_diff::outcome::DisclosedGapKind::CallerRawPtrAliasing,
        detail: "verified without miri".into(),
    };
    no_miri_gap.miri = None;
    for require_miri in [false, true] {
        let rep = DifferentialReport::from_cases(
            "disabled",
            false,
            require_miri,
            "unavailable",
            LeanTraceMode::CompositionalITree,
            vec![no_miri_gap.clone()],
            Vec::new(),
        );
        let rec = SemanticDetailRecord::from_report_and_registry(
            &rep,
            &BugRegistry::new("google/zerocopy"),
            &clean_ctx,
        )
        .unwrap();
        assert_eq!(rec.overall_status, if require_miri { "FAIL" } else { "UNVERIFIED" });
        assert_eq!(rec.differential_runs[0].overall_status, "UNVERIFIED");
    }

    // `--no-lean` with `ConservativeOverApprox` via `mir_eval` also stays
    // `UNVERIFIED`.
    let mut no_lean_overapprox = agree_case;
    no_lean_overapprox.verdict = TraceVerdict::ConservativeOverApprox {
        ub_refutation_disallowed: true,
        undeclared_ub_fault: false,
        reason: "mir_eval conservative overapprox".into(),
    };
    no_lean_overapprox.lean = None;
    no_lean_overapprox.mir_eval = Some(mk_auth("anneal-mir-eval", ret_ok));
    let no_lean_rep = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "available",
        LeanTraceMode::CompositionalITree,
        vec![no_lean_overapprox],
        Vec::new(),
    );
    let no_lean_rec = SemanticDetailRecord::from_report_and_registry(
        &no_lean_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    assert_eq!(no_lean_rec.overall_status, "UNVERIFIED");
    assert_eq!(no_lean_rec.differential_runs[0].overall_status, "UNVERIFIED");

    // 3. Unscheduled `ShrinkableCase` with `HelperCall` still traces
    //    `CallEnter`/`CallReturn` in Rust and matches Lean `.mir.lean` spine.
    let unsched_helper = ShrinkableCase {
        name: "unsched_helper".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 4, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 2,
            addend: 3,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![ShrinkStep::HelperCall {
            dst_local: 1,
            helper_id: 0,
            block_id: 0,
            bias: 5,
            rhs_local: None,
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 1,
    };
    let rs_unsched = render_standalone_shrinkable_repro_rs(&unsched_helper, "unsched_hc");
    assert!(rs_unsched.contains("anneal_rt::handle_scheduled_call"));
    let rs_u_path = tmp.path().join("unsched_hc.rs");
    let bin_u_path = tmp.path().join("unsched_hc_bin");
    fs::write(&rs_u_path, &rs_unsched).unwrap();
    let comp_u = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&rs_u_path)
        .arg("-o")
        .arg(&bin_u_path)
        .output()
        .unwrap();
    assert!(comp_u.status.success(), "{}", String::from_utf8_lossy(&comp_u.stderr));
    let run_u = Command::new(&bin_u_path).output().unwrap();
    assert!(run_u.status.success(), "{}", String::from_utf8_lossy(&run_u.stderr));
    let parsed_u_rs = parse_trace_json_stdout_with_expected_args(
        "rustc-repro",
        &String::from_utf8_lossy(&run_u.stdout),
        &String::from_utf8_lossy(&run_u.stderr),
        1,
        Some(1),
    )
    .expect("parse unscheduled helper trace");
    assert!(
        parsed_u_rs
            .spine
            .events
            .iter()
            .any(|ev| matches!(ev, ObservableEvent::CallEnter { callee, .. } if callee == "h0"))
    );
    assert!(
        parsed_u_rs
            .spine
            .events
            .iter()
            .any(|ev| matches!(ev, ObservableEvent::CallReturn { callee, .. } if callee == "h0"))
    );
    let lean_u = anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
        &unsched_helper,
        "unsched_hc",
    )
    .unwrap();
    if let Some(lean_sess) = &engine.lean {
        let body_part = lean_u
            .split("open Trusted.MirAst Trusted.MirSemantics\n\n")
            .nth(1)
            .unwrap()
            .replace("#check reproProgram\n", "");
        let driver_probe = format!(
            "import ITreeDriver\n\
             open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
             {body_part}\n\
             #eval IO.println (ITreeDriver.runTraceChecked reproProgram TraceMode.compositionalITree reproFuel (reproArgs.map Except.ok) [] reproExternalCallees)\n"
        );
        let parsed_u_lean = lean_sess.run_raw_driver_probe(&driver_probe, "lean-unsched-helper");
        assert!(parsed_u_lean.tool_error.is_none(), "{:?}", parsed_u_lean.tool_error);
        assert_eq!(parsed_u_lean.outcome, parsed_u_rs.outcome);
        assert_eq!(parsed_u_rs.spine.erased_call_spine(), parsed_u_lean.spine.erased_call_spine());
    }

    // 4. `ShrinkableCase` shrinking drops noncausal `align_hint` (permitting
    //    Lean promotion) and narrows causal `align_hint` to the minimum
    //    required power of two.
    let hinted_case = ShrinkableCase {
        name: "hinted_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: Some(16) },
            ShrinkInput { local_id: 1, width: IntKind::U32, value: 4, align_hint: Some(16) },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: Vec::new(),
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let noncausal_shrunk = anneal_itree_diff::shrink::shrink_case_with_budget(
        &ShrinkableCase { inputs: vec![hinted_case.inputs[0].clone()], ..hinted_case.clone() },
        ShrinkBudget::default(),
        |cand| cand.inputs.len() == 1,
    );
    assert!(noncausal_shrunk.is_one_minimal);
    assert_eq!(noncausal_shrunk.minimized.inputs[0].align_hint, None);
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
            &noncausal_shrunk.minimized,
            "noncausal_hint",
        )
        .is_ok()
    );

    let causal_shrunk = anneal_itree_diff::shrink::shrink_case_with_budget(
        &hinted_case,
        ShrinkBudget::default(),
        |cand| cand.inputs.len() == 2 && cand.inputs[1].align_hint.is_some_and(|a| a >= 4),
    );
    assert!(causal_shrunk.is_one_minimal);
    assert_eq!(causal_shrunk.minimized.inputs[0].align_hint, None);
    assert_eq!(causal_shrunk.minimized.inputs[1].align_hint, Some(4));

    // 5. `load_fuzz_programs_from_dir` preserves non-UTF-8 Unix path bytes when
    //    stripping trailing separators and still rejects trailing-slash
    //    symlinks.
    #[cfg(unix)]
    {
        use std::os::unix::ffi::{OsStrExt, OsStringExt};
        let mut raw_dir = tmp.path().as_os_str().as_bytes().to_vec();
        raw_dir.extend_from_slice(b"/seeds_\xff_dir");
        let non_utf8_dir = std::path::PathBuf::from(std::ffi::OsString::from_vec(raw_dir.clone()));
        fs::create_dir_all(&non_utf8_dir).unwrap();
        let prog = generate_fuzz_batch(0x1234_5678, 1).pop().unwrap();
        fs::write(non_utf8_dir.join("seed.json"), serde_json::to_string(&prog).unwrap()).unwrap();
        let mut raw_with_slash = raw_dir.clone();
        raw_with_slash.push(b'/');
        let dir_with_slash = std::path::PathBuf::from(std::ffi::OsString::from_vec(raw_with_slash));
        let loaded = anneal_itree_diff::load_fuzz_programs_from_dir(&dir_with_slash)
            .expect("non-UTF-8 dir with trailing slash must load seeds losslessly");
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].seed, prog.seed);

        let mut sym_raw = tmp.path().as_os_str().as_bytes().to_vec();
        sym_raw.extend_from_slice(b"/sym_\xff_link");
        let sym_path = std::path::PathBuf::from(std::ffi::OsString::from_vec(sym_raw.clone()));
        std::os::unix::fs::symlink(&non_utf8_dir, &sym_path).unwrap();
        sym_raw.push(b'/');
        let sym_with_slash = std::path::PathBuf::from(std::ffi::OsString::from_vec(sym_raw));
        assert!(anneal_itree_diff::load_fuzz_programs_from_dir(&sym_with_slash).is_err());
    }
}

#[test]
fn cross_mode_shrinkable_repro_multi_width_helpers_spine_classification_and_unwind_flag() {
    let tmp = tempfile::tempdir().unwrap();
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Helper-free `rustc_o0_o2` direct `ShrinkableCase` promotes a witness
    //    whose Rust repro emits `ANNEAL_ITREE_TRACE_JSON:` under
    //    `--anneal-single-run`, fails closed alone, and checks peers via
    //    `--compare-opt`.
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let dual_unwound = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) },
        ),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 outcome mismatch".into()),
    };
    let sig_o0_o2 = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "rustc_o0_o2",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let helper_free_o0_o2 = ShrinkableCase {
        name: "helper_free_o0_o2".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 99, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let miri_ok = mk_auth("miri", ret_ok.clone());
    let lean_ok = mk_auth("lean", ret_ok.clone());
    let mut reg_xmode = BugRegistry::new("google/zerocopy");
    let bid_xmode = match reg_xmode.record_shrinkable_case(
        &helper_free_o0_o2,
        &sig_o0_o2,
        Some(&dual_unwound),
        Some(&miri_ok),
        Some(&lean_ok),
        "main",
        true,
        "v1",
        "cccccccccccccccccccccccccccccccccccccccc",
        1,
        true,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug for helper-free rustc_o0_o2: {other:?}"),
    };
    let xmode_src = &reg_xmode.buckets[&bid_xmode].witnesses[0].repro_rust_source;
    assert!(xmode_src.contains("--compare-opt"));
    assert!(xmode_src.contains("--anneal-single-run"));

    let xmode_rs = tmp.path().join("xmode.rs");
    let xmode_div_rs = tmp.path().join("xmode_div.rs");
    let xmode_bin = tmp.path().join("xmode_o0");
    let xmode_div_bin = tmp.path().join("xmode_div");
    fs::write(&xmode_rs, xmode_src).unwrap();
    fs::write(&xmode_div_rs, xmode_src.replacen("99u32", "100u32", 2)).unwrap();
    for (src, bin) in [(&xmode_rs, &xmode_bin), (&xmode_div_rs, &xmode_div_bin)] {
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
            .arg(src)
            .arg("-o")
            .arg(bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    }
    assert!(
        !Command::new(&xmode_bin).output().unwrap().status.success(),
        "rustc_o0_o2 shrinkable repro must fail closed without peer"
    );
    let single_run = Command::new(&xmode_bin).arg("--anneal-single-run").output().unwrap();
    assert!(single_run.status.success());
    let single_parsed = parse_trace_json_stdout_with_expected_args(
        "rustc-single",
        &String::from_utf8_lossy(&single_run.stdout),
        &String::from_utf8_lossy(&single_run.stderr),
        1,
        Some(1),
    )
    .expect("single-run must emit valid trace JSON");
    assert!(matches!(
        single_parsed.outcome,
        TerminalOutcome::Returned { ret: TraceVal::Scalar { kind: IntKind::U32, bits: 100 }, .. }
    ));
    assert!(
        Command::new(&xmode_bin)
            .args(["--compare-opt"])
            .arg(&xmode_bin)
            .output()
            .unwrap()
            .status
            .success()
    );
    let cmp_div =
        Command::new(&xmode_bin).args(["--compare-opt"]).arg(&xmode_div_bin).output().unwrap();
    assert!(!cmp_div.status.success(), "--compare-opt must fail on cross-mode outcome divergence");
    assert!(
        String::from_utf8_lossy(&cmp_div.stderr).contains("rustc O0 vs O2 cross-mode divergence"),
        "stderr={}",
        String::from_utf8_lossy(&cmp_div.stderr)
    );

    // 2. Unscheduled multi-width `ShrinkableCase` helper calls emit identical
    //    suffixed callees (`h0_u8`, `h0_u16`) in Rust and Lean `.mir.lean`.
    let multi_w_case = ShrinkableCase {
        name: "multi_width_unsched".into(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 1, width: IntKind::U8, value: 3, align_hint: None },
            ShrinkInput { local_id: 2, width: IntKind::U16, value: 5, align_hint: None },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 2,
            addend: 1,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::HelperCall {
                dst_local: 1,
                helper_id: 0,
                block_id: 0,
                bias: 4,
                rhs_local: None,
            },
            ShrinkStep::HelperCall {
                dst_local: 2,
                helper_id: 0,
                block_id: 1,
                bias: 6,
                rhs_local: None,
            },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 2,
    };
    let sig_ret_mis = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "unwound",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "unwound".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let lean_uw =
        mk_auth("lean", TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) });
    let dual_mw_ok = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth("rustc-o2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let mut reg_mw = BugRegistry::new("google/zerocopy");
    let bid_mw = match reg_mw.record_shrinkable_case(
        &multi_w_case,
        &sig_ret_mis,
        Some(&dual_mw_ok),
        Some(&miri_ok),
        Some(&lean_uw),
        "main",
        true,
        "v1",
        "dddddddddddddddddddddddddddddddddddddddd",
        1,
        true,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug for multi-width unscheduled helper: {other:?}"),
    };
    let mw_rs = &reg_mw.buckets[&bid_mw].witnesses[0].repro_rust_source;
    let mw_lean = &reg_mw.buckets[&bid_mw].witnesses[0].mir_lean_source;
    assert!(mw_rs.contains("\"h0_u8\""));
    assert!(mw_rs.contains("\"h0_u16\""));
    assert!(mw_lean.contains("identity := \"h0_u8\""));
    assert!(mw_lean.contains("identity := \"h0_u16\""));

    let mw_rs_path = tmp.path().join("mw.rs");
    let mw_bin_path = tmp.path().join("mw_bin");
    fs::write(&mw_rs_path, mw_rs).unwrap();
    let mw_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no", "-C", "debug-assertions=no"])
        .arg(&mw_rs_path)
        .arg("-o")
        .arg(&mw_bin_path)
        .output()
        .unwrap();
    assert!(mw_comp.status.success(), "{}", String::from_utf8_lossy(&mw_comp.stderr));
    let mw_run = Command::new(&mw_bin_path).output().unwrap();
    assert!(mw_run.status.success(), "{}", String::from_utf8_lossy(&mw_run.stderr));
    let mw_parsed_rs = parse_trace_json_stdout_with_expected_args(
        "rustc-mw",
        &String::from_utf8_lossy(&mw_run.stdout),
        &String::from_utf8_lossy(&mw_run.stderr),
        2,
        Some(2),
    )
    .expect("parse multi-width rust trace");
    if let Some(lean_sess) = &engine.lean {
        let body_part = mw_lean
            .split("open Trusted.MirAst Trusted.MirSemantics\n\n")
            .nth(1)
            .unwrap()
            .replace("#check reproProgram\n", "");
        let driver_probe = format!(
            "import ITreeDriver\n\
             open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
             {body_part}\n\
             #eval IO.println (ITreeDriver.runTraceChecked reproProgram TraceMode.compositionalITree reproFuel (reproArgs.map Except.ok) [] reproExternalCallees)\n"
        );
        let mw_parsed_lean = lean_sess.run_raw_driver_probe(&driver_probe, "lean-mw-repro");
        assert!(mw_parsed_lean.tool_error.is_none(), "{:?}", mw_parsed_lean.tool_error);
        assert_eq!(mw_parsed_lean.outcome, mw_parsed_rs.outcome);
        assert_eq!(
            mw_parsed_rs.spine.erased_call_spine(),
            mw_parsed_lean.spine.erased_call_spine()
        );
    }

    // 3. Equal-outcome `compare_spines` divergences under `rustc O0 vs O2` and
    //    `miri vs rustc-O0` classify as `"spine_mismatch"` under
    //    `unsound_missed_fault_count`, never `value_mismatch_count`.
    let head_sha = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    let clean_ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: head_sha.into(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "unit-test".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some(head_sha.into()),
    };
    let ev_a = ObservableEvent::CallEnter {
        callee: "a".into(),
        arg_bytes: Vec::new(),
        arg_reprs: Vec::new(),
    };
    let ev_b = ObservableEvent::CallEnter {
        callee: "b".into(),
        arg_bytes: Vec::new(),
        arg_reprs: Vec::new(),
    };
    let mk_eq_outcome_spine = |id: &str,
                               detail: &str,
                               o0_events: Vec<ObservableEvent>,
                               o2_events: Vec<ObservableEvent>,
                               o0_o2_parity: bool,
                               miri_events: Vec<ObservableEvent>,
                               lean_events: Vec<ObservableEvent>| {
        let mut o0 = mk_auth("rustc-o0", ret_ok.clone());
        o0.spine.events = o0_events;
        let mut o2 = mk_auth("rustc-o2", ret_ok.clone());
        o2.spine.events = o2_events;
        let mut miri_leg = miri_ok.clone();
        miri_leg.spine.events = miri_events;
        let mut lean_leg = lean_ok.clone();
        lean_leg.spine.events = lean_events;
        CaseReport {
            case_id: id.into(),
            category: CaseCategory::FuzzGenerated,
            expected_class: ExpectedCaseClass::Agree,
            verdict: TraceVerdict::UnsoundAccept { detail: detail.into() },
            expectation_violation: None,
            rustc_dual: RustcDualResult {
                o0,
                o2,
                parity_ok: o0_o2_parity,
                skipped_for_ub: false,
                mismatch_detail: (!o0_o2_parity).then(|| detail.into()),
            },
            miri: Some(miri_leg),
            lean: Some(lean_leg),
            lean_strict_probe: None,
            mir_eval: None,
            metamorphic: None,
        }
    };
    let c_o0_o2_spine = mk_eq_outcome_spine(
        "o0_o2_sp",
        "rustc O0 vs O2: spine mismatch: event count mismatch",
        vec![ev_a.clone()],
        Vec::new(),
        false,
        vec![ev_a.clone()],
        vec![ev_a.clone()],
    );
    let c_miri_sp = mk_eq_outcome_spine(
        "miri_sp",
        "miri vs rustc-O0: event interleaving mismatch at 0",
        vec![ev_a.clone()],
        vec![ev_a.clone()],
        true,
        vec![ev_b.clone()],
        vec![ev_b.clone()],
    );
    let c_eq_o0_o2 = mk_eq_outcome_spine(
        "eq_sp",
        "rustc O0 vs O2 mismatch",
        vec![ev_a.clone()],
        vec![ev_b.clone()],
        false,
        vec![ev_a.clone()],
        vec![ev_a.clone()],
    );
    let c_miri_lean_sp = mk_eq_outcome_spine(
        "miri_lean_sp",
        "full call spine mismatch: miri=[\"ENTER:a\"] vs lean=[\"ENTER:b\"]",
        vec![ev_a.clone()],
        vec![ev_a.clone()],
        true,
        vec![ev_a],
        vec![ev_b],
    );
    for (c, expected_rel) in [
        (&c_o0_o2_spine, "rustc_o0_vs_o2"),
        (&c_miri_sp, "miri_vs_rustc_o0"),
        (&c_eq_o0_o2, "rustc_o0_vs_o2"),
        (&c_miri_lean_sp, "miri_vs_lean"),
    ] {
        let sig = ShrinkFailureSignature::from_case_report(c).unwrap();
        assert_eq!(sig.mismatch_category, "spine_mismatch");
        assert_eq!(sig.spine_relation.as_deref(), Some(expected_rel));
    }
    let mut spine_rel_reg = BugRegistry::new("google/zerocopy");
    let mut spine_bug_ids = std::collections::BTreeSet::new();
    for c in [&c_o0_o2_spine, &c_miri_sp, &c_miri_lean_sp] {
        let sig = ShrinkFailureSignature::from_case_report(c).unwrap();
        match spine_rel_reg.record_shrinkable_case(
            &helper_free_o0_o2,
            &sig,
            Some(&c.rustc_dual),
            c.miri.as_ref(),
            c.lean.as_ref(),
            "main",
            true,
            "v1",
            head_sha,
            1,
            true,
        ) {
            DedupRecordOutcome::NewBug { bug_id, .. } => {
                spine_bug_ids.insert(bug_id);
            }
            other => panic!("expected distinct spine bucket, got {other:?}"),
        }
    }
    assert_eq!(spine_bug_ids.len(), 3, "spine relations must not coalesce");
    let spine_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![c_o0_o2_spine, c_miri_sp, c_eq_o0_o2],
        Vec::new(),
    );
    let spine_detail = SemanticDetailRecord::from_report_and_registry(
        &spine_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    assert_eq!(spine_detail.differential_runs[0].value_mismatch_count, 0);
    assert_eq!(spine_detail.differential_runs[0].unsound_missed_fault_count, 3);

    // 4. Shrinking minimizes noncausal `UnwindProbe::trigger_unwind = true` ->
    //    `false` before declaring 1-minimality, permitting Lean promotion.
    let trig_noncausal = ShrinkableCase {
        name: "trig_noncausal".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::UnwindProbe {
            callee: "fuzz_ext_unwind".into(),
            dst_local: 0,
            trigger_unwind: true,
            block_id: 0,
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let shrunk_unw = anneal_itree_diff::shrink::shrink_case_with_budget(
        &trig_noncausal,
        ShrinkBudget::default(),
        |cand| cand.steps.iter().any(|s| matches!(s, ShrinkStep::UnwindProbe { .. })),
    );
    assert!(shrunk_unw.is_one_minimal);
    assert!(matches!(
        shrunk_unw.minimized.steps.as_slice(),
        [ShrinkStep::UnwindProbe { trigger_unwind: false, .. }]
    ));
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
            &shrunk_unw.minimized,
            "shrunk_unw_false",
        )
        .is_ok()
    );

    // 5. Standalone cross-mode metamorphic reproducers catch spine-only
    //    `called_rustc_o0_vs_o2` and `inlined_rustc_o0_vs_o2` divergences
    //    (honoring `ObsErasedCallsOnly` vs `FullBranchesAndCalls`) without
    //    breaking valid `called` vs `inlined` pairs whose call spines differ.
    let mut spine_called_case =
        generate_fuzz_batch(0x0918_0001, 1).pop().unwrap().to_trace_test_case();
    spine_called_case.rust_arg_exprs = vec!["1u32".into(), "2u32".into()];
    spine_called_case.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    spine_called_case.env_schedule = EnvSchedule::default();
    spine_called_case.spine_mode = SpineCompareMode::ObsErasedCallsOnly;
    spine_called_case.traced_rust_source = None;
    spine_called_case.pure_rust_source = "pub fn fuzz_entry(x: u32, y: u32) -> u32 {\n\
         \x20   if cfg!(debug_assertions) {\n\
         \x20       crate::anneal_rt::emit_call_enter(\"sp_h\", &[], &[]);\n\
         \x20       crate::anneal_rt::emit_call_return(\"sp_h\", &[], \"()\");\n\
         \x20   }\n\
         \x20   x.wrapping_add(y)\n\
         }\n"
    .to_string();
    spine_called_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, y: u32) -> u32 {\n\
         \x20   x.wrapping_add(y)\n\
         }\n"
        .to_string();

    let sp_called_rs = tmp.path().join("sp_called.rs");
    let sp_called_o0 = tmp.path().join("sp_called_o0");
    let sp_called_o2 = tmp.path().join("sp_called_o2");
    fs::write(
        &sp_called_rs,
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &spine_called_case,
            &["called_rustc_o0_vs_o2".to_string()],
        ),
    )
    .unwrap();
    for (extra, out_bin) in [
        (&["-C", "debug-assertions=yes"][..], &sp_called_o0),
        (&["-C", "opt-level=2", "-C", "debug-assertions=no"][..], &sp_called_o2),
    ] {
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .args(extra)
            .arg(&sp_called_rs)
            .arg("-o")
            .arg(out_bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    }
    let sp_called_cmp =
        Command::new(&sp_called_o0).args(["--compare-opt"]).arg(&sp_called_o2).output().unwrap();
    assert!(
        !sp_called_cmp.status.success(),
        "called_rustc_o0_vs_o2 repro must reject call-spine-only divergence"
    );
    assert!(
        String::from_utf8_lossy(&sp_called_cmp.stderr).contains("called_rustc_o0_vs_o2"),
        "stderr={}",
        String::from_utf8_lossy(&sp_called_cmp.stderr)
    );

    // Identical outcomes across `called` and `inlined` (with different call
    // events) must still pass self-vs-self comparison under `--compare-opt`.
    let sp_same_cmp =
        Command::new(&sp_called_o0).args(["--compare-opt"]).arg(&sp_called_o0).output().unwrap();
    assert!(
        sp_same_cmp.status.success(),
        "matching O0-vs-O0 with different called vs inlined spines must pass: {}",
        String::from_utf8_lossy(&sp_same_cmp.stderr)
    );

    // Same-return `inlined_rustc_o0_vs_o2` branch-spine divergence is ignored
    // in `ObsErasedCallsOnly` and caught in `FullBranchesAndCalls`.
    let mut sp_inlined_case = spine_called_case;
    sp_inlined_case.pure_rust_source = "pub fn fuzz_entry(x: u32, y: u32) -> u32 {\n\
         \x20   x.wrapping_add(y)\n\
         }\n"
    .to_string();
    sp_inlined_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, y: u32) -> u32 {\n\
         \x20   if cfg!(debug_assertions) {\n\
         \x20       crate::anneal_rt::emit_branch(0, \"true\", 1);\n\
         \x20   } else {\n\
         \x20       crate::anneal_rt::emit_branch(0, \"false\", 2);\n\
         \x20   }\n\
         \x20   x.wrapping_add(y)\n\
         }\n"
        .to_string();
    for (mode, expect_pass) in [
        (SpineCompareMode::ObsErasedCallsOnly, true),
        (SpineCompareMode::FullBranchesAndCalls, false),
    ] {
        sp_inlined_case.spine_mode = mode;
        let tag = if expect_pass { "erased" } else { "full" };
        let rs_p = tmp.path().join(format!("sp_inl_{tag}.rs"));
        let o0_p = tmp.path().join(format!("sp_inl_{tag}_o0"));
        let o2_p = tmp.path().join(format!("sp_inl_{tag}_o2"));
        fs::write(
            &rs_p,
            anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
                &sp_inlined_case,
                &["inlined_rustc_o0_vs_o2".to_string()],
            ),
        )
        .unwrap();
        for (extra, out_bin) in [
            (&["-C", "debug-assertions=yes"][..], &o0_p),
            (&["-C", "opt-level=2", "-C", "debug-assertions=no"][..], &o2_p),
        ] {
            let comp = Command::new(&engine.rustc.rustc_bin)
                .args(["--edition", "2024", "-C", "overflow-checks=no"])
                .args(extra)
                .arg(&rs_p)
                .arg("-o")
                .arg(out_bin)
                .output()
                .unwrap();
            assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
        }
        let res = Command::new(&o0_p).args(["--compare-opt"]).arg(&o2_p).output().unwrap();
        assert_eq!(
            res.status.success(),
            expect_pass,
            "mode={mode:?} stderr={}",
            String::from_utf8_lossy(&res.stderr)
        );
    }

    // 6. Noncausal `slice_len` (including `Some(0)`) shrinks to `None` before
    //    declaring 1-minimality, permitting Lean lowering.
    for init_len in [24usize, 0usize] {
        let noncausal_slice = ShrinkableCase {
            name: format!("noncausal_slice_{init_len}"),
            scalar_width: IntKind::U32,
            inputs: vec![ShrinkInput {
                local_id: 0,
                width: IntKind::U32,
                value: 1,
                align_hint: None,
            }],
            struct_fields: Vec::new(),
            slice_len: Some(init_len),
            slice_align: 16,
            helpers: Vec::new(),
            steps: Vec::new(),
            env_schedule: EnvSchedule::default(),
            return_local: 0,
        };
        let shrunk_slice = anneal_itree_diff::shrink::shrink_case_with_budget(
            &noncausal_slice,
            ShrinkBudget::default(),
            |cand| !cand.inputs.is_empty(),
        );
        assert!(shrunk_slice.is_one_minimal);
        assert_eq!(shrunk_slice.minimized.slice_len, None);
        assert_eq!(shrunk_slice.minimized.slice_align, 1);
        assert!(
            anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
                &shrunk_slice.minimized,
                &format!("noncausal_slice_{init_len}"),
            )
            .is_ok()
        );
    }
}

#[test]
fn r21_ub_buckets_arith_norm_parity_count_and_auth_signature() {
    let tmp = tempfile::tempdir().unwrap();
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(1),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ub_o0_ok = RustcDualResult::skipped_for_ub("expected UB");

    // 1. Expected-UB acceptance without Miri and UB entry-input digest
    //    errors must map to UB fault categories (`missed_ub` /
    //    `ub_cause_mismatch`) and ignore trailing `; secondary ...` notes.
    let exp_ub_rep = CaseReport {
        case_id: "exp_ub_acc".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        verdict: TraceVerdict::UnsoundAccept {
            detail: "expected-UB case accepted by lean (Returned) \
                     while Miri was unavailable; secondary rustc O0 vs O2"
                .into(),
        },
        expectation_violation: None,
        rustc_dual: ub_o0_ok.clone(),
        miri: None,
        lean: Some(mk_auth("lean-compositional-itree", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let exp_ub_sig = ShrinkFailureSignature::from_case_report(&exp_ub_rep).unwrap();
    assert_eq!(exp_ub_sig.mismatch_category, "missed_ub");

    let mut entry_dig_rep = mk_ub_case_report(
        "ub_dig",
        "Undefined Behavior: division by zero",
        TerminalOutcome::FaultUb { detail: "divide by zero".into() },
        TraceVerdict::UnsoundAccept {
            detail: "UB entry-input boundary digest mismatch: miri (aa) \
                     vs lean (bb); secondary miri vs rustc-O0"
                .into(),
        },
    );
    let entry_dig_sig = ShrinkFailureSignature::from_case_report(&entry_dig_rep).unwrap();
    assert_eq!(entry_dig_sig.mismatch_category, "ub_cause_mismatch");

    entry_dig_rep.verdict = TraceVerdict::UnsoundAccept {
        detail: "UB fault missing authenticated entry-input digest on \
                 one authority: miri=Some(\"aa\") vs lean=None"
            .into(),
    };
    let miss_dig_sig = ShrinkFailureSignature::from_case_report(&entry_dig_rep).unwrap();
    assert_eq!(miss_dig_sig.mismatch_category, "ub_cause_mismatch");

    let ub_rep_comb = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![exp_ub_rep.clone(), entry_dig_rep.clone()],
        Vec::new(),
    );
    let ub_ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: "1111111111111111111111111111111111111111".into(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "test".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some("1111111111111111111111111111111111111111".into()),
    };
    let ub_detail = SemanticDetailRecord::from_report_and_registry(
        &ub_rep_comb,
        &BugRegistry::new("google/zerocopy"),
        &ub_ctx,
    )
    .unwrap();
    assert_eq!(ub_detail.differential_runs[0].unsound_missed_fault_count, 2);
    assert_eq!(ub_detail.differential_runs[0].value_mismatch_count, 0);

    // 2. Non-causal `Sub 0`, `Xor 0`, `BitOr 0` normalize to `Add 0` before
    //    1-minimal convergence (both `FuzzProgram` and `ShrinkableCase`).
    let mut base_fp = generate_fuzz_batch(0x2100_0001, 1).pop().unwrap();
    let mut sub_prog = base_fp.clone();
    sub_prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Sub, imm: 17 }];
    let mut xor_prog = base_fp.clone();
    xor_prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Xor, imm: 9 }];
    let mut or_prog = base_fp.clone();
    or_prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::BitOr, imm: 5 }];
    for p in [&sub_prog, &xor_prog, &or_prog] {
        let sr = shrink_fuzz_program_with_budget(p, ShrinkBudget::default(), |cand| {
            cand.steps.len() == 1
        });
        assert!(sr.is_one_minimal);
        assert_eq!(sr.minimized.steps, vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 0 }]);
    }
    base_fp.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 0 }];
    let canon_case = ShrinkableCase {
        name: "norm_op".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Xor, imm: 11 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let canon_case_sr = anneal_itree_diff::shrink::shrink_case_with_budget(
        &canon_case,
        ShrinkBudget::default(),
        |c| c.steps.len() == 1,
    );
    assert!(canon_case_sr.is_one_minimal);
    assert_eq!(
        canon_case_sr.minimized.steps,
        vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 0 }]
    );

    // 3. `rustc_o0_o2_parity_checked` counts every non-skipped O0/O2 run
    //    without tool errors, including divergences (`parity_ok == false`).
    let ok_auth = mk_auth("rustc-o0", ret_val.clone());
    let mut o2_err = mk_auth("rustc-o2", ret_val.clone());
    o2_err.tool_error = Some("compile error".into());
    let mut o2_div = mk_auth("rustc-o2", ret_val.clone());
    o2_div.outcome = TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) };
    let mk_dual_case = |id: &str, dual: RustcDualResult| CaseReport {
        case_id: id.into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: dual,
        miri: None,
        lean: None,
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let div_dual = RustcDualResult {
        o0: ok_auth.clone(),
        o2: o2_div,
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 diverged".into()),
    };
    let err_dual = RustcDualResult {
        o0: ok_auth.clone(),
        o2: o2_err,
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let pass_dual = RustcDualResult {
        o0: ok_auth.clone(),
        o2: mk_auth("rustc-o2", ret_val.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let count_rep = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![
            mk_dual_case("p", pass_dual.clone()),
            mk_dual_case("d", div_dual),
            mk_dual_case("s", RustcDualResult::skipped_for_ub("ub")),
            mk_dual_case("e", err_dual),
        ],
        Vec::new(),
    );
    assert_eq!(count_rep.counts.rustc_o0_o2_parity_checked, 2);

    // 4. Reject stale `witness.signature` when authoritative `minimized_report`
    //    (or fallback `report`) reports `Agree` or `ToolError`.
    let sr_base =
        shrink_fuzz_program_with_budget(&base_fp, ShrinkBudget::default(), |c| c.steps.len() == 1);
    let agree_rep = mk_dual_case(&entry_dig_rep.case_id, pass_dual);
    let mut err_rep = agree_rep.clone();
    err_rep.verdict = TraceVerdict::ToolError { authority: "lean".into(), detail: "boom".into() };
    let w_stale_min = WitnessArtifact::from_shrink(
        &entry_dig_rep.case_id,
        entry_dig_rep.verdict.clone(),
        entry_dig_rep.verdict.clone(),
        sr_base,
    )
    .with_signature(entry_dig_sig)
    .with_minimized_report(agree_rep);
    assert!(
        CanonicalBugFingerprint::from_1_minimal_witness(
            &w_stale_min,
            &entry_dig_rep,
            "main",
            "mir_v1",
            None,
        )
        .is_err()
    );
    let mut stale_reg = BugRegistry::new("google/zerocopy");
    let stale_out = stale_reg.record_witness(
        &w_stale_min,
        &entry_dig_rep,
        "main",
        true,
        "mir_v1",
        "1111111111111111111111111111111111111111",
        None,
    );
    assert!(matches!(stale_out, DedupRecordOutcome::Provisional { .. }));
    assert!(stale_reg.buckets.is_empty());
    let w_stale_err = w_stale_min.clone().with_minimized_report(err_rep);
    assert!(
        CanonicalBugFingerprint::from_1_minimal_witness(
            &w_stale_err,
            &entry_dig_rep,
            "main",
            "mir_v1",
            None,
        )
        .is_err()
    );

    // 5. Metamorphic standalone reproducers reject incompatible `fault_ub`
    //    causes and accept compatible `fault_ub` causes.
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let mut ub_meta_case = generate_fuzz_batch(0x0921_0001, 1).pop().unwrap().to_trace_test_case();
    ub_meta_case.rust_arg_exprs = vec!["1u32".into(), "2u32".into()];
    ub_meta_case.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    ub_meta_case.env_schedule = EnvSchedule::default();
    ub_meta_case.traced_rust_source = None;
    ub_meta_case.pure_rust_source = "pub fn fuzz_entry(_x: u32, _y: u32) -> u32 {\n\
         \x20   if cfg!(debug_assertions) {\n\
         \x20       std::panic::panic_any(crate::anneal_rt::ScheduleDecodeFailed(\n\
         \x20           \"callee `foo` scheduled ReturnBytes invalid: bad\".into(),\n\
         \x20       ));\n\
         \x20   } else {\n\
         \x20       std::panic::panic_any(crate::anneal_rt::ScheduleDecodeFailed(\n\
         \x20           \"callee `bar` scheduled ReturnBytes invalid: bad\".into(),\n\
         \x20       ));\n\
         \x20   }\n\
         }\n"
    .into();
    ub_meta_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, y: u32) -> u32 { x.wrapping_add(y) }\n".into();
    let ub_rs = tmp.path().join("meta_ub_cmp.rs");
    let ub_o0 = tmp.path().join("meta_ub_o0");
    let ub_o2 = tmp.path().join("meta_ub_o2");
    fs::write(
        &ub_rs,
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &ub_meta_case,
            &["called_rustc_o0_vs_o2".to_string()],
        ),
    )
    .unwrap();
    for (extra, out_bin) in [
        (&["-C", "debug-assertions=yes"][..], &ub_o0),
        (&["-C", "opt-level=2", "-C", "debug-assertions=no"][..], &ub_o2),
    ] {
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .args(extra)
            .arg(&ub_rs)
            .arg("-o")
            .arg(out_bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    }
    let ub_div_cmp = Command::new(&ub_o0).args(["--compare-opt"]).arg(&ub_o2).output().unwrap();
    assert!(
        !ub_div_cmp.status.success(),
        "incompatible fault_ub causes across O0 vs O2 must fail loudly"
    );
    let ub_same_cmp = Command::new(&ub_o0).args(["--compare-opt"]).arg(&ub_o0).output().unwrap();
    assert!(
        ub_same_cmp.status.success(),
        "compatible fault_ub causes must pass: {}",
        String::from_utf8_lossy(&ub_same_cmp.stderr)
    );
}

#[test]
fn r22_validate_pass_blocks_win_drive_padded_provisional_and_input_shrink() {
    let tmp = tempfile::tempdir().unwrap();
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(1),
        mem_digest: compute_boundary_mem_digest(&[]),
    };

    // 1. `validate_honesty` rejects `PASS` parents when `evidence_blocks`
    //    contains `FAIL`/`UNVERIFIED` or is empty.
    let agree_case = CaseReport {
        case_id: "c_agree".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-o0", ret_val.clone()),
            o2: mk_auth("rustc-o2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let clean_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![agree_case],
        Vec::new(),
    );
    let clean_ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: "1111111111111111111111111111111111111111".into(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "test".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some("1111111111111111111111111111111111111111".into()),
    };
    let base_rec = SemanticDetailRecord::from_report_and_registry(
        &clean_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    for bad_status in ["FAIL", "UNVERIFIED"] {
        let mut bad_rec = base_rec.clone();
        bad_rec.evidence_blocks[0].overall_status = bad_status.into();
        assert!(bad_rec.validate_honesty().is_err());
        let p = tmp.path().join(format!("bad_{bad_status}.jsonl"));
        assert!(bad_rec.write_jsonl(&p).is_err());
        assert!(!p.exists());
    }
    let mut empty_blocks = base_rec;
    empty_blocks.evidence_blocks.clear();
    assert!(empty_blocks.validate_honesty().is_err());

    // 2. `normalize_repo_slug` rejects Windows drive-letter local paths before
    //    SCP-style colon parsing.
    for win_path in [
        "C:/Users/alice/repo.git",
        "c:/work/private/repo",
        "D:Users/bob/repo.git",
        r"C:\Users\alice\repo.git",
    ] {
        assert_eq!(normalize_repo_slug(win_path), "google/zerocopy", "{win_path}");
    }
    assert_eq!(normalize_repo_slug("git@github.com:org/repo.git"), "org/repo");

    // 3. Converged `ShrinkableCase` containing causal `PaddedRoundTrip` cannot
    //    lower to plain scalar `.mir.lean` and stays `Provisional`.
    let pad_sc = ShrinkableCase {
        name: "causal_padded".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::PaddedRoundTrip { local_id: 0, tag_byte: 5 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&pad_sc, "p").is_err()
    );
    let mut ub_sig_rep = mk_ub_case_report(
        "pad_sig",
        "signed arithmetic overflow",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "missed".into() },
    );
    ub_sig_rep.rustc_dual.skipped_for_ub = false;
    let pad_sig = ShrinkFailureSignature::from_case_report(&ub_sig_rep).unwrap();
    let mut pad_reg = BugRegistry::new("google/zerocopy");
    let pad_out = pad_reg.record_shrinkable_case(
        &pad_sc,
        &pad_sig,
        Some(&ub_sig_rep.rustc_dual),
        ub_sig_rep.miri.as_ref(),
        ub_sig_rep.lean.as_ref(),
        "main",
        true,
        "v1",
        "1111111111111111111111111111111111111111",
        1,
        true,
    );
    assert!(matches!(pad_out, DedupRecordOutcome::Provisional { .. }));
    assert!(pad_reg.buckets.is_empty());

    // 4. `shrink_case_with_budget` prunes noncausal `ShrinkInput` entries to
    //    1-minimal arity so extra unused args never fragment skeletons.
    let extra_in_case = ShrinkableCase {
        name: "extra_inputs".into(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 1, width: IntKind::U128, value: 99, align_hint: Some(16) },
            ShrinkInput { local_id: 2, width: IntKind::U64, value: 7, align_hint: None },
            ShrinkInput { local_id: 3, width: IntKind::U32, value: 55, align_hint: Some(8) },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 2, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 2,
    };
    let in_shrunk = anneal_itree_diff::shrink::shrink_case_with_budget(
        &extra_in_case,
        ShrinkBudget::default(),
        |c| {
            c.inputs.iter().any(|i| i.local_id == 2 && i.value >= 7)
                && c.steps.iter().any(|s| matches!(s, ShrinkStep::ArithImm { .. }))
        },
    );
    assert!(in_shrunk.is_one_minimal);
    assert_eq!(in_shrunk.minimized.inputs.len(), 1);
    assert_eq!(in_shrunk.minimized.inputs[0].width, IntKind::U8);
    assert_eq!(in_shrunk.minimized.inputs[0].value, 7);
    assert_eq!(in_shrunk.minimized.inputs[0].align_hint, None);
    let mut only_causal = extra_in_case;
    only_causal.inputs =
        vec![ShrinkInput { local_id: 2, width: IntKind::U64, value: 7, align_hint: None }];
    let causal_shrunk = anneal_itree_diff::shrink::shrink_case_with_budget(
        &only_causal,
        ShrinkBudget::default(),
        |c| {
            c.inputs.iter().any(|i| i.local_id == 2 && i.value >= 7)
                && c.steps.iter().any(|s| matches!(s, ShrinkStep::ArithImm { .. }))
        },
    );
    assert_eq!(
        canonical_shrinkable_case_skeleton_hash(&in_shrunk.minimized),
        canonical_shrinkable_case_skeleton_hash(&causal_shrunk.minimized)
    );
}

#[test]
fn r23_pass_slice_accounting_wider_id_exe_peer_head_auth_and_bundle_preserve() {
    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. `validate_honesty` enforces mutually-exclusive slice accounting and
    // parent/subset upper bounds.
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let clean_case = CaseReport {
        case_id: "r23_clean".to_string(),
        category: CaseCategory::ScalarBitwise,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_ok.clone()),
            o2: mk_auth("rustc-O2", ret_ok.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_ok.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_ok)),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let rep = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![clean_case],
        vec![],
    );
    let sha = "b".repeat(40);
    let ctx = TelemetryContext {
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        branch_scope: "main".to_string(),
        exposed_on_main: true,
        commit_sha: sha.clone(),
        commit_unix_ts: 1_774_000_000,
        environment_profile: "local-itree-diff".to_string(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: None,
        build_exit_code_override: None,
        head_provenance_verified: true,
        discovered_head_sha: Some(sha),
    };
    let valid_rec = SemanticDetailRecord::from_report_and_registry(
        &rep,
        &BugRegistry::new("google/zerocopy"),
        &ctx,
    )
    .expect("valid PASS record");
    valid_rec.validate_honesty().expect("valid slice accounting accepted");

    let mut zero_counters = valid_rec.clone();
    zero_counters.differential_runs[0].agree_count = 0;
    zero_counters.differential_runs[0].panic_agreed_count = 0;
    assert!(
        zero_counters.validate_honesty().is_err(),
        "PASS slice with compared_count>0 and zero disposition counts must fail"
    );

    let mut panic_gt_agree = valid_rec.clone();
    panic_gt_agree.differential_runs[0].panic_agreed_count = 2;
    assert!(panic_gt_agree.validate_honesty().is_err(), "panic_agreed_count > agree_count");

    let mut exp_gt_compared = valid_rec.clone();
    exp_gt_compared.differential_runs[0].expectation_mismatch_count = 2;
    exp_gt_compared.differential_runs[0].overall_status = "FAIL".to_string();
    exp_gt_compared.overall_status = "FAIL".to_string();
    exp_gt_compared.evidence_blocks[0].overall_status = "FAIL".to_string();
    assert!(
        exp_gt_compared.validate_honesty().is_err(),
        "expectation_mismatch_count > compared_count must fail"
    );

    let mut kernel_gt_compared = valid_rec;
    kernel_gt_compared.differential_runs[0].kernel_checked_count = 2;
    assert!(
        kernel_gt_compared.validate_honesty().is_err(),
        "kernel_checked_count > compared_count must fail"
    );

    // 2. Witness and shrinkable artifact IDs retain a 24-hex (96-bit) digest
    // suffix after `<skel_hash>_`.
    let sig_o2 = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "rustc_o0_o2",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: String::new(),
        metamorphic_relations: vec!["called_rustc_o0_vs_o2".to_string()],
        metamorphic_leg_kinds: String::new(),
        spine_relation: Some("rustc_o0_vs_o2".to_string()),
    };
    let prog = FuzzProgram {
        seed: 0x2301,
        index: 1,
        input_x: 9,
        input_y: 4,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 3 },
            FuzzStep::HelperCall { callee_idx: 0, bias: 2 },
        ],
        applied_mutators: Vec::new(),
    };
    let wid = canonical_witness_artifact_id(
        "abcd1234",
        &prog,
        None,
        Some(&sig_o2),
        &TraceVerdict::UnsoundAccept { detail: "o0 vs o2".to_string() },
    );
    let (_, w_hex) = wid.split_once('_').expect("witness id underscore");
    assert_eq!(w_hex.len(), 24, "expected 24-hex suffix, got {wid}");
    assert!(w_hex.bytes().all(|b| b.is_ascii_hexdigit()));

    let scase = ShrinkableCase {
        name: "r23_o2".into(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 1, width: IntKind::U32, value: 9, align_hint: None },
            ShrinkInput { local_id: 2, width: IntKind::U32, value: 4, align_hint: None },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 1, op: FuzzArithOp::Add, imm: 3 }],
        env_schedule: EnvSchedule::default(),
        return_local: 1,
    };
    let sid = canonical_shrinkable_artifact_id("ef012345", &scase, &sig_o2);
    let (_, s_hex) = sid.split_once('_').expect("shrinkable id underscore");
    assert_eq!(s_hex.len(), 24, "expected 24-hex suffix, got {sid}");
    assert!(s_hex.bytes().all(|b| b.is_ascii_hexdigit()));

    // 3. Both `spec.rs` and `shrink.rs` `rustc_o0_o2` reproducers emit shared
    // `.exe`/`.EXE`-aware sibling discovery and execute `repro_o2.exe` <->
    // `repro.exe` comparisons cleanly when `rustc` is available.
    let meta_case = prog.to_trace_test_case();
    assert!(meta_case.metamorphic_inlined_twin.is_some());
    let meta_rs = render_standalone_metamorphic_rust_harness_with_relations(
        &meta_case,
        &["called_rustc_o0_vs_o2".to_string()],
    );
    let shrink_rs =
        render_standalone_shrinkable_repro_rs_for_signature(&scase, &wid, Some(&sig_o2));
    assert!(meta_rs.contains("eq_ignore_ascii_case(b\".exe\")"));
    assert!(shrink_rs.contains("eq_ignore_ascii_case(b\".exe\")"));
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let exe_dir = tmp.path().join("exe_peer");
    fs::create_dir_all(&exe_dir).unwrap();
    let meta_src = exe_dir.join("meta_exe_repro.rs");
    fs::write(&meta_src, &meta_rs).unwrap();
    let meta_o0 = exe_dir.join("meta_repro.exe");
    let meta_o2 = exe_dir.join("meta_repro_o2.exe");
    for (opt, out_bin) in [("0", &meta_o0), ("2", &meta_o2)] {
        let st = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2021", "-C"])
            .arg(format!("opt-level={opt}"))
            .arg(&meta_src)
            .arg("-o")
            .arg(out_bin)
            .status()
            .expect("compile meta .exe peer");
        assert!(st.success(), "rustc meta opt={opt} failed");
    }
    let meta_run = Command::new(&meta_o2).output().expect("run meta _o2.exe");
    assert!(
        meta_run.status.success(),
        "meta _o2.exe failed finding .exe peer: {}",
        String::from_utf8_lossy(&meta_run.stderr)
    );

    let shrink_src = exe_dir.join("shrink_exe_repro.rs");
    fs::write(&shrink_src, &shrink_rs).unwrap();
    let shrink_o0 = exe_dir.join("shrink_repro.EXE");
    let shrink_o2 = exe_dir.join("shrink_repro_o2.EXE");
    for (opt, out_bin) in [("0", &shrink_o0), ("2", &shrink_o2)] {
        let st = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C"])
            .arg(format!("opt-level={opt}"))
            .arg(&shrink_src)
            .arg("-o")
            .arg(out_bin)
            .status()
            .expect("compile shrink .EXE peer");
        assert!(st.success(), "rustc shrink opt={opt} failed");
    }
    let shrink_run = Command::new(&shrink_o2).output().expect("run shrink _o2.EXE");
    assert!(
        shrink_run.status.success(),
        "shrink _o2.EXE failed finding .EXE peer: {}",
        String::from_utf8_lossy(&shrink_run.stderr)
    );

    // 4. `WitnessBundle::write_to_dir` preserves pre-existing valid bundle
    // members when replacing a bundle encounters a write/persist failure.
    let bundle_dir = tmp.path().join("preserve_bundle");
    let sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| {
        p.input_x == prog.input_x
    });
    assert!(sr.succeeded && sr.is_one_minimal);
    let sig_r23 = ShrinkFailureSignature::from_verdict_and_legs(
        &TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".to_string() },
        None,
        None,
    )
    .unwrap();
    let art = WitnessArtifact::from_shrink(
        "r23_bundle",
        TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".to_string() },
        TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".to_string() },
        sr,
    )
    .with_signature(sig_r23);
    let mut bundle = WitnessBundle::from_witness(art, None);
    let orig_paths = bundle.write_to_dir(&bundle_dir).expect("initial bundle write");
    let orig_rs = fs::read_to_string(&orig_paths.repro_rs_path).unwrap();
    let orig_lean = fs::read_to_string(&orig_paths.mir_lean_path).unwrap();

    fs::remove_file(&orig_paths.witness_json_path).unwrap();
    fs::create_dir_all(&orig_paths.witness_json_path).unwrap();
    bundle.repro_rust_source = "// overwritten-should-not-persist\n".to_string();
    bundle.mir_lean_source = "-- overwritten-should-not-persist\n".to_string();
    assert!(
        bundle.write_to_dir(&bundle_dir).is_err(),
        "directory blocking witness JSON must fail replacement write"
    );
    assert_eq!(fs::read_to_string(&orig_paths.repro_rs_path).unwrap(), orig_rs);
    assert_eq!(fs::read_to_string(&orig_paths.mir_lean_path).unwrap(), orig_lean);
}

#[test]
fn r24_fail_slice_propagation_per_case_witness_restore_and_repro_regen() {
    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. `validate_honesty` rejects parent `UNVERIFIED` when any slice or
    // evidence block reports `FAIL`, and rejects `UNVERIFIED` slices carrying
    // hard failure counters.
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ret_bad = TerminalOutcome::Returned {
        ret: TraceVal::u32(99),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let mut fail_case = CaseReport {
        case_id: "r24_fail".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: "value mismatch".to_string() },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_ok.clone()),
            o2: mk_auth("rustc-O2", ret_ok.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_ok)),
        lean: Some(mk_auth("lean-compositional-itree", ret_bad)),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let rep = DifferentialReport::from_cases(
        "available",
        true,
        false,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![fail_case.clone()],
        vec![],
    );
    let sha = "c".repeat(40);
    let ctx = TelemetryContext {
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        branch_scope: "main".to_string(),
        exposed_on_main: true,
        commit_sha: sha.clone(),
        commit_unix_ts: 1_774_000_000,
        environment_profile: "local-itree-diff".to_string(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: None,
        build_exit_code_override: None,
        head_provenance_verified: true,
        discovered_head_sha: Some(sha),
    };
    let fail_rec = SemanticDetailRecord::from_report_and_registry(
        &rep,
        &BugRegistry::new("google/zerocopy"),
        &ctx,
    )
    .expect("valid FAIL record");
    fail_rec.validate_honesty().expect("FAIL record accepted");

    let mut unverified_parent = fail_rec.clone();
    unverified_parent.overall_status = "UNVERIFIED".to_string();
    assert!(
        unverified_parent.validate_honesty().is_err(),
        "UNVERIFIED parent must be rejected when slice/evidence reports FAIL"
    );

    let mut unverified_slice = fail_rec;
    unverified_slice.differential_runs[0].overall_status = "UNVERIFIED".to_string();
    assert!(
        unverified_slice.validate_honesty().is_err(),
        "UNVERIFIED slice with value_mismatch_count > 0 must be rejected"
    );

    // 2. `apply_fuzz_shrink_outcome` preserves a pre-existing per-case
    // `<case_id>.witness.json` when emitting the companion bundle fails.
    let prog = FuzzProgram {
        seed: 0x2401,
        index: 0,
        input_x: 11,
        input_y: 5,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 2 }],
        applied_mutators: Vec::new(),
    };
    let sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| {
        p.input_x == prog.input_x
    });
    assert!(sr.succeeded && sr.is_one_minimal);
    let art = WitnessArtifact::from_shrink(
        &fail_case.case_id,
        fail_case.verdict.clone(),
        fail_case.verdict.clone(),
        sr,
    );
    let wdir = tmp.path().join("restore_case_witness");
    let mut initial_out = Vec::new();
    anneal_itree_diff::apply_fuzz_shrink_outcome(
        &mut fail_case.clone(),
        Some(&wdir),
        &mut initial_out,
        art.clone(),
        None,
    );
    assert_eq!(initial_out.len(), 1);
    let per_case_json = wdir.join(format!("{}.witness.json", fail_case.case_id));
    let orig_per_case = "PRIOR-VALID-WITNESS-JSON";
    fs::write(&per_case_json, orig_per_case).unwrap();
    let bundle = WitnessBundle::from_witness(art.clone(), None);
    let bundle_json = wdir.join(format!("witness_{}.json", bundle.bundle_id));
    fs::remove_file(&bundle_json).unwrap();
    fs::create_dir_all(&bundle_json).unwrap();

    let mut blocked_out = Vec::new();
    let mut retry_case = fail_case.clone();
    anneal_itree_diff::apply_fuzz_shrink_outcome(
        &mut retry_case,
        Some(&wdir),
        &mut blocked_out,
        art.clone(),
        None,
    );
    assert!(blocked_out.is_empty());
    assert_eq!(fs::read_to_string(&per_case_json).unwrap(), orig_per_case);

    // 3. `BugRegistry::record_witness` regenerates Rust reproducer source from
    // `witness.shrink.minimized` even if `reproducer_rust_source` was tampered
    // while keeping `repro_case_id` and empty schedule.
    let mut stale_art = art;
    let saved_repro_id = stale_art.repro_case_id.clone();
    stale_art.repro_schedule = None;
    stale_art.reproducer_rust_source = "// STALE ARBITRARY SOURCE\nfn wrong() {}".to_string();
    assert_eq!(stale_art.repro_case_id, saved_repro_id);
    fail_case.verdict = TraceVerdict::UnsoundAccept { detail: "value mismatch".to_string() };
    let mut reg = BugRegistry::new("google/zerocopy");
    let rec = reg.record_witness(
        &stale_art,
        &fail_case,
        "main",
        true,
        "lean_compositional_itree_v1",
        &"d".repeat(40),
        None,
    );
    let bug_id = match rec {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("unexpected outcome: {other:?}"),
    };
    let stored = &reg.buckets[&bug_id].witnesses[0].repro_rust_source;
    assert!(!stored.contains("STALE ARBITRARY SOURCE"));
    assert!(stored.contains("fuzz_entry"));
}

#[test]
fn r25_direct_o0_o2_pinning_skel_recompute_and_corpus_component_symlinks() {
    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. Direct non-metamorphic `rustc_o0_o2` and `spine_mismatch`
    // (`rustc_o0_vs_o2`) failures propagate O0/O2 pinning into `record_witness`
    // reproducers (both non-metamorphic `ReturnBytes`-scheduled single harness
    // and metamorphic dual-twin harness).
    let single_prog = FuzzProgram {
        seed: 0x2501,
        index: 0,
        input_x: 7,
        input_y: 3,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 },
            FuzzStep::HelperCall { callee_idx: 0, bias: 2 },
        ],
        applied_mutators: Vec::new(),
    };
    let mut rb_sched = EnvSchedule::default();
    rb_sched.push_callee("fuzz_helper_0", EnvAction::ReturnBytes(vec![7, 0, 0, 0]));
    let multi_prog = FuzzProgram {
        seed: 0x2502,
        index: 1,
        input_x: 13,
        input_y: 4,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
            FuzzStep::HelperCall { callee_idx: 0, bias: 2 },
        ],
        applied_mutators: Vec::new(),
    };
    assert!(multi_prog.to_trace_test_case().metamorphic_inlined_twin.is_some());

    let sr_single = shrink_fuzz_program_with_budget(&single_prog, ShrinkBudget::default(), |p| {
        p.steps.iter().any(|s| matches!(s, FuzzStep::ArithImm { .. }))
            && p.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
    });
    let sr_multi = shrink_fuzz_program_with_budget(&multi_prog, ShrinkBudget::default(), |p| {
        p.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
    });
    assert!(sr_single.succeeded && sr_single.is_one_minimal);
    assert!(sr_multi.succeeded && sr_multi.is_one_minimal);

    let ret0 = TerminalOutcome::Returned {
        ret: TraceVal::u32(12),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ret2 = TerminalOutcome::Returned {
        ret: TraceVal::u32(99),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let direct_verdict = TraceVerdict::UnsoundAccept {
        detail: "rustc O0 vs O2 terminal outcome divergence: O0=Returned vs O2=Returned"
            .to_string(),
    };
    let single_case = CaseReport {
        case_id: "r25_single_o2".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: direct_verdict.clone(),
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret0.clone()),
            o2: mk_auth("rustc-O2", ret2),
            parity_ok: false,
            skipped_for_ub: false,
            mismatch_detail: Some("O0=12 vs O2=99".to_string()),
        },
        miri: Some(mk_auth("miri", ret0.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret0.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let w_single = WitnessArtifact::from_shrink_with_schedule(
        &single_case.case_id,
        direct_verdict.clone(),
        direct_verdict,
        sr_single,
        Some(&rb_sched),
    );

    let spine_verdict = TraceVerdict::UnsoundAccept {
        detail: "rustc O0 vs O2: spine_mismatch: rustc_o0_vs_o2: length mismatch".to_string(),
    };
    let mut multi_o0 = mk_auth("rustc-O0", ret0.clone());
    multi_o0.spine.events = vec![ObservableEvent::CallEnter {
        callee: "fuzz_helper_0".to_string(),
        arg_bytes: Vec::new(),
        arg_reprs: Vec::new(),
    }];
    let multi_case = CaseReport {
        case_id: "r25_multi_o2".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: spine_verdict.clone(),
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: multi_o0,
            o2: mk_auth("rustc-O2", ret0.clone()),
            parity_ok: false,
            skipped_for_ub: false,
            mismatch_detail: Some("spine length mismatch".to_string()),
        },
        miri: Some(mk_auth("miri", ret0.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret0)),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let w_multi = WitnessArtifact::from_shrink(
        &multi_case.case_id,
        spine_verdict.clone(),
        spine_verdict,
        sr_multi,
    );

    let mut reg_o2 = BugRegistry::new("google/zerocopy");
    let rec_single = reg_o2.record_witness(
        &w_single,
        &single_case,
        "main",
        true,
        "lean_compositional_itree_v1",
        &"e".repeat(40),
        Some(&rb_sched),
    );
    let rec_multi = reg_o2.record_witness(
        &w_multi,
        &multi_case,
        "main",
        true,
        "lean_compositional_itree_v1",
        &"e".repeat(40),
        None,
    );
    let bug_single = match rec_single {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("unexpected outcome: {other:?}"),
    };
    let bug_multi = match rec_multi {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("unexpected outcome: {other:?}"),
    };
    let single_src = &reg_o2.buckets[&bug_single].witnesses[0].repro_rust_source;
    let multi_src = &reg_o2.buckets[&bug_multi].witnesses[0].repro_rust_source;
    assert!(single_src.contains("run_single_subject"), "single_src:\n{single_src}");
    assert!(single_src.contains("called_rustc_o0_vs_o2"), "single_src:\n{single_src}");
    assert!(multi_src.contains("\"called_rustc_o0_vs_o2\""), "multi_src:\n{multi_src}");

    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let o2_dir = tmp.path().join("direct_o2");
    fs::create_dir_all(&o2_dir).unwrap();
    for (tag, src) in [("single", single_src), ("multi", multi_src)] {
        let src_path = o2_dir.join(format!("{tag}.rs"));
        fs::write(&src_path, src).unwrap();
        let bin_o0 = o2_dir.join(format!("{tag}_bin"));
        let bin_o2 = o2_dir.join(format!("{tag}_bin_o2"));
        for (opt, out_bin) in [("0", &bin_o0), ("2", &bin_o2)] {
            let st = Command::new(&engine.rustc.rustc_bin)
                .args(["--edition", "2024", "-C"])
                .arg(format!("opt-level={opt}"))
                .arg(&src_path)
                .arg("-o")
                .arg(out_bin)
                .status()
                .expect("compile direct o0/o2 repro");
            assert!(st.success(), "rustc {tag} opt={opt} failed");
        }
        let with_peer = Command::new(&bin_o0).output().expect("run with sibling o2");
        assert!(with_peer.status.success(), "{tag} failed with sibling o2");
        fs::remove_file(&bin_o2).unwrap();
        let without_peer = Command::new(&bin_o0).output().expect("run without sibling o2");
        assert!(!without_peer.status.success(), "{tag} must fail loudly without O2 peer");
    }

    // 2. Schedule-free `WitnessArtifact` with a stale non-empty
    // `minimized_skeleton_hash` recomputes its skeleton hash from
    // `shrink.minimized` across fingerprint, bundle, and `BugRegistry`.
    let mut w_stale_skel = w_multi;
    w_stale_skel.repro_schedule = None;
    let true_multi_skel =
        canonical_fuzz_program_skeleton_hash(&w_stale_skel.shrink.minimized, None);
    let wrong_single_skel = canonical_fuzz_program_skeleton_hash(&w_single.shrink.minimized, None);
    assert_ne!(true_multi_skel, wrong_single_skel);
    w_stale_skel.minimized_skeleton_hash = wrong_single_skel;
    let fp_recomputed = CanonicalBugFingerprint::from_1_minimal_witness(
        &w_stale_skel,
        &multi_case,
        "main",
        "lean_compositional_itree_v1",
        None,
    )
    .expect("fingerprint recomputed");
    assert_eq!(fp_recomputed.minimized_skeleton_hash, true_multi_skel);
    let bundle_recomputed = WitnessBundle::from_witness(w_stale_skel.clone(), None);
    assert_eq!(bundle_recomputed.skel_hash, true_multi_skel);
    let mut reg_skel = BugRegistry::new("google/zerocopy");
    reg_skel.record_witness(
        &w_stale_skel,
        &multi_case,
        "main",
        true,
        "lean_compositional_itree_v1",
        &"f".repeat(40),
        None,
    );
    let rec_entry = reg_skel.buckets.values().next().unwrap();
    assert_eq!(rec_entry.witnesses[0].minimized_skeleton_hash, true_multi_skel);

    // 3. `load_fuzz_seeds_from_dir` rejects symlinks anywhere in `--corpus-dir`
    // (`symlink/.`, intermediate `sym/child`, `sym/../sym/child`).
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let corpus_base = tmp.path().join("corpus_sym_components");
        let real_parent = corpus_base.join("real_parent");
        let real_child = real_parent.join("real_child");
        fs::create_dir_all(&real_child).unwrap();
        let seed_json = serde_json::to_string(&single_prog).unwrap();
        fs::write(real_child.join("seed.json"), &seed_json).unwrap();

        let sym_dir = corpus_base.join("sym_dir");
        symlink(&real_child, &sym_dir).unwrap();
        let sym_parent = corpus_base.join("sym_parent");
        symlink(&real_parent, &sym_parent).unwrap();

        assert!(anneal_itree_diff::load_fuzz_seeds_from_dir(&real_child).is_ok());
        assert!(anneal_itree_diff::load_fuzz_seeds_from_dir(&real_child.join(".")).is_ok());
        for bad_dir in [
            sym_dir.clone(),
            sym_dir.join("."),
            sym_parent.join("real_child"),
            sym_parent.join("real_child").join("."),
            sym_parent.join("..").join("sym_parent").join("real_child"),
        ] {
            assert!(
                anneal_itree_diff::load_fuzz_seeds_from_dir(&bad_dir).is_err(),
                "expected symlinked path component to be rejected: {}",
                bad_dir.display()
            );
        }
    }
}

#[test]
fn r26_empty_schedule_queues_auth_bundle_branch_polarity_ub_slots_and_skip_unverified() {
    use std::collections::VecDeque;

    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. Empty per-callee action queues (`per_callee: {"h0": []}`) must NOT
    //    mark `h0` external in `strip_env_schedule_for_strict_probe` or
    //    standalone `.mir.lean` generation.
    let mut base_prog = generate_fuzz_batch(0x2601_0001, 1).pop().unwrap();
    base_prog.steps = vec![FuzzStep::HelperCall { callee_idx: 0, bias: 1 }];
    let mut empty_queue_sched = EnvSchedule::default();
    empty_queue_sched.per_callee.insert("h0".to_string(), VecDeque::new());
    let mut empty_q_case = base_prog.to_trace_test_case();
    empty_q_case.env_schedule = empty_queue_sched.clone();
    assert!(!empty_q_case.requires_strict_refusal());
    let stripped = anneal_itree_diff::strip_env_schedule_for_strict_probe(&empty_q_case);
    assert!(!stripped.requires_strict_refusal(), "empty per_callee queue must stay strict-clean");
    if let LeanProgramSpec::MultiCallWithCapturedCallees { external_callees, .. } =
        &stripped.lean_program_spec
    {
        assert!(!external_callees.contains(&"h0".to_string()));
    } else {
        panic!("expected MultiCallWithCapturedCallees");
    }
    let mir_lean_empty_q = anneal_itree_diff::shrink::render_standalone_mir_lean(
        &base_prog,
        Some(&empty_queue_sched),
        "r26_eq",
    );
    assert!(
        mir_lean_empty_q.contains("def reproExternalCallees : List String := []"),
        "standalone .mir.lean must ignore empty per_callee queue:\n{mir_lean_empty_q}"
    );

    // 2. `WitnessBundle::try_from_witness` & `BugRegistry::record_witness`
    //    derive signature from authoritative `minimized_report` first and
    //    reject stale/conflicting stored `artifact.signature`.
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ret_bad = TerminalOutcome::Returned {
        ret: TraceVal::u32(99),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let o0_o2_rep = CaseReport {
        case_id: "r26_o0_o2".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".into() },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_bad.clone()),
            parity_ok: false,
            skipped_for_ub: false,
            mismatch_detail: Some("O0 vs O2 diverged".into()),
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let stale_val_rep = CaseReport {
        case_id: "r26_stale_val".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".into() },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_bad)),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let stale_sig = ShrinkFailureSignature::from_case_report(&stale_val_rep).unwrap();
    let mut o0_o2_prog = base_prog.clone();
    o0_o2_prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let mut sr_bundle =
        shrink_fuzz_program_with_budget(&o0_o2_prog, ShrinkBudget::default(), |p| {
            !p.steps.is_empty()
        });
    sr_bundle.succeeded = true;
    sr_bundle.is_one_minimal = true;
    sr_bundle.converged_1_minimal = true;

    let conflicting_art = WitnessArtifact::from_shrink(
        &o0_o2_rep.case_id,
        o0_o2_rep.verdict.clone(),
        o0_o2_rep.verdict.clone(),
        sr_bundle.clone(),
    )
    .with_signature(stale_sig)
    .with_minimized_report(o0_o2_rep.clone());
    assert!(WitnessBundle::try_from_witness(conflicting_art.clone(), None).is_err());

    let conflict_wdir = tmp.path().join("conflict_bundle_dir");
    let mut emitted_conflict = Vec::new();
    let mut conflict_rep = o0_o2_rep.clone();
    anneal_itree_diff::apply_fuzz_shrink_outcome(
        &mut conflict_rep,
        Some(&conflict_wdir),
        &mut emitted_conflict,
        conflicting_art.clone(),
        None,
    );
    assert!(emitted_conflict.is_empty());
    assert!(matches!(
        &conflict_rep.verdict,
        TraceVerdict::UnsoundAccept { detail } if detail.contains("secondary witness-writer tool error")
    ));

    let mut reg_conflict = BugRegistry::new("google/zerocopy");
    assert!(matches!(
        reg_conflict.record_witness(
            &conflicting_art,
            &o0_o2_rep,
            "main",
            true,
            "v1",
            &"1".repeat(40),
            None,
        ),
        DedupRecordOutcome::Provisional { .. }
    ));

    let auth_no_sig_art = WitnessArtifact::from_shrink(
        &o0_o2_rep.case_id,
        stale_val_rep.verdict.clone(),
        stale_val_rep.verdict.clone(),
        sr_bundle,
    )
    .with_minimized_report(o0_o2_rep);
    let auth_bundle = WitnessBundle::try_from_witness(auth_no_sig_art, None).unwrap();
    assert!(auth_bundle.repro_rust_source.contains("called_rustc_o0_vs_o2"));
    assert!(auth_bundle.repro_rust_source.contains("--compare-opt"));

    // 3. `BranchMix` polarity minimizes `taken_then: true -> false` when
    //    noncausal so equivalent branch-spine failures merge skeletons.
    let mk_branch_case = |taken_then: bool| ShrinkableCase {
        name: "branch_polarity".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::BranchMix {
            block_id: 0,
            cond_local: 0,
            taken_then,
            dynamic_even_cond: false,
            then_steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
            else_steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 2 }],
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let branch_pred =
        |c: &ShrinkableCase| c.steps.iter().any(|s| matches!(s, ShrinkStep::BranchMix { .. }));
    let res_true = shrink_case_two_tier_with_budget(
        &mk_branch_case(true),
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        branch_pred,
    );
    let res_false = shrink_case_two_tier_with_budget(
        &mk_branch_case(false),
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        branch_pred,
    );
    assert!(res_true.is_one_minimal && res_false.is_one_minimal);
    assert!(matches!(
        res_true.minimized.steps.as_slice(),
        [ShrinkStep::BranchMix { taken_then: false, .. }]
    ));
    assert_eq!(
        canonical_shrinkable_case_skeleton_hash(&res_true.minimized.canonical_alpha_renamed()),
        canonical_shrinkable_case_skeleton_hash(&res_false.minimized.canonical_alpha_renamed()),
    );

    // 4. Metamorphic standalone reproducers reject mismatched `fault_ub`
    //    entry `boundary_slots` across O0 vs O2.
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    let mut slot_ub_case = generate_fuzz_batch(0x2604_0001, 1).pop().unwrap().to_trace_test_case();
    slot_ub_case.rust_arg_exprs =
        vec!["if cfg!(debug_assertions) { 1u32 } else { 2u32 }".into(), "9u32".into()];
    slot_ub_case.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    slot_ub_case.env_schedule = EnvSchedule::default();
    slot_ub_case.traced_rust_source = None;
    slot_ub_case.pure_rust_source = "pub fn fuzz_entry(_x: u32, _y: u32) -> u32 {\n\
         \x20   std::panic::panic_any(crate::anneal_rt::ScheduleDecodeFailed(\n\
         \x20       \"callee `foo` scheduled ReturnBytes invalid: bad\".into(),\n\
         \x20   ));\n\
         }\n"
    .into();
    slot_ub_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, y: u32) -> u32 { x.wrapping_add(y) }\n".into();
    let slot_ub_rs = tmp.path().join("meta_ub_slots.rs");
    let slot_ub_o0 = tmp.path().join("meta_ub_slots_o0");
    let slot_ub_o2 = tmp.path().join("meta_ub_slots_o2");
    fs::write(
        &slot_ub_rs,
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &slot_ub_case,
            &["called_rustc_o0_vs_o2".to_string()],
        ),
    )
    .unwrap();
    for (extra, out_bin) in [
        (&["-C", "debug-assertions=yes"][..], &slot_ub_o0),
        (&["-C", "opt-level=2", "-C", "debug-assertions=no"][..], &slot_ub_o2),
    ] {
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .args(extra)
            .arg(&slot_ub_rs)
            .arg("-o")
            .arg(out_bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    }
    let slot_div_cmp =
        Command::new(&slot_ub_o0).args(["--compare-opt"]).arg(&slot_ub_o2).output().unwrap();
    assert!(
        !slot_div_cmp.status.success(),
        "mismatched fault_ub entry slots across O0 vs O2 must fail loudly"
    );

    // Also confirm called-vs-inlined `fault_ub` rejects mismatched slots.
    let mut slot_inlined_case = slot_ub_case;
    slot_inlined_case.rust_arg_exprs = vec!["1u32".into(), "9u32".into()];
    slot_inlined_case.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(_x: u32, _y: u32) -> u32 {\n\
         \x20   anneal_rt::record_boundary_slot(vec![Some(0xAA)]);\n\
         \x20   std::panic::panic_any(crate::anneal_rt::ScheduleDecodeFailed(\n\
         \x20       \"callee `foo` scheduled ReturnBytes invalid: bad\".into(),\n\
         \x20   ));\n\
         }\n"
        .into();
    let slot_in_rs = tmp.path().join("meta_ub_slots_inlined.rs");
    let slot_in_bin = tmp.path().join("meta_ub_slots_inlined");
    fs::write(
        &slot_in_rs,
        anneal_itree_diff::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &slot_inlined_case,
            &["rustc_called_vs_inlined".to_string()],
        ),
    )
    .unwrap();
    let comp_in = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no"])
        .arg(&slot_in_rs)
        .arg("-o")
        .arg(&slot_in_bin)
        .output()
        .unwrap();
    assert!(comp_in.status.success(), "{}", String::from_utf8_lossy(&comp_in.stderr));
    let slot_in_run = Command::new(&slot_in_bin).output().unwrap();
    assert!(
        !slot_in_run.status.success(),
        "mismatched fault_ub slots across called vs inlined must fail loudly"
    );

    // 5. Skipped metamorphic checks downgrade parent and slice status to
    //    `UNVERIFIED` instead of `PASS`.
    let sha = "e".repeat(40);
    let mut skip_meta_case = CaseReport {
        case_id: "r26_meta_skip".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: Some(MetamorphicDualityReceipt {
            called_lean: mk_auth("lean", ret_val.clone()),
            inlined_lean: mk_auth("lean", ret_val),
            inlined_rustc_parity_ok: true,
            inlined_miri_matched: Some(true),
            tool_error: None,
            status: MetamorphicStatus::SkippedConservative {
                reason: "twin refused conservatively".into(),
            },
            duality_holds: true,
            detail: "twin skipped conservatively".into(),
            failed_relations: Vec::new(),
            twin_outcome_summary: "called_o0=returned,inlined_o0=refused".into(),
        }),
    };
    let skip_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![skip_meta_case.clone()],
        Vec::new(),
    );
    assert_eq!(skip_rep.counts.metamorphic_skipped, 1);
    let skip_ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: sha.clone(),
        commit_unix_ts: 1_774_000_100,
        environment_profile: "local-itree-diff".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some(sha),
    };
    let skip_rec = SemanticDetailRecord::from_report_and_registry(
        &skip_rep,
        &BugRegistry::new("google/zerocopy"),
        &skip_ctx,
    )
    .expect("valid UNVERIFIED record for skipped metamorphic twin");
    assert_eq!(skip_rec.overall_status, "UNVERIFIED");
    assert_eq!(skip_rec.evidence_blocks[0].overall_status, "UNVERIFIED");
    assert_eq!(skip_rec.differential_runs[0].overall_status, "UNVERIFIED");

    skip_meta_case.metamorphic = None;
    let unskipped_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![skip_meta_case],
        Vec::new(),
    );
    let unskipped_rec = SemanticDetailRecord::from_report_and_registry(
        &unskipped_rep,
        &BugRegistry::new("google/zerocopy"),
        &skip_ctx,
    )
    .unwrap();
    assert_eq!(unskipped_rec.overall_status, "PASS");
}

#[test]
fn shrinkable_fault_ub_with_remaining_sched_and_non_twin_o0_o2() {
    use std::collections::VecDeque;

    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. ShrinkableCase reproducer terminating via `ScheduleDecodeFailed`
    //    preserves `"outcome_kind":"fault_ub"` even when trailing scheduled
    //    `EnvAction`s remain unconsumed.
    let mut sched = EnvSchedule::default();
    sched.per_callee.insert(
        "h0".to_string(),
        VecDeque::from([
            EnvAction::ReturnBytes(vec![0xAA]),
            EnvAction::ReturnBytes(vec![1, 0, 0, 0]),
        ]),
    );
    let sc_ub = ShrinkableCase {
        name: "shrinkable_ub_rem".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 1,
            addend: 0,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![ShrinkStep::HelperCall {
            dst_local: 0,
            helper_id: 0,
            block_id: 0,
            bias: 1,
            rhs_local: None,
        }],
        env_schedule: sched,
        return_local: 0,
    };
    let rs_path = tmp.path().join("shrinkable_ub_rem.rs");
    let bin_path = tmp.path().join("shrinkable_ub_rem_bin");
    fs::write(&rs_path, render_standalone_shrinkable_repro_rs(&sc_ub, "shrink_ub_rem")).unwrap();
    let comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024"])
        .arg(&rs_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .unwrap();
    assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    let out = Command::new(&bin_path).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"outcome_kind\":\"fault_ub\""), "stdout:\n{stdout}");
    assert!(!stdout.contains("\"outcome_kind\":\"unconsumed_schedule\""), "stdout:\n{stdout}");

    // 2. Non-twin `TraceTestCase` preserves `pinned_relations` through
    //    `render_standalone_metamorphic_rust_harness_with_relations`.
    let mut non_twin = generate_fuzz_batch(0x2717_0002, 1).pop().unwrap().to_trace_test_case();
    non_twin.metamorphic_inlined_twin = None;
    let non_twin_src = render_standalone_metamorphic_rust_harness_with_relations(
        &non_twin,
        &["called_rustc_o0_vs_o2".to_string()],
    );
    assert!(non_twin_src.contains("run_single_subject"), "src:\n{non_twin_src}");
    assert!(non_twin_src.contains("--compare-opt"), "src:\n{non_twin_src}");
    let nt_rs = tmp.path().join("non_twin_o0_o2.rs");
    let nt_bin = tmp.path().join("non_twin_o0_o2_bin");
    fs::write(&nt_rs, &non_twin_src).unwrap();
    let nt_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024"])
        .arg(&nt_rs)
        .arg("-o")
        .arg(&nt_bin)
        .output()
        .unwrap();
    assert!(nt_comp.status.success(), "{}", String::from_utf8_lossy(&nt_comp.stderr));
    let nt_run = Command::new(&nt_bin).output().unwrap();
    assert!(!nt_run.status.success(), "non-twin O0/O2 repro must fail without O2 peer");
}

#[test]
fn mir_eval_fingerprints_separate_fault_causes_and_failed_meta_forces_fail() {
    // 1. CanonicalBugFingerprint incorporates `auth_report.mir_eval` and its
    //    normalized fault cause so distinct mir-eval defects never collide.
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let oob_miri =
        mk_auth("miri", TerminalOutcome::FaultUb { detail: "out-of-bounds read".into() });
    let mk_mir_eval_case = |id: &str, me_outcome: TerminalOutcome| CaseReport {
        case_id: id.into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept {
            detail: "miri detected UB while lean accepted".into(),
        },
        expectation_violation: None,
        rustc_dual: RustcDualResult::skipped_for_ub("ub"),
        miri: Some(oob_miri.clone()),
        lean: Some(mk_auth("lean-compositional-itree", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: Some(mk_auth("anneal-mir-eval", me_outcome)),
        metamorphic: None,
    };

    let prog = generate_fuzz_batch(0x2801_0001, 1).pop().unwrap();
    let mut sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |_| true);
    sr.succeeded = true;
    sr.is_one_minimal = true;
    sr.converged_1_minimal = true;

    let rep_div =
        mk_mir_eval_case("me_div", TerminalOutcome::FaultUb { detail: "division by zero".into() });
    let rep_unreach = mk_mir_eval_case(
        "me_unreach",
        TerminalOutcome::FaultUb { detail: "entering unreachable code".into() },
    );
    let rep_none = {
        let mut r = rep_div.clone();
        r.mir_eval = None;
        r
    };

    let fp_from_rep = |r: &CaseReport| {
        let w = WitnessArtifact::from_shrink(
            &r.case_id,
            r.verdict.clone(),
            r.verdict.clone(),
            sr.clone(),
        )
        .with_minimized_report(r.clone());
        CanonicalBugFingerprint::from_1_minimal_witness(&w, r, "main", "mir_v1_itree", None)
            .unwrap()
    };
    let fp_div = fp_from_rep(&rep_div);
    let fp_unreach = fp_from_rep(&rep_unreach);
    let fp_none = fp_from_rep(&rep_none);
    assert_ne!(fp_div.bug_id(), fp_unreach.bug_id());
    assert_ne!(fp_div.bug_id(), fp_none.bug_id());
    assert_ne!(fp_unreach.bug_id(), fp_none.bug_id());

    // 2. A `MetamorphicStatus::Failed` receipt forces parent, evidence block,
    //    and slice `overall_status = "FAIL"` even if the verdict says `Agree`.
    let sha = "a".repeat(40);
    let inconsistent_case = CaseReport {
        case_id: "meta_failed_agree".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: mk_auth("rustc-O0", ret_val.clone()),
            o2: mk_auth("rustc-O2", ret_val.clone()),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(mk_auth("miri", ret_val.clone())),
        lean: Some(mk_auth("lean-compositional-itree", ret_val.clone())),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: Some(MetamorphicDualityReceipt {
            called_lean: mk_auth("lean", ret_val.clone()),
            inlined_lean: mk_auth("lean", ret_val),
            inlined_rustc_parity_ok: false,
            inlined_miri_matched: Some(false),
            tool_error: None,
            status: MetamorphicStatus::Failed,
            duality_holds: false,
            detail: "metamorphic_duality: source-inlined twin mismatch".into(),
            failed_relations: vec!["lean_called_vs_inlined".into()],
            twin_outcome_summary: "called=returned,inlined=returned".into(),
        }),
    };
    let rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![inconsistent_case],
        Vec::new(),
    );
    let ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: sha.clone(),
        commit_unix_ts: 1_774_000_200,
        environment_profile: "local-itree-diff".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some(sha),
    };
    let rec = SemanticDetailRecord::from_report_and_registry(
        &rep,
        &BugRegistry::new("google/zerocopy"),
        &ctx,
    )
    .expect("valid FAIL telemetry record");
    assert_eq!(rec.overall_status, "FAIL");
    assert_eq!(rec.evidence_blocks[0].overall_status, "FAIL");
    assert_eq!(rec.differential_runs[0].overall_status, "FAIL");
    assert_eq!(rec.differential_runs[0].agree_count, 0);
    assert_eq!(rec.differential_runs[0].unsound_missed_fault_count, 1);
}

#[test]
fn single_opt_peer_rejects_untraced_crash_and_meta_preserves_fault_ub_with_rem_sched() {
    use std::collections::VecDeque;

    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Single-subject O0 vs O2 peer reproducer fails closed when both O0 and
    //    O2 exit/abort without emitting a trace line (`trace == None`).
    let mut crash_case = generate_fuzz_batch(0x2901_0001, 1).pop().unwrap().to_trace_test_case();
    crash_case.metamorphic_inlined_twin = None;
    crash_case.env_schedule = EnvSchedule::default();
    crash_case.traced_rust_source = None;
    crash_case.pure_rust_source =
        "pub fn fuzz_entry(_x: u32, _y: u32) -> u32 { std::process::exit(9); }\n".into();
    let crash_src = render_standalone_metamorphic_rust_harness_with_relations(
        &crash_case,
        &["called_rustc_o0_vs_o2".to_string()],
    );
    assert!(crash_src.contains("out.status.signal()"), "src:\n{crash_src}");
    let crash_rs = tmp.path().join("crash_o0_o2.rs");
    let crash_bin = tmp.path().join("crash_o0_o2_bin");
    fs::write(&crash_rs, &crash_src).unwrap();
    let crash_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024"])
        .arg(&crash_rs)
        .arg("-o")
        .arg(&crash_bin)
        .output()
        .unwrap();
    assert!(crash_comp.status.success(), "{}", String::from_utf8_lossy(&crash_comp.stderr));
    let crash_run =
        Command::new(&crash_bin).args(["--compare-opt"]).arg(&crash_bin).output().unwrap();
    assert!(
        !crash_run.status.success(),
        "identical untraced child exits must fail closed rather than exiting 0"
    );

    // 2. Metamorphic `run_called_variant` with `ScheduleDecodeFailed` and
    //    trailing scheduled actions preserves `"outcome_kind":"fault_ub"` and
    //    catches incompatible O0 vs O2 UB causes under `--compare-opt`.
    let mut meta_rem_ub = generate_fuzz_batch(0x2902_0001, 1).pop().unwrap().to_trace_test_case();
    meta_rem_ub.rust_arg_exprs = vec!["1u32".into(), "2u32".into()];
    meta_rem_ub.ret_shape = ReturnShape::Scalar { kind: IntKind::U32 };
    meta_rem_ub.env_schedule = EnvSchedule::default();
    meta_rem_ub
        .env_schedule
        .per_callee
        .insert("h0".to_string(), VecDeque::from([EnvAction::ReturnBytes(vec![0xAA])]));
    meta_rem_ub.traced_rust_source = None;
    meta_rem_ub.pure_rust_source = "pub fn fuzz_entry(_x: u32, _y: u32) -> u32 {\n\
         \x20   if cfg!(debug_assertions) {\n\
         \x20       std::panic::panic_any(crate::anneal_rt::ScheduleDecodeFailed(\n\
         \x20           \"callee `foo` scheduled ReturnBytes invalid: bad\".into(),\n\
         \x20       ));\n\
         \x20   } else {\n\
         \x20       std::panic::panic_any(crate::anneal_rt::ScheduleDecodeFailed(\n\
         \x20           \"callee `bar` scheduled ReturnBytes invalid: bad\".into(),\n\
         \x20       ));\n\
         \x20   }\n\
         }\n"
    .into();
    meta_rem_ub.metamorphic_inlined_twin.as_mut().unwrap().pure_rust_source =
        "pub fn fuzz_entry_inlined(x: u32, y: u32) -> u32 { x.wrapping_add(y) }\n".into();
    let meta_rs = tmp.path().join("meta_rem_ub.rs");
    let meta_o0 = tmp.path().join("meta_rem_ub_o0");
    let meta_o2 = tmp.path().join("meta_rem_ub_o2");
    fs::write(
        &meta_rs,
        render_standalone_metamorphic_rust_harness_with_relations(
            &meta_rem_ub,
            &["called_rustc_o0_vs_o2".to_string()],
        ),
    )
    .unwrap();
    for (extra, out_bin) in [
        (&["-C", "debug-assertions=yes"][..], &meta_o0),
        (&["-C", "opt-level=2", "-C", "debug-assertions=no"][..], &meta_o2),
    ] {
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "-C", "overflow-checks=no"])
            .args(extra)
            .arg(&meta_rs)
            .arg("-o")
            .arg(out_bin)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    }
    let meta_single = Command::new(&meta_o0).arg("--anneal-meta-called").output().unwrap();
    assert!(meta_single.status.success());
    let single_stdout = String::from_utf8_lossy(&meta_single.stdout);
    assert!(single_stdout.contains("\"outcome_kind\":\"fault_ub\""), "stdout:\n{single_stdout}");
    assert!(
        !single_stdout.contains("\"outcome_kind\":\"unconsumed_schedule\""),
        "stdout:\n{single_stdout}"
    );
    let meta_cmp = Command::new(&meta_o0).args(["--compare-opt"]).arg(&meta_o2).output().unwrap();
    assert!(
        !meta_cmp.status.success(),
        "incompatible fault_ub causes with remaining schedule must fail loudly across O0 vs O2"
    );
}

#[test]
fn twin_fault_fingerprints_unclassified_miri_and_freshness_vocabulary_enforced() {
    let tmp = tempfile::tempdir().unwrap();

    // 1. Unclassified Miri UB causes produce distinct canonical causes & BugIds
    //    rather than collapsing to `unclassified:generic`.
    let miri_u1 = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: alpha experimental ub".into() },
    );
    let miri_u2 = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: beta experimental ub".into() },
    );
    let c1 = normalize_miri_ub_cause(Some(&miri_u1));
    let c2 = normalize_miri_ub_cause(Some(&miri_u2));
    assert!(c1.starts_with("unclassified:generic:"), "got {c1}");
    assert!(c2.starts_with("unclassified:generic:"), "got {c2}");
    assert_ne!(c1, c2);

    // 2. `evaluate_metamorphic_duality` preserves distinct inlined twin
    //    fault causes and CallerFrameLaw failure flags inside
    //    `ShrinkFailureSignature` & `BugId` even when called legs match.
    let mem_dig = compute_boundary_mem_digest(&[]);
    let ret_ok = mk_auth(
        "auth",
        TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: mem_dig.clone() },
    );
    let dual_ok = RustcDualResult {
        o0: ret_ok.clone(),
        o2: ret_ok.clone(),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let skipped_rustc = RustcDualResult {
        o0: AuthorityRunResult::skipped_for_ub("rustc-O0", "ub"),
        o2: AuthorityRunResult::skipped_for_ub("rustc-O2", "ub"),
        parity_ok: true,
        skipped_for_ub: true,
        mismatch_detail: None,
    };
    let called_miri_ub = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: dereferencing null pointer".into(),
        },
    );
    let twin_miri_u1 = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: custom twin mismatch one".into() },
    );
    let twin_miri_u2 = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: custom twin mismatch two".into() },
    );
    let receipt_a = evaluate_metamorphic_duality(
        &skipped_rustc,
        Some(&called_miri_ub),
        &ret_ok,
        &skipped_rustc,
        Some(&twin_miri_u1),
        ret_ok.clone(),
    );
    let receipt_b = evaluate_metamorphic_duality(
        &skipped_rustc,
        Some(&called_miri_ub),
        &ret_ok,
        &skipped_rustc,
        Some(&twin_miri_u2),
        ret_ok.clone(),
    );
    assert_ne!(receipt_a.twin_outcome_summary, receipt_b.twin_outcome_summary);

    let prog = generate_fuzz_batch(0x3001_0001, 1).pop().unwrap();
    let case_from_receipt = |case_id: &str, rcpt: MetamorphicDualityReceipt| CaseReport {
        case_id: case_id.into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: rcpt.detail.clone() },
        expectation_violation: None,
        rustc_dual: dual_ok.clone(),
        miri: Some(called_miri_ub.clone()),
        lean: Some(ret_ok.clone()),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: Some(rcpt),
    };
    let rep_a = case_from_receipt("meta_twin_fp_a", receipt_a);
    let rep_b = case_from_receipt("meta_twin_fp_b", receipt_b);
    let sig_a = ShrinkFailureSignature::from_case_report(&rep_a).unwrap();
    let sig_b = ShrinkFailureSignature::from_case_report(&rep_b).unwrap();
    let (w_a, err_a) = shrink_and_build_witness_with_budget(
        "meta_twin_fp_a",
        &prog,
        &rep_a.verdict,
        &sig_a,
        ShrinkBudget::default(),
        |_| rep_a.clone(),
    );
    assert!(err_a.is_none());
    let (w_b, err_b) = shrink_and_build_witness_with_budget(
        "meta_twin_fp_b",
        &prog,
        &rep_b.verdict,
        &sig_b,
        ShrinkBudget::default(),
        |_| rep_b.clone(),
    );
    assert!(err_b.is_none());
    let fp_a =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_a, &rep_a, "main", "mir_v1_itree", None)
            .unwrap();
    let fp_b =
        CanonicalBugFingerprint::from_1_minimal_witness(&w_b, &rep_b, "main", "mir_v1_itree", None)
            .unwrap();
    assert_ne!(fp_a.bug_id(), fp_b.bug_id());

    // 3. Unknown `build_freshness` strings are rejected in parent, evidence
    //    blocks, and KnownBugsExport before writing disk files.
    let bad_detail = SemanticDetailRecord {
        schema: SEMANTIC_DETAIL_SCHEMA.to_string(),
        alpha_notice: ALPHA_BANNER_DEFAULT.to_string(),
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        commit_sha: "1111111111111111111111111111111111111111".to_string(),
        commit_unix_ts: 1_700_000_000,
        mir_dialect: "mir_v1_itree".to_string(),
        environment_profile: "test".to_string(),
        trust_tier: TRUST_TIER_DEFAULT.to_string(),
        build_freshness: "bogus_freshness".to_string(),
        build_exit_code: 0,
        overall_status: "UNVERIFIED".to_string(),
        source_url: String::new(),
        evidence_blocks: vec![EvidenceBlockTelemetry {
            domain: "differential_oracle".to_string(),
            evidence_grade: "empirical_difftest".to_string(),
            build_freshness: "stale".to_string(),
            build_exit_code: 0,
            overall_status: "UNVERIFIED".to_string(),
        }],
        differential_runs: Vec::new(),
        known_bugs: Vec::new(),
    };
    assert!(bad_detail.validate_honesty().is_err());
    let detail_path = tmp.path().join("bad_detail.jsonl");
    assert!(bad_detail.write_jsonl(&detail_path).is_err());
    assert!(!detail_path.exists());

    let mut bad_block_detail = bad_detail;
    bad_block_detail.build_freshness = "stale".to_string();
    bad_block_detail.evidence_blocks[0].build_freshness = "unknown_enum_val".to_string();
    assert!(bad_block_detail.validate_honesty().is_err());
    assert!(bad_block_detail.write_jsonl(&detail_path).is_err());

    let bad_kb = KnownBugsExport {
        schema: "anneal-known-bugs/v1".to_string(),
        alpha_notice: ALPHA_BANNER_DEFAULT.to_string(),
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        commit_sha: "1111111111111111111111111111111111111111".to_string(),
        dialect_key: "mir_v1_itree".to_string(),
        build_freshness: "invented".to_string(),
        build_exit_code: 0,
        provisional_count: 0,
        known_bugs: Vec::new(),
    };
    let kb_path = tmp.path().join("bad_kb.json");
    assert!(bad_kb.write_to_path(&kb_path).is_err());
    assert!(!kb_path.exists());

    // 4. `TelemetryContext::discover` and `verify_head_build_provenance_with`
    //    never self-attest `verified_at_head` from env flags alone.
    assert!(BuildFreshness::parse("verified_at_head").is_some());
    assert!(BuildFreshness::parse("invalid").is_none());
    let anneal_root = workspace_anneal_root().unwrap();
    let ctx = TelemetryContext::discover(&anneal_root);
    assert!(!ctx.head_provenance_verified);
    assert!(!verify_head_build_provenance_with(
        &anneal_root,
        ctx.discovered_head_sha.as_deref(),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        std::env::current_exe().ok().as_deref(),
        ctx.discovered_head_sha.as_deref(),
        Some("1"),
    ));
}

#[test]
fn r28_bundle_convergence_companion_borrow_slice_block_known_bugs_and_id_binding() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let prog = FuzzProgram {
        seed: 0x2801,
        index: 0,
        input_x: 5,
        input_y: 9,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);

    // 1. `WitnessBundle::try_from_witness` rejects unconverged artifacts.
    let mut bad_succ = ok_sr.clone();
    bad_succ.succeeded = false;
    let art_bad_succ = WitnessArtifact::from_shrink(
        "bad_succ",
        TraceVerdict::UnsoundAccept { detail: "d".into() },
        TraceVerdict::UnsoundAccept { detail: "d".into() },
        bad_succ,
    );
    assert!(WitnessBundle::try_from_witness(art_bad_succ, None).is_err());

    let mut bad_min = ok_sr.clone();
    bad_min.is_one_minimal = false;
    let art_bad_min = WitnessArtifact::from_shrink(
        "bad_min",
        TraceVerdict::UnsoundAccept { detail: "d".into() },
        TraceVerdict::UnsoundAccept { detail: "d".into() },
        bad_min,
    );
    assert!(WitnessBundle::try_from_witness(art_bad_min, None).is_err());

    // 2. Companion `<case_id>.witness.json` stores the normalized artifact
    //    rather than stale pre-bundle fields/source.
    let mut meta_rep = mk_ub_case_report(
        "r28_companion",
        "Undefined Behavior: Data race detected between read and write",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri UB vs lean accept".into() },
    );
    meta_rep.verdict =
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() };
    let stale_verdict = TraceVerdict::UnsoundAccept { detail: "stale_pre_bundle_verdict".into() };
    let mut stale_art =
        WitnessArtifact::from_shrink("r28_companion", stale_verdict.clone(), stale_verdict, ok_sr);
    stale_art.reproducer_rust_source = "// STALE UNNORMALIZED SOURCE".to_string();
    stale_art.repro_case_id = "repro_stale_id".to_string();
    stale_art.minimized_report = Some(Box::new(meta_rep.clone()));
    let wdir = tmp.path().join("companion_sync");
    let mut emitted = Vec::new();
    let mut rep_out = meta_rep.clone();
    anneal_itree_diff::apply_fuzz_shrink_outcome(
        &mut rep_out,
        Some(&wdir),
        &mut emitted,
        stale_art,
        None,
    );
    assert_eq!(emitted.len(), 1);
    let comp_bytes = fs::read(wdir.join("r28_companion.witness.json")).unwrap();
    let comp_art: WitnessArtifact = serde_json::from_slice(&comp_bytes).unwrap();
    let bid = comp_art.repro_case_id.strip_prefix("repro_").unwrap();
    let canon_bytes = fs::read(wdir.join(format!("witness_{bid}.json"))).unwrap();
    let canon_art: WitnessArtifact = serde_json::from_slice(&canon_bytes).unwrap();
    assert_eq!(comp_art, canon_art);
    assert!(comp_art.signature.is_some());
    assert!(!comp_art.reproducer_rust_source.contains("STALE UNNORMALIZED SOURCE"));

    // 3. Noncausal `ShrinkStep::Borrow { mutable: true }` canonicalizes to
    //    `mutable: false` and preserves causal `mutable: true`.
    let mk_borrow_case = |mutable: bool| ShrinkableCase {
        name: "borrow_mut".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 0, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![
            ShrinkStep::Alloc { handle: HandleId(0), size: 4, align: 1, local_id: 0 },
            ShrinkStep::Borrow { dst: HandleId(1), src: HandleId(0), mutable, local_id: 0 },
            ShrinkStep::UseHandle { handle: HandleId(1), offset: 0, len: 1, align: 1, local_id: 0 },
        ],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let borrow_noncausal =
        |c: &ShrinkableCase| c.steps.iter().any(|s| matches!(s, ShrinkStep::Borrow { .. }));
    let b_mut_res = shrink_case_two_tier_with_budget(
        &mk_borrow_case(true),
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        borrow_noncausal,
    );
    let b_shr_res = shrink_case_two_tier_with_budget(
        &mk_borrow_case(false),
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        borrow_noncausal,
    );
    assert!(b_mut_res.succeeded && b_mut_res.is_one_minimal);
    assert!(b_shr_res.succeeded && b_shr_res.is_one_minimal);
    assert_eq!(
        canonical_shrinkable_case_skeleton_hash(&b_mut_res.minimized),
        canonical_shrinkable_case_skeleton_hash(&b_shr_res.minimized),
    );
    assert!(
        matches!(
            b_mut_res.minimized.steps.as_slice(),
            [ShrinkStep::Alloc { .. }, ShrinkStep::Borrow { mutable: false, .. }]
        ),
        "expected shrunk noncausal Borrow {{ mutable: false }}, got {:?}",
        b_mut_res.minimized.steps
    );
    let b_causal_res = shrink_case_two_tier_with_budget(
        &mk_borrow_case(true),
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        |c| c.steps.iter().any(|s| matches!(s, ShrinkStep::Borrow { mutable: true, .. })),
    );
    assert!(
        matches!(
            b_causal_res.minimized.steps.as_slice(),
            [ShrinkStep::Alloc { .. }, ShrinkStep::Borrow { mutable: true, .. }]
        ),
        "expected causal mutable Borrow preserved, got {:?}",
        b_causal_res.minimized.steps
    );

    // 4. `validate_honesty` rejects failed differential slices paired with a
    //    `PASS`/`UNVERIFIED` or missing `differential_oracle` evidence block.
    let fail_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![meta_rep.clone()],
        Vec::new(),
    );
    let clean_ctx = TelemetryContext {
        repo: "google/zerocopy".into(),
        branch: "main".into(),
        branch_scope: "main".into(),
        exposed_on_main: true,
        commit_sha: "1111111111111111111111111111111111111111".into(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "test".into(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: Some(BuildFreshness::VerifiedAtHead),
        build_exit_code_override: Some(0),
        head_provenance_verified: true,
        discovered_head_sha: Some("1111111111111111111111111111111111111111".into()),
    };
    let fail_detail = SemanticDetailRecord::from_report_and_registry(
        &fail_rep,
        &BugRegistry::new("google/zerocopy"),
        &clean_ctx,
    )
    .unwrap();
    for bad_blk in ["PASS", "UNVERIFIED"] {
        let mut altered = fail_detail.clone();
        altered.evidence_blocks[0].overall_status = bad_blk.to_string();
        let err_path = tmp.path().join(format!("fail_slice_{bad_blk}.jsonl"));
        assert!(altered.validate_honesty().is_err());
        assert!(altered.write_jsonl(&err_path).is_err());
        assert!(!err_path.exists());
    }
    let mut missing_block = fail_detail;
    missing_block.evidence_blocks[0].domain = "other_domain".to_string();
    assert!(missing_block.validate_honesty().is_err());

    // 5. `KnownBugsExport::write_to_path` enforces record schema, `bug_id`,
    //    `status` vocabulary, and `fixed_sha` invariants on both JSON & NDJSON.
    let valid_kb_row = KnownBugRecord {
        schema_version: KNOWN_BUG_RECORD_SCHEMA.to_string(),
        repo: "google/zerocopy".to_string(),
        bug_id: "ITREE-MISSUB-0123456789ab".to_string(),
        branch_scope: "main".to_string(),
        exposed_on_main: true,
        dialect_key: "mir_v1_itree".to_string(),
        source: "itree_diff_fuzzer".to_string(),
        status: "fixed".to_string(),
        severity: "P0".to_string(),
        witness_polarity: "negative_bug".to_string(),
        summary: "fixed bug".to_string(),
        tracking_url: String::new(),
        repro_case_id: "repro_0123".to_string(),
        introduced_sha: "1111111111111111111111111111111111111111".to_string(),
        fixed_sha: "2222222222222222222222222222222222222222".to_string(),
    };
    let make_kb_export = |row: KnownBugRecord| KnownBugsExport {
        schema: "anneal-known-bugs/v1".to_string(),
        alpha_notice: ALPHA_BANNER_DEFAULT.to_string(),
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        commit_sha: "1111111111111111111111111111111111111111".to_string(),
        dialect_key: "mir_v1_itree".to_string(),
        build_freshness: "verified_at_head".to_string(),
        build_exit_code: 0,
        provisional_count: 0,
        known_bugs: vec![row],
    };
    let mut fixed_no_sha = valid_kb_row.clone();
    fixed_no_sha.fixed_sha = "   ".to_string();
    let mut bad_status_row = valid_kb_row.clone();
    bad_status_row.status = "bogus_status".to_string();
    let mut bad_schema_row = valid_kb_row;
    bad_schema_row.schema_version = "wrong/v0".to_string();
    for (idx, bad_row) in [fixed_no_sha, bad_status_row, bad_schema_row].into_iter().enumerate() {
        let exp = make_kb_export(bad_row);
        let p_json = tmp.path().join(format!("bad_row_{idx}.json"));
        let p_ndjson = tmp.path().join(format!("bad_row_{idx}.jsonl"));
        assert!(exp.write_to_path(&p_json).is_err());
        assert!(exp.write_to_path(&p_ndjson).is_err());
        assert!(!p_json.exists() && !p_ndjson.exists());
    }

    // 6. Witnesses sharing `FuzzProgram`, schedule, `ShrinkFailureSignature`,
    //    and verdict string whose reports normalize to distinct Miri UB causes
    //    receive distinct `bundle_id` / `repro_case_id` across artifact,
    //    `WitnessBundle`, and `BugRegistry` (and shrinkable IDs differ too).
    let same_verdict =
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() };
    let rep_stack = mk_ub_case_report(
        "same_prog_stack",
        "Undefined Behavior: attempting a read access using <alloc1>: borrow stack forbids",
        ret_val.clone(),
        same_verdict.clone(),
    );
    let rep_oob = mk_ub_case_report(
        "same_prog_oob",
        "Undefined Behavior: pointer dereference failed: out-of-bounds",
        ret_val,
        same_verdict,
    );
    let sig_common = ShrinkFailureSignature::from_case_report(&rep_stack).unwrap();
    assert_eq!(sig_common, ShrinkFailureSignature::from_case_report(&rep_oob).unwrap());
    let shared_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    let w_stack = WitnessArtifact::from_shrink(
        &rep_stack.case_id,
        rep_stack.verdict.clone(),
        rep_stack.verdict.clone(),
        shared_sr.clone(),
    )
    .with_signature(sig_common.clone())
    .with_minimized_report(rep_stack.clone());
    let w_oob = WitnessArtifact::from_shrink(
        &rep_oob.case_id,
        rep_oob.verdict.clone(),
        rep_oob.verdict.clone(),
        shared_sr,
    )
    .with_signature(sig_common)
    .with_minimized_report(rep_oob.clone());
    assert_ne!(w_stack.repro_case_id, w_oob.repro_case_id);
    let b_stack = WitnessBundle::try_from_witness(w_stack.clone(), None).unwrap();
    let b_oob = WitnessBundle::try_from_witness(w_oob.clone(), None).unwrap();
    assert_ne!(b_stack.bundle_id, b_oob.bundle_id);
    assert_eq!(w_stack.repro_case_id, b_stack.repro_case_id);
    assert_eq!(w_oob.repro_case_id, b_oob.repro_case_id);
    let mut reg_distinct = BugRegistry::new("google/zerocopy");
    let out_stack = reg_distinct.record_witness(
        &w_stack,
        &rep_stack,
        "main",
        true,
        "mir_v1_itree",
        &"1".repeat(40),
        None,
    );
    let out_oob = reg_distinct.record_witness(
        &w_oob,
        &rep_oob,
        "main",
        true,
        "mir_v1_itree",
        &"1".repeat(40),
        None,
    );
    match (out_stack, out_oob) {
        (
            DedupRecordOutcome::NewBug { bug_id: id1, repro_case_id: r1, .. },
            DedupRecordOutcome::NewBug { bug_id: id2, repro_case_id: r2, .. },
        ) => {
            assert_ne!(id1, id2);
            assert_ne!(r1, r2);
            assert_eq!(r1, b_stack.repro_case_id);
            assert_eq!(r2, b_oob.repro_case_id);
        }
        other => panic!("expected two distinct NewBug entries, got {other:?}"),
    }
}

#[test]
fn r29_bundle_failing_verdict_id_validation_and_embedded_known_bug_status() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let prog = FuzzProgram {
        seed: 0x2901,
        index: 0,
        input_x: 3,
        input_y: 9,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);

    // 1. `WitnessBundle::try_from_witness` rejects converged artifacts whose
    //    `verdict` is non-failing (`Agree` or non-undeclared
    //    `ConservativeOverApprox`), even when a forged signature is attached.
    let agree_art = WitnessArtifact::from_shrink(
        "r29_agree",
        TraceVerdict::Agree,
        TraceVerdict::Agree,
        ok_sr.clone(),
    );
    assert!(WitnessBundle::try_from_witness(agree_art.clone(), None).is_err());

    let rep_ub = mk_ub_case_report(
        "r29_ub",
        "Undefined Behavior: Data race detected between read and write",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let sig_ub = ShrinkFailureSignature::from_case_report(&rep_ub).unwrap();
    let agree_forged_sig = agree_art.with_signature(sig_ub);
    assert!(WitnessBundle::try_from_witness(agree_forged_sig, None).is_err());

    let benign_cons = WitnessArtifact::from_shrink(
        "r29_cons",
        TraceVerdict::ConservativeOverApprox {
            reason: "unsupported".into(),
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
        },
        TraceVerdict::ConservativeOverApprox {
            reason: "unsupported".into(),
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
        },
        ok_sr.clone(),
    );
    assert!(WitnessBundle::try_from_witness(benign_cons, None).is_err());

    // 2. `WitnessBundle::write_to_dir` rejects tampered/traversal `bundle_id`
    //    and `skel_hash` without writing outside the target directory.
    let valid_art = WitnessArtifact::from_shrink(
        &rep_ub.case_id,
        rep_ub.verdict.clone(),
        rep_ub.verdict.clone(),
        ok_sr,
    )
    .with_minimized_report(rep_ub.clone());
    let valid_bundle = WitnessBundle::try_from_witness(valid_art, None).unwrap();
    let nested_dir = tmp.path().join("bundles").join("sub");
    let outside_dir = tmp.path().join("escaped_dir");
    fs::create_dir_all(&outside_dir).unwrap();

    let mut trav_bundle = valid_bundle.clone();
    trav_bundle.bundle_id = "../../escaped_dir/evil".to_string();
    assert!(trav_bundle.write_to_dir(&nested_dir).is_err());
    assert!(!outside_dir.join("evil.rs").exists());
    assert!(!tmp.path().join("bundles").join("repro_evil.rs").exists());

    let mut mismatched_hex = valid_bundle.clone();
    mismatched_hex.bundle_id = "000000000000_000000000000000000000000".to_string();
    assert!(mismatched_hex.write_to_dir(&nested_dir).is_err());

    let mut bad_skel = valid_bundle.clone();
    bad_skel.bundle_id.clear();
    bad_skel.skel_hash = "../escape".to_string();
    assert!(bad_skel.write_to_dir(&nested_dir).is_err());

    let written = valid_bundle.write_to_dir(&nested_dir).unwrap();
    assert!(written.repro_rs_path.is_file());

    // 3. `SemanticDetailRecord::validate_honesty` and `write_jsonl` reject
    //    embedded `known_bugs` entries with invalid `BugStatus` values.
    let diff_report = DifferentialReport::from_cases(
        "miri=available",
        true,
        true,
        "mir_eval=unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep_ub],
        Vec::new(),
    );
    let mut reg = BugRegistry::new("google/zerocopy");
    let mut ctx = TelemetryContext::discover(std::path::Path::new("/nonexistent_anneal_root"));
    ctx.commit_sha = "1".repeat(40);
    ctx.head_provenance_verified = true;
    ctx.build_freshness_override = Some(BuildFreshness::VerifiedAtHead);
    ctx.build_exit_code_override = Some(0);
    let _ = reg.record_witness(
        &valid_bundle.artifact,
        &diff_report.cases[0],
        "main",
        true,
        "mir_v1_itree",
        &ctx.commit_sha,
        None,
    );
    let mut detail_rec =
        SemanticDetailRecord::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();
    assert_eq!(detail_rec.known_bugs.len(), 1);
    for bad_status in ["closed", "FIXED", "typo_open", ""] {
        let mut bad_rec = detail_rec.clone();
        bad_rec.known_bugs[0].status = bad_status.to_string();
        assert!(
            bad_rec.validate_honesty().is_err(),
            "expected validate_honesty to reject unknown status {bad_status:?}"
        );
        assert!(bad_rec.write_jsonl(&tmp.path().join("bad_detail.jsonl")).is_err());
    }
    detail_rec.known_bugs[0].status = "fixed".to_string();
    detail_rec.known_bugs[0].resolved_by_commit = Some("deadbeef".to_string());
    assert!(detail_rec.validate_honesty().is_err());
    detail_rec.known_bugs[0].resolved_by_commit = Some("2".repeat(40));
    assert!(detail_rec.validate_honesty().is_ok());
}

#[test]
fn reportless_signature_bundle_members_volatile_miri_and_known_bug_freshness() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let prog = FuzzProgram {
        seed: 0x3001,
        index: 0,
        input_x: 3,
        input_y: 9,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);

    // 1. Report-less `WitnessBundle::try_from_witness` rejects contradicting
    //    `mismatch_category` or spurious relation pins on stored signatures.
    let term_rep = mk_ub_case_report(
        "r30_term",
        "Undefined Behavior: dereferencing null pointer",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".into() },
    );
    let term_sig = ShrinkFailureSignature::from_case_report(&term_rep).unwrap();
    let mismatched_art = WitnessArtifact::from_shrink(
        "r30_mismatched_sig",
        TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".into() },
        TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".into() },
        ok_sr.clone(),
    )
    .with_signature(term_sig);
    assert!(WitnessBundle::try_from_witness(mismatched_art, None).is_err());

    let o0_o2_verdict = TraceVerdict::UnsoundAccept { detail: "rustc O0 vs O2 mismatch".into() };
    let mut spurious_rel_sig =
        ShrinkFailureSignature::from_verdict_and_legs(&o0_o2_verdict, None, None).unwrap();
    spurious_rel_sig.metamorphic_relations = vec!["called_rustc_o0_vs_o2".into()];
    let spurious_art = WitnessArtifact::from_shrink(
        "r30_spurious_rel",
        o0_o2_verdict.clone(),
        o0_o2_verdict,
        ok_sr.clone(),
    )
    .with_signature(spurious_rel_sig);
    assert!(WitnessBundle::try_from_witness(spurious_art, None).is_err());

    // 2. `WitnessBundle::write_to_dir` rejects tampered `repro_rust_source`,
    //    `mir_lean_source`, `repro_case_id`, or `artifact` fields even when
    //    `bundle_id` and `skel_hash` remain canonical.
    let rep_ub = mk_ub_case_report(
        "r30_ub",
        "Undefined Behavior: Data race detected between read and write",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let valid_art = WitnessArtifact::from_shrink(
        &rep_ub.case_id,
        rep_ub.verdict.clone(),
        rep_ub.verdict.clone(),
        ok_sr,
    )
    .with_minimized_report(rep_ub.clone());
    let valid_bundle = WitnessBundle::try_from_witness(valid_art, None).unwrap();
    let bdir = tmp.path().join("canonical_bundle_members");

    let mut bad_rs = valid_bundle.clone();
    bad_rs.repro_rust_source = "fn main() {}\n".into();
    assert!(bad_rs.write_to_dir(&bdir).is_err());

    let mut empty_bid = valid_bundle.clone();
    empty_bid.bundle_id.clear();
    assert!(empty_bid.write_to_dir(&bdir).is_err());

    let mut bad_lean = valid_bundle.clone();
    bad_lean.mir_lean_source = "-- tampered\n".into();
    assert!(bad_lean.write_to_dir(&bdir).is_err());

    let mut bad_case_id = valid_bundle.clone();
    bad_case_id.repro_case_id = "repro_000000000000_000000000000000000000000".into();
    assert!(bad_case_id.write_to_dir(&bdir).is_err());

    let mut bad_art = valid_bundle.clone();
    bad_art.artifact.shrink.minimized.input_x = 999;
    assert!(bad_art.write_to_dir(&bdir).is_err());
    assert!(!bdir.join(format!("repro_{}.rs", valid_bundle.bundle_id)).exists());

    // 3. Unclassified Miri UB diagnostics differing only in volatile
    //    allocation IDs, hex addresses, borrow tags, and numeric offsets merge
    //    to one `generic:<digest>` and `BugId`, while integer-width tokens stay
    //    distinct.
    let m_a = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: memory fault at alloc12+0x8 (0x7ffe11223344) tag <99> offset 24 u32".into(),
        },
    );
    let m_b = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: memory fault at alloc590+0x20 (0x5555deadbeef) tag <401> offset 64 u32".into(),
        },
    );
    let m_c = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: memory fault at alloc590+0x20 (0x5555deadbeef) tag <401> offset 64 u64".into(),
        },
    );
    assert_eq!(normalize_miri_ub_cause(Some(&m_a)), normalize_miri_ub_cause(Some(&m_b)));
    assert_ne!(normalize_miri_ub_cause(Some(&m_a)), normalize_miri_ub_cause(Some(&m_c)));

    // 4. `KnownBugsExport` and `SemanticDetailRecord` enforce consistent
    //    `(build_freshness, build_exit_code)` pairs before serialization.
    let diff_report = DifferentialReport::from_cases(
        "miri=available",
        true,
        true,
        "mir_eval=unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep_ub],
        Vec::new(),
    );
    let mut reg = BugRegistry::new("google/zerocopy");
    let mut ctx = TelemetryContext::discover(std::path::Path::new("/nonexistent_anneal_root"));
    ctx.commit_sha = "1".repeat(40);
    ctx.head_provenance_verified = true;
    ctx.build_freshness_override = Some(BuildFreshness::VerifiedAtHead);
    ctx.build_exit_code_override = Some(1);
    assert!(KnownBugsExport::from_report_and_registry(&diff_report, &reg, &ctx).is_err());
    ctx.build_exit_code_override = Some(0);
    let _ = reg.record_witness(
        &valid_bundle.artifact,
        &diff_report.cases[0],
        "main",
        true,
        "mir_v1_itree",
        &ctx.commit_sha,
        None,
    );
    let valid_kb = KnownBugsExport::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();
    for (bad_fresh, bad_exit) in [
        ("verified_at_head", 1i64),
        ("failed_or_oom", 0i64),
        ("timed_out", 0i64),
        ("not_run", 0i64),
    ] {
        let mut bad_kb = valid_kb.clone();
        bad_kb.build_freshness = bad_fresh.to_string();
        bad_kb.build_exit_code = bad_exit;
        assert!(bad_kb.validate().is_err());
        assert!(bad_kb.write_to_path(&tmp.path().join("bad_kb.json")).is_err());
        assert!(bad_kb.write_to_path(&tmp.path().join("bad_kb.jsonl")).is_err());
    }
    for bad_status in ["open", "triaged"] {
        let mut bad_sha_kb = valid_kb.clone();
        bad_sha_kb.known_bugs[0].status = bad_status.to_string();
        bad_sha_kb.known_bugs[0].fixed_sha = "deadbeef".to_string();
        assert!(bad_sha_kb.validate().is_err());
        assert!(bad_sha_kb.write_to_path(&tmp.path().join("bad_sha_kb.json")).is_err());
        assert!(bad_sha_kb.write_to_path(&tmp.path().join("bad_sha_kb.jsonl")).is_err());
    }
    let mut bad_detail =
        SemanticDetailRecord::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();
    for bad_status in ["open", "triaged"] {
        let mut bad_sha_detail = bad_detail.clone();
        bad_sha_detail.known_bugs[0].status = bad_status.to_string();
        bad_sha_detail.known_bugs[0].resolved_by_commit = Some("deadbeef".to_string());
        assert!(bad_sha_detail.validate_honesty().is_err());
    }
    let mut bad_notice_detail = bad_detail.clone();
    bad_notice_detail.alpha_notice = "custom production notice".to_string();
    assert!(bad_notice_detail.validate_honesty().is_err());
    let bad_notice_path = tmp.path().join("bad_notice_detail.jsonl");
    assert!(bad_notice_detail.write_jsonl(&bad_notice_path).is_err());
    assert!(!bad_notice_path.exists());

    let mut bad_tier_detail = bad_detail.clone();
    bad_tier_detail.trust_tier = "audited".to_string();
    assert!(bad_tier_detail.validate_honesty().is_err());
    let bad_tier_path = tmp.path().join("bad_tier_detail.jsonl");
    assert!(bad_tier_detail.write_jsonl(&bad_tier_path).is_err());
    assert!(!bad_tier_path.exists());

    for bad_commit in ["", "   "] {
        let mut bad_commit_kb = valid_kb.clone();
        bad_commit_kb.commit_sha = bad_commit.to_string();
        assert!(bad_commit_kb.validate().is_err());
        let bad_json = tmp.path().join("bad_commit_kb.json");
        let bad_jsonl = tmp.path().join("bad_commit_kb.jsonl");
        assert!(bad_commit_kb.write_to_path(&bad_json).is_err());
        assert!(bad_commit_kb.write_to_path(&bad_jsonl).is_err());
        assert!(!bad_json.exists());
        assert!(!bad_jsonl.exists());
    }
    let mut bad_notice_kb = valid_kb.clone();
    bad_notice_kb.alpha_notice = "custom banner".to_string();
    assert!(bad_notice_kb.validate().is_err());
    let bad_kb_notice_json = tmp.path().join("bad_notice_kb.json");
    let bad_kb_notice_jsonl = tmp.path().join("bad_notice_kb.jsonl");
    assert!(bad_notice_kb.write_to_path(&bad_kb_notice_json).is_err());
    assert!(bad_notice_kb.write_to_path(&bad_kb_notice_jsonl).is_err());
    assert!(!bad_kb_notice_json.exists());
    assert!(!bad_kb_notice_jsonl.exists());

    bad_detail.build_freshness = "verified_at_head".to_string();
    bad_detail.build_exit_code = 1;
    assert!(bad_detail.validate_honesty().is_err());
}

#[test]
fn orphan_witness_envelope_scope_and_generic_caller_frame_pin_fail_closed() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let prog = FuzzProgram {
        seed: 0x3201,
        index: 0,
        input_x: 3,
        input_y: 9,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);

    // 1. Orphan witnesses (invalid `report_index` and unmatched `case_id`)
    //    never enter `BugRegistry` even when `minimized_report` is set.
    let rep_ub = mk_ub_case_report(
        "r32_in_run",
        "Undefined Behavior: Data race detected between read and write",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let orphan_rep = mk_ub_case_report(
        "r32_orphan",
        "Undefined Behavior: dereferencing null pointer",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri null deref vs lean accept".into() },
    );
    let orphan_wit = WitnessArtifact::from_shrink(
        "r32_orphan",
        orphan_rep.verdict.clone(),
        orphan_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_minimized_report(orphan_rep)
    .with_report_index(99);
    let mut reg_orphan = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut reg_orphan,
        std::slice::from_ref(&rep_ub),
        &[orphan_wit],
        "main",
        true,
        "mir_v1_itree",
        &"1".repeat(40),
    );
    assert!(reg_orphan.buckets.is_empty());
    assert_eq!(reg_orphan.provisional_cases.len(), 1);

    // 2. `KnownBugsExport` rejects rows outside envelope `repo` /
    //    `dialect_key`, and `SemanticDetailRecord` rejects `mir_dialect`
    //    mismatch.
    let valid_wit = WitnessArtifact::from_shrink(
        &rep_ub.case_id,
        rep_ub.verdict.clone(),
        rep_ub.verdict.clone(),
        ok_sr.clone(),
    )
    .with_minimized_report(rep_ub.clone());
    let mut reg = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut reg,
        std::slice::from_ref(&rep_ub),
        &[valid_wit],
        "main",
        true,
        "mir_v1_itree",
        &"1".repeat(40),
    );
    let diff_report = DifferentialReport::from_cases(
        "miri=available",
        true,
        true,
        "mir_eval=unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep_ub],
        Vec::new(),
    );
    let mut ctx = TelemetryContext::discover(std::path::Path::new("/nonexistent_anneal_root"));
    ctx.commit_sha = "1".repeat(40);
    ctx.head_provenance_verified = true;
    ctx.build_freshness_override = Some(BuildFreshness::VerifiedAtHead);
    ctx.build_exit_code_override = Some(0);
    let valid_kb = KnownBugsExport::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();

    let mut wrong_repo_kb = valid_kb.clone();
    wrong_repo_kb.known_bugs[0].repo = "other/repo".to_string();
    assert!(wrong_repo_kb.validate().is_err());
    assert!(wrong_repo_kb.write_to_path(&tmp.path().join("wrong_repo.json")).is_err());
    assert!(wrong_repo_kb.write_to_path(&tmp.path().join("wrong_repo.jsonl")).is_err());

    let mut wrong_dialect_kb = valid_kb;
    wrong_dialect_kb.known_bugs[0].dialect_key = "mir_v2_tree_borrows".to_string();
    assert!(wrong_dialect_kb.validate().is_err());
    assert!(wrong_dialect_kb.write_to_path(&tmp.path().join("wrong_dialect.json")).is_err());
    assert!(wrong_dialect_kb.write_to_path(&tmp.path().join("wrong_dialect.jsonl")).is_err());

    let mut wrong_detail =
        SemanticDetailRecord::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();
    wrong_detail.known_bugs[0].mir_dialect = "mir_v2_tree_borrows".to_string();
    assert!(wrong_detail.validate_honesty().is_err());

    // 3. Report-less generic `metamorphic_caller_frame_law` pin compiles as a
    //    standalone metamorphic reproducer that fails closed natively rather
    //    than claiming rustc replay coverage for a potential Lean/Miri fault.
    let frame_verdict = TraceVerdict::UnsoundAccept {
        detail: "metamorphic_duality: CallerFrameLaw failed in metamorphic pair".to_string(),
    };
    let frame_art =
        WitnessArtifact::from_shrink("r32_frame", frame_verdict.clone(), frame_verdict, ok_sr);
    let frame_bundle = WitnessBundle::try_from_witness(frame_art, None).unwrap();
    assert!(frame_bundle.repro_rust_source.contains("\"metamorphic_caller_frame_law\""));
    let frame_rs = tmp.path().join("generic_caller_frame_repro.rs");
    let frame_bin = tmp.path().join("generic_caller_frame_bin");
    fs::write(&frame_rs, &frame_bundle.repro_rust_source).unwrap();
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");
    let comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024"])
        .arg(&frame_rs)
        .arg("-o")
        .arg(&frame_bin)
        .output()
        .unwrap();
    assert!(comp.status.success(), "{}", String::from_utf8_lossy(&comp.stderr));
    let run = Command::new(&frame_bin).output().unwrap();
    assert!(
        !run.status.success(),
        "generic metamorphic_caller_frame_law must fail closed when native rustc passes"
    );
}

#[test]
fn telemetry_row_provenance_and_safe_witness_case_id_guards() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep_ub = mk_ub_case_report(
        "prov_case",
        "Undefined Behavior: Data race detected between read and write",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let prog = FuzzProgram {
        seed: 0x3401,
        index: 0,
        input_x: 3,
        input_y: 9,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);
    let valid_wit = WitnessArtifact::from_shrink(
        "prov_case",
        rep_ub.verdict.clone(),
        rep_ub.verdict.clone(),
        ok_sr,
    )
    .with_minimized_report(rep_ub.clone());

    let mut reg = BugRegistry::new("google/zerocopy");
    let _ = reg.record_witness(
        &valid_wit,
        &rep_ub,
        "main",
        true,
        "mir_v1_itree",
        &"1".repeat(40),
        None,
    );
    let diff_report = DifferentialReport::from_cases(
        "miri=available",
        true,
        true,
        "mir_eval=unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep_ub.clone()],
        Vec::new(),
    );
    let mut ctx = TelemetryContext::discover(std::path::Path::new("/nonexistent_anneal_root"));
    ctx.commit_sha = "1".repeat(40);
    ctx.head_provenance_verified = true;
    ctx.build_freshness_override = Some(BuildFreshness::VerifiedAtHead);
    ctx.build_exit_code_override = Some(0);

    let base_detail =
        SemanticDetailRecord::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();
    for bad_repo in ["", "   "] {
        let mut d = base_detail.clone();
        d.repo = bad_repo.to_string();
        assert!(d.validate_honesty().is_err());
        let p = tmp.path().join("empty_repo_detail.jsonl");
        assert!(d.write_jsonl(&p).is_err());
        assert!(!p.exists());
    }
    for bad_intro in ["", "   "] {
        let mut d = base_detail.clone();
        d.known_bugs[0].introduced_sha = bad_intro.to_string();
        assert!(d.validate_honesty().is_err());
        let p = tmp.path().join("empty_intro_detail.jsonl");
        assert!(d.write_jsonl(&p).is_err());
        assert!(!p.exists());
    }

    let base_kb = KnownBugsExport::from_report_and_registry(&diff_report, &reg, &ctx).unwrap();
    for bad_intro in ["", "   "] {
        let mut kb = base_kb.clone();
        kb.known_bugs[0].introduced_sha = bad_intro.to_string();
        assert!(kb.validate().is_err());
        let p_json = tmp.path().join("empty_intro_kb.json");
        let p_jsonl = tmp.path().join("empty_intro_kb.jsonl");
        assert!(kb.write_to_path(&p_json).is_err());
        assert!(kb.write_to_path(&p_jsonl).is_err());
        assert!(!p_json.exists() && !p_jsonl.exists());
    }

    // Companion `.witness.json` emission rejects unsafe `case_id` paths without
    // creating parent directories or touching external files.
    let wdir = tmp.path().join("witness_out");
    let escaped_sentinel = tmp.path().join("sentinel.witness.json");
    fs::write(&escaped_sentinel, b"sentinel").unwrap();
    for bad_id in ["../sentinel", "/tmp/outside_escape", "nested/sub", "nested\\sub", "", ".", ".."]
    {
        let mut rep_bad = rep_ub.clone();
        rep_bad.case_id = bad_id.to_string();
        let mut out_wits = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        anneal_itree_diff::apply_fuzz_shrink_outcome_with_seen(
            &mut rep_bad,
            Some(&wdir),
            &mut out_wits,
            valid_wit.clone(),
            None,
            Some(&mut seen),
        );
        assert!(out_wits.is_empty(), "unsafe case_id {bad_id:?} must not emit witness");
        assert!(
            matches!(
                &rep_bad.verdict,
                TraceVerdict::UnsoundAccept { detail }
                    if detail.contains("secondary witness-writer tool error:")
            ),
            "unsafe case_id {bad_id:?} verdict={:?}",
            rep_bad.verdict
        );
    }
    let mut rep_noncrit = rep_ub;
    rep_noncrit.verdict = TraceVerdict::ConservativeOverApprox {
        reason: "safe conservative".into(),
        ub_refutation_disallowed: true,
        undeclared_ub_fault: false,
    };
    rep_noncrit.case_id = "../sentinel".to_string();
    let mut out_noncrit = Vec::new();
    anneal_itree_diff::apply_fuzz_shrink_outcome(
        &mut rep_noncrit,
        Some(&wdir),
        &mut out_noncrit,
        valid_wit,
        None,
    );
    assert!(out_noncrit.is_empty());
    assert!(
        matches!(
            &rep_noncrit.verdict,
            TraceVerdict::ToolError { authority, .. } if authority == "witness-writer"
        ),
        "verdict={:?}",
        rep_noncrit.verdict
    );
    assert_eq!(fs::read(&escaped_sentinel).unwrap(), b"sentinel");
    assert!(!wdir.exists(), "no witness_dir artifacts created on rejected paths");
}

#[test]
fn r35_codex_findings_regression() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Preceding `UnwindProbe { trigger_unwind: false }` must NOT consume
    //    `fuzz_ext_unwind`'s scheduled `EnvAction::Unwind` in either
    //    `FuzzProgram::to_trace_test_case`, standalone fuzz repro, or
    //    `ShrinkableCase::from_fuzz_program`.
    let multi_unw_prog = FuzzProgram {
        seed: 0x3501,
        index: 0,
        input_x: 11,
        input_y: 22,
        steps: vec![
            FuzzStep::UnwindProbe { trigger_unwind: false },
            FuzzStep::UnwindProbe { trigger_unwind: true },
        ],
        applied_mutators: Vec::new(),
    };
    let multi_case = multi_unw_prog.to_trace_test_case();
    let multi_rep = engine.run_case(&multi_case);
    assert!(
        matches!(multi_rep.verdict, TraceVerdict::Agree | TraceVerdict::DegradedNoMiri { .. }),
        "report={multi_rep:?}"
    );
    assert!(multi_rep.expectation_violation.is_none(), "{:?}", multi_rep.expectation_violation);
    assert!(matches!(multi_rep.rustc_dual.o0.outcome, TerminalOutcome::Unwound { .. }));
    let probe_pos = multi_rep
        .rustc_dual
        .o0
        .spine
        .events
        .iter()
        .position(|ev| matches!(ev, ObservableEvent::CallReturn { callee, .. } if callee == "fuzz_ext_probe"))
        .expect("non-triggering UnwindProbe must execute fuzz_ext_probe CallReturn first");
    let unw_pos = multi_rep
        .rustc_dual
        .o0
        .spine
        .events
        .iter()
        .position(|ev| matches!(ev, ObservableEvent::CallUnwind { callee, .. } if callee == "fuzz_ext_unwind"))
        .expect("triggering UnwindProbe must consume unwind at fuzz_ext_unwind");
    assert!(probe_pos < unw_pos);
    if let Some(lean_leg) = &multi_rep.lean {
        assert!(lean_leg.tool_error.is_none(), "{:?}", lean_leg.tool_error);
        assert!(matches!(lean_leg.outcome, TerminalOutcome::Unwound { .. }));
        let lean_probe_pos = lean_leg
            .spine
            .events
            .iter()
            .position(|ev| {
                matches!(ev, ObservableEvent::CallReturn { callee, .. } if callee == "fuzz_ext_probe")
            })
            .expect("Lean non-triggering UnwindProbe must return via fuzz_ext_probe");
        let lean_unw_pos = lean_leg
            .spine
            .events
            .iter()
            .position(|ev| {
                matches!(ev, ObservableEvent::CallUnwind { callee, .. } if callee == "fuzz_ext_unwind")
            })
            .expect("Lean triggering UnwindProbe must unwind at fuzz_ext_unwind");
        assert!(lean_probe_pos < lean_unw_pos);
    }

    let sc_multi_unw = ShrinkableCase::from_fuzz_program(&multi_unw_prog, None);
    let sc_multi_rs = render_standalone_shrinkable_repro_rs(&sc_multi_unw, "r35scmulti01");
    let sc_multi_src = tmp.path().join("r35_sc_multi_unw.rs");
    let sc_multi_bin = tmp.path().join("r35_sc_multi_unw_bin");
    fs::write(&sc_multi_src, &sc_multi_rs).unwrap();
    let sc_multi_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&sc_multi_src)
        .arg("-o")
        .arg(&sc_multi_bin)
        .output()
        .unwrap();
    assert!(sc_multi_comp.status.success(), "{}", String::from_utf8_lossy(&sc_multi_comp.stderr));
    let sc_multi_run = Command::new(&sc_multi_bin).output().unwrap();
    assert!(sc_multi_run.status.success());
    let sc_multi_parsed = parse_trace_json_stdout_with_expected_args(
        "r35-sc-multi-unw",
        &String::from_utf8_lossy(&sc_multi_run.stdout),
        &String::from_utf8_lossy(&sc_multi_run.stderr),
        1,
        Some(sc_multi_unw.inputs.len()),
    )
    .expect("parse shrinkable multi-unwind trace JSON");
    assert!(matches!(sc_multi_parsed.outcome, TerminalOutcome::Unwound { .. }));
    let sc_probe_pos = sc_multi_parsed
        .spine
        .events
        .iter()
        .position(|ev| matches!(ev, ObservableEvent::CallReturn { callee, .. } if callee == "fuzz_ext_probe"))
        .expect("ShrinkableCase must complete non-triggering fuzz_ext_probe first");
    let sc_unw_pos = sc_multi_parsed
        .spine
        .events
        .iter()
        .position(|ev| matches!(ev, ObservableEvent::CallUnwind { callee, .. } if callee == "fuzz_ext_unwind"))
        .expect("ShrinkableCase must unwind at triggering fuzz_ext_unwind");
    assert!(sc_probe_pos < sc_unw_pos);

    // 2. `ShrinkableCase::from_fuzz_program` initializes accumulator local 3
    //    from `input_x + input_y` and returns it cleanly in Rust and Lean.
    let acc_prog = FuzzProgram {
        seed: 0x3502,
        index: 0,
        input_x: 10,
        input_y: 20,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 5 }],
        applied_mutators: Vec::new(),
    };
    let mut acc_prog_other_consts = acc_prog.clone();
    acc_prog_other_consts.input_x = 99;
    acc_prog_other_consts.input_y = 77;
    acc_prog_other_consts.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 123 }];
    assert_eq!(
        canonical_fuzz_program_skeleton_hash(&acc_prog, None),
        canonical_fuzz_program_skeleton_hash(&acc_prog_other_consts, None)
    );
    let sc_acc = ShrinkableCase::from_fuzz_program(&acc_prog, None);
    assert_eq!(sc_acc.return_local, 3);
    assert!(sc_acc.inputs.iter().any(|i| i.local_id == 3 && i.value == 30));
    let sc_acc_sig = ShrinkFailureSignature::from_case_report(&mk_ub_case_report(
        "r35acc_sig",
        "Undefined Behavior: expected 4 bytes, got 8",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(0),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
        TraceVerdict::UnsoundAccept { detail: "r35 sig".into() },
    ))
    .unwrap();
    let sc_acc_rs =
        render_standalone_shrinkable_repro_rs_for_signature(&sc_acc, "r35acc01", Some(&sc_acc_sig));
    let sc_acc_src = tmp.path().join("r35_sc_acc.rs");
    let sc_acc_bin = tmp.path().join("r35_sc_acc_bin");
    fs::write(&sc_acc_src, &sc_acc_rs).unwrap();
    let sc_acc_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&sc_acc_src)
        .arg("-o")
        .arg(&sc_acc_bin)
        .output()
        .unwrap();
    assert!(sc_acc_comp.status.success(), "{}", String::from_utf8_lossy(&sc_acc_comp.stderr));
    let sc_acc_run = Command::new(&sc_acc_bin).output().unwrap();
    assert!(sc_acc_run.status.success());
    let sc_acc_parsed = parse_trace_json_stdout_with_expected_args(
        "r35-sc-acc",
        &String::from_utf8_lossy(&sc_acc_run.stdout),
        &String::from_utf8_lossy(&sc_acc_run.stderr),
        1,
        Some(sc_acc.inputs.len()),
    )
    .expect("parse shrinkable acc trace JSON");
    assert!(matches!(
        sc_acc_parsed.outcome,
        TerminalOutcome::Returned { ret: TraceVal::Scalar { bits: 42380, .. }, .. }
    ));

    let mut sc_acc_lean = sc_acc.clone();
    sc_acc_lean.struct_fields.clear();
    let lean_acc_src =
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&sc_acc_lean, "r35accln")
            .expect("lower shrinkable acc case to Lean");
    assert!(lean_acc_src.contains("BitVec.ofNat 128 30"));
    if let Some(lean_sess) = &engine.lean {
        let lean_acc_path = tmp.path().join("r35_sc_acc.mir.lean");
        fs::write(&lean_acc_path, &lean_acc_src).unwrap();
        let lp = lean_sess.lean_path_with(None).unwrap();
        let lean_out = Command::new(&lean_sess.lean_bin)
            .env("LEAN_PATH", lp)
            .arg(&lean_acc_path)
            .output()
            .unwrap();
        assert!(
            lean_out.status.success(),
            "Lean shrinkable acc repro failed:\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&lean_out.stdout),
            String::from_utf8_lossy(&lean_out.stderr)
        );
    }

    // 3. Fallback Miri UB normalization preserves semantic counts/alignments
    //    while collapsing volatile allocation IDs, hex addresses, borrow tags,
    //    and offsets.
    let m_sz_a = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: expected 4 bytes, got 8".into() },
    );
    let m_sz_b = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: expected 8 bytes, got 16".into() },
    );
    let m_al_a = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: required alignment 4".into() },
    );
    let m_al_b = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: required alignment 8".into() },
    );
    assert_ne!(normalize_miri_ub_cause(Some(&m_sz_a)), normalize_miri_ub_cause(Some(&m_sz_b)));
    assert_ne!(normalize_miri_ub_cause(Some(&m_al_a)), normalize_miri_ub_cause(Some(&m_al_b)));

    let m_vol_a = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: fault at alloc12+32 (0x7f01) tag 99 <17> offset: 24"
                .into(),
        },
    );
    let m_vol_b = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail:
                "Undefined Behavior: fault at alloc900+64 (0xdeadbeef) tag 401 <882> offset: 128"
                    .into(),
        },
    );
    assert_eq!(normalize_miri_ub_cause(Some(&m_vol_a)), normalize_miri_ub_cause(Some(&m_vol_b)));

    // 4. Reject embedded `minimized_report` whose `case_id` disagrees with the
    //    witness or run `case_id`.
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep_c1 = mk_ub_case_report(
        "r35_c1",
        "Undefined Behavior: expected 4 bytes, got 8",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let rep_other = mk_ub_case_report(
        "r35_other",
        "Undefined Behavior: expected 8 bytes, got 16",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let ok_sr = shrink_fuzz_program_with_budget(&acc_prog, ShrinkBudget::default(), |p| {
        !p.steps.is_empty()
    });
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);
    let mismatched_wit = WitnessArtifact::from_shrink(
        "r35_c1",
        rep_c1.verdict.clone(),
        rep_c1.verdict.clone(),
        ok_sr.clone(),
    )
    .with_minimized_report(rep_other)
    .with_report_index(0);
    for wit_cand in [mismatched_wit.clone(), {
        let mut w = mismatched_wit;
        w.report_index = None;
        w
    }] {
        let mut reg_mm = BugRegistry::new("google/zerocopy");
        record_report_telemetry_witnesses(
            &mut reg_mm,
            std::slice::from_ref(&rep_c1),
            &[wit_cand],
            "main",
            true,
            "mir_v1_itree",
            &"2".repeat(40),
        );
        assert!(
            reg_mm.buckets.is_empty(),
            "mismatched minimized_report must not enter BugRegistry"
        );
        assert_eq!(reg_mm.provisional_cases.len(), 1);
        assert_eq!(reg_mm.provisional_cases[0].case_id, "r35_c1");
    }

    // 5. Reject duplicate `bug_id` rows in `SemanticDetailRecord` and
    //    `KnownBugsExport`.
    let valid_wit = WitnessArtifact::from_shrink(
        "r35_c1",
        rep_c1.verdict.clone(),
        rep_c1.verdict.clone(),
        ok_sr,
    )
    .with_minimized_report(rep_c1.clone())
    .with_report_index(0);
    let mut reg_dup = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut reg_dup,
        std::slice::from_ref(&rep_c1),
        &[valid_wit],
        "main",
        true,
        "mir_v1_itree",
        &"2".repeat(40),
    );
    let diff_report = DifferentialReport::from_cases(
        "miri=available",
        true,
        true,
        "mir_eval=unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep_c1],
        Vec::new(),
    );
    let mut ctx = TelemetryContext::discover(std::path::Path::new("/nonexistent_anneal_root"));
    ctx.commit_sha = "2".repeat(40);
    ctx.head_provenance_verified = true;
    ctx.build_freshness_override = Some(BuildFreshness::VerifiedAtHead);
    ctx.build_exit_code_override = Some(0);

    let mut dup_detail =
        SemanticDetailRecord::from_report_and_registry(&diff_report, &reg_dup, &ctx).unwrap();
    dup_detail.known_bugs.push(dup_detail.known_bugs[0].clone());
    assert!(dup_detail.validate_honesty().unwrap_err().contains("duplicate bug_id"));
    let dup_detail_path = tmp.path().join("dup_detail.jsonl");
    assert!(dup_detail.write_jsonl(&dup_detail_path).is_err());
    assert!(!dup_detail_path.exists());

    let mut dup_kb =
        KnownBugsExport::from_report_and_registry(&diff_report, &reg_dup, &ctx).unwrap();
    dup_kb.known_bugs.push(dup_kb.known_bugs[0].clone());
    assert!(dup_kb.validate().unwrap_err().contains("duplicate bug_id"));
    let dup_kb_path = tmp.path().join("dup_kb.json");
    assert!(dup_kb.write_to_path(&dup_kb_path).is_err());
    assert!(!dup_kb_path.exists());
}

#[test]
fn metamorphic_post_return_slots_reportless_relations_and_fuzz_shrink_parity() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Standalone metamorphic harness records matching entry + 0x10-tagged
    //    post-return `boundary_slots` on BOTH called and inlined JSON lines.
    let meta_prog = FuzzProgram {
        seed: 0x3601,
        index: 0,
        input_x: 12,
        input_y: 7,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 3 },
            FuzzStep::HelperCall { callee_idx: 1, bias: 5 },
            FuzzStep::BranchMix { then_imm: 4, else_imm: 9 },
            FuzzStep::BoundedLoop { iters: 2, step_imm: 3 },
        ],
        applied_mutators: Vec::new(),
    };
    let meta_case = meta_prog.to_trace_test_case();
    let meta_rs = format!(
        "#![allow(dead_code, unused_variables, unused_mut)]\n{}",
        render_standalone_metamorphic_rust_harness(&meta_case)
    );
    let meta_src_path = tmp.path().join("meta_post_ret_slots.rs");
    let meta_bin_path = tmp.path().join("meta_post_ret_slots_bin");
    fs::write(&meta_src_path, &meta_rs).unwrap();
    let meta_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2024", "-C", "overflow-checks=no"])
        .arg(&meta_src_path)
        .arg("-o")
        .arg(&meta_bin_path)
        .output()
        .unwrap();
    assert!(meta_comp.status.success(), "{}", String::from_utf8_lossy(&meta_comp.stderr));
    let meta_run = Command::new(&meta_bin_path).output().unwrap();
    assert!(meta_run.status.success(), "{}", String::from_utf8_lossy(&meta_run.stderr));
    let meta_stdout = String::from_utf8_lossy(&meta_run.stdout);
    let called_line = meta_stdout
        .lines()
        .find_map(|l| l.trim().strip_prefix("ANNEAL_ITREE_TRACE_JSON:"))
        .expect("missing ANNEAL_ITREE_TRACE_JSON");
    let inlined_line = meta_stdout
        .lines()
        .find_map(|l| l.trim().strip_prefix("ANNEAL_ITREE_INLINED_TWIN_JSON:"))
        .expect("missing ANNEAL_ITREE_INLINED_TWIN_JSON");
    let called_json: serde_json::Value = serde_json::from_str(called_line).unwrap();
    let inlined_json: serde_json::Value = serde_json::from_str(inlined_line).unwrap();
    assert_eq!(called_json["outcome_kind"], "returned");
    assert_eq!(inlined_json["outcome_kind"], "returned");
    assert_eq!(called_json["ret"], inlined_json["ret"]);
    let called_slots = called_json["boundary_slots"].as_array().unwrap();
    let inlined_slots = inlined_json["boundary_slots"].as_array().unwrap();
    assert_eq!(called_slots.len(), 3);
    assert_eq!(called_slots, inlined_slots);
    assert_eq!(called_slots[2].as_array().unwrap()[0], 0x10);

    // 2. Reportless `WitnessBundle::try_from_witness` accepts genuine
    //    `ShrinkFailureSignature::from_case_report` metamorphic signatures
    //    for both authority-qualified CallerFrameLaw and Miri-vs-Lean UB
    //    mismatches, while rejecting contradicting or bogus relation sets.
    let parity_prog = FuzzProgram {
        seed: 0x3602,
        index: 0,
        input_x: 12,
        input_y: 7,
        steps: vec![
            FuzzStep::BranchMix { then_imm: 11, else_imm: 17 },
            FuzzStep::HelperCall { callee_idx: 0, bias: 4 },
            FuzzStep::HelperCall { callee_idx: 1, bias: 6 },
            FuzzStep::HelperCall { callee_idx: 2, bias: 100 },
            FuzzStep::HelperCall { callee_idx: 2, bias: 3 },
            FuzzStep::BoundedLoop { iters: 3, step_imm: 5 },
            FuzzStep::BranchMix { then_imm: 10, else_imm: 99 },
        ],
        applied_mutators: Vec::new(),
    };
    let ok_sr = shrink_fuzz_program_with_budget(&parity_prog, ShrinkBudget::default(), |p| {
        p.steps.len() == parity_prog.steps.len()
    });
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal);

    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(10),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let dual_ok = RustcDualResult {
        o0: mk_auth("rustc-O0", ret_ok.clone()),
        o2: mk_auth("rustc-O2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let mut bad_frame_miri = mk_auth("miri", ret_ok.clone());
    bad_frame_miri.caller_frame_law = CallerFrameLaw {
        caller_locals_preserved: false,
        untouched_alloc_bytes_preserved: true,
        padding_mask_respected: true,
        violations: vec!["inlined frame clobbered".into()],
    };
    let frame_rec = evaluate_metamorphic_duality(
        &dual_ok,
        Some(&mk_auth("miri", ret_ok.clone())),
        &mk_auth("lean", ret_ok.clone()),
        &dual_ok,
        Some(&bad_frame_miri),
        mk_auth("lean", ret_ok.clone()),
    );
    let mut frame_rep = mk_ub_case_report(
        "g2_r22_frame",
        "",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: frame_rec.detail.clone() },
    );
    frame_rep.rustc_dual = dual_ok.clone();
    frame_rep.miri = Some(mk_auth("miri", ret_ok.clone()));
    frame_rep.lean = Some(mk_auth("lean", ret_ok.clone()));
    frame_rep.metamorphic = Some(frame_rec);
    let frame_sig = ShrinkFailureSignature::from_case_report(&frame_rep).unwrap();
    assert_eq!(frame_sig.metamorphic_relations, vec!["metamorphic_caller_frame_law:inlined_miri"]);
    let frame_art_with_report = WitnessArtifact::from_shrink(
        &frame_rep.case_id,
        frame_rep.verdict.clone(),
        frame_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(frame_sig.clone())
    .with_minimized_report(frame_rep.clone());
    let frame_bundle = WitnessBundle::try_from_witness(frame_art_with_report, None)
        .expect("authoritative CallerFrameLaw report+signature must validate");
    assert!(
        frame_bundle.repro_rust_source.contains("\"metamorphic_caller_frame_law:inlined_miri\"")
    );

    // Reportless signature carrying verdict-derived relation pin (`none`
    // outcome tags) validates cleanly, whereas enriched leg outcomes/classes
    // without an authoritative `minimized_report` are rejected.
    let mut reportless_frame_sig =
        ShrinkFailureSignature::from_verdict_and_legs(&frame_rep.verdict, None, None).unwrap();
    reportless_frame_sig.metamorphic_relations =
        vec!["metamorphic_caller_frame_law:inlined_miri".into()];
    let reportless_frame_art = WitnessArtifact::from_shrink(
        "g2_r22_frame_reportless_ok",
        frame_rep.verdict.clone(),
        frame_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(reportless_frame_sig.clone());
    let reportless_frame_bundle = WitnessBundle::try_from_witness(reportless_frame_art, None)
        .expect("reportless verdict-derived CallerFrameLaw signature must validate");
    assert!(
        reportless_frame_bundle
            .repro_rust_source
            .contains("\"metamorphic_caller_frame_law:inlined_miri\"")
    );
    let reportless_enriched_frame_art = WitnessArtifact::from_shrink(
        "g2_r22_frame_enriched_no_report",
        frame_rep.verdict.clone(),
        frame_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(frame_sig.clone());
    assert!(
        WitnessBundle::try_from_witness(reportless_enriched_frame_art, None).is_err(),
        "reportless artifact claiming enriched outcome kinds/legs must be rejected"
    );

    let bad_miri_ub = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: out-of-bounds pointer arithmetic".into(),
        },
    );
    let bad_lean_ub = mk_auth(
        "lean-compositional-itree",
        TerminalOutcome::FaultUb { detail: "unchecked arithmetic overflow".into() },
    );
    let dual_skipped = RustcDualResult {
        o0: mk_auth("rustc-O0", ret_ok.clone()),
        o2: mk_auth("rustc-O2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: true,
        mismatch_detail: None,
    };
    let inlined_lean_match_ub = mk_auth(
        "lean-strict-verbatim",
        TerminalOutcome::CaptureRefused { reason: "external callee in twin".into() },
    );
    let pure_ub_rec = evaluate_metamorphic_duality(
        &dual_skipped,
        Some(&bad_miri_ub),
        &bad_lean_ub,
        &dual_skipped,
        Some(&bad_miri_ub),
        inlined_lean_match_ub,
    );
    assert!(pure_ub_rec.detail.contains("UB fault cause mismatch:"));
    assert_eq!(pure_ub_rec.failed_relations, vec!["called_miri_vs_lean_ub"]);
    let mut pure_ub_rep = mk_ub_case_report(
        "g2_r22_pure_ub",
        "",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: pure_ub_rec.detail.clone() },
    );
    pure_ub_rep.rustc_dual = dual_skipped;
    pure_ub_rep.miri = Some(bad_miri_ub.clone());
    pure_ub_rep.lean = Some(bad_lean_ub.clone());
    pure_ub_rep.metamorphic = Some(pure_ub_rec);
    let pure_ub_sig = ShrinkFailureSignature::from_case_report(&pure_ub_rep).unwrap();
    let pure_ub_art = WitnessArtifact::from_shrink(
        &pure_ub_rep.case_id,
        pure_ub_rep.verdict.clone(),
        pure_ub_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(pure_ub_sig.clone())
    .with_minimized_report(pure_ub_rep.clone());
    let pure_ub_bundle = WitnessBundle::try_from_witness(pure_ub_art, None)
        .expect("authoritative compare_ub_fault_results report+signature must validate");
    assert!(pure_ub_bundle.repro_rust_source.contains("\"called_miri_vs_lean_ub\""));
    let reportless_pure_ub_art = WitnessArtifact::from_shrink(
        "g2_r22_pure_ub_no_report",
        pure_ub_rep.verdict.clone(),
        pure_ub_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(pure_ub_sig.clone());
    assert!(WitnessBundle::try_from_witness(reportless_pure_ub_art, None).is_err());

    let combined_ub_rec = evaluate_metamorphic_duality(
        &dual_ok,
        Some(&bad_miri_ub),
        &bad_lean_ub,
        &dual_ok,
        Some(&mk_auth("miri", ret_ok.clone())),
        mk_auth("lean", ret_ok.clone()),
    );
    assert!(combined_ub_rec.detail.contains("UB fault cause mismatch:"));
    assert_eq!(
        combined_ub_rec.failed_relations,
        vec![
            "lean_called_vs_inlined",
            "called_rustc_vs_lean",
            "called_miri_vs_lean_ub",
            "miri_called_vs_inlined",
        ]
    );
    let mut combined_ub_rep = mk_ub_case_report(
        "g2_r22_ub",
        "",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: combined_ub_rec.detail.clone() },
    );
    combined_ub_rep.rustc_dual = dual_ok;
    combined_ub_rep.miri = Some(bad_miri_ub);
    combined_ub_rep.lean = Some(bad_lean_ub);
    combined_ub_rep.metamorphic = Some(combined_ub_rec);
    let ub_sig = ShrinkFailureSignature::from_case_report(&combined_ub_rep).unwrap();
    let ub_art = WitnessArtifact::from_shrink(
        &combined_ub_rep.case_id,
        combined_ub_rep.verdict.clone(),
        combined_ub_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(ub_sig)
    .with_minimized_report(combined_ub_rep.clone());
    let ub_bundle = WitnessBundle::try_from_witness(ub_art, None)
        .expect("authoritative combined compare_ub_fault_results report+signature must validate");
    assert!(ub_bundle.repro_rust_source.contains("\"called_miri_vs_lean_ub\""));

    let mut wrong_rel_sig = reportless_frame_sig.clone();
    wrong_rel_sig.metamorphic_relations = vec!["inlined_rustc_o0_vs_o2".into()];
    let wrong_rel_art = WitnessArtifact::from_shrink(
        "g2_r22_wrong_rel",
        frame_rep.verdict.clone(),
        frame_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(wrong_rel_sig);
    assert!(WitnessBundle::try_from_witness(wrong_rel_art, None).is_err());

    let mut bogus_cf_sig = reportless_frame_sig.clone();
    bogus_cf_sig.metamorphic_relations = vec!["metamorphic_caller_frame_law:bogus".into()];
    let bogus_cf_art = WitnessArtifact::from_shrink(
        "g2_r22_bogus_cf",
        frame_rep.verdict.clone(),
        frame_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(bogus_cf_sig);
    assert!(WitnessBundle::try_from_witness(bogus_cf_art, None).is_err());

    let mut mismatched_ub_sig =
        ShrinkFailureSignature::from_verdict_and_legs(&pure_ub_rep.verdict, None, None).unwrap();
    mismatched_ub_sig.metamorphic_relations = vec!["called_rustc_o0_vs_o2".into()];
    let mismatched_ub_art = WitnessArtifact::from_shrink(
        "g2_r22_mm_ub",
        pure_ub_rep.verdict.clone(),
        pure_ub_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_signature(mismatched_ub_sig);
    assert!(WitnessBundle::try_from_witness(mismatched_ub_art, None).is_err());

    // Forged reportless outcome tags (`returned` vs `unwound`), UB classes, or
    // leg/fault-site kinds MUST fail when `minimized_report` is absent.
    let generic_verdict =
        TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".into() };
    let generic_sig =
        ShrinkFailureSignature::from_verdict_and_legs(&generic_verdict, None, None).unwrap();
    let mut forged_outcomes = generic_sig.clone();
    forged_outcomes.ref_outcome_kind = "returned";
    forged_outcomes.lean_outcome_kind = "unwound";
    assert!(
        WitnessBundle::try_from_witness(
            WitnessArtifact::from_shrink(
                "r46_forged_outcomes",
                generic_verdict.clone(),
                generic_verdict.clone(),
                ok_sr.clone(),
            )
            .with_signature(forged_outcomes),
            None,
        )
        .is_err()
    );
    let mut forged_site = generic_sig;
    forged_site.lean_fault_site_kind = "unreachable".into();
    assert!(
        WitnessBundle::try_from_witness(
            WitnessArtifact::from_shrink(
                "r46_forged_site",
                generic_verdict.clone(),
                generic_verdict,
                ok_sr.clone(),
            )
            .with_signature(forged_site),
            None,
        )
        .is_err()
    );
    let mut forged_legs = reportless_frame_sig;
    forged_legs.metamorphic_leg_kinds = "miri=returned;lean=unwound".into();
    assert!(
        WitnessBundle::try_from_witness(
            WitnessArtifact::from_shrink(
                "r46_forged_legs",
                frame_rep.verdict.clone(),
                frame_rep.verdict,
                ok_sr.clone(),
            )
            .with_signature(forged_legs),
            None,
        )
        .is_err()
    );
    let _ = (frame_sig, pure_ub_sig);

    // 3. `ShrinkableCase::from_fuzz_program` matches `FuzzProgram` semantics
    //    across `HelperCall` (0/1/2 + `y.wrapping_add(bias)`), `BranchMix`
    //    (runtime `(acc & 1) == 0` for both odd and even `acc`), and
    //    `BoundedLoop` (`k * step_imm + 1`) in BOTH Rust and Lean, while
    //    preserving constant-erased skeleton invariance.
    let mut parity_prog_other_consts = parity_prog.clone();
    parity_prog_other_consts.input_x = 999;
    parity_prog_other_consts.input_y = 888;
    parity_prog_other_consts.steps = vec![
        FuzzStep::BranchMix { then_imm: 1, else_imm: 2 },
        FuzzStep::HelperCall { callee_idx: 3, bias: 11 },
        FuzzStep::HelperCall { callee_idx: 4, bias: 22 },
        FuzzStep::HelperCall { callee_idx: 5, bias: 33 },
        FuzzStep::HelperCall { callee_idx: 2, bias: 44 },
        FuzzStep::BoundedLoop { iters: 7, step_imm: 9 },
        FuzzStep::BranchMix { then_imm: 55, else_imm: 66 },
    ];
    assert_eq!(
        canonical_fuzz_program_skeleton_hash(&parity_prog, None),
        canonical_fuzz_program_skeleton_hash(&parity_prog_other_consts, None)
    );

    let sc_parity = ShrinkableCase::from_fuzz_program(&parity_prog, None);
    let sc_parity_sig = ShrinkFailureSignature::from_case_report(&mk_ub_case_report(
        "r36_parity_sig",
        "Undefined Behavior: expected 4 bytes, got 8",
        ret_ok,
        TraceVerdict::UnsoundAccept { detail: "r36 sig".into() },
    ))
    .unwrap();
    let sc_parity_rs = render_standalone_shrinkable_repro_rs_for_signature(
        &sc_parity,
        "r36parity01",
        Some(&sc_parity_sig),
    );
    let sc_parity_src = tmp.path().join("r36_parity.rs");
    let sc_parity_bin = tmp.path().join("r36_parity_bin");
    fs::write(&sc_parity_src, &sc_parity_rs).unwrap();
    let sc_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&sc_parity_src)
        .arg("-o")
        .arg(&sc_parity_bin)
        .output()
        .unwrap();
    assert!(sc_comp.status.success(), "{}", String::from_utf8_lossy(&sc_comp.stderr));
    let sc_run = Command::new(&sc_parity_bin).output().unwrap();
    assert!(sc_run.status.success());
    let sc_parsed = parse_trace_json_stdout_with_expected_args(
        "r36-sc-parity",
        &String::from_utf8_lossy(&sc_run.stdout),
        &String::from_utf8_lossy(&sc_run.stderr),
        1,
        Some(sc_parity.inputs.len()),
    )
    .expect("parse shrinkable parity trace JSON");
    assert!(
        matches!(
            sc_parsed.outcome,
            TerminalOutcome::Returned { ret: TraceVal::Scalar { bits: 42487, .. }, .. }
        ),
        "expected exact accumulated+sentinel return 42487, got {:?}",
        sc_parsed.outcome
    );

    let mut sc_parity_lean = sc_parity.clone();
    sc_parity_lean.struct_fields.clear();
    let lean_raw = anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(
        &sc_parity_lean,
        "r36parityln",
    )
    .expect("lower shrinkable parity case to Lean");
    let lean_parity_src = format!(
        "import Anneal.MirTotal.ExecTotal\n{lean_raw}\n\
         open Anneal.MirTotal in\n\
         def evalParity (prog : Program) (args : List Val) (fuel : Nat) : String :=\n\
           match initStateBy (mirTyBeqAt 64) prog {{ args := args }} with\n\
           | .error _ => \"init_err\"\n\
           | .ok s0 =>\n\
             let rec go : Nat → State → String\n\
               | 0, _ => \"diverged\"\n\
               | n + 1, st => match evalMirStepBy (mirTyBeqAt 64) prog 0 st with\n\
                 | .done (.returned out) => (match out.ret with\n\
                   | .scalar sv => toString sv.bits.toNat\n\
                   | _ => \"non_scalar\")\n\
                 | .done _ => \"other_done\"\n\
                 | .fault _ => \"fault\"\n\
                 | .step st' => go n st'\n\
             go fuel s0\n\
         #eval IO.println (\"PARITY_RET=\" ++ evalParity reproProgram reproArgs reproFuel)\n"
    );
    if let Some(lean_sess) = &engine.lean {
        let lean_parity_path = tmp.path().join("r36_sc_parity.mir.lean");
        fs::write(&lean_parity_path, &lean_parity_src).unwrap();
        let lp = lean_sess.lean_path_with(None).unwrap();
        let lean_out = Command::new(&lean_sess.lean_bin)
            .env("LEAN_PATH", lp)
            .arg(&lean_parity_path)
            .output()
            .unwrap();
        let lean_stdout = String::from_utf8_lossy(&lean_out.stdout);
        let lean_stderr = String::from_utf8_lossy(&lean_out.stderr);
        assert!(
            lean_out.status.success(),
            "Lean failed:\nstdout={lean_stdout}\nstderr={lean_stderr}"
        );
        assert!(
            lean_stdout.lines().any(|l| l.trim() == "PARITY_RET=42487"),
            "Lean shrinkable parity must return PARITY_RET=42487:\nstdout={lean_stdout}\nstderr={lean_stderr}"
        );
    }

    // Also confirm `Pass 3` / `Pass 5` preserve causal dynamic branch,
    // `BoundedLoopInduction`, and helper `rhs_local` when required, while
    // `Pass 5` collapses `BoundedLoopInduction { step_mul }` when noncausal.
    let shrunk_causal = shrink_case_two_tier_with_budget(
        &sc_parity,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        |c| {
            c.steps
                .iter()
                .any(|s| matches!(s, ShrinkStep::BranchMix { dynamic_even_cond: true, .. }))
                && c.steps.iter().any(|s| {
                    matches!(
                        s,
                        ShrinkStep::BoundedLoop {
                            induction: Some(BoundedLoopInduction { step_mul, .. }),
                            ..
                        } if *step_mul >= 2
                    )
                })
                && c.steps
                    .iter()
                    .any(|s| matches!(s, ShrinkStep::HelperCall { rhs_local: Some(_), .. }))
        },
    );
    assert!(shrunk_causal.succeeded && shrunk_causal.is_one_minimal);
}

#[test]
fn r37_codex_findings_regression() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_miri = false;
    cfg.check_metamorphic_duality = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. Both `WitnessBundle::try_from_witness` / `write_to_dir` and
    //    `BugRegistry::record_witness` / `from_1_minimal_witness` MUST reject a
    //    `minimized_report` whose `case_id` disagrees with `artifact.case_id`
    //    (even via direct struct assembly or JSON tampering).
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep_a = mk_ub_case_report(
        "r37_case_a",
        "Undefined Behavior: expected 4 bytes, got 8",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let rep_b = mk_ub_case_report(
        "r37_case_b",
        "Undefined Behavior: Data race detected between read and write",
        ret_ok,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let prog = FuzzProgram {
        seed: 0x3701,
        index: 0,
        input_x: 0x1234,
        input_y: 0x55,
        steps: Vec::new(),
        applied_mutators: Vec::new(),
    };
    let mut ok_sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |_| true);
    ok_sr.succeeded = true;
    ok_sr.is_one_minimal = true;
    ok_sr.converged_1_minimal = true;

    let base_art = WitnessArtifact::from_shrink(
        &rep_a.case_id,
        rep_a.verdict.clone(),
        rep_a.verdict.clone(),
        ok_sr.clone(),
    );
    let base_repro_id = base_art.repro_case_id.clone();
    let attached_mm = base_art.clone().with_minimized_report(rep_b.clone());
    assert_eq!(attached_mm.repro_case_id, base_repro_id);
    assert!(
        WitnessBundle::try_from_witness(attached_mm.clone(), None)
            .unwrap_err()
            .contains("does not match witness artifact case_id")
    );
    let json_roundtrip: WitnessArtifact =
        serde_json::from_str(&serde_json::to_string(&attached_mm).unwrap()).unwrap();
    assert!(WitnessBundle::try_from_witness(json_roundtrip, None).is_err());

    let valid_a = base_art.with_minimized_report(rep_a.clone());
    let mut tampered_bundle = WitnessBundle::try_from_witness(valid_a, None).unwrap();
    tampered_bundle.artifact.minimized_report = Some(Box::new(rep_b.clone()));
    let mm_dir = tmp.path().join("r37_mm_bundles");
    assert!(tampered_bundle.write_to_dir(&mm_dir).is_err());
    assert!(!mm_dir.exists());

    assert!(
        CanonicalBugFingerprint::from_1_minimal_witness(
            &attached_mm,
            &rep_a,
            "main",
            "mir_v1_itree",
            None,
        )
        .is_err()
    );
    let mut mm_reg = BugRegistry::new("google/zerocopy");
    assert!(matches!(
        mm_reg.record_witness(
            &attached_mm,
            &rep_a,
            "main",
            true,
            "mir_v1_itree",
            &"3".repeat(40),
            None,
        ),
        DedupRecordOutcome::Provisional { .. }
    ));
    assert!(mm_reg.buckets.is_empty());

    // 2. Empty-step and multi-step `ShrinkableCase::from_fuzz_program` preserve
    //    `FuzzProgram`'s final `acc ^ (input_x ^ 0xA5A5)` sentinel XOR in BOTH
    //    Rust and Lean while retaining constant-erased skeleton invariance and
    //    `Pass 2`/`Pass 5` shrinking.
    let fp_case = prog.to_trace_test_case();
    let fp_rep = engine.run_case(&fp_case);
    let expected_ret = (prog.input_x.wrapping_add(prog.input_y)) ^ (prog.input_x ^ 0xA5A5);
    assert_eq!(expected_ret, 42264);
    assert!(
        matches!(
            fp_rep.rustc_dual.o0.outcome,
            TerminalOutcome::Returned { ret: TraceVal::Scalar { bits: 42264, .. }, .. }
        ),
        "rustc fuzz_entry outcome={:?}",
        fp_rep.rustc_dual.o0.outcome
    );

    let sc_empty = ShrinkableCase::from_fuzz_program(&prog, None);
    let sc_sig = ShrinkFailureSignature::from_case_report(&rep_a).unwrap();
    let sc_rs =
        render_standalone_shrinkable_repro_rs_for_signature(&sc_empty, "r37sent01", Some(&sc_sig));
    let sc_src = tmp.path().join("r37_sentinel.rs");
    let sc_bin = tmp.path().join("r37_sentinel_bin");
    fs::write(&sc_src, &sc_rs).unwrap();
    let sc_comp = Command::new(&engine.rustc.rustc_bin)
        .args(["--edition", "2021"])
        .arg(&sc_src)
        .arg("-o")
        .arg(&sc_bin)
        .output()
        .unwrap();
    assert!(sc_comp.status.success(), "{}", String::from_utf8_lossy(&sc_comp.stderr));
    let sc_run = Command::new(&sc_bin).output().unwrap();
    assert!(sc_run.status.success());
    let sc_parsed = parse_trace_json_stdout_with_expected_args(
        "r37-sentinel",
        &String::from_utf8_lossy(&sc_run.stdout),
        &String::from_utf8_lossy(&sc_run.stderr),
        1,
        Some(sc_empty.inputs.len()),
    )
    .expect("parse r37 sentinel JSON");
    assert!(
        matches!(
            sc_parsed.outcome,
            TerminalOutcome::Returned { ret: TraceVal::Scalar { bits: 42264, .. }, .. }
        ),
        "expected exact sentinel return 42264, got {:?}",
        sc_parsed.outcome
    );

    let mut sc_lean = sc_empty.clone();
    sc_lean.struct_fields.clear();
    let lean_raw =
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&sc_lean, "r37sentln")
            .expect("lower sentinel ShrinkableCase to Lean");
    if let Some(lean_sess) = &engine.lean {
        let lean_src = format!(
            "import Anneal.MirTotal.ExecTotal\n{lean_raw}\n\
             open Anneal.MirTotal in\n\
             def evalSent (prog : Program) (args : List Val) (fuel : Nat) : String :=\n\
               match initStateBy (mirTyBeqAt 64) prog {{ args := args }} with\n\
               | .error _ => \"init_err\"\n\
               | .ok s0 =>\n\
                 let rec go : Nat → State → String\n\
                   | 0, _ => \"diverged\"\n\
                   | n + 1, st => match evalMirStepBy (mirTyBeqAt 64) prog 0 st with\n\
                     | .done (.returned out) => (match out.ret with\n\
                       | .scalar sv => toString sv.bits.toNat\n\
                       | _ => \"non_scalar\")\n\
                     | .done _ => \"other_done\"\n\
                     | .fault _ => \"fault\"\n\
                     | .step st' => go n st'\n\
                 go fuel s0\n\
             #eval IO.println (\"SENT_RET=\" ++ evalSent reproProgram reproArgs reproFuel)\n"
        );
        let lean_path = tmp.path().join("r37_sent.mir.lean");
        fs::write(&lean_path, &lean_src).unwrap();
        let lp = lean_sess.lean_path_with(None).unwrap();
        let lean_out = Command::new(&lean_sess.lean_bin)
            .env("LEAN_PATH", lp)
            .arg(&lean_path)
            .output()
            .unwrap();
        let lean_stdout = String::from_utf8_lossy(&lean_out.stdout);
        assert!(lean_out.status.success(), "{}", String::from_utf8_lossy(&lean_out.stderr));
        assert!(lean_stdout.lines().any(|l| l.trim() == "SENT_RET=42264"), "stdout={lean_stdout}");
    }

    let kept = anneal_itree_diff::shrink::shrink_case_with_budget(
        &sc_empty,
        ShrinkBudget::default(),
        |c| {
            c.steps
                .iter()
                .any(|s| matches!(s, ShrinkStep::XorLocalImm { xor_imm, .. } if *xor_imm != 0))
        },
    );
    assert!(kept.is_one_minimal);
    assert!(matches!(
        kept.minimized.steps.as_slice(),
        [ShrinkStep::XorLocalImm { xor_imm: 1, .. }]
    ));
}

#[test]
fn r40_codex_findings_regression() {
    let tmp = tempfile::tempdir().unwrap();
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let miri_ub = TerminalOutcome::FaultUb {
        detail: "Undefined Behavior: out-of-bounds pointer arithmetic".to_string(),
    };
    let lean_uw = TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) };

    // 1. Cross-branch-scope deduplication: the same canonical bug seen first on
    //    `unstable_only` and then on `main` shares ONE `BugId` and merges
    //    `branch_scope` to `"both"` (`exposed_on_main = true`).
    let mut rep = mk_ub_case_report(
        "scope_case",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    rep.case_id = "r40_scope".into();
    let mut prog = generate_fuzz_batch(0x4040_0001, 1).pop().unwrap();
    prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let mut sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| p.steps.len() == 1);
    sr.succeeded = true;
    sr.is_one_minimal = true;
    sr.converged_1_minimal = true;
    let w_scope = WitnessArtifact::from_shrink(
        "r40_scope",
        rep.verdict.clone(),
        rep.verdict.clone(),
        sr.clone(),
    );

    let mut reg_scope = BugRegistry::new("google/zerocopy");
    let first_out = reg_scope.record_witness(
        &w_scope,
        &rep,
        "unstable_only",
        false,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    );
    let bid_unstable = match first_out {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug on unstable_only, got {other:?}"),
    };
    assert_eq!(reg_scope.buckets[&bid_unstable].branch_scope, "unstable_only");
    assert!(!reg_scope.buckets[&bid_unstable].exposed_on_main);

    let second_out = reg_scope.record_witness(
        &w_scope,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        "2222222222222222222222222222222222222222",
        None,
    );
    assert!(
        matches!(second_out, DedupRecordOutcome::DuplicateHit { ref bug_id, .. } if bug_id == &bid_unstable),
        "expected merge into existing BugId across branch scopes, got {second_out:?}"
    );
    assert_eq!(reg_scope.buckets.len(), 1);
    assert_eq!(reg_scope.buckets[&bid_unstable].branch_scope, "both");
    assert!(reg_scope.buckets[&bid_unstable].exposed_on_main);

    // 2. Direct `record_shrinkable_case` rejects stale or contradictory
    //    `ShrinkFailureSignature`s against supplied authority outcomes and
    //    holds them provisional instead of minting a bogus `BugBucket`.
    let sc = ShrinkableCase {
        name: "r40_sig_check".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 1, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 1,
    };
    let stale_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "unwound",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "unwound".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let dual_ok = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth("rustc-o2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let auth_miri_ub = mk_auth("miri", miri_ub);
    let auth_lean_uw = mk_auth("lean", lean_uw);
    let auth_lean_ok = mk_auth("lean", ret_ok.clone());
    let mut reg_sig = BugRegistry::new("google/zerocopy");

    // Stale `ref_outcome_kind: "returned"` when `miri` has `FaultUb`:
    let bad_miri_out = reg_sig.record_shrinkable_case(
        &sc,
        &stale_sig,
        Some(&dual_ok),
        Some(&auth_miri_ub),
        Some(&auth_lean_uw),
        "main",
        true,
        "mir_v1_itree",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        1,
        true,
    );
    assert!(matches!(bad_miri_out, DedupRecordOutcome::Provisional { .. }), "{bad_miri_out:?}");

    // Stale `lean_outcome_kind: "unwound"` when `lean` actually `Returned`:
    let auth_miri_ok = mk_auth("miri", ret_ok.clone());
    let bad_lean_out = reg_sig.record_shrinkable_case(
        &sc,
        &stale_sig,
        Some(&dual_ok),
        Some(&auth_miri_ok),
        Some(&auth_lean_ok),
        "main",
        true,
        "mir_v1_itree",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        1,
        true,
    );
    assert!(matches!(bad_lean_out, DedupRecordOutcome::Provisional { .. }), "{bad_lean_out:?}");
    assert!(reg_sig.buckets.is_empty());

    // Consistent authorities promote cleanly:
    let good_out = reg_sig.record_shrinkable_case(
        &sc,
        &stale_sig,
        Some(&dual_ok),
        Some(&auth_miri_ok),
        Some(&auth_lean_uw),
        "main",
        true,
        "mir_v1_itree",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        1,
        true,
    );
    assert!(matches!(good_out, DedupRecordOutcome::NewBug { .. }), "{good_out:?}");

    // 3. `SemanticDetailRecord::from_report_and_registry` and
    //    `KnownBugsExport::from_report_and_registry` fail closed if either the
    //    registry or any contained bucket belongs to a different `repo`.
    let head_sha = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    let mut ctx = TelemetryContext::discover(tmp.path());
    ctx.repo = "google/zerocopy".to_string();
    ctx.branch = "main".to_string();
    ctx.branch_scope = "main".to_string();
    ctx.exposed_on_main = true;
    ctx.commit_sha = head_sha.to_string();
    let empty_report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![],
        vec![],
    );
    let foreign_empty_reg = BugRegistry::new("other/repo");
    let err_foreign_det =
        SemanticDetailRecord::from_report_and_registry(&empty_report, &foreign_empty_reg, &ctx)
            .unwrap_err();
    assert!(err_foreign_det.contains("does not match telemetry repo"), "{err_foreign_det}");
    let err_foreign_kb =
        KnownBugsExport::from_report_and_registry(&empty_report, &foreign_empty_reg, &ctx)
            .unwrap_err();
    assert!(err_foreign_kb.contains("does not match telemetry repo"), "{err_foreign_kb}");

    let mut mixed_repo_reg = reg_sig.clone();
    mixed_repo_reg.buckets.values_mut().next().unwrap().repo = "other/repo".to_string();
    let err_bucket_det =
        SemanticDetailRecord::from_report_and_registry(&empty_report, &mixed_repo_reg, &ctx)
            .unwrap_err();
    assert!(err_bucket_det.contains("outside telemetry repo"), "{err_bucket_det}");
    let err_bucket_kb =
        KnownBugsExport::from_report_and_registry(&empty_report, &mixed_repo_reg, &ctx)
            .unwrap_err();
    assert!(err_bucket_kb.contains("outside telemetry repo"), "{err_bucket_kb}");
    assert!(SemanticDetailRecord::from_report_and_registry(&empty_report, &reg_sig, &ctx).is_ok());
    assert!(KnownBugsExport::from_report_and_registry(&empty_report, &reg_sig, &ctx).is_ok());

    // 4. Same-batch SCB split with two distinct failing skeletons sharing the
    //    same 6-char skeleton prefix produces two distinct split child buckets
    //    instead of coalescing them.
    let mut pass_prog = prog.clone();
    pass_prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
        FuzzStep::ArithImm { op: FuzzArithOp::Sub, imm: 1 },
    ];
    let mk_same_bucket_witness = |id: &str, fp_prog: &FuzzProgram| {
        let mut sres = shrink_fuzz_program_with_budget(fp_prog, ShrinkBudget::default(), |c| {
            c.steps == fp_prog.steps
        });
        sres.succeeded = true;
        sres.is_one_minimal = true;
        sres.converged_1_minimal = true;
        WitnessArtifact::from_shrink(id, rep.verdict.clone(), rep.verdict.clone(), sres)
    };
    let w_pass = mk_same_bucket_witness("r40_scope", &pass_prog);
    let pass_skel = w_pass.minimized_skeleton_hash.clone();
    let base_min_prog = w_pass.shrink.minimized.clone();

    let mut seen_skel6: std::collections::HashMap<String, (FuzzProgram, String)> =
        std::collections::HashMap::new();
    let mut pair_opt = None;
    for code in 1..65_535u32 {
        let mut cand = base_min_prog.clone();
        cand.steps = (0..16)
            .map(|k| FuzzStep::ArithImm {
                op: if (code >> k) & 1 == 0 { FuzzArithOp::Add } else { FuzzArithOp::Sub },
                imm: 1,
            })
            .collect();
        let skel = canonical_fuzz_program_skeleton_hash(&cand, None);
        let skel6 = skel[..6].to_string();
        if let Some((prev_p, prev_skel)) = seen_skel6.get(&skel6) {
            if prev_skel != &skel {
                pair_opt = Some((prev_p.clone(), cand));
                break;
            }
        } else {
            seen_skel6.insert(skel6, (cand, skel));
        }
    }
    let (p_col_a, p_col_b) = pair_opt.expect("6-char skeleton prefix collision pair");
    let w_col_a = mk_same_bucket_witness("r40_scope", &p_col_a);
    let w_col_b = mk_same_bucket_witness("r40_scope", &p_col_b);
    assert_eq!(w_col_a.shrink.minimized.steps.len(), p_col_a.steps.len());
    assert_eq!(&w_col_a.minimized_skeleton_hash[..6], &w_col_b.minimized_skeleton_hash[..6]);
    assert_ne!(w_col_a.minimized_skeleton_hash, w_col_b.minimized_skeleton_hash);

    let mut scb_col_reg = BugRegistry::new("google/zerocopy");
    let root_col_id = match scb_col_reg.record_witness(
        &w_pass,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug for pass skeleton: {other:?}"),
    };
    let rec_col_a = scb_col_reg.record_witness(
        &w_col_a,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        "2222222222222222222222222222222222222222",
        None,
    );
    assert!(matches!(rec_col_a, DedupRecordOutcome::NewSkeletonAttached { .. }), "{rec_col_a:?}");
    let rec_col_b = scb_col_reg.record_witness(
        &w_col_b,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        "3333333333333333333333333333333333333333",
        None,
    );
    assert!(matches!(rec_col_b, DedupRecordOutcome::NewSkeletonAttached { .. }), "{rec_col_b:?}");
    let batch_split = scb_col_reg
        .classify_post_patch_replay(&root_col_id, "4444444444444444444444444444444444444444", |w| {
            w.minimized_skeleton_hash != pass_skel
        })
        .unwrap();
    let ScbReplayVerdict::Split { split_bugs, .. } = batch_split else {
        panic!("expected Split for colliding prefix skeletons");
    };
    assert_eq!(split_bugs.len(), 2, "colliding 6-char prefix skeletons must stay separate");
    assert_ne!(split_bugs[0].bug_id, split_bugs[1].bug_id);
}

#[test]
fn r41_codex_findings_regression() {
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep_a = mk_ub_case_report(
        "r41_case_a",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );
    let rep_b = mk_ub_case_report(
        "r41_case_b",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
    );

    // 1. Reportless witness rejects mismatched fallback `CaseReport.case_id`.
    let mut prog_a = generate_fuzz_batch(0x4141_0001, 1).pop().unwrap();
    prog_a.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let mut sr_a =
        shrink_fuzz_program_with_budget(&prog_a, ShrinkBudget::default(), |p| p.steps.len() == 1);
    sr_a.succeeded = true;
    sr_a.is_one_minimal = true;
    sr_a.converged_1_minimal = true;
    let wit_reportless_a = WitnessArtifact::from_shrink(
        "r41_case_a",
        rep_a.verdict.clone(),
        rep_a.verdict.clone(),
        sr_a.clone(),
    );
    assert!(wit_reportless_a.minimized_report.is_none());
    let mismatch_err = CanonicalBugFingerprint::from_1_minimal_witness(
        &wit_reportless_a,
        &rep_b,
        "main",
        "mir_v1_itree",
        None,
    )
    .unwrap_err();
    assert!(
        mismatch_err.contains(
            "fallback report case_id `r41_case_b` does not match witness case_id `r41_case_a`"
        ),
        "{mismatch_err}"
    );
    let mut reg_mismatch = BugRegistry::new("google/zerocopy");
    let prov = reg_mismatch.record_witness(
        &wit_reportless_a,
        &rep_b,
        "main",
        true,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    );
    assert!(matches!(prov, DedupRecordOutcome::Provisional { .. }), "{prov:?}");
    assert!(reg_mismatch.buckets.is_empty());

    // 2. Identical skeleton seen on `unstable_only` then `main` preserves
    //    `branch_scope == "both"` on mixed SCB split child.
    let mut prog_pass = prog_a.clone();
    prog_pass.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
    ];
    let mut sr_pass = shrink_fuzz_program_with_budget(&prog_pass, ShrinkBudget::default(), |p| {
        p.steps.len() == 2
    });
    sr_pass.succeeded = true;
    sr_pass.is_one_minimal = true;
    sr_pass.converged_1_minimal = true;
    let wit_pass = WitnessArtifact::from_shrink(
        "r41_pass_b",
        rep_b.verdict.clone(),
        rep_b.verdict.clone(),
        sr_pass,
    );
    let pass_skel = wit_pass.minimized_skeleton_hash.clone();

    let mut reg_split_scope = BugRegistry::new("google/zerocopy");
    let root_bid = match reg_split_scope.record_witness(
        &wit_reportless_a,
        &rep_a,
        "unstable_only",
        false,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug on unstable_only, got {other:?}"),
    };
    let mut rep_a2 = rep_a.clone();
    rep_a2.case_id = wit_reportless_a.case_id.clone();
    let dup_main = reg_split_scope.record_witness(
        &wit_reportless_a,
        &rep_a2,
        "main",
        true,
        "mir_v1_itree",
        "2222222222222222222222222222222222222222",
        None,
    );
    assert!(matches!(dup_main, DedupRecordOutcome::DuplicateHit { .. }));
    assert_eq!(reg_split_scope.buckets[&root_bid].branch_scope, "both");
    assert_eq!(reg_split_scope.buckets[&root_bid].witnesses[0].fingerprint.branch_scope, "both");
    let mut rep_pass = rep_b.clone();
    rep_pass.case_id = wit_pass.case_id.clone();
    assert!(matches!(
        reg_split_scope.record_witness(
            &wit_pass,
            &rep_pass,
            "main",
            true,
            "mir_v1_itree",
            "3333333333333333333333333333333333333333",
            None,
        ),
        DedupRecordOutcome::NewSkeletonAttached { .. }
    ));
    let split = reg_split_scope
        .classify_post_patch_replay(&root_bid, "4444444444444444444444444444444444444444", |w| {
            w.minimized_skeleton_hash != pass_skel
        })
        .unwrap();
    let ScbReplayVerdict::Split { split_bugs, .. } = split else {
        panic!("expected SCB Split");
    };
    assert_eq!(split_bugs.len(), 1);
    assert_eq!(split_bugs[0].branch_scope, "both");
    assert_eq!(split_bugs[0].primary_fingerprint.branch_scope, "both");
    assert!(split_bugs[0].exposed_on_main);

    // 3. `shrink_and_build_witness_two_tier_with_budget` never runs `eval_prog`
    //    past `budget.max_evals` (including `max_evals = 0` -> 0 calls).
    let sig_a = ShrinkFailureSignature::from_case_report(&rep_a).unwrap();
    let mut eval_calls_zero = 0usize;
    let (w_zero, err_zero) = shrink_and_build_witness_two_tier_with_budget(
        "r41_case_a",
        &prog_a,
        &rep_a.verdict,
        &sig_a,
        ShrinkBudget { max_evals: 0, max_duration: Duration::from_secs(60) },
        FastLegStrategy::FullFourWay,
        |_| true,
        |_| {
            eval_calls_zero += 1;
            rep_a.clone()
        },
    );
    assert_eq!(eval_calls_zero, 0, "max_evals=0 must perform zero eval_prog calls");
    assert!(w_zero.shrink.budget_exhausted);
    assert!(!w_zero.shrink.is_one_minimal);
    assert!(matches!(err_zero, Some(TraceVerdict::ToolError { .. })));

    let mut big_prog = generate_fuzz_batch(0x4141_0009, 1).pop().unwrap();
    big_prog.input_x = 100;
    big_prog.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 2 },
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 3 },
    ];
    let mut eval_calls_two = 0usize;
    let (w_two, err_two) = shrink_and_build_witness_two_tier_with_budget(
        "r41_case_a",
        &big_prog,
        &rep_a.verdict,
        &sig_a,
        ShrinkBudget { max_evals: 2, max_duration: Duration::from_secs(60) },
        FastLegStrategy::FullFourWay,
        |_| true,
        |_| {
            eval_calls_two += 1;
            rep_a.clone()
        },
    );
    assert!(eval_calls_two <= 2, "budgeted shrink exceeded max_evals=2: calls={eval_calls_two}");
    assert_eq!(eval_calls_two, w_two.shrink.predicate_evaluations);
    assert!(w_two.shrink.budget_exhausted);
    assert!(matches!(err_two, Some(TraceVerdict::ToolError { .. })));

    let mut eval_calls_conv = 0usize;
    let (w_conv, err_conv) = shrink_and_build_witness_two_tier_with_budget(
        "r41_case_a",
        &prog_a,
        &rep_a.verdict,
        &sig_a,
        ShrinkBudget::default(),
        FastLegStrategy::FullFourWay,
        |_| true,
        |_| {
            eval_calls_conv += 1;
            rep_a.clone()
        },
    );
    assert!(err_conv.is_none());
    assert!(w_conv.shrink.is_one_minimal);
    assert_eq!(
        eval_calls_conv, w_conv.shrink.predicate_evaluations,
        "converged witness confirmation eval must be charged to predicate_evaluations"
    );

    // 4. Direct `metamorphic_duality` `ShrinkableCase` stays provisional in
    //    `BugRegistry::record_shrinkable_case` because it emits no twin pair.
    let sc_meta = ShrinkableCase {
        name: "r41_meta_sc".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let meta_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "metamorphic_duality",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: vec!["called_rustc_o0_vs_o2".to_string()],
        metamorphic_leg_kinds: "called_o0=returned,called_o2=unwound".into(),
        spine_relation: None,
    };
    let dual_unw = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) },
        ),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2".into()),
    };
    let mut reg_meta_sc = BugRegistry::new("google/zerocopy");
    let meta_out = reg_meta_sc.record_shrinkable_case(
        &sc_meta,
        &meta_sig,
        Some(&dual_unw),
        Some(&mk_auth("miri", ret_ok.clone())),
        Some(&mk_auth("lean", ret_ok)),
        "main",
        true,
        "v1",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        1,
        true,
    );
    assert!(matches!(meta_out, DedupRecordOutcome::Provisional { .. }), "{meta_out:?}");
    assert!(reg_meta_sc.buckets.is_empty());

    // 5. Mixed `unstable_only` + `main` split leaves child with
    //    `branch_scope == "unstable_only"` AND `exposed_on_main == false`,
    //    and `KnownBugRecord::validate` / `SemanticsDetailKnownBug::validate`
    //    reject contradictory `unstable_only` + `exposed_on_main=true`.
    let mut reg_split_uns = BugRegistry::new("google/zerocopy");
    let mixed_parent_bid = match reg_split_uns.record_witness(
        &wit_reportless_a,
        &rep_a,
        "unstable_only",
        false,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    assert!(matches!(
        reg_split_uns.record_witness(
            &wit_pass,
            &rep_pass,
            "main",
            true,
            "mir_v1_itree",
            "2222222222222222222222222222222222222222",
            None,
        ),
        DedupRecordOutcome::NewSkeletonAttached { .. }
    ));
    let uns_split = reg_split_uns
        .classify_post_patch_replay(
            &mixed_parent_bid,
            "3333333333333333333333333333333333333333",
            |w| w.minimized_skeleton_hash != pass_skel,
        )
        .unwrap();
    let ScbReplayVerdict::Split { split_bugs: uns_children, .. } = uns_split else {
        panic!("expected SCB Split");
    };
    assert_eq!(uns_children.len(), 1);
    assert_eq!(uns_children[0].branch_scope, "unstable_only");
    assert!(!uns_children[0].exposed_on_main);
    let mut bad_kb = uns_children[0].to_known_bug_record().unwrap();
    let mut bad_sd = uns_children[0].to_semantics_detail_entry().unwrap();
    bad_kb.exposed_on_main = true;
    bad_sd.exposed_on_main = true;
    assert!(bad_kb.validate().is_err());
    assert!(bad_sd.validate().is_err());

    // 6. Reportless witness with conflicting `signature` or `verdict` fails
    //    closed against fallback `report`.
    let mut rep_other_verdict = rep_a.clone();
    rep_other_verdict.verdict =
        TraceVerdict::UnsoundAccept { detail: "different detail".to_string() };
    assert!(
        CanonicalBugFingerprint::from_1_minimal_witness(
            &wit_reportless_a,
            &rep_other_verdict,
            "main",
            "mir_v1_itree",
            None,
        )
        .is_err()
    );
    let wrong_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "unwound",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "unwound".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut wit_wrong_sig = wit_reportless_a;
    wit_wrong_sig.signature = Some(wrong_sig);
    assert!(
        CanonicalBugFingerprint::from_1_minimal_witness(
            &wit_wrong_sig,
            &rep_a,
            "main",
            "mir_v1_itree",
            None,
        )
        .is_err()
    );
}

#[test]
fn codex_branch_scope_empty_corpus_and_nested_outputs_regression() {
    // 1. Validate bidirectional `branch_scope` <-> `exposed_on_main` invariants
    //    and allowed scope vocabulary (`unstable_only`, `main`, `both`).
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep = mk_ub_case_report(
        "scope_case",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let mut prog = generate_fuzz_batch(0x4242_0001, 1).pop().unwrap();
    prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let mut sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| p.steps.len() == 1);
    sr.succeeded = true;
    sr.is_one_minimal = true;
    sr.converged_1_minimal = true;
    let wit =
        WitnessArtifact::from_shrink("scope_case", rep.verdict.clone(), rep.verdict.clone(), sr);

    let mut reg_valid = BugRegistry::new("google/zerocopy");
    let bid = match reg_valid.record_witness(
        &wit,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    let bucket = &reg_valid.buckets[&bid];

    for (bad_scope, bad_exposed) in [
        ("main", false),
        ("both", false),
        ("unstable_only", true),
        ("custom_branch", false),
        ("custom_branch", true),
    ] {
        let mut bad_kb = bucket.to_known_bug_record().unwrap();
        bad_kb.branch_scope = bad_scope.to_string();
        bad_kb.exposed_on_main = bad_exposed;
        assert!(
            bad_kb.validate().is_err(),
            "KnownBugRecord must reject ({bad_scope:?}, {bad_exposed})"
        );

        let mut bad_sd = bucket.to_semantics_detail_entry().unwrap();
        bad_sd.branch_scope = bad_scope.to_string();
        bad_sd.exposed_on_main = bad_exposed;
        assert!(
            bad_sd.validate().is_err(),
            "SemanticsDetailKnownBug must reject ({bad_scope:?}, {bad_exposed})"
        );

        let mut bad_reg = BugRegistry::new("google/zerocopy");
        let rec = bad_reg.record_witness(
            &wit,
            &rep,
            bad_scope,
            bad_exposed,
            "mir_v1_itree",
            "1111111111111111111111111111111111111111",
            None,
        );
        assert!(
            matches!(rec, DedupRecordOutcome::Provisional { .. }),
            "record_witness must reject ({bad_scope:?}, {bad_exposed}): {rec:?}"
        );
        assert!(bad_reg.buckets.is_empty());
    }

    // 2. Reject empty explicit `--corpus-dir` when neither `--corpus` nor
    //    `--fuzz` is supplied (preventing silent zero-case exit 0).
    let tmp = tempfile::tempdir().unwrap();
    let empty_corpus = tmp.path().join("empty_corpus");
    fs::create_dir_all(&empty_corpus).unwrap();
    let cli_empty = Command::new(env!("CARGO_BIN_EXE_itree-diff"))
        .args(["--no-miri", "--no-lean", "--corpus-dir"])
        .arg(&empty_corpus)
        .output()
        .unwrap();
    assert_eq!(cli_empty.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&cli_empty.stderr).contains("contained no supported seed"),
        "stderr={:?}",
        String::from_utf8_lossy(&cli_empty.stderr)
    );

    // 3. Reject nested ancestor/descendant CLI report paths while permitting
    //    disjoint sibling paths.
    let nested_parent = tmp.path().join("out");
    let nested_child = nested_parent.join("bugs.json");
    let disjoint_sibling = tmp.path().join("out2");
    assert!(
        anneal_itree_diff::validate_distinct_output_paths_with_dirs(
            &[
                ("--json-report", nested_parent.as_path()),
                ("--known-bugs-out", nested_child.as_path()),
            ],
            &[],
        )
        .is_err()
    );
    assert!(
        anneal_itree_diff::validate_distinct_output_paths_with_dirs(
            &[
                ("--known-bugs-out", nested_child.as_path()),
                ("--json-report", nested_parent.as_path()),
            ],
            &[],
        )
        .is_err()
    );
    assert!(
        anneal_itree_diff::validate_distinct_output_paths_with_dirs(
            &[
                ("--json-report", nested_parent.as_path()),
                ("--known-bugs-out", disjoint_sibling.as_path()),
            ],
            &[],
        )
        .is_ok()
    );
}

#[test]
fn duration_budget_verdict_binding_caller_frame_and_mixed_split_regression() {
    // 1. Honor `budget.max_duration` BEFORE invoking the initial evaluation on
    //    `shrink_fuzz_program_two_tier_with_budget`,
    //    `shrink_and_build_witness_two_tier_with_budget`,
    //    and `shrink_case_two_tier_with_budget`.
    let mut prog = generate_fuzz_batch(0x4343_0001, 1).pop().unwrap();
    prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let zero_dur_budget = ShrinkBudget { max_evals: 64, max_duration: std::time::Duration::ZERO };

    let (mut prog_fast_calls, mut prog_calls) = (0usize, 0usize);
    let prog_zero = shrink_fuzz_program_two_tier_with_budget(
        &prog,
        zero_dur_budget,
        FastLegStrategy::FullFourWay,
        |_| {
            prog_fast_calls += 1;
            true
        },
        |_| {
            prog_calls += 1;
            true
        },
    );
    assert_eq!(
        prog_fast_calls + prog_calls,
        0,
        "zero wall-clock budget must make zero evaluations"
    );
    assert!(prog_zero.budget_exhausted);
    assert!(!prog_zero.succeeded && !prog_zero.is_one_minimal);

    let sc = ShrinkableCase {
        name: "zero_dur_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 5, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 3, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let (mut sc_fast_calls, mut sc_calls) = (0usize, 0usize);
    let sc_zero = shrink_case_two_tier_with_budget(
        &sc,
        zero_dur_budget,
        FastLegStrategy::FullFourWay,
        |_| {
            sc_fast_calls += 1;
            true
        },
        |_| {
            sc_calls += 1;
            true
        },
    );
    assert_eq!(
        sc_fast_calls + sc_calls,
        0,
        "zero wall-clock budget must make zero ShrinkableCase evals"
    );
    assert!(sc_zero.budget_exhausted);
    assert!(!sc_zero.succeeded && !sc_zero.is_one_minimal);

    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep_ub = mk_ub_case_report(
        "r43_idx_case",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let sig_ub = ShrinkFailureSignature::from_case_report(&rep_ub).unwrap();
    let (mut wit_fast_calls, mut wit_calls) = (0usize, 0usize);
    let (w_zero_dur, w_zero_err) = shrink_and_build_witness_two_tier_with_budget(
        "r43_idx_case",
        &prog,
        &rep_ub.verdict,
        &sig_ub,
        zero_dur_budget,
        FastLegStrategy::FullFourWay,
        |_| {
            wit_fast_calls += 1;
            true
        },
        |_| {
            wit_calls += 1;
            rep_ub.clone()
        },
    );
    assert_eq!(wit_fast_calls + wit_calls, 0, "zero wall-clock budget must not run eval_prog");
    assert!(w_zero_dur.shrink.budget_exhausted);
    assert!(matches!(w_zero_err, Some(TraceVerdict::ToolError { .. })));

    // 2. Indexed witness whose `original_verdict` disagrees with `cases[idx]`
    //    must NOT record its embedded `minimized_report` against an `Agree`
    //    case sharing the same `case_id` (nor fall back to it).
    let mut sr_ok =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| p.steps.len() == 1);
    sr_ok.succeeded = true;
    sr_ok.is_one_minimal = true;
    sr_ok.converged_1_minimal = true;
    let wit_idx_mismatch = WitnessArtifact::from_shrink(
        "r43_idx_case",
        rep_ub.verdict.clone(),
        rep_ub.verdict.clone(),
        sr_ok,
    )
    .with_minimized_report(rep_ub.clone())
    .with_report_index(0);
    let mut agree_case = rep_ub.clone();
    agree_case.verdict = TraceVerdict::Agree;
    let mut reg_idx = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut reg_idx,
        std::slice::from_ref(&agree_case),
        std::slice::from_ref(&wit_idx_mismatch),
        "main",
        true,
        "mir_v1_itree",
        &"5".repeat(40),
    );
    assert!(
        reg_idx.buckets.is_empty(),
        "indexed witness with mismatched original_verdict must not promote Agree case"
    );
    let mut wit_none_mismatch = wit_idx_mismatch;
    wit_none_mismatch.report_index = None;
    let mut reg_none = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut reg_none,
        &[agree_case],
        &[wit_none_mismatch],
        "main",
        true,
        "mir_v1_itree",
        &"5".repeat(40),
    );
    assert!(
        reg_none.buckets.is_empty(),
        "reportless witness with mismatched original_verdict must not promote Agree case"
    );

    // 3. Keep `ShrinkableCase` `caller_frame_law` provisional since
    //    standalone shrinkable reproducers lack caller-frame watchers.
    let mut bad_frame_rep = rep_ub;
    bad_frame_rep.verdict =
        TraceVerdict::UnsoundAccept { detail: "lean violated CallerFrameLaw".into() };
    let mut bad_lean = bad_frame_rep.lean.unwrap();
    bad_lean.caller_frame_law = CallerFrameLaw {
        caller_locals_preserved: false,
        untouched_alloc_bytes_preserved: true,
        padding_mask_respected: true,
        violations: vec!["caller_locals corrupted".into()],
    };
    bad_frame_rep.lean = Some(bad_lean);
    let cf_sig = ShrinkFailureSignature::from_case_report(&bad_frame_rep).unwrap();
    assert_eq!(cf_sig.mismatch_category, "caller_frame_law");
    let mut reg_cf = BugRegistry::new("google/zerocopy");
    let cf_out = reg_cf.record_shrinkable_case(
        &sc,
        &cf_sig,
        Some(&bad_frame_rep.rustc_dual),
        bad_frame_rep.miri.as_ref(),
        bad_frame_rep.lean.as_ref(),
        "main",
        true,
        "mir_v1_itree",
        &"6".repeat(40),
        1,
        true,
    );
    assert!(
        matches!(cf_out, DedupRecordOutcome::Provisional { .. }),
        "ShrinkableCase caller_frame_law must stay provisional: {cf_out:?}"
    );
    assert!(reg_cf.buckets.is_empty());

    // 4. Recompute `orig.branch_scope` / `orig.exposed_on_main` from retained
    //    fixed witnesses on mixed-branch SCB splits in both
    //    `unstable_only`-fixed / `main`-open and
    //    `main`-fixed / `unstable_only`-open directions.
    let mut prog_u = prog;
    prog_u.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let mut prog_m = prog_u.clone();
    prog_m.steps = vec![
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
        FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
    ];
    let mut sr_u =
        shrink_fuzz_program_with_budget(&prog_u, ShrinkBudget::default(), |p| p.steps.len() == 1);
    sr_u.succeeded = true;
    sr_u.is_one_minimal = true;
    sr_u.converged_1_minimal = true;
    let mut sr_m =
        shrink_fuzz_program_with_budget(&prog_m, ShrinkBudget::default(), |p| p.steps.len() == 2);
    sr_m.succeeded = true;
    sr_m.is_one_minimal = true;
    sr_m.converged_1_minimal = true;

    let mut rep_u = mk_ub_case_report(
        "g2_r26_unstable",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let mut rep_m = mk_ub_case_report(
        "g2_r26_main",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_ok,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let wit_u = WitnessArtifact::from_shrink(
        &rep_u.case_id,
        rep_u.verdict.clone(),
        rep_u.verdict.clone(),
        sr_u,
    );
    let wit_m = WitnessArtifact::from_shrink(
        &rep_m.case_id,
        rep_m.verdict.clone(),
        rep_m.verdict.clone(),
        sr_m,
    );
    let u_skel = wit_u.minimized_skeleton_hash.clone();
    let m_skel = wit_m.minimized_skeleton_hash.clone();

    // Case A: `unstable_only` witness fixed, `main` witness still failing.
    let mut reg_u_fixed = BugRegistry::new("google/zerocopy");
    let bid_a = match reg_u_fixed.record_witness(
        &wit_u,
        &rep_u,
        "unstable_only",
        false,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    assert!(matches!(
        reg_u_fixed.record_witness(
            &wit_m,
            &rep_m,
            "main",
            true,
            "mir_v1_itree",
            "2222222222222222222222222222222222222222",
            None,
        ),
        DedupRecordOutcome::NewSkeletonAttached { .. }
    ));
    let ScbReplayVerdict::Split { split_bugs: split_a, .. } = reg_u_fixed
        .classify_post_patch_replay(&bid_a, "3333333333333333333333333333333333333333", |w| {
            w.minimized_skeleton_hash == m_skel
        })
        .unwrap()
    else {
        panic!("expected Split for case A");
    };
    let parent_a = &reg_u_fixed.buckets[&bid_a];
    assert_eq!(parent_a.branch_scope, "unstable_only");
    assert!(!parent_a.exposed_on_main);
    assert_eq!(parent_a.primary_fingerprint.branch_scope, "unstable_only");
    assert_eq!(split_a.len(), 1);
    assert_eq!(split_a[0].branch_scope, "main");
    assert!(split_a[0].exposed_on_main);
    assert!(reg_u_fixed.to_known_bug_records().is_ok());
    assert!(reg_u_fixed.to_semantics_detail_entries().is_ok());

    // Case B: `main` witness fixed, `unstable_only` witness still failing.
    rep_u.case_id = "g2_r26_b_unstable".into();
    rep_m.case_id = "g2_r26_b_main".into();
    let mut wit_u_b = wit_u;
    wit_u_b.case_id = rep_u.case_id.clone();
    let mut wit_m_b = wit_m;
    wit_m_b.case_id = rep_m.case_id.clone();
    let mut reg_m_fixed = BugRegistry::new("google/zerocopy");
    let bid_b = match reg_m_fixed.record_witness(
        &wit_m_b,
        &rep_m,
        "main",
        true,
        "mir_v1_itree",
        "1111111111111111111111111111111111111111",
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    assert!(matches!(
        reg_m_fixed.record_witness(
            &wit_u_b,
            &rep_u,
            "unstable_only",
            false,
            "mir_v1_itree",
            "2222222222222222222222222222222222222222",
            None,
        ),
        DedupRecordOutcome::NewSkeletonAttached { .. }
    ));
    let ScbReplayVerdict::Split { split_bugs: split_b, .. } = reg_m_fixed
        .classify_post_patch_replay(&bid_b, "3333333333333333333333333333333333333333", |w| {
            w.minimized_skeleton_hash == u_skel
        })
        .unwrap()
    else {
        panic!("expected Split for case B");
    };
    let parent_b = &reg_m_fixed.buckets[&bid_b];
    assert_eq!(parent_b.branch_scope, "main");
    assert!(parent_b.exposed_on_main);
    assert_eq!(parent_b.primary_fingerprint.branch_scope, "main");
    assert_eq!(split_b.len(), 1);
    assert_eq!(split_b[0].branch_scope, "unstable_only");
    assert!(!split_b[0].exposed_on_main);
    assert!(reg_m_fixed.to_known_bug_records().is_ok());
    assert!(reg_m_fixed.to_semantics_detail_entries().is_ok());
}

#[test]
fn shrinkable_signature_authority_validation_and_strict_probe_provisional_regression() {
    let head_sha = "7".repeat(40);
    let sc = ShrinkableCase {
        name: "sig_auth_guard".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let ret_ok = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let unw_ok = TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) };
    let dual_ok = RustcDualResult {
        o0: mk_auth("rustc-o0", ret_ok.clone()),
        o2: mk_auth("rustc-o2", ret_ok.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let miri_ok = mk_auth("miri", ret_ok.clone());
    let lean_ok = mk_auth("lean", ret_ok);
    let lean_unw = mk_auth("lean", unw_ok);

    // 1. `ub_cause_mismatch` rejects agreeing Miri + Lean `FaultUb` legs and
    //    only promotes when `compare_ub_fault_results` actually diverges.
    let mut miri_ptr_ub = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: dereferencing pointer failed".into(),
        },
    );
    miri_ptr_ub.entry_mem_digest = Some("same_digest".into());
    let mut lean_ptr_ub = mk_auth(
        "lean",
        TerminalOutcome::FaultUb {
            detail: "FaultKind.undefined: pointer or memory access undefined".into(),
        },
    );
    lean_ptr_ub.entry_mem_digest = Some("same_digest".into());
    let mut lean_uninit_ub = mk_auth(
        "lean",
        TerminalOutcome::FaultUb {
            detail: "FaultKind.undefined: uninitialized or invalid value undefined".into(),
        },
    );
    lean_uninit_ub.entry_mem_digest = Some("same_digest".into());
    let agreeing_ub_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "fault_ub",
        lean_outcome_kind: "fault_ub",
        mismatch_category: "ub_cause_mismatch",
        ref_ub_class: Some(anneal_itree_diff::outcome::UbFaultClass::PointerOrMemoryAccess),
        lean_ub_class: Some(anneal_itree_diff::outcome::UbFaultClass::PointerOrMemoryAccess),
        lean_fault_site_kind: "assign_or_mem_deref".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_ub = BugRegistry::new("google/zerocopy");
    let ub_agree_out = reg_ub.record_shrinkable_case(
        &sc,
        &agreeing_ub_sig,
        None,
        Some(&miri_ptr_ub),
        Some(&lean_ptr_ub),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(matches!(ub_agree_out, DedupRecordOutcome::Provisional { .. }), "{ub_agree_out:?}");
    assert!(reg_ub.buckets.is_empty());

    let true_ub_sig = ShrinkFailureSignature {
        lean_ub_class: Some(anneal_itree_diff::outcome::UbFaultClass::InvalidValueOrUninit),
        lean_fault_site_kind: "uninit_or_invalid_value".into(),
        ..agreeing_ub_sig
    };
    let ub_div_out = reg_ub.record_shrinkable_case(
        &sc,
        &true_ub_sig,
        None,
        Some(&miri_ptr_ub),
        Some(&lean_uninit_ub),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(matches!(ub_div_out, DedupRecordOutcome::NewBug { .. }), "{ub_div_out:?}");

    // 2. `terminal_outcome_mismatch` rejects zero-authority, missing-Lean,
    //    `Diverged`, and `FaultUb` legs, promoting only real accepting outcome
    //    divergences.
    let zero_auth_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "none",
        lean_outcome_kind: "none",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: String::new(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_val = BugRegistry::new("google/zerocopy");
    assert!(matches!(
        reg_val.record_shrinkable_case(
            &sc,
            &zero_auth_sig,
            None,
            None,
            None,
            "main",
            true,
            "mir_v1_itree",
            &head_sha,
            1,
            true,
        ),
        DedupRecordOutcome::Provisional { .. }
    ));
    let no_lean_sig =
        ShrinkFailureSignature { ref_outcome_kind: "returned", ..zero_auth_sig.clone() };
    assert!(matches!(
        reg_val.record_shrinkable_case(
            &sc,
            &no_lean_sig,
            Some(&dual_ok),
            Some(&miri_ok),
            None,
            "main",
            true,
            "mir_v1_itree",
            &head_sha,
            1,
            true,
        ),
        DedupRecordOutcome::Provisional { .. }
    ));
    let lean_diverged = mk_auth("lean", TerminalOutcome::Diverged { fuel: 32 });
    let div_sig = ShrinkFailureSignature {
        lean_outcome_kind: "diverged",
        lean_fault_site_kind: "diverged".into(),
        ..no_lean_sig.clone()
    };
    assert!(matches!(
        reg_val.record_shrinkable_case(
            &sc,
            &div_sig,
            Some(&dual_ok),
            Some(&miri_ok),
            Some(&lean_diverged),
            "main",
            true,
            "mir_v1_itree",
            &head_sha,
            1,
            true,
        ),
        DedupRecordOutcome::Provisional { .. }
    ));
    assert!(reg_val.buckets.is_empty());

    let real_val_sig = ShrinkFailureSignature {
        lean_outcome_kind: "unwound",
        lean_fault_site_kind: "unwound".into(),
        ..no_lean_sig
    };
    assert!(matches!(
        reg_val.record_shrinkable_case(
            &sc,
            &real_val_sig,
            Some(&dual_ok),
            Some(&miri_ok),
            Some(&lean_unw),
            "main",
            true,
            "mir_v1_itree",
            &head_sha,
            1,
            true,
        ),
        DedupRecordOutcome::NewBug { .. }
    ));

    // 3. `spine_mismatch` requires a named `spine_relation` backed by
    //    genuinely diverging authority spines.
    let ev_x = ObservableEvent::CallEnter {
        callee: "x".into(),
        arg_bytes: Vec::new(),
        arg_reprs: Vec::new(),
    };
    let mut reg_sp = BugRegistry::new("google/zerocopy");
    for bad_rel in [None, Some("rustc_o0_vs_o2"), Some("miri_vs_lean")] {
        let sp_sig = ShrinkFailureSignature {
            verdict_kind: "unsound_accept",
            ref_outcome_kind: "returned",
            lean_outcome_kind: "returned",
            mismatch_category: "spine_mismatch",
            ref_ub_class: None,
            lean_ub_class: None,
            lean_fault_site_kind: "returned".into(),
            metamorphic_relations: Vec::new(),
            metamorphic_leg_kinds: String::new(),
            spine_relation: bad_rel.map(str::to_string),
        };
        let mut dual_same_spine = dual_ok.clone();
        dual_same_spine.o0.spine.events = vec![ev_x.clone()];
        dual_same_spine.o2.spine.events = vec![ev_x.clone()];
        dual_same_spine.parity_ok = false;
        let mut m_same = miri_ok.clone();
        m_same.spine.events = vec![ev_x.clone()];
        let mut l_same = lean_ok.clone();
        l_same.spine.events = vec![ev_x.clone()];
        let out = reg_sp.record_shrinkable_case(
            &sc,
            &sp_sig,
            Some(&dual_same_spine),
            Some(&m_same),
            Some(&l_same),
            "main",
            true,
            "mir_v1_itree",
            &head_sha,
            1,
            true,
        );
        assert!(matches!(out, DedupRecordOutcome::Provisional { .. }), "bad_rel={bad_rel:?}");
    }
    assert!(reg_sp.buckets.is_empty());

    // 4. `strict_probe_accepted_multicall` remains Provisional via
    //    `record_shrinkable_case` because it carries no `lean_strict_probe`.
    let strict_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "strict_probe_accepted_multicall",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_strict = BugRegistry::new("google/zerocopy");
    let strict_out = reg_strict.record_shrinkable_case(
        &sc,
        &strict_sig,
        Some(&dual_ok),
        Some(&miri_ok),
        Some(&lean_ok),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(matches!(strict_out, DedupRecordOutcome::Provisional { .. }), "{strict_out:?}");
    assert!(reg_strict.buckets.is_empty());

    // 5. Preserve helper-shaped `UnwindProbe` callee schedule keys (`h7`,
    //    `fuzz_helper_7`) across `canonical_alpha_renamed` and direct
    //    `record_shrinkable_case` promotion.
    let mut uw_sched = EnvSchedule::default();
    uw_sched.push_callee("h7", EnvAction::Unwind { message: "probe_unwind".into() });
    uw_sched.push_callee("fuzz_helper_9", EnvAction::Unwind { message: "probe_nested".into() });
    let uw_probe_case = ShrinkableCase {
        name: "uw_helper_shaped".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 2,
            multiplier: 3,
            addend: 1,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::HelperCall {
                dst_local: 0,
                helper_id: 2,
                block_id: 0,
                bias: 1,
                rhs_local: None,
            },
            ShrinkStep::UnwindProbe {
                callee: "h7".into(),
                dst_local: 0,
                trigger_unwind: true,
                block_id: 1,
            },
            ShrinkStep::BranchMix {
                block_id: 2,
                cond_local: 0,
                taken_then: true,
                dynamic_even_cond: false,
                then_steps: vec![ShrinkStep::UnwindProbe {
                    callee: "fuzz_helper_9".into(),
                    dst_local: 0,
                    trigger_unwind: true,
                    block_id: 3,
                }],
                else_steps: Vec::new(),
            },
        ],
        env_schedule: uw_sched,
        return_local: 0,
    };
    let uw_alpha = uw_probe_case.canonical_alpha_renamed();
    assert!(uw_alpha.env_schedule.per_callee.contains_key("h7"));
    assert!(uw_alpha.env_schedule.per_callee.contains_key("fuzz_helper_9"));
    assert!(!uw_alpha.env_schedule.per_callee.contains_key("h1"));
    assert!(!uw_alpha.env_schedule.per_callee.contains_key("fuzz_helper_1"));
    assert!(!uw_alpha.env_schedule.per_callee.contains_key("fuzz_helper_2"));

    // 6. Re-observing skeleton `A` retained in a `Fixed` root bucket must
    //    reopen `root_id` via `UseRoot` even when split child
    //    `{root_id}-{skel6(A)}` holds a distinct 6-hex-colliding skeleton `B`.
    let rep_a_orig = mk_ub_case_report(
        "root_fixed_a",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(7),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let mut by_prefix6: std::collections::HashMap<String, (FuzzProgram, String)> =
        std::collections::HashMap::new();
    let mut cand_ab_progs = None;
    let base_prog = generate_fuzz_batch(0x9191_0001, 1).pop().unwrap();
    for code in 1..65_535u32 {
        let mut p = base_prog.clone();
        p.steps = (0..16)
            .map(|k| FuzzStep::ArithImm {
                op: if (code >> k) & 1 == 0 { FuzzArithOp::Add } else { FuzzArithOp::Sub },
                imm: 1,
            })
            .collect();
        let sk = canonical_fuzz_program_skeleton_hash(&p, None);
        let p6 = sk[..6].to_string();
        if let Some((prev_p, prev_sk)) = by_prefix6.get(&p6) {
            if prev_sk != &sk {
                cand_ab_progs = Some((prev_p.clone(), p));
                break;
            }
        } else {
            by_prefix6.insert(p6, (p, sk));
        }
    }
    let (pa, pb) = cand_ab_progs.expect("found 6-hex colliding pair (A, B)");
    let mk_wit = |id: &str, p: FuzzProgram| {
        let mut sr = shrink_fuzz_program_with_budget(&p, ShrinkBudget::default(), |q| q == &p);
        sr.succeeded = true;
        sr.is_one_minimal = true;
        sr.converged_1_minimal = true;
        let mut r = rep_a_orig.clone();
        r.case_id = id.into();
        let w = WitnessArtifact::from_shrink(id, r.verdict.clone(), r.verdict.clone(), sr);
        (w, r)
    };
    let (wa, ra) = mk_wit("col_root_a", pa);
    let (wb, rb) = mk_wit("col_root_b", pb);
    let sk_a = wa.minimized_skeleton_hash.clone();
    let sk_b = wb.minimized_skeleton_hash.clone();
    assert_eq!(&sk_a[..6], &sk_b[..6]);
    assert_ne!(sk_a, sk_b);

    let mut reg_col = BugRegistry::new("google/zerocopy");
    let root_bid =
        match reg_col.record_witness(&wa, &ra, "main", true, "mir_v1_itree", &head_sha, None) {
            DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
            other => panic!("expected root NewBug: {other:?}"),
        };
    assert!(matches!(
        reg_col.record_witness(&wb, &rb, "main", true, "mir_v1_itree", &head_sha, None),
        DedupRecordOutcome::NewSkeletonAttached { .. }
    ));
    let patch_sha = "8".repeat(40);
    // Mark `A` fixed while `B` splits into `{root_bid}-{skel6}`.
    let split_v = reg_col
        .classify_post_patch_replay(&root_bid, &patch_sha, |w| w.minimized_skeleton_hash == sk_b)
        .unwrap();
    assert!(matches!(split_v, ScbReplayVerdict::Split { .. }));
    assert_eq!(reg_col.buckets[&root_bid].status, BugStatus::Fixed);
    assert_eq!(reg_col.buckets.len(), 2);

    // Re-observing `A` must reopen `root_bid` via `UseRoot`, NOT mint a
    // duplicate `{root_bid}-{A}` child bucket.
    let reobs_a =
        reg_col.record_witness(&wa, &ra, "main", true, "mir_v1_itree", &"9".repeat(40), None);
    assert!(
        matches!(reobs_a, DedupRecordOutcome::DuplicateHit { ref bug_id, .. } if bug_id == &root_bid),
        "{reobs_a:?}"
    );
    assert_eq!(reg_col.buckets[&root_bid].status, BugStatus::Open);
    assert!(reg_col.buckets[&root_bid].fixed_sha.is_empty());
    assert_eq!(reg_col.buckets.len(), 2);
}

#[test]
fn r42_codex_findings_regression() {
    let head_sha = "1111111111111111111111111111111111111111";
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep = mk_ub_case_report(
        "r42_ub",
        "Undefined Behavior: Tree Borrows: write access through <0x10> at alloc5 is forbidden",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let sig = ShrinkFailureSignature::from_case_report(&rep).unwrap();
    let mut prog = generate_fuzz_batch(0x4242_0001, 1).pop().unwrap();
    prog.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }];
    let mut sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |q| q == &prog);
    sr.succeeded = true;
    sr.is_one_minimal = true;
    sr.converged_1_minimal = true;
    sr.budget_exhausted = false;

    let mut stored_sched = EnvSchedule::default();
    stored_sched.global.push_back(EnvAction::ReturnBytes(5u32.to_le_bytes().to_vec()));
    let mut alt_sched = EnvSchedule::default();
    alt_sched.global.push_back(EnvAction::Abort { reason: "alt abort".into() });

    let base_art = WitnessArtifact::from_shrink_with_schedule(
        "r42_ub",
        rep.verdict.clone(),
        rep.verdict.clone(),
        sr.clone(),
        Some(&stored_sched),
    )
    .with_signature(sig)
    .with_minimized_report(rep.clone());
    assert_eq!(base_art.repro_schedule.as_ref(), Some(&stored_sched));

    // 1. Conflicting explicit schedule against stored `repro_schedule` fails
    //    closed in `try_from_witness`, `from_1_minimal_witness`, and
    //    `record_witness`.
    assert!(WitnessBundle::try_from_witness(base_art.clone(), Some(&stored_sched)).is_ok());
    let err_bundle =
        WitnessBundle::try_from_witness(base_art.clone(), Some(&alt_sched)).unwrap_err();
    assert!(err_bundle.contains("conflicts with stored"), "{err_bundle}");
    let err_fp = CanonicalBugFingerprint::from_1_minimal_witness(
        &base_art,
        &rep,
        "main",
        "mir_v1_itree",
        Some(&alt_sched),
    )
    .unwrap_err();
    assert!(err_fp.contains("conflicts with stored"), "{err_fp}");
    let mut conflict_reg = BugRegistry::new("google/zerocopy");
    let conflict_out = conflict_reg.record_witness(
        &base_art,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        Some(&alt_sched),
    );
    assert!(matches!(conflict_out, DedupRecordOutcome::Provisional { .. }), "{conflict_out:?}");
    assert!(conflict_reg.buckets.is_empty());

    // 2. Non-converged (`converged_1_minimal = false`) or `budget_exhausted`
    //    witnesses are rejected even when `succeeded && is_one_minimal`.
    let mut not_conv_art = base_art.clone();
    not_conv_art.shrink.converged_1_minimal = false;
    assert!(WitnessBundle::try_from_witness(not_conv_art.clone(), None).is_err());
    let mut exhaust_art = base_art.clone();
    exhaust_art.shrink.budget_exhausted = true;
    assert!(WitnessBundle::try_from_witness(exhaust_art.clone(), None).is_err());
    let mut conv_reg = BugRegistry::new("google/zerocopy");
    for bad_art in [&not_conv_art, &exhaust_art] {
        let out =
            conv_reg.record_witness(bad_art, &rep, "main", true, "mir_v1_itree", head_sha, None);
        assert!(matches!(out, DedupRecordOutcome::Provisional { .. }), "{out:?}");
    }
    assert!(conv_reg.buckets.is_empty());
    assert_eq!(conv_reg.provisional_cases.len(), 2);

    // 3. Exported `BugBucket` rejects fabricated `bug_id`, mismatched
    //    witness fingerprints, missing witnesses, and bad split suffixes.
    let mut valid_reg = BugRegistry::new("google/zerocopy");
    let root_id = match valid_reg.record_witness(
        &base_art,
        &rep,
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    assert!(valid_reg.to_known_bug_records().is_ok());
    assert!(valid_reg.to_semantics_detail_entries().is_ok());

    let mut bogus_id_reg = valid_reg.clone();
    bogus_id_reg.buckets.get_mut(&root_id).unwrap().bug_id = "ITREE-FAKE-000000000000".into();
    assert!(bogus_id_reg.to_known_bug_records().is_err());
    assert!(bogus_id_reg.to_semantics_detail_entries().is_err());

    let mut bad_split_reg = valid_reg.clone();
    bad_split_reg.buckets.get_mut(&root_id).unwrap().bug_id = format!("{root_id}-deadbe");
    assert!(bad_split_reg.to_known_bug_records().is_err());
    assert!(bad_split_reg.to_semantics_detail_entries().is_err());

    let mut empty_wit_reg = valid_reg.clone();
    empty_wit_reg.buckets.get_mut(&root_id).unwrap().witnesses.clear();
    assert!(empty_wit_reg.to_known_bug_records().is_err());
    assert!(empty_wit_reg.to_semantics_detail_entries().is_err());

    let mut ok_resplit_reg = valid_reg.clone();
    let skel = base_art.minimized_skeleton_hash.clone();
    ok_resplit_reg.buckets.get_mut(&root_id).unwrap().bug_id = format!("{root_id}-resplit-{skel}");
    assert!(ok_resplit_reg.to_known_bug_records().is_ok());
    assert!(ok_resplit_reg.to_semantics_detail_entries().is_ok());

    // 4. Both `KnownBugsExport::validate` and
    //    `SemanticDetailRecord::validate_honesty` enforce 40-hex Git SHAs
    //    (and reject all-zero SHAs on `PASS` / `verified_at_head`).
    let diff_report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![rep],
        Vec::new(),
    );
    let mut ctx = TelemetryContext::discover(std::path::Path::new("/nonexistent"));
    ctx.repo = "google/zerocopy".into();
    ctx.branch = "main".into();
    ctx.branch_scope = "main".into();
    ctx.exposed_on_main = true;
    ctx.commit_sha = head_sha.into();
    let base_kb =
        KnownBugsExport::from_report_and_registry(&diff_report, &valid_reg, &ctx).unwrap();
    let base_det =
        SemanticDetailRecord::from_report_and_registry(&diff_report, &valid_reg, &ctx).unwrap();
    for bad_sha in ["unknown", "abc", "deadbeef", &"z".repeat(40), &"1".repeat(39)] {
        let mut kb = base_kb.clone();
        kb.commit_sha = bad_sha.into();
        assert!(kb.validate().is_err(), "expected KB error for {bad_sha:?}");
        let mut det = base_det.clone();
        det.commit_sha = bad_sha.into();
        assert!(det.validate_honesty().is_err(), "expected detail error for {bad_sha:?}");
    }
    let mut zero_verified_kb = base_kb;
    zero_verified_kb.commit_sha = "0".repeat(40);
    zero_verified_kb.build_freshness = "verified_at_head".into();
    assert!(zero_verified_kb.validate().is_err());

    let mut zero_verified_det = base_det;
    zero_verified_det.commit_sha = "0".repeat(40);
    zero_verified_det.build_freshness = "verified_at_head".into();
    assert!(zero_verified_det.validate_honesty().is_err());
}

#[test]
fn fast_first_shrink_preserves_custom_case_id_and_alpha_rename_avoids_unwind_probe_collision() {
    use std::os::unix::fs::PermissionsExt;

    let tmp = tempfile::tempdir().expect("tempdir");

    // 1. `DifferentialEngine::shrink_fuzz_program_fast_first` preserves custom
    //    `case_id` values across both Tier-1 and Tier-2 runs so
    //    `witness.case_id` and `witness.minimized_report.case_id` match.
    let real_rustc =
        anneal_itree_diff::rustc_runner::RustcRunner::discover(None).expect("discover host rustc");
    let fake_rustc = tmp.path().join("fake_rustc.sh");
    let script = format!(
        r#"#!/bin/sh
set -eu
PATH="/usr/bin:/bin:${{PATH:-}}"
export PATH
for a in "$@"; do
  if [ "$a" = "--print" ]; then
    exec "{rustc}" "$@"
  fi
  if [ "$a" = "-vV" ]; then
    exec "{rustc}" "$@"
  fi
done
out=""
opt="0"
src=""
prev=""
for a in "$@"; do
  case "$prev" in
    -o) out="$a"; prev="" ;;
    -C)
      case "$a" in
        opt-level=*) opt="${{a#opt-level=}}" ;;
      esac
      prev=""
      ;;
    *)
      case "$a" in
        -o|-C) prev="$a" ;;
        *.rs) src="$a" ;;
      esac
      ;;
  esac
done
ret_val="1"
if [ "$opt" = "2" ] && grep -q "11111" "$src"; then
  ret_val="2"
fi
cat > "$out" <<EOF
#!/bin/sh
PATH="/usr/bin:/bin:\${{PATH:-}}"
export PATH
printf 'ANNEAL_ITREE_PRE_ENTRY:{{"boundary_slots":[[1,0,0,0],[2,0,0,0]]}}\n'
printf 'ANNEAL_ITREE_TRACE_JSON:{{"outcome_kind":"returned","ret":{{"kind":"scalar","kind_id":"u32","bits":"%s"}},"detail":"","boundary_slots":[[1,0,0,0],[2,0,0,0],[16,%s,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}}\n' "$ret_val" "$ret_val"
EOF
chmod +x "$out"
"#,
        rustc = real_rustc.rustc_bin.display(),
    );
    fs::write(&fake_rustc, script).expect("write fake rustc");
    let mut perms = fs::metadata(&fake_rustc).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&fake_rustc, perms).unwrap();

    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.enable_lean = false;
    cfg.check_metamorphic_duality = false;
    let fake_rustc_os = fake_rustc.as_os_str().to_os_string();
    let engine = DifferentialEngine::prepare_with_env(cfg, |k| match k {
        "ANNEAL_ITREE_RUSTC" => Some(fake_rustc_os.clone()),
        _ => None,
    })
    .expect("prepare engine with fake rustc");

    let prog = FuzzProgram {
        seed: 0x3001,
        index: 7,
        input_x: 1,
        input_y: 2,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 22222 },
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 11111 },
        ],
        applied_mutators: Vec::new(),
    };
    let custom_id = "custom_fast_first_case";
    let mut init_case = prog.to_trace_test_case();
    init_case.id = custom_id.to_string();
    let init_report = engine.run_case(&init_case);
    let target_sig = ShrinkFailureSignature::from_case_report(&init_report)
        .unwrap_or_else(|| panic!("expected failure signature, got {:?}", init_report.verdict));
    assert_eq!(target_sig.mismatch_category, "rustc_o0_o2");

    let (witness, propagated_err) =
        engine.shrink_fuzz_program_fast_first(custom_id, &prog, &init_report.verdict, &target_sig);
    assert!(propagated_err.is_none(), "unexpected error: {propagated_err:?}");
    assert!(witness.shrink.succeeded);
    assert!(witness.shrink.is_one_minimal);
    assert!(witness.shrink.converged_1_minimal);
    assert!(!witness.shrink.budget_exhausted);
    assert_eq!(
        witness.shrink.minimized.steps,
        vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 11111 }]
    );
    assert_eq!(witness.case_id, custom_id);
    let min_rep = witness
        .minimized_report
        .as_deref()
        .expect("minimized_report must attach when custom case_id matches");
    assert_eq!(min_rep.case_id, custom_id);
    assert!(WitnessBundle::try_from_witness(witness.clone(), None).is_ok());

    let head_sha = "3".repeat(40);
    let mut reg_ff = BugRegistry::new("google/zerocopy");
    let rec_out = reg_ff.record_witness(
        &witness,
        &init_report,
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        None,
    );
    assert!(matches!(rec_out, DedupRecordOutcome::NewBug { .. }), "{rec_out:?}");
    assert!(reg_ff.provisional_cases.is_empty());

    let mut reg_tel = BugRegistry::new("google/zerocopy");
    record_report_telemetry_witnesses(
        &mut reg_tel,
        std::slice::from_ref(&init_report),
        &[witness],
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
    );
    assert_eq!(reg_tel.buckets.len(), 1);
    assert!(reg_tel.provisional_cases.is_empty());

    // 2. `ShrinkableCase::canonical_alpha_renamed` reserves numeric helper IDs
    //    claimed by helper-shaped `UnwindProbe` callees so neither helpers nor
    //    orphan `env_schedule` keys collide or demote to Provisional.
    let act_a: std::collections::VecDeque<EnvAction> =
        vec![EnvAction::ReturnBytes(vec![1, 0, 0, 0])].into();
    let act_b: std::collections::VecDeque<EnvAction> =
        vec![EnvAction::ReturnBytes(vec![2, 0, 0, 0])].into();
    let mut per_callee_t1 = std::collections::BTreeMap::new();
    per_callee_t1.insert("h0".to_string(), act_a.clone());
    per_callee_t1.insert("h2".to_string(), act_b.clone());
    let trig1 = ShrinkableCase {
        name: "trig1".into(),
        scalar_width: IntKind::U32,
        inputs: vec![
            ShrinkInput { local_id: 1, width: IntKind::U32, value: 3, align_hint: None },
            ShrinkInput { local_id: 2, width: IntKind::U32, value: 4, align_hint: None },
        ],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 2,
            multiplier: 3,
            addend: 5,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![
            ShrinkStep::HelperCall {
                dst_local: 3,
                helper_id: 2,
                block_id: 0,
                bias: 1,
                rhs_local: Some(2),
            },
            ShrinkStep::UnwindProbe {
                callee: "h0".into(),
                dst_local: 4,
                trigger_unwind: false,
                block_id: 1,
            },
        ],
        env_schedule: EnvSchedule {
            per_callee: per_callee_t1,
            global: std::collections::VecDeque::new(),
        },
        return_local: 4,
    };
    let canon1 = trig1.canonical_alpha_renamed();
    assert_eq!(canon1.helpers.len(), 1);
    assert_eq!(canon1.helpers[0].helper_id, 1);
    assert_eq!(canon1.env_schedule.per_callee.get("h0"), Some(&act_a));
    assert_eq!(canon1.env_schedule.per_callee.get("h1"), Some(&act_b));
    assert_eq!(canon1.canonical_alpha_renamed(), canon1);
    let lean_t1 = anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&canon1, "t1");
    assert!(lean_t1.is_ok(), "Trigger 1 Lean lowering failed: {lean_t1:?}");

    let mut reg_sc = BugRegistry::new("google/zerocopy");
    let sc_rec = reg_sc.record_shrinkable_case(
        &trig1,
        &target_sig,
        Some(&init_report.rustc_dual),
        init_report.miri.as_ref(),
        init_report.lean.as_ref(),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(matches!(sc_rec, DedupRecordOutcome::NewBug { .. }), "{sc_rec:?}");
    assert!(reg_sc.provisional_cases.is_empty());

    // Trigger 2: helper maps to 0 and `"h1"` is reserved, so orphan `"h5"`
    // skips 0 and 1 and remaps to `"h2"`, while orphan `"fuzz_helper_9"`
    // remaps cleanly past reserved/assigned IDs too.
    let act_c: std::collections::VecDeque<EnvAction> =
        vec![EnvAction::ReturnBytes(vec![9, 0, 0, 0])].into();
    let mut per_callee_t2 = std::collections::BTreeMap::new();
    per_callee_t2.insert("h1".to_string(), act_a.clone());
    per_callee_t2.insert("h5".to_string(), act_b.clone());
    per_callee_t2.insert("fuzz_helper_9".to_string(), act_c.clone());
    let mut trig2 = trig1;
    trig2.steps[1] = ShrinkStep::UnwindProbe {
        callee: "h1".into(),
        dst_local: 4,
        trigger_unwind: false,
        block_id: 1,
    };
    trig2.env_schedule =
        EnvSchedule { per_callee: per_callee_t2, global: std::collections::VecDeque::new() };
    let canon2 = trig2.canonical_alpha_renamed();
    assert_eq!(canon2.helpers[0].helper_id, 0);
    assert_eq!(canon2.env_schedule.per_callee.get("h1"), Some(&act_a));
    assert_eq!(canon2.env_schedule.per_callee.get("h2"), Some(&act_b));
    assert_eq!(canon2.env_schedule.per_callee.get("fuzz_helper_3"), Some(&act_c));
    assert_eq!(canon2.canonical_alpha_renamed(), canon2);
    // Orphan schedule queues (`h2`, `fuzz_helper_3`) fail closed on standalone
    // Lean lowering.
    let err_t2 = anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&canon2, "t2")
        .unwrap_err();
    assert!(err_t2.contains("unreachable callee"), "unexpected err: {err_t2}");
    let mut canon2_reachable = canon2;
    canon2_reachable.env_schedule.per_callee.remove("h2");
    canon2_reachable.env_schedule.per_callee.remove("fuzz_helper_3");
    let lean_t2 =
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&canon2_reachable, "t2");
    assert!(lean_t2.is_ok(), "Trigger 2 Lean lowering failed: {lean_t2:?}");
}

#[test]
fn wide_int_unwind_reservation_miri_pin_gating_lifecycle_shas_bucket_invariants_and_seed_bounds() {
    use anneal_itree_diff::{
        fuzzer::{FuzzArithOp, FuzzProgram, FuzzStep, MutatorKind},
        load_fuzz_programs_from_dir,
        shrink::{ShrinkHelper, ShrinkHelperOp, ShrinkInput, ShrinkStep, ShrinkableCase},
    };

    let tmp = tempfile::tempdir().expect("tempdir");
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare engine");

    // 1. `parse_reserved_helper_callee_id` reserves helper ID 0 across `u128`
    //    and `i128` suffixes (`h0_u128`, `h0_i128`, `fuzz_helper_0_u128`).
    for reserved_callee in ["h0_u128", "h0_i128", "fuzz_helper_0_u128"] {
        let sc = ShrinkableCase {
            name: format!("wide_{reserved_callee}"),
            scalar_width: IntKind::U32,
            inputs: vec![
                ShrinkInput { local_id: 1, width: IntKind::U32, value: 3, align_hint: None },
                ShrinkInput { local_id: 2, width: IntKind::U128, value: 5, align_hint: None },
            ],
            struct_fields: Vec::new(),
            slice_len: None,
            slice_align: 1,
            helpers: vec![ShrinkHelper {
                helper_id: 2,
                op: ShrinkHelperOp::AffineMulAdd,
                multiplier: 3,
                addend: 1,
            }],
            steps: vec![
                ShrinkStep::HelperCall {
                    dst_local: 3,
                    helper_id: 2,
                    block_id: 0,
                    bias: 1,
                    rhs_local: None,
                },
                ShrinkStep::HelperCall {
                    dst_local: 4,
                    helper_id: 2,
                    block_id: 1,
                    bias: 2,
                    rhs_local: Some(2),
                },
                ShrinkStep::UnwindProbe {
                    callee: reserved_callee.to_string(),
                    dst_local: 5,
                    trigger_unwind: false,
                    block_id: 2,
                },
            ],
            env_schedule: EnvSchedule::default(),
            return_local: 5,
        };
        let canon = sc.canonical_alpha_renamed();
        assert_eq!(canon.helpers[0].helper_id, 1, "callee={reserved_callee}");
        assert_eq!(canon.canonical_alpha_renamed(), canon);
        let lean_res =
            anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&canon, "wide");
        assert!(lean_res.is_ok(), "callee={reserved_callee}: {lean_res:?}");

        let ok_res = AuthorityRunResult {
            authority: "miri".to_string(),
            outcome: TerminalOutcome::Returned {
                ret: TraceVal::Scalar { kind: IntKind::U32, bits: 1 },
                mem_digest: compute_boundary_mem_digest(&[]),
            },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::default(),
            entry_mem_digest: None,
            post_only_mem_digest: false,
            elapsed_ms: 0,
            raw_diagnostics: String::new(),
            tool_error: None,
        };
        let mut lean_uw = ok_res.clone();
        lean_uw.authority = "lean".to_string();
        lean_uw.outcome = TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) };
        let sig = ShrinkFailureSignature {
            verdict_kind: "unsound_accept",
            mismatch_category: "terminal_outcome_mismatch",
            ref_outcome_kind: "returned",
            ref_ub_class: None,
            lean_outcome_kind: "unwound",
            lean_ub_class: None,
            lean_fault_site_kind: "unwound".to_string(),
            spine_relation: None,
            metamorphic_relations: Vec::new(),
            metamorphic_leg_kinds: String::new(),
        };
        let mut reg = BugRegistry::new("google/zerocopy");
        let rec = reg.record_shrinkable_case(
            &sc,
            &sig,
            None,
            Some(&ok_res),
            Some(&lean_uw),
            "main",
            true,
            "mir_v1_itree",
            &"a".repeat(40),
            1,
            true,
        );
        assert!(
            matches!(rec, DedupRecordOutcome::NewBug { .. }),
            "callee={reserved_callee}: {rec:?}"
        );
    }

    // 2. Standalone metamorphic reproducer fails closed under `cfg!(miri)` for
    //    rustc-pinned relations and abort-scheduled runs.
    let meta_prog = FuzzProgram {
        seed: 0x32_02,
        index: 0,
        input_x: 7,
        input_y: 11,
        steps: vec![FuzzStep::HelperCall { callee_idx: 0, bias: 3 }],
        applied_mutators: vec![MutatorKind::CallBoundaryOutliner],
    };
    let mut abort_sched = EnvSchedule::default();
    abort_sched.push_callee("fuzz_helper_0", EnvAction::Abort { reason: "repro".into() });
    type MiriPinCase<'a> = (&'a str, Option<&'a EnvSchedule>, &'a [&'a str], bool, &'a str);
    let miri_pin_cases: &[MiriPinCase<'_>] = &[
        ("rustc_rel_under_miri", None, &["rustc_called_vs_inlined"], false, "cannot be replayed"),
        (
            "frame_rustc_under_miri",
            None,
            &["metamorphic_caller_frame_law:called_rustc"],
            false,
            "cannot be replayed",
        ),
        (
            "abort_rustc_rel_under_miri",
            Some(&abort_sched),
            &["rustc_called_vs_inlined"],
            false,
            "cannot be replayed",
        ),
        (
            "abort_miri_rel_under_miri",
            Some(&abort_sched),
            &["miri_called_vs_inlined"],
            false,
            "cannot be replayed",
        ),
        ("miri_rel_under_miri", None, &["miri_called_vs_inlined"], true, ""),
        ("unpinned_under_miri", None, &[], true, ""),
    ];
    for (tag, sched_opt, pins, expect_ok, expect_err_substr) in miri_pin_cases {
        let owned_pins: Vec<String> = pins.iter().map(|s| (*s).to_string()).collect();
        let src = anneal_itree_diff::shrink::render_standalone_fuzz_repro_rs_for_relations(
            &meta_prog,
            *sched_opt,
            tag,
            true,
            &owned_pins,
        );
        let rs_path = tmp.path().join(format!("{tag}.rs"));
        let bin_path = tmp.path().join(format!("{tag}_bin"));
        fs::write(&rs_path, &src).unwrap();
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024", "--cfg", "miri", "-A", "unexpected_cfgs"])
            .arg(&rs_path)
            .arg("-o")
            .arg(&bin_path)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{tag}: {}", String::from_utf8_lossy(&comp.stderr));
        let run = Command::new(&bin_path).output().unwrap();
        assert_eq!(
            run.status.success(),
            *expect_ok,
            "{tag}: stdout={} stderr={}",
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        );
        if !expect_err_substr.is_empty() {
            let stderr = String::from_utf8_lossy(&run.stderr);
            assert!(stderr.contains(expect_err_substr), "{tag}: {stderr}");
        }
    }

    // 3. Codex 4724136969 / 4724136973 / 4724136980: Lifecycle SHAs, bucket
    //    dialect binding, and derived severity / polarity validation.
    let head_sha = "a".repeat(40);
    let patch_sha = "b".repeat(40);
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep = mk_ub_case_report(
        "r32_dedup_guard",
        "Undefined Behavior: Data race detected between read and write",
        ret_val,
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let shrink_res = shrink_fuzz_program_with_budget(&meta_prog, ShrinkBudget::default(), |c| {
        !c.steps.is_empty()
    });
    assert!(shrink_res.succeeded && shrink_res.is_one_minimal);
    let art = WitnessArtifact::from_shrink(
        "r32_dedup_guard",
        rep.verdict.clone(),
        rep.verdict.clone(),
        shrink_res,
    )
    .with_minimized_report(rep.clone());

    for bad_head in ["", "   ", "unknown", "1111111", "deadbeef", &"z".repeat(40), &"1".repeat(39)]
    {
        let mut reg_bad = BugRegistry::new("google/zerocopy");
        let out = reg_bad.record_witness(&art, &rep, "main", true, "mir_v1_itree", bad_head, None);
        assert!(matches!(out, DedupRecordOutcome::Provisional { .. }), "bad_head={bad_head:?}");
        assert!(reg_bad.buckets.is_empty());
        assert_eq!(reg_bad.provisional_cases.len(), 1);
    }

    let mut reg_ok = BugRegistry::new("google/zerocopy");
    let bug_id =
        match reg_ok.record_witness(&art, &rep, "main", true, "mir_v1_itree", &head_sha, None) {
            DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
            other => panic!("expected NewBug: {other:?}"),
        };
    for bad_patch in ["", "   ", "unknown", "deadbeef", &"0".repeat(40), &"1".repeat(39)] {
        assert!(
            reg_ok.classify_post_patch_replay(&bug_id, bad_patch, |_| false).is_err(),
            "patch_sha={bad_patch:?} must be rejected"
        );
    }

    let mut reg_fixed = reg_ok.clone();
    assert!(matches!(
        reg_fixed.classify_post_patch_replay(&bug_id, &patch_sha, |_| false).unwrap(),
        ScbReplayVerdict::AllFixed { .. }
    ));

    let valid_kb = reg_fixed.buckets[&bug_id].to_known_bug_record().unwrap();
    let valid_sd = reg_fixed.buckets[&bug_id].to_semantics_detail_entry().unwrap();
    for bad_sha in ["unknown", "1111111", "deadbeef", &"z".repeat(40), &"1".repeat(39)] {
        let mut kb = valid_kb.clone();
        kb.introduced_sha = bad_sha.into();
        assert!(kb.validate().is_err(), "kb introduced_sha={bad_sha:?}");
        let mut kb2 = valid_kb.clone();
        kb2.fixed_sha = bad_sha.into();
        assert!(kb2.validate().is_err(), "kb fixed_sha={bad_sha:?}");

        let mut sd = valid_sd.clone();
        sd.introduced_sha = bad_sha.into();
        assert!(sd.validate().is_err(), "sd introduced_sha={bad_sha:?}");
        let mut sd2 = valid_sd.clone();
        sd2.resolved_by_commit = Some(bad_sha.into());
        assert!(sd2.validate().is_err(), "sd resolved_by_commit={bad_sha:?}");
    }
    let mut kb_zero_fix = valid_kb;
    kb_zero_fix.fixed_sha = "0".repeat(40);
    assert!(kb_zero_fix.validate().is_err());
    let mut sd_zero_fix = valid_sd;
    sd_zero_fix.resolved_by_commit = Some("0".repeat(40));
    assert!(sd_zero_fix.validate().is_err());

    let mut ws_open = reg_ok.clone();
    ws_open.buckets.get_mut(&bug_id).unwrap().fixed_sha = "   ".into();
    assert!(ws_open.to_known_bug_records().is_err());
    assert!(ws_open.to_semantics_detail_entries().is_err());

    let mut bad_dialect = reg_ok.clone();
    bad_dialect.buckets.get_mut(&bug_id).unwrap().dialect_key = "mir_v1_strict".into();
    assert!(bad_dialect.to_known_bug_records().is_err());
    assert!(bad_dialect.to_semantics_detail_entries().is_err());

    let mut bad_scope = reg_ok.clone();
    bad_scope.buckets.get_mut(&bug_id).unwrap().branch_scope = "both".into();
    assert!(bad_scope.to_known_bug_records().is_err());
    assert!(bad_scope.to_semantics_detail_entries().is_err());

    let mut bad_sev = reg_ok.clone();
    bad_sev.buckets.get_mut(&bug_id).unwrap().severity = "P2".into();
    assert!(bad_sev.to_known_bug_records().is_err());
    assert!(bad_sev.to_semantics_detail_entries().is_err());

    let mut bad_pol = reg_ok.clone();
    bad_pol.buckets.get_mut(&bug_id).unwrap().witness_polarity = "spurious_lean_ub".into();
    assert!(bad_pol.to_known_bug_records().is_err());
    assert!(bad_pol.to_semantics_detail_entries().is_err());

    let mut bad_wit_sig = reg_ok;
    {
        let b = bad_wit_sig.buckets.get_mut(&bug_id).unwrap();
        b.severity = "P1".into();
        b.witnesses[0].signature.verdict_kind = "undeclared_ub_fault";
    }
    assert!(bad_wit_sig.to_known_bug_records().is_err());
    assert!(bad_wit_sig.to_semantics_detail_entries().is_err());

    // 4. Codex 4724136977: `load_fuzz_programs_from_dir` rejects out-of-range
    //    `BoundedLoop`, `HelperCall`, and oversized step counts across
    //    `.jsonl` and `.json` seeds.
    let valid_seed_dir = tmp.path().join("valid_seeds");
    fs::create_dir_all(&valid_seed_dir).unwrap();
    let mut valid_loop_prog = meta_prog.clone();
    valid_loop_prog.steps.push(FuzzStep::BoundedLoop { iters: 4, step_imm: 3 });
    fs::write(
        valid_seed_dir.join("ok.jsonl"),
        format!("{}\n", serde_json::to_string(&valid_loop_prog).unwrap()),
    )
    .unwrap();
    assert_eq!(load_fuzz_programs_from_dir(&valid_seed_dir).unwrap().len(), 1);

    let mut loop_huge = meta_prog.clone();
    loop_huge.steps.push(FuzzStep::BoundedLoop { iters: u32::MAX, step_imm: 1 });
    let mut loop_zero = meta_prog.clone();
    loop_zero.steps.push(FuzzStep::BoundedLoop { iters: 0, step_imm: 1 });
    let mut bad_callee = meta_prog.clone();
    bad_callee.steps.push(FuzzStep::HelperCall { callee_idx: 3, bias: 1 });
    let mut too_many_steps = meta_prog;
    too_many_steps.steps = vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }; 33];

    for (idx, (ext, payload)) in [
        ("jsonl", serde_json::to_string(&loop_huge).unwrap()),
        ("jsonl", serde_json::to_string(&loop_zero).unwrap()),
        ("json", serde_json::to_string(&bad_callee).unwrap()),
        ("json", serde_json::to_string(&vec![too_many_steps]).unwrap()),
    ]
    .into_iter()
    .enumerate()
    {
        let dir = tmp.path().join(format!("bad_seeds_{idx}"));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join(format!("seed.{ext}")), payload).unwrap();
        assert!(
            load_fuzz_programs_from_dir(&dir).is_err(),
            "malformed seed {idx} (.{ext}) must be rejected at preflight"
        );
    }

    // 5. `missed_ub` requires a terminating accepting Lean outcome
    //    (`Returned` / `Unwound` / `Aborted`); fuel-exhaustion `Diverged`
    //    is a conservative over-approximation in `classify_pair` and must
    //    stay `Provisional` rather than promoting as a P0 bug.
    let sc_div = ShrinkableCase {
        name: "missed_ub_diverged".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let mut miri_ptr_div = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: dereferencing pointer failed".into(),
        },
    );
    miri_ptr_div.entry_mem_digest = Some("same_digest".into());
    let mut reg_missed_div = BugRegistry::new("google/zerocopy");
    let lean_div_ub = mk_auth("lean", TerminalOutcome::Diverged { fuel: 64 });
    let missed_div_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "fault_ub",
        lean_outcome_kind: "diverged",
        mismatch_category: "missed_ub",
        ref_ub_class: Some(anneal_itree_diff::outcome::UbFaultClass::PointerOrMemoryAccess),
        lean_ub_class: None,
        lean_fault_site_kind: "diverged".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let div_out = reg_missed_div.record_shrinkable_case(
        &sc_div,
        &missed_div_sig,
        None,
        Some(&miri_ptr_div),
        Some(&lean_div_ub),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(matches!(div_out, DedupRecordOutcome::Provisional { .. }), "{div_out:?}");

    let skipped_dual = RustcDualResult {
        o0: mk_auth(
            "rustc-o0",
            TerminalOutcome::CaptureRefused { reason: "skipped_for_ub".into() },
        ),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::CaptureRefused { reason: "skipped_for_ub".into() },
        ),
        parity_ok: true,
        skipped_for_ub: true,
        mismatch_detail: None,
    };
    let skipped_div_sig = ShrinkFailureSignature {
        ref_outcome_kind: "none",
        ref_ub_class: None,
        ..missed_div_sig.clone()
    };
    let skipped_div_out = reg_missed_div.record_shrinkable_case(
        &sc_div,
        &skipped_div_sig,
        Some(&skipped_dual),
        None,
        Some(&lean_div_ub),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(
        matches!(skipped_div_out, DedupRecordOutcome::Provisional { .. }),
        "{skipped_div_out:?}"
    );
    assert!(reg_missed_div.buckets.is_empty());

    let lean_ret_ub = mk_auth(
        "lean",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(7),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
    );
    let missed_ret_sig = ShrinkFailureSignature {
        lean_outcome_kind: "returned",
        lean_fault_site_kind: "returned".into(),
        ..missed_div_sig
    };
    let missed_ret_out = reg_missed_div.record_shrinkable_case(
        &sc_div,
        &missed_ret_sig,
        None,
        Some(&miri_ptr_div),
        Some(&lean_ret_ub),
        "main",
        true,
        "mir_v1_itree",
        &head_sha,
        1,
        true,
    );
    assert!(matches!(missed_ret_out, DedupRecordOutcome::NewBug { .. }), "{missed_ret_out:?}");
}

#[test]
fn r52_codex_run_fuzz_programs_validation_regression() {
    let anneal_root = workspace_anneal_root().expect("locate anneal root");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut cfg =
        DifferentialConfig::for_workspace_with_cache(anneal_root, Some(tmp.path().join("cache")));
    cfg.enable_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare_with_env(cfg, |key| {
        if key == "ANNEAL_MIR_EVAL_BIN" { None } else { std::env::var_os(key) }
    })
    .expect("prepare engine");

    let huge_loop = FuzzProgram {
        seed: 910_001,
        index: 0,
        input_x: 1,
        input_y: 2,
        steps: vec![FuzzStep::BoundedLoop { iters: u32::MAX, step_imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let bad_helper = FuzzProgram {
        seed: 910_002,
        index: 1,
        input_x: 3,
        input_y: 4,
        steps: vec![FuzzStep::HelperCall { callee_idx: 9, bias: 1 }],
        applied_mutators: Vec::new(),
    };

    let rep = engine.run_fuzz_programs(&[huge_loop, bad_helper]);
    assert_eq!(rep.cases.len(), 2, "{rep:?}");
    assert_eq!(rep.counts.tool_error, 2, "{:?}", rep.counts);
    assert_eq!(rep.counts.rustc_o0_o2_parity_checked, 0, "{:?}", rep.counts);
    assert!(rep.has_critical_failures());
    for (idx, expected_id) in [(0, "fuzz_s910001_i000"), (1, "fuzz_s910002_i001")] {
        let case = &rep.cases[idx];
        assert_eq!(case.case_id, expected_id);
        assert!(
            matches!(
                &case.verdict,
                TraceVerdict::ToolError { authority, detail }
                    if authority == "fuzz-program"
                        && detail.contains("invalid caller-supplied FuzzProgram")
            ),
            "unexpected verdict: {:?}",
            case.verdict
        );
        assert!(case.miri.is_none());
        assert!(case.lean.is_none());
    }
}

#[test]
fn r53_codex_spurious_lean_ub_diverged_ref_stays_provisional() {
    let sc = ShrinkableCase {
        name: "spurious_ub_diverged_ref".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let head_sha = "1111111111111111111111111111111111111111";
    let mut lean_ub = mk_auth(
        "lean",
        TerminalOutcome::FaultUb {
            detail: "pointer or memory access undefined: Trusted.MirSemantics.FaultKind.undefined"
                .into(),
        },
    );
    lean_ub.entry_mem_digest = Some("same_digest".into());
    let spurious_sig = ShrinkFailureSignature {
        verdict_kind: "undeclared_ub_fault",
        ref_outcome_kind: "diverged",
        lean_outcome_kind: "fault_ub",
        mismatch_category: "spurious_lean_ub",
        ref_ub_class: None,
        lean_ub_class: Some(anneal_itree_diff::outcome::UbFaultClass::PointerOrMemoryAccess),
        lean_fault_site_kind: "assign_or_mem_deref".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };

    // Fuel exhaustion (`Diverged`) on Miri or rustc reference must stay
    // provisional rather than promoting a spurious_lean_ub P1 bug.
    let mut reg_div = BugRegistry::new("google/zerocopy");
    let miri_div = mk_auth("miri", TerminalOutcome::Diverged { fuel: 64 });
    let miri_div_out = reg_div.record_shrinkable_case(
        &sc,
        &spurious_sig,
        None,
        Some(&miri_div),
        Some(&lean_ub),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    match miri_div_out {
        DedupRecordOutcome::Provisional { reason } => {
            assert!(reason.contains("terminating accepting non-UB reference"), "got {reason}");
        }
        other => panic!("expected Provisional, got {other:?}"),
    }
    assert!(reg_div.buckets.is_empty());

    let rustc_div_dual = RustcDualResult {
        o0: mk_auth("rustc-o0", TerminalOutcome::Diverged { fuel: 64 }),
        o2: mk_auth("rustc-o2", TerminalOutcome::Diverged { fuel: 64 }),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let rustc_div_out = reg_div.record_shrinkable_case(
        &sc,
        &spurious_sig,
        Some(&rustc_div_dual),
        None,
        Some(&lean_ub),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    match rustc_div_out {
        DedupRecordOutcome::Provisional { reason } => {
            assert!(reason.contains("terminating accepting non-UB reference"), "got {reason}");
        }
        other => panic!("expected Provisional, got {other:?}"),
    }
    assert!(reg_div.buckets.is_empty());

    // A terminating accepting reference (`Returned`) still promotes cleanly.
    let mut miri_ret = mk_auth(
        "miri",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(7),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
    );
    miri_ret.entry_mem_digest = Some("same_digest".into());
    let ret_sig = ShrinkFailureSignature { ref_outcome_kind: "returned", ..spurious_sig };
    let ret_out = reg_div.record_shrinkable_case(
        &sc,
        &ret_sig,
        None,
        Some(&miri_ret),
        Some(&lean_ub),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(matches!(ret_out, DedupRecordOutcome::NewBug { .. }), "{ret_out:?}");
    assert_eq!(reg_div.buckets.len(), 1);
}

#[test]
fn r54_codex_dedup_bugid_witness_cap_and_miri_parity() {
    // 1. `metamorphic_duality` fingerprints containing nested compiler/frame
    //    substrings (`rustc_o0_o2`, `called_rustc_o0_vs_o2`, `miri_vs_rustc`,
    //    `metamorphic_caller_frame_law`) must classify as `METADUAL`.
    for embedded in [
        "unsound_accept:metamorphic_duality:called_rustc_o0_vs_o2:called_o0=returned",
        "unsound_accept:metamorphic_duality:rustc_o0_o2+miri_vs_rustc",
        "unsound_accept:metamorphic_duality:metamorphic_caller_frame_law:called_o0=returned",
    ] {
        let fp = CanonicalBugFingerprint::new(
            "main",
            "mir_v1_itree",
            embedded,
            vec!["step:ArithImm".into()],
            "none",
            "returned",
            "0123456789abcdef",
        );
        assert_eq!(fp.short_category_code(), "METADUAL", "class={embedded}");
        assert!(fp.bug_id().starts_with("ITREE-METADUAL-"), "bug_id={}", fp.bug_id());
    }

    let head_sha = "1111111111111111111111111111111111111111";
    let patch_sha = "2222222222222222222222222222222222222222";
    let sc = ShrinkableCase {
        name: "r54_miri_parity_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };

    // 2. Oversized `BugBucket` (> MAX_WITNESSES_PER_BUG) must fail closed on
    //    replay (before invoking `witness_still_fails`) and export.
    let mut cap_reg = BugRegistry::new("google/zerocopy");
    let ret_7 = mk_auth(
        "miri",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(7),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
    );
    let ret_8 = mk_auth(
        "lean",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(8),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
    );
    let val_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let ok_dual = RustcDualResult {
        o0: mk_auth(
            "rustc-o0",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(7),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(7),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let out = cap_reg.record_shrinkable_case(
        &sc,
        &val_sig,
        Some(&ok_dual),
        Some(&ret_7),
        Some(&ret_8),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    let bucket_id = match out {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug, got {other:?}"),
    };
    {
        let bucket = cap_reg.buckets.get_mut(&bucket_id).unwrap();
        let template = bucket.witnesses[0].clone();
        for _ in 0..MAX_WITNESSES_PER_BUG {
            bucket.witnesses.push(template.clone());
        }
        assert_eq!(bucket.witnesses.len(), MAX_WITNESSES_PER_BUG + 1);
    }
    let mut replay_calls = 0usize;
    let replay_err = cap_reg
        .classify_post_patch_replay(&bucket_id, patch_sha, |_| {
            replay_calls += 1;
            true
        })
        .expect_err("oversized bucket must fail before replay");
    assert_eq!(replay_calls, 0, "witness_still_fails must not run on oversized bucket");
    assert!(replay_err.contains("MAX_WITNESSES_PER_BUG"), "err={replay_err}");
    assert!(
        cap_reg
            .to_known_bug_records()
            .expect_err("oversized bucket must fail export")
            .contains("MAX_WITNESSES_PER_BUG")
    );
    assert!(
        cap_reg
            .to_semantics_detail_entries()
            .expect_err("oversized bucket must fail detail export")
            .contains("MAX_WITNESSES_PER_BUG")
    );

    // 3. `miri_vs_rustc` must require non-skipped rustc O0/O2 semantic parity.
    let miri_rustc_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "miri_vs_rustc",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let div_dual = RustcDualResult {
        o0: mk_auth(
            "rustc-o0",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(8),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(9),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 diverged".into()),
    };
    let mut miri_reg = BugRegistry::new("google/zerocopy");
    let div_out = miri_reg.record_shrinkable_case(
        &sc,
        &miri_rustc_sig,
        Some(&div_dual),
        Some(&ret_7),
        Some(&ret_7),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(div_out, DedupRecordOutcome::Provisional { .. }),
        "diverged O0/O2 must keep miri_vs_rustc provisional: {div_out:?}"
    );

    let same_outcome_bad_spine = RustcDualResult {
        o0: mk_auth(
            "rustc-o0",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(8),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(8),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("spine diverged".into()),
    };
    let spine_out = miri_reg.record_shrinkable_case(
        &sc,
        &miri_rustc_sig,
        Some(&same_outcome_bad_spine),
        Some(&ret_7),
        Some(&ret_7),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(spine_out, DedupRecordOutcome::Provisional { .. }),
        "parity_ok=false must keep miri_vs_rustc provisional: {spine_out:?}"
    );

    let par_dual = RustcDualResult {
        o0: mk_auth(
            "rustc-o0",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(8),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        o2: mk_auth(
            "rustc-o2",
            TerminalOutcome::Returned {
                ret: TraceVal::u32(8),
                mem_digest: compute_boundary_mem_digest(&[]),
            },
        ),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let ok_out = miri_reg.record_shrinkable_case(
        &sc,
        &miri_rustc_sig,
        Some(&par_dual),
        Some(&ret_7),
        Some(&ret_7),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    match ok_out {
        DedupRecordOutcome::NewBug { bug_id, .. } => {
            assert!(bug_id.starts_with("ITREE-MIRIRUST-"), "got {bug_id}");
        }
        other => panic!("expected NewBug with matching O0/O2 parity, got {other:?}"),
    }
}

#[test]
fn r55_codex_and_gate2_missed_ub_and_miri_spine_parity() {
    use anneal_itree_diff::outcome::UbFaultClass;

    let head_sha = "5555555555555555555555555555555555555555";
    let mem0 = compute_boundary_mem_digest(&[]);
    let mk_ret_with_spine = |auth: &str, val: u32, callee: Option<&str>| {
        let mut r = mk_auth(
            auth,
            TerminalOutcome::Returned { ret: TraceVal::u32(val), mem_digest: mem0.clone() },
        );
        if let Some(target) = callee {
            r.spine.events = vec![ObservableEvent::CallEnter {
                callee: target.to_string(),
                arg_bytes: Vec::new(),
                arg_reprs: Vec::new(),
            }];
        }
        r
    };

    let sc = ShrinkableCase {
        name: "r55_parity_and_ub".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };

    // 1. Codex 4724923365: `missed_ub` in `record_shrinkable_case` must not
    //    promote merely from `rustc_dual.skipped_for_ub = true` without an
    //    actual `FaultUb` authority result.
    let skipped_dual = RustcDualResult::skipped_for_ub("skipped for UB without Miri");
    let lean_ret = mk_ret_with_spine("lean", 7, None);
    let skipped_missed_ub_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "none",
        lean_outcome_kind: "returned",
        mismatch_category: "missed_ub",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_ub = BugRegistry::new("google/zerocopy");
    let skipped_out = reg_ub.record_shrinkable_case(
        &sc,
        &skipped_missed_ub_sig,
        Some(&skipped_dual),
        None,
        Some(&lean_ret),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(skipped_out, DedupRecordOutcome::Provisional { .. }),
        "skipped_for_ub without FaultUb must remain provisional: {skipped_out:?}"
    );
    assert!(reg_ub.buckets.is_empty());

    // Passing Miri `Returned` while `rustc_dual` was skipped must also remain
    // provisional.
    let mut miri_ok_sig = skipped_missed_ub_sig;
    miri_ok_sig.ref_outcome_kind = "returned";
    let miri_ok_out = reg_ub.record_shrinkable_case(
        &sc,
        &miri_ok_sig,
        Some(&skipped_dual),
        Some(&mk_ret_with_spine("miri", 7, None)),
        Some(&lean_ret),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(miri_ok_out, DedupRecordOutcome::Provisional { .. }),
        "non-UB Miri with skipped_for_ub must remain provisional: {miri_ok_out:?}"
    );
    assert!(reg_ub.buckets.is_empty());

    // Actual Miri `FaultUb` with `rustc_dual.skipped_for_ub = true` still
    // promotes.
    let miri_ub = mk_auth(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "Undefined Behavior: dereferencing pointer failed".into(),
        },
    );
    let mut miri_ub_sig = miri_ok_sig;
    miri_ub_sig.ref_outcome_kind = "fault_ub";
    miri_ub_sig.ref_ub_class = Some(UbFaultClass::PointerOrMemoryAccess);
    let valid_ub_out = reg_ub.record_shrinkable_case(
        &sc,
        &miri_ub_sig,
        Some(&skipped_dual),
        Some(&miri_ub),
        Some(&lean_ret),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    match valid_ub_out {
        DedupRecordOutcome::NewBug { bug_id, .. } => {
            assert!(bug_id.starts_with("ITREE-MISSUB-"), "got {bug_id}");
        }
        other => panic!("expected NewBug with Miri FaultUb evidence, got {other:?}"),
    }

    // 2. `spine_mismatch` (`miri_vs_rustc_o0`) must reject `rustc_dual` without
    //    O0/O2 parity (`parity_ok = true` and matching O0/O2 outcomes).
    let spine_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "spine_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: Some("miri_vs_rustc_o0".into()),
    };
    let miri_sp = mk_ret_with_spine("miri", 7, Some("a"));
    let lean_sp = mk_ret_with_spine("lean", 7, Some("a"));

    let bad_parity_flag = RustcDualResult {
        o0: mk_ret_with_spine("rustc-O0", 7, Some("b")),
        o2: mk_ret_with_spine("rustc-O2", 7, Some("b")),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 spine mismatch".into()),
    };
    let bad_outcome_parity = RustcDualResult {
        o0: mk_ret_with_spine("rustc-O0", 7, Some("b")),
        o2: mk_ret_with_spine("rustc-O2", 9, Some("b")),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };

    let mut reg_sp = BugRegistry::new("google/zerocopy");
    for (label, bad_dual) in
        [("parity_ok=false", &bad_parity_flag), ("o0!=o2 outcome", &bad_outcome_parity)]
    {
        let out = reg_sp.record_shrinkable_case(
            &sc,
            &spine_sig,
            Some(bad_dual),
            Some(&miri_sp),
            Some(&lean_sp),
            "main",
            true,
            "mir_v1_itree",
            head_sha,
            1,
            true,
        );
        assert!(
            matches!(out, DedupRecordOutcome::Provisional { .. }),
            "{label} must keep miri_vs_rustc_o0 spine_mismatch provisional: {out:?}"
        );
        assert!(reg_sp.buckets.is_empty(), "{label} must not insert a bucket");
    }

    let ok_parity = RustcDualResult {
        o0: mk_ret_with_spine("rustc-O0", 7, Some("b")),
        o2: mk_ret_with_spine("rustc-O2", 7, Some("b")),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let ok_sp_out = reg_sp.record_shrinkable_case(
        &sc,
        &spine_sig,
        Some(&ok_parity),
        Some(&miri_sp),
        Some(&lean_sp),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    match ok_sp_out {
        DedupRecordOutcome::NewBug { bug_id, .. } => {
            assert!(bug_id.starts_with("ITREE-SPINEMIS-"), "got {bug_id}");
        }
        other => panic!("expected NewBug with valid O0/O2 parity, got {other:?}"),
    }
}

#[test]
fn codex_parity_file_uri_loop_budget_helper_key_and_witness_dir_guards() {
    let mem0 = compute_boundary_mem_digest(&[]);
    let mk_ret = |auth: &str, val: u32| {
        mk_auth(
            auth,
            TerminalOutcome::Returned { ret: TraceVal::u32(val), mem_digest: mem0.clone() },
        )
    };
    let head_sha = "6666666666666666666666666666666666666666";
    let base_sc = ShrinkableCase {
        name: "guard_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 7,
            multiplier: 3,
            addend: 1,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![ShrinkStep::HelperCall {
            dst_local: 0,
            helper_id: 7,
            block_id: 1,
            bias: 1,
            rhs_local: None,
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };

    // 1. Do not promote `rustc_o0_o2` when Miri establishes `FaultUb`
    //    (`ignore_host_rustc`).
    let miri_ub = mk_auth(
        "miri",
        TerminalOutcome::FaultUb { detail: "Undefined Behavior: null pointer deref".into() },
    );
    let div_dual = RustcDualResult {
        o0: mk_ret("rustc-O0", 7),
        o2: mk_ret("rustc-O2", 9),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 vs O2 outcome diverged".into()),
    };
    let rustc_opt_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "fault_ub",
        lean_outcome_kind: "returned",
        mismatch_category: "rustc_o0_o2",
        ref_ub_class: Some(anneal_itree_diff::outcome::UbFaultClass::PointerOrMemoryAccess),
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_rustc_ub = BugRegistry::new("google/zerocopy");
    let rustc_ub_out = reg_rustc_ub.record_shrinkable_case(
        &base_sc,
        &rustc_opt_sig,
        Some(&div_dual),
        Some(&miri_ub),
        Some(&mk_ret("lean", 7)),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(rustc_ub_out, DedupRecordOutcome::Provisional { .. }),
        "rustc_o0_o2 must stay provisional when Miri reports FaultUb: {rustc_ub_out:?}"
    );
    assert!(reg_rustc_ub.buckets.is_empty());

    // 2. Require prior rustc O0/O2 (and Miri/rustc) parity before promoting
    //    `terminal_outcome_mismatch`.
    let term_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_term = BugRegistry::new("google/zerocopy");
    let bad_rustc_term = reg_term.record_shrinkable_case(
        &base_sc,
        &term_sig,
        Some(&div_dual),
        None,
        Some(&mk_ret("lean", 11)),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(bad_rustc_term, DedupRecordOutcome::Provisional { .. }),
        "diverged O0/O2 must keep terminal_outcome_mismatch provisional: {bad_rustc_term:?}"
    );
    let par_dual_8 = RustcDualResult {
        o0: mk_ret("rustc-O0", 8),
        o2: mk_ret("rustc-O2", 8),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let bad_miri_rustc_term = reg_term.record_shrinkable_case(
        &base_sc,
        &term_sig,
        Some(&par_dual_8),
        Some(&mk_ret("miri", 7)),
        Some(&mk_ret("lean", 11)),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(bad_miri_rustc_term, DedupRecordOutcome::Provisional { .. }),
        "diverged Miri/rustc-O0 must keep terminal_outcome_mismatch provisional: {bad_miri_rustc_term:?}"
    );
    assert!(reg_term.buckets.is_empty());

    // 3. Reject single-slash `file:/...` and non-host SCP-style repo URIs.
    for bad in [
        "file:/tmp/customer/private.git",
        "FILE:/tmp/foo@bar.com/customer/private.git",
        "file:customer/private.git",
        "ssh:/tmp/customer/private.git",
        "work:customer/private.git",
    ] {
        assert!(try_normalize_repo_slug(bad).is_err(), "expected Err for {bad:?}");
        assert_eq!(normalize_repo_slug(bad), "google/zerocopy", "{bad:?}");
    }
    assert_eq!(
        try_normalize_repo_slug("git@github.com:google/zerocopy.git").unwrap(),
        "google/zerocopy"
    );

    // 4. Width-suffixed helper schedule keys (`h7_u32`, `fuzz_helper_9_u64`)
    //    must remap alongside canonical helper renumbering.
    let mut sched = EnvSchedule::default();
    sched.push_callee("h7_u32", EnvAction::ReturnBytes(vec![1, 0, 0, 0]));
    sched.push_callee("fuzz_helper_9_u64", EnvAction::Abort { reason: "orphan".into() });
    let sc_sched = ShrinkableCase { env_schedule: sched, ..base_sc.clone() };
    let renamed = sc_sched.canonical_alpha_renamed();
    assert!(renamed.env_schedule.per_callee.contains_key("h0_u32"), "{:?}", renamed.env_schedule);
    assert!(!renamed.env_schedule.per_callee.contains_key("h7_u32"), "{:?}", renamed.env_schedule);
    assert!(
        renamed.env_schedule.per_callee.contains_key("fuzz_helper_1_u64"),
        "{:?}",
        renamed.env_schedule
    );

    // 5. Huge/fuel-exceeding `BoundedLoop` counts on `ShrinkableCase` must be
    //    rejected before promotion or Lean lowering.
    let huge_loop_sc = ShrinkableCase {
        helpers: Vec::new(),
        steps: vec![ShrinkStep::BoundedLoop {
            block_id: 1,
            iters: u32::MAX,
            induction: Some(anneal_itree_diff::shrink::BoundedLoopInduction {
                dst_local: 0,
                step_mul: 1,
                addend: 1,
            }),
            body: Vec::new(),
        }],
        ..base_sc.clone()
    };
    assert!(!anneal_itree_diff::shrink::all_handles_defined_and_typed(
        &huge_loop_sc.steps,
        &huge_loop_sc.helpers,
    ));
    let nested_exceed_sc = ShrinkableCase {
        helpers: Vec::new(),
        steps: vec![ShrinkStep::BoundedLoop {
            block_id: 1,
            iters: 32,
            induction: None,
            body: vec![ShrinkStep::BoundedLoop {
                block_id: 2,
                iters: 32,
                induction: None,
                body: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
            }],
        }],
        ..base_sc.clone()
    };
    assert!(!anneal_itree_diff::shrink::all_handles_defined_and_typed(
        &nested_exceed_sc.steps,
        &nested_exceed_sc.helpers,
    ));
    let mut reg_loop = BugRegistry::new("google/zerocopy");
    let par_dual_7 = RustcDualResult {
        o0: mk_ret("rustc-O0", 7),
        o2: mk_ret("rustc-O2", 7),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let loop_out = reg_loop.record_shrinkable_case(
        &huge_loop_sc,
        &term_sig,
        Some(&par_dual_7),
        None,
        Some(&mk_ret("lean", 8)),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(matches!(loop_out, DedupRecordOutcome::Provisional { .. }), "{loop_out:?}");

    // 6. Any nonexistent ordinary report path nested under `--witness-dir`
    //    must collide deterministically on first run too.
    let tmp = tempfile::tempdir().unwrap();
    let wdir = tmp.path().join("witnesses");
    let nested_rep = wdir.join("report.json");
    assert!(!nested_rep.exists());
    assert!(
        anneal_itree_diff::validate_distinct_output_paths_with_dirs(
            &[("--json-report", nested_rep.as_path())],
            &[("--witness-dir", wdir.as_path())],
        )
        .is_err()
    );
}

#[test]
fn codex_handle_bounds_caller_frame_ub_parity_and_inconclusive_ref() {
    use anneal_itree_diff::outcome::{CallerFrameLaw, UbFaultClass};

    let h0 = HandleId(0);
    let h1 = HandleId(1);
    let h2 = HandleId(2);
    let head_sha = "7777777777777777777777777777777777777777";
    let mem0 = compute_boundary_mem_digest(&[]);
    let mk_ret = |auth: &str, val: u32| {
        mk_auth(
            auth,
            TerminalOutcome::Returned { ret: TraceVal::u32(val), mem_digest: mem0.clone() },
        )
    };

    // 1. Track handle extent and alignment across `Alloc`, `Borrow`, `SplitAt`,
    //    and `UseHandle`, rejecting OOB or misaligned slices before promotion.
    let oob_split = vec![
        ShrinkStep::Alloc { handle: h0, size: 1, align: 1, local_id: 0 },
        ShrinkStep::SplitAt { left: h1, right: h2, src: h0, mid: 2, len: 4, align: 1 },
    ];
    assert!(!all_handles_defined_and_typed(&oob_split, &[]));

    let oob_use = vec![
        ShrinkStep::Alloc { handle: h0, size: 8, align: 8, local_id: 0 },
        ShrinkStep::UseHandle { handle: h0, offset: 4, len: 8, align: 4, local_id: 0 },
    ];
    assert!(!all_handles_defined_and_typed(&oob_use, &[]));

    let bad_align_use = vec![
        ShrinkStep::Alloc { handle: h0, size: 16, align: 4, local_id: 0 },
        ShrinkStep::UseHandle { handle: h0, offset: 0, len: 8, align: 8, local_id: 0 },
    ];
    assert!(!all_handles_defined_and_typed(&bad_align_use, &[]));

    let bad_mid_align_split = vec![
        ShrinkStep::Alloc { handle: h0, size: 16, align: 8, local_id: 0 },
        ShrinkStep::SplitAt { left: h1, right: h2, src: h0, mid: 4, len: 16, align: 8 },
    ];
    assert!(!all_handles_defined_and_typed(&bad_mid_align_split, &[]));

    let valid_handle_steps = vec![
        ShrinkStep::Alloc { handle: h0, size: 16, align: 8, local_id: 0 },
        ShrinkStep::SplitAt { left: h1, right: h2, src: h0, mid: 8, len: 16, align: 8 },
        ShrinkStep::UseHandle { handle: h2, offset: 0, len: 8, align: 8, local_id: 0 },
    ];
    assert!(all_handles_defined_and_typed(&valid_handle_steps, &[]));

    let sc = ShrinkableCase {
        name: "bounds_case".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };

    // 2. Reject inconclusive Miri outcomes (`Diverged`, `CaptureRefused`) on
    //    `terminal_outcome_mismatch` even when Lean terminates.
    let mut reg_inconc = BugRegistry::new("google/zerocopy");
    let ok_dual = RustcDualResult {
        o0: mk_ret("rustc-O0", 7),
        o2: mk_ret("rustc-O2", 7),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    for (ref_kind, miri_res) in [
        ("diverged", mk_auth("miri", TerminalOutcome::Diverged { fuel: 64 })),
        (
            "capture_refused",
            mk_auth("miri", TerminalOutcome::CaptureRefused { reason: "skip".into() }),
        ),
    ] {
        let sig = ShrinkFailureSignature {
            verdict_kind: "unsound_accept",
            ref_outcome_kind: ref_kind,
            lean_outcome_kind: "returned",
            mismatch_category: "terminal_outcome_mismatch",
            ref_ub_class: None,
            lean_ub_class: None,
            lean_fault_site_kind: "returned".into(),
            metamorphic_relations: Vec::new(),
            metamorphic_leg_kinds: String::new(),
            spine_relation: None,
        };
        let out = reg_inconc.record_shrinkable_case(
            &sc,
            &sig,
            Some(&ok_dual),
            Some(&miri_res),
            Some(&mk_ret("lean", 7)),
            "main",
            true,
            "mir_v1_itree",
            head_sha,
            1,
            true,
        );
        assert!(
            matches!(out, DedupRecordOutcome::Provisional { .. }),
            "inconclusive miri ({ref_kind}) must stay provisional: {out:?}"
        );
    }

    // 3. Require host rustc O0/O2 parity before promoting `missed_ub` or
    //    `ub_cause_mismatch` when Miri is absent.
    let rustc_ub_div = RustcDualResult {
        o0: mk_auth(
            "rustc-O0",
            TerminalOutcome::FaultUb { detail: "Undefined Behavior: null pointer".into() },
        ),
        o2: mk_ret("rustc-O2", 7),
        parity_ok: false,
        skipped_for_ub: false,
        mismatch_detail: Some("O0 faulted while O2 returned".into()),
    };
    let missed_ub_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "fault_ub",
        lean_outcome_kind: "returned",
        mismatch_category: "missed_ub",
        ref_ub_class: Some(UbFaultClass::PointerOrMemoryAccess),
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_ub_div = BugRegistry::new("google/zerocopy");
    let missed_out = reg_ub_div.record_shrinkable_case(
        &sc,
        &missed_ub_sig,
        Some(&rustc_ub_div),
        None,
        Some(&mk_ret("lean", 7)),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(missed_out, DedupRecordOutcome::Provisional { .. }),
        "diverged O0/O2 must keep rustc-backed missed_ub provisional: {missed_out:?}"
    );
    let ub_cause_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "fault_ub",
        lean_outcome_kind: "fault_ub",
        mismatch_category: "ub_cause_mismatch",
        ref_ub_class: Some(UbFaultClass::PointerOrMemoryAccess),
        lean_ub_class: Some(UbFaultClass::UncheckedArithOrDivOverflow),
        lean_fault_site_kind: "fault_ub".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let cause_out = reg_ub_div.record_shrinkable_case(
        &sc,
        &ub_cause_sig,
        Some(&rustc_ub_div),
        None,
        Some(&mk_auth("lean", TerminalOutcome::FaultUb { detail: "division by zero".into() })),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(cause_out, DedupRecordOutcome::Provisional { .. }),
        "diverged O0/O2 must keep rustc-backed ub_cause_mismatch provisional: {cause_out:?}"
    );

    // 4. Reject non-UB accepting authorities with violated `CallerFrameLaw` so
    //    they cannot promote under unrelated failure categories.
    let mut bad_frame_lean = mk_ret("lean", 9);
    bad_frame_lean.caller_frame_law = CallerFrameLaw {
        caller_locals_preserved: false,
        untouched_alloc_bytes_preserved: true,
        padding_mask_respected: true,
        violations: vec!["clobbered caller stack".into()],
    };
    let val_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let frame_out = reg_ub_div.record_shrinkable_case(
        &sc,
        &val_sig,
        Some(&ok_dual),
        Some(&mk_ret("miri", 7)),
        Some(&bad_frame_lean),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(
        matches!(frame_out, DedupRecordOutcome::Provisional { .. }),
        "CallerFrameLaw violation must block terminal_outcome_mismatch promotion: {frame_out:?}"
    );
    assert!(reg_ub_div.buckets.is_empty());
}

#[test]
fn invalid_minimized_witness_bucket_scope_and_caller_frame_symmetry() {
    use anneal_itree_diff::fuzzer::{FuzzArithOp, FuzzProgram, FuzzStep};
    use anneal_itree_diff::shrink::{
        ShrinkBudget, WitnessArtifact, WitnessBundle, shrink_fuzz_program_with_budget,
    };

    let tmp = tempfile::tempdir().expect("tempdir");
    let head_sha = &"a".repeat(40);
    let patch_sha = &"b".repeat(40);
    let ret_val = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let rep_base = mk_ub_case_report(
        "invalid_min_case",
        "Undefined Behavior: Data race detected between read and write",
        ret_val.clone(),
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() },
    );
    let valid_prog = FuzzProgram {
        seed: 0x5901,
        index: 0,
        input_x: 5,
        input_y: 9,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr = shrink_fuzz_program_with_budget(&valid_prog, ShrinkBudget::default(), |p| {
        !p.steps.is_empty()
    });
    assert!(ok_sr.succeeded && ok_sr.is_one_minimal && ok_sr.converged_1_minimal);

    // 1. Out-of-bounds `BoundedLoop`, invalid `HelperCall`, and oversized step
    //    lists on `shrink.minimized` fail closed across bundle rendering,
    //    fingerprinting, `BugRegistry::record_witness`, and bucket export.
    let bad_programs = [
        FuzzProgram {
            steps: vec![FuzzStep::BoundedLoop { iters: u32::MAX, step_imm: 1 }],
            ..valid_prog.clone()
        },
        FuzzProgram {
            steps: vec![FuzzStep::HelperCall { callee_idx: 9, bias: 1 }],
            ..valid_prog.clone()
        },
        FuzzProgram {
            steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }; 33],
            ..valid_prog.clone()
        },
    ];
    let mut reg_bad = BugRegistry::new("google/zerocopy");
    for bad_prog in &bad_programs {
        let mut tampered_sr = ok_sr.clone();
        tampered_sr.original = bad_prog.clone();
        tampered_sr.minimized = bad_prog.clone();
        let bad_wit = WitnessArtifact::from_shrink(
            &rep_base.case_id,
            rep_base.verdict.clone(),
            rep_base.verdict.clone(),
            tampered_sr,
        )
        .with_minimized_report(rep_base.clone());
        assert!(WitnessBundle::try_from_witness(bad_wit.clone(), None).is_err());
        assert!(
            CanonicalBugFingerprint::from_1_minimal_witness(
                &bad_wit,
                &rep_base,
                "main",
                "mir_v1_itree",
                None,
            )
            .is_err()
        );
        let rec_out = reg_bad.record_witness(
            &bad_wit,
            &rep_base,
            "main",
            true,
            "mir_v1_itree",
            head_sha,
            None,
        );
        assert!(
            matches!(rec_out, DedupRecordOutcome::Provisional { .. }),
            "invalid minimized FuzzProgram must stay provisional: {rec_out:?}"
        );
    }
    assert!(reg_bad.buckets.is_empty());
    assert_eq!(reg_bad.provisional_cases.len(), bad_programs.len());

    // Deserialized/tampered bucket witness carrying an invalid `program` also
    // fails closed on export and SCB replay.
    let good_wit = WitnessArtifact::from_shrink(
        &rep_base.case_id,
        rep_base.verdict.clone(),
        rep_base.verdict.clone(),
        ok_sr.clone(),
    )
    .with_minimized_report(rep_base.clone());
    let mut reg_tamper_prog = BugRegistry::new("google/zerocopy");
    let bucket_id_prog = match reg_tamper_prog.record_witness(
        &good_wit,
        &rep_base,
        "unstable_only",
        false,
        "mir_v1_itree",
        head_sha,
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug, got {other:?}"),
    };
    reg_tamper_prog.buckets.get_mut(&bucket_id_prog).unwrap().witnesses[0].program =
        Some(bad_programs[0].clone());
    assert!(reg_tamper_prog.to_known_bug_records().is_err());
    assert!(reg_tamper_prog.to_semantics_detail_entries().is_err());
    assert!(
        reg_tamper_prog.classify_post_patch_replay(&bucket_id_prog, patch_sha, |_| true).is_err()
    );

    // 2. Bucket `branch_scope` and `exposed_on_main` must match the scope
    //    union of its retained witnesses; full-capacity (8-witness) buckets
    //    widen cleanly from `unstable_only` to `both` when hit on `main`.
    let mut reg_scope = BugRegistry::new("google/zerocopy");
    let scope_bug_id = match reg_scope.record_witness(
        &good_wit,
        &rep_base,
        "unstable_only",
        false,
        "mir_v1_itree",
        head_sha,
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug, got {other:?}"),
    };
    let mut falsified = reg_scope.clone();
    {
        let bucket = falsified.buckets.get_mut(&scope_bug_id).unwrap();
        bucket.branch_scope = "main".to_string();
        bucket.primary_fingerprint.branch_scope = "main".to_string();
        bucket.exposed_on_main = true;
    }
    assert!(falsified.to_known_bug_records().is_err());
    assert!(falsified.to_semantics_detail_entries().is_err());
    assert!(falsified.classify_post_patch_replay(&scope_bug_id, patch_sha, |_| true).is_err());

    let mut reg_cap_widen = BugRegistry::new("google/zerocopy");
    let mut widen_bug_id = String::new();
    for k in 1..=9usize {
        let mut p = FuzzProgram {
            seed: 0x5950 + k as u64,
            index: k,
            input_x: 3,
            input_y: 7,
            steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: k as u32 }; k],
            applied_mutators: Vec::new(),
        };
        if k == 9 {
            p.input_x = 11;
        }
        let mut sr = shrink_fuzz_program_with_budget(&p, ShrinkBudget::default(), |cand| {
            cand.steps.len() == k
        });
        sr.succeeded = true;
        sr.is_one_minimal = true;
        sr.converged_1_minimal = true;
        sr.budget_exhausted = false;
        let mut rep_k = rep_base.clone();
        rep_k.case_id = format!("widen_{k}");
        let wit_k = WitnessArtifact::from_shrink(
            &rep_k.case_id,
            rep_k.verdict.clone(),
            rep_k.verdict.clone(),
            sr,
        )
        .with_minimized_report(rep_k.clone());
        let (scope_k, exposed_k) = if k < 9 { ("unstable_only", false) } else { ("main", true) };
        let out = reg_cap_widen.record_witness(
            &wit_k,
            &rep_k,
            scope_k,
            exposed_k,
            "mir_v1_itree",
            &format!("{k:040x}"),
            None,
        );
        if k == 1 {
            match out {
                DedupRecordOutcome::NewBug { bug_id, .. } => widen_bug_id = bug_id,
                other => panic!("expected NewBug at k=1, got {other:?}"),
            }
        }
    }
    let widened_bucket = &reg_cap_widen.buckets[&widen_bug_id];
    assert_eq!(widened_bucket.witnesses.len(), MAX_WITNESSES_PER_BUG);
    assert_eq!(widened_bucket.branch_scope, "both");
    assert!(widened_bucket.exposed_on_main);
    assert!(reg_cap_widen.to_known_bug_records().is_ok());
    assert!(reg_cap_widen.to_semantics_detail_entries().is_ok());

    // 3. Generic vs authority-qualified `metamorphic_caller_frame_law`
    //    symmetry: bare `metamorphic_caller_frame_law` skips in-process claim
    //    and fails closed natively with `cannot be replayed`, whereas
    //    `:called_rustc` passes natively when `CallerFrameLaw` holds.
    let anneal_root = workspace_anneal_root().expect("workspace_anneal_root");
    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, None);
    cfg.enable_miri = false;
    cfg.require_miri = false;
    cfg.enable_lean = false;
    let engine = DifferentialEngine::prepare_with_env(cfg, |key| {
        if key == "ANNEAL_MIR_EVAL_BIN" { None } else { std::env::var_os(key) }
    })
    .expect("prepare engine");

    let meta_prog = FuzzProgram {
        seed: 0x59_99,
        index: 0,
        input_x: 7,
        input_y: 11,
        steps: vec![FuzzStep::HelperCall { callee_idx: 0, bias: 3 }],
        applied_mutators: vec![anneal_itree_diff::fuzzer::MutatorKind::CallBoundaryOutliner],
    };
    for (tag, pin, expect_ok, expect_err) in [
        ("generic_frame_pin", "metamorphic_caller_frame_law", false, "cannot be replayed"),
        ("rustc_frame_pin", "metamorphic_caller_frame_law:called_rustc", true, ""),
    ] {
        let src = anneal_itree_diff::shrink::render_standalone_fuzz_repro_rs_for_relations(
            &meta_prog,
            None,
            tag,
            true,
            &[pin.to_string()],
        );
        let rs_path = tmp.path().join(format!("{tag}.rs"));
        let bin_path = tmp.path().join(format!("{tag}_bin"));
        fs::write(&rs_path, &src).unwrap();
        let comp = Command::new(&engine.rustc.rustc_bin)
            .args(["--edition", "2024"])
            .arg(&rs_path)
            .arg("-o")
            .arg(&bin_path)
            .output()
            .unwrap();
        assert!(comp.status.success(), "{tag}: {}", String::from_utf8_lossy(&comp.stderr));
        let run = Command::new(&bin_path).output().unwrap();
        assert_eq!(
            run.status.success(),
            expect_ok,
            "{tag}: stdout={} stderr={}",
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        );
        let stderr = String::from_utf8_lossy(&run.stderr);
        assert!(
            !stderr.contains("metamorphic called vs source-inlined twin divergence"),
            "{tag}: unexpected divergence panic: {stderr}"
        );
        if !expect_err.is_empty() {
            assert!(stderr.contains(expect_err), "{tag}: {stderr}");
        }
    }
}

#[test]
fn misaligned_pair_miri_spine_parity_retained_rep_and_verdict_authority_guards() {
    use anneal_itree_diff::fuzzer::{FuzzArithOp, FuzzProgram, FuzzStep};
    use anneal_itree_diff::shrink::{
        ShrinkBudget, WitnessArtifact, WitnessBundle, all_handles_defined_and_typed,
        shrink_fuzz_program_with_budget,
    };

    let head_sha = &"a".repeat(40);
    let patch_sha = &"b".repeat(40);
    let ret7 = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let ret9 = TerminalOutcome::Returned {
        ret: TraceVal::u32(9),
        mem_digest: compute_boundary_mem_digest(&[]),
    };

    // 1. Reject misaligned and over-budget `PairOffsetLen` steps before
    //    `ShrinkableCase` lowering or promotion.
    assert!(!all_handles_defined_and_typed(
        &[ShrinkStep::PairOffsetLen { offset: 1, len: 8, align: 8, local_id: 0 }],
        &[],
    ));
    assert!(!all_handles_defined_and_typed(
        &[ShrinkStep::PairOffsetLen { offset: 1 << 20, len: 1, align: 1, local_id: 0 }],
        &[],
    ));
    assert!(all_handles_defined_and_typed(
        &[ShrinkStep::PairOffsetLen { offset: 8, len: 8, align: 8, local_id: 0 }],
        &[],
    ));

    let misaligned_sc = ShrinkableCase {
        name: "misaligned_pair".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::PairOffsetLen { offset: 1, len: 8, align: 8, local_id: 0 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let ok_dual = RustcDualResult {
        o0: mk_auth("rustc-O0", ret7.clone()),
        o2: mk_auth("rustc-O2", ret7.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let term_sig = ShrinkFailureSignature {
        verdict_kind: "unsound_accept",
        ref_outcome_kind: "returned",
        lean_outcome_kind: "returned",
        mismatch_category: "terminal_outcome_mismatch",
        ref_ub_class: None,
        lean_ub_class: None,
        lean_fault_site_kind: "returned".into(),
        metamorphic_relations: Vec::new(),
        metamorphic_leg_kinds: String::new(),
        spine_relation: None,
    };
    let mut reg_misalign = BugRegistry::new("google/zerocopy");
    let mis_out = reg_misalign.record_shrinkable_case(
        &misaligned_sc,
        &term_sig,
        Some(&ok_dual),
        Some(&mk_auth("miri", ret7.clone())),
        Some(&mk_auth("lean", ret9.clone())),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(matches!(mis_out, DedupRecordOutcome::Provisional { .. }), "{mis_out:?}");
    assert!(reg_misalign.buckets.is_empty());

    // 2. Diverging `miri` vs `rustc-O0` observable spines keep downstream
    //    `terminal_outcome_mismatch` promotion `Provisional`.
    let mut miri_div_sp = mk_auth("miri", ret7.clone());
    miri_div_sp.spine.events = vec![ObservableEvent::CallEnter {
        callee: "m_ev".into(),
        arg_bytes: Vec::new(),
        arg_reprs: Vec::new(),
    }];
    let mut o0_div_sp = mk_auth("rustc-O0", ret7.clone());
    o0_div_sp.spine.events = vec![ObservableEvent::CallEnter {
        callee: "r_ev".into(),
        arg_bytes: Vec::new(),
        arg_reprs: Vec::new(),
    }];
    let mut o2_div_sp = o0_div_sp.clone();
    o2_div_sp.authority = "rustc-O2".into();
    let dual_div_sp = RustcDualResult {
        o0: o0_div_sp,
        o2: o2_div_sp,
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let valid_sc = ShrinkableCase {
        name: "miri_sp_parity".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 0, width: IntKind::U32, value: 1, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: Vec::new(),
        steps: vec![ShrinkStep::ArithImm { dst_local: 0, op: FuzzArithOp::Add, imm: 1 }],
        env_schedule: EnvSchedule::default(),
        return_local: 0,
    };
    let mut reg_sp = BugRegistry::new("google/zerocopy");
    let sc_sp_out = reg_sp.record_shrinkable_case(
        &valid_sc,
        &term_sig,
        Some(&dual_div_sp),
        Some(&miri_div_sp),
        Some(&mk_auth("lean", ret9.clone())),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    );
    assert!(matches!(sc_sp_out, DedupRecordOutcome::Provisional { .. }), "{sc_sp_out:?}");

    // 3. Retained witnesses require strictly one authenticated `program` or
    //    `shrinkable_case` matching their canonical sources and skeleton.
    let mut reg_rep_sc = BugRegistry::new("google/zerocopy");
    let sc_bug_id = match reg_rep_sc.record_shrinkable_case(
        &valid_sc,
        &term_sig,
        Some(&ok_dual),
        Some(&mk_auth("miri", ret7.clone())),
        Some(&mk_auth("lean", ret9.clone())),
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        1,
        true,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug, got {other:?}"),
    };
    assert!(reg_rep_sc.to_known_bug_records().is_ok());

    let prog = FuzzProgram {
        seed: 0x6001,
        index: 0,
        input_x: 3,
        input_y: 7,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let ok_sr =
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty());
    let mut real_rep = CaseReport {
        case_id: "verdict_auth_guard".into(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".into() },
        expectation_violation: None,
        rustc_dual: ok_dual.clone(),
        miri: Some(mk_auth("miri", ret7.clone())),
        lean: Some(mk_auth("lean", ret9)),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let prog_wit = WitnessArtifact::from_shrink(
        &real_rep.case_id,
        real_rep.verdict.clone(),
        real_rep.verdict.clone(),
        ok_sr.clone(),
    )
    .with_minimized_report(real_rep.clone());
    let mut reg_rep_prog = BugRegistry::new("google/zerocopy");
    let prog_bug_id = match reg_rep_prog.record_witness(
        &prog_wit,
        &real_rep,
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        None,
    ) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug, got {other:?}"),
    };

    let mut sc_neither = reg_rep_sc.clone();
    sc_neither.buckets.get_mut(&sc_bug_id).unwrap().witnesses[0].shrinkable_case = None;
    let mut sc_both = reg_rep_sc.clone();
    sc_both.buckets.get_mut(&sc_bug_id).unwrap().witnesses[0].program = Some(prog.clone());
    let mut prog_neither = reg_rep_prog.clone();
    prog_neither.buckets.get_mut(&prog_bug_id).unwrap().witnesses[0].program = None;
    let mut prog_both = reg_rep_prog.clone();
    prog_both.buckets.get_mut(&prog_bug_id).unwrap().witnesses[0].shrinkable_case =
        Some(valid_sc.canonical_alpha_renamed());
    let mut prog_bad_rs = reg_rep_prog.clone();
    prog_bad_rs.buckets.get_mut(&prog_bug_id).unwrap().witnesses[0].repro_rust_source =
        "fn forged() {}".into();
    let mut prog_bad_lean = reg_rep_prog;
    prog_bad_lean.buckets.get_mut(&prog_bug_id).unwrap().witnesses[0].mir_lean_source =
        "-- forged lean".into();

    for (label, tampered_reg, bid) in [
        ("sc_neither", &sc_neither, &sc_bug_id),
        ("sc_both", &sc_both, &sc_bug_id),
        ("prog_neither", &prog_neither, &prog_bug_id),
        ("prog_both", &prog_both, &prog_bug_id),
        ("prog_bad_rs", &prog_bad_rs, &prog_bug_id),
        ("prog_bad_lean", &prog_bad_lean, &prog_bug_id),
    ] {
        assert!(tampered_reg.to_known_bug_records().is_err(), "{label}");
        assert!(tampered_reg.to_semantics_detail_entries().is_err(), "{label}");
        let mut r_clone = tampered_reg.clone();
        assert!(r_clone.classify_post_patch_replay(bid, patch_sha, |_| true).is_err(), "{label}");
    }

    // 4. Forged `UnsoundAccept` verdict text cannot promote matching non-UB
    //    authorities as `missed_ub` (`MISSUB`).
    real_rep.lean = Some(mk_auth("lean", ret7.clone()));
    real_rep.verdict =
        TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".into() };
    let forged_wit = WitnessArtifact::from_shrink(
        &real_rep.case_id,
        real_rep.verdict.clone(),
        real_rep.verdict.clone(),
        ok_sr,
    )
    .with_minimized_report(real_rep.clone());
    assert!(WitnessBundle::try_from_witness(forged_wit.clone(), None).is_err());
    assert!(
        CanonicalBugFingerprint::from_1_minimal_witness(
            &forged_wit,
            &real_rep,
            "main",
            "mir_v1_itree",
            None,
        )
        .is_err()
    );
    let mut reg_forged = BugRegistry::new("google/zerocopy");
    let forged_out = reg_forged.record_witness(
        &forged_wit,
        &real_rep,
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        None,
    );
    assert!(matches!(forged_out, DedupRecordOutcome::Provisional { .. }), "{forged_out:?}");
    assert!(reg_forged.buckets.is_empty());

    // Also reject diverging `miri` vs `rustc-O0` spines in `record_witness`.
    let mut miri_sp_rep = real_rep;
    miri_sp_rep.rustc_dual = dual_div_sp;
    miri_sp_rep.miri = Some(miri_div_sp);
    miri_sp_rep.lean = Some(mk_auth(
        "lean",
        TerminalOutcome::Returned {
            ret: TraceVal::u32(9),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
    ));
    miri_sp_rep.verdict = TraceVerdict::UnsoundAccept { detail: "value mismatch".into() };
    let miri_sp_wit = WitnessArtifact::from_shrink(
        &miri_sp_rep.case_id,
        miri_sp_rep.verdict.clone(),
        miri_sp_rep.verdict.clone(),
        shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| !p.steps.is_empty()),
    )
    .with_minimized_report(miri_sp_rep.clone());
    assert!(WitnessBundle::try_from_witness(miri_sp_wit.clone(), None).is_err());
    let rep_sp_out = reg_forged.record_witness(
        &miri_sp_wit,
        &miri_sp_rep,
        "main",
        true,
        "mir_v1_itree",
        head_sha,
        None,
    );
    assert!(matches!(rep_sp_out, DedupRecordOutcome::Provisional { .. }), "{rep_sp_out:?}");
    assert!(reg_forged.buckets.is_empty());
}

#[test]
fn converged_witness_secondary_signature_report_cases_unreachable_schedule_and_fixed_reopen_scope_guards()
 {
    use std::collections::VecDeque;

    let head_sha = "7777777777777777777777777777777777777777";
    let patch_sha = "8888888888888888888888888888888888888888";
    let mem0 = compute_boundary_mem_digest(&[]);
    let mk_auth = |auth: &str, outcome: TerminalOutcome| AuthorityRunResult {
        authority: auth.to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::default(),
        entry_mem_digest: None,
        post_only_mem_digest: false,
        elapsed_ms: 1,
        raw_diagnostics: String::new(),
        tool_error: None,
    };
    let ret_ok = mk_auth(
        "miri",
        TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: mem0.clone() },
    );
    let o0_ok = mk_auth(
        "rustc-O0",
        TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: mem0.clone() },
    );
    let o2_ok = mk_auth(
        "rustc-O2",
        TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: mem0.clone() },
    );
    let lean_bad =
        mk_auth("lean", TerminalOutcome::Returned { ret: TraceVal::u32(99), mem_digest: mem0 });

    let mk_fuzz_case_rep = |case_id: &str| CaseReport {
        case_id: case_id.to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: "terminal outcome value mismatch".into() },
        expectation_violation: None,
        rustc_dual: RustcDualResult {
            o0: o0_ok.clone(),
            o2: o2_ok.clone(),
            parity_ok: true,
            skipped_for_ub: false,
            mismatch_detail: None,
        },
        miri: Some(ret_ok.clone()),
        lean: Some(lean_bad.clone()),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let mk_converged_wit = |prog: FuzzProgram, case_id: &str| {
        let rep = mk_fuzz_case_rep(case_id);
        let mut sr =
            shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| p == &prog);
        sr.succeeded = true;
        sr.is_one_minimal = true;
        sr.converged_1_minimal = true;
        sr.budget_exhausted = false;
        let art =
            WitnessArtifact::from_shrink(case_id, rep.verdict.clone(), rep.verdict.clone(), sr)
                .with_minimized_report(rep.clone());
        (art, rep)
    };

    let prog0 = FuzzProgram {
        seed: 0x6101,
        index: 0,
        input_x: 3,
        input_y: 5,
        steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
        applied_mutators: Vec::new(),
    };
    let prog1 = FuzzProgram {
        seed: 0x6102,
        index: 1,
        input_x: 4,
        input_y: 6,
        steps: vec![
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 },
            FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 2 },
        ],
        applied_mutators: Vec::new(),
    };
    let mut reg = BugRegistry::new("google/zerocopy");
    let (w0, r0) = mk_converged_wit(prog0, "fuzz_s24833_i000");
    let bug_id = match reg.record_witness(&w0, &r0, "main", true, "mir_v1_itree", head_sha, None) {
        DedupRecordOutcome::NewBug { bug_id, .. } => bug_id,
        other => panic!("expected NewBug: {other:?}"),
    };
    let (w1, r1) = mk_converged_wit(prog1, "fuzz_s24834_i001");
    assert!(matches!(
        reg.record_witness(&w1, &r1, "main", true, "mir_v1_itree", head_sha, None),
        DedupRecordOutcome::NewSkeletonAttached { retained_count: 2, .. }
    ));

    // 1. Codex 4725624900: deserialized/mutated witness with
    //    `converged_1_minimal = false` must be rejected by export & SCB replay.
    let mut non_conv_reg = reg.clone();
    non_conv_reg.buckets.get_mut(&bug_id).unwrap().witnesses[1].converged_1_minimal = false;
    let err_conv = non_conv_reg.to_known_bug_records().unwrap_err();
    assert!(err_conv.contains("non-1-minimal"), "unexpected err: {err_conv}");
    assert!(non_conv_reg.to_semantics_detail_entries().is_err());

    // 2. Secondary witness with mutated `signature` category keeping valid
    //    `fingerprint` + regenerated repro/lean sources must fail
    //    `validate_bucket_identity` for all witnesses (not just
    //    `repro_case_id`).
    let mut bad_sec_reg = reg.clone();
    {
        let sec = &mut bad_sec_reg.buckets.get_mut(&bug_id).unwrap().witnesses[1];
        sec.signature.mismatch_category = "rustc_o0_o2";
        let aid = sec.repro_case_id.strip_prefix("repro_").unwrap().to_string();
        let sec_prog = sec.program.as_ref().unwrap().clone();
        sec.mir_lean_source =
            anneal_itree_diff::shrink::render_standalone_mir_lean(&sec_prog, None, &aid);
        sec.repro_rust_source =
            anneal_itree_diff::shrink::render_standalone_fuzz_repro_rs_for_relations(
                &sec_prog,
                None,
                &aid,
                false,
                &["called_rustc_o0_vs_o2".to_string()],
            );
    }
    let err_sec = bad_sec_reg.to_known_bug_records().unwrap_err();
    assert!(err_sec.contains("signature contradicts verdict_class"), "unexpected err: {err_sec}");
    assert!(bad_sec_reg.to_semantics_detail_entries().is_err());

    // 3. Codex 4725624911: inconsistent `DifferentialReport` counters (empty
    //    `cases` with `counts.total > 0`, or `ToolError` case with
    //    `counts.tool_error = 0`) must fail accounting rather than emitting
    //    `verified_at_head`.
    let ctx_verified = TelemetryContext {
        repo: "google/zerocopy".to_string(),
        branch: "main".to_string(),
        branch_scope: "main".to_string(),
        exposed_on_main: true,
        commit_sha: head_sha.to_string(),
        commit_unix_ts: 1_700_000_000,
        environment_profile: "unit".to_string(),
        source_url: String::new(),
        profile_v2: false,
        build_freshness_override: None,
        build_exit_code_override: None,
        head_provenance_verified: true,
        discovered_head_sha: Some(head_sha.to_string()),
    };
    let mut forged_empty = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        Vec::new(),
        Vec::new(),
    );
    forged_empty.counts.total = 1;
    forged_empty.counts.agree = 1;
    assert!(KnownBugsExport::from_report_and_registry(&forged_empty, &reg, &ctx_verified).is_err());
    assert!(
        SemanticDetailRecord::from_report_and_registry(&forged_empty, &reg, &ctx_verified).is_err()
    );

    let mut tool_err_rep = r0.clone();
    tool_err_rep.verdict =
        TraceVerdict::ToolError { authority: "lean".into(), detail: "timed out".into() };
    let mut forged_err = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![tool_err_rep],
        Vec::new(),
    );
    forged_err.counts.tool_error = 0;
    forged_err.counts.agree = 1;
    assert!(KnownBugsExport::from_report_and_registry(&forged_err, &reg, &ctx_verified).is_err());
    assert!(
        SemanticDetailRecord::from_report_and_registry(&forged_err, &reg, &ctx_verified).is_err()
    );

    // 4. Codex 4725624915: `ShrinkableCase` with non-empty schedule queues for
    //    unreachable callees (`bogus_ext`, unused helper `h0`, decoy-only or
    //    untaken static-arm calls) must be rejected before Lean rendering,
    //    `record_shrinkable_case` promotion, and bucket export.
    let base_sc = ShrinkableCase {
        name: "sched_reach".into(),
        scalar_width: IntKind::U32,
        inputs: vec![ShrinkInput { local_id: 1, width: IntKind::U32, value: 3, align_hint: None }],
        struct_fields: Vec::new(),
        slice_len: None,
        slice_align: 1,
        helpers: vec![ShrinkHelper {
            helper_id: 0,
            multiplier: 2,
            addend: 1,
            op: ShrinkHelperOp::AffineMulAdd,
        }],
        steps: vec![ShrinkStep::IfFalseDecoy {
            block_id: 0,
            body: vec![ShrinkStep::HelperCall {
                dst_local: 1,
                helper_id: 0,
                block_id: 1,
                bias: 1,
                rhs_local: None,
            }],
        }],
        env_schedule: EnvSchedule::default(),
        return_local: 1,
    };
    let val_sig = ShrinkFailureSignature::from_case_report(&r0).unwrap();
    for bad_callee in ["h0", "bogus_ext"] {
        let mut sc_bad = base_sc.clone();
        sc_bad.env_schedule.push_callee(bad_callee, EnvAction::Abort { reason: "orphan".into() });
        let lean_err =
            anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&sc_bad, "orphan")
                .unwrap_err();
        assert!(lean_err.contains("unreachable callee"), "{bad_callee}: {lean_err}");
        let mut reg_orphan = BugRegistry::new("google/zerocopy");
        let rec_out = reg_orphan.record_shrinkable_case(
            &sc_bad,
            &val_sig,
            Some(&r0.rustc_dual),
            r0.miri.as_ref(),
            r0.lean.as_ref(),
            "main",
            true,
            "mir_v1_itree",
            head_sha,
            1,
            true,
        );
        assert!(
            matches!(rec_out, DedupRecordOutcome::Provisional { .. }),
            "{bad_callee}: {rec_out:?}"
        );
        assert!(reg_orphan.buckets.is_empty());
    }
    // Untaken static `BranchMix` arm also makes contained calls unreachable.
    let mut sc_untaken = base_sc.clone();
    sc_untaken.steps = vec![ShrinkStep::BranchMix {
        block_id: 0,
        cond_local: 1,
        taken_then: true,
        dynamic_even_cond: false,
        then_steps: Vec::new(),
        else_steps: vec![ShrinkStep::UnwindProbe {
            callee: "dead_unwind".into(),
            dst_local: 1,
            trigger_unwind: false,
            block_id: 1,
        }],
    }];
    sc_untaken.env_schedule.push_callee("dead_unwind", EnvAction::ReturnBytes(vec![1, 0, 0, 0]));
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&sc_untaken, "dead")
            .unwrap_err()
            .contains("unreachable callee")
    );
    // Empty queue for uncalled name stays harmless.
    let mut sc_empty_q = base_sc;
    sc_empty_q.env_schedule.per_callee.insert("unused_empty".into(), VecDeque::new());
    assert!(
        anneal_itree_diff::shrink::render_standalone_shrinkable_mir_lean(&sc_empty_q, "emptyq")
            .is_ok()
    );

    // 5. Reopening a full K=8 Fixed bucket containing 7 `unstable_only` + 1
    //    `main` witness with a 9th `unstable_only` witness must preserve
    //    `"both"`/`exposed_on_main = true` and pass bucket identity validation
    //    (and symmetrically for 7 `main` + 1 `unstable_only` + 9th `main`).
    for (majority_scope, majority_exposed, minority_scope, minority_exposed) in
        [("unstable_only", false, "main", true), ("main", true, "unstable_only", false)]
    {
        let mut reg_k8 = BugRegistry::new("google/zerocopy");
        let mut bid = String::new();
        for idx in 0..8usize {
            let p = FuzzProgram {
                seed: 0x6200 + idx as u64,
                index: idx,
                input_x: 3,
                input_y: 5,
                steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }; idx + 1],
                applied_mutators: Vec::new(),
            };
            let (w, r) = mk_converged_wit(p, &format!("k8_{majority_scope}_{idx}"));
            let (bscope, bexp) = if idx < 7 {
                (majority_scope, majority_exposed)
            } else {
                (minority_scope, minority_exposed)
            };
            match reg_k8.record_witness(&w, &r, bscope, bexp, "mir_v1_itree", head_sha, None) {
                DedupRecordOutcome::NewBug { bug_id, .. } => bid = bug_id,
                DedupRecordOutcome::NewSkeletonAttached { .. } => {}
                other => panic!("idx={idx}: {other:?}"),
            }
        }
        assert_eq!(reg_k8.buckets[&bid].branch_scope, "both");
        assert!(reg_k8.buckets[&bid].exposed_on_main);
        assert_eq!(reg_k8.buckets[&bid].witnesses.len(), 8);

        let scb =
            reg_k8.classify_post_patch_replay(&bid, patch_sha, |_| false).expect("SCB AllFixed");
        assert!(matches!(scb, ScbReplayVerdict::AllFixed { replayed_count: 8, .. }), "{scb:?}");

        let p9 = FuzzProgram {
            seed: 0x6209,
            index: 9,
            input_x: 3,
            input_y: 5,
            steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }; 9],
            applied_mutators: Vec::new(),
        };
        let (w9, r9) = mk_converged_wit(p9, &format!("k8_{majority_scope}_9"));
        let reopen_out = reg_k8.record_witness(
            &w9,
            &r9,
            majority_scope,
            majority_exposed,
            "mir_v1_itree",
            patch_sha,
            None,
        );
        assert!(
            matches!(reopen_out, DedupRecordOutcome::NewSkeletonAttached { retained_count: 8, .. }),
            "expected reopened attachment: {reopen_out:?}"
        );
        assert_eq!(reg_k8.buckets[&bid].status, BugStatus::Open);
        assert_eq!(reg_k8.buckets[&bid].branch_scope, "both");
        assert!(reg_k8.buckets[&bid].exposed_on_main);
        assert!(reg_k8.to_known_bug_records().is_ok());
        assert!(reg_k8.to_semantics_detail_entries().is_ok());
    }
}
