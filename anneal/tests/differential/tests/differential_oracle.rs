// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for `anneal-differential-tests`: exact Profile v1
//! manifest contract verification and live multi-leg Miri / Lean `StepCore` /
//! kernel `WP` / AST-mutant differential runs.

use std::path::PathBuf;

use anneal_differential_tests::{
    RunOptions,
    corpus::load_manifest,
    default_manifest_path,
    fuzz::{FuzzOptions, FuzzSession, report_has_any_tool_error, run_fuzz_campaign},
    r#gen::{
        GenArithOp, GenCategory, GenCmpOp, GenEnumKind, GenExpr, GenLocal, GenParam, GenProgram,
        GenStmt, GenSysrootNumOp, GenType,
    },
    run_differential_suite,
    shrink::{ShrinkConfig, ShrinkOutcome, shrink_program},
    verdict::{
        Expectation, IntKind, MirValue, ObservedOutcome, OracleAgreementClass, RustcCheckStatus,
        Verdict, evaluate_fuzz_case,
    },
};

#[test]
fn profile_v1_manifest_loads_without_waivers_or_escapes() {
    let manifest = default_manifest_path().expect("resolve default profile_v1 manifest");
    let loaded = load_manifest(&manifest).expect("load profile_v1 manifest");
    assert_eq!(loaded.mir_dialect, "profile_v1");
    assert_eq!(loaded.cases.len(), 39);
    assert_eq!(loaded.cases.iter().filter(|c| c.expected == Expectation::Pass).count(), 29);
    assert_eq!(loaded.cases.iter().filter(|c| c.expected == Expectation::Ub).count(), 8);
    assert_eq!(
        loaded.cases.iter().filter(|c| c.expected == Expectation::UnsupportedControl).count(),
        2
    );
}

fn isolated_capture_bin() -> (tempfile::TempDir, PathBuf) {
    let src = std::path::Path::new(env!("CARGO_BIN_EXE_anneal-diff-capture-test-bin"));
    let dir = tempfile::Builder::new()
        .prefix("anneal-diff-capture-iso-")
        .tempdir()
        .expect("create single-link capture tempdir");
    let canon_dir = std::fs::canonicalize(dir.path()).expect("canonicalize capture tempdir");
    let dest = canon_dir.join("anneal-diff-capture-test-bin");
    std::fs::copy(src, &dest).expect("copy capture test binary to single-link path");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(&dest, std::fs::Permissions::from_mode(0o755))
            .expect("chmod isolated capture binary");
    }
    (dir, dest)
}

#[test]
fn profile_v1_differential_oracle_and_mutants_pass_live() {
    let manifest = default_manifest_path().expect("resolve default profile_v1 manifest");
    let (_cap_dir, capture_bin) = isolated_capture_bin();
    let report = run_differential_suite(&RunOptions {
        manifest_path: manifest.clone(),
        capture_bin: Some(capture_bin),
        mir_eval_bin: None,
        self_check_oracle: true,
        cache_root: None,
    })
    .expect("execute Stage-1 differential oracle suite");

    assert!(report.is_passing(), "differential oracle failed:\n{report:#?}");
    assert_eq!(report.capture_bin_source, "explicit");
    assert_eq!(report.capture_bin_sha256.len(), 64);
    assert!(report.capture_bin_sha256.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')));
    assert!(!report.prebuilt_overlay.is_empty());

    assert_eq!(report.metrics.compared_count, 39);
    assert_eq!(report.metrics.pass_agreed_count, 29);
    assert_eq!(report.metrics.ub_agreed_count, 8);
    assert_eq!(report.metrics.conservative_unsupported_count, 2);
    assert_eq!(report.metrics.kernel_checked_pass_count, 10);
    assert_eq!(report.metrics.kernel_checked_ub_count, 5);
    assert_eq!(report.metrics.unsound_missed_fault_count, 0);
    assert_eq!(report.metrics.value_mismatch_count, 0);
    assert_eq!(report.metrics.unexpected_conservative_count, 0);
    assert_eq!(report.metrics.leg_divergence_count, 0);
    assert_eq!(report.red_flags_passed, 7);

    let enum_seven = report
        .cases
        .iter()
        .find(|c| c.id == "enum_signed_seven")
        .expect("missing enum_signed_seven");
    assert_eq!(
        enum_seven.verdict,
        Verdict::AgreeValue { value: MirValue::Int { int_kind: IntKind::I32, bits: 70 } }
    );

    let enum_solo = report
        .cases
        .iter()
        .find(|c| c.id == "enum_repr_u8_singleton")
        .expect("missing enum_repr_u8_singleton");
    assert_eq!(
        enum_solo.verdict,
        Verdict::AgreeValue { value: MirValue::Int { int_kind: IntKind::U8, bits: 42 } }
    );

    let move_reinit = report
        .cases
        .iter()
        .find(|c| c.id == "cf_move_then_reinit")
        .expect("missing cf_move_then_reinit");
    assert_eq!(
        move_reinit.verdict,
        Verdict::AgreeValue { value: MirValue::Int { int_kind: IntKind::I16, bits: 5 } }
    );
    assert!(report.red_flag_error.is_none(), "expected captured Use(Move)+reinit check to pass");

    let pass_abort_benign = report
        .cases
        .iter()
        .find(|c| c.id == "pass_abort_control_benign")
        .expect("missing pass_abort_control_benign");
    assert_eq!(
        pass_abort_benign.verdict,
        Verdict::AgreeValue { value: MirValue::Int { int_kind: IntKind::U32, bits: 2 } }
    );

    let unsup_abort = report
        .cases
        .iter()
        .find(|c| c.id == "unsup_diverging_abort_call")
        .expect("missing unsup_diverging_abort_call");
    assert!(matches!(unsup_abort.miri, ObservedOutcome::AbnormalAbort { .. }));
    assert!(matches!(unsup_abort.lean, ObservedOutcome::Unsupported { .. }));
    assert!(matches!(unsup_abort.verdict, Verdict::SoundConservativeAbstraction { .. }));

    let unsup_hint = report
        .cases
        .iter()
        .find(|c| c.id == "unsup_hint_unreachable_call")
        .expect("missing unsup_hint_unreachable_call");
    assert!(matches!(unsup_hint.miri, ObservedOutcome::UndefinedBehavior { .. }));
    assert!(matches!(unsup_hint.lean, ObservedOutcome::Unsupported { .. }));
    assert!(matches!(unsup_hint.verdict, Verdict::SoundConservativeAbstraction { .. }));

    let mutants = report.mutant_check.expect("mutant check requested");
    assert_eq!(mutants.total_mutants, 5);
    assert_eq!(mutants.killed_mutants, 5);
    assert_eq!(mutants.synthetic_lean_probes.len(), 1);
    assert!(mutants.synthetic_lean_probes[0].passed);
}

#[test]
fn semantic_regressions_preserve_structured_verdicts_and_json() {
    // Verify that semantic regressions on single-block WP-eligible functions
    // still produce structured `DifferentialReport` verdicts and valid JSON
    // rather than aborting `Probe.lean` elaboration on failed `rfl` theorems.
    let manifest = default_manifest_path().expect("resolve default profile_v1 manifest");
    let reg_dir = tempfile::tempdir().expect("create regression manifest dir");
    let src_dir = reg_dir.path().join("src");
    std::fs::create_dir_all(&src_dir).expect("create regression src dir");
    let orig_arith = manifest.parent().expect("manifest parent").join("src/arith_pass.rs");
    std::fs::copy(&orig_arith, src_dir.join("arith_pass.rs")).expect("copy arith_pass.rs");
    let reg_manifest = reg_dir.path().join("manifest.toml");
    std::fs::write(
        &reg_manifest,
        r#"schema_version = 1
mir_dialect = "profile_v1"

[[case]]
id = "reg_ok"
source = "src/arith_pass.rs"
function = "u32_wrapping_add"
category = "arith"
expected = "pass"
args = [{ kind = "u32", value = "1" }, { kind = "u32", value = "3" }]
expected_return = { kind = "u32", value = "4" }
fuel = 16

[[case]]
id = "reg_val_mismatch"
source = "src/arith_pass.rs"
function = "u32_wrapping_add"
category = "arith"
expected = "pass"
args = [{ kind = "u32", value = "1" }, { kind = "u32", value = "3" }]
expected_return = { kind = "u32", value = "999" }
fuel = 16

[[case]]
id = "reg_ub_missed"
source = "src/arith_pass.rs"
function = "u32_wrapping_add"
category = "ub"
expected = "ub"
miri_ub_contains = "overflow"
args = [{ kind = "u32", value = "1" }, { kind = "u32", value = "3" }]
fuel = 16
"#,
    )
    .expect("write regression manifest");

    let (_cap_dir, capture_bin) = isolated_capture_bin();
    let reg_report = run_differential_suite(&RunOptions {
        manifest_path: reg_manifest,
        capture_bin: Some(capture_bin),
        mir_eval_bin: None,
        self_check_oracle: false,
        cache_root: None,
    })
    .expect("regression manifest must return structured report rather than aborting");

    assert!(!reg_report.is_passing());
    assert_eq!(reg_report.metrics.compared_count, 3);
    assert_eq!(reg_report.metrics.kernel_checked_pass_count, 1);
    assert_eq!(reg_report.metrics.value_mismatch_count, 1);
    assert_eq!(reg_report.metrics.leg_divergence_count, 1);
    let reg_json: serde_json::Value = serde_json::from_str(
        &serde_json::to_string(&reg_report).expect("serialize regression report"),
    )
    .expect("parse regression JSON");
    assert_eq!(reg_json["schema"], "anneal-differential-run/v1");
}

#[test]
fn miri_harness_keeps_auth_token_secret_from_cfg_miri_fixtures() {
    use anneal_differential_tests::{
        corpus::LitmusCase, find_anneal_root, miri_runner::MiriSession, resolve_cache_root,
        resolve_toolchain_for_suite,
    };

    let manifest = default_manifest_path().expect("resolve default profile_v1 manifest");
    let anneal_root = find_anneal_root(&manifest).expect("resolve anneal root");
    let (_cap_dir, capture_bin) = isolated_capture_bin();
    let prepared_tools = resolve_toolchain_for_suite(Some(&capture_bin), |k| std::env::var_os(k))
        .expect("resolve toolchain");
    let tools = &prepared_tools.tools;
    let (cache_root, _cache_guard) =
        resolve_cache_root(&anneal_root, None).expect("resolve differential cache root");
    let miri = MiriSession::prepare(&tools.sysroot, &cache_root).expect("prepare Miri");

    let dir = tempfile::tempdir().expect("create adversarial Miri fixture dir");
    let src_path = dir.path().join("adversarial.rs");
    std::fs::write(
        &src_path,
        r#"
#[cfg(miri)]
fn find_32_hex_token(text: &str) -> Option<String> {
    let bytes = text.as_bytes();
    for win in bytes.windows(32) {
        if win.iter().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {
            if let Ok(s) = core::str::from_utf8(win) {
                return Some(s.to_owned());
            }
        }
    }
    None
}

#[cfg(miri)]
#[track_caller]
pub fn leak_probe() -> u32 {
    let _bt = std::backtrace::Backtrace::force_capture();
    let f = file!();
    let caller = core::panic::Location::caller().file();
    let mut saw_secret = f.contains("sec_") || caller.contains("sec_") || f.contains("harness");
    if caller.contains("harness")
        || find_32_hex_token(f).is_some()
        || find_32_hex_token(caller).is_some()
    {
        saw_secret = true;
    }
    for arg in std::env::args().take(1) {
        if arg.contains("sec_") || arg.contains('_') || find_32_hex_token(&arg).is_some() {
            saw_secret = true;
        }
    }
    if saw_secret { 99 } else { 7 }
}

#[cfg(not(miri))]
pub fn leak_probe() -> u32 { 7 }

#[cfg(miri)]
pub fn spoof_ret_and_exit0() -> u32 {
    let f = file!();
    let tok = f.rsplit('_').next().unwrap_or("").trim_end_matches(".rs");
    println!("ANNEAL_MIRI_RET:{tok}=INT:u32:42");
    println!("ANNEAL_MIRI_RET=INT:u32:42");
    std::process::exit(0);
}

#[cfg(not(miri))]
pub fn spoof_ret_and_exit0() -> u32 { 7 }

#[cfg(miri)]
pub fn spoof_backtrace_token_and_exit0() -> u32 {
    let _bt = std::backtrace::Backtrace::force_capture();
    for s in [file!(), core::panic::Location::caller().file()] {
        if let Some(tok) = find_32_hex_token(s) {
            println!("ANNEAL_MIRI_RET:{tok}=INT:u32:42");
        }
    }
    for arg in std::env::args() {
        if let Some(tok) = find_32_hex_token(&arg) {
            println!("ANNEAL_MIRI_RET:{tok}=INT:u32:42");
        }
    }
    println!("ANNEAL_MIRI_RET=INT:u32:42");
    std::process::exit(0);
}

#[cfg(not(miri))]
pub fn spoof_backtrace_token_and_exit0() -> u32 { 7 }

#[cfg(miri)]
pub fn spoof_json_ub_and_exit1() -> u32 {
    eprintln!(
        "{{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{{\"file_name\":\"/tmp/h/harness.rs\"}}],\"children\":[{{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}}],\"rendered\":\"...\"}}"
    );
    eprintln!(
        "{{\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}}"
    );
    std::process::exit(1);
}

#[cfg(not(miri))]
pub fn spoof_json_ub_and_exit1() -> u32 { 7 }

#[cfg(miri)]
pub fn spoof_plain_ub_and_exit1() -> u32 {
    eprintln!("error: Undefined Behavior: forged");
    std::process::exit(1);
}

#[cfg(not(miri))]
pub fn spoof_plain_ub_and_exit1() -> u32 { 7 }
"#,
    )
    .expect("write adversarial fixture");

    let mk_case = |id: &str, func: &str| LitmusCase {
        id: id.to_owned(),
        source_rel: PathBuf::from("adversarial.rs"),
        source_abs: src_path.clone(),
        function: func.to_owned(),
        category: "security".to_owned(),
        expected: Expectation::Pass,
        miri_ub_contains: None,
        expected_miri: None,
        args: vec![],
        expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
        fuel: 64,
    };
    let cases = vec![
        mk_case("adv_leak_probe", "leak_probe"),
        mk_case("adv_spoof_ret_exit0", "spoof_ret_and_exit0"),
        mk_case("adv_spoof_bt_exit0", "spoof_backtrace_token_and_exit0"),
        mk_case("adv_spoof_json_ub_exit1", "spoof_json_ub_and_exit1"),
        mk_case("adv_spoof_plain_ub_exit1", "spoof_plain_ub_and_exit1"),
    ];
    let outcomes = miri.run_cases(&cases).expect("execute adversarial Miri fixtures");
    assert_eq!(
        outcomes["adv_leak_probe"],
        ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } },
        "fixture must not observe harness token via file!(), Location::caller(), args()[0], or Backtrace"
    );
    for forged_id in [
        "adv_spoof_ret_exit0",
        "adv_spoof_bt_exit0",
        "adv_spoof_json_ub_exit1",
        "adv_spoof_plain_ub_exit1",
    ] {
        assert!(
            matches!(outcomes[forged_id], ObservedOutcome::ToolError { .. }),
            "expected fail-closed ToolError for {forged_id}, got {:?}",
            outcomes[forged_id]
        );
    }
}

#[test]
fn stage2_fuzz_campaign_admitted_subset_and_ub_probes_pass_live() {
    // Use seed `20261125` (`16` cases) distinct from
    // `check_mir_differential.py`'s `20261124` (`32` cases) so
    // `cargo test --workspace` and the CI sensor exercise complementary
    // deterministic campaigns.
    let (_cap_dir, capture_bin) = isolated_capture_bin();
    let report = run_fuzz_campaign(&FuzzOptions {
        seed: 20_261_125,
        cases: 16,
        max_stmts: 6,
        ub_ratio: 0.20,
        shrink: true,
        run_rustc: true,
        capture_bin: Some(capture_bin),
        mir_eval_bin: None,
        mir_eval_manifest: None,
        cache_root: None,
        min_admission_rate: 0.90,
        fuel: 1_500,
        shrink_config: ShrinkConfig::default(),
    })
    .expect("execute Stage-2 16-case differential fuzz campaign");

    assert!(report.is_passing(), "Stage-2 fuzz campaign failed:\n{report:#?}");
    assert_eq!(report.schema, "anneal-differential-fuzz/v1");
    assert_eq!(report.fuel, 1_500);
    for case in &report.cases {
        assert!((1..=report.fuel).contains(&case.fuel), "invalid case fuel: {}", case.fuel);
        if matches!(
            case.evaluation.disclosed_gap,
            Some(anneal_differential_tests::verdict::DisclosedGapKind::FuelExhausted)
        ) {
            assert_eq!(case.fuel, report.fuel.min(40));
        }
    }
    assert_eq!(report.metrics.total_cases, 16);
    assert_eq!(report.metrics.unsound_accept_count, 0);
    assert_eq!(report.metrics.authority_disagreement_count, 0);
    assert_eq!(report.metrics.spurious_lean_ub_count, 0);
    assert_eq!(report.metrics.admitted_authority_ub_count, 0);
    assert!(
        report.metrics.admission_rate >= 0.90,
        "admission rate {:.2}% fell below 90%",
        report.metrics.admission_rate * 100.0
    );
    assert!(report.metrics.bi_fault_equiv_count > 0);
    assert!(report.metrics.ub_probes_agreed_count > 0);
    assert_eq!(report.metrics.ub_probes_agreed_count, report.metrics.targeted_ub_probes);
    assert!(report.metrics.rustc_agreed_count > 0);
    assert!(report.metrics.rustc_ignored_ub_count > 0);
    assert_eq!(report.metrics.rustc_disagreement_count, 0);
    assert!(
        report.metrics.move_reinit_exercised_count > 0,
        "expected captured fuzz bodies to exercise real non-Copy Operand::Move + reinit"
    );
    assert!(
        report.cases.iter().any(|c| c.category == GenCategory::ScopeControl
            && c.evaluation.agreement
                == OracleAgreementClass::ConservativeOverApproxForwardSimOnly),
        "expected ScopeControl conservative over-approximation cases"
    );
    for c in &report.cases {
        if c.capture_rejected.is_none() {
            let cb = c
                .capture_body
                .as_ref()
                .unwrap_or_else(|| panic!("case {} missing capture_body", c.case_id));
            assert_eq!(cb.arg_count, c.args.len());
            assert!(!cb.blocks.is_empty());
            let le = c
                .leg_evidence
                .as_ref()
                .unwrap_or_else(|| panic!("case {} missing leg_evidence", c.case_id));
            assert!(le.lean_probe_line.as_deref().is_some_and(|l| l.contains(&c.case_id)));
            assert!(le.miri_evidence.as_deref().is_some_and(|l| l.contains(&c.case_id)));
            if matches!(c.miri, ObservedOutcome::UndefinedBehavior { .. }) {
                assert!(
                    c.rustc.is_none(),
                    "Miri-established UB case {} must never run compiled rustc",
                    c.case_id
                );
                assert!(
                    le.rustc_evidence.is_none(),
                    "Miri-established UB case {} must not carry rustc_evidence",
                    c.case_id
                );
                assert_eq!(c.evaluation.rustc_status, RustcCheckStatus::IgnoredDueToMiriUb);
            } else if !matches!(c.rustc, Some(ObservedOutcome::ToolError { .. })) {
                assert!(le.rustc_evidence.as_deref().is_some_and(|l| l.contains(&c.case_id)));
            }
        }
    }
}

#[test]
fn stage2_shrinker_live_broken_oracle_reaches_1_minimal() {
    let (_cap_dir, capture_bin) = isolated_capture_bin();
    let poisoned_cache = tempfile::tempdir().expect("create poisoned fuzz cache fixture");
    let forged_miri = poisoned_cache.path().join("miri-sysroot-deadbeef-0000000000000000");
    std::fs::create_dir_all(forged_miri.join("lib/rustlib")).unwrap();
    std::fs::write(forged_miri.join(".anneal-miri-ready"), "{}").unwrap();
    let session = FuzzSession::prepare(&FuzzOptions {
        capture_bin: Some(capture_bin),
        cache_root: Some(poisoned_cache.path().to_path_buf()),
        run_rustc: false,
        ..FuzzOptions::default()
    })
    .expect("prepare live FuzzSession for shrinker self-test");
    assert_eq!(
        std::fs::read_dir(poisoned_cache.path()).unwrap().count(),
        1,
        "FuzzSession must never populate or rely on writable --cache-root"
    );

    // Verify `exercised_move_reinit` tracks only the concrete executed path:
    // an untaken `if cond` branch containing `MoveReinit` must report `false`,
    // whereas the identical program with `cond = true` must report `true`.
    let make_branch_move_probe = |id: &str, take_branch: bool| GenProgram {
        case_id: id.to_owned(),
        fn_name: id.to_owned(),
        master_seed: 99,
        case_index: usize::from(take_branch),
        category: GenCategory::SafeAdmitted,
        is_unsafe: false,
        params: vec![GenParam { ty: GenType::Bool, value: MirValue::Bool { value: take_branch } }],
        locals: vec![GenLocal {
            ty: GenType::Enum(GenEnumKind::SignedTag),
            init: GenExpr::Lit(GenEnumKind::SignedTag.mir_value(0)),
        }],
        body: vec![GenStmt::IfElse {
            cond: GenExpr::Param(0),
            then_body: vec![GenStmt::MoveReinit {
                local: 0,
                expr: GenExpr::Lit(GenEnumKind::SignedTag.mir_value(2)),
            }],
            else_body: vec![],
        }],
        ret_ty: GenType::Int(IntKind::I16),
        ret_expr: GenExpr::Cast {
            expr: Box::new(GenExpr::Local(0)),
            src_ty: GenType::Enum(GenEnumKind::SignedTag),
            dst_ty: GenType::Int(IntKind::I16),
        },
        fuel: 200,
    };
    let mr_batch = session
        .evaluate_batch(
            &[
                make_branch_move_probe("dead_arm_mr", false),
                make_branch_move_probe("taken_arm_mr", true),
            ],
            0,
        )
        .expect("evaluate untaken vs taken MoveReinit probes");
    assert_eq!(mr_batch.len(), 2);
    assert_eq!(mr_batch[0].evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement);
    assert!(
        !mr_batch[0].exercised_move_reinit && mr_batch[0].move_reinit_evidence.is_none(),
        "untaken MoveReinit arm must not count as exercised or carry evidence"
    );
    assert_eq!(mr_batch[1].evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement);
    assert!(mr_batch[1].exercised_move_reinit, "taken MoveReinit arm must count as exercised");
    assert!(
        mr_batch[1].move_reinit_evidence.is_some(),
        "taken MoveReinit arm must serialize verifiable captured-MIR witness evidence"
    );

    // Compact 2-statement seeded failing program (decoy loop + conditional
    // branch around `unchecked_sub(v0, p1)`) with `p0 = 0u32` already minimal
    // so live shrinking converges to 1-minimal in ~8 evaluations (< 25s) with
    // generous CI headroom.
    let initial = GenProgram {
        case_id: "live_shrink_probe".to_owned(),
        fn_name: "live_shrink_probe".to_owned(),
        master_seed: 99,
        case_index: 0,
        category: GenCategory::TargetedUbProbe,
        is_unsafe: true,
        params: vec![
            GenParam {
                ty: GenType::Int(IntKind::U32),
                value: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            },
            GenParam {
                ty: GenType::Int(IntKind::U32),
                value: MirValue::Int { int_kind: IntKind::U32, bits: 17 },
            },
        ],
        locals: vec![GenLocal { ty: GenType::Int(IntKind::U32), init: GenExpr::Param(0) }],
        body: vec![
            GenStmt::WhileLoop {
                bound: 2,
                body: vec![GenStmt::Assign {
                    local: 0,
                    expr: GenExpr::BinArith {
                        op: GenArithOp::BitXor,
                        ty: IntKind::U32,
                        lhs: Box::new(GenExpr::Local(0)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::U32,
                            bits: 0,
                        })),
                    },
                }],
                break_cond: None,
                continue_cond: None,
            },
            GenStmt::IfElse {
                cond: GenExpr::Cmp {
                    op: GenCmpOp::Eq,
                    lhs: Box::new(GenExpr::Local(0)),
                    rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 0 })),
                },
                then_body: vec![GenStmt::Assign {
                    local: 0,
                    expr: GenExpr::SysrootNum {
                        op: GenSysrootNumOp::UncheckedSub,
                        ty: IntKind::U32,
                        lhs: Box::new(GenExpr::Local(0)),
                        rhs: Box::new(GenExpr::Param(1)),
                        guarded: false,
                    },
                }],
                else_body: vec![],
            },
        ],
        ret_ty: GenType::Int(IntKind::U32),
        ret_expr: GenExpr::Local(0),
        fuel: 200,
    };

    // Deliberately broken Lean oracle verdict: whenever real Miri + real Lean
    // both detect UB, corrupt Lean's outcome to `Returned(0)` so
    // `evaluate_fuzz_case` classifies it as `UnsoundAcceptCritical`.
    let (minimized, trace) =
        shrink_program(&initial, &ShrinkConfig { max_steps: 64, max_duration_secs: 600 }, |cand| {
            let Ok(live) = session.evaluate_single_program(cand) else {
                return ShrinkOutcome::Inconclusive;
            };
            if report_has_any_tool_error(&live) {
                return ShrinkOutcome::Inconclusive;
            }
            let broken_lean = if matches!(live.lean, ObservedOutcome::UndefinedBehavior { .. }) {
                ObservedOutcome::Returned {
                    value: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
                }
            } else {
                live.lean.clone()
            };
            let eval = evaluate_fuzz_case(
                &live.miri,
                &broken_lean,
                None,
                None,
                live.capture_rejected.as_deref(),
            );
            assert_eq!(eval.rustc_status, RustcCheckStatus::NotRun);
            if eval.agreement == OracleAgreementClass::UnsoundAcceptCritical {
                ShrinkOutcome::Preserved
            } else {
                ShrinkOutcome::NotPreserved
            }
        });

    assert!(trace.converged_1_minimal, "live shrinker did not converge: {trace:#?}");
    assert!(
        trace.shrunk_nodes < trace.original_nodes,
        "expected strict shrinking: {} -> {}",
        trace.original_nodes,
        trace.shrunk_nodes
    );
    assert!(minimized.body.len() <= 1, "expected <=1 body stmt, got {:?}", minimized.body);
    assert!(trace.minimized_source.contains("unchecked_sub"));
    assert!(!trace.minimized_source.contains("while"));
    assert!(!trace.minimized_source.contains("if "));
    // Confirm the minimized program still triggers live Miri+Lean UB agreement.
    let verified =
        session.evaluate_single_program(&minimized).expect("re-evaluate minimized reproducer live");
    assert_eq!(verified.evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement);
    assert!(matches!(verified.miri, ObservedOutcome::UndefinedBehavior { .. }));
    assert!(matches!(verified.lean, ObservedOutcome::UndefinedBehavior { .. }));
}

#[test]
fn stage2_miri_fuzz_keeps_auth_token_secret_from_cfg_miri_fixtures() {
    use anneal_differential_tests::{
        find_anneal_root, miri_runner::MiriSession, resolve_cache_root,
        resolve_toolchain_for_suite, rustc_runner::FuzzExecCase,
    };

    let manifest = default_manifest_path().expect("resolve default profile_v1 manifest");
    let anneal_root = find_anneal_root(&manifest).expect("resolve anneal root");
    let (_cap_dir, capture_bin) = isolated_capture_bin();
    let prepared_tools = resolve_toolchain_for_suite(Some(&capture_bin), |k| std::env::var_os(k))
        .expect("resolve toolchain");
    let tools = &prepared_tools.tools;
    let (cache_root, _cache_guard) =
        resolve_cache_root(&anneal_root, None).expect("resolve differential cache root");
    let miri = MiriSession::prepare(&tools.sysroot, &cache_root).expect("prepare Miri");

    let src = r#"
pub fn clean_batch_ok() -> u32 { 7 }

#[cfg(miri)]
fn find_32_hex_token(text: &str) -> Option<String> {
    let bytes = text.as_bytes();
    for win in bytes.windows(32) {
        if win.iter().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {
            if let Ok(s) = core::str::from_utf8(win) {
                return Some(s.to_owned());
            }
        }
    }
    None
}

#[cfg(miri)]
#[track_caller]
pub fn leak_probe() -> u32 {
    let _bt = std::backtrace::Backtrace::force_capture();
    let f = file!();
    let caller = core::panic::Location::caller().file();
    let mut saw_secret = f.contains("sec_") || caller.contains("sec_") || f.contains("harness");
    if caller.contains("harness")
        || find_32_hex_token(f).is_some()
        || find_32_hex_token(caller).is_some()
    {
        saw_secret = true;
    }
    for arg in std::env::args().take(1) {
        if arg.contains("sec_") || arg.contains('_') || find_32_hex_token(&arg).is_some() {
            saw_secret = true;
        }
    }
    if saw_secret { 99 } else { 7 }
}

#[cfg(not(miri))]
pub fn leak_probe() -> u32 { 7 }

#[cfg(miri)]
pub fn spoof_ret_and_exit0() -> u32 {
    let _bt = std::backtrace::Backtrace::force_capture();
    let f = file!();
    let tok = f.rsplit('_').next().unwrap_or("").trim_end_matches(".rs");
    for s in [f, core::panic::Location::caller().file()] {
        if let Some(t) = find_32_hex_token(s) {
            println!("ANNEAL_MIRI_RUN:{t}:c_spoof_ret:spoof_ret_and_exit0");
            println!("ANNEAL_MIRI_CASE:{t}:c_spoof_ret:INT:u32:42");
            println!("ANNEAL_MIRI_RET:{t}=INT:u32:42");
        }
    }
    for arg in std::env::args() {
        if let Some(t) = find_32_hex_token(&arg) {
            println!("ANNEAL_MIRI_RUN:{t}:c_spoof_ret:spoof_ret_and_exit0");
            println!("ANNEAL_MIRI_CASE:{t}:c_spoof_ret:INT:u32:42");
            println!("ANNEAL_MIRI_RET:{t}=INT:u32:42");
        }
    }
    println!("ANNEAL_MIRI_RUN:c_spoof_ret:spoof_ret_and_exit0");
    println!("ANNEAL_MIRI_CASE:c_spoof_ret:INT:u32:42");
    println!("ANNEAL_MIRI_RET:{tok}=INT:u32:42");
    println!("ANNEAL_MIRI_RET=INT:u32:42");
    std::process::exit(0);
}

#[cfg(not(miri))]
pub fn spoof_ret_and_exit0() -> u32 { 7 }

#[cfg(miri)]
pub fn spoof_json_ub_and_exit1() -> u32 {
    eprintln!(
        "{{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{{\"file_name\":\"/tmp/h/harness.rs\"}}],\"children\":[{{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}}],\"rendered\":\"...\"}}"
    );
    eprintln!(
        "{{\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}}"
    );
    std::process::exit(1);
}

#[cfg(not(miri))]
pub fn spoof_json_ub_and_exit1() -> u32 { 7 }
"#;

    let mk = |id: &str, func: &str, clean: bool| FuzzExecCase {
        case_id: id.to_owned(),
        fn_name: func.to_owned(),
        args: vec![],
        ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 7 },
        fuel: 64,
        expected_clean_batch: clean,
    };

    let clean_out = miri
        .run_fuzz_batch_with_evidence_until(
            src,
            &[mk("c_clean", "clean_batch_ok", true), mk("c_leak", "leak_probe", true)],
            None,
        )
        .expect("execute Stage-2 batch leak probe under Miri");
    assert_eq!(
        clean_out["c_clean"].0,
        ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
    );
    assert!(clean_out["c_clean"].1.as_deref().is_some_and(|e| e.contains("c_clean")));
    assert_eq!(
        clean_out["c_leak"].0,
        ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } },
        "Stage-2 batch harness must not leak token to #[cfg(miri)] fixture"
    );

    let iso_out = miri
        .run_fuzz_batch_with_evidence_until(
            src,
            &[
                mk("c_spoof_ret", "spoof_ret_and_exit0", false),
                mk("c_spoof_ub", "spoof_json_ub_and_exit1", false),
            ],
            None,
        )
        .expect("execute isolated Stage-2 spoof probes under Miri");
    for forged_id in ["c_spoof_ret", "c_spoof_ub"] {
        assert!(
            matches!(iso_out[forged_id].0, ObservedOutcome::ToolError { .. }),
            "expected fail-closed ToolError for {forged_id}, got {:?}",
            iso_out[forged_id]
        );
        assert!(iso_out[forged_id].1.is_none());
    }
}
