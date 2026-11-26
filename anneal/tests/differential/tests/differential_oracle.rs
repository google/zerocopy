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
    default_manifest_path, run_differential_suite,
    verdict::{Expectation, IntKind, MirValue, ObservedOutcome, Verdict},
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

#[test]
fn profile_v1_differential_oracle_and_mutants_pass_live() {
    let manifest = default_manifest_path().expect("resolve default profile_v1 manifest");
    let report = run_differential_suite(&RunOptions {
        manifest_path: manifest.clone(),
        capture_bin: Some(PathBuf::from(env!("CARGO_BIN_EXE_anneal-diff-capture-test-bin"))),
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

    let reg_report = run_differential_suite(&RunOptions {
        manifest_path: reg_manifest,
        capture_bin: Some(PathBuf::from(env!("CARGO_BIN_EXE_anneal-diff-capture-test-bin"))),
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
    let capture_bin = PathBuf::from(env!("CARGO_BIN_EXE_anneal-diff-capture-test-bin"));
    let (tools, _, _) = resolve_toolchain_for_suite(Some(&capture_bin), |k| std::env::var_os(k))
        .expect("resolve toolchain");
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
