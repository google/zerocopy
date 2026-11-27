// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::*;

#[test]
fn parses_all_stages_guard_tag_and_mir_assertions() {
    let src = "\
// === case: pass_case ===
//@ pass
//@ mir-contains: \"add\"
pub fn pass_fn() {}

// === case: guard_case ===
//@ fail(preflight): \"sorry\"
//@ kills-guard: preflight_sorry_reject
pub fn bad_preflight() {}

// === case: audit_case ===
//@ fail(audit): \"custom axiom\"
pub fn bad_audit() {}

// === case: proof_case ===
//@ known_bug(#4123, proof, my_fn): \"unsolved goals\"
//@ mir-not-contains: \"panic\"
pub fn my_fn() {}
";
    let cases = DirectiveParser::parse("demo", Path::new("demo.rs"), src).unwrap();
    assert_eq!(cases.len(), 4);
    assert_eq!(cases[0].expectation, PrimaryExpectation::Pass);
    assert_eq!(cases[0].mir_contains, vec!["add"]);
    assert_eq!(
        cases[1].expectation,
        PrimaryExpectation::Fail {
            stage: FailureStage::Preflight,
            substring: "sorry".into()
        }
    );
    assert_eq!(
        cases[1].kills_guard.as_deref(),
        Some("preflight_sorry_reject")
    );
    assert_eq!(
        cases[2].expectation,
        PrimaryExpectation::Fail {
            stage: FailureStage::Audit,
            substring: "custom axiom".into()
        }
    );
    assert_eq!(
        cases[3].expectation,
        PrimaryExpectation::KnownBug {
            issue: 4123,
            stage: FailureStage::Proof {
                scope: "my_fn".into()
            },
            substring: "unsolved goals".into()
        }
    );
}

#[test]
fn polarity_lock_refuses_pass_to_fail_and_fail_to_pass_even_when_blessing() {
    let dir = tempfile::tempdir().unwrap();
    let file_path = dir.path().join("corpus.rs");
    let original = "\
// === case: must_pass ===
//@ pass
pub fn ok() {}

// === case: must_fail ===
//@ fail(capture): \"unsupported\"
pub fn bad() {}

// === case: tracked_bug ===
//@ known_bug(#99, audit): \"old error\"
pub fn bug() {}
";
    fs::write(&file_path, original).unwrap();
    let cases = DirectiveParser::parse("corpus", &file_path, original).unwrap();

    // 1. `evaluate_case(..., bless = true)` refuses `pass -> fail`.
    let pass_failed = evaluate_case(
        &cases[0],
        &CaseExpectationResult::Failed {
            message: "unexpected failure".into(),
            failure: Some(StageFailure {
                stage: FailureStage::Capture,
                diagnostic: "broken".into(),
            }),
            mir_lean: None,
        },
        true,
    );
    assert!(matches!(pass_failed, CaseOutcome::Failed(_)), "{pass_failed:?}");

    // 2. `evaluate_case(..., bless = true)` refuses `fail -> pass`.
    let fail_passed = evaluate_case(
        &cases[1],
        &CaseExpectationResult::Passed {
            mir_lean: None,
            output_text: "verified".into(),
        },
        true,
    );
    assert!(matches!(fail_passed, CaseOutcome::Failed(_)), "{fail_passed:?}");

    // 3. `apply_bless_patches` directly refuses forced polarity flips
    //    without touching disk.
    let bad_flip_1 = BlessPatch {
        file_path: file_path.clone(),
        line_idx: cases[0].primary_line_idx,
        replacement: "//@ fail(capture): \"broken\"".into(),
    };
    let err1 = apply_bless_patches(&[bad_flip_1]).unwrap_err();
    assert!(err1.contains("polarity-lock refusal"), "{err1}");

    let bad_flip_2 = BlessPatch {
        file_path: file_path.clone(),
        line_idx: cases[1].primary_line_idx,
        replacement: "//@ pass".into(),
    };
    let err2 = apply_bless_patches(&[bad_flip_2]).unwrap_err();
    assert!(err2.contains("polarity-lock refusal"), "{err2}");
    assert_eq!(fs::read_to_string(&file_path).unwrap(), original);

    let bad_stage_shift = evaluate_case(
        &cases[1],
        &CaseExpectationResult::Failed {
            message: "shifted stage".into(),
            failure: Some(StageFailure {
                stage: FailureStage::Audit,
                diagnostic: "wrong stage".into(),
            }),
            mir_lean: None,
        },
        true,
    );
    assert!(
        matches!(bad_stage_shift, CaseOutcome::Failed(_)),
        "stage shift must not bless: {bad_stage_shift:?}"
    );

    let bad_stage_patch = BlessPatch {
        file_path: file_path.clone(),
        line_idx: cases[1].primary_line_idx,
        replacement: "//@ fail(audit): \"shifted\"".into(),
    };
    let err3 = apply_bless_patches(&[bad_stage_patch]).unwrap_err();
    assert!(err3.contains("stage-lock refusal"), "{err3}");
    assert_eq!(fs::read_to_string(&file_path).unwrap(), original);

    // 4. Legitimate fail->fail diagnostic refresh and known_bug->pass
    //    promotion succeed.
    let CaseOutcome::Blessed(fail_refresh) = evaluate_case(
        &cases[1],
        &CaseExpectationResult::Failed {
            message: "diag changed".into(),
            failure: Some(StageFailure {
                stage: FailureStage::Capture,
                diagnostic: "new capture refusal".into(),
            }),
            mir_lean: None,
        },
        true,
    ) else {
        panic!("expected fail->fail bless patch");
    };
    let CaseOutcome::Blessed(bug_promote) = evaluate_case(
        &cases[2],
        &CaseExpectationResult::Passed {
            mir_lean: None,
            output_text: "ok".into(),
        },
        true,
    ) else {
        panic!("expected known_bug->pass bless patch");
    };
    apply_bless_patches(&[fail_refresh, bug_promote]).unwrap();
    let updated = DirectiveParser::parse(
        "corpus",
        &file_path,
        &fs::read_to_string(&file_path).unwrap(),
    )
    .unwrap();
    assert_eq!(
        updated[1].expectation,
        PrimaryExpectation::Fail {
            stage: FailureStage::Capture,
            substring: "new capture refusal".into()
        }
    );
    assert_eq!(updated[2].expectation, PrimaryExpectation::Pass);
}
