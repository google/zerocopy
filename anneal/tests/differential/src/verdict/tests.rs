// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests for the verdict algebra, canonical MIR values, and suite metrics.

use super::*;

fn int_u32(v: u32) -> MirValue {
    MirValue::Int { int_kind: IntKind::U32, bits: u128::from(v) }
}

fn ret_u32(v: u32) -> ObservedOutcome {
    ObservedOutcome::Returned { value: int_u32(v) }
}

#[test]
fn pass_agreement_and_mismatch_classified() {
    let ok = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(42)),
        None,
        None,
        &ret_u32(42),
        &ret_u32(42),
        Some(&ret_u32(42)),
    );
    assert_eq!(ok, Verdict::AgreeValue { value: int_u32(42) });
    assert!(ok.is_ok());

    let mismatch = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(42)),
        None,
        None,
        &ret_u32(42),
        &ret_u32(43),
        None,
    );
    assert!(matches!(mismatch, Verdict::ValueMismatch { .. }));
    assert!(!mismatch.is_ok());

    let leg3_div = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(42)),
        None,
        None,
        &ret_u32(42),
        &ret_u32(42),
        Some(&ret_u32(99)),
    );
    assert!(matches!(leg3_div, Verdict::LegDivergence { .. }));
    assert!(!leg3_div.is_ok());
}

#[test]
fn missed_ub_or_panic_is_unsound() {
    let missed_ub = evaluate_case(
        Expectation::UnsupportedControl,
        None,
        None,
        None,
        &ObservedOutcome::UndefinedBehavior { detail: "div by zero".to_owned() },
        &ret_u32(0),
        None,
    );
    assert!(matches!(missed_ub, Verdict::UnsoundMissedFault { .. }));
    assert!(!missed_ub.is_ok());

    let missed_panic = evaluate_case(
        Expectation::Pass,
        None,
        None,
        None,
        &ObservedOutcome::Panic { detail: "panicked at explicit panic".to_owned() },
        &ret_u32(0),
        None,
    );
    assert!(matches!(missed_panic, Verdict::UnsoundMissedFault { .. }));
    assert!(!missed_panic.is_ok());

    let unexpected_unwind = evaluate_case(
        Expectation::Pass,
        None,
        None,
        None,
        &ObservedOutcome::Panic { detail: "panicked at explicit panic".to_owned() },
        &ObservedOutcome::AbnormalAbort { detail: "TerminalOut.unwound".to_owned() },
        Some(&ObservedOutcome::AbnormalAbort { detail: "unwound".to_owned() }),
    );
    assert!(matches!(unexpected_unwind, Verdict::LegDivergence { .. }));
    assert!(!unexpected_unwind.is_ok());
}

#[test]
fn conservative_unsupported_requires_step_time_and_control_expectation() {
    let disallowed = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(1)),
        None,
        None,
        &ret_u32(1),
        &ObservedOutcome::Unsupported { detail: "unmodeled call".to_owned() },
        None,
    );
    assert!(matches!(disallowed, Verdict::ConservativeRejection { .. }));
    assert!(!disallowed.is_ok());

    let init_rej = evaluate_case(
        Expectation::UnsupportedControl,
        None,
        None,
        None,
        &ObservedOutcome::AbnormalAbort { detail: "aborted".to_owned() },
        &ObservedOutcome::InitUnsupported { detail: "initStateBy unsupported".to_owned() },
        Some(&ObservedOutcome::Unsupported { detail: "init".to_owned() }),
    );
    assert!(matches!(init_rej, Verdict::LegDivergence { .. }));
    assert!(!init_rej.is_ok());

    let allowed = evaluate_case(
        Expectation::UnsupportedControl,
        None,
        None,
        Some(ExpectedMiriOutcome::AbnormalAbort),
        &ObservedOutcome::AbnormalAbort { detail: "aborted".to_owned() },
        &ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() },
        Some(&ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() }),
    );
    assert!(matches!(allowed, Verdict::SoundConservativeAbstraction { .. }));
    assert!(allowed.is_ok());

    let wrong_miri_pin = evaluate_case(
        Expectation::UnsupportedControl,
        None,
        None,
        Some(ExpectedMiriOutcome::AbnormalAbort),
        &ret_u32(2),
        &ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() },
        None,
    );
    assert!(matches!(wrong_miri_pin, Verdict::LegDivergence { .. }));
    assert!(!wrong_miri_pin.is_ok());

    let miri_init_err = evaluate_case(
        Expectation::UnsupportedControl,
        None,
        None,
        None,
        &ObservedOutcome::InitUnsupported { detail: "unexpected Miri init error".to_owned() },
        &ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() },
        None,
    );
    assert!(matches!(miri_init_err, Verdict::LegDivergence { .. }));
    assert!(!miri_init_err.is_ok());
}

#[test]
fn ub_cause_substring_and_false_positive_checked() {
    let wrong_cause = evaluate_case(
        Expectation::Ub,
        None,
        Some("overflow in signed division"),
        None,
        &ObservedOutcome::UndefinedBehavior {
            detail: "error: Undefined Behavior: dividing by zero".to_owned(),
        },
        &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
        None,
    );
    assert!(matches!(wrong_cause, Verdict::LegDivergence { .. }));

    let right_cause = evaluate_case(
        Expectation::Ub,
        None,
        Some("dividing by zero"),
        None,
        &ObservedOutcome::UndefinedBehavior {
            detail: "error: Undefined Behavior: dividing by zero".to_owned(),
        },
        &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
        None,
    );
    assert_eq!(right_cause, Verdict::AgreeUndefinedBehavior);

    let false_pos = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(7)),
        None,
        None,
        &ret_u32(7),
        &ObservedOutcome::UndefinedBehavior { detail: "spurious UB".to_owned() },
        None,
    );
    assert!(matches!(false_pos, Verdict::LegDivergence { .. }));
    assert!(!false_pos.is_ok());
}

#[test]
fn red_flags_reject_empty_missing_polarities_or_zero_kernel_checks() {
    let empty = SuiteMetrics::from_outcomes([]);
    assert!(empty.check_red_flags().is_err());

    let only_pass =
        SuiteMetrics::from_outcomes([(&Verdict::AgreeValue { value: int_u32(1) }, true)]);
    assert!(only_pass.check_red_flags().is_err());

    let missing_kernel_ub = SuiteMetrics::from_outcomes([
        (&Verdict::AgreeValue { value: int_u32(1) }, true),
        (&Verdict::AgreeUndefinedBehavior, false),
        (
            &Verdict::SoundConservativeAbstraction {
                miri: Box::new(ObservedOutcome::AbnormalAbort { detail: "abort".to_owned() }),
                lean_detail: "unsupported".to_owned(),
            },
            false,
        ),
    ]);
    assert!(missing_kernel_ub.check_red_flags().is_err());

    let complete = SuiteMetrics::from_outcomes([
        (&Verdict::AgreeValue { value: int_u32(1) }, true),
        (&Verdict::AgreeUndefinedBehavior, true),
        (
            &Verdict::SoundConservativeAbstraction {
                miri: Box::new(ObservedOutcome::AbnormalAbort { detail: "abort".to_owned() }),
                lean_detail: "unsupported".to_owned(),
            },
            false,
        ),
    ]);
    assert_eq!(complete.check_red_flags().unwrap(), 7);
}

#[test]
fn observed_outcome_json_has_no_duplicate_kind_keys_and_round_trips() {
    let returned = ret_u32(42);
    let serialized = serde_json::to_string(&returned).expect("serialize ObservedOutcome");
    assert_eq!(
        serialized.matches("\"kind\"").count(),
        2,
        "expected outer outcome kind + nested value.kind in {serialized}"
    );
    let top_val: serde_json::Value = serde_json::from_str(&serialized).unwrap();
    assert_eq!(top_val["kind"], "returned");
    assert_eq!(top_val["value"]["kind"], "int");
    let parsed: ObservedOutcome =
        serde_json::from_str(&serialized).expect("round-trip ObservedOutcome");
    assert_eq!(parsed, returned);
}

#[test]
fn scalar_range_validation_enforced() {
    assert_eq!(IntKind::I8.parse_decimal_bits("-128").unwrap(), 128);
    assert!(IntKind::I8.parse_decimal_bits("-129").is_err());
    assert!(IntKind::U8.parse_decimal_bits("256").is_err());
    assert_eq!(
        IntKind::I32.format_decimal(IntKind::I32.parse_decimal_bits("-2147483648").unwrap()),
        "-2147483648"
    );
}

#[test]
fn primary_miri_vs_lean_failures_take_precedence_over_leg3_disagreement() {
    // Missed Miri UB in Lean must stay `UnsoundMissedFault` even when Leg 3
    // (`anneal-mir-eval`) agrees with Miri (disagreeing with Lean).
    let missed_ub = evaluate_case(
        Expectation::Ub,
        None,
        Some("dividing by zero"),
        None,
        &ObservedOutcome::UndefinedBehavior {
            detail: "Undefined Behavior: dividing by zero".to_owned(),
        },
        &ret_u32(0),
        Some(&ObservedOutcome::UndefinedBehavior { detail: "ub".to_owned() }),
    );
    assert!(matches!(missed_ub, Verdict::UnsoundMissedFault { .. }), "{missed_ub:?}");

    // Value mismatch between Miri and Lean must stay `ValueMismatch` even
    // when Leg 3 agrees with Miri.
    let val_mismatch = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(7)),
        None,
        None,
        &ret_u32(7),
        &ret_u32(9),
        Some(&ret_u32(7)),
    );
    assert!(matches!(val_mismatch, Verdict::ValueMismatch { .. }), "{val_mismatch:?}");

    // Disallowed step-time `.unsupported` in Lean must stay
    // `ConservativeRejection` even when Leg 3 returned a value.
    let cons_rej = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(7)),
        None,
        None,
        &ret_u32(7),
        &ObservedOutcome::Unsupported { detail: "step unsupported".to_owned() },
        Some(&ret_u32(7)),
    );
    assert!(matches!(cons_rej, Verdict::ConservativeRejection { .. }), "{cons_rej:?}");

    // When Miri and Lean agree, a Leg 3 disagreement still triggers
    // `LegDivergence`.
    let leg3_div = evaluate_case(
        Expectation::Pass,
        Some(&int_u32(7)),
        None,
        None,
        &ret_u32(7),
        &ret_u32(7),
        Some(&ret_u32(9)),
    );
    assert!(matches!(leg3_div, Verdict::LegDivergence { .. }), "{leg3_div:?}");
}
