// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Curated multi-category differential trace corpus spanning:
//! 1. Multi-arg scalar & bitwise functions (`5` cases)
//! 2. Padded `#[repr(C)]` structs & fieldless enums (`4` cases)
//! 3. Multi-block branching & loop CFGs (`5` `FullBranchesAndCalls` cases)
//! 4. Multi-step & multi-call chains (`8` cases covering `0..3+` calls, nested
//!    stacks, cleanup unwinds, scheduled `ReturnBytes`, scheduled `Abort`
//!    without drop execution, and invalid scheduled bit-pattern `FaultUb`)
//! 5. Metamorphic inlining duality pairs (`5` cases comparing multi-call
//!    execution against source-inlined single-body twins across all active
//!    authorities)
//! 6. Negative UB, conservative over-approximation, and disclosed-gap probes
//!    (`6` cases)

use crate::{
    outcome::{
        ConservativeRefKind, DisclosedGapKind, DisclosedGapSpec, ExpectedConservativeSpec,
        ExpectedUbSpec, IntKind, SpineCompareMode, TraceVal, UbFaultClass,
    },
    spec::{
        CaseCategory, ExpectedCaseClass, LeanProgramSpec, MetamorphicTwin, ReturnShape,
        TraceTestCase,
    },
    trace_observer::{EnvAction, EnvSchedule},
};

mod builders;
mod sources;

use builders::*;
use sources::*;

/// Filter corpus cases by substring match on `case.id`, failing closed when an
/// explicit filter matches zero cases so typos never silently pass with
/// `total=0`.
pub fn filter_corpus_cases(
    mut corpus: Vec<TraceTestCase>,
    filter: Option<&str>,
) -> Result<Vec<TraceTestCase>, String> {
    if let Some(substr) = filter {
        corpus.retain(|c| c.id.contains(substr));
        if corpus.is_empty() {
            return Err(format!("corpus filter {substr:?} matched 0 cases"));
        }
    }
    Ok(corpus)
}

/// Build the full curated differential trace corpus covering all 6 categories
/// (`33` cases).
pub fn curated_corpus() -> Vec<TraceTestCase> {
    let mut cases = Vec::with_capacity(33);

    // -----------------------------------------------------------------------
    // Category 1: Multi-arg scalar & bitwise (5 cases — real captured MIR)
    // -----------------------------------------------------------------------
    cases.push(captured_u32_case(
        "cat1_clamp_u32_range",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "clamp_u32_range",
        &[42, 10, 30],
        SpineCompareMode::ObsErasedCallsOnly,
    ));
    cases.push(captured_u32_case(
        "cat1_rotate_xor_mix",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "rotate_xor_mix",
        &[0x1234_5678, 0x9ABC_DEF0, 3],
        SpineCompareMode::ObsErasedCallsOnly,
    ));
    cases.push(captured_u32_case(
        "cat1_checked_affine_step",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "checked_affine_step",
        &[100, 7, 55],
        SpineCompareMode::ObsErasedCallsOnly,
    ));
    cases.push(TraceTestCase {
        id: "cat1_signed_abs_diff".to_string(),
        category: CaseCategory::ScalarBitwise,
        pure_rust_source: CAT1_SCALAR_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "signed_abs_diff".to_string(),
        rust_arg_exprs: vec!["-15i32".to_string(), "27i32".to_string()],
        lean_args: vec![TraceVal::i32(-15), TraceVal::i32(27)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat1_scalar".to_string(),
            select_fn: "signed_abs_diff".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(captured_u32_case(
        "cat1_bitfield_extract",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "bitfield_extract",
        &[0xABCD_1234, 4, 0x0FFF],
        SpineCompareMode::ObsErasedCallsOnly,
    ));

    // -----------------------------------------------------------------------
    // Category 2: Padded #[repr(C)] structs & fieldless enums (4 cases)
    // -----------------------------------------------------------------------
    cases.push(TraceTestCase {
        id: "cat2_c_like_enum_dispatch".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_ENUM_SRC.to_string(),
        traced_rust_source: Some(CAT2_ENUM_TRACED_SRC.to_string()),
        entry_fn: "c_like_enum_dispatch".to_string(),
        rust_arg_exprs: vec![
            "subject::DispatchMode::Xor".to_string(),
            "0xF0F0u32".to_string(),
            "0x0FF0u32".to_string(),
        ],
        lean_args: vec![
            TraceVal::Enum {
                type_name: "DispatchMode".to_string(),
                variant_name: "Xor".to_string(),
                variant_index: 2,
                discriminant: 2,
                tag_bytes: Some(1),
            },
            TraceVal::u32(0xF0F0),
            TraceVal::u32(0x0FF0),
        ],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_enum".to_string(),
            select_fn: "c_like_enum_dispatch".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat2_repr_c_padded_header".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_PADDED_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT2_PADDED_TRACED_SRC.to_string()),
        entry_fn: "repr_c_padded_header".to_string(),
        rust_arg_exprs: vec!["1u8".to_string(), "100u32".to_string(), "23u32".to_string()],
        lean_args: vec![TraceVal::u8(1), TraceVal::u32(100), TraceVal::u32(23)],
        ret_shape: ReturnShape::PaddedStruct { type_name: "PaddedHeader".to_string() },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_padded".to_string(),
            select_fn: "repr_c_padded_header".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Returned,
            "initStateBy unsupported",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat2_nested_padded_pair_sum".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_PADDED_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT2_PADDED_TRACED_SRC.to_string()),
        entry_fn: "nested_padded_pair_sum".to_string(),
        rust_arg_exprs: vec![
            "1u8".to_string(),
            "7u32".to_string(),
            "13u32".to_string(),
            "3u32".to_string(),
        ],
        lean_args: vec![TraceVal::u8(1), TraceVal::u32(7), TraceVal::u32(13), TraceVal::u32(3)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_padded".to_string(),
            select_fn: "nested_padded_pair_sum".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Returned,
            "initStateBy unsupported",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat2_option_u32_map_or".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_PADDED_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT2_PADDED_TRACED_SRC.to_string()),
        entry_fn: "option_u32_map_or".to_string(),
        rust_arg_exprs: vec![
            "true".to_string(),
            "40u32".to_string(),
            "99u32".to_string(),
            "2u32".to_string(),
        ],
        lean_args: vec![
            TraceVal::bool_val(true),
            TraceVal::u32(40),
            TraceVal::u32(99),
            TraceVal::u32(2),
        ],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_padded".to_string(),
            select_fn: "option_u32_map_or".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Returned,
            "initStateBy unsupported",
        )),
        disclosed_gap: None,
    });

    // -----------------------------------------------------------------------
    // Category 3: Multi-block branching & loop CFGs (5 cases — real captured
    // MIR cross-checked under `SpineCompareMode::FullBranchesAndCalls`)
    // -----------------------------------------------------------------------
    cases.push(captured_u32_case(
        "cat3_match_four_way_tag",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "match_four_way_tag",
        &[2, 9, 25],
        SpineCompareMode::FullBranchesAndCalls,
    ));
    cases.push(captured_u32_case(
        "cat3_short_circuit_guard_chain",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "short_circuit_guard_chain",
        &[3, 7, 15],
        SpineCompareMode::FullBranchesAndCalls,
    ));
    cases.push(captured_u32_case(
        "cat3_while_loop_accumulate",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "while_loop_accumulate",
        &[5, 4],
        SpineCompareMode::FullBranchesAndCalls,
    ));
    cases.push(TraceTestCase {
        id: "cat3_early_return_search_4".to_string(),
        category: CaseCategory::BranchLoopCfg,
        pure_rust_source: CAT3_CFG_SRC.to_string(),
        traced_rust_source: Some(CAT3_CFG_TRACED_SRC.to_string()),
        entry_fn: "early_return_search_4".to_string(),
        rust_arg_exprs: vec![
            "11u32".to_string(),
            "22u32".to_string(),
            "33u32".to_string(),
            "44u32".to_string(),
            "33u32".to_string(),
        ],
        lean_args: vec![
            TraceVal::u32(11),
            TraceVal::u32(22),
            TraceVal::u32(33),
            TraceVal::u32(44),
            TraceVal::u32(33),
        ],
        ret_shape: ReturnShape::Scalar { kind: IntKind::I32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat3_cfg".to_string(),
            select_fn: "early_return_search_4".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::FullBranchesAndCalls,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(captured_u32_case(
        "cat3_nested_if_else_matrix",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "nested_if_else_matrix",
        &[3, 1, 100],
        SpineCompareMode::FullBranchesAndCalls,
    ));

    // -----------------------------------------------------------------------
    // Category 4: Multi-step & multi-call chains (8 cases — captured leaf
    // callees + scheduled ReturnBytes, Unwind cleanup, real Abort, & invalid
    // ReturnBytes UB)
    // -----------------------------------------------------------------------
    cases.push(TraceTestCase {
        id: "cat4_call_once_and_postprocess".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_once_and_postprocess".to_string(),
        rust_arg_exprs: vec!["10u32".to_string(), "5u32".to_string()],
        lean_args: vec![TraceVal::u32(10), TraceVal::u32(5)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string()],
            caller_identity: "call_once_and_postprocess".to_string(),
            caller_lean_body: lean_body_call_once_and_postprocess(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::FullBranchesAndCalls,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat4_call_twice_sequential".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_twice_sequential".to_string(),
        rust_arg_exprs: vec!["4u32".to_string(), "6u32".to_string()],
        lean_args: vec![TraceVal::u32(4), TraceVal::u32(6)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string()],
            caller_identity: "call_twice_sequential".to_string(),
            caller_lean_body: lean_body_call_twice_sequential(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat4_call_in_branch_arms".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_in_branch_arms".to_string(),
        rust_arg_exprs: vec!["3u32".to_string(), "11u32".to_string(), "7u32".to_string()],
        lean_args: vec![TraceVal::u32(3), TraceVal::u32(11), TraceVal::u32(7)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string(), "ext_combine_u32".to_string()],
            caller_identity: "call_in_branch_arms".to_string(),
            caller_lean_body: lean_body_call_in_branch_arms(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat4_call_in_bounded_loop_3x".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_in_bounded_loop_3x".to_string(),
        rust_arg_exprs: vec!["2u32".to_string()],
        lean_args: vec![TraceVal::u32(2)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string()],
            caller_identity: "call_in_bounded_loop_3x".to_string(),
            caller_lean_body: lean_body_call_in_bounded_loop_3x(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 512,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    {
        let mut unwind_sched = EnvSchedule::default();
        unwind_sched.push_callee(
            "ext_may_panic_u32",
            EnvAction::Unwind { message: "simulated external callee panic".to_string() },
        );
        cases.push(TraceTestCase {
            id: "cat4_callee_panic_unwind_cleanup".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "callee_panic_unwind_cleanup".to_string(),
            rust_arg_exprs: vec!["0xDEADu32".to_string(), "17u32".to_string()],
            lean_args: vec![TraceVal::u32(0xDEAD), TraceVal::u32(17)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::SyntheticMirAst {
                program_lean_expr: lean_prog_unwind_cleanup(),
                external_callees: vec!["ext_may_panic_u32".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: unwind_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::FullBranchesAndCalls,
            expected_class: ExpectedCaseClass::Unwind,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        });
    }
    {
        let mut ret_sched = EnvSchedule::default();
        ret_sched.push_callee(
            "ext_transform_u32",
            EnvAction::ReturnBytes(777u32.to_le_bytes().to_vec()),
        );
        cases.push(TraceTestCase {
            id: "cat4_scheduled_return_bytes_override".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "call_twice_sequential".to_string(),
            rust_arg_exprs: vec!["4u32".to_string(), "6u32".to_string()],
            lean_args: vec![TraceVal::u32(4), TraceVal::u32(6)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
                crate_name: "cat4_helpers".to_string(),
                captured_callees: vec!["ext_transform_u32".to_string()],
                caller_identity: "call_twice_sequential".to_string(),
                caller_lean_body: lean_body_call_twice_sequential(),
                external_callees: vec!["ext_transform_u32".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: ret_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::FullBranchesAndCalls,
            expected_class: ExpectedCaseClass::Agree,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        });
    }
    {
        let mut abort_sched = EnvSchedule::default();
        abort_sched.push_callee(
            "ext_may_panic_u32",
            EnvAction::Abort { reason: "halt_boundary".to_string() },
        );
        cases.push(TraceTestCase {
            id: "cat4_scheduled_abort_no_drop".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "callee_abort_skips_drops".to_string(),
            rust_arg_exprs: vec!["1u32".to_string(), "17u32".to_string()],
            lean_args: vec![TraceVal::u32(1), TraceVal::u32(17)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::SyntheticMirAst {
                program_lean_expr: lean_prog_unwind_cleanup(),
                external_callees: vec!["ext_may_panic_u32".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: abort_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::ObsErasedCallsOnly,
            expected_class: ExpectedCaseClass::Abort,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        });
    }
    {
        let mut bad_bool_sched = EnvSchedule::default();
        bad_bool_sched.push_callee("ext_oracle_bool", EnvAction::ReturnBytes(vec![2u8]));
        cases.push(TraceTestCase {
            id: "cat4_scheduled_invalid_bool_return_ub".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "call_bool_oracle_select".to_string(),
            rust_arg_exprs: vec!["5u32".to_string(), "100u32".to_string(), "200u32".to_string()],
            lean_args: vec![TraceVal::u32(5), TraceVal::u32(100), TraceVal::u32(200)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
                crate_name: "cat4_helpers".to_string(),
                captured_callees: vec!["ext_oracle_bool".to_string()],
                caller_identity: "call_bool_oracle_select".to_string(),
                caller_lean_body: lean_body_call_bool_oracle_select(),
                external_callees: vec!["ext_oracle_bool".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: bad_bool_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::OutcomeOnly,
            expected_class: ExpectedCaseClass::UndefinedBehavior,
            expected_ub: Some(
                ExpectedUbSpec::new(
                    UbFaultClass::ScheduledReturnDecode,
                    "callee `ext_oracle_bool` scheduled ReturnBytes invalid",
                    Some("invalid scheduled ReturnBytes for ext_oracle_bool"),
                )
                .with_lean_refusal_marker(
                    "external callee unsupported in StrictVerbatim: ext_oracle_bool",
                ),
            ),
            expected_conservative: None,
            disclosed_gap: None,
        });
    }

    // -----------------------------------------------------------------------
    // Category 5: Metamorphic Inlining Duality Pairs (5 cases)
    // -----------------------------------------------------------------------
    cases.push(metamorphic_case(
        "cat5_pipeline_two_helpers",
        "pipeline_two_helpers",
        "pipeline_two_helpers_inlined",
        &[19, 77],
        vec!["helper_add_const".to_string(), "helper_xor_fold".to_string()],
        lean_body_pipeline_two_helpers(),
    ));
    cases.push(metamorphic_case(
        "cat5_diamond_helper_dag",
        "diamond_helper_dag",
        "diamond_helper_dag_inlined",
        &[23],
        vec!["helper_add_const".to_string(), "helper_xor_fold".to_string()],
        lean_body_diamond_helper_dag(),
    ));
    cases.push(metamorphic_case(
        "cat5_conditional_helper_dispatch",
        "conditional_helper_dispatch",
        "conditional_helper_dispatch_inlined",
        &[1, 35, 19],
        vec!["helper_add_const".to_string(), "helper_xor_fold".to_string()],
        lean_body_conditional_helper_dispatch(),
    ));
    cases.push(metamorphic_case(
        "cat5_stateful_counter_pair",
        "stateful_counter_pair",
        "stateful_counter_pair_inlined",
        &[8, 3],
        vec!["helper_step_counter".to_string()],
        lean_body_stateful_counter_pair(),
    ));
    cases.push(metamorphic_case(
        "cat5_recursive_depth_2_unroll",
        "recursive_depth_2_unroll",
        "recursive_depth_2_unroll_inlined",
        &[3, 10],
        vec!["helper_depth_step".to_string()],
        lean_body_recursive_depth_2_unroll(),
    ));

    // -----------------------------------------------------------------------
    // Category 6: Negative UB / Conservative Over-Approx / Disclosed Gaps (6)
    // -----------------------------------------------------------------------
    cases.push(TraceTestCase {
        id: "cat6_unreachable_ub".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "unreachable_ub".to_string(),
        rust_arg_exprs: vec!["0u32".to_string()],
        lean_args: vec![TraceVal::u32(0)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "unreachable_ub".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        expected_ub: Some(
            ExpectedUbSpec::new(
                UbFaultClass::UnreachableOrNoUnwind,
                "entering unreachable code",
                None,
            )
            .with_lean_refusal_marker(
                "unsupported terminator: Trusted.MirSemantics.FaultKind.unsupported",
            )
            .with_mir_eval_marker("executed Unreachable terminator"),
        ),
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_mir_unreachable_ub".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "unreachable_ub".to_string(),
        rust_arg_exprs: vec!["0u32".to_string()],
        lean_args: vec![TraceVal::u32(0)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::SyntheticMirAst {
            program_lean_expr: lean_prog_unreachable_ub(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        expected_ub: Some(ExpectedUbSpec::new(
            UbFaultClass::UnreachableOrNoUnwind,
            "entering unreachable code",
            Some("entering unreachable code"),
        )),
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_shift_overflow_ub".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "shift_overflow_ub".to_string(),
        rust_arg_exprs: vec!["1u32".to_string(), "32u32".to_string()],
        lean_args: vec![TraceVal::u32(1), TraceVal::u32(32)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::SyntheticMirAst {
            program_lean_expr: lean_prog_shl_unchecked_ub(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        expected_ub: Some(ExpectedUbSpec::new(
            UbFaultClass::UncheckedShiftOverflow,
            "unchecked_shl",
            Some("unchecked shift overflow"),
        )),
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_div_by_zero_probe".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "div_by_zero_probe".to_string(),
        rust_arg_exprs: vec!["9u32".to_string(), "0u32".to_string()],
        lean_args: vec![TraceVal::u32(9), TraceVal::u32(0)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "div_by_zero_probe".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::Unwind,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_oob_index_probe".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "oob_index_probe".to_string(),
        rust_arg_exprs: vec!["9usize".to_string()],
        lean_args: vec![TraceVal::usize_val(9)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "oob_index_probe".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Unwound,
            "initStateBy unsupported",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_caller_raw_ptr_aliasing_gap".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "caller_raw_ptr_aliasing_gap".to_string(),
        rust_arg_exprs: vec!["7u32".to_string()],
        lean_args: vec![TraceVal::u32(7)],
        ret_shape: ReturnShape::OpaquePtr,
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "caller_raw_ptr_aliasing_gap".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::DisclosedGap,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: Some(DisclosedGapSpec::new(
            DisclosedGapKind::CallerRawPtrAliasing,
            "does not model Rust's pointer aliasing rules",
        )),
    });

    cases
}
