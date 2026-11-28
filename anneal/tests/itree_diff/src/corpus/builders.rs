// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Case builders and hand-written Lean `Trusted.MirAst.Body` programs that
//! `curated_corpus` assembles into trace test cases.

use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn captured_u32_case(
    id: &str,
    category: CaseCategory,
    crate_name: &str,
    src: &str,
    traced_src: Option<&str>,
    fn_name: &str,
    args: &[u32],
    spine_mode: SpineCompareMode,
) -> TraceTestCase {
    TraceTestCase {
        id: id.to_string(),
        category,
        pure_rust_source: src.to_string(),
        traced_rust_source: traced_src.map(ToString::to_string),
        entry_fn: fn_name.to_string(),
        rust_arg_exprs: args.iter().map(|v| format!("{v}u32")).collect(),
        lean_args: args.iter().copied().map(TraceVal::u32).collect(),
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: crate_name.to_string(),
            select_fn: fn_name.to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 512,
        spine_mode,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    }
}

pub(super) fn metamorphic_case(
    id: &str,
    entry_fn: &str,
    inlined_fn: &str,
    args: &[u32],
    captured_callees: Vec<String>,
    caller_lean_body: String,
) -> TraceTestCase {
    TraceTestCase {
        id: id.to_string(),
        category: CaseCategory::MetamorphicInliningDuality,
        pure_rust_source: CAT5_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT5_TRACED_SRC.to_string()),
        entry_fn: entry_fn.to_string(),
        rust_arg_exprs: args.iter().map(|v| format!("{v}u32")).collect(),
        lean_args: args.iter().copied().map(TraceVal::u32).collect(),
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat5_helpers".to_string(),
            captured_callees,
            caller_identity: entry_fn.to_string(),
            caller_lean_body,
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: Some(MetamorphicTwin {
            crate_name: "cat5_inlined".to_string(),
            pure_rust_source: CAT5_INLINED_TWINS_SRC.to_string(),
            entry_fn: inlined_fn.to_string(),
        }),
        env_schedule: EnvSchedule::default(),
        fuel: 512,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    }
}

// ---------------------------------------------------------------------------
// Lean `Trusted.MirAst.Body` definitions for multi-call callers whose callees
// are REAL `anneal-rustc-capture` captured MIR bodies at indices 1, 2, ...
// ---------------------------------------------------------------------------

pub(super) fn lean_body_call_once_and_postprocess() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [
            .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩))
          ],
          terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_call_twice_sequential() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩))
          ],
          terminator := .call 1 [.copy ⟨4, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_call_in_branch_arms() -> String {
    r#"{
      argumentCount := 3,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .bitAnd (.copy ⟨1, []⟩)
              (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .switchInt (.copy ⟨4, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_call_in_bounded_loop_3x() -> String {
    r#"{
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨2, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩] ⟨3, []⟩ (some 2) .continue_ },
        { statements := [],
          terminator := .call 1 [.copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_call_bool_oracle_select() -> String {
    r#"{
      argumentCount := 3,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .bool],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨4, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .switchInt (.copy ⟨4, []⟩) ⟨[(BitVec.ofNat 128 0, 3)], 2⟩ },
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))],
          terminator := .return_ },
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))],
          terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_prog_unwind_cleanup() -> String {
    r#"{
      bodies := [
        {
          argumentCount := 2,
          locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [.storageLive 3],
              terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨3, []⟩ (some 1) (.cleanup 2) },
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩)
                  (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
              ],
              terminator := .return_ },
            { statements := [.nop, .storageDead 3],
              terminator := .unwindResume,
              cleanup := true }
          ],
          identity := "callee_panic_unwind_cleanup"
        },
        {
          argumentCount := 2,
          locals := [.int .i32 false, .int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
              ],
              terminator := .return_ }
          ],
          identity := "ext_may_panic_u32"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#
    .to_string()
}

pub(super) fn lean_body_pipeline_two_helpers() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1
            [.copy ⟨1, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 12)⟩]
            ⟨3, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨3, []⟩, .copy ⟨2, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_diamond_helper_dag() -> String {
    r#"{
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1
            [.copy ⟨1, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 5)⟩]
            ⟨2, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 1
            [.copy ⟨1, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 9)⟩]
            ⟨3, []⟩ (some 2) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_conditional_helper_dispatch() -> String {
    r#"{
      argumentCount := 3,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_stateful_counter_pair() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨2, []⟩)
              (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .call 1 [.copy ⟨3, []⟩, .copy ⟨4, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_body_recursive_depth_2_unroll() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 2)], 3⟩ },
        { statements := [
            .assign ⟨4, []⟩ (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))
          ],
          terminator := .goto 4 },
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩)
              (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .goto 4 },
        { statements := [],
          terminator := .call 1 [.copy ⟨4, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 5) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

pub(super) fn lean_prog_unreachable_ub() -> String {
    r#"{
      bodies := [
        {
          argumentCount := 1,
          locals := [.int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [],
              terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩ },
            { statements := [],
              terminator := .unreachable },
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
                  (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
              ],
              terminator := .return_ }
          ],
          identity := "unreachable_ub"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#
    .to_string()
}

pub(super) fn lean_prog_shl_unchecked_ub() -> String {
    r#"{
      bodies := [
        {
          argumentCount := 2,
          locals := [.int .i32 false, .int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .shlUnchecked (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
              ],
              terminator := .return_ }
          ],
          identity := "shift_overflow_ub"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#
    .to_string()
}
