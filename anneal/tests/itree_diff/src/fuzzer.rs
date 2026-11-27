// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Seeded deterministic multi-call program generator and structured mutators
//! (`CallBoundaryOutliner`, `BranchLoopWeaver`, `PaddingPerturber`,
//! `MultiCallChainMutator`, `UnwindCleanupInjector`).
//!
//! Each generated [`FuzzProgram`] compiles cleanly to:
//! 1. Traced standalone Rust source for `rustc -O0`, `rustc -O2`, and `miri`,
//! 2. Real `anneal-rustc-capture` leaf helper bodies + multi-call caller
//!    `Trusted.MirAst.Body` for Lean Mode (a)/(b), and
//! 3. A source-inlined single-body Rust twin for full-authority metamorphic
//!    inlining duality verification.

use std::fmt::Write as _;

use serde::{Deserialize, Serialize};

use crate::{
    outcome::{IntKind, SpineCompareMode, TraceVal},
    spec::{
        CaseCategory, ExpectedCaseClass, LeanProgramSpec, MetamorphicTwin, ReturnShape,
        TraceTestCase,
    },
    trace_observer::{EnvAction, EnvSchedule},
};

/// Deterministic SplitMix64 PRNG (zero external RNG crate required).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DeterministicRng {
    state: u64,
}

impl DeterministicRng {
    pub fn new(seed: u64) -> Self {
        Self { state: seed ^ 0x9E37_79B9_7F4A_7C15 }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }

    pub fn gen_range(&mut self, upper: usize) -> usize {
        if upper == 0 { 0 } else { (self.next_u64() as usize) % upper }
    }

    pub fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }
}

/// Binary operation step inside a generated program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FuzzArithOp {
    Add,
    Sub,
    Xor,
    BitOr,
    BitAndMask,
}

impl FuzzArithOp {
    fn rust_expr(self, lhs: &str, rhs: &str) -> String {
        match self {
            Self::Add => format!("({lhs}.wrapping_add({rhs}))"),
            Self::Sub => format!("({lhs}.wrapping_sub({rhs}))"),
            Self::Xor => format!("({lhs} ^ {rhs})"),
            Self::BitOr => format!("({lhs} | {rhs})"),
            Self::BitAndMask => format!("(({lhs} & 0xFFFFu32).wrapping_add({rhs}))"),
        }
    }

    fn pure_rust_expr(self, lhs: &str, rhs: &str) -> String {
        match self {
            Self::Add => format!("({lhs} + {rhs})"),
            Self::Sub => format!("({lhs} - {rhs})"),
            Self::Xor => format!("({lhs} ^ {rhs})"),
            Self::BitOr => format!("({lhs} | {rhs})"),
            Self::BitAndMask => format!("(({lhs} & 0xFFFFu32) + {rhs})"),
        }
    }

    pub(crate) fn lean_binop(self) -> &'static str {
        match self {
            Self::Add => ".add",
            Self::Sub => ".sub",
            Self::Xor => ".bitXor",
            Self::BitOr => ".bitOr",
            Self::BitAndMask => ".add",
        }
    }
}

/// Structured step in a [`FuzzProgram`] sequence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "step", rename_all = "snake_case")]
pub enum FuzzStep {
    /// Local scalar arithmetic updating accumulator (`acc = op(acc, imm)`).
    ArithImm { op: FuzzArithOp, imm: u32 },
    /// Call to captured helper `fuzz_helper_k(acc, arg2)` where `callee_idx`
    /// selects one of the captured helper functions (`0..3`).
    HelperCall { callee_idx: usize, bias: u32 },
    /// Conditional branch switching on `(acc & 1)`: executes `then_op` vs
    /// `else_op`.
    BranchMix { then_imm: u32, else_imm: u32 },
    /// Bounded loop iterating `iters` (`1..=4`) times applying `step_imm`.
    BoundedLoop { iters: u32, step_imm: u32 },
    /// Padding-carrier round-trip exercised in Rust/Miri via `offset_of!`
    /// `TraceCapture`, preserving value semantics across Lean.
    PaddedRoundTrip { tag_byte: u8 },
    /// Conditional unwind edge with RAII cleanup guard (`trigger_unwind`).
    UnwindProbe { trigger_unwind: bool },
}

/// Named structured mutators applied to [`FuzzProgram`]s.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MutatorKind {
    CallBoundaryOutliner,
    BranchLoopWeaver,
    PaddingPerturber,
    MultiCallChainMutator,
    UnwindCleanupInjector,
}

impl MutatorKind {
    pub const ALL: [Self; 5] = [
        Self::CallBoundaryOutliner,
        Self::BranchLoopWeaver,
        Self::PaddingPerturber,
        Self::MultiCallChainMutator,
        Self::UnwindCleanupInjector,
    ];
}

/// Maximum structured step count permitted in a persisted or generated
/// [`FuzzProgram`] seed so preflight bounds total execution within Lean fuel.
pub const MAX_FUZZ_PROGRAM_STEPS: usize = 32;

/// Minimum iteration bound permitted on [`FuzzStep::BoundedLoop`].
pub const MIN_FUZZ_BOUNDED_LOOP_ITERS: u32 = 1;

/// Maximum iteration bound permitted on [`FuzzStep::BoundedLoop`].
pub const MAX_FUZZ_BOUNDED_LOOP_ITERS: u32 = 4;

/// Number of captured `fuzz_helper_k` definitions emitted by [`FuzzProgram`].
pub const NUM_FUZZ_HELPERS: usize = 3;

/// Complete structured representation of a generated multi-call fuzz program.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzProgram {
    pub seed: u64,
    pub index: usize,
    pub input_x: u32,
    pub input_y: u32,
    pub steps: Vec<FuzzStep>,
    pub applied_mutators: Vec<MutatorKind>,
}

impl FuzzProgram {
    /// Enforce structural seed invariants on step counts, `BoundedLoop`
    /// iteration bounds (`1..=4`), `HelperCall` callee indices (`0..3`), and
    /// mutator history length before lowering/execution.
    pub fn validate(&self) -> Result<(), String> {
        let case_id = format!("fuzz_s{}_i{:03}", self.seed, self.index);
        if self.steps.len() > MAX_FUZZ_PROGRAM_STEPS {
            return Err(format!(
                "FuzzProgram `{case_id}` step count {} exceeds limit {MAX_FUZZ_PROGRAM_STEPS}",
                self.steps.len()
            ));
        }
        if self.applied_mutators.len() > MAX_FUZZ_PROGRAM_STEPS {
            return Err(format!(
                "FuzzProgram `{case_id}` applied_mutators count {} exceeds limit {MAX_FUZZ_PROGRAM_STEPS}",
                self.applied_mutators.len()
            ));
        }
        for (idx, step) in self.steps.iter().enumerate() {
            match step {
                FuzzStep::BoundedLoop { iters, .. }
                    if !(MIN_FUZZ_BOUNDED_LOOP_ITERS..=MAX_FUZZ_BOUNDED_LOOP_ITERS)
                        .contains(iters) =>
                {
                    return Err(format!(
                        "FuzzProgram `{case_id}` step {idx} BoundedLoop iters={iters} outside allowed range {MIN_FUZZ_BOUNDED_LOOP_ITERS}..={MAX_FUZZ_BOUNDED_LOOP_ITERS}"
                    ));
                }
                FuzzStep::HelperCall { callee_idx, .. } if *callee_idx >= NUM_FUZZ_HELPERS => {
                    return Err(format!(
                        "FuzzProgram `{case_id}` step {idx} HelperCall callee_idx={callee_idx} outside allowed range 0..{NUM_FUZZ_HELPERS}"
                    ));
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Deterministically generate one initial multi-call fuzz program from
    /// `rng`, applying 1..=2 structured mutators.
    pub fn generate(seed: u64, index: usize, rng: &mut DeterministicRng) -> Self {
        let input_x = rng.next_u32() & 0xFFFF;
        let input_y = (rng.next_u32() & 0x0FFF).wrapping_add(1);
        let init_len = 1 + rng.gen_range(3);
        let mut steps = Vec::with_capacity(init_len + 3);
        for _ in 0..init_len {
            let op = pick_op(rng);
            let imm = (rng.next_u32() & 0xFF).wrapping_add(1);
            steps.push(FuzzStep::ArithImm { op, imm });
        }

        let mut prog = Self { seed, index, input_x, input_y, steps, applied_mutators: Vec::new() };

        let primary = MutatorKind::ALL[index % MutatorKind::ALL.len()];
        prog.apply_mutator(primary, rng);
        let secondary = MutatorKind::ALL[(index + 1 + rng.gen_range(4)) % MutatorKind::ALL.len()];
        if secondary != primary && secondary != MutatorKind::UnwindCleanupInjector {
            prog.apply_mutator(secondary, rng);
        }
        prog
    }

    /// Apply one named structured mutator to `self`.
    pub fn apply_mutator(&mut self, mutator: MutatorKind, rng: &mut DeterministicRng) {
        self.applied_mutators.push(mutator);
        match mutator {
            MutatorKind::CallBoundaryOutliner => {
                let callee_idx = rng.gen_range(3);
                let bias = (rng.next_u32() & 0x7F).wrapping_add(1);
                if let Some(pos) =
                    self.steps.iter().position(|s| matches!(s, FuzzStep::ArithImm { .. }))
                {
                    self.steps[pos] = FuzzStep::HelperCall { callee_idx, bias };
                } else {
                    self.steps.push(FuzzStep::HelperCall { callee_idx, bias });
                }
            }
            MutatorKind::BranchLoopWeaver => {
                if rng.gen_bool() {
                    let then_imm = (rng.next_u32() & 0x3F).wrapping_add(3);
                    let else_imm = (rng.next_u32() & 0x3F).wrapping_add(7);
                    self.steps.push(FuzzStep::BranchMix { then_imm, else_imm });
                } else {
                    let iters = 1 + (rng.next_u32() % 4);
                    let step_imm = (rng.next_u32() & 0x1F).wrapping_add(1);
                    self.steps.push(FuzzStep::BoundedLoop { iters, step_imm });
                }
            }
            MutatorKind::PaddingPerturber => {
                let tag_byte = (rng.next_u32() & 0xFF) as u8;
                self.steps.push(FuzzStep::PaddedRoundTrip { tag_byte });
            }
            MutatorKind::MultiCallChainMutator => {
                let chain_len = 2 + rng.gen_range(2);
                for _ in 0..chain_len {
                    let callee_idx = rng.gen_range(3);
                    let bias = (rng.next_u32() & 0x3F).wrapping_add(1);
                    self.steps.push(FuzzStep::HelperCall { callee_idx, bias });
                }
            }
            MutatorKind::UnwindCleanupInjector => {
                let trigger_unwind = self.index.is_multiple_of(2);
                self.steps.push(FuzzStep::UnwindProbe { trigger_unwind });
            }
        }
    }

    pub fn has_triggering_unwind(&self) -> bool {
        self.steps.iter().any(|s| matches!(s, FuzzStep::UnwindProbe { trigger_unwind: true }))
    }

    pub fn has_helper_calls(&self) -> bool {
        self.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { .. }))
    }

    /// Lower this [`FuzzProgram`] into an executable [`TraceTestCase`] ready
    /// for 4-way differential testing (`rustc O0/O2`, `miri`, Lean Mode
    /// (a)/(b), and source-inlined metamorphic duality when non-unwinding).
    pub fn to_trace_test_case(&self) -> TraceTestCase {
        let id = format!("fuzz_s{}_i{:03}", self.seed, self.index);
        let helpers_pure = FUZZ_HELPERS_PURE_SRC.to_string();
        let traced_rust = self.render_traced_rust();
        let caller_lean_body = self.render_lean_caller_body();
        let has_unwind = self.has_triggering_unwind();

        let mut env_schedule = EnvSchedule::default();
        let mut external_callees = Vec::new();
        if has_unwind {
            external_callees.push("fuzz_ext_unwind".to_string());
            env_schedule.push_callee(
                "fuzz_ext_unwind",
                EnvAction::Unwind { message: "fuzz injected unwind".to_string() },
            );
        }

        let twin = if !has_unwind {
            Some(MetamorphicTwin {
                crate_name: format!("fuzz_twin_{}", self.index),
                pure_rust_source: self.render_inlined_pure_rust(),
                entry_fn: "fuzz_entry_inlined".to_string(),
            })
        } else {
            None
        };

        let captured_callees = vec![
            "fuzz_helper_0".to_string(),
            "fuzz_helper_1".to_string(),
            "fuzz_helper_2".to_string(),
            "fuzz_ext_unwind".to_string(),
            "fuzz_ext_probe".to_string(),
        ];

        TraceTestCase {
            id,
            category: CaseCategory::FuzzGenerated,
            pure_rust_source: helpers_pure,
            traced_rust_source: Some(traced_rust),
            entry_fn: "fuzz_entry".to_string(),
            rust_arg_exprs: vec![format!("{}u32", self.input_x), format!("{}u32", self.input_y)],
            lean_args: vec![TraceVal::u32(self.input_x), TraceVal::u32(self.input_y)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
                crate_name: "fuzz_helpers".to_string(),
                captured_callees,
                caller_identity: "fuzz_entry".to_string(),
                caller_lean_body,
                external_callees,
            },
            metamorphic_inlined_twin: twin,
            env_schedule,
            fuel: 1024,
            spine_mode: SpineCompareMode::ObsErasedCallsOnly,
            expected_class: if has_unwind {
                ExpectedCaseClass::Unwind
            } else {
                ExpectedCaseClass::Agree
            },
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        }
    }

    fn render_traced_rust(&self) -> String {
        let mut out = String::from(
            r#"
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FuzzPaddedCarrier {
    pub tag: u8,
    pub payload: u32,
}

impl anneal_rt::TraceCapture for FuzzPaddedCarrier {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let o0 = core::mem::offset_of!(FuzzPaddedCarrier, tag);
        self.tag.write_captured_bytes(&mut dst[o0..o0 + 1]);
        let o1 = core::mem::offset_of!(FuzzPaddedCarrier, payload);
        self.payload.write_captured_bytes(&mut dst[o1..o1 + 4]);
    }
    fn trace_repr(&self) -> String {
        format!("FuzzPaddedCarrier({},{})", self.tag, self.payload)
    }
}

#[inline(never)]
pub fn fuzz_helper_0(a: u32, b: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "fuzz_helper_0",
        vec![anneal_rt::capture_value_bytes(&a), anneal_rt::capture_value_bytes(&b)],
        vec![format!("{a}"), format!("{b}")],
        || a.wrapping_mul(3).wrapping_add(b),
    )
}

#[inline(never)]
pub fn fuzz_helper_1(a: u32, b: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "fuzz_helper_1",
        vec![anneal_rt::capture_value_bytes(&a), anneal_rt::capture_value_bytes(&b)],
        vec![format!("{a}"), format!("{b}")],
        || (a ^ b).wrapping_add(17),
    )
}

#[inline(never)]
pub fn fuzz_helper_2(a: u32, b: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "fuzz_helper_2",
        vec![anneal_rt::capture_value_bytes(&a), anneal_rt::capture_value_bytes(&b)],
        vec![format!("{a}"), format!("{b}")],
        || {
            if a >= b {
                a.wrapping_sub(b).wrapping_add(5)
            } else {
                b.wrapping_sub(a).wrapping_add(9)
            }
        },
    )
}

#[inline(never)]
pub fn fuzz_ext_unwind(v: u32, trigger: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "fuzz_ext_unwind",
        vec![anneal_rt::capture_value_bytes(&v), anneal_rt::capture_value_bytes(&trigger)],
        vec![format!("{v}"), format!("{trigger}")],
        || {
            if trigger != 0 {
                panic!("fuzz injected unwind");
            }
            v.wrapping_add(1)
        },
    )
}

#[inline(never)]
pub fn fuzz_ext_probe(v: u32, trigger: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "fuzz_ext_probe",
        vec![anneal_rt::capture_value_bytes(&v), anneal_rt::capture_value_bytes(&trigger)],
        vec![format!("{v}"), format!("{trigger}")],
        || {
            if trigger != 0 {
                panic!("fuzz injected unwind");
            }
            v.wrapping_add(1)
        },
    )
}

#[inline(never)]
pub fn fuzz_entry(x: u32, y: u32) -> u32 {
    let mut acc: u32 = x.wrapping_add(y);
    let sentinel: u32 = x ^ 0xA5A5u32;
    let mut live_carrier = FuzzPaddedCarrier { tag: (x & 0xFF) as u8, payload: sentinel };
    let live_ptr: *mut FuzzPaddedCarrier = std::hint::black_box(&mut live_carrier);
"#,
        );

        for (i, step) in self.steps.iter().enumerate() {
            match step {
                FuzzStep::ArithImm { op, imm } => {
                    let expr = op.rust_expr("acc", &format!("{imm}u32"));
                    let _ = writeln!(out, "    acc = {expr};");
                }
                FuzzStep::HelperCall { callee_idx, bias } => {
                    let h = callee_idx % 3;
                    let _ = writeln!(
                        out,
                        "    let pre_{i} = unsafe {{ anneal_rt::capture_value_bytes(&*std::hint::black_box(live_ptr)) }};"
                    );
                    let _ =
                        writeln!(out, "    acc = fuzz_helper_{h}(acc, y.wrapping_add({bias}u32));");
                    let _ = writeln!(
                        out,
                        "    let post_{i} = unsafe {{ anneal_rt::capture_value_bytes(&*std::hint::black_box(live_ptr)) }};"
                    );
                    let _ = writeln!(
                        out,
                        "    assert_eq!(pre_{i}, post_{i}, \"caller stack carrier mutated across fuzz_helper_{h}\");"
                    );
                    let _ = writeln!(
                        out,
                        "    assert!(post_{i}[1].is_none() && post_{i}[2].is_none() && post_{i}[3].is_none());"
                    );
                }
                FuzzStep::BranchMix { then_imm, else_imm } => {
                    let _ = writeln!(
                        out,
                        "    if (acc & 1u32) == 0u32 {{ acc = acc.wrapping_add({then_imm}u32); }} else {{ acc = acc ^ {else_imm}u32; }}"
                    );
                }
                FuzzStep::BoundedLoop { iters, step_imm } => {
                    let _ = writeln!(out, "    let mut k_{i}: u32 = 0u32;");
                    let _ = writeln!(out, "    while k_{i} < {iters}u32 {{");
                    let _ = writeln!(
                        out,
                        "        acc = acc.wrapping_add(k_{i}.wrapping_mul({step_imm}u32).wrapping_add(1u32));"
                    );
                    let _ = writeln!(out, "        k_{i} = k_{i}.wrapping_add(1u32);");
                    let _ = writeln!(out, "    }}");
                }
                FuzzStep::PaddedRoundTrip { tag_byte } => {
                    let _ = writeln!(
                        out,
                        "    let carrier_{i} = FuzzPaddedCarrier {{ tag: {tag_byte}u8, payload: acc }};"
                    );
                    let _ = writeln!(
                        out,
                        "    let bytes_{i} = anneal_rt::capture_value_bytes(&carrier_{i});"
                    );
                    let _ = writeln!(
                        out,
                        "    assert!(bytes_{i}[1].is_none() && bytes_{i}[2].is_none() && bytes_{i}[3].is_none());"
                    );
                    let _ = writeln!(
                        out,
                        "    acc = carrier_{i}.payload.wrapping_add(carrier_{i}.tag as u32);"
                    );
                }
                FuzzStep::UnwindProbe { trigger_unwind } => {
                    let (helper_fn, trig) = if *trigger_unwind {
                        ("fuzz_ext_unwind", 1u32)
                    } else {
                        ("fuzz_ext_probe", 0u32)
                    };
                    let _ =
                        writeln!(out, "    struct DropGuard_{i}(*const FuzzPaddedCarrier, u32);");
                    let _ = writeln!(
                        out,
                        "    impl Drop for DropGuard_{i} {{ fn drop(&mut self) {{ let cur = unsafe {{ (*std::hint::black_box(self.0)).payload }}; assert_eq!(cur, self.1); }} }}"
                    );
                    let _ = writeln!(
                        out,
                        "    let _g_{i} = DropGuard_{i}(live_ptr.cast_const(), sentinel);"
                    );
                    let _ = writeln!(out, "    acc = {helper_fn}(acc, {trig}u32);");
                }
            }
        }
        out.push_str(
            "    let final_sentinel = unsafe { (*std::hint::black_box(live_ptr)).payload };\n    acc ^ final_sentinel\n}\n",
        );
        out
    }

    fn render_inlined_pure_rust(&self) -> String {
        let mut out = String::from(
            "#![no_std]\n\n#[inline(never)]\npub fn fuzz_entry_inlined(x: u32, y: u32) -> u32 {\n    let mut acc: u32 = x + y;\n    let sentinel: u32 = x ^ 0xA5A5u32;\n",
        );
        for (i, step) in self.steps.iter().enumerate() {
            match step {
                FuzzStep::ArithImm { op, imm } => {
                    let expr = op.pure_rust_expr("acc", &format!("{imm}u32"));
                    let _ = writeln!(out, "    acc = {expr};");
                }
                FuzzStep::HelperCall { callee_idx, bias } => {
                    let _ = writeln!(out, "    let arg_{i} = y + {bias}u32;");
                    match callee_idx % 3 {
                        0 => {
                            let _ = writeln!(out, "    acc = (acc * 3u32) + arg_{i};");
                        }
                        1 => {
                            let _ = writeln!(out, "    acc = (acc ^ arg_{i}) + 17u32;");
                        }
                        _ => {
                            let _ = writeln!(
                                out,
                                "    acc = if acc >= arg_{i} {{ (acc - arg_{i}) + 5u32 }} else {{ (arg_{i} - acc) + 9u32 }};"
                            );
                        }
                    }
                }
                FuzzStep::BranchMix { then_imm, else_imm } => {
                    let _ = writeln!(
                        out,
                        "    if (acc & 1u32) == 0u32 {{ acc = acc + {then_imm}u32; }} else {{ acc = acc ^ {else_imm}u32; }}"
                    );
                }
                FuzzStep::BoundedLoop { iters, step_imm } => {
                    let _ = writeln!(out, "    let mut k_{i}: u32 = 0u32;");
                    let _ = writeln!(out, "    while k_{i} < {iters}u32 {{");
                    let _ = writeln!(out, "        acc = acc + ((k_{i} * {step_imm}u32) + 1u32);");
                    let _ = writeln!(out, "        k_{i} = k_{i} + 1u32;");
                    let _ = writeln!(out, "    }}");
                }
                FuzzStep::PaddedRoundTrip { tag_byte } => {
                    let _ = writeln!(out, "    acc = acc + ({tag_byte}u32);");
                }
                FuzzStep::UnwindProbe { trigger_unwind } => {
                    if !*trigger_unwind {
                        let _ = writeln!(out, "    acc = acc + 1u32;");
                    }
                }
            }
        }
        out.push_str("    acc ^ sentinel\n}\n");
        out
    }

    /// Lower one shared pure intra-body `FuzzStep` into `cur_stmts` /
    /// `blocks` (`ArithImm`, `BranchMix`, `BoundedLoop`, `PaddedRoundTrip`).
    fn push_common_lean_step(
        step: &FuzzStep,
        cur_stmts: &mut Vec<String>,
        blocks: &mut Vec<String>,
    ) -> bool {
        match step {
            FuzzStep::ArithImm { op, imm } => {
                if *op == FuzzArithOp::BitAndMask {
                    cur_stmts.push(
                        ".assign ⟨5, []⟩ (.binaryOp .bitAnd (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 65535)⟩))"
                            .to_string(),
                    );
                    cur_stmts.push(format!(
                        ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {imm})⟩))"
                    ));
                } else {
                    cur_stmts.push(format!(
                        ".assign ⟨3, []⟩ (.binaryOp {} (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {imm})⟩))",
                        op.lean_binop()
                    ));
                }
                true
            }
            FuzzStep::BranchMix { then_imm, else_imm } => {
                cur_stmts.push(
                    ".assign ⟨5, []⟩ (.binaryOp .bitAnd (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))"
                        .to_string(),
                );
                let then_bb = blocks.len() + 1;
                let else_bb = blocks.len() + 2;
                let join_bb = blocks.len() + 3;
                blocks.push(format!(
                    "{{ statements := [{}], terminator := .switchInt (.copy ⟨5, []⟩) ⟨[(BitVec.ofNat 128 0, {then_bb})], {else_bb}⟩ }}",
                    cur_stmts.join(", ")
                ));
                cur_stmts.clear();
                blocks.push(format!(
                    "{{ statements := [.assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {then_imm})⟩))], terminator := .goto {join_bb} }}"
                ));
                blocks.push(format!(
                    "{{ statements := [.assign ⟨3, []⟩ (.binaryOp .bitXor (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {else_imm})⟩))], terminator := .goto {join_bb} }}"
                ));
                true
            }
            FuzzStep::BoundedLoop { iters, step_imm } => {
                cur_stmts.push(
                    ".assign ⟨6, []⟩ (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))"
                        .to_string(),
                );
                let header_bb = blocks.len() + 1;
                let body_bb = blocks.len() + 2;
                let exit_bb = blocks.len() + 3;
                blocks.push(format!(
                    "{{ statements := [{}], terminator := .goto {header_bb} }}",
                    cur_stmts.join(", ")
                ));
                cur_stmts.clear();
                blocks.push(format!(
                    "{{ statements := [.assign ⟨7, []⟩ (.binaryOp .lt (.copy ⟨6, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {iters})⟩))], terminator := .switchInt (.copy ⟨7, []⟩) ⟨[(BitVec.ofNat 128 0, {exit_bb})], {body_bb}⟩ }}"
                ));
                blocks.push(format!(
                    "{{ statements := [\
                        .assign ⟨5, []⟩ (.binaryOp .mul (.copy ⟨6, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {step_imm})⟩)), \
                        .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩)), \
                        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)), \
                        .assign ⟨6, []⟩ (.binaryOp .add (.copy ⟨6, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))\
                    ], terminator := .goto {header_bb} }}"
                ));
                true
            }
            FuzzStep::PaddedRoundTrip { tag_byte } => {
                cur_stmts.push(format!(
                    ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {tag_byte})⟩))"
                ));
                true
            }
            FuzzStep::HelperCall { .. } | FuzzStep::UnwindProbe { .. } => false,
        }
    }

    /// Lower the caller function directly to a `Trusted.MirAst.Body` whose
    /// `TerminatorKind.call` instructions target the REAL captured helper
    /// bodies at DefIds `1 = fuzz_helper_0`, `2 = fuzz_helper_1`,
    /// `3 = fuzz_helper_2`, `4 = fuzz_ext_unwind`, `5 = fuzz_ext_probe`.
    fn render_lean_caller_body(&self) -> String {
        let mut blocks: Vec<String> = Vec::new();
        let mut cur_stmts: Vec<String> = vec![
            ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))".to_string(),
            ".assign ⟨4, []⟩ (.binaryOp .bitXor (.copy ⟨1, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 42405)⟩))".to_string(),
        ];

        for step in &self.steps {
            if Self::push_common_lean_step(step, &mut cur_stmts, &mut blocks) {
                continue;
            }
            match step {
                FuzzStep::HelperCall { callee_idx, bias } => {
                    let callee_def_id = 1 + (callee_idx % 3);
                    cur_stmts.push(format!(
                        ".assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {bias})⟩))"
                    ));
                    let next_bb = blocks.len() + 1;
                    blocks.push(format!(
                        "{{ statements := [{}], terminator := .call {callee_def_id} [.copy ⟨3, []⟩, .copy ⟨5, []⟩] ⟨3, []⟩ (some {next_bb}) .continue_ }}",
                        cur_stmts.join(", ")
                    ));
                    cur_stmts.clear();
                }
                FuzzStep::UnwindProbe { trigger_unwind } => {
                    let (callee_def_id, trig) =
                        if *trigger_unwind { (4usize, 1u32) } else { (5usize, 0u32) };
                    let resume_bb = blocks.len() + 1;
                    let cleanup_bb = blocks.len() + 2;
                    let after_bb = blocks.len() + 3;
                    blocks.push(format!(
                        "{{ statements := [{}], terminator := .call {callee_def_id} [.copy ⟨3, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {trig})⟩] ⟨3, []⟩ (some {resume_bb}) (.cleanup {cleanup_bb}) }}",
                        cur_stmts.join(", ")
                    ));
                    cur_stmts.clear();
                    blocks.push(format!("{{ statements := [], terminator := .goto {after_bb} }}"));
                    blocks.push(
                        "{ statements := [.nop], terminator := .unwindResume, cleanup := true }"
                            .to_string(),
                    );
                }
                _ => unreachable!("handled by push_common_lean_step"),
            }
        }

        cur_stmts.push(
            ".assign ⟨0, []⟩ (.binaryOp .bitXor (.copy ⟨3, []⟩) (.copy ⟨4, []⟩))".to_string(),
        );
        blocks.push(format!(
            "{{ statements := [{}], terminator := .return_ }}",
            cur_stmts.join(", ")
        ));

        format!(
            "{{\n  argumentCount := 2,\n  locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .bool],\n  basicBlocks := [{}]\n}}",
            blocks.join(", ")
        )
    }

    /// Lower the source-inlined twin directly to a standalone
    /// `Trusted.MirAst.Body` matching `render_inlined_pure_rust` (zero
    /// external `.call` instructions so Lean `StrictVerbatim` can execute
    /// it verbatim alongside `CompositionalITree`).
    pub(crate) fn render_lean_inlined_body(&self) -> String {
        let mut blocks: Vec<String> = Vec::new();
        let mut cur_stmts: Vec<String> = vec![
            ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))".to_string(),
            ".assign ⟨4, []⟩ (.binaryOp .bitXor (.copy ⟨1, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 42405)⟩))".to_string(),
        ];

        for step in &self.steps {
            if Self::push_common_lean_step(step, &mut cur_stmts, &mut blocks) {
                continue;
            }
            match step {
                FuzzStep::HelperCall { callee_idx, bias } => {
                    cur_stmts.push(format!(
                        ".assign ⟨8, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {bias})⟩))"
                    ));
                    match callee_idx % 3 {
                        0 => {
                            cur_stmts.push(
                                ".assign ⟨5, []⟩ (.binaryOp .mul (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 3)⟩))"
                                    .to_string(),
                            );
                            cur_stmts.push(
                                ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.copy ⟨8, []⟩))"
                                    .to_string(),
                            );
                        }
                        1 => {
                            cur_stmts.push(
                                ".assign ⟨5, []⟩ (.binaryOp .bitXor (.copy ⟨3, []⟩) (.copy ⟨8, []⟩))"
                                    .to_string(),
                            );
                            cur_stmts.push(
                                ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 17)⟩))"
                                    .to_string(),
                            );
                        }
                        _ => {
                            cur_stmts.push(
                                ".assign ⟨7, []⟩ (.binaryOp .ge (.copy ⟨3, []⟩) (.copy ⟨8, []⟩))"
                                    .to_string(),
                            );
                            let then_bb = blocks.len() + 1;
                            let else_bb = blocks.len() + 2;
                            let join_bb = blocks.len() + 3;
                            blocks.push(format!(
                                "{{ statements := [{}], terminator := .switchInt (.copy ⟨7, []⟩) ⟨[(BitVec.ofNat 128 0, {else_bb})], {then_bb}⟩ }}",
                                cur_stmts.join(", ")
                            ));
                            cur_stmts.clear();
                            blocks.push(format!(
                                "{{ statements := [\
                                    .assign ⟨5, []⟩ (.binaryOp .sub (.copy ⟨3, []⟩) (.copy ⟨8, []⟩)), \
                                    .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 5)⟩))\
                                ], terminator := .goto {join_bb} }}"
                            ));
                            blocks.push(format!(
                                "{{ statements := [\
                                    .assign ⟨5, []⟩ (.binaryOp .sub (.copy ⟨8, []⟩) (.copy ⟨3, []⟩)), \
                                    .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 9)⟩))\
                                ], terminator := .goto {join_bb} }}"
                            ));
                        }
                    }
                }
                FuzzStep::UnwindProbe { trigger_unwind } => {
                    if *trigger_unwind {
                        blocks.push(format!(
                            "{{ statements := [{}], terminator := .unsupported }}",
                            cur_stmts.join(", ")
                        ));
                        cur_stmts.clear();
                    } else {
                        cur_stmts.push(
                            ".assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))"
                                .to_string(),
                        );
                    }
                }
                _ => unreachable!("handled by push_common_lean_step"),
            }
        }

        cur_stmts.push(
            ".assign ⟨0, []⟩ (.binaryOp .bitXor (.copy ⟨3, []⟩) (.copy ⟨4, []⟩))".to_string(),
        );
        blocks.push(format!(
            "{{ statements := [{}], terminator := .return_ }}",
            cur_stmts.join(", ")
        ));

        format!(
            "{{\n  argumentCount := 2,\n  locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .bool, .int .i32 false],\n  basicBlocks := [{}]\n}}",
            blocks.join(", ")
        )
    }
}

/// Generate a deterministic batch of `count` multi-call fuzz programs from
/// `seed`.
pub fn generate_fuzz_batch(seed: u64, count: usize) -> Vec<FuzzProgram> {
    let mut rng = DeterministicRng::new(seed);
    (0..count).map(|i| FuzzProgram::generate(seed, i, &mut rng)).collect()
}

fn pick_op(rng: &mut DeterministicRng) -> FuzzArithOp {
    match rng.gen_range(5) {
        0 => FuzzArithOp::Add,
        1 => FuzzArithOp::Sub,
        2 => FuzzArithOp::Xor,
        3 => FuzzArithOp::BitOr,
        _ => FuzzArithOp::BitAndMask,
    }
}

const FUZZ_HELPERS_PURE_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn fuzz_helper_0(a: u32, b: u32) -> u32 {
    (a * 3) + b
}

#[inline(never)]
pub fn fuzz_helper_1(a: u32, b: u32) -> u32 {
    (a ^ b) + 17
}

#[inline(never)]
pub fn fuzz_helper_2(a: u32, b: u32) -> u32 {
    if a >= b {
        (a - b) + 5
    } else {
        (b - a) + 9
    }
}

#[inline(never)]
pub fn fuzz_ext_unwind(v: u32, _trigger: u32) -> u32 {
    v + 1
}

#[inline(never)]
pub fn fuzz_ext_probe(v: u32, _trigger: u32) -> u32 {
    v + 1
}
"#;
