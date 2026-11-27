// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared differential test-case specification and standalone Rust/Miri harness
//! rendering helpers.

use std::fmt::Write as _;

use serde::{Deserialize, Serialize};

use crate::{
    outcome::{
        AuthorityRunResult, CallerFrameLaw, DisclosedGapSpec, ExpectedConservativeSpec,
        ExpectedUbSpec, IntKind, OrderingVal, SpineCompareMode, TerminalOutcome, TraceVal,
        compute_boundary_mem_digest, is_rust_scheduled_return_decode_fault,
        validate_boundary_slots_for_outcome,
    },
    trace_observer::{
        EnvAction, EnvSchedule, ObservableEvent, ObservableSpine, PRE_ABORT_JSON_PREFIX,
        PRE_ENTRY_JSON_PREFIX, render_embedded_trace_prelude,
    },
};

/// Prefix marking the structured JSON result line emitted by standalone
/// `rustc` and `miri` execution harnesses.
pub const TRACE_JSON_PREFIX: &str = "ANNEAL_ITREE_TRACE_JSON:";

/// High-level corpus or fuzzer category.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CaseCategory {
    ScalarBitwise,
    PaddedAggregatesAndEnums,
    BranchLoopCfg,
    MultiCallChain,
    MetamorphicInliningDuality,
    NegativeUbAndOverApprox,
    FuzzGenerated,
}

/// Return type shape used to serialize return values from generated Rust/Miri
/// binaries into canonical [`TraceVal`] JSON.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "shape", rename_all = "snake_case")]
pub enum ReturnShape {
    Scalar { kind: IntKind },
    Bool,
    Char,
    Ordering,
    Unit,
    PaddedStruct { type_name: String },
    OpaquePtr,
}

impl ReturnShape {
    /// Render a Rust expression that converts `ret_var` into a JSON string
    /// matching [`TraceVal`].
    pub fn render_rust_to_json_expr(&self, ret_var: &str) -> String {
        match self {
            Self::Scalar { kind } => {
                let kind_name = kind.rust_name();
                let bits_expr = match kind {
                    IntKind::U8 => format!("{ret_var} as u128"),
                    IntKind::U16 => format!("{ret_var} as u128"),
                    IntKind::U32 => format!("{ret_var} as u128"),
                    IntKind::U64 => format!("{ret_var} as u128"),
                    IntKind::U128 => ret_var.to_owned(),
                    IntKind::Usize => format!("{ret_var} as u128"),
                    IntKind::I8 => format!("({ret_var} as u8) as u128"),
                    IntKind::I16 => format!("({ret_var} as u16) as u128"),
                    IntKind::I32 => format!("({ret_var} as u32) as u128"),
                    IntKind::I64 => format!("({ret_var} as u64) as u128"),
                    IntKind::I128 => format!("{ret_var} as u128"),
                    IntKind::Isize => format!("({ret_var} as usize) as u128"),
                };
                format!("anneal_rt::json_scalar(\"{kind_name}\", {bits_expr})")
            }
            Self::Bool => format!("anneal_rt::json_bool({ret_var})"),
            Self::Char => format!("anneal_rt::json_char({ret_var})"),
            Self::Ordering => format!("anneal_rt::json_ordering({ret_var})"),
            Self::Unit => format!("{{ let () = {ret_var}; anneal_rt::json_unit() }}"),
            Self::PaddedStruct { type_name } => {
                format!("anneal_rt::json_padded({type_name:?}, &{ret_var})")
            }
            Self::OpaquePtr => {
                format!("anneal_rt::json_scalar(\"usize\", ({ret_var} as usize != 0) as u128)")
            }
        }
    }

    /// Render a Rust expression capturing canonical layout-aware post-execution
    /// return bytes (`Vec<Option<u8>>`) for `boundary_slots` `mem_digest`.
    pub fn render_rust_ret_bytes_expr(&self, ret_var: &str) -> String {
        match self {
            Self::Scalar { .. }
            | Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::PaddedStruct { .. } => {
                format!("anneal_rt::capture_value_bytes(&{ret_var})")
            }
            Self::OpaquePtr => {
                format!("anneal_rt::capture_value_bytes(&(({ret_var} as usize != 0) as usize))")
            }
        }
    }
}

/// How the Lean trace runner should build/capture the `Trusted.MirAst.Program`
/// for a [`TraceTestCase`].
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "source", rename_all = "snake_case")]
pub enum LeanProgramSpec {
    /// Capture `select_fn` from `pure_rust_source` directly with
    /// `anneal-rustc-capture` and evaluate it in Lean.
    CapturedRust { crate_name: String, select_fn: String },
    /// Capture each leaf helper in `captured_callees` from `pure_rust_source`
    /// with `anneal-rustc-capture`, splice those real captured MIR bodies into
    /// a multi-call `Trusted.MirAst.Program` alongside `caller_lean_body`
    /// (which uses `TerminatorKind.call` targeting the captured callee
    /// indices), and verify both Mode (a) conservative refusal and Mode (b)
    /// compositional multi-call execution.
    MultiCallWithCapturedCallees {
        crate_name: String,
        captured_callees: Vec<String>,
        caller_lean_body: String,
        caller_identity: String,
        external_callees: Vec<String>,
    },
    /// Directly evaluate a synthesized `Trusted.MirAst.Program` expression
    /// (e.g. cleanup unwind blocks, `assert`, or fuzzer-generated multi-call
    /// MIR programs) in both Mode (a) and Mode (b).
    SyntheticMirAst { program_lean_expr: String, external_callees: Vec<String> },
}

fn contains_lean_terminator_token(expr: &str, token: &str) -> bool {
    let bytes = expr.as_bytes();
    let t_bytes = token.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut start = 0usize;
    while let Some(rel) = expr[start..].find(token) {
        let idx = start + rel;
        let end = idx + t_bytes.len();
        let before_ok = idx == 0 || !is_ident(bytes[idx - 1]);
        let after_ok = end == bytes.len() || !is_ident(bytes[end]);
        if before_ok && after_ok {
            return true;
        }
        start = end;
    }
    false
}

impl LeanProgramSpec {
    /// Returns `true` when this Lean program spec requires conservative
    /// refusal (`CaptureRefused`) under `StrictVerbatim` (`evalMirStepBy`) —
    /// specifically non-empty `external_callees` or `.cleanup`/`.unwindResume`/
    /// `.coreCall` boundaries not modeled in strict verbatim mode.
    pub fn requires_strict_refusal(&self) -> bool {
        let (expr, external_callees) = match self {
            Self::CapturedRust { .. } => return false,
            Self::MultiCallWithCapturedCallees { caller_lean_body, external_callees, .. } => {
                (caller_lean_body.as_str(), external_callees.as_slice())
            }
            Self::SyntheticMirAst { program_lean_expr, external_callees } => {
                (program_lean_expr.as_str(), external_callees.as_slice())
            }
        };
        if !external_callees.is_empty() {
            return true;
        }
        [
            ".cleanup",
            "UnwindAction.cleanup",
            ".coreCall",
            "TerminatorKind.coreCall",
            ".unwindResume",
            "TerminatorKind.unwindResume",
        ]
        .iter()
        .any(|tok| contains_lean_terminator_token(expr, tok))
    }
}

/// Source-inlined single-body Rust twin paired with a multi-call case to verify
/// metamorphic inlining duality across `rustc` (`-O0`/`-O2`), `miri`, and Lean
/// (`CompositionalITree` multi-call == `StrictVerbatim` single-body).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MetamorphicTwin {
    pub crate_name: String,
    pub pure_rust_source: String,
    pub entry_fn: String,
}

/// Expected high-level outcome classification for suite reporting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExpectedCaseClass {
    /// All authorities should agree cleanly (`TraceVerdict::Agree` with Miri).
    Agree,
    /// Strict Lean / capture conservatively refuses or faults unsupported while
    /// Rust/Miri succeeds (`TraceVerdict::ConservativeOverApprox` in strict
    /// mode, or `Agree` in compositional mode).
    ConservativeOverApprox,
    /// Explicitly disclosed boundary gap artifact.
    DisclosedGap,
    /// Negative UB probe: Miri detects UB and Lean either detects UB (`Agree`)
    /// or conservatively refuses (`ConservativeOverApprox`), NEVER
    /// `UnsoundAccept`. Host `rustc` is skipped on UB inputs.
    UndefinedBehavior,
    /// Panicking / unwinding case: Rust, Miri, and Compositional Lean all
    /// unwind cleanly while preserving caller frames.
    Unwind,
    /// Scheduled boundary abort case: `rustc`, `miri`, and Compositional Lean
    /// all terminate via `Aborted` without executing caller unwind drops.
    Abort,
}

/// Complete specification of one differential test case.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceTestCase {
    pub id: String,
    pub category: CaseCategory,
    pub pure_rust_source: String,
    pub traced_rust_source: Option<String>,
    pub entry_fn: String,
    pub rust_arg_exprs: Vec<String>,
    pub lean_args: Vec<TraceVal>,
    pub ret_shape: ReturnShape,
    pub lean_program_spec: LeanProgramSpec,
    pub metamorphic_inlined_twin: Option<MetamorphicTwin>,
    pub env_schedule: EnvSchedule,
    pub fuel: u64,
    pub spine_mode: SpineCompareMode,
    pub expected_class: ExpectedCaseClass,
    #[serde(default)]
    pub expected_ub: Option<ExpectedUbSpec>,
    #[serde(default)]
    pub expected_conservative: Option<ExpectedConservativeSpec>,
    pub disclosed_gap: Option<DisclosedGapSpec>,
}

impl TraceTestCase {
    /// Returns `true` when this case intentionally exercises Undefined Behavior
    /// so host `rustc` must never execute it natively without Miri's guard.
    pub fn is_expected_ub(&self) -> bool {
        self.expected_class == ExpectedCaseClass::UndefinedBehavior
    }

    /// Returns `true` when this test case requires conservative refusal
    /// (`CaptureRefused`) under `StrictVerbatim`, either due to unmodeled
    /// boundaries in `lean_program_spec` or non-empty `env_schedule` actions.
    pub fn requires_strict_refusal(&self) -> bool {
        !self.env_schedule.is_empty()
            || self.expected_class == ExpectedCaseClass::Unwind
            || self.lean_program_spec.requires_strict_refusal()
    }
}

fn render_rt_env_action(action: &EnvAction) -> String {
    match action {
        EnvAction::ReturnBytes(bytes) => {
            let elems: Vec<String> = bytes.iter().map(|b| format!("{b}u8")).collect();
            format!("anneal_rt::RtEnvAction::ReturnBytes(vec![{}])", elems.join(", "))
        }
        EnvAction::Unwind { message } => {
            format!("anneal_rt::RtEnvAction::Unwind({message:?}.to_string())")
        }
        EnvAction::Abort { reason } => {
            format!("anneal_rt::RtEnvAction::Abort({reason:?}.to_string())")
        }
    }
}

fn extract_crate_attrs_and_body(source: &str) -> (Vec<String>, Vec<String>) {
    let mut crate_attrs = Vec::new();
    let mut body_lines = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed == "#![no_std]" || trimmed.starts_with("#![cfg_attr(") {
            continue;
        }
        if trimmed.starts_with("#![") {
            crate_attrs.push(line.to_owned());
        } else {
            body_lines.push(line.to_owned());
        }
    }
    (crate_attrs, body_lines)
}

fn push_sanitized_module(out: &mut String, mod_name: &str, body_lines: &[String]) {
    let _ = writeln!(
        out,
        "\n#[allow(dead_code, unused_variables, unused_imports, clippy::all)]\nmod {mod_name} {{"
    );
    out.push_str("    use crate::anneal_rt;\n");
    for line in body_lines {
        out.push_str("    ");
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("}\n");
}

pub(crate) fn push_env_schedule_setup(sched_setup: &mut String, sched: &EnvSchedule) {
    for (callee, queue) in &sched.per_callee {
        for act in queue {
            let rendered = render_rt_env_action(act);
            let _ =
                writeln!(sched_setup, "    anneal_rt::push_callee_action({callee:?}, {rendered});");
        }
    }
    for act in &sched.global {
        let rendered = render_rt_env_action(act);
        let _ = writeln!(sched_setup, "    anneal_rt::push_global_action({rendered});");
    }
}

/// Return `true` when `rel` enforces cross-opt (`-O0` vs `-O2`) parity.
pub(crate) fn is_rustc_o0_vs_o2_relation(rel: &str) -> bool {
    matches!(rel, "called_rustc_o0_vs_o2" | "inlined_rustc_o0_vs_o2")
}

/// Render a self-contained Rust executable harness for `rustc` (`-O0`/`-O2`)
/// and `miri` that installs `case.env_schedule`, captures runtime entry
/// argument bytes into `boundary_slots`, materializes a `#[repr(C)]` padded
/// caller stack frame via `core::hint::black_box`, catches unwinds vs invalid
/// schedule bit patterns cleanly, and prints one `ANNEAL_ITREE_TRACE_JSON:`
/// line (or `ANNEAL_ITREE_PRE_ABORT:` right before `std::process::abort()`).
pub fn render_standalone_rust_harness(case: &TraceTestCase) -> String {
    render_standalone_rust_harness_inner(case, &[], false)
}

/// Variant of [`render_standalone_rust_harness`] that enforces `-O0` vs `-O2`
/// peer comparison (`--compare-opt` / `ANNEAL_COMPARE_OPT_BIN` / sibling
/// `*_o2{.exe}`) when `pinned_relations` includes an O0/O2 relation.
pub fn render_standalone_rust_harness_with_relations(
    case: &TraceTestCase,
    pinned_relations: &[String],
) -> String {
    render_standalone_rust_harness_inner(case, pinned_relations, true)
}

fn render_standalone_rust_harness_inner(
    case: &TraceTestCase,
    pinned_relations: &[String],
    preserve_fault_ub_with_rem: bool,
) -> String {
    let source = case.traced_rust_source.as_deref().unwrap_or(&case.pure_rust_source);
    let (crate_attrs, body_lines) = extract_crate_attrs_and_body(source);
    let needs_opt = pinned_relations.iter().any(|r| is_rustc_o0_vs_o2_relation(r));

    let mut out = String::new();
    for attr in &crate_attrs {
        out.push_str(attr);
        out.push('\n');
    }
    out.push_str(render_embedded_trace_prelude());
    push_sanitized_module(&mut out, "subject", &body_lines);
    out.push('\n');

    let mut sched_setup = String::new();
    push_env_schedule_setup(&mut sched_setup, &case.env_schedule);

    let mut arg_bindings = String::new();
    let mut arg_vars = Vec::with_capacity(case.rust_arg_exprs.len());
    for (idx, expr) in case.rust_arg_exprs.iter().enumerate() {
        let var = format!("__arg_{idx}");
        let _ = writeln!(arg_bindings, "    let {var} = {expr};");
        let _ = writeln!(
            arg_bindings,
            "    anneal_rt::record_boundary_slot(anneal_rt::capture_value_bytes(&{var}));"
        );
        arg_vars.push(var);
    }

    let arg_list = arg_vars.join(", ");
    let ret_json_expr = case.ret_shape.render_rust_to_json_expr("ret");
    let ret_bytes_expr = case.ret_shape.render_rust_ret_bytes_expr("ret");
    let run_fn_name = if needs_opt { "run_single_subject" } else { "main" };

    let _ = writeln!(
        out,
        r#"fn {run_fn_name}() {{
{sched_setup}{arg_bindings}    anneal_rt::emit_pre_entry_slots();
    let root_frame = std::hint::black_box(anneal_rt::RootCallerFrame {{
        tag: 0x5Au8,
        magic: 0xDEAD_BEEFu32,
        flag: true,
        counter: 0xCAFE_BABE_1234_5678u64,
    }});
    let watched_alloc: [u8; 16] = std::hint::black_box([
        0xA5u8, 0x5A, 0xC3, 0x3C, 0x0F, 0xF0, 0x12, 0x34,
        0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22,
    ]);
    let _caller_watch_guard = unsafe {{
        anneal_rt::ScopedCallerWatchGuard::install(
            core::ptr::from_ref(&root_frame),
            watched_alloc.as_ptr(),
            watched_alloc.len(),
        )
    }};

    let call_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
        #[allow(unused_unsafe)]
        unsafe {{ subject::{entry}({arg_list}) }}
    }}));

    match call_res {{
        Ok(ret) => {{
            anneal_rt::check_and_emit_caller_frame("root_exit");
            anneal_rt::record_post_return_slot({ret_bytes_expr});
            let ret_json = {ret_json_expr};
            anneal_rt::finish_json("returned", &ret_json, "");
        }}
        Err(payload) => {{
            if let Some(sched_err) = payload.downcast_ref::<anneal_rt::ScheduleDecodeFailed>() {{
                {reset_sched_on_ub}anneal_rt::finish_json("fault_ub", "null", &sched_err.0);
                return;
            }}
            anneal_rt::check_and_emit_caller_frame("root_exit");
            anneal_rt::record_post_unwind_slot();
            let msg = if let Some(s) = payload.downcast_ref::<&str>() {{
                (*s).to_string()
            }} else if let Some(s) = payload.downcast_ref::<String>() {{
                s.clone()
            }} else {{
                "panic".to_string()
            }};
            anneal_rt::finish_json("unwound", "null", &msg);
        }}
    }}
}}"#,
        run_fn_name = run_fn_name,
        sched_setup = sched_setup,
        arg_bindings = arg_bindings,
        entry = case.entry_fn,
        arg_list = arg_list,
        ret_bytes_expr = ret_bytes_expr,
        ret_json_expr = ret_json_expr,
        reset_sched_on_ub = if preserve_fault_ub_with_rem {
            "anneal_rt::reset_schedules();\n                "
        } else {
            ""
        },
    );

    if needs_opt {
        out.push_str(&render_single_opt_peer_compare_fns(
            "run_single_child_once",
            "discover_sibling_opt_peer",
            "compare_single_opt_peer",
            "run_single_subject",
            "rustc_o0_o2",
        ));
    }

    out
}

/// Render a standalone Rust reproducer comparing BOTH the called multi-call
/// variant (`subject`) AND its `metamorphic_inlined_twin` (`subject_inlined`),
/// failing loudly if the called and source-inlined variants diverge at runtime.
pub fn render_standalone_metamorphic_rust_harness(case: &TraceTestCase) -> String {
    render_standalone_metamorphic_rust_harness_with_relations(case, &[])
}

/// Variant of [`render_standalone_metamorphic_rust_harness`] preserving pinned
/// `metamorphic_relations` from [`ShrinkFailureSignature`] so reproducers for
/// `called_rustc_o0_vs_o2` or `inlined_rustc_o0_vs_o2` expose and enforce
/// cross-mode (`-O0` vs `-O2`) comparison instead of only within-mode
/// called-vs-inlined equality.
pub fn render_standalone_metamorphic_rust_harness_with_relations(
    case: &TraceTestCase,
    pinned_relations: &[String],
) -> String {
    let Some(twin) = &case.metamorphic_inlined_twin else {
        return render_standalone_rust_harness_with_relations(case, pinned_relations);
    };
    let called_src = case.traced_rust_source.as_deref().unwrap_or(&case.pure_rust_source);
    let (mut crate_attrs, called_body) = extract_crate_attrs_and_body(called_src);
    let (twin_attrs, twin_body) = extract_crate_attrs_and_body(&twin.pure_rust_source);
    for attr in twin_attrs {
        if !crate_attrs.contains(&attr) {
            crate_attrs.push(attr);
        }
    }

    let mut out = String::new();
    for attr in &crate_attrs {
        out.push_str(attr);
        out.push('\n');
    }
    out.push_str(render_embedded_trace_prelude());
    push_sanitized_module(&mut out, "subject", &called_body);
    push_sanitized_module(&mut out, "subject_inlined", &twin_body);
    out.push('\n');

    let mut sched_setup = String::new();
    push_env_schedule_setup(&mut sched_setup, &case.env_schedule);

    let mut arg_bindings = String::new();
    let mut arg_vars = Vec::with_capacity(case.rust_arg_exprs.len());
    let mut twin_arg_bindings = String::new();
    let mut twin_arg_vars = Vec::with_capacity(case.rust_arg_exprs.len());
    for (idx, expr) in case.rust_arg_exprs.iter().enumerate() {
        let var = format!("__arg_{idx}");
        let _ = writeln!(arg_bindings, "    let {var} = {expr};");
        let _ = writeln!(
            arg_bindings,
            "    anneal_rt::record_boundary_slot(anneal_rt::capture_value_bytes(&{var}));"
        );
        arg_vars.push(var);

        let twin_var = format!("__twin_arg_{idx}");
        let _ = writeln!(twin_arg_bindings, "    let {twin_var} = {expr};");
        let _ = writeln!(
            twin_arg_bindings,
            "    anneal_rt::record_boundary_slot(anneal_rt::capture_value_bytes(&{twin_var}));"
        );
        twin_arg_vars.push(twin_var);
    }

    let arg_list = arg_vars.join(", ");
    let twin_arg_list = twin_arg_vars.join(", ");
    let ret_json_expr = case.ret_shape.render_rust_to_json_expr("ret");
    let ret_bytes_expr = case.ret_shape.render_rust_ret_bytes_expr("ret");
    let has_abort = case
        .env_schedule
        .per_callee
        .values()
        .flatten()
        .chain(case.env_schedule.global.iter())
        .any(|a| matches!(a, crate::trace_observer::EnvAction::Abort { .. }));

    let install_sched_body = if sched_setup.is_empty() {
        "    anneal_rt::reset_schedules();\n".to_string()
    } else {
        format!("    anneal_rt::reset_schedules();\n{sched_setup}")
    };

    let pinned_rel_lits =
        pinned_relations.iter().map(|r| format!("{r:?}")).collect::<Vec<_>>().join(", ");
    let spine_mode_lit = format!(
        "{:?}",
        match case.spine_mode {
            SpineCompareMode::FullBranchesAndCalls => "full_branches_and_calls",
            SpineCompareMode::ObsErasedCallsOnly => "obs_erased_calls_only",
            SpineCompareMode::OutcomeOnly => "outcome_only",
        }
    );

    let _ = writeln!(
        out,
        r#"const HAS_ABORT_SCHEDULE: bool = {has_abort};
const PINNED_META_RELATIONS: &[&str] = &[{pinned_rel_lits}];
const SPINE_COMPARE_MODE: &str = {spine_mode_lit};

#[derive(Clone, Debug)]
struct MetaVariantOutcome {{
    kind: String,
    ret_json: String,
    detail: String,
    slots_json: String,
    frame_ok: bool,
    events_json: String,
}}

fn outcomes_diverge(c: &MetaVariantOutcome, i: &MetaVariantOutcome) -> bool {{
    if c.kind != i.kind {{
        return true;
    }}
    if c.kind == "returned" && c.ret_json != i.ret_json {{
        return true;
    }}
    if matches!(c.kind.as_str(), "returned" | "unwound" | "aborted" | "fault_ub")
        && c.slots_json != i.slots_json
    {{
        return true;
    }}
    if c.kind == "fault_ub" && !standalone_ub_fault_causes_compatible(&c.detail, &i.detail) {{
        return true;
    }}
    !c.frame_ok || !i.frame_ok
}}

fn cross_mode_outcomes_diverge(o0: &MetaVariantOutcome, o2: &MetaVariantOutcome) -> bool {{
    outcomes_diverge(o0, o2) || spines_diverge(o0, o2)
}}

fn install_meta_schedule() {{
{install_sched_body}}}

fn run_called_variant() -> MetaVariantOutcome {{
    anneal_rt::reset_trace_observer();
    install_meta_schedule();
{arg_bindings}    anneal_rt::emit_pre_entry_slots();
    let root_frame = std::hint::black_box(anneal_rt::RootCallerFrame {{
        tag: 0x5Au8,
        magic: 0xDEAD_BEEFu32,
        flag: true,
        counter: 0xCAFE_BABE_1234_5678u64,
    }});
    let watched_alloc: [u8; 16] = std::hint::black_box([
        0xA5u8, 0x5A, 0xC3, 0x3C, 0x0F, 0xF0, 0x12, 0x34,
        0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22,
    ]);
    let _caller_watch_guard = unsafe {{
        anneal_rt::ScopedCallerWatchGuard::install(
            core::ptr::from_ref(&root_frame),
            watched_alloc.as_ptr(),
            watched_alloc.len(),
        )
    }};

    let call_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
        #[allow(unused_unsafe)]
        unsafe {{ subject::{entry}({arg_list}) }}
    }}));

    let (kind, ret_json, detail): (&str, String, String) = match call_res {{
        Ok(ret) => {{
            anneal_rt::check_and_emit_caller_frame("root_exit");
            anneal_rt::record_post_return_slot({ret_bytes_expr});
            ("returned", {ret_json_expr}, String::new())
        }}
        Err(payload) => {{
            if let Some(sched_err) = payload.downcast_ref::<anneal_rt::ScheduleDecodeFailed>() {{
                ("fault_ub", "null".to_string(), sched_err.0.clone())
            }} else {{
                anneal_rt::check_and_emit_caller_frame("root_exit");
                anneal_rt::record_post_unwind_slot();
                let msg = if let Some(s) = payload.downcast_ref::<&str>() {{
                    (*s).to_string()
                }} else if let Some(s) = payload.downcast_ref::<String>() {{
                    s.clone()
                }} else {{
                    "panic".to_string()
                }};
                ("unwound", "null".to_string(), msg)
            }}
        }}
    }};
    let slots_json = anneal_rt::current_boundary_slots_json();
    let frame_ok = anneal_rt::current_caller_frame_preserved();
    let events_json = anneal_rt::current_events_json();
    let rem = anneal_rt::remaining_schedule_count();
    let (final_kind, final_ret, final_detail) = if kind != "fault_ub" && rem > 0 {{
        (
            "unconsumed_schedule",
            "null".to_string(),
            format!("{{rem}} scheduled EnvAction(s) remained unconsumed at termination"),
        )
    }} else {{
        if kind == "fault_ub" {{
            anneal_rt::reset_schedules();
        }}
        (kind, ret_json, detail)
    }};
    anneal_rt::finish_json(final_kind, &final_ret, &final_detail);
    MetaVariantOutcome {{
        kind: final_kind.to_string(),
        ret_json: final_ret,
        detail: final_detail,
        slots_json,
        frame_ok,
        events_json,
    }}
}}

fn run_inlined_variant() -> MetaVariantOutcome {{
    anneal_rt::reset_trace_observer();
    anneal_rt::reset_schedules();
{twin_arg_bindings}    let root_frame = std::hint::black_box(anneal_rt::RootCallerFrame {{
        tag: 0x5Au8,
        magic: 0xDEAD_BEEFu32,
        flag: true,
        counter: 0xCAFE_BABE_1234_5678u64,
    }});
    let watched_alloc: [u8; 16] = std::hint::black_box([
        0xA5u8, 0x5A, 0xC3, 0x3C, 0x0F, 0xF0, 0x12, 0x34,
        0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22,
    ]);
    let _caller_watch_guard = unsafe {{
        anneal_rt::ScopedCallerWatchGuard::install(
            core::ptr::from_ref(&root_frame),
            watched_alloc.as_ptr(),
            watched_alloc.len(),
        )
    }};
    let twin_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
        #[allow(unused_unsafe)]
        unsafe {{ subject_inlined::{twin_entry}({twin_arg_list}) }}
    }}));
    let (inlined_kind, inlined_ret_json, inlined_detail): (&str, String, String) = match twin_res {{
        Ok(ret) => {{
            anneal_rt::check_and_emit_caller_frame("root_exit");
            anneal_rt::record_post_return_slot({ret_bytes_expr});
            ("returned", {ret_json_expr}, String::new())
        }}
        Err(payload) => {{
            if let Some(sched_err) = payload.downcast_ref::<anneal_rt::ScheduleDecodeFailed>() {{
                ("fault_ub", "null".to_string(), sched_err.0.clone())
            }} else {{
                anneal_rt::check_and_emit_caller_frame("root_exit");
                anneal_rt::record_post_unwind_slot();
                let msg = if let Some(s) = payload.downcast_ref::<&str>() {{
                    (*s).to_string()
                }} else if let Some(s) = payload.downcast_ref::<String>() {{
                    s.clone()
                }} else {{
                    "panic".to_string()
                }};
                ("unwound", "null".to_string(), msg)
            }}
        }}
    }};
    anneal_rt::reset_schedules();
    let payload = anneal_rt::render_trace_payload_json(
        inlined_kind,
        &inlined_ret_json,
        &inlined_detail,
    );
    let events_json = anneal_rt::current_events_json();
    println!("ANNEAL_ITREE_INLINED_TWIN_JSON:{{payload}}");
    MetaVariantOutcome {{
        kind: inlined_kind.to_string(),
        ret_json: inlined_ret_json,
        detail: inlined_detail,
        slots_json: anneal_rt::current_boundary_slots_json(),
        frame_ok: anneal_rt::current_caller_frame_preserved(),
        events_json,
    }}
}}"#,
        has_abort = has_abort,
        pinned_rel_lits = pinned_rel_lits,
        spine_mode_lit = spine_mode_lit,
        install_sched_body = install_sched_body,
        arg_bindings = arg_bindings,
        entry = case.entry_fn,
        arg_list = arg_list,
        ret_bytes_expr = ret_bytes_expr,
        ret_json_expr = ret_json_expr,
        twin_arg_bindings = twin_arg_bindings,
        twin_entry = twin.entry_fn,
        twin_arg_list = twin_arg_list,
    );

    out.push_str(
        r#"
fn unescape_json_str(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut chars = raw.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('"') => out.push('"'),
            Some('\\') => out.push('\\'),
            Some('/') => out.push('/'),
            Some('b') => out.push('\u{0008}'),
            Some('f') => out.push('\u{000C}'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('u') => {
                let hex: String = chars.by_ref().take(4).collect();
                let decoded = if hex.len() == 4 {
                    u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32)
                } else {
                    None
                };
                if let Some(ch) = decoded {
                    out.push(ch);
                } else {
                    out.push_str("\\u");
                    out.push_str(&hex);
                }
            }
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

fn extract_json_str_field(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{}\":\"", key);
    let idx = line.find(&needle)? + needle.len();
    let rest = &line[idx..];
    let mut end = 0usize;
    let bytes = rest.as_bytes();
    while end < bytes.len() {
        if bytes[end] == b'\\' {
            end += 2;
        } else if bytes[end] == b'"' {
            return Some(unescape_json_str(&rest[..end]));
        } else {
            end += 1;
        }
    }
    None
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StandaloneUbFaultClass {
    ScheduledReturnDecode,
    UnreachableOrNoUnwind,
    UncheckedShiftOverflow,
    UncheckedArithOrDivOverflow,
    PointerOrMemoryAccess,
    InvalidValueOrUninit,
    Unclassified,
}

fn standalone_extract_scheduled_decode_callee(detail: &str) -> Option<&str> {
    if let Some(rest) = detail.strip_prefix("callee `") {
        if let Some((callee, reason)) = rest.split_once("` scheduled ReturnBytes invalid: ") {
            if !callee.is_empty() && !reason.trim().is_empty() {
                return Some(callee);
            }
        }
    }
    if let Some(callee) = detail.strip_prefix("invalid scheduled ReturnBytes for ") {
        let trimmed = callee.trim();
        if !trimmed.is_empty() {
            return Some(trimmed);
        }
    }
    None
}

fn standalone_classify_ub_fault_detail(detail: &str) -> StandaloneUbFaultClass {
    let lower = detail.to_ascii_lowercase();
    if lower.contains("scheduled returnbytes") {
        StandaloneUbFaultClass::ScheduledReturnDecode
    } else if lower.contains("unreachable")
        || lower.contains("does not allow unwinding")
        || lower.contains("from diverging call")
    {
        StandaloneUbFaultClass::UnreachableOrNoUnwind
    } else if lower.contains("overflowing shift")
        || lower.contains("unchecked_shl")
        || lower.contains("unchecked_shr")
        || lower.contains("unchecked shift")
        || lower.contains("shift overflow")
    {
        StandaloneUbFaultClass::UncheckedShiftOverflow
    } else if lower.contains("unchecked_add")
        || lower.contains("unchecked_sub")
        || lower.contains("unchecked_mul")
        || lower.contains("unchecked arithmetic")
        || lower.contains("unchecked signed arithmetic")
        || lower.contains("unchecked unsigned arithmetic")
        || lower.contains("overflowing arithmetic")
        || lower.contains("division by zero")
        || lower.contains("dividing by zero")
        || lower.contains("remainder by zero")
        || lower.contains("divisor of zero")
        || lower.contains("division or remainder")
        || lower.contains("min / -1")
        || lower.contains("overflow in signed")
    {
        StandaloneUbFaultClass::UncheckedArithOrDivOverflow
    } else if lower.contains("dereferencing pointer")
        || lower.contains("pointer dereference")
        || lower.contains("pointer arithmetic")
        || lower.contains("pointer or memory access")
        || lower.contains("memory access")
        || lower.contains("memory read")
        || lower.contains("memory write")
        || lower.contains("misaligned")
        || lower.contains("with alignment")
        || lower.contains("null pointer")
        || lower.contains("dangling")
        || lower.contains("use-after-free")
        || lower.contains("deallocating")
        || lower.contains("immutable allocation")
        || lower.contains("out-of-bounds")
        || lower.contains("borrow stack")
        || lower.contains("tree borrows")
        || lower.contains("is forbidden")
        || lower.contains("copy_nonoverlapping")
        || lower.contains("overlapping memory copy")
    {
        StandaloneUbFaultClass::PointerOrMemoryAccess
    } else if lower.contains("constructing invalid value")
        || lower.contains("using uninitialized")
        || lower.contains("uninitialized")
        || lower.contains("dead local")
        || lower.contains("dead _0")
        || lower.contains("dead destination")
        || lower.contains("entry argument bit-validity")
        || lower.contains("invalid boolean")
        || lower.contains("invalid char")
        || lower.contains("surrogate")
        || lower.contains("invalid ordering")
        || lower.contains("invalid fieldless enum")
        || lower.contains("invalid tag")
        || lower.contains("invalid discriminant")
        || lower.contains("invalid value")
        || lower.contains("validation failure")
        || lower.contains("writeplace undefined")
        || lower.contains("call argument eval undefined")
        || lower.contains("assert condition undefined")
    {
        StandaloneUbFaultClass::InvalidValueOrUninit
    } else {
        StandaloneUbFaultClass::Unclassified
    }
}

fn standalone_ub_fault_causes_compatible(c_detail: &str, i_detail: &str) -> bool {
    let c1 = standalone_classify_ub_fault_detail(c_detail);
    let c2 = standalone_classify_ub_fault_detail(i_detail);
    match (c1, c2) {
        (StandaloneUbFaultClass::Unclassified, StandaloneUbFaultClass::Unclassified) => {
            let t1 = c_detail.trim();
            !t1.is_empty() && t1 == i_detail.trim()
        }
        (
            StandaloneUbFaultClass::ScheduledReturnDecode,
            StandaloneUbFaultClass::ScheduledReturnDecode,
        ) => {
            if let (Some(cal1), Some(cal2)) = (
                standalone_extract_scheduled_decode_callee(c_detail),
                standalone_extract_scheduled_decode_callee(i_detail),
            ) {
                cal1 == cal2
            } else {
                true
            }
        }
        (a, b) if a != StandaloneUbFaultClass::Unclassified && b != StandaloneUbFaultClass::Unclassified => a == b,
        _ => false,
    }
}

fn extract_json_raw_field(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{}\":", key);
    let idx = line.find(&needle)? + needle.len();
    let rest = line[idx..].trim_start();
    let mut depth = 0usize;
    let mut in_str = false;
    let mut escape = false;
    for (pos, ch) in rest.char_indices() {
        if in_str {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_str = false;
                if depth == 0 {
                    return Some(rest[..=pos].trim().to_string());
                }
            }
            continue;
        }
        match ch {
            '"' => in_str = true,
            '{' | '[' => depth += 1,
            '}' | ']' => {
                if depth == 0 {
                    return Some(rest[..pos].trim().to_string());
                }
                depth -= 1;
                if depth == 0 {
                    return Some(rest[..=pos].trim().to_string());
                }
            }
            ',' if depth == 0 => {
                return Some(rest[..pos].trim().to_string());
            }
            _ => {}
        }
    }
    Some(rest.trim().to_string())
}

fn split_json_array_elements(arr: &str) -> Vec<String> {
    let trimmed = arr.trim();
    let inner = trimmed
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .unwrap_or(trimmed)
        .trim();
    if inner.is_empty() {
        return Vec::new();
    }
    let mut items = Vec::new();
    let mut depth = 0usize;
    let mut in_str = false;
    let mut escape = false;
    let mut start = 0usize;
    for (pos, ch) in inner.char_indices() {
        if in_str {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        match ch {
            '"' => in_str = true,
            '{' | '[' => depth += 1,
            '}' | ']' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                let elem = inner[start..pos].trim();
                if !elem.is_empty() {
                    items.push(elem.to_string());
                }
                start = pos + 1;
            }
            _ => {}
        }
    }
    let tail = inner[start..].trim();
    if !tail.is_empty() {
        items.push(tail.to_string());
    }
    items
}

fn normalize_unwind_reason_str(reason: &str) -> String {
    let trimmed = reason.trim();
    if let Some(rest) = trimmed.strip_prefix("abort:") {
        format!("abort:{rest}")
    } else if trimmed == "assert:div_by_zero" || trimmed.contains("attempt to divide by zero") {
        "panic:div_by_zero".to_string()
    } else if trimmed == "assert:rem_by_zero"
        || trimmed.contains("attempt to calculate the remainder with a divisor of zero")
    {
        "panic:rem_by_zero".to_string()
    } else if trimmed == "assert:bounds_check" || trimmed.starts_with("index out of bounds:") {
        "panic:bounds_check".to_string()
    } else if trimmed == "assert:overflow"
        || (trimmed.starts_with("attempt to ") && trimmed.ends_with(" with overflow"))
    {
        "panic:overflow".to_string()
    } else {
        format!("unwind:{trimmed}")
    }
}

fn normalize_event_spine(events_json: &str) -> Vec<String> {
    let elems = split_json_array_elements(events_json);
    if SPINE_COMPARE_MODE != "obs_erased_calls_only" {
        return elems;
    }
    elems
        .into_iter()
        .filter_map(|ev| {
            let kind = extract_json_str_field(&ev, "kind");
            if kind.as_deref() == Some("branch_tag") {
                None
            } else if kind.as_deref() == Some("call_unwind") {
                let callee = extract_json_str_field(&ev, "callee").unwrap_or_default();
                let reason = extract_json_str_field(&ev, "reason").unwrap_or_default();
                Some(format!("UNWIND:{callee}:{}", normalize_unwind_reason_str(&reason)))
            } else {
                Some(ev)
            }
        })
        .collect()
}

fn spines_diverge(c: &MetaVariantOutcome, i: &MetaVariantOutcome) -> bool {
    if SPINE_COMPARE_MODE == "outcome_only" {
        return false;
    }
    normalize_event_spine(&c.events_json) != normalize_event_spine(&i.events_json)
}

fn parse_outcome_from_json_line(j: &str, default_kind: Option<&str>) -> MetaVariantOutcome {
    let kind = extract_json_str_field(j, "outcome_kind")
        .or_else(|| default_kind.map(str::to_string))
        .unwrap_or_else(|| "unknown".into());
    let ret_json = extract_json_raw_field(j, "ret").unwrap_or_else(|| "null".into());
    let detail = extract_json_str_field(j, "detail").unwrap_or_default();
    let slots_json = extract_json_raw_field(j, "boundary_slots").unwrap_or_else(|| "[]".into());
    let frame_ok = extract_json_raw_field(j, "caller_locals_preserved").as_deref() == Some("true")
        && extract_json_raw_field(j, "untouched_alloc_bytes_preserved").as_deref() == Some("true")
        && extract_json_raw_field(j, "padding_mask_respected").as_deref() == Some("true");
    let events_json = extract_json_raw_field(j, "events").unwrap_or_else(|| "[]".into());
    MetaVariantOutcome { kind, ret_json, detail, slots_json, frame_ok, events_json }
}

fn parse_child_outcome_on(exe: &std::path::Path, flag: &str) -> MetaVariantOutcome {
    let out = std::process::Command::new(exe).arg(flag).output().expect("spawn metamorphic child");
    let stdout = String::from_utf8_lossy(&out.stdout);
    for line in stdout.lines() {
        print!("{line}\n");
    }
    let stderr = String::from_utf8_lossy(&out.stderr);
    for line in stdout.lines().rev() {
        if let Some(j) = line.trim().strip_prefix("ANNEAL_ITREE_INLINED_TWIN_JSON:") {
            return parse_outcome_from_json_line(j, None);
        }
        if let Some(j) = line.trim().strip_prefix("ANNEAL_ITREE_TRACE_JSON:") {
            return parse_outcome_from_json_line(j, None);
        }
        if let Some(j) = line.trim().strip_prefix("ANNEAL_ITREE_PRE_ABORT:") {
            return parse_outcome_from_json_line(j, Some("aborted"));
        }
    }
    if !out.status.success() {
        MetaVariantOutcome {
            kind: "aborted".into(),
            ret_json: "null".into(),
            detail: stderr.trim().to_string(),
            slots_json: String::new(),
            frame_ok: false,
            events_json: String::new(),
        }
    } else {
        MetaVariantOutcome {
            kind: "unknown".into(),
            ret_json: "null".into(),
            detail: stdout.trim().to_string(),
            slots_json: String::new(),
            frame_ok: false,
            events_json: String::new(),
        }
    }
}

"#,
    );
    out.push_str(&render_discover_sibling_opt_peer_fn("discover_sibling_opt_peer"));
    out.push('\n');
    out.push_str(
        r#"fn is_rustc_o0_vs_o2_rel(rel: &str) -> bool {
    matches!(rel, "called_rustc_o0_vs_o2" | "inlined_rustc_o0_vs_o2")
}

fn is_rustc_called_vs_inlined_rel(rel: &str) -> bool {
    matches!(
        rel,
        "rustc_called_vs_inlined"
            | "metamorphic_caller_frame_law:called_rustc"
            | "metamorphic_caller_frame_law:inlined_rustc"
    )
}

fn is_miri_called_vs_inlined_rel(rel: &str) -> bool {
    matches!(
        rel,
        "miri_called_vs_inlined"
            | "metamorphic_caller_frame_law:called_miri"
            | "metamorphic_caller_frame_law:inlined_miri"
    )
}

fn collect_unreplayed_pinned_relations(include_opt_modes: bool) -> Vec<&'static str> {
    let rustc_in_process = !cfg!(miri);
    let miri_in_process = cfg!(miri) && !HAS_ABORT_SCHEDULE;
    PINNED_META_RELATIONS
        .iter()
        .copied()
        .filter(|r| {
            let opt_covered =
                rustc_in_process && include_opt_modes && is_rustc_o0_vs_o2_rel(r);
            let rustc_covered = rustc_in_process && is_rustc_called_vs_inlined_rel(r);
            let miri_covered = miri_in_process && is_miri_called_vs_inlined_rel(r);
            !(opt_covered || rustc_covered || miri_covered)
        })
        .collect()
}

// Leave bare `"metamorphic_caller_frame_law"` uncovered by single-authority
// in-process runs: without an authority tag it may reflect a Lean or Miri
// fault, so standalone rustc/Miri fails closed in
// `collect_unreplayed_pinned_relations` rather than false-passing.
fn should_check_called_vs_inlined_in_process() -> bool {
    let rustc_in_process = !cfg!(miri);
    let miri_in_process = cfg!(miri) && !HAS_ABORT_SCHEDULE;
    (rustc_in_process || miri_in_process)
        && (PINNED_META_RELATIONS.is_empty()
            || PINNED_META_RELATIONS.iter().any(|r| {
                (rustc_in_process && is_rustc_called_vs_inlined_rel(r))
                    || (miri_in_process && is_miri_called_vs_inlined_rel(r))
            }))
}

fn run_in_process_variant_pair() -> (MetaVariantOutcome, MetaVariantOutcome) {
    let called = if HAS_ABORT_SCHEDULE {
        let self_exe = std::env::current_exe().expect("current_exe");
        parse_child_outcome_on(&self_exe, "--anneal-meta-called")
    } else {
        run_called_variant()
    };
    let inlined = if HAS_ABORT_SCHEDULE {
        let self_exe = std::env::current_exe().expect("current_exe");
        parse_child_outcome_on(&self_exe, "--anneal-meta-inlined")
    } else {
        run_inlined_variant()
    };
    (called, inlined)
}

fn compare_with_peer(peer: &std::path::Path, explicit_compare: bool) {
    let self_exe = std::env::current_exe().expect("current_exe");
    let self_called = parse_child_outcome_on(&self_exe, "--anneal-meta-called");
    let self_inlined = parse_child_outcome_on(&self_exe, "--anneal-meta-inlined");
    let peer_called = parse_child_outcome_on(peer, "--anneal-meta-called");
    let peer_inlined = parse_child_outcome_on(peer, "--anneal-meta-inlined");
    let check_called_opt = PINNED_META_RELATIONS.iter().any(|r| *r == "called_rustc_o0_vs_o2")
        || (explicit_compare && PINNED_META_RELATIONS.is_empty());
    let check_inlined_opt = PINNED_META_RELATIONS.iter().any(|r| *r == "inlined_rustc_o0_vs_o2")
        || (explicit_compare && PINNED_META_RELATIONS.is_empty());
    let check_called_vs_inlined = should_check_called_vs_inlined_in_process();

    if check_called_opt && cross_mode_outcomes_diverge(&self_called, &peer_called) {
        panic!(
            "metamorphic called_rustc_o0_vs_o2 divergence: self={self_called:?} vs peer={peer_called:?}"
        );
    }
    if check_inlined_opt && cross_mode_outcomes_diverge(&self_inlined, &peer_inlined) {
        panic!(
            "metamorphic inlined_rustc_o0_vs_o2 divergence: self={self_inlined:?} vs peer={peer_inlined:?}"
        );
    }
    if check_called_vs_inlined
        && (outcomes_diverge(&self_called, &self_inlined)
            || outcomes_diverge(&peer_called, &peer_inlined))
    {
        panic!(
            "metamorphic called vs source-inlined twin divergence: self=({self_called:?} vs {self_inlined:?}), peer=({peer_called:?} vs {peer_inlined:?})"
        );
    }
    let unreplayed = collect_unreplayed_pinned_relations(true);
    if !unreplayed.is_empty() {
        panic!(
            "pinned authority relation(s) {unreplayed:?} cannot be replayed by native rustc O0/O2 peer alone; run sibling `program_*.mir.lean` under Lean, `cargo miri` (with `-Zmiri-disable-isolation` if aborting), or `itree-diff --corpus-dir`"
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if let Some(arg1) = args.get(1).map(String::as_str) {
        if arg1 == "--anneal-meta-called" {
            let _ = run_called_variant();
            return;
        }
        if arg1 == "--anneal-meta-inlined" {
            let _ = run_inlined_variant();
            return;
        }
        if arg1 == "--compare-opt" || arg1 == "--anneal-compare-opt" {
            let peer = args
                .get(2)
                .expect("--compare-opt requires a path to the peer optimization binary");
            compare_with_peer(std::path::Path::new(peer), true);
            return;
        }
        if let Some(peer) = arg1
            .strip_prefix("--compare-opt=")
            .or_else(|| arg1.strip_prefix("--anneal-compare-opt="))
        {
            compare_with_peer(std::path::Path::new(peer), true);
            return;
        }
    }
    if !cfg!(miri) {
        if let Some(env_peer) = std::env::var_os("ANNEAL_COMPARE_OPT_BIN") {
            if !env_peer.is_empty() {
                compare_with_peer(std::path::Path::new(&env_peer), true);
                return;
            }
        }
        let self_exe = std::env::current_exe().expect("current_exe");
        if let Some(sibling) = discover_sibling_opt_peer(&self_exe) {
            compare_with_peer(&sibling, false);
            return;
        }
    }

    let needs_opt = PINNED_META_RELATIONS.iter().any(|r| is_rustc_o0_vs_o2_rel(r));
    let check_called_vs_inlined = should_check_called_vs_inlined_in_process();
    if check_called_vs_inlined {
        let (called, inlined) = run_in_process_variant_pair();
        if outcomes_diverge(&called, &inlined) {
            panic!(
                "metamorphic called vs source-inlined twin divergence: called={called:?} vs inlined={inlined:?}"
            );
        }
    }
    let unreplayed_external: Vec<&str> = collect_unreplayed_pinned_relations(false)
        .into_iter()
        .filter(|r| !is_rustc_o0_vs_o2_rel(r))
        .collect();
    if !unreplayed_external.is_empty() {
        panic!(
            "pinned authority relation(s) {unreplayed_external:?} cannot be replayed by standalone native rustc alone; run sibling `program_*.mir.lean` under Lean, `cargo miri` (with `-Zmiri-disable-isolation` if aborting), or `itree-diff --corpus-dir`"
        );
    }
    if needs_opt {
        panic!(
            "pinned cross-mode relation(s) {PINNED_META_RELATIONS:?} require O0 vs O2 comparison; pass --compare-opt <peer_exe> or build sibling *_o2 executable"
        );
    }
    if cfg!(miri) && HAS_ABORT_SCHEDULE {
        panic!(
            "abort-scheduled metamorphic reproducer cannot spawn child processes under Miri; run natively under rustc or run sibling `program_*.mir.lean` under Lean"
        );
    }
}
"#,
    );

    out
}

/// Render a standalone single-subject `-O0` vs `-O2` peer comparison runner
/// capturing exit success, exit code, Unix termination signal, and required
/// trace line, failing closed if either peer exits without emitting a trace.
pub(crate) fn render_single_opt_peer_compare_fns(
    child_fn: &str,
    discover_fn: &str,
    compare_fn: &str,
    subject_fn: &str,
    repro_label: &str,
) -> String {
    let mut out = format!(
        "\nfn {child_fn}(exe: &std::path::Path) -> (bool, Option<i32>, Option<i32>, Option<String>) {{\n\
         \x20   let out = std::process::Command::new(exe)\n\
         \x20       .arg(\"--anneal-single-run\")\n\
         \x20       .output()\n\
         \x20       .expect(\"spawn single opt peer\");\n\
         \x20   let stdout = String::from_utf8_lossy(&out.stdout);\n\
         \x20   for line in stdout.lines() {{\n\
         \x20       println!(\"{{line}}\");\n\
         \x20   }}\n\
         \x20   let trace = stdout.lines().rev().find_map(|line| {{\n\
         \x20       let t = line.trim();\n\
         \x20       if t.starts_with(\"ANNEAL_ITREE_TRACE_JSON:\") || t.starts_with(\"ANNEAL_ITREE_PRE_ABORT:\") {{\n\
         \x20           Some(t.to_string())\n\
         \x20       }} else {{\n\
         \x20           None\n\
         \x20       }}\n\
         \x20   }});\n\
         \x20   #[cfg(unix)]\n\
         \x20   let signal = {{\n\
         \x20       use std::os::unix::process::ExitStatusExt;\n\
         \x20       out.status.signal()\n\
         \x20   }};\n\
         \x20   #[cfg(not(unix))]\n\
         \x20   let signal = None;\n\
         \x20   (out.status.success(), out.status.code(), signal, trace)\n\
         }}\n",
    );
    out.push_str(&render_discover_sibling_opt_peer_fn(discover_fn));
    out.push_str(&format!(
        "fn {compare_fn}(peer: &std::path::Path) {{\n\
         \x20   let self_exe = std::env::current_exe().expect(\"current_exe\");\n\
         \x20   let self_res = {child_fn}(&self_exe);\n\
         \x20   let peer_res = {child_fn}(peer);\n\
         \x20   if self_res.3.is_none() || peer_res.3.is_none() {{\n\
         \x20       panic!(\"rustc O0 vs O2 {repro_label} child terminated without emitting a trace line: self={{self_res:?}} vs peer={{peer_res:?}}\");\n\
         \x20   }}\n\
         \x20   if self_res != peer_res {{\n\
         \x20       panic!(\"rustc O0 vs O2 cross-mode divergence: self={{self_res:?}} vs peer={{peer_res:?}}\");\n\
         \x20   }}\n\
         }}\n\
         fn main() {{\n\
         \x20   let args: Vec<String> = std::env::args().collect();\n\
         \x20   if let Some(arg1) = args.get(1).map(String::as_str) {{\n\
         \x20       if arg1 == \"--anneal-single-run\" {{\n\
         \x20           {subject_fn}();\n\
         \x20           return;\n\
         \x20       }}\n\
         \x20       if arg1 == \"--compare-opt\" || arg1 == \"--anneal-compare-opt\" {{\n\
         \x20           let peer = args.get(2).expect(\"--compare-opt requires peer path\");\n\
         \x20           {compare_fn}(std::path::Path::new(peer));\n\
         \x20           return;\n\
         \x20       }}\n\
         \x20       if let Some(peer) = arg1\n\
         \x20           .strip_prefix(\"--compare-opt=\")\n\
         \x20           .or_else(|| arg1.strip_prefix(\"--anneal-compare-opt=\"))\n\
         \x20       {{\n\
         \x20           {compare_fn}(std::path::Path::new(peer));\n\
         \x20           return;\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   if !cfg!(miri) {{\n\
         \x20       if let Some(env_peer) = std::env::var_os(\"ANNEAL_COMPARE_OPT_BIN\") {{\n\
         \x20           if !env_peer.is_empty() {{\n\
         \x20               {compare_fn}(std::path::Path::new(&env_peer));\n\
         \x20               return;\n\
         \x20           }}\n\
         \x20       }}\n\
         \x20       let self_exe = std::env::current_exe().expect(\"current_exe\");\n\
         \x20       if let Some(sibling) = {discover_fn}(&self_exe) {{\n\
         \x20           {compare_fn}(&sibling);\n\
         \x20           return;\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   panic!(\"{repro_label} fuzz reproducer requires O0 vs O2 comparison; pass --compare-opt <peer_exe> or build sibling *_o2 executable\");\n\
         }}\n",
    ));
    out
}

/// Render a standalone sibling `*_o2` / `*_o2.exe` discovery helper shared by
/// both `render_standalone_metamorphic_rust_harness_with_relations` and
/// `shrink::render_standalone_shrinkable_repro_rust`.
pub(crate) fn render_discover_sibling_opt_peer_fn(fn_name: &str) -> String {
    format!(
        "fn {fn_name}(self_exe: &std::path::Path) -> Option<std::path::PathBuf> {{\n\
         \x20   let file_name = self_exe.file_name()?.to_str()?;\n\
         \x20   let bytes = file_name.as_bytes();\n\
         \x20   let (base, ext) = if bytes.len() >= 4 && bytes[bytes.len() - 4..].eq_ignore_ascii_case(b\".exe\") {{\n\
         \x20       (&file_name[..file_name.len() - 4], &file_name[file_name.len() - 4..])\n\
         \x20   }} else {{\n\
         \x20       (file_name, \"\")\n\
         \x20   }};\n\
         \x20   let peer_name = if let Some(stem) = base.strip_suffix(\"_o2\").filter(|s| !s.is_empty()) {{\n\
         \x20       format!(\"{{stem}}{{ext}}\")\n\
         \x20   }} else {{\n\
         \x20       format!(\"{{base}}_o2{{ext}}\")\n\
         \x20   }};\n\
         \x20   let cand = self_exe.with_file_name(peer_name);\n\
         \x20   if cand != self_exe && cand.is_file() {{\n\
         \x20       Some(cand)\n\
         \x20   }} else {{\n\
         \x20       None\n\
         \x20   }}\n\
         }}\n"
    )
}

#[derive(Deserialize)]
struct RawTraceLine {
    outcome_kind: String,
    ret: Option<RawRetVal>,
    #[serde(default)]
    detail: String,
    boundary_slots: Vec<Vec<Option<u8>>>,
    caller_locals_preserved: bool,
    untouched_alloc_bytes_preserved: bool,
    padding_mask_respected: bool,
    violations: Vec<String>,
    events: Vec<ObservableEvent>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawRetVal {
    Scalar { kind_id: IntKind, bits: String },
    Bool { value: bool },
    Char { scalar: u32 },
    Ordering { value: OrderingVal },
    Unit,
    PaddedBytes { type_name: String, bytes: Vec<Option<u8>> },
}

impl TryFrom<RawRetVal> for TraceVal {
    type Error = String;

    fn try_from(v: RawRetVal) -> Result<Self, String> {
        match v {
            RawRetVal::Scalar { kind_id, bits } => {
                let parsed =
                    bits.parse::<u128>().map_err(|e| format!("parse scalar bits {bits:?}: {e}"))?;
                Ok(Self::Scalar { kind: kind_id, bits: kind_id.mask_bits(parsed) })
            }
            RawRetVal::Bool { value } => Ok(Self::Bool { value }),
            RawRetVal::Char { scalar } => Ok(Self::Char { scalar }),
            RawRetVal::Ordering { value } => Ok(Self::Ordering { value }),
            RawRetVal::Unit => Ok(Self::Unit),
            RawRetVal::PaddedBytes { type_name, bytes } => {
                Ok(Self::PaddedBytes { type_name, bytes })
            }
        }
    }
}

fn extract_unique_prefixed_line<'a>(
    authority: &str,
    stdout: &'a str,
    stderr: &str,
    prefix: &str,
) -> Result<&'a str, String> {
    let matches: Vec<&'a str> =
        stdout.lines().filter_map(|line| line.trim().strip_prefix(prefix)).collect();
    match matches.as_slice() {
        [single] => Ok(*single),
        [] => Err(format!(
            "{authority} output missing `{prefix}` line; stdout={stdout:?}, stderr={stderr:?}"
        )),
        many => Err(format!(
            "{authority} output emitted {} `{prefix}` lines (expected exactly 1); stdout={stdout:?}",
            many.len()
        )),
    }
}

#[derive(Deserialize)]
struct RawPreEntrySlots {
    boundary_slots: Vec<Vec<Option<u8>>>,
}

/// Parse an optional unique `ANNEAL_ITREE_PRE_ENTRY:` stdout line into
/// validated entry argument `boundary_slots`. Fails closed on duplicate or
/// malformed lines or count mismatches against `expected_entry_slots`.
pub fn parse_pre_entry_slots_stdout(
    authority: &str,
    stdout: &str,
    stderr: &str,
    expected_entry_slots: Option<usize>,
) -> Result<Option<Vec<Vec<Option<u8>>>>, String> {
    if !stdout.lines().any(|l| l.trim().starts_with(PRE_ENTRY_JSON_PREFIX)) {
        return Ok(None);
    }
    let json_str = extract_unique_prefixed_line(authority, stdout, stderr, PRE_ENTRY_JSON_PREFIX)?;
    let parsed: RawPreEntrySlots = serde_json::from_str(json_str)
        .map_err(|e| format!("parse {authority} pre-entry JSON: {e}; raw={json_str:?}"))?;
    validate_boundary_slots_for_outcome(
        authority,
        "pre_entry",
        None,
        expected_entry_slots,
        &parsed.boundary_slots,
    )?;
    Ok(Some(parsed.boundary_slots))
}

fn entry_slots_slice<'a>(
    outcome_kind: &str,
    boundary_slots: &'a [Vec<Option<u8>>],
) -> &'a [Vec<Option<u8>>] {
    match outcome_kind {
        "returned" | "unwound" | "aborted" => {
            &boundary_slots[..boundary_slots.len().saturating_sub(1)]
        }
        "fault_ub" => boundary_slots,
        _ => &[],
    }
}

fn verify_optional_pre_entry_parity(
    authority: &str,
    stdout: &str,
    stderr: &str,
    expected_entry_slots: Option<usize>,
    entry_slots: &[Vec<Option<u8>>],
) -> Result<Option<String>, String> {
    let pre = parse_pre_entry_slots_stdout(authority, stdout, stderr, expected_entry_slots)?;
    if let Some(pre_slots) = &pre
        && pre_slots.as_slice() != entry_slots
    {
        return Err(format!(
            "{authority} pre-entry boundary_slots mismatch: PRE_ENTRY={pre_slots:?} vs terminal entry={entry_slots:?}"
        ));
    }
    if pre.is_some() || expected_entry_slots.is_some() || !entry_slots.is_empty() {
        Ok(Some(compute_boundary_mem_digest(entry_slots)))
    } else {
        Ok(None)
    }
}

fn parse_raw_trace_json(
    authority: &str,
    stdout: &str,
    json_str: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> Result<AuthorityRunResult, String> {
    let parsed: RawTraceLine = serde_json::from_str(json_str)
        .map_err(|e| format!("parse {authority} trace JSON: {e}; raw={json_str:?}"))?;

    if parsed.outcome_kind == "unconsumed_schedule" {
        return Err(format!(
            "{authority} unconsumed scheduled environment actions: {}",
            parsed.detail
        ));
    }

    let parsed_ret = match parsed.outcome_kind.as_str() {
        "returned" => {
            let ret: TraceVal = parsed
                .ret
                .ok_or_else(|| format!("{authority} returned outcome missing `ret` payload"))?
                .try_into()?;
            Some(ret)
        }
        _ => None,
    };

    validate_boundary_slots_for_outcome(
        authority,
        &parsed.outcome_kind,
        parsed_ret.as_ref(),
        expected_entry_slots,
        &parsed.boundary_slots,
    )?;

    let entry_slice = entry_slots_slice(&parsed.outcome_kind, &parsed.boundary_slots);
    let entry_mem_digest = verify_optional_pre_entry_parity(
        authority,
        stdout,
        stderr,
        expected_entry_slots,
        entry_slice,
    )?;

    let mem_digest = compute_boundary_mem_digest(&parsed.boundary_slots);
    let outcome = match parsed.outcome_kind.as_str() {
        "returned" => TerminalOutcome::Returned {
            ret: parsed_ret.expect("checked returned payload"),
            mem_digest,
        },
        "unwound" => TerminalOutcome::Unwound { mem_digest },
        "aborted" => TerminalOutcome::Aborted { mem_digest },
        "fault_ub" => TerminalOutcome::FaultUb { detail: parsed.detail },
        other => {
            return Err(format!(
                "unknown {authority} outcome_kind {other:?} (detail={:?})",
                parsed.detail
            ));
        }
    };

    Ok(AuthorityRunResult {
        authority: authority.to_string(),
        outcome,
        spine: ObservableSpine { events: parsed.events },
        caller_frame_law: CallerFrameLaw {
            caller_locals_preserved: parsed.caller_locals_preserved,
            untouched_alloc_bytes_preserved: parsed.untouched_alloc_bytes_preserved,
            padding_mask_respected: parsed.padding_mask_respected,
            violations: parsed.violations,
        },
        tool_error: None,
        raw_diagnostics: stderr.to_string(),
        elapsed_ms,
        post_only_mem_digest: false,
        entry_mem_digest,
    })
}

/// Parse the single `ANNEAL_ITREE_TRACE_JSON:` stdout line emitted by a
/// standalone `rustc` or `miri` harness into an [`AuthorityRunResult`].
/// Rejects both `0` and `>= 2` JSON lines as framing errors.
pub fn parse_trace_json_stdout(
    authority: &str,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> Result<AuthorityRunResult, String> {
    parse_trace_json_stdout_with_expected_args(authority, stdout, stderr, elapsed_ms, None)
}

/// Entry-count-checked variant of [`parse_trace_json_stdout`] enforcing
/// zero-exit outcome authentication: co-occurring `ANNEAL_ITREE_PRE_ABORT:`
/// lines, `outcome_kind = "aborted"`, and unauthenticated
/// `outcome_kind = "fault_ub"` lines outside `anneal_rt::ScheduleDecodeFailed`
/// all fail closed.
pub fn parse_trace_json_stdout_with_expected_args(
    authority: &str,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> Result<AuthorityRunResult, String> {
    if stdout.lines().any(|l| l.trim().starts_with(PRE_ABORT_JSON_PREFIX)) {
        return Err(format!(
            "{authority} emitted unexpected `{PRE_ABORT_JSON_PREFIX}` alongside zero-exit `{TRACE_JSON_PREFIX}` line"
        ));
    }
    let json_str = extract_unique_prefixed_line(authority, stdout, stderr, TRACE_JSON_PREFIX)?;
    let res = parse_raw_trace_json(
        authority,
        stdout,
        json_str,
        stderr,
        elapsed_ms,
        expected_entry_slots,
    )?;
    match &res.outcome {
        TerminalOutcome::Returned { .. } | TerminalOutcome::Unwound { .. } => Ok(res),
        TerminalOutcome::FaultUb { detail } if is_rust_scheduled_return_decode_fault(detail) => {
            Ok(res)
        }
        other => Err(format!(
            "{authority} zero-exit trace disallowed non-authenticated outcome {other:?}"
        )),
    }
}

/// Parse the single `ANNEAL_ITREE_PRE_ABORT:` stdout line flushed immediately
/// before `std::process::abort()` when a scheduled `EnvAction::Abort` fires.
pub fn parse_pre_abort_stdout(
    authority: &str,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> Result<AuthorityRunResult, String> {
    parse_pre_abort_stdout_with_expected_args(authority, stdout, stderr, elapsed_ms, None)
}

/// Entry-count-checked variant of [`parse_pre_abort_stdout`].
pub fn parse_pre_abort_stdout_with_expected_args(
    authority: &str,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> Result<AuthorityRunResult, String> {
    if stdout.lines().any(|l| l.trim().starts_with(TRACE_JSON_PREFIX)) {
        return Err(format!(
            "{authority} emitted both `{PRE_ABORT_JSON_PREFIX}` and `{TRACE_JSON_PREFIX}`"
        ));
    }
    let json_str = extract_unique_prefixed_line(authority, stdout, stderr, PRE_ABORT_JSON_PREFIX)?;
    let res = parse_raw_trace_json(
        authority,
        stdout,
        json_str,
        stderr,
        elapsed_ms,
        expected_entry_slots,
    )?;
    if !matches!(res.outcome, TerminalOutcome::Aborted { .. }) {
        return Err(format!(
            "{authority} pre-abort line had non-aborted outcome {:?}",
            res.outcome
        ));
    }
    Ok(res)
}
