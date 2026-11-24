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
        !self.env_schedule.is_empty() || self.lean_program_spec.requires_strict_refusal()
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

/// Render a self-contained Rust executable harness for `rustc` (`-O0`/`-O2`)
/// and `miri` that installs `case.env_schedule`, captures runtime entry
/// argument bytes into `boundary_slots`, materializes a `#[repr(C)]` padded
/// caller stack frame via `core::hint::black_box`, catches unwinds vs invalid
/// schedule bit patterns cleanly, and prints one `ANNEAL_ITREE_TRACE_JSON:`
/// line (or `ANNEAL_ITREE_PRE_ABORT:` right before `std::process::abort()`).
pub fn render_standalone_rust_harness(case: &TraceTestCase) -> String {
    let source = case.traced_rust_source.as_deref().unwrap_or(&case.pure_rust_source);
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

    let mut out = String::new();
    for attr in &crate_attrs {
        out.push_str(attr);
        out.push('\n');
    }
    out.push_str(render_embedded_trace_prelude());
    out.push_str(
        "\n#[allow(dead_code, unused_variables, unused_imports, clippy::all)]\nmod subject {\n",
    );
    out.push_str("    use crate::anneal_rt;\n");
    for line in &body_lines {
        out.push_str("    ");
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("}\n\n");

    let mut sched_setup = String::new();
    for (callee, queue) in &case.env_schedule.per_callee {
        for act in queue {
            let rendered = render_rt_env_action(act);
            let _ =
                writeln!(sched_setup, "    anneal_rt::push_callee_action({callee:?}, {rendered});");
        }
    }
    for act in &case.env_schedule.global {
        let rendered = render_rt_env_action(act);
        let _ = writeln!(sched_setup, "    anneal_rt::push_global_action({rendered});");
    }

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

    let _ = writeln!(
        out,
        r#"fn main() {{
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
                anneal_rt::finish_json("fault_ub", "null", &sched_err.0);
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
        sched_setup = sched_setup,
        arg_bindings = arg_bindings,
        entry = case.entry_fn,
        arg_list = arg_list,
        ret_bytes_expr = ret_bytes_expr,
        ret_json_expr = ret_json_expr,
    );

    out
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
