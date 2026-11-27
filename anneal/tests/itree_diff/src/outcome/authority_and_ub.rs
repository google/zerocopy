// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Authority run results, spine comparison modes, disclosed gaps, and UB
//! fault classification.

use super::*;

/// How strictly observable spines should be compared between authorities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SpineCompareMode {
    /// Compare full `CallEnter`/`CallReturn`/`CallUnwind`, `CallerFrameCheck`,
    /// AND `BranchTag` sequences.
    FullBranchesAndCalls,
    /// Compare branch-erased call events and `CallerFrameCheck` checkpoints in
    /// exact relative interleaving order (ignoring `BranchTag` transitions).
    ObsErasedCallsOnly,
    /// Compare only terminal outcome + caller-frame preservation flags.
    OutcomeOnly,
}

/// Complete receipt returned by a single execution authority (`rustc`, `miri`,
/// `lean`, or `anneal-mir-eval`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorityRunResult {
    pub authority: String,
    pub outcome: TerminalOutcome,
    pub spine: ObservableSpine,
    pub caller_frame_law: CallerFrameLaw,
    pub tool_error: Option<String>,
    pub raw_diagnostics: String,
    pub elapsed_ms: u64,
    #[serde(default)]
    pub post_only_mem_digest: bool,
    /// SHA-256 hex digest of entry-argument `boundary_slots` captured before
    /// executing the subject body (`None` only in value-only / synthetic unit
    /// fixtures omitting entry slots).
    #[serde(default)]
    pub entry_mem_digest: Option<String>,
}

impl AuthorityRunResult {
    pub fn tool_error(authority: impl Into<String>, detail: impl Into<String>) -> Self {
        let d = detail.into();
        Self {
            authority: authority.into(),
            outcome: TerminalOutcome::CaptureRefused { reason: d.clone() },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: Some(d),
            raw_diagnostics: String::new(),
            elapsed_ms: 0,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        }
    }

    pub fn skipped_for_ub(authority: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            authority: authority.into(),
            outcome: TerminalOutcome::CaptureRefused { reason: reason.into() },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: String::new(),
            elapsed_ms: 0,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        }
    }
}

/// Explicit disclosed semantic gap categories documented at Anneal's boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DisclosedGapKind {
    /// Caller-supplied raw pointer aliasing outside value-only entry memory.
    CallerRawPtrAliasing,
    /// Selected-unit scope (`VerificationScope.unit`) omitting external
    /// callees.
    SelectedUnitScope,
    /// Unbridged Rust construct intentionally outside the modeled MIR fragment.
    UnbridgedSemantics,
}

/// Specification pairing a [`DisclosedGapKind`] with the exact Lean or capture
/// boundary diagnostic marker required to admit a discrepancy as a
/// [`TraceVerdict::DisclosedGapArtifact`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DisclosedGapSpec {
    pub kind: DisclosedGapKind,
    pub expected_fault_marker: String,
}

impl DisclosedGapSpec {
    pub fn new(kind: DisclosedGapKind, expected_fault_marker: impl Into<String>) -> Self {
        Self { kind, expected_fault_marker: expected_fault_marker.into() }
    }

    /// Return `true` only when `outcome` is a Lean `CaptureRefused` or
    /// `FaultUb` whose diagnostic contains `self.expected_fault_marker` and
    /// carries no unrelated arithmetic, division, unreachable, or generic step
    /// UB markers.
    pub fn matches_lean_outcome(&self, outcome: &TerminalOutcome) -> bool {
        let marker = self.expected_fault_marker.trim();
        if marker.is_empty() {
            return false;
        }
        let detail = match outcome {
            TerminalOutcome::CaptureRefused { reason } => reason.as_str(),
            TerminalOutcome::FaultUb { detail } => detail.as_str(),
            TerminalOutcome::Returned { .. }
            | TerminalOutcome::Unwound { .. }
            | TerminalOutcome::Aborted { .. }
            | TerminalOutcome::Diverged { .. } => return false,
        };
        if !detail.contains(marker) {
            return false;
        }
        let lower = detail.to_ascii_lowercase();
        const UNRELATED_FAULT_MARKERS: &[&str] = &[
            "overflow",
            "division by zero",
            "div by zero",
            "divide by zero",
            "remainder by zero",
            "unreachable",
            "uninitialized return",
            "uninit return",
            "assert condition undefined",
            "diverging call",
            "trusted.mirsemantics.faultkind.undefined",
        ];
        if UNRELATED_FAULT_MARKERS.iter().any(|bad| lower.contains(bad)) {
            return false;
        }
        if self.kind == DisclosedGapKind::CallerRawPtrAliasing {
            let marker_lower = marker.to_ascii_lowercase();
            const PTR_MARKERS: &[&str] =
                &["*const", "*mut", "ptr", "pointer", "deref", "addr", "alias", "provenance"];
            if !PTR_MARKERS.iter().any(|p| marker_lower.contains(p)) {
                return false;
            }
        }
        true
    }
}

/// Normalized Undefined Behavior cause category used to verify that two
/// authorities reporting [`TerminalOutcome::FaultUb`] faulted for compatible
/// semantic reasons (preventing an earlier unrelated UB in Miri from silently
/// matching a later UB in Lean or `anneal-mir-eval`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UbFaultClass {
    /// Invalid scheduled boundary return payload (`ReturnBytes` bit pattern or
    /// byte length rejected before resuming caller).
    ScheduledReturnDecode,
    /// Execution entered `unreachable_unchecked` or
    /// `TerminatorKind.unreachable`, unwound into `UnwindAction.unreachable` or
    /// a `nounwind` frame, or returned from a diverging `!` call.
    UnreachableOrNoUnwind,
    /// Unchecked shift overflow (`unchecked_shl` / `unchecked_shr` /
    /// `.shlUnchecked` / `.shrUnchecked`).
    UncheckedShiftOverflow,
    /// Unchecked integer arithmetic overflow (`unchecked_add`/`sub`/`mul`) or
    /// division/remainder UB (division by zero or `MIN / -1`).
    UncheckedArithOrDivOverflow,
    /// Pointer dereference, alignment, null, out-of-bounds, provenance,
    /// deallocation, or borrow-stack / Tree Borrows violation.
    PointerOrMemoryAccess,
    /// Invalid scalar/enum/bool/char bit pattern, uninitialized read, or dead
    /// local access outside scheduled return decoding.
    InvalidValueOrUninit,
    /// Uncategorized / synthetic UB diagnostic.
    Unclassified,
}

fn extract_rust_scheduled_decode_callee(detail: &str) -> Option<&str> {
    if let Some(rest) = detail.strip_prefix("callee `")
        && let Some((callee, reason)) = rest.split_once("` scheduled ReturnBytes invalid: ")
        && !callee.is_empty()
        && !reason.trim().is_empty()
    {
        return Some(callee);
    }
    None
}

/// Return `true` only when `detail` matches the standalone Rust/Miri harness
/// `anneal_rt::ScheduleDecodeFailed` message emitted on zero-exit
/// `ANNEAL_ITREE_TRACE_JSON` `fault_ub` output.
pub fn is_rust_scheduled_return_decode_fault(detail: &str) -> bool {
    extract_rust_scheduled_decode_callee(detail).is_some()
}

fn extract_scheduled_decode_callee(detail: &str) -> Option<&str> {
    if let Some(callee) = extract_rust_scheduled_decode_callee(detail) {
        return Some(callee);
    }
    if let Some(callee) = detail.strip_prefix("invalid scheduled ReturnBytes for ") {
        let trimmed = callee.trim();
        if !trimmed.is_empty() {
            return Some(trimmed);
        }
    }
    None
}

/// Normalize a Miri, Lean `ITreeDriver`, `anneal-mir-eval`, or standalone Rust
/// harness `FaultUb` diagnostic into a canonical [`UbFaultClass`].
pub fn classify_ub_fault_detail(detail: &str) -> UbFaultClass {
    let lower = detail.to_ascii_lowercase();
    if lower.contains("scheduled returnbytes") {
        UbFaultClass::ScheduledReturnDecode
    } else if lower.contains("unreachable")
        || lower.contains("does not allow unwinding")
        || lower.contains("from diverging call")
    {
        UbFaultClass::UnreachableOrNoUnwind
    } else if lower.contains("overflowing shift")
        || lower.contains("unchecked_shl")
        || lower.contains("unchecked_shr")
        || lower.contains("unchecked shift")
        || lower.contains("shift overflow")
    {
        UbFaultClass::UncheckedShiftOverflow
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
        UbFaultClass::UncheckedArithOrDivOverflow
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
        UbFaultClass::PointerOrMemoryAccess
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
        UbFaultClass::InvalidValueOrUninit
    } else {
        UbFaultClass::Unclassified
    }
}

/// Return `true` only when two `FaultUb` diagnostics denote compatible UB fault
/// causes (matching [`UbFaultClass`] and, for `ScheduledReturnDecode`, matching
/// callee identity whenever both diagnostics name a callee; `Unclassified`
/// strings match only identical non-empty synthetic tokens and never match a
/// classified UB category).
pub fn ub_fault_causes_compatible(ref_detail: &str, cand_detail: &str) -> bool {
    let c1 = classify_ub_fault_detail(ref_detail);
    let c2 = classify_ub_fault_detail(cand_detail);
    match (c1, c2) {
        (UbFaultClass::Unclassified, UbFaultClass::Unclassified) => {
            let t1 = ref_detail.trim();
            !t1.is_empty() && t1 == cand_detail.trim()
        }
        (UbFaultClass::ScheduledReturnDecode, UbFaultClass::ScheduledReturnDecode) => {
            if let (Some(cal1), Some(cal2)) = (
                extract_scheduled_decode_callee(ref_detail),
                extract_scheduled_decode_callee(cand_detail),
            ) {
                cal1 == cal2
            } else {
                true
            }
        }
        (a, b) if a != UbFaultClass::Unclassified && b != UbFaultClass::Unclassified => a == b,
        _ => false,
    }
}

/// Expected Undefined Behavior fault cause and authority diagnostic markers
/// required on [`crate::spec::ExpectedCaseClass::UndefinedBehavior`] cases so
/// negative UB tests cannot pass for an unrelated fault.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedUbSpec {
    pub class: UbFaultClass,
    pub miri_marker: String,
    #[serde(default)]
    pub lean_marker: Option<String>,
    #[serde(default)]
    pub lean_refusal_marker: Option<String>,
    #[serde(default)]
    pub mir_eval_marker: Option<String>,
}

impl ExpectedUbSpec {
    pub fn new(
        class: UbFaultClass,
        miri_marker: impl Into<String>,
        lean_marker: Option<&str>,
    ) -> Self {
        Self {
            class,
            miri_marker: miri_marker.into(),
            lean_marker: lean_marker.map(str::to_owned),
            lean_refusal_marker: None,
            mir_eval_marker: None,
        }
    }

    /// Require conservative Lean `CaptureRefused` outcomes on this UB case (or
    /// in `StrictVerbatim` when the spec also requires strict-mode refusal) to
    /// contain `marker` instead of accepting unrelated refusals.
    pub fn with_lean_refusal_marker(mut self, marker: impl Into<String>) -> Self {
        self.lean_refusal_marker = Some(marker.into());
        self
    }

    /// Require `anneal-mir-eval` `FaultUb` diagnostics to match `marker`.
    pub fn with_mir_eval_marker(mut self, marker: impl Into<String>) -> Self {
        self.mir_eval_marker = Some(marker.into());
        self
    }
}

/// Expected reference outcome shape on
/// [`crate::spec::ExpectedCaseClass::ConservativeOverApprox`] cases.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConservativeRefKind {
    /// Reference (`rustc`/`miri`) returns normally (`Returned`).
    Returned,
    /// Reference (`rustc`/`miri`) panics/unwinds (`Unwound`).
    Unwound,
    /// Reference (`rustc`/`miri`) aborts (`Aborted`).
    Aborted,
}

impl ConservativeRefKind {
    /// Return `true` when `outcome` matches the expected reference kind.
    pub fn matches_outcome(self, outcome: Option<&TerminalOutcome>) -> bool {
        match self {
            Self::Returned => matches!(outcome, Some(TerminalOutcome::Returned { .. })),
            Self::Unwound => matches!(outcome, Some(TerminalOutcome::Unwound { .. })),
            Self::Aborted => matches!(outcome, Some(TerminalOutcome::Aborted { .. })),
        }
    }
}

/// Expected conservative refusal cause and reference outcome binding
/// required on [`crate::spec::ExpectedCaseClass::ConservativeOverApprox`]
/// cases so negative tests cannot pass vacuously via unrelated refusals or
/// step-fuel exhaustion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedConservativeSpec {
    pub ref_kind: ConservativeRefKind,
    pub lean_marker: String,
}

impl ExpectedConservativeSpec {
    pub fn new(ref_kind: ConservativeRefKind, lean_marker: impl Into<String>) -> Self {
        Self { ref_kind, lean_marker: lean_marker.into() }
    }
}

/// Disposition of a metamorphic multi-call vs source-inlined twin check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetamorphicStatus {
    /// Both multi-call (`CompositionalITree`) and source-inlined
    /// (`StrictVerbatim`) Lean executions completed non-conservatively and
    /// matched across all active authorities.
    Passed,
    /// Either the multi-call or source-inlined Lean leg conservatively refused
    /// (`CaptureRefused`) or exhausted step fuel (`Diverged`), while all
    /// non-conservative compiler and Miri checks succeeded.
    SkippedConservative { reason: String },
    /// Semantic disagreement, `CallerFrameLaw` failure, or `ToolError` between
    /// the multi-call and source-inlined twins.
    Failed,
}
