// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Hierarchical 6-pass fast-leg-first delta shrinker, canonical alpha-renamer,
//! and standalone `repro_<skel_hash>.rs` + `.mir.lean` witness bundle emitter.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    fs,
    path::Path,
    time::{Duration, Instant},
};

use serde::{Deserialize, Serialize};

use crate::{
    CaseReport,
    fuzzer::{FuzzArithOp, FuzzProgram, FuzzStep},
    outcome::{
        AuthorityRunResult, IntKind, MetamorphicStatus, TerminalOutcome, TraceVerdict,
        UbFaultClass, classify_ub_fault_detail, sha256_hex,
    },
    trace_observer::{EnvAction, EnvSchedule},
};

/// Evaluation and wall-clock budget for [`shrink_fuzz_program_with_budget`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkBudget {
    pub max_evals: usize,
    pub max_duration: Duration,
}

impl Default for ShrinkBudget {
    fn default() -> Self {
        Self { max_evals: 256, max_duration: Duration::from_secs(120) }
    }
}

/// Strategy used by the two-tier fast-leg-first oracle during shrinking.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FastLegStrategy {
    /// Run Miri first and require `FaultUb` with matching `ref_ub_class`.
    MiriUbFirst,
    /// Run Miri first when available as a UB guard, then run `rustc -O0`/`-O2`
    /// (plus the source-inlined twin when `sig` pins metamorphic `rustc`
    /// relations such as `rustc_called_vs_inlined`).
    RustcDualFirst,
    /// Run Miri + `rustc` first (skipping Lean and metamorphic twins).
    MiriAndRustcFirst,
    /// Run Lean first and require `FaultUb` matching `lean_ub_class`.
    LeanUbFirst,
    /// Evaluate full 4-way differential oracle directly.
    #[default]
    FullFourWay,
}

impl FastLegStrategy {
    /// Select the cheapest rejecting authority leg for `sig` given the active
    /// authorities in the session.
    pub fn select(
        sig: &ShrinkFailureSignature,
        has_miri: bool,
        has_rustc: bool,
        has_lean: bool,
    ) -> Self {
        if sig.mismatch_category == "metamorphic_duality" {
            let only_rustc_meta = !sig.metamorphic_relations.is_empty()
                && sig.metamorphic_relations.iter().all(|r| {
                    matches!(
                        r.as_str(),
                        "called_rustc_o0_vs_o2"
                            | "inlined_rustc_o0_vs_o2"
                            | "rustc_called_vs_inlined"
                    )
                });
            if only_rustc_meta && has_rustc {
                return Self::RustcDualFirst;
            }
            let only_miri_ub_meta = !sig.metamorphic_relations.is_empty()
                && sig.metamorphic_relations.iter().all(|r| {
                    matches!(r.as_str(), "called_miri_vs_lean_ub" | "inlined_miri_vs_lean_ub")
                });
            if only_miri_ub_meta && has_miri && sig.ref_ub_class.is_some() {
                return Self::MiriUbFirst;
            }
            return Self::FullFourWay;
        }
        if sig.ref_outcome_kind == "fault_ub" && has_miri {
            return Self::MiriUbFirst;
        }
        if (sig.mismatch_category == "rustc_o0_o2"
            || (sig.mismatch_category == "spine_mismatch"
                && sig.spine_relation.as_deref() == Some("rustc_o0_vs_o2")))
            && has_rustc
        {
            return Self::RustcDualFirst;
        }
        if (sig.mismatch_category == "miri_vs_rustc"
            || (sig.mismatch_category == "spine_mismatch"
                && sig.spine_relation.as_deref() == Some("miri_vs_rustc_o0")))
            && has_miri
            && has_rustc
        {
            return Self::MiriAndRustcFirst;
        }
        if sig.verdict_kind == "undeclared_ub_fault" && has_lean && sig.lean_ub_class.is_some() {
            return Self::LeanUbFirst;
        }
        Self::FullFourWay
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::MiriUbFirst => "miri_ub_first",
            Self::RustcDualFirst => "rustc_dual_first",
            Self::MiriAndRustcFirst => "miri_and_rustc_first",
            Self::LeanUbFirst => "lean_ub_first",
            Self::FullFourWay => "full_four_way",
        }
    }
}

/// Telemetry counters recorded across the two-tier oracle and 6 shrink passes.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkPassStats {
    pub fast_leg_strategy: FastLegStrategy,
    pub fast_leg_evaluations: usize,
    pub fast_leg_rejections: usize,
    pub full_oracle_evaluations: usize,
    pub final_full_confirmations: usize,
    pub def_use_filter_skips: usize,
    pub schedule_ddmin_reductions: usize,
    pub step_ddmin_reductions: usize,
    pub call_cfg_collapse_reductions: usize,
    pub type_layout_narrow_reductions: usize,
    pub stride_diff_proxy_reductions: usize,
    pub alpha_rename_applied: usize,
}

/// Structured failure signature pinning the exact semantic failure class during
/// shrinking so candidates can never drift across UB classes, from missed-UB
/// into a value mismatch, or into a `ToolError`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ShrinkFailureSignature {
    pub verdict_kind: &'static str,
    pub ref_outcome_kind: &'static str,
    pub lean_outcome_kind: &'static str,
    pub mismatch_category: &'static str,
    #[serde(default)]
    pub ref_ub_class: Option<UbFaultClass>,
    #[serde(default)]
    pub lean_ub_class: Option<UbFaultClass>,
    #[serde(default)]
    pub lean_fault_site_kind: String,
    #[serde(default)]
    pub metamorphic_relations: Vec<String>,
    #[serde(default)]
    pub metamorphic_leg_kinds: String,
    #[serde(default)]
    pub spine_relation: Option<String>,
}

impl<'de> serde::Deserialize<'de> for ShrinkFailureSignature {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct RawSig {
            verdict_kind: String,
            ref_outcome_kind: String,
            lean_outcome_kind: String,
            mismatch_category: String,
            #[serde(default)]
            ref_ub_class: Option<UbFaultClass>,
            #[serde(default)]
            lean_ub_class: Option<UbFaultClass>,
            #[serde(default)]
            lean_fault_site_kind: String,
            #[serde(default)]
            metamorphic_relations: Vec<String>,
            #[serde(default)]
            metamorphic_leg_kinds: String,
            #[serde(default)]
            spine_relation: Option<String>,
        }
        let raw = RawSig::deserialize(deserializer)?;
        Ok(Self {
            verdict_kind: parse_verdict_kind::<D::Error>(&raw.verdict_kind)?,
            ref_outcome_kind: parse_outcome_kind::<D::Error>(&raw.ref_outcome_kind)?,
            lean_outcome_kind: parse_outcome_kind::<D::Error>(&raw.lean_outcome_kind)?,
            mismatch_category: parse_mismatch_category::<D::Error>(&raw.mismatch_category)?,
            ref_ub_class: raw.ref_ub_class,
            lean_ub_class: raw.lean_ub_class,
            lean_fault_site_kind: raw.lean_fault_site_kind,
            metamorphic_relations: raw.metamorphic_relations,
            metamorphic_leg_kinds: raw.metamorphic_leg_kinds,
            spine_relation: raw.spine_relation,
        })
    }
}

fn parse_verdict_kind<E: serde::de::Error>(s: &str) -> Result<&'static str, E> {
    match s {
        "unsound_accept" => Ok("unsound_accept"),
        "undeclared_ub_fault" => Ok("undeclared_ub_fault"),
        other => Err(E::custom(format!("unknown verdict_kind `{other}`"))),
    }
}

fn parse_outcome_kind<E: serde::de::Error>(s: &str) -> Result<&'static str, E> {
    match s {
        "returned" => Ok("returned"),
        "unwound" => Ok("unwound"),
        "aborted" => Ok("aborted"),
        "diverged" => Ok("diverged"),
        "fault_ub" => Ok("fault_ub"),
        "capture_refused" => Ok("capture_refused"),
        "none" => Ok("none"),
        other => Err(E::custom(format!("unknown outcome_kind `{other}`"))),
    }
}

fn parse_mismatch_category<E: serde::de::Error>(s: &str) -> Result<&'static str, E> {
    match s {
        "metamorphic_duality" => Ok("metamorphic_duality"),
        "strict_probe_accepted_multicall" => Ok("strict_probe_accepted_multicall"),
        "caller_frame_law" => Ok("caller_frame_law"),
        "rustc_o0_o2" => Ok("rustc_o0_o2"),
        "miri_vs_rustc" => Ok("miri_vs_rustc"),
        "ub_cause_mismatch" => Ok("ub_cause_mismatch"),
        "missed_ub" => Ok("missed_ub"),
        "spine_mismatch" => Ok("spine_mismatch"),
        "terminal_outcome_mismatch" => Ok("terminal_outcome_mismatch"),
        "spurious_lean_ub" => Ok("spurious_lean_ub"),
        other => Err(E::custom(format!("unknown mismatch_category `{other}`"))),
    }
}

/// Normalize a Lean `TerminalOutcome` into a canonical fault-site or terminal
/// tag for `ShrinkFailureSignature` and post-shrink deduplication.
pub fn normalize_lean_fault_site_kind(outcome: &TerminalOutcome) -> String {
    match outcome {
        TerminalOutcome::Returned { .. } => "returned".to_string(),
        TerminalOutcome::Unwound { .. } => "unwound".to_string(),
        TerminalOutcome::Aborted { .. } => "aborted".to_string(),
        TerminalOutcome::Diverged { .. } => "diverged".to_string(),
        TerminalOutcome::CaptureRefused { reason } => {
            let lower = reason.to_ascii_lowercase();
            if lower.contains("unsupported terminator") {
                "unsupported_terminator".to_string()
            } else if lower.contains("external callee unsupported") {
                "external_callee_unsupported".to_string()
            } else if lower.contains("initstateby unsupported") || lower.contains("initstate") {
                "unsupported_init_state".to_string()
            } else if lower.contains("faultkind.unsupported") {
                "unsupported_step".to_string()
            } else {
                "capture_refused".to_string()
            }
        }
        TerminalOutcome::FaultUb { detail } => {
            let lower = detail.to_ascii_lowercase();
            if lower.contains("pointer dereference undefined") {
                "assert_ptr_deref".to_string()
            } else if lower.contains("pointer or memory access undefined") {
                "assign_or_mem_deref".to_string()
            } else if lower.contains("dead local write undefined") {
                "dead_local_write".to_string()
            } else if lower.contains("uninitialized or dead return slot") {
                "dead_or_uninit_return".to_string()
            } else if lower.contains("unchecked shift overflow") {
                "unchecked_shift".to_string()
            } else if lower.contains("unchecked arithmetic overflow") {
                "unchecked_arith".to_string()
            } else if lower.contains("division or remainder by zero") {
                "div_or_rem_zero".to_string()
            } else if lower.contains("entering unreachable code") {
                "unreachable".to_string()
            } else if lower.contains("uninitialized or invalid value undefined") {
                "uninit_or_invalid_value".to_string()
            } else {
                match classify_ub_fault_detail(detail) {
                    UbFaultClass::ScheduledReturnDecode => "scheduled_return_decode".to_string(),
                    UbFaultClass::UnreachableOrNoUnwind => "unreachable".to_string(),
                    UbFaultClass::UncheckedShiftOverflow => "unchecked_shift".to_string(),
                    UbFaultClass::UncheckedArithOrDivOverflow => "unchecked_arith".to_string(),
                    UbFaultClass::PointerOrMemoryAccess => "assign_or_mem_deref".to_string(),
                    UbFaultClass::InvalidValueOrUninit => "uninit_or_invalid_value".to_string(),
                    UbFaultClass::Unclassified => "unclassified_ub".to_string(),
                }
            }
        }
    }
}

fn extract_metamorphic_relations_from_detail(detail: &str) -> Vec<String> {
    let mut rels = Vec::new();
    for part in detail.split("; ") {
        let trimmed = part.trim();
        let rel = if trimmed.contains("Lean multi-call vs source-inlined outcome mismatch") {
            Some("lean_called_vs_inlined")
        } else if trimmed.contains("original multi-call rustc O0 vs O2 mismatch") {
            Some("called_rustc_o0_vs_o2")
        } else if trimmed.contains("source-inlined twin rustc O0 vs O2 mismatch") {
            Some("inlined_rustc_o0_vs_o2")
        } else if trimmed.contains("rustc multi-call vs source-inlined mismatch") {
            Some("rustc_called_vs_inlined")
        } else if trimmed.contains("source-inlined twin rustc-O0 vs Lean StrictVerbatim mismatch") {
            Some("inlined_rustc_vs_lean")
        } else if trimmed
            .contains("original multi-call rustc-O0 vs Lean CompositionalITree mismatch")
        {
            Some("called_rustc_vs_lean")
        } else if trimmed.contains("source-inlined twin Miri detected UB") {
            Some("inlined_miri_vs_lean_ub")
        } else if trimmed.contains("original multi-call Miri detected UB") {
            Some("called_miri_vs_lean_ub")
        } else if trimmed.contains("source-inlined twin skipped host rustc") {
            Some("inlined_skipped_ub_lean_accept")
        } else if trimmed.contains("original multi-call skipped host rustc") {
            Some("called_skipped_ub_lean_accept")
        } else if trimmed.contains("Miri multi-call vs source-inlined mismatch") {
            Some("miri_called_vs_inlined")
        } else if trimmed.contains("CallerFrameLaw failed in metamorphic pair") {
            Some("metamorphic_caller_frame_law")
        } else {
            None
        };
        if let Some(r) = rel
            && !rels.iter().any(|x| x == r)
        {
            rels.push(r.to_string());
        }
    }
    if rels.is_empty() {
        rels.push("metamorphic_unspecified".to_string());
    }
    rels
}

pub(crate) fn sanitize_auth_tag(raw: &str) -> String {
    raw.trim()
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_lowercase() } else { '_' })
        .collect()
}

fn find_matching_bracket_end(s: &str, open_idx: usize) -> Option<usize> {
    let rest = s.get(open_idx..)?;
    if !rest.starts_with('[') {
        return None;
    }
    let mut depth = 0usize;
    let mut in_str = false;
    let mut escape = false;
    for (off, ch) in rest.char_indices() {
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
            '[' => depth += 1,
            ']' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(open_idx + off + 1);
                }
            }
            _ => {}
        }
    }
    None
}

fn extract_spine_relation_from_detail(detail: &str) -> Option<String> {
    let head = detail.split("; secondary ").next().unwrap_or(detail).trim();
    if head.starts_with("rustc O0 vs O2") {
        return Some("rustc_o0_vs_o2".to_string());
    }
    if head.starts_with("miri vs rustc-O0") {
        return Some("miri_vs_rustc_o0".to_string());
    }
    for marker in ["spine mismatch: ", "event interleaving mismatch: "] {
        let Some(marker_idx) = head.find(marker) else {
            continue;
        };
        let rest = &head[marker_idx + marker.len()..];
        let Some(eq1) = rest.find("=[") else {
            continue;
        };
        let ref_auth = rest[..eq1].trim();
        if ref_auth.is_empty() {
            continue;
        }
        let Some(close1) = find_matching_bracket_end(rest, eq1 + 1) else {
            continue;
        };
        let Some(after_vs) = rest[close1..].strip_prefix(" vs ") else {
            continue;
        };
        let Some(eq2) = after_vs.find("=[") else {
            continue;
        };
        let cand_auth = after_vs[..eq2].trim();
        if cand_auth.is_empty() {
            continue;
        }
        return Some(format!(
            "{}_vs_{}",
            sanitize_auth_tag(ref_auth),
            sanitize_auth_tag(cand_auth)
        ));
    }
    None
}

impl ShrinkFailureSignature {
    /// Extract a shrinkable semantic failure signature from a full
    /// [`CaseReport`], pinning exact UB fault classes, fault site kind, and
    /// metamorphic relations (scoped exclusively to primary
    /// `metamorphic_duality` verdicts).
    pub fn from_case_report(report: &CaseReport) -> Option<Self> {
        let ref_leg = report.miri.as_ref().or(if report.rustc_dual.skipped_for_ub {
            None
        } else {
            Some(&report.rustc_dual.o0)
        });
        let mut sig = Self::from_verdict_and_legs(&report.verdict, ref_leg, report.lean.as_ref())?;
        let equal_outcome_authority_spine = !report.rustc_dual.skipped_for_ub
            && ((sig.mismatch_category == "rustc_o0_o2"
                && report.rustc_dual.o0.outcome.semantically_eq(&report.rustc_dual.o2.outcome))
                || (sig.mismatch_category == "miri_vs_rustc"
                    && report.miri.as_ref().is_some_and(|m| {
                        m.outcome.semantically_eq(&report.rustc_dual.o0.outcome)
                    })));
        if equal_outcome_authority_spine {
            sig.spine_relation = Some(if sig.mismatch_category == "rustc_o0_o2" {
                "rustc_o0_vs_o2".to_string()
            } else {
                "miri_vs_rustc_o0".to_string()
            });
            sig.mismatch_category = "spine_mismatch";
        }
        if sig.mismatch_category == "metamorphic_duality"
            && let Some(m) = &report.metamorphic
        {
            if m.tool_error.is_some() {
                return None;
            }
            if matches!(m.status, MetamorphicStatus::Failed) {
                if !m.failed_relations.is_empty() {
                    sig.metamorphic_relations = m.failed_relations.clone();
                }
                sig.metamorphic_leg_kinds = m.twin_outcome_summary.clone();
            }
        }
        Some(sig)
    }

    /// Extract a shrinkable semantic failure signature, returning `None` for
    /// non-failing verdicts AND for `ToolError` (so `ToolError` is never
    /// accepted as a valid shrink step).
    pub fn from_verdict_and_legs(
        verdict: &TraceVerdict,
        reference: Option<&AuthorityRunResult>,
        lean: Option<&AuthorityRunResult>,
    ) -> Option<Self> {
        if reference.is_some_and(|r| r.tool_error.is_some())
            || lean.is_some_and(|l| l.tool_error.is_some())
        {
            return None;
        }
        let ref_kind = reference.map(|r| r.outcome.kind_tag()).unwrap_or("none");
        let lean_kind = lean.map(|l| l.outcome.kind_tag()).unwrap_or("none");
        let ref_ub_class = reference.and_then(|r| match &r.outcome {
            TerminalOutcome::FaultUb { detail } => Some(classify_ub_fault_detail(detail)),
            _ => None,
        });
        let lean_ub_class = lean.and_then(|l| match &l.outcome {
            TerminalOutcome::FaultUb { detail } => Some(classify_ub_fault_detail(detail)),
            _ => None,
        });
        let lean_fault_site_kind =
            lean.map(|l| normalize_lean_fault_site_kind(&l.outcome)).unwrap_or_default();

        match verdict {
            TraceVerdict::UnsoundAccept { detail } => {
                // Strip any trailing `; secondary ...` tool-error suffix so
                // appended diagnostic notes never perturb primary category or
                // extracted relation tags.
                let primary_detail = detail.split("; secondary ").next().unwrap_or(detail).trim();
                // Check `metamorphic_duality:` / `source-inlined` BEFORE
                // compiler-leg substrings so twin O0/O2 or Miri mismatches are
                // never misbucketed as primary `rustc_o0_o2` / `miri_vs_rustc`,
                // and check spine/interleaving BEFORE compiler legs so equal-
                // outcome spine divergences never classify as value mismatches.
                let is_metamorphic = primary_detail.starts_with("metamorphic_duality:")
                    || primary_detail.contains("source-inlined")
                    || primary_detail.contains("metamorphic");
                let mismatch_category = if is_metamorphic {
                    "metamorphic_duality"
                } else if primary_detail.contains("StrictVerbatim failed to conservatively refuse")
                {
                    "strict_probe_accepted_multicall"
                } else if primary_detail.contains("CallerFrameLaw") {
                    "caller_frame_law"
                } else if primary_detail.contains("spine mismatch")
                    || primary_detail.contains("event interleaving mismatch")
                {
                    "spine_mismatch"
                } else if primary_detail.contains("rustc O0 vs O2") {
                    "rustc_o0_o2"
                } else if primary_detail.contains("miri vs rustc-O0") {
                    "miri_vs_rustc"
                } else if primary_detail.contains("UB fault cause mismatch")
                    || primary_detail.contains("UB entry-input boundary digest mismatch")
                    || primary_detail.contains("UB fault missing authenticated entry-input digest")
                {
                    "ub_cause_mismatch"
                } else if primary_detail.contains("detected UB")
                    || primary_detail.contains("expected-UB case accepted by ")
                {
                    "missed_ub"
                } else {
                    "terminal_outcome_mismatch"
                };
                let metamorphic_relations = if is_metamorphic {
                    extract_metamorphic_relations_from_detail(primary_detail)
                } else {
                    Vec::new()
                };
                let spine_relation = if mismatch_category == "spine_mismatch" {
                    extract_spine_relation_from_detail(primary_detail)
                } else {
                    None
                };
                Some(Self {
                    verdict_kind: "unsound_accept",
                    ref_outcome_kind: ref_kind,
                    lean_outcome_kind: lean_kind,
                    mismatch_category,
                    ref_ub_class,
                    lean_ub_class,
                    lean_fault_site_kind,
                    metamorphic_relations,
                    metamorphic_leg_kinds: String::new(),
                    spine_relation,
                })
            }
            TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: true, .. } => Some(Self {
                verdict_kind: "undeclared_ub_fault",
                ref_outcome_kind: ref_kind,
                lean_outcome_kind: lean_kind,
                mismatch_category: "spurious_lean_ub",
                ref_ub_class,
                lean_ub_class,
                lean_fault_site_kind,
                metamorphic_relations: Vec::new(),
                metamorphic_leg_kinds: String::new(),
                spine_relation: None,
            }),
            _ => None,
        }
    }
}

/// Result of deterministic 1-minimal shrinking over a sequence of items.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SequenceShrinkOutcome<T> {
    pub original_len: usize,
    pub minimized: Vec<T>,
    pub predicate_evaluations: usize,
    pub succeeded: bool,
    pub is_one_minimal: bool,
}

impl<T> SequenceShrinkOutcome<T> {
    pub fn reduction_ratio(&self) -> f64 {
        if self.original_len == 0 {
            0.0
        } else {
            1.0 - (self.minimized.len() as f64 / self.original_len as f64)
        }
    }
}

/// Deterministically minimize `initial` using Zeller's `ddmin` algorithm until
/// a 1-minimal fixpoint is reached: removing ANY single element from
/// `minimized` causes `predicate` to return `false`.
pub fn shrink_sequence_1_minimal<T, F>(initial: &[T], mut predicate: F) -> SequenceShrinkOutcome<T>
where
    T: Clone,
    F: FnMut(&[T]) -> bool,
{
    let mut evals = 1usize;
    if !predicate(initial) {
        return SequenceShrinkOutcome {
            original_len: initial.len(),
            minimized: initial.to_vec(),
            predicate_evaluations: evals,
            succeeded: false,
            is_one_minimal: false,
        };
    }

    let mut best = initial.to_vec();
    if best.is_empty() {
        return SequenceShrinkOutcome {
            original_len: 0,
            minimized: best,
            predicate_evaluations: evals,
            succeeded: true,
            is_one_minimal: true,
        };
    }

    // Fast path: check empty sequence first.
    evals += 1;
    if predicate(&[]) {
        best.clear();
        return SequenceShrinkOutcome {
            original_len: initial.len(),
            minimized: best,
            predicate_evaluations: evals,
            succeeded: true,
            is_one_minimal: true,
        };
    }

    let mut n = 2usize;
    while best.len() >= 2 {
        let len = best.len();
        let gran = n.min(len);
        let mut reduced = false;

        // Pass A: try reducing directly to a single partition subset.
        for i in 0..gran {
            let start = (i * len) / gran;
            let end = ((i + 1) * len) / gran;
            if start >= end || (end - start) == len {
                continue;
            }
            let subset = &best[start..end];
            evals += 1;
            if predicate(subset) {
                best = subset.to_vec();
                n = 2;
                reduced = true;
                break;
            }
        }
        if reduced {
            continue;
        }

        // Pass B: try removing each partition complement.
        for i in 0..gran {
            let start = (i * len) / gran;
            let end = ((i + 1) * len) / gran;
            if start >= end {
                continue;
            }
            let mut complement = Vec::with_capacity(len - (end - start));
            complement.extend_from_slice(&best[..start]);
            complement.extend_from_slice(&best[end..]);
            evals += 1;
            if predicate(&complement) {
                best = complement;
                n = (gran - 1).max(2);
                reduced = true;
                break;
            }
        }
        if reduced {
            continue;
        }

        if gran >= len {
            break;
        }
        n = (gran * 2).min(len);
    }

    // Final fixpoint sweep guaranteeing exact 1-minimality.
    loop {
        let mut changed = false;
        let mut idx = 0usize;
        while idx < best.len() {
            let mut cand = Vec::with_capacity(best.len() - 1);
            cand.extend_from_slice(&best[..idx]);
            cand.extend_from_slice(&best[idx + 1..]);
            evals += 1;
            if predicate(&cand) {
                best = cand;
                changed = true;
            } else {
                idx += 1;
            }
        }
        if !changed {
            break;
        }
    }

    SequenceShrinkOutcome {
        original_len: initial.len(),
        minimized: best,
        predicate_evaluations: evals,
        succeeded: true,
        is_one_minimal: true,
    }
}

/// Complete result of shrinking a failing [`FuzzProgram`] across the 6-pass
/// hierarchical loop under [`ShrinkBudget`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgramShrinkResult {
    pub original: FuzzProgram,
    pub minimized: FuzzProgram,
    pub original_steps: usize,
    pub minimized_steps: usize,
    pub predicate_evaluations: usize,
    pub succeeded: bool,
    pub is_one_minimal: bool,
    #[serde(default)]
    pub budget_exhausted: bool,
    #[serde(default)]
    pub converged_1_minimal: bool,
    #[serde(default)]
    pub pass_stats: ShrinkPassStats,
}

/// Deterministically shrink a [`FuzzProgram`] under [`ShrinkBudget::default`].
pub fn shrink_fuzz_program<F>(initial: &FuzzProgram, predicate: F) -> ProgramShrinkResult
where
    F: FnMut(&FuzzProgram) -> bool,
{
    shrink_fuzz_program_with_budget(initial, ShrinkBudget::default(), predicate)
}

/// Deterministically shrink a [`FuzzProgram`] to a combined 6-pass fixed point
/// under `budget`.
pub fn shrink_fuzz_program_with_budget<F>(
    initial: &FuzzProgram,
    budget: ShrinkBudget,
    mut predicate: F,
) -> ProgramShrinkResult
where
    F: FnMut(&FuzzProgram) -> bool,
{
    shrink_fuzz_program_two_tier_with_budget(
        initial,
        budget,
        FastLegStrategy::FullFourWay,
        |_| true,
        |p| predicate(p),
    )
}

/// Two-tier fast-leg-first variant of [`shrink_fuzz_program_with_budget`].
///
/// Every uncached candidate is checked via `fast_leg_check` first; rejections
/// skip `full_eval` immediately. All accepted reductions AND the final
/// fixed point before asserting `is_one_minimal = true` /
/// `converged_1_minimal = true` are confirmed by `full_eval`.
pub fn shrink_fuzz_program_two_tier_with_budget<F1, F2>(
    initial: &FuzzProgram,
    budget: ShrinkBudget,
    strategy: FastLegStrategy,
    mut fast_leg_check: F1,
    mut full_eval: F2,
) -> ProgramShrinkResult
where
    F1: FnMut(&FuzzProgram) -> bool,
    F2: FnMut(&FuzzProgram) -> bool,
{
    let start = Instant::now();
    let mut cache: BTreeMap<String, bool> = BTreeMap::new();
    let eval_count = std::cell::Cell::new(0usize);
    let budget_exhausted = std::cell::Cell::new(false);
    let stats = std::cell::RefCell::new(ShrinkPassStats {
        fast_leg_strategy: strategy,
        ..Default::default()
    });
    let last_full_confirmed_key = std::cell::RefCell::new(String::new());

    let mut eval_cached = |p: &FuzzProgram| -> bool {
        let key = canonical_fuzz_program_key(p);
        if let Some(&cached) = cache.get(&key) {
            return cached;
        }
        let seen = eval_count.get();
        if seen >= budget.max_evals || start.elapsed() >= budget.max_duration {
            budget_exhausted.set(true);
            return false;
        }
        eval_count.set(seen + 1);
        let res = if strategy != FastLegStrategy::FullFourWay && seen > 0 {
            stats.borrow_mut().fast_leg_evaluations += 1;
            if !fast_leg_check(p) {
                stats.borrow_mut().fast_leg_rejections += 1;
                false
            } else {
                stats.borrow_mut().full_oracle_evaluations += 1;
                let ok = full_eval(p);
                if ok {
                    *last_full_confirmed_key.borrow_mut() = key.clone();
                }
                ok
            }
        } else {
            stats.borrow_mut().full_oracle_evaluations += 1;
            let ok = full_eval(p);
            if ok {
                *last_full_confirmed_key.borrow_mut() = key.clone();
            }
            ok
        };
        cache.insert(key, res);
        res
    };

    if budget.max_evals == 0 || start.elapsed() >= budget.max_duration {
        budget_exhausted.set(true);
        return ProgramShrinkResult {
            original: initial.clone(),
            minimized: initial.clone(),
            original_steps: initial.steps.len(),
            minimized_steps: initial.steps.len(),
            predicate_evaluations: eval_count.get(),
            succeeded: false,
            is_one_minimal: false,
            budget_exhausted: true,
            converged_1_minimal: false,
            pass_stats: stats.into_inner(),
        };
    }

    if !eval_cached(initial) {
        return ProgramShrinkResult {
            original: initial.clone(),
            minimized: initial.clone(),
            original_steps: initial.steps.len(),
            minimized_steps: initial.steps.len(),
            predicate_evaluations: eval_count.get(),
            succeeded: false,
            is_one_minimal: false,
            budget_exhausted: budget_exhausted.get(),
            converged_1_minimal: false,
            pass_stats: stats.into_inner(),
        };
    }

    let mut best = initial.clone();

    loop {
        let prev = best.clone();

        // Pass 1 (ScheduleDdmin): disable injected trigger_unwind if not
        // causal.
        for idx in 0..best.steps.len() {
            if budget_exhausted.get() {
                break;
            }
            if let FuzzStep::UnwindProbe { trigger_unwind: true } = best.steps[idx] {
                let mut cand = best.clone();
                cand.steps[idx] = FuzzStep::UnwindProbe { trigger_unwind: false };
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().schedule_ddmin_reductions += 1;
                }
            }
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 2 (StepDdmin): 1-minimal ddmin over FuzzStep sequences
        // (`FuzzStep` operates over explicit pre-initialized locals without
        // heap handles; handle def-use validation applies to `ShrinkableCase`
        // in `shrink_case_two_tier_with_budget`).
        let template = best.clone();
        let before_len = best.steps.len();
        let seq_res = shrink_sequence_1_minimal(&best.steps, |cand_steps| {
            let mut cand = template.clone();
            cand.steps = cand_steps.to_vec();
            eval_cached(&cand)
        });
        best.steps = seq_res.minimized;
        if best.steps.len() < before_len {
            stats.borrow_mut().step_ddmin_reductions += before_len - best.steps.len();
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 3 (CallAndCfgCollapse): collapse calls, branches, loops, and
        // non-causal wrappers into simple ArithImm steps.
        for idx in 0..best.steps.len() {
            if budget_exhausted.get() {
                break;
            }
            let replacements: Vec<FuzzStep> = match best.steps[idx] {
                FuzzStep::HelperCall { bias, .. } => vec![
                    FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 0 },
                    FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: bias },
                ],
                FuzzStep::BranchMix { then_imm, else_imm } => vec![
                    FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: then_imm },
                    FuzzStep::ArithImm { op: FuzzArithOp::Xor, imm: else_imm },
                ],
                FuzzStep::BoundedLoop { iters, step_imm } => {
                    let mut v = Vec::new();
                    if iters > 1 {
                        v.push(FuzzStep::BoundedLoop { iters: 1, step_imm });
                    }
                    v.push(FuzzStep::ArithImm {
                        op: FuzzArithOp::Add,
                        imm: step_imm.wrapping_add(1),
                    });
                    v.push(FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: step_imm });
                    v
                }
                FuzzStep::PaddedRoundTrip { tag_byte } => {
                    vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: u32::from(tag_byte) }]
                }
                FuzzStep::UnwindProbe { trigger_unwind: false } => {
                    vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }]
                }
                FuzzStep::ArithImm { .. } | FuzzStep::UnwindProbe { trigger_unwind: true } => {
                    Vec::new()
                }
            };
            for rep in replacements {
                if budget_exhausted.get() {
                    break;
                }
                let mut cand = best.clone();
                cand.steps[idx] = rep;
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().call_cfg_collapse_reductions += 1;
                    break;
                }
            }
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 4 (TypeAndLayoutNarrow): normalize non-`Add` arithmetic ops
        // (`BitAndMask`, `Sub`, `Xor`, `BitOr`) toward canonical `Add` when the
        // predicate holds so equivalent ops never split fingerprints.
        for idx in 0..best.steps.len() {
            if budget_exhausted.get() {
                break;
            }
            if let FuzzStep::ArithImm { op, imm } = best.steps[idx]
                && op != FuzzArithOp::Add
            {
                let mut cand = best.clone();
                cand.steps[idx] = FuzzStep::ArithImm { op: FuzzArithOp::Add, imm };
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().type_layout_narrow_reductions += 1;
                }
            }
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 5 (StrideAndDifferenceProxyScalarShrink): coupled
        // difference-proxy shrinking over (input_x, input_y) plus
        // stride-aware individual scalars.
        let (nx, ny) = shrink_coupled_pair_with_difference_proxy(
            best.input_x,
            best.input_y,
            None,
            |cx, cy| {
                let mut cand = best.clone();
                cand.input_x = cx;
                cand.input_y = cy;
                eval_cached(&cand)
            },
        );
        if (nx, ny) != (best.input_x, best.input_y) {
            best.input_x = nx;
            best.input_y = ny;
            stats.borrow_mut().stride_diff_proxy_reductions += 1;
        }
        if budget_exhausted.get() {
            break;
        }

        for idx in 0..best.steps.len() {
            if budget_exhausted.get() {
                break;
            }
            let step = best.steps[idx].clone();
            let shrunk = match step {
                FuzzStep::ArithImm { op, imm } => {
                    let s = shrink_u32_non_monotonic(imm, |v| {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::ArithImm { op, imm: v };
                        eval_cached(&cand)
                    });
                    let mut next_op = op;
                    if next_op != FuzzArithOp::Add && !budget_exhausted.get() {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: s };
                        if eval_cached(&cand) {
                            next_op = FuzzArithOp::Add;
                        }
                    }
                    FuzzStep::ArithImm { op: next_op, imm: s }
                }
                FuzzStep::HelperCall { callee_idx, bias } => {
                    let s = shrink_u32_non_monotonic(bias, |v| {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::HelperCall { callee_idx, bias: v };
                        eval_cached(&cand)
                    });
                    FuzzStep::HelperCall { callee_idx, bias: s }
                }
                FuzzStep::BranchMix { then_imm, else_imm } => {
                    let (t, e) = shrink_coupled_pair_with_difference_proxy(
                        then_imm,
                        else_imm,
                        None,
                        |ct, ce| {
                            let mut cand = best.clone();
                            cand.steps[idx] = FuzzStep::BranchMix { then_imm: ct, else_imm: ce };
                            eval_cached(&cand)
                        },
                    );
                    FuzzStep::BranchMix { then_imm: t, else_imm: e }
                }
                FuzzStep::BoundedLoop { iters, step_imm } => {
                    let it = shrink_u32_non_monotonic(iters, |v| {
                        if v == 0 {
                            return false;
                        }
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::BoundedLoop { iters: v, step_imm };
                        eval_cached(&cand)
                    });
                    let st = shrink_u32_non_monotonic(step_imm, |v| {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::BoundedLoop { iters: it, step_imm: v };
                        eval_cached(&cand)
                    });
                    FuzzStep::BoundedLoop { iters: it, step_imm: st }
                }
                FuzzStep::PaddedRoundTrip { tag_byte } => {
                    let tb = shrink_u32_non_monotonic(u32::from(tag_byte), |v| {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::PaddedRoundTrip { tag_byte: v as u8 };
                        eval_cached(&cand)
                    });
                    FuzzStep::PaddedRoundTrip { tag_byte: tb as u8 }
                }
                other => other,
            };
            if shrunk != best.steps[idx] {
                best.steps[idx] = shrunk;
                stats.borrow_mut().stride_diff_proxy_reductions += 1;
            }
        }

        // Pass 6 (CanonicalAlphaRename): FuzzProgram helper indices
        // normalize to canonical order when equivalent (no-op if already
        // canonical).
        let canon = canonicalize_fuzz_program_helpers(&best);
        if canon != best && eval_cached(&canon) {
            best = canon;
            stats.borrow_mut().alpha_rename_applied += 1;
        }

        if budget_exhausted.get() || best == prev {
            break;
        }
    }

    let (hit_budget, final_confirmed, succeeded) = confirm_final_shrink_outcome(
        budget_exhausted.get(),
        last_full_confirmed_key.borrow().as_str(),
        canonical_fuzz_program_key(&best).as_str(),
        &eval_count,
        budget,
        start.elapsed(),
        &stats,
        || full_eval(&best),
    );
    let is_one_minimal = !hit_budget && final_confirmed;

    ProgramShrinkResult {
        original: initial.clone(),
        original_steps: initial.steps.len(),
        minimized_steps: best.steps.len(),
        minimized: best,
        predicate_evaluations: eval_count.get(),
        succeeded,
        is_one_minimal,
        budget_exhausted: hit_budget,
        converged_1_minimal: is_one_minimal,
        pass_stats: stats.into_inner(),
    }
}

#[allow(clippy::too_many_arguments)]
fn confirm_final_shrink_outcome(
    budget_hit: bool,
    last_confirmed_key: &str,
    best_key: &str,
    eval_count: &std::cell::Cell<usize>,
    budget: ShrinkBudget,
    elapsed: std::time::Duration,
    stats: &std::cell::RefCell<ShrinkPassStats>,
    full_eval: impl FnOnce() -> bool,
) -> (bool, bool, bool) {
    if budget_hit {
        return (true, false, true);
    }
    if last_confirmed_key == best_key {
        stats.borrow_mut().final_full_confirmations += 1;
        return (false, true, true);
    }
    if eval_count.get() >= budget.max_evals || elapsed >= budget.max_duration {
        return (true, false, true);
    }
    eval_count.set(eval_count.get() + 1);
    stats.borrow_mut().full_oracle_evaluations += 1;
    stats.borrow_mut().final_full_confirmations += 1;
    let final_confirmed = full_eval();
    (false, final_confirmed, final_confirmed)
}

fn canonicalize_fuzz_program_helpers(prog: &FuzzProgram) -> FuzzProgram {
    let mut out = prog.clone();
    for step in &mut out.steps {
        if let FuzzStep::HelperCall { callee_idx, .. } = step {
            *callee_idx %= 3;
        }
    }
    out
}

/// Enumerate strictly smaller `u32` candidates (`cand < v`) sorted in ascending
/// magnitude without assuming threshold monotonicity: includes `0..=12`, powers
/// of two and `(1 << k) - 1`, dyadic/midpoint fractions, alignment-preserving
/// stride candidates `align * (v / (2 * align))`, decimal quotients, byte
/// masks/shifts, single-bit clears, and immediate predecessors toward `0`.
pub fn smaller_u32_candidates(v: u32) -> Vec<u32> {
    smaller_u32_stride_candidates(v, None)
}

/// Alignment-preserving stride-aware `u32` candidate generator (`Plausible`).
///
/// Includes `align * (v / (2 * align))` and `v - align` for an explicit `align`
/// (and automatically for common power-of-2 alignments `2..=64` dividing `v`),
/// so aligned offsets like `24` (`align=8`) or `48` (`align=12`) shrink cleanly
/// without stalling on unaligned midpoints (`12` or `24`).
pub fn smaller_u32_stride_candidates(v: u32, align: Option<u32>) -> Vec<u32> {
    if v == 0 {
        return Vec::new();
    }
    let mut cands = Vec::with_capacity(64);
    for small in 0..=12u32 {
        if small < v {
            cands.push(small);
        }
    }
    for k in 0..32u32 {
        let pow = 1u32 << k;
        if pow < v {
            cands.push(pow);
        }
        let mask = pow.saturating_sub(1);
        if mask < v {
            cands.push(mask);
        }
        if (v & pow) != 0 {
            cands.push(v & !pow);
        }
    }
    for num in 1..=7u64 {
        let frac = ((u64::from(v) * num) / 8) as u32;
        if frac < v {
            cands.push(frac);
        }
    }
    for dec in [v / 100, v / 10] {
        if dec < v {
            cands.push(dec);
        }
    }
    for masked in [v & 0xFF, v & 0xFFFF, v & 0x00FF_FFFF, v >> 8, v >> 16, v >> 24] {
        if masked < v {
            cands.push(masked);
        }
    }
    for delta in [8u32, 4, 2, 1] {
        let sub = v.saturating_sub(delta);
        if sub < v {
            cands.push(sub);
        }
    }
    let mut strides = [2u32, 4, 8, 16, 32, 64].to_vec();
    if let Some(a) = align
        && a > 1
        && !strides.contains(&a)
    {
        strides.push(a);
    }
    for a in strides {
        if v.is_multiple_of(a) {
            let half_stride = a.saturating_mul(v / a.saturating_mul(2).max(1));
            if half_stride < v {
                cands.push(half_stride);
            }
            let one_step = v.saturating_sub(a);
            if one_step < v {
                cands.push(one_step);
            }
            if a < v {
                cands.push(a);
            }
            if let Some(two_a) = a.checked_mul(2)
                && two_a < v
            {
                cands.push(two_a);
            }
        }
    }
    cands.retain(|&c| c < v);
    cands.sort_unstable();
    cands.dedup();
    cands
}

/// Narrow an unsigned `u32` scalar to a fixed point over
/// [`smaller_u32_candidates`].
pub fn shrink_u32_non_monotonic(initial: u32, mut pred: impl FnMut(u32) -> bool) -> u32 {
    let mut cur = initial;
    while cur > 0 {
        let mut reduced = None;
        for cand in smaller_u32_candidates(cur) {
            if pred(cand) {
                reduced = Some(cand);
                break;
            }
        }
        match reduced {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// Narrow an unsigned `u32` scalar with an explicit alignment stride hint.
pub fn shrink_u32_stride_non_monotonic(
    initial: u32,
    align: Option<u32>,
    mut pred: impl FnMut(u32) -> bool,
) -> u32 {
    let mut cur = initial;
    while cur > 0 {
        let mut reduced = None;
        for cand in smaller_u32_stride_candidates(cur, align) {
            if pred(cand) {
                reduced = Some(cand);
                break;
            }
        }
        match reduced {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// Coupled-pair difference-proxy shrinker (`Plausible`):
/// 1. Holds `delta = |a - b|` constant and shrinks the smaller coordinate with
///    alignment strides (jointly reducing `(a, b)` -> `(a - d, b - d)`),
/// 2. Holds the smaller coordinate fixed and shrinks `delta` (e.g. `(20, 10)`
///    -> `(11, 10)`), and
/// 3. Shrinks `a` and `b` individually to a combined fixed point.
pub fn shrink_coupled_pair_with_difference_proxy(
    init_a: u32,
    init_b: u32,
    align_hint: Option<u32>,
    mut pred: impl FnMut(u32, u32) -> bool,
) -> (u32, u32) {
    let mut a = init_a;
    let mut b = init_b;

    loop {
        let prev = (a, b);
        let delta = a.abs_diff(b);
        let a_larger = a > b;
        let small = a.min(b);

        // Phase A: hold difference `delta` fixed while shrinking `small`
        // (including `delta == 0`, e.g. `a == b && a >= 8`).
        if small > 0 {
            for cs in smaller_u32_stride_candidates(small, align_hint) {
                let Some(large) = cs.checked_add(delta) else {
                    continue;
                };
                let (ca, cb) = if a_larger { (large, cs) } else { (cs, large) };
                if pred(ca, cb) {
                    a = ca;
                    b = cb;
                    break;
                }
            }
        }

        // Phase B: hold smaller coordinate fixed while shrinking difference.
        let cur_small = a.min(b);
        let cur_delta = a.abs_diff(b);
        let cur_a_larger = a > b;
        if cur_delta > 0 {
            for cd in smaller_u32_stride_candidates(cur_delta, align_hint) {
                let Some(large) = cur_small.checked_add(cd) else {
                    continue;
                };
                let (ca, cb) = if cur_a_larger { (large, cur_small) } else { (cur_small, large) };
                if pred(ca, cb) {
                    a = ca;
                    b = cb;
                    break;
                }
            }
        }

        // Phase C: shrink each coordinate individually with stride support.
        a = shrink_u32_stride_non_monotonic(a, align_hint, |ca| pred(ca, b));
        b = shrink_u32_stride_non_monotonic(b, align_hint, |cb| pred(a, cb));

        if (a, b) == prev {
            break;
        }
    }

    (a, b)
}

/// Alignment-aware strictly smaller `u64` candidates (`cand < v`).
pub fn smaller_u64_stride_candidates(v: u64, align: Option<u64>) -> Vec<u64> {
    if v == 0 {
        return Vec::new();
    }
    let mut cands = Vec::with_capacity(80);
    for small in 0..=12u64 {
        if small < v {
            cands.push(small);
        }
    }
    for k in 0..64u32 {
        let pow = 1u64 << k;
        if pow < v {
            cands.push(pow);
        }
        let mask = pow.saturating_sub(1);
        if mask < v {
            cands.push(mask);
        }
        if (v & pow) != 0 {
            cands.push(v & !pow);
        }
    }
    for num in 1..=7u128 {
        let frac = ((u128::from(v) * num) / 8) as u64;
        if frac < v {
            cands.push(frac);
        }
    }
    for delta in [8u64, 4, 2, 1] {
        let sub = v.saturating_sub(delta);
        if sub < v {
            cands.push(sub);
        }
    }
    let mut strides = vec![2u64, 4, 8, 16, 32, 64];
    if let Some(a) = align
        && a > 1
        && !strides.contains(&a)
    {
        strides.push(a);
    }
    for a in strides {
        if v.is_multiple_of(a) {
            let half = a.saturating_mul(v / a.saturating_mul(2).max(1));
            if half < v {
                cands.push(half);
            }
            let one_step = v.saturating_sub(a);
            if one_step < v {
                cands.push(one_step);
            }
            if a < v {
                cands.push(a);
            }
        }
    }
    cands.retain(|&c| c < v);
    cands.sort_unstable();
    cands.dedup();
    cands
}

/// Alignment-aware strictly smaller `u128` candidates (`cand < v`).
pub fn smaller_u128_stride_candidates(v: u128, align: Option<u128>) -> Vec<u128> {
    if v == 0 {
        return Vec::new();
    }
    let mut cands = Vec::with_capacity(96);
    for small in 0..=12u128 {
        if small < v {
            cands.push(small);
        }
    }
    for k in 0..128u32 {
        let pow = 1u128 << k;
        if pow < v {
            cands.push(pow);
        }
        let mask = pow.saturating_sub(1);
        if mask < v {
            cands.push(mask);
        }
        if (v & pow) != 0 {
            cands.push(v & !pow);
        }
    }
    for num in 1..=7u128 {
        let frac = (v / 8).saturating_mul(num);
        if frac < v {
            cands.push(frac);
        }
    }
    for delta in [8u128, 4, 2, 1] {
        let sub = v.saturating_sub(delta);
        if sub < v {
            cands.push(sub);
        }
    }
    if let Some(a) = align
        && a > 1
        && v.is_multiple_of(a)
    {
        let half = a.saturating_mul(v / a.saturating_mul(2).max(1));
        if half < v {
            cands.push(half);
        }
        let one_step = v.saturating_sub(a);
        if one_step < v {
            cands.push(one_step);
        }
        if a < v {
            cands.push(a);
        }
    }
    cands.retain(|&c| c < v);
    cands.sort_unstable();
    cands.dedup();
    cands
}

pub fn shrink_u128_stride_non_monotonic(
    initial: u128,
    align: Option<u128>,
    mut pred: impl FnMut(u128) -> bool,
) -> u128 {
    let mut cur = initial;
    while cur > 0 {
        let mut reduced = None;
        for cand in smaller_u128_stride_candidates(cur, align) {
            if pred(cand) {
                reduced = Some(cand);
                break;
            }
        }
        match reduced {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// Enumerate signed `i32` candidates strictly simpler than `v` under the
/// well-founded order `(|a|, a < 0) < (|v|, v < 0)`.
pub fn smaller_i32_candidates(v: i32) -> Vec<i32> {
    if v == 0 {
        return Vec::new();
    }
    let v_key = (v.unsigned_abs(), v < 0);
    let mut cands = vec![0, 1, -1];
    if let Some(pos) = v.checked_abs() {
        cands.push(pos);
    }
    cands.push(if v > 0 { v - 1 } else { v + 1 });
    for u in smaller_u32_candidates(v.unsigned_abs()) {
        if let Ok(pos) = i32::try_from(u) {
            cands.push(pos);
            if let Some(neg) = pos.checked_neg() {
                cands.push(neg);
            }
        }
    }
    cands.retain(|&c| (c.unsigned_abs(), c < 0) < v_key);
    cands.sort_by_key(|&c| (c.unsigned_abs(), c < 0));
    cands.dedup();
    cands
}

/// Narrow a signed `i32` scalar to a fixed point over
/// [`smaller_i32_candidates`] without assuming threshold monotonicity.
pub fn shrink_i32_non_monotonic(initial: i32, mut pred: impl FnMut(i32) -> bool) -> i32 {
    let mut cur = initial;
    while cur != 0 {
        let mut reduced = None;
        for cand in smaller_i32_candidates(cur) {
            if pred(cand) {
                reduced = Some(cand);
                break;
            }
        }
        match reduced {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// Pass 1 (`ScheduleDdmin`): minimize `EnvSchedule` via `ddmin` over `global`
/// and `per_callee` entries, zero-fill `ReturnBytes`, and shorten `Unwind` /
/// `Abort` tags toward `"u"` / `"a"`.
pub fn shrink_env_schedule<F>(initial: &EnvSchedule, mut pred: F) -> EnvSchedule
where
    F: FnMut(&EnvSchedule) -> bool,
{
    if initial.is_empty() || !pred(initial) {
        return initial.clone();
    }
    let empty = EnvSchedule::default();
    if pred(&empty) {
        return empty;
    }

    let mut cur = initial.clone();

    if !cur.global.is_empty() {
        let base = cur.clone();
        let global_vec: Vec<EnvAction> = cur.global.iter().cloned().collect();
        let res = shrink_sequence_1_minimal(&global_vec, |cand_global| {
            let mut next = base.clone();
            next.global = cand_global.iter().cloned().collect();
            pred(&next)
        });
        cur.global = res.minimized.into_iter().collect();
    }

    let pairs: Vec<(String, Vec<EnvAction>)> =
        cur.per_callee.iter().map(|(k, v)| (k.clone(), v.iter().cloned().collect())).collect();
    if !pairs.is_empty() {
        let base = cur.clone();
        let kept = shrink_sequence_1_minimal(&pairs, |cand_pairs| {
            let mut next = base.clone();
            next.per_callee =
                cand_pairs.iter().map(|(k, v)| (k.clone(), v.iter().cloned().collect())).collect();
            pred(&next)
        });
        cur.per_callee =
            kept.minimized.into_iter().map(|(k, v)| (k, v.into_iter().collect())).collect();
    }

    let keys: Vec<String> = cur.per_callee.keys().cloned().collect();
    for k in keys {
        if let Some(actions) = cur.per_callee.get(&k) {
            let actions_vec: Vec<EnvAction> = actions.iter().cloned().collect();
            let base = cur.clone();
            let res = shrink_sequence_1_minimal(&actions_vec, |cand_acts| {
                let mut next = base.clone();
                if cand_acts.is_empty() {
                    next.per_callee.remove(&k);
                } else {
                    next.per_callee.insert(k.clone(), cand_acts.iter().cloned().collect());
                }
                pred(&next)
            });
            if res.minimized.is_empty() {
                cur.per_callee.remove(&k);
            } else {
                cur.per_callee.insert(k, res.minimized.into_iter().collect());
            }
        }
    }

    let shrink_action = |act: &mut EnvAction, apply: &mut dyn FnMut(&EnvAction) -> bool| match act {
        EnvAction::ReturnBytes(bytes) => {
            if !bytes.is_empty() && bytes.iter().any(|&b| b != 0) {
                let zeros = EnvAction::ReturnBytes(vec![0u8; bytes.len()]);
                if apply(&zeros) {
                    *bytes = vec![0u8; bytes.len()];
                }
            }
            for idx in 0..bytes.len() {
                let orig_b = bytes[idx];
                if orig_b == 0 {
                    continue;
                }
                let shrunk_b = shrink_u32_non_monotonic(u32::from(orig_b), |cand_v| {
                    let mut nb = bytes.clone();
                    nb[idx] = cand_v as u8;
                    apply(&EnvAction::ReturnBytes(nb))
                }) as u8;
                bytes[idx] = shrunk_b;
            }
        }
        EnvAction::Unwind { message } => {
            if message != "u" {
                let short = EnvAction::Unwind { message: "u".to_string() };
                if apply(&short) {
                    *message = "u".to_string();
                }
            }
        }
        EnvAction::Abort { reason } => {
            if reason != "a" {
                let short = EnvAction::Abort { reason: "a".to_string() };
                if apply(&short) {
                    *reason = "a".to_string();
                }
            }
        }
    };

    for idx in 0..cur.global.len() {
        let mut act = cur.global[idx].clone();
        let snapshot = cur.clone();
        shrink_action(&mut act, &mut |cand_act| {
            let mut next = snapshot.clone();
            next.global[idx] = cand_act.clone();
            pred(&next)
        });
        cur.global[idx] = act;
    }

    let callee_keys: Vec<String> = cur.per_callee.keys().cloned().collect();
    for k in callee_keys {
        let len = cur.per_callee.get(&k).map(std::collections::VecDeque::len).unwrap_or(0);
        for idx in 0..len {
            let Some(mut act) = cur.per_callee.get(&k).and_then(|v| v.get(idx)).cloned() else {
                continue;
            };
            let snapshot = cur.clone();
            shrink_action(&mut act, &mut |cand_act| {
                let mut next = snapshot.clone();
                if let Some(vec_ref) = next.per_callee.get_mut(&k) {
                    vec_ref[idx] = cand_act.clone();
                }
                pred(&next)
            });
            if let Some(vec_ref) = cur.per_callee.get_mut(&k) {
                vec_ref[idx] = act;
            }
        }
    }

    cur
}

/// Producer-consumer handle identifier for Wave-2 MIR shrinking (`PropEr`
/// static def-use filter).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HandleId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HandleType {
    Alloc,
    Borrow { mutable: bool },
    Slice,
}

/// Typed input slot in a [`ShrinkableCase`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkInput {
    pub local_id: usize,
    pub width: IntKind,
    pub value: u128,
    #[serde(default)]
    pub align_hint: Option<u32>,
}

/// Pure helper computation modeled by a [`ShrinkHelper`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShrinkHelperOp {
    /// `a.wrapping_mul(multiplier).wrapping_add(b).wrapping_add(addend)`.
    #[default]
    AffineMulAdd,
    /// `(a ^ b).wrapping_add(addend)` (`fuzz_helper_1` parity).
    BitXorAdd,
    /// `if a >= b { a.wrapping_sub(b).wrapping_add(multiplier) } else { b.wrapping_sub(a).wrapping_add(addend) }` (`fuzz_helper_2` parity).
    AbsDiffBranch,
}

/// Loop-counter induction step updated on every iteration of a
/// [`ShrinkStep::BoundedLoop`] (`acc += k * step_mul + addend` for
/// `k = 0..iters`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedLoopInduction {
    pub dst_local: usize,
    pub step_mul: u64,
    pub addend: u64,
}

/// Helper function descriptor inside a [`ShrinkableCase`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkHelper {
    pub helper_id: usize,
    pub multiplier: u64,
    pub addend: u64,
    #[serde(default)]
    pub op: ShrinkHelperOp,
}

/// Hierarchical structured step supporting all 6 shrink passes (schedules,
/// producer-consumer handles, nested CFG/call/loop/decoy blocks, layout
/// narrowing, coupled `(offset, len)` + `align` strides, and alpha-renaming).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ShrinkStep {
    Alloc {
        handle: HandleId,
        size: u32,
        align: u32,
        local_id: usize,
    },
    Borrow {
        dst: HandleId,
        src: HandleId,
        mutable: bool,
        local_id: usize,
    },
    SplitAt {
        left: HandleId,
        right: HandleId,
        src: HandleId,
        mid: u32,
        len: u32,
        align: u32,
    },
    UseHandle {
        handle: HandleId,
        offset: u32,
        len: u32,
        align: u32,
        local_id: usize,
    },
    ArithImm {
        dst_local: usize,
        op: FuzzArithOp,
        imm: u64,
    },
    HelperCall {
        dst_local: usize,
        helper_id: usize,
        block_id: usize,
        bias: u64,
        #[serde(default)]
        rhs_local: Option<usize>,
    },
    BranchMix {
        block_id: usize,
        cond_local: usize,
        taken_then: bool,
        #[serde(default)]
        dynamic_even_cond: bool,
        then_steps: Vec<ShrinkStep>,
        else_steps: Vec<ShrinkStep>,
    },
    BoundedLoop {
        block_id: usize,
        iters: u32,
        #[serde(default)]
        induction: Option<BoundedLoopInduction>,
        body: Vec<ShrinkStep>,
    },
    IfFalseDecoy {
        block_id: usize,
        body: Vec<ShrinkStep>,
    },
    DropGuardWrapper {
        local_id: usize,
        body: Vec<ShrinkStep>,
    },
    PaddedRoundTrip {
        local_id: usize,
        tag_byte: u8,
    },
    UnwindProbe {
        callee: String,
        #[serde(default)]
        dst_local: usize,
        trigger_unwind: bool,
        block_id: usize,
    },
    PairOffsetLen {
        offset: u32,
        len: u32,
        align: u32,
        local_id: usize,
    },
    /// Bit-xor sentinel update (`dst_local ^= (rhs_local ^ xor_imm)`).
    XorLocalImm {
        dst_local: usize,
        rhs_local: usize,
        xor_imm: u64,
    },
}

/// Complete hierarchical shrinkable program IR supporting Wave-1 and Wave-2
/// reduction passes, standalone Rust emission, and `.mir.lean` bundle emission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkableCase {
    pub name: String,
    pub scalar_width: IntKind,
    pub inputs: Vec<ShrinkInput>,
    #[serde(default)]
    pub struct_fields: Vec<IntKind>,
    #[serde(default)]
    pub slice_len: Option<usize>,
    #[serde(default = "default_one")]
    pub slice_align: usize,
    #[serde(default)]
    pub helpers: Vec<ShrinkHelper>,
    pub steps: Vec<ShrinkStep>,
    #[serde(default)]
    pub env_schedule: EnvSchedule,
    pub return_local: usize,
}

fn default_one() -> usize {
    1
}

/// Maximum iteration bound permitted on a single [`ShrinkStep::BoundedLoop`]
/// so standalone Rust reproducers cannot spin for billions of iterations while
/// Lean `.mir.lean` bundles execute under fixed `SHRINKABLE_REPRO_FUEL`.
pub const MAX_SHRINKABLE_BOUNDED_LOOP_ITERS: u32 = 64;

/// Fixed execution step fuel emitted into standalone `ShrinkableCase`
/// `.mir.lean` witness bundles (`def reproFuel : Nat := 1024`).
pub const SHRINKABLE_REPRO_FUEL: usize = 1024;

fn estimate_shrinkable_steps_mir_cost(steps: &[ShrinkStep]) -> Option<usize> {
    let mut total = 0usize;
    for step in steps {
        let step_cost = match step {
            ShrinkStep::ArithImm { .. }
            | ShrinkStep::XorLocalImm { .. }
            | ShrinkStep::PairOffsetLen { .. } => 4usize,
            ShrinkStep::Alloc { .. }
            | ShrinkStep::Borrow { .. }
            | ShrinkStep::SplitAt { .. }
            | ShrinkStep::UseHandle { .. } => 6usize,
            ShrinkStep::PaddedRoundTrip { .. } => 10usize,
            ShrinkStep::HelperCall { .. } | ShrinkStep::UnwindProbe { .. } => 14usize,
            ShrinkStep::BranchMix {
                dynamic_even_cond, taken_then, then_steps, else_steps, ..
            } => {
                let arm_cost = if *dynamic_even_cond {
                    estimate_shrinkable_steps_mir_cost(then_steps)?
                        .max(estimate_shrinkable_steps_mir_cost(else_steps)?)
                } else if *taken_then {
                    estimate_shrinkable_steps_mir_cost(then_steps)?
                } else {
                    estimate_shrinkable_steps_mir_cost(else_steps)?
                };
                4usize.checked_add(arm_cost)?
            }
            ShrinkStep::IfFalseDecoy { .. } => 3usize,
            ShrinkStep::DropGuardWrapper { body, .. } => {
                2usize.checked_add(estimate_shrinkable_steps_mir_cost(body)?)?
            }
            ShrinkStep::BoundedLoop { iters, induction, body, .. } => {
                let body_cost = estimate_shrinkable_steps_mir_cost(body)?;
                let iter_overhead = if induction.is_some() { 8usize } else { 4usize };
                let per_iter = iter_overhead.checked_add(body_cost)?;
                let loop_cost = (*iters as usize).checked_mul(per_iter)?;
                4usize.checked_add(loop_cost)?
            }
        };
        total = total.checked_add(step_cost)?;
        if total > SHRINKABLE_REPRO_FUEL {
            return None;
        }
    }
    Some(total)
}

/// Maximum allocation byte size permitted on a single [`ShrinkStep::Alloc`].
pub const MAX_SHRINKABLE_ALLOC_BYTES: u32 = 1 << 20;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct HandleDefInfo {
    kind: HandleType,
    len: u32,
    align: usize,
}

/// $O(n)$ static `PropEr`-style handle def-use, extent/alignment, and step
/// budget validity filter (`< 1 µs`), rejecting candidate subsets with unbound
/// consumer handles, colliding output handles, out-of-bounds or misaligned
/// slice/handle operations, invalid alignments, missing/duplicate helper IDs,
/// or loop bounds exceeding the Lean replay fuel budget before spawning any
/// execution authority.
pub fn all_handles_defined_and_typed(steps: &[ShrinkStep], helpers: &[ShrinkHelper]) -> bool {
    let mut helper_ids = BTreeSet::new();
    for h in helpers {
        if !helper_ids.insert(h.helper_id) {
            return false;
        }
    }
    let mut must_env: BTreeMap<HandleId, HandleDefInfo> = BTreeMap::new();
    let mut may_env: BTreeSet<HandleId> = BTreeSet::new();
    if !check_steps_def_use(steps, &helper_ids, &mut must_env, &mut may_env) {
        return false;
    }
    estimate_shrinkable_steps_mir_cost(steps)
        .and_then(|c| c.checked_add(32))
        .is_some_and(|total| total <= SHRINKABLE_REPRO_FUEL)
}

fn check_steps_def_use(
    steps: &[ShrinkStep],
    helper_ids: &BTreeSet<usize>,
    must_env: &mut BTreeMap<HandleId, HandleDefInfo>,
    may_env: &mut BTreeSet<HandleId>,
) -> bool {
    for step in steps {
        match step {
            ShrinkStep::Alloc { handle, size, align, .. } => {
                if *align == 0
                    || !align.is_power_of_two()
                    || *size > MAX_SHRINKABLE_ALLOC_BYTES
                    || may_env.contains(handle)
                {
                    return false;
                }
                must_env.insert(
                    *handle,
                    HandleDefInfo { kind: HandleType::Alloc, len: *size, align: *align as usize },
                );
                may_env.insert(*handle);
            }
            ShrinkStep::Borrow { dst, src, mutable, .. } => {
                let Some(src_info) = must_env.get(src).copied() else {
                    return false;
                };
                if may_env.contains(dst) {
                    return false;
                }
                must_env.insert(
                    *dst,
                    HandleDefInfo {
                        kind: HandleType::Borrow { mutable: *mutable },
                        len: src_info.len,
                        align: src_info.align,
                    },
                );
                may_env.insert(*dst);
            }
            ShrinkStep::SplitAt { left, right, src, mid, len, align } => {
                if *align == 0 || !align.is_power_of_two() || left == right {
                    return false;
                }
                let Some(src_info) = must_env.get(src).copied() else {
                    return false;
                };
                let eff_align = *align as usize;
                if *len > src_info.len
                    || *mid > *len
                    || eff_align > src_info.align
                    || !(*mid as usize).is_multiple_of(eff_align)
                    || may_env.contains(left)
                    || may_env.contains(right)
                {
                    return false;
                }
                // Consume `src` into two distinct slice handles.
                must_env.remove(src);
                may_env.remove(src);
                must_env.insert(
                    *left,
                    HandleDefInfo { kind: HandleType::Slice, len: *mid, align: eff_align },
                );
                must_env.insert(
                    *right,
                    HandleDefInfo { kind: HandleType::Slice, len: *len - *mid, align: eff_align },
                );
                may_env.insert(*left);
                may_env.insert(*right);
            }
            ShrinkStep::UseHandle { handle, offset, len, align, .. } => {
                if *align == 0 || !align.is_power_of_two() {
                    return false;
                }
                let Some(info) = must_env.get(handle).copied() else {
                    return false;
                };
                let eff_align = *align as usize;
                if offset.checked_add(*len).is_none_or(|end| end > info.len)
                    || eff_align > info.align
                    || !(*offset as usize).is_multiple_of(eff_align)
                {
                    return false;
                }
            }
            ShrinkStep::HelperCall { helper_id, .. } => {
                if !helper_ids.contains(helper_id) {
                    return false;
                }
            }
            ShrinkStep::BranchMix {
                taken_then, dynamic_even_cond, then_steps, else_steps, ..
            } => {
                let mut then_must = must_env.clone();
                let mut then_may = may_env.clone();
                let mut else_must = must_env.clone();
                let mut else_may = may_env.clone();
                if !check_steps_def_use(then_steps, helper_ids, &mut then_must, &mut then_may)
                    || !check_steps_def_use(else_steps, helper_ids, &mut else_must, &mut else_may)
                {
                    return false;
                }
                if *dynamic_even_cond {
                    then_must.retain(|k, tv| {
                        if let Some(ev) = else_must.get(k)
                            && tv.kind == ev.kind
                        {
                            tv.len = tv.len.min(ev.len);
                            tv.align = tv.align.min(ev.align);
                            true
                        } else {
                            false
                        }
                    });
                    then_may.extend(else_may);
                    *must_env = then_must;
                    *may_env = then_may;
                } else {
                    // Static manual branches execute strictly the selected arm
                    // (`*taken_then`), so propagate that arm's def-use state
                    // while keeping both arms structurally valid.
                    if *taken_then {
                        *must_env = then_must;
                        *may_env = then_may;
                    } else {
                        *must_env = else_must;
                        *may_env = else_may;
                    }
                }
            }
            ShrinkStep::BoundedLoop { iters, body, .. } => {
                if *iters == 0 || *iters > MAX_SHRINKABLE_BOUNDED_LOOP_ITERS {
                    return false;
                }
                let mut cur_must = must_env.clone();
                let mut cur_may = may_env.clone();
                let mut visited: Vec<(BTreeMap<HandleId, HandleDefInfo>, BTreeSet<HandleId>)> =
                    Vec::new();
                let mut iter_idx = 0u32;
                while iter_idx < *iters {
                    let prev_must = cur_must.clone();
                    let prev_may = cur_may.clone();
                    if !check_steps_def_use(body, helper_ids, &mut cur_must, &mut cur_may) {
                        return false;
                    }
                    iter_idx += 1;
                    if cur_must == prev_must && cur_may == prev_may {
                        break;
                    }
                    if let Some(cycle_start) =
                        visited.iter().position(|(m, y)| m == &cur_must && y == &cur_may)
                    {
                        let cycle_len = visited.len() - cycle_start;
                        let rem = ((*iters - iter_idx) as usize) % cycle_len;
                        let (fin_must, fin_may) = visited[cycle_start + rem].clone();
                        cur_must = fin_must;
                        cur_may = fin_may;
                        break;
                    }
                    visited.push((cur_must.clone(), cur_may.clone()));
                }
                *must_env = cur_must;
                *may_env = cur_may;
            }
            ShrinkStep::IfFalseDecoy { body, .. } => {
                let mut decoy_must = must_env.clone();
                let mut decoy_may = may_env.clone();
                if !check_steps_def_use(body, helper_ids, &mut decoy_must, &mut decoy_may) {
                    return false;
                }
            }
            ShrinkStep::DropGuardWrapper { body, .. } => {
                if !check_steps_def_use(body, helper_ids, must_env, may_env) {
                    return false;
                }
            }
            ShrinkStep::PairOffsetLen { offset, len, align, .. } => {
                if *align == 0 || !align.is_power_of_two() {
                    return false;
                }
                let eff_align = *align as usize;
                let total_bytes = (*offset as usize).checked_add((*len).max(1) as usize);
                if !(*offset as usize).is_multiple_of(eff_align)
                    || total_bytes.is_none_or(|tot| tot > MAX_SHRINKABLE_ALLOC_BYTES as usize)
                {
                    return false;
                }
            }
            ShrinkStep::ArithImm { .. }
            | ShrinkStep::PaddedRoundTrip { .. }
            | ShrinkStep::UnwindProbe { .. }
            | ShrinkStep::XorLocalImm { .. } => {}
        }
    }
    true
}

fn resolve_effective_fuzz_schedule(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
) -> EnvSchedule {
    match schedule {
        Some(sched) => sched.clone(),
        None => {
            let mut sched = EnvSchedule::default();
            if prog.has_triggering_unwind() {
                sched.push_callee(
                    "fuzz_ext_unwind",
                    EnvAction::Unwind { message: "fuzz injected unwind".to_string() },
                );
            }
            sched
        }
    }
}

impl ShrinkableCase {
    /// Convert a [`FuzzProgram`] (plus optional [`EnvSchedule`]) into a
    /// [`ShrinkableCase`] preserving exact helper and step structure.
    pub fn from_fuzz_program(prog: &FuzzProgram, schedule: Option<&EnvSchedule>) -> Self {
        let sched = resolve_effective_fuzz_schedule(prog, schedule);
        let helpers = vec![
            ShrinkHelper {
                helper_id: 0,
                multiplier: 3,
                addend: 0,
                op: ShrinkHelperOp::AffineMulAdd,
            },
            ShrinkHelper { helper_id: 1, multiplier: 1, addend: 17, op: ShrinkHelperOp::BitXorAdd },
            ShrinkHelper {
                helper_id: 2,
                multiplier: 5,
                addend: 9,
                op: ShrinkHelperOp::AbsDiffBranch,
            },
        ];
        let mut steps = Vec::with_capacity(prog.steps.len() + 1);
        let mut next_bb = 1usize;
        for step in &prog.steps {
            match step {
                FuzzStep::ArithImm { op, imm } => {
                    steps.push(ShrinkStep::ArithImm {
                        dst_local: 3,
                        op: *op,
                        imm: u64::from(*imm),
                    });
                }
                FuzzStep::HelperCall { callee_idx, bias } => {
                    steps.push(ShrinkStep::HelperCall {
                        dst_local: 3,
                        helper_id: callee_idx % 3,
                        block_id: next_bb,
                        bias: u64::from(*bias),
                        rhs_local: Some(2),
                    });
                    next_bb += 1;
                }
                FuzzStep::BranchMix { then_imm, else_imm } => {
                    steps.push(ShrinkStep::BranchMix {
                        block_id: next_bb,
                        cond_local: 3,
                        taken_then: false,
                        dynamic_even_cond: true,
                        then_steps: vec![ShrinkStep::ArithImm {
                            dst_local: 3,
                            op: FuzzArithOp::Add,
                            imm: u64::from(*then_imm),
                        }],
                        else_steps: vec![ShrinkStep::ArithImm {
                            dst_local: 3,
                            op: FuzzArithOp::Xor,
                            imm: u64::from(*else_imm),
                        }],
                    });
                    next_bb += 3;
                }
                FuzzStep::BoundedLoop { iters, step_imm } => {
                    steps.push(ShrinkStep::BoundedLoop {
                        block_id: next_bb,
                        iters: *iters,
                        induction: Some(BoundedLoopInduction {
                            dst_local: 3,
                            step_mul: u64::from(*step_imm),
                            addend: 1,
                        }),
                        body: Vec::new(),
                    });
                    next_bb += 3;
                }
                FuzzStep::PaddedRoundTrip { tag_byte } => {
                    steps.push(ShrinkStep::PaddedRoundTrip { local_id: 3, tag_byte: *tag_byte });
                }
                FuzzStep::UnwindProbe { trigger_unwind } => {
                    steps.push(ShrinkStep::UnwindProbe {
                        callee: if *trigger_unwind {
                            "fuzz_ext_unwind".to_string()
                        } else {
                            "fuzz_ext_probe".to_string()
                        },
                        dst_local: 3,
                        trigger_unwind: *trigger_unwind,
                        block_id: next_bb,
                    });
                    next_bb += 3;
                }
            }
        }
        steps.push(ShrinkStep::XorLocalImm { dst_local: 3, rhs_local: 1, xor_imm: 0xA5A5 });
        Self {
            name: format!("fuzz_s{}_i{:03}", prog.seed, prog.index),
            scalar_width: IntKind::U32,
            inputs: vec![
                ShrinkInput {
                    local_id: 1,
                    width: IntKind::U32,
                    value: u128::from(prog.input_x),
                    align_hint: None,
                },
                ShrinkInput {
                    local_id: 2,
                    width: IntKind::U32,
                    value: u128::from(prog.input_y),
                    align_hint: None,
                },
                ShrinkInput {
                    local_id: 3,
                    width: IntKind::U32,
                    value: u128::from(prog.input_x.wrapping_add(prog.input_y)),
                    align_hint: None,
                },
            ],
            struct_fields: vec![IntKind::U8, IntKind::U32],
            slice_len: None,
            slice_align: 1,
            helpers,
            steps,
            env_schedule: sched,
            return_local: 3,
        }
    }

    /// Extract sorted deduplicated MIR construct tags for canonical bug
    /// fingerprinting.
    pub fn extract_mir_construct_tags(&self) -> Vec<String> {
        let mut tags = BTreeSet::new();
        tags.insert(format!("type:width:{}", self.scalar_width.rust_name()));
        if !self.struct_fields.is_empty() {
            tags.insert("type:repr_c_struct".to_string());
        }
        if self.slice_len.is_some() {
            tags.insert("type:slice".to_string());
        }
        collect_shrink_step_tags(&self.steps, &mut tags);
        for act in &self.env_schedule.global {
            tags.insert(env_action_tag(act));
        }
        for acts in self.env_schedule.per_callee.values() {
            for act in acts {
                tags.insert(env_action_tag(act));
            }
        }
        tags.into_iter().collect()
    }

    /// Deterministic Pass 6 (`CanonicalAlphaRename`): renumber locals (`0..`),
    /// blocks (`0..`), helpers (`0..`), and handles (`0..`) in first-appearance
    /// DFS order.
    pub fn canonical_alpha_renamed(&self) -> Self {
        fn parse_helper_callee_key_with_suffix(
            callee: &str,
        ) -> Option<(&'static str, usize, &str)> {
            for prefix in ["fuzz_helper_", "h"] {
                let Some(rest) = callee.strip_prefix(prefix) else {
                    continue;
                };
                if let Some((digits, suffix)) = rest.split_once('_') {
                    if !digits.is_empty()
                        && digits.bytes().all(|b| b.is_ascii_digit())
                        && matches!(
                            suffix,
                            "u8" | "u16"
                                | "u32"
                                | "u64"
                                | "u128"
                                | "usize"
                                | "i8"
                                | "i16"
                                | "i32"
                                | "i64"
                                | "i128"
                                | "isize"
                        )
                        && let Ok(id) = digits.parse::<usize>()
                    {
                        let width_suffix = &rest[digits.len()..];
                        return Some((prefix, id, width_suffix));
                    }
                } else if !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                    && let Ok(id) = rest.parse::<usize>()
                {
                    return Some((prefix, id, ""));
                }
            }
            None
        }

        fn collect_unwind_probe_callees(steps: &[ShrinkStep], out: &mut BTreeSet<String>) {
            for step in steps {
                match step {
                    ShrinkStep::UnwindProbe { callee, .. } => {
                        out.insert(callee.clone());
                    }
                    ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                        collect_unwind_probe_callees(then_steps, out);
                        collect_unwind_probe_callees(else_steps, out);
                    }
                    ShrinkStep::BoundedLoop { body, .. }
                    | ShrinkStep::IfFalseDecoy { body, .. }
                    | ShrinkStep::DropGuardWrapper { body, .. } => {
                        collect_unwind_probe_callees(body, out);
                    }
                    _ => {}
                }
            }
        }

        struct HelperIdRenamer {
            map: BTreeMap<usize, usize>,
            used_ids: BTreeSet<usize>,
        }

        impl HelperIdRenamer {
            fn alloc_next_id(&mut self) -> usize {
                let mut next = 0usize;
                while self.used_ids.contains(&next) {
                    next += 1;
                }
                self.used_ids.insert(next);
                next
            }

            fn map_helper(&mut self, old_id: usize) -> usize {
                if let Some(&mapped) = self.map.get(&old_id) {
                    return mapped;
                }
                let next = self.alloc_next_id();
                self.map.insert(old_id, next);
                next
            }
        }

        let mut unwind_probe_callees = BTreeSet::new();
        collect_unwind_probe_callees(&self.steps, &mut unwind_probe_callees);
        let reserved_helper_ids: BTreeSet<usize> = unwind_probe_callees
            .iter()
            .filter_map(|callee| parse_helper_callee_key_with_suffix(callee).map(|(_, id, _)| id))
            .collect();

        let mut local_map: BTreeMap<usize, usize> = BTreeMap::new();
        let mut block_map: BTreeMap<usize, usize> = BTreeMap::new();
        let mut helper_renamer =
            HelperIdRenamer { map: BTreeMap::new(), used_ids: reserved_helper_ids };
        let mut handle_map: BTreeMap<HandleId, HandleId> = BTreeMap::new();

        let map_local = |id: usize, m: &mut BTreeMap<usize, usize>| -> usize {
            let next = m.len();
            *m.entry(id).or_insert(next)
        };
        let map_block = |id: usize, m: &mut BTreeMap<usize, usize>| -> usize {
            let next = m.len();
            *m.entry(id).or_insert(next)
        };
        let map_handle = |id: HandleId, m: &mut BTreeMap<HandleId, HandleId>| -> HandleId {
            let next = m.len();
            *m.entry(id).or_insert(HandleId(next))
        };

        let mut inputs = Vec::with_capacity(self.inputs.len());
        for inp in &self.inputs {
            inputs.push(ShrinkInput {
                local_id: map_local(inp.local_id, &mut local_map),
                width: inp.width,
                value: inp.value,
                align_hint: inp.align_hint,
            });
        }
        let return_local = map_local(self.return_local, &mut local_map);

        #[allow(clippy::too_many_arguments)]
        fn rename_steps(
            steps: &[ShrinkStep],
            local_map: &mut BTreeMap<usize, usize>,
            block_map: &mut BTreeMap<usize, usize>,
            helper_renamer: &mut HelperIdRenamer,
            handle_map: &mut BTreeMap<HandleId, HandleId>,
            map_local: &dyn Fn(usize, &mut BTreeMap<usize, usize>) -> usize,
            map_block: &dyn Fn(usize, &mut BTreeMap<usize, usize>) -> usize,
            map_handle: &dyn Fn(HandleId, &mut BTreeMap<HandleId, HandleId>) -> HandleId,
        ) -> Vec<ShrinkStep> {
            steps
                .iter()
                .map(|s| match s {
                    ShrinkStep::Alloc { handle, size, align, local_id } => ShrinkStep::Alloc {
                        handle: map_handle(*handle, handle_map),
                        size: *size,
                        align: *align,
                        local_id: map_local(*local_id, local_map),
                    },
                    ShrinkStep::Borrow { dst, src, mutable, local_id } => ShrinkStep::Borrow {
                        dst: map_handle(*dst, handle_map),
                        src: map_handle(*src, handle_map),
                        mutable: *mutable,
                        local_id: map_local(*local_id, local_map),
                    },
                    ShrinkStep::SplitAt { left, right, src, mid, len, align } => {
                        ShrinkStep::SplitAt {
                            left: map_handle(*left, handle_map),
                            right: map_handle(*right, handle_map),
                            src: map_handle(*src, handle_map),
                            mid: *mid,
                            len: *len,
                            align: *align,
                        }
                    }
                    ShrinkStep::UseHandle { handle, offset, len, align, local_id } => {
                        ShrinkStep::UseHandle {
                            handle: map_handle(*handle, handle_map),
                            offset: *offset,
                            len: *len,
                            align: *align,
                            local_id: map_local(*local_id, local_map),
                        }
                    }
                    ShrinkStep::ArithImm { dst_local, op, imm } => ShrinkStep::ArithImm {
                        dst_local: map_local(*dst_local, local_map),
                        op: *op,
                        imm: *imm,
                    },
                    ShrinkStep::HelperCall { dst_local, helper_id, block_id, bias, rhs_local } => {
                        ShrinkStep::HelperCall {
                            dst_local: map_local(*dst_local, local_map),
                            helper_id: helper_renamer.map_helper(*helper_id),
                            block_id: map_block(*block_id, block_map),
                            bias: *bias,
                            rhs_local: rhs_local.map(|id| map_local(id, local_map)),
                        }
                    }
                    ShrinkStep::BranchMix {
                        block_id,
                        cond_local,
                        taken_then,
                        dynamic_even_cond,
                        then_steps,
                        else_steps,
                    } => ShrinkStep::BranchMix {
                        block_id: map_block(*block_id, block_map),
                        cond_local: map_local(*cond_local, local_map),
                        taken_then: *taken_then,
                        dynamic_even_cond: *dynamic_even_cond,
                        then_steps: rename_steps(
                            then_steps,
                            local_map,
                            block_map,
                            helper_renamer,
                            handle_map,
                            map_local,
                            map_block,
                            map_handle,
                        ),
                        else_steps: rename_steps(
                            else_steps,
                            local_map,
                            block_map,
                            helper_renamer,
                            handle_map,
                            map_local,
                            map_block,
                            map_handle,
                        ),
                    },
                    ShrinkStep::BoundedLoop { block_id, iters, induction, body } => {
                        ShrinkStep::BoundedLoop {
                            block_id: map_block(*block_id, block_map),
                            iters: *iters,
                            induction: induction.map(|ind| BoundedLoopInduction {
                                dst_local: map_local(ind.dst_local, local_map),
                                step_mul: ind.step_mul,
                                addend: ind.addend,
                            }),
                            body: rename_steps(
                                body,
                                local_map,
                                block_map,
                                helper_renamer,
                                handle_map,
                                map_local,
                                map_block,
                                map_handle,
                            ),
                        }
                    }
                    ShrinkStep::IfFalseDecoy { block_id, body } => ShrinkStep::IfFalseDecoy {
                        block_id: map_block(*block_id, block_map),
                        body: rename_steps(
                            body,
                            local_map,
                            block_map,
                            helper_renamer,
                            handle_map,
                            map_local,
                            map_block,
                            map_handle,
                        ),
                    },
                    ShrinkStep::DropGuardWrapper { local_id, body } => {
                        ShrinkStep::DropGuardWrapper {
                            local_id: map_local(*local_id, local_map),
                            body: rename_steps(
                                body,
                                local_map,
                                block_map,
                                helper_renamer,
                                handle_map,
                                map_local,
                                map_block,
                                map_handle,
                            ),
                        }
                    }
                    ShrinkStep::PaddedRoundTrip { local_id, tag_byte } => {
                        ShrinkStep::PaddedRoundTrip {
                            local_id: map_local(*local_id, local_map),
                            tag_byte: *tag_byte,
                        }
                    }
                    ShrinkStep::UnwindProbe { callee, dst_local, trigger_unwind, block_id } => {
                        ShrinkStep::UnwindProbe {
                            callee: callee.clone(),
                            dst_local: map_local(*dst_local, local_map),
                            trigger_unwind: *trigger_unwind,
                            block_id: map_block(*block_id, block_map),
                        }
                    }
                    ShrinkStep::PairOffsetLen { offset, len, align, local_id } => {
                        ShrinkStep::PairOffsetLen {
                            offset: *offset,
                            len: *len,
                            align: *align,
                            local_id: map_local(*local_id, local_map),
                        }
                    }
                    ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm } => {
                        ShrinkStep::XorLocalImm {
                            dst_local: map_local(*dst_local, local_map),
                            rhs_local: map_local(*rhs_local, local_map),
                            xor_imm: *xor_imm,
                        }
                    }
                })
                .collect()
        }

        let steps = rename_steps(
            &self.steps,
            &mut local_map,
            &mut block_map,
            &mut helper_renamer,
            &mut handle_map,
            &map_local,
            &map_block,
            &map_handle,
        );

        let mut helpers: Vec<ShrinkHelper> = self
            .helpers
            .iter()
            .filter_map(|h| {
                helper_renamer.map.get(&h.helper_id).map(|&new_id| ShrinkHelper {
                    helper_id: new_id,
                    multiplier: h.multiplier,
                    addend: h.addend,
                    op: h.op,
                })
            })
            .collect();
        helpers.sort_by_key(|h| h.helper_id);

        let mut orphan_ids = BTreeSet::new();
        for callee in self.env_schedule.per_callee.keys() {
            if unwind_probe_callees.contains(callee) {
                continue;
            }
            if let Some((_, old_id, _)) = parse_helper_callee_key_with_suffix(callee)
                && !helper_renamer.map.contains_key(&old_id)
            {
                orphan_ids.insert(old_id);
            }
        }
        let mut orphan_map = BTreeMap::new();
        for old_id in orphan_ids {
            orphan_map.insert(old_id, helper_renamer.alloc_next_id());
        }

        let mut env_schedule =
            EnvSchedule { per_callee: BTreeMap::new(), global: self.env_schedule.global.clone() };
        for (callee, acts) in &self.env_schedule.per_callee {
            let remapped_key = if unwind_probe_callees.contains(callee) {
                callee.clone()
            } else if let Some((prefix, old_id, width_suffix)) =
                parse_helper_callee_key_with_suffix(callee)
            {
                let new_id = helper_renamer
                    .map
                    .get(&old_id)
                    .or_else(|| orphan_map.get(&old_id))
                    .copied()
                    .unwrap_or(old_id);
                format!("{prefix}{new_id}{width_suffix}")
            } else {
                callee.clone()
            };
            env_schedule.per_callee.entry(remapped_key).or_default().extend(acts.iter().cloned());
        }

        Self {
            name: "repro_case".to_string(),
            scalar_width: self.scalar_width,
            inputs,
            struct_fields: self.struct_fields.clone(),
            slice_len: self.slice_len,
            slice_align: self.slice_align,
            helpers,
            steps,
            env_schedule,
            return_local,
        }
    }
}

fn env_action_tag(act: &EnvAction) -> String {
    match act {
        EnvAction::ReturnBytes(_) => "sched:return_bytes".to_string(),
        EnvAction::Unwind { .. } => "sched:unwind".to_string(),
        EnvAction::Abort { .. } => "sched:abort".to_string(),
    }
}

fn collect_shrink_step_tags(steps: &[ShrinkStep], out: &mut BTreeSet<String>) {
    for step in steps {
        match step {
            ShrinkStep::Alloc { .. } => {
                out.insert("v2:alloc".to_string());
            }
            ShrinkStep::Borrow { mutable, .. } => {
                out.insert(if *mutable {
                    "v2:borrow_mut".to_string()
                } else {
                    "v2:borrow_shared".to_string()
                });
            }
            ShrinkStep::SplitAt { .. } => {
                out.insert("v2:split_at".to_string());
            }
            ShrinkStep::UseHandle { .. } => {
                out.insert("v2:use_handle".to_string());
            }
            ShrinkStep::ArithImm { op, .. } => {
                out.insert(format!("assign:binop:{}", fuzz_arith_op_tag(*op)));
            }
            ShrinkStep::HelperCall { .. } => {
                out.insert("term:call_intra".to_string());
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                out.insert("term:switch_int".to_string());
                collect_shrink_step_tags(then_steps, out);
                collect_shrink_step_tags(else_steps, out);
            }
            ShrinkStep::BoundedLoop { body, .. } => {
                out.insert("cfg:bounded_loop".to_string());
                out.insert("term:switch_int".to_string());
                collect_shrink_step_tags(body, out);
            }
            ShrinkStep::IfFalseDecoy { body, .. } => {
                out.insert("cfg:if_false_decoy".to_string());
                collect_shrink_step_tags(body, out);
            }
            ShrinkStep::DropGuardWrapper { body, .. } => {
                out.insert("cfg:drop_guard".to_string());
                collect_shrink_step_tags(body, out);
            }
            ShrinkStep::PaddedRoundTrip { .. } => {
                out.insert("stmt:padded_round_trip".to_string());
            }
            ShrinkStep::UnwindProbe { trigger_unwind, .. } => {
                out.insert("term:call_cleanup".to_string());
                if *trigger_unwind {
                    out.insert("term:unwind_resume".to_string());
                }
            }
            ShrinkStep::PairOffsetLen { .. } => {
                out.insert("v2:pair_offset_len".to_string());
            }
            ShrinkStep::XorLocalImm { .. } => {
                out.insert("assign:binop:bit_xor".to_string());
            }
        }
    }
}

fn fuzz_arith_op_tag(op: FuzzArithOp) -> &'static str {
    match op {
        FuzzArithOp::Add => "add",
        FuzzArithOp::Sub => "sub",
        FuzzArithOp::Xor => "bit_xor",
        FuzzArithOp::BitOr => "bit_or",
        FuzzArithOp::BitAndMask => "bit_and_mask",
    }
}

/// Extract sorted, deduplicated MIR construct tags directly from a
/// [`FuzzProgram`] for canonical semantic bug fingerprinting.
pub fn extract_fuzz_program_construct_tags(prog: &FuzzProgram) -> Vec<String> {
    extract_fuzz_program_construct_tags_with_schedule(prog, None)
}

/// Extract sorted, deduplicated MIR construct tags from a [`FuzzProgram`] plus
/// its effective [`EnvSchedule`] so scheduled and unscheduled bugs separate
/// cleanly under canonical [`crate::dedup::CanonicalBugFingerprint`].
pub fn extract_fuzz_program_construct_tags_with_schedule(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
) -> Vec<String> {
    let mut tags = BTreeSet::new();
    tags.insert("type:width:u32".to_string());
    for step in &prog.steps {
        match step {
            FuzzStep::ArithImm { op, .. } => {
                tags.insert(format!("assign:binop:{}", fuzz_arith_op_tag(*op)));
            }
            FuzzStep::HelperCall { callee_idx, .. } => {
                tags.insert("term:call_intra".to_string());
                tags.insert(format!("callee:fuzz_helper_{}", callee_idx % 3));
            }
            FuzzStep::BranchMix { .. } => {
                tags.insert("term:switch_int".to_string());
            }
            FuzzStep::BoundedLoop { .. } => {
                tags.insert("cfg:bounded_loop".to_string());
                tags.insert("term:switch_int".to_string());
            }
            FuzzStep::PaddedRoundTrip { .. } => {
                tags.insert("stmt:padded_round_trip".to_string());
            }
            FuzzStep::UnwindProbe { trigger_unwind } => {
                tags.insert("term:call_cleanup".to_string());
                if *trigger_unwind {
                    tags.insert("term:unwind_resume".to_string());
                }
            }
        }
    }
    let eff_sched = resolve_effective_fuzz_schedule(prog, schedule);
    for act in &eff_sched.global {
        tags.insert(env_action_tag(act));
    }
    for acts in eff_sched.per_callee.values() {
        for act in acts {
            tags.insert(env_action_tag(act));
        }
    }
    tags.into_iter().collect()
}

/// Result of shrinking a [`ShrinkableCase`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkableCaseResult {
    pub original: ShrinkableCase,
    pub minimized: ShrinkableCase,
    pub predicate_evaluations: usize,
    pub succeeded: bool,
    pub is_one_minimal: bool,
    pub converged_1_minimal: bool,
    pub budget_exhausted: bool,
    pub pass_stats: ShrinkPassStats,
}

fn narrow_int_widths(w: IntKind) -> Vec<IntKind> {
    match w {
        IntKind::U128 => vec![IntKind::U64, IntKind::U32, IntKind::U16, IntKind::U8],
        IntKind::U64 | IntKind::Usize => vec![IntKind::U32, IntKind::U16, IntKind::U8],
        IntKind::U32 => vec![IntKind::U16, IntKind::U8],
        IntKind::U16 => vec![IntKind::U8],
        IntKind::I128 => vec![IntKind::I64, IntKind::I32, IntKind::I16, IntKind::I8],
        IntKind::I64 | IntKind::Isize => vec![IntKind::I32, IntKind::I16, IntKind::I8],
        IntKind::I32 => vec![IntKind::I16, IntKind::I8],
        IntKind::I16 => vec![IntKind::I8],
        IntKind::U8 | IntKind::I8 => Vec::new(),
    }
}

fn collect_used_helpers_in_steps(steps: &[ShrinkStep], used: &mut BTreeSet<usize>) {
    for step in steps {
        match step {
            ShrinkStep::HelperCall { helper_id, .. } => {
                used.insert(*helper_id);
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                collect_used_helpers_in_steps(then_steps, used);
                collect_shrink_step_helpers_else(else_steps, used);
            }
            ShrinkStep::BoundedLoop { body, .. }
            | ShrinkStep::IfFalseDecoy { body, .. }
            | ShrinkStep::DropGuardWrapper { body, .. } => {
                collect_used_helpers_in_steps(body, used);
            }
            _ => {}
        }
    }
}

fn collect_shrink_step_helpers_else(steps: &[ShrinkStep], used: &mut BTreeSet<usize>) {
    collect_used_helpers_in_steps(steps, used);
}

/// Shrink a [`ShrinkableCase`] across all 6 hierarchical passes using a
/// single predicate.
pub fn shrink_case_with_budget<F>(
    initial: &ShrinkableCase,
    budget: ShrinkBudget,
    mut predicate: F,
) -> ShrinkableCaseResult
where
    F: FnMut(&ShrinkableCase) -> bool,
{
    shrink_case_two_tier_with_budget(
        initial,
        budget,
        FastLegStrategy::FullFourWay,
        |_| true,
        |c| predicate(c),
    )
}

type NestedStepVisitor = fn(
    &mut Vec<ShrinkStep>,
    &std::cell::Cell<bool>,
    &std::cell::RefCell<ShrinkPassStats>,
    &mut dyn FnMut(&[ShrinkStep]) -> bool,
);

fn visit_shrink_step_children(
    steps: &mut [ShrinkStep],
    idx: usize,
    snapshot: &[ShrinkStep],
    budget_exhausted: &std::cell::Cell<bool>,
    stats: &std::cell::RefCell<ShrinkPassStats>,
    eval_seq: &mut dyn FnMut(&[ShrinkStep]) -> bool,
    visitor: NestedStepVisitor,
) {
    match steps[idx].clone() {
        ShrinkStep::BranchMix {
            block_id,
            cond_local,
            taken_then,
            dynamic_even_cond,
            mut then_steps,
            mut else_steps,
        } => {
            {
                let es = else_steps.clone();
                let mut sub_eval = |sub: &[ShrinkStep]| -> bool {
                    let mut cand = snapshot.to_vec();
                    cand[idx] = ShrinkStep::BranchMix {
                        block_id,
                        cond_local,
                        taken_then,
                        dynamic_even_cond,
                        then_steps: sub.to_vec(),
                        else_steps: es.clone(),
                    };
                    eval_seq(&cand)
                };
                visitor(&mut then_steps, budget_exhausted, stats, &mut sub_eval);
            }
            if !budget_exhausted.get() {
                let ts = then_steps.clone();
                let mut snapshot2 = snapshot.to_vec();
                snapshot2[idx] = ShrinkStep::BranchMix {
                    block_id,
                    cond_local,
                    taken_then,
                    dynamic_even_cond,
                    then_steps: ts.clone(),
                    else_steps: else_steps.clone(),
                };
                let mut sub_eval = |sub: &[ShrinkStep]| -> bool {
                    let mut cand = snapshot2.clone();
                    cand[idx] = ShrinkStep::BranchMix {
                        block_id,
                        cond_local,
                        taken_then,
                        dynamic_even_cond,
                        then_steps: ts.clone(),
                        else_steps: sub.to_vec(),
                    };
                    eval_seq(&cand)
                };
                visitor(&mut else_steps, budget_exhausted, stats, &mut sub_eval);
            }
            steps[idx] = ShrinkStep::BranchMix {
                block_id,
                cond_local,
                taken_then,
                dynamic_even_cond,
                then_steps,
                else_steps,
            };
        }
        ShrinkStep::BoundedLoop { block_id, iters, induction, mut body } => {
            let mut sub_eval = |sub: &[ShrinkStep]| -> bool {
                let mut cand = snapshot.to_vec();
                cand[idx] =
                    ShrinkStep::BoundedLoop { block_id, iters, induction, body: sub.to_vec() };
                eval_seq(&cand)
            };
            visitor(&mut body, budget_exhausted, stats, &mut sub_eval);
            steps[idx] = ShrinkStep::BoundedLoop { block_id, iters, induction, body };
        }
        ShrinkStep::IfFalseDecoy { block_id, mut body } => {
            let mut sub_eval = |sub: &[ShrinkStep]| -> bool {
                let mut cand = snapshot.to_vec();
                cand[idx] = ShrinkStep::IfFalseDecoy { block_id, body: sub.to_vec() };
                eval_seq(&cand)
            };
            visitor(&mut body, budget_exhausted, stats, &mut sub_eval);
            steps[idx] = ShrinkStep::IfFalseDecoy { block_id, body };
        }
        ShrinkStep::DropGuardWrapper { local_id, mut body } => {
            let mut sub_eval = |sub: &[ShrinkStep]| -> bool {
                let mut cand = snapshot.to_vec();
                cand[idx] = ShrinkStep::DropGuardWrapper { local_id, body: sub.to_vec() };
                eval_seq(&cand)
            };
            visitor(&mut body, budget_exhausted, stats, &mut sub_eval);
            steps[idx] = ShrinkStep::DropGuardWrapper { local_id, body };
        }
        _ => {}
    }
}

fn shrink_steps_recursive(
    steps: &mut Vec<ShrinkStep>,
    budget_exhausted: &std::cell::Cell<bool>,
    stats: &std::cell::RefCell<ShrinkPassStats>,
    eval_seq: &mut dyn FnMut(&[ShrinkStep]) -> bool,
) {
    let before = steps.len();
    let seq_res = shrink_sequence_1_minimal(steps, |cand_steps| eval_seq(cand_steps));
    *steps = seq_res.minimized;
    if steps.len() < before {
        stats.borrow_mut().step_ddmin_reductions += before - steps.len();
    }
    for idx in 0..steps.len() {
        if budget_exhausted.get() {
            break;
        }
        let snapshot = steps.clone();
        visit_shrink_step_children(
            steps,
            idx,
            &snapshot,
            budget_exhausted,
            stats,
            eval_seq,
            shrink_steps_recursive,
        );
    }
}

fn collapse_steps_recursive(
    steps: &mut Vec<ShrinkStep>,
    budget_exhausted: &std::cell::Cell<bool>,
    stats: &std::cell::RefCell<ShrinkPassStats>,
    eval_seq: &mut dyn FnMut(&[ShrinkStep]) -> bool,
) {
    let mut idx = 0usize;
    while idx < steps.len() && !budget_exhausted.get() {
        let replacements: Vec<Vec<ShrinkStep>> = match &steps[idx] {
            ShrinkStep::HelperCall { dst_local, bias, .. } => vec![
                vec![ShrinkStep::ArithImm { dst_local: *dst_local, op: FuzzArithOp::Add, imm: 0 }],
                vec![ShrinkStep::ArithImm {
                    dst_local: *dst_local,
                    op: FuzzArithOp::Add,
                    imm: *bias,
                }],
            ],
            ShrinkStep::BranchMix {
                taken_then, dynamic_even_cond, then_steps, else_steps, ..
            } => {
                if *dynamic_even_cond || *taken_then {
                    vec![then_steps.clone(), else_steps.clone()]
                } else {
                    vec![else_steps.clone(), then_steps.clone()]
                }
            }
            ShrinkStep::BoundedLoop { block_id, iters, induction, body } => {
                let mut opts = Vec::new();
                if *iters > 1 {
                    opts.push(vec![ShrinkStep::BoundedLoop {
                        block_id: *block_id,
                        iters: 1,
                        induction: *induction,
                        body: body.clone(),
                    }]);
                }
                if let Some(ind) = induction {
                    let mut unrolled = vec![ShrinkStep::ArithImm {
                        dst_local: ind.dst_local,
                        op: FuzzArithOp::Add,
                        imm: ind.addend,
                    }];
                    unrolled.extend(body.iter().cloned());
                    opts.push(unrolled);
                }
                opts.push(body.clone());
                opts
            }
            ShrinkStep::IfFalseDecoy { .. } => vec![Vec::new()],
            ShrinkStep::DropGuardWrapper { body, .. } => vec![body.clone()],
            _ => Vec::new(),
        };
        let mut collapsed = false;
        for rep in replacements {
            if budget_exhausted.get() {
                break;
            }
            let mut cand = steps.clone();
            cand.splice(idx..=idx, rep);
            if eval_seq(&cand) {
                *steps = cand;
                stats.borrow_mut().call_cfg_collapse_reductions += 1;
                collapsed = true;
                break;
            }
        }
        if collapsed {
            continue;
        }
        let snapshot = steps.clone();
        visit_shrink_step_children(
            steps,
            idx,
            &snapshot,
            budget_exhausted,
            stats,
            eval_seq,
            collapse_steps_recursive,
        );
        idx += 1;
    }
}

fn shrink_u64_stride_budgeted(
    initial: u64,
    align: Option<u64>,
    budget_exhausted: &std::cell::Cell<bool>,
    mut pred: impl FnMut(u64) -> bool,
) -> u64 {
    let mut cur = initial;
    while cur > 0 && !budget_exhausted.get() {
        let mut found = None;
        for cand in smaller_u64_stride_candidates(cur, align) {
            if budget_exhausted.get() {
                break;
            }
            if pred(cand) {
                found = Some(cand);
                break;
            }
        }
        match found {
            Some(v) => cur = v,
            None => break,
        }
    }
    cur
}

fn smaller_power_of_two_aligns(align: u32) -> Vec<u32> {
    let mut cands = Vec::new();
    let mut a = 1u32;
    while a < align {
        cands.push(a);
        a = match a.checked_mul(2) {
            Some(next) => next,
            None => break,
        };
    }
    cands
}

#[allow(clippy::ptr_arg)] // Signature matches visitor fn pointer shared with Vec-mutating passes.
fn shrink_step_scalars_recursive(
    steps: &mut Vec<ShrinkStep>,
    budget_exhausted: &std::cell::Cell<bool>,
    stats: &std::cell::RefCell<ShrinkPassStats>,
    eval_seq: &mut dyn FnMut(&[ShrinkStep]) -> bool,
) {
    let mut idx = 0usize;
    while idx < steps.len() && !budget_exhausted.get() {
        let mut snapshot = steps.clone();
        match steps[idx].clone() {
            ShrinkStep::PairOffsetLen { offset, len, mut align, local_id } => {
                for cand_align in smaller_power_of_two_aligns(align) {
                    if budget_exhausted.get() {
                        break;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] =
                        ShrinkStep::PairOffsetLen { offset, len, align: cand_align, local_id };
                    if eval_seq(&cand) {
                        align = cand_align;
                        steps[idx] = cand[idx].clone();
                        snapshot[idx] = steps[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                        break;
                    }
                }
                let (no, nl) = shrink_coupled_pair_with_difference_proxy(
                    offset,
                    len,
                    Some(align),
                    |co, cl| {
                        let mut cand = snapshot.clone();
                        cand[idx] =
                            ShrinkStep::PairOffsetLen { offset: co, len: cl, align, local_id };
                        eval_seq(&cand)
                    },
                );
                if (no, nl) != (offset, len) {
                    steps[idx] = ShrinkStep::PairOffsetLen { offset: no, len: nl, align, local_id };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::SplitAt { left, right, src, mid, len, mut align } => {
                for cand_align in smaller_power_of_two_aligns(align) {
                    if budget_exhausted.get() {
                        break;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] =
                        ShrinkStep::SplitAt { left, right, src, mid, len, align: cand_align };
                    if eval_seq(&cand) {
                        align = cand_align;
                        steps[idx] = cand[idx].clone();
                        snapshot[idx] = steps[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                        break;
                    }
                }
                let (nm, nl) =
                    shrink_coupled_pair_with_difference_proxy(mid, len, Some(align), |cm, cl| {
                        let mut cand = snapshot.clone();
                        cand[idx] =
                            ShrinkStep::SplitAt { left, right, src, mid: cm, len: cl, align };
                        eval_seq(&cand)
                    });
                if (nm, nl) != (mid, len) {
                    steps[idx] = ShrinkStep::SplitAt { left, right, src, mid: nm, len: nl, align };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::UseHandle { handle, offset, len, mut align, local_id } => {
                for cand_align in smaller_power_of_two_aligns(align) {
                    if budget_exhausted.get() {
                        break;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] =
                        ShrinkStep::UseHandle { handle, offset, len, align: cand_align, local_id };
                    if eval_seq(&cand) {
                        align = cand_align;
                        steps[idx] = cand[idx].clone();
                        snapshot[idx] = steps[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                        break;
                    }
                }
                let (no, nl) = shrink_coupled_pair_with_difference_proxy(
                    offset,
                    len,
                    Some(align),
                    |co, cl| {
                        let mut cand = snapshot.clone();
                        cand[idx] =
                            ShrinkStep::UseHandle { handle, offset: co, len: cl, align, local_id };
                        eval_seq(&cand)
                    },
                );
                if (no, nl) != (offset, len) {
                    steps[idx] =
                        ShrinkStep::UseHandle { handle, offset: no, len: nl, align, local_id };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::Alloc { handle, size, mut align, local_id } => {
                for cand_align in smaller_power_of_two_aligns(align) {
                    if budget_exhausted.get() {
                        break;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::Alloc { handle, size, align: cand_align, local_id };
                    if eval_seq(&cand) {
                        align = cand_align;
                        steps[idx] = cand[idx].clone();
                        snapshot[idx] = steps[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                        break;
                    }
                }
                let ns = shrink_u32_stride_non_monotonic(size, Some(align), |cs| {
                    if budget_exhausted.get() {
                        return false;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::Alloc { handle, size: cs, align, local_id };
                    eval_seq(&cand)
                });
                if ns < size {
                    steps[idx] = ShrinkStep::Alloc { handle, size: ns, align, local_id };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::ArithImm { dst_local, op, imm } => {
                let cur = shrink_u64_stride_budgeted(imm, None, budget_exhausted, |cand_imm| {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::ArithImm { dst_local, op, imm: cand_imm };
                    eval_seq(&cand)
                });
                let mut next_op = op;
                if next_op != FuzzArithOp::Add && !budget_exhausted.get() {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::ArithImm { dst_local, op: FuzzArithOp::Add, imm: cur };
                    if eval_seq(&cand) {
                        next_op = FuzzArithOp::Add;
                    }
                }
                if cur < imm || next_op != op {
                    steps[idx] = ShrinkStep::ArithImm { dst_local, op: next_op, imm: cur };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::HelperCall { dst_local, helper_id, block_id, bias, rhs_local } => {
                let mut cur_rhs = rhs_local;
                if cur_rhs.is_some() && !budget_exhausted.get() {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::HelperCall {
                        dst_local,
                        helper_id,
                        block_id,
                        bias,
                        rhs_local: None,
                    };
                    if eval_seq(&cand) {
                        cur_rhs = None;
                        steps[idx] = cand[idx].clone();
                        snapshot[idx] = steps[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                    }
                }
                let cur = shrink_u64_stride_budgeted(bias, None, budget_exhausted, |cand_bias| {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::HelperCall {
                        dst_local,
                        helper_id,
                        block_id,
                        bias: cand_bias,
                        rhs_local: cur_rhs,
                    };
                    eval_seq(&cand)
                });
                if cur < bias {
                    steps[idx] = ShrinkStep::HelperCall {
                        dst_local,
                        helper_id,
                        block_id,
                        bias: cur,
                        rhs_local: cur_rhs,
                    };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::PaddedRoundTrip { local_id, tag_byte } => {
                let tb = shrink_u32_non_monotonic(u32::from(tag_byte), |cand_tb| {
                    if budget_exhausted.get() {
                        return false;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::PaddedRoundTrip { local_id, tag_byte: cand_tb as u8 };
                    eval_seq(&cand)
                });
                if tb < u32::from(tag_byte) {
                    steps[idx] = ShrinkStep::PaddedRoundTrip { local_id, tag_byte: tb as u8 };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::BoundedLoop { block_id, mut iters, mut induction, body } => {
                let shrunk_iters = shrink_u32_stride_non_monotonic(iters, None, |ci| {
                    if ci == 0 || budget_exhausted.get() {
                        return false;
                    }
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::BoundedLoop {
                        block_id,
                        iters: ci,
                        induction,
                        body: body.clone(),
                    };
                    eval_seq(&cand)
                });
                if shrunk_iters < iters {
                    iters = shrunk_iters;
                    steps[idx] =
                        ShrinkStep::BoundedLoop { block_id, iters, induction, body: body.clone() };
                    snapshot[idx] = steps[idx].clone();
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
                if let Some(mut ind) = induction {
                    if !body.is_empty() && !budget_exhausted.get() {
                        let mut cand = snapshot.clone();
                        cand[idx] = ShrinkStep::BoundedLoop {
                            block_id,
                            iters,
                            induction: None,
                            body: body.clone(),
                        };
                        if eval_seq(&cand) {
                            induction = None;
                            steps[idx] = cand[idx].clone();
                            snapshot[idx] = steps[idx].clone();
                            stats.borrow_mut().stride_diff_proxy_reductions += 1;
                        }
                    }
                    if induction.is_some() && !budget_exhausted.get() {
                        let shrunk_mul = shrink_u64_stride_budgeted(
                            ind.step_mul,
                            None,
                            budget_exhausted,
                            |cm| {
                                let mut cand = snapshot.clone();
                                let mut c_ind = ind;
                                c_ind.step_mul = cm;
                                cand[idx] = ShrinkStep::BoundedLoop {
                                    block_id,
                                    iters,
                                    induction: Some(c_ind),
                                    body: body.clone(),
                                };
                                eval_seq(&cand)
                            },
                        );
                        if shrunk_mul < ind.step_mul {
                            ind.step_mul = shrunk_mul;
                            steps[idx] = ShrinkStep::BoundedLoop {
                                block_id,
                                iters,
                                induction: Some(ind),
                                body: body.clone(),
                            };
                            snapshot[idx] = steps[idx].clone();
                            stats.borrow_mut().stride_diff_proxy_reductions += 1;
                        }
                        if !budget_exhausted.get() {
                            let shrunk_add = shrink_u64_stride_budgeted(
                                ind.addend,
                                None,
                                budget_exhausted,
                                |ca| {
                                    let mut cand = snapshot.clone();
                                    let mut c_ind = ind;
                                    c_ind.addend = ca;
                                    cand[idx] = ShrinkStep::BoundedLoop {
                                        block_id,
                                        iters,
                                        induction: Some(c_ind),
                                        body: body.clone(),
                                    };
                                    eval_seq(&cand)
                                },
                            );
                            if shrunk_add < ind.addend {
                                ind.addend = shrunk_add;
                                steps[idx] = ShrinkStep::BoundedLoop {
                                    block_id,
                                    iters,
                                    induction: Some(ind),
                                    body: body.clone(),
                                };
                                snapshot[idx] = steps[idx].clone();
                                stats.borrow_mut().stride_diff_proxy_reductions += 1;
                            }
                        }
                    }
                }
                if !budget_exhausted.get() {
                    let snap_loop = steps.clone();
                    visit_shrink_step_children(
                        steps,
                        idx,
                        &snap_loop,
                        budget_exhausted,
                        stats,
                        eval_seq,
                        shrink_step_scalars_recursive,
                    );
                }
            }
            ShrinkStep::Borrow { dst, src, mutable: true, local_id } => {
                if !budget_exhausted.get() {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::Borrow { dst, src, mutable: false, local_id };
                    if eval_seq(&cand) {
                        steps[idx] = cand[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                    }
                }
            }
            ShrinkStep::UnwindProbe { callee, dst_local, trigger_unwind: true, block_id } => {
                if !budget_exhausted.get() {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::UnwindProbe {
                        callee: callee.clone(),
                        dst_local,
                        trigger_unwind: false,
                        block_id,
                    };
                    if eval_seq(&cand) {
                        steps[idx] = cand[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                    }
                }
            }
            ShrinkStep::BranchMix {
                block_id,
                cond_local,
                mut taken_then,
                mut dynamic_even_cond,
                then_steps,
                else_steps,
            } => {
                if dynamic_even_cond && !budget_exhausted.get() {
                    for cand_taken in [false, true] {
                        if budget_exhausted.get() {
                            break;
                        }
                        let mut cand = snapshot.clone();
                        cand[idx] = ShrinkStep::BranchMix {
                            block_id,
                            cond_local,
                            taken_then: cand_taken,
                            dynamic_even_cond: false,
                            then_steps: then_steps.clone(),
                            else_steps: else_steps.clone(),
                        };
                        if eval_seq(&cand) {
                            taken_then = cand_taken;
                            dynamic_even_cond = false;
                            steps[idx] = cand[idx].clone();
                            snapshot[idx] = steps[idx].clone();
                            stats.borrow_mut().stride_diff_proxy_reductions += 1;
                            break;
                        }
                    }
                }
                if !dynamic_even_cond && taken_then && !budget_exhausted.get() {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::BranchMix {
                        block_id,
                        cond_local,
                        taken_then: false,
                        dynamic_even_cond: false,
                        then_steps: then_steps.clone(),
                        else_steps: else_steps.clone(),
                    };
                    if eval_seq(&cand) {
                        steps[idx] = cand[idx].clone();
                        snapshot[idx] = steps[idx].clone();
                        stats.borrow_mut().stride_diff_proxy_reductions += 1;
                    }
                }
                if !budget_exhausted.get() {
                    visit_shrink_step_children(
                        steps,
                        idx,
                        &snapshot,
                        budget_exhausted,
                        stats,
                        eval_seq,
                        shrink_step_scalars_recursive,
                    );
                }
            }
            ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm } => {
                let cur = shrink_u64_stride_budgeted(xor_imm, None, budget_exhausted, |cand_imm| {
                    let mut cand = snapshot.clone();
                    cand[idx] = ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm: cand_imm };
                    eval_seq(&cand)
                });
                if cur < xor_imm {
                    steps[idx] = ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm: cur };
                    stats.borrow_mut().stride_diff_proxy_reductions += 1;
                }
            }
            ShrinkStep::IfFalseDecoy { .. } | ShrinkStep::DropGuardWrapper { .. } => {
                visit_shrink_step_children(
                    steps,
                    idx,
                    &snapshot,
                    budget_exhausted,
                    stats,
                    eval_seq,
                    shrink_step_scalars_recursive,
                );
            }
            _ => {}
        }
        idx += 1;
    }
}

/// Shrink a [`ShrinkableCase`] across all 6 hierarchical passes
/// (`ScheduleDdmin`, `StepDdmin` + `PropEr` handle def-use filter,
/// `CallAndCfgCollapse`, `TypeAndLayoutNarrow`,
/// `StrideAndDifferenceProxyScalarShrink`, `CanonicalAlphaRename`) with
/// two-tier fast-leg-first short-circuiting.
pub fn shrink_case_two_tier_with_budget<F1, F2>(
    initial: &ShrinkableCase,
    budget: ShrinkBudget,
    strategy: FastLegStrategy,
    mut fast_leg_check: F1,
    mut full_eval: F2,
) -> ShrinkableCaseResult
where
    F1: FnMut(&ShrinkableCase) -> bool,
    F2: FnMut(&ShrinkableCase) -> bool,
{
    let start = Instant::now();
    let mut cache: BTreeMap<String, bool> = BTreeMap::new();
    let eval_count = std::cell::Cell::new(0usize);
    let budget_exhausted = std::cell::Cell::new(false);
    let stats = std::cell::RefCell::new(ShrinkPassStats {
        fast_leg_strategy: strategy,
        ..Default::default()
    });
    let last_full_confirmed_key = std::cell::RefCell::new(String::new());

    let mut eval_cached = |c: &ShrinkableCase| -> bool {
        if !all_handles_defined_and_typed(&c.steps, &c.helpers) {
            stats.borrow_mut().def_use_filter_skips += 1;
            return false;
        }
        let key = canonical_shrinkable_case_key(c);
        if let Some(&cached) = cache.get(&key) {
            return cached;
        }
        let seen = eval_count.get();
        if seen >= budget.max_evals || start.elapsed() >= budget.max_duration {
            budget_exhausted.set(true);
            return false;
        }
        eval_count.set(seen + 1);
        let res = if strategy != FastLegStrategy::FullFourWay && seen > 0 {
            stats.borrow_mut().fast_leg_evaluations += 1;
            if !fast_leg_check(c) {
                stats.borrow_mut().fast_leg_rejections += 1;
                false
            } else {
                stats.borrow_mut().full_oracle_evaluations += 1;
                let ok = full_eval(c);
                if ok {
                    *last_full_confirmed_key.borrow_mut() = key.clone();
                }
                ok
            }
        } else {
            stats.borrow_mut().full_oracle_evaluations += 1;
            let ok = full_eval(c);
            if ok {
                *last_full_confirmed_key.borrow_mut() = key.clone();
            }
            ok
        };
        cache.insert(key, res);
        res
    };

    if budget.max_evals == 0 || start.elapsed() >= budget.max_duration {
        budget_exhausted.set(true);
        return ShrinkableCaseResult {
            original: initial.clone(),
            minimized: initial.clone(),
            predicate_evaluations: eval_count.get(),
            succeeded: false,
            is_one_minimal: false,
            converged_1_minimal: false,
            budget_exhausted: true,
            pass_stats: stats.into_inner(),
        };
    }

    if !eval_cached(initial) {
        return ShrinkableCaseResult {
            original: initial.clone(),
            minimized: initial.clone(),
            predicate_evaluations: eval_count.get(),
            succeeded: false,
            is_one_minimal: false,
            converged_1_minimal: false,
            budget_exhausted: budget_exhausted.get(),
            pass_stats: stats.into_inner(),
        };
    }

    let mut best = initial.clone();

    loop {
        let prev = best.clone();

        // Pass 1: ScheduleDdmin.
        if !best.env_schedule.is_empty() {
            let snapshot = best.clone();
            let shrunk_sched = shrink_env_schedule(&best.env_schedule, |cand_sched| {
                let mut cand = snapshot.clone();
                cand.env_schedule = cand_sched.clone();
                eval_cached(&cand)
            });
            if shrunk_sched != best.env_schedule {
                best.env_schedule = shrunk_sched;
                stats.borrow_mut().schedule_ddmin_reductions += 1;
            }
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 2: StepDdmin + PropEr handle def-use filter (recursively across
        // nested BranchMix, BoundedLoop, IfFalseDecoy, and DropGuardWrapper
        // step lists).
        {
            let template = best.clone();
            let mut steps_work = template.steps.clone();
            let mut seq_eval = |cand_steps: &[ShrinkStep]| -> bool {
                let mut cand = template.clone();
                cand.steps = cand_steps.to_vec();
                eval_cached(&cand)
            };
            shrink_steps_recursive(&mut steps_work, &budget_exhausted, &stats, &mut seq_eval);
            best.steps = steps_work;
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 3: CallAndCfgCollapse (calls -> imm, BranchMix -> arm,
        // BoundedLoop -> 1 iter -> body, strip IfFalseDecoy &
        // DropGuardWrapper, recursively through nested blocks, prune unused
        // helpers).
        {
            let template = best.clone();
            let mut steps_work = template.steps.clone();
            let mut seq_eval = |cand_steps: &[ShrinkStep]| -> bool {
                let mut cand = template.clone();
                cand.steps = cand_steps.to_vec();
                eval_cached(&cand)
            };
            collapse_steps_recursive(&mut steps_work, &budget_exhausted, &stats, &mut seq_eval);
            best.steps = steps_work;
        }
        // Prune unused helpers (`remove_fns`).
        if !best.helpers.is_empty() && !budget_exhausted.get() {
            let mut used = BTreeSet::new();
            collect_used_helpers_in_steps(&best.steps, &mut used);
            let pruned: Vec<ShrinkHelper> =
                best.helpers.iter().filter(|h| used.contains(&h.helper_id)).cloned().collect();
            if pruned.len() < best.helpers.len() {
                let mut cand = best.clone();
                cand.helpers = pruned;
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().call_cfg_collapse_reductions += 1;
                }
            }
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 4: TypeAndLayoutNarrow (prune noncausal inputs via 1-minimal
        // ddmin, narrow u128 -> u64 -> u32 -> u16 -> u8, struct field
        // counts/widths preserving alignment, slice/alloc lengths).
        if !best.inputs.is_empty() && !budget_exhausted.get() {
            let snapshot = best.clone();
            let res = shrink_sequence_1_minimal(&best.inputs, |cand_inputs| {
                if budget_exhausted.get() {
                    return false;
                }
                let mut cand = snapshot.clone();
                cand.inputs = cand_inputs.to_vec();
                eval_cached(&cand)
            });
            if res.minimized.len() < best.inputs.len() {
                best.inputs = res.minimized;
                stats.borrow_mut().type_layout_narrow_reductions += 1;
            }
        }
        if budget_exhausted.get() {
            break;
        }
        // Narrow default `scalar_width` independently of per-input widths, then
        // narrow each input width individually.
        for w in narrow_int_widths(best.scalar_width) {
            if budget_exhausted.get() {
                break;
            }
            let mut cand = best.clone();
            cand.scalar_width = w;
            if eval_cached(&cand) {
                best = cand;
                stats.borrow_mut().type_layout_narrow_reductions += 1;
            }
        }
        for ii in 0..best.inputs.len() {
            if budget_exhausted.get() {
                break;
            }
            for w in narrow_int_widths(best.inputs[ii].width) {
                if budget_exhausted.get() {
                    break;
                }
                let mut cand = best.clone();
                cand.inputs[ii].width = w;
                cand.inputs[ii].value = w.mask_bits(cand.inputs[ii].value);
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().type_layout_narrow_reductions += 1;
                }
            }
            if let Some(cur_align) = best.inputs[ii].align_hint
                && !budget_exhausted.get()
            {
                let mut cand = best.clone();
                cand.inputs[ii].align_hint = None;
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().type_layout_narrow_reductions += 1;
                } else {
                    let mut align_cands = Vec::new();
                    let mut a = 1u32;
                    while a < cur_align {
                        align_cands.push(Some(a));
                        a = a.saturating_mul(2);
                    }
                    for cand_align in align_cands {
                        if budget_exhausted.get() {
                            break;
                        }
                        let mut cand = best.clone();
                        cand.inputs[ii].align_hint = cand_align;
                        if eval_cached(&cand) {
                            best = cand;
                            stats.borrow_mut().type_layout_narrow_reductions += 1;
                            break;
                        }
                    }
                }
            }
        }
        if !best.struct_fields.is_empty() && !budget_exhausted.get() {
            let snapshot = best.clone();
            let res = shrink_sequence_1_minimal(&best.struct_fields, |cand_fields| {
                let mut cand = snapshot.clone();
                cand.struct_fields = cand_fields.to_vec();
                eval_cached(&cand)
            });
            if res.minimized.len() < best.struct_fields.len() {
                best.struct_fields = res.minimized;
                stats.borrow_mut().type_layout_narrow_reductions += 1;
            }
        }
        for fi in 0..best.struct_fields.len() {
            if budget_exhausted.get() {
                break;
            }
            for w in narrow_int_widths(best.struct_fields[fi]) {
                let mut cand = best.clone();
                cand.struct_fields[fi] = w;
                if eval_cached(&cand) {
                    best = cand;
                    stats.borrow_mut().type_layout_narrow_reductions += 1;
                    break;
                }
            }
        }
        if best.slice_align > 1 && !budget_exhausted.get() {
            let mut align_cands = Vec::new();
            let mut a = 1usize;
            while a < best.slice_align {
                align_cands.push(a);
                a = a.saturating_mul(2);
            }
            for cand_align in align_cands {
                let mut cand = best.clone();
                cand.slice_align = cand_align;
                if eval_cached(&cand) {
                    best.slice_align = cand_align;
                    stats.borrow_mut().type_layout_narrow_reductions += 1;
                    break;
                }
            }
        }
        if let Some(len) = best.slice_len
            && !budget_exhausted.get()
        {
            let mut drop_cand = best.clone();
            drop_cand.slice_len = None;
            if eval_cached(&drop_cand) {
                best.slice_len = None;
                stats.borrow_mut().type_layout_narrow_reductions += 1;
            } else if len > 0 {
                let align = best.slice_align.max(1) as u64;
                for cand_len in smaller_u64_stride_candidates(len as u64, Some(align)) {
                    let mut cand = best.clone();
                    cand.slice_len = Some(cand_len as usize);
                    if eval_cached(&cand) {
                        best.slice_len = Some(cand_len as usize);
                        stats.borrow_mut().type_layout_narrow_reductions += 1;
                        break;
                    }
                }
            }
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 5: StrideAndDifferenceProxyScalarShrink.
        for i in 0..best.inputs.len() {
            if budget_exhausted.get() {
                break;
            }
            let orig = best.inputs[i].value;
            let align = best.inputs[i].align_hint.map(u128::from);
            let shrunk = shrink_u128_stride_non_monotonic(orig, align, |nv| {
                let mut cand = best.clone();
                cand.inputs[i].value = nv;
                eval_cached(&cand)
            });
            if shrunk < orig {
                best.inputs[i].value = shrunk;
                stats.borrow_mut().stride_diff_proxy_reductions += 1;
            }
        }
        for i in 0..best.helpers.len() {
            if budget_exhausted.get() {
                break;
            }
            let orig_mul = best.helpers[i].multiplier;
            let shrunk_mul = shrink_u64_stride_budgeted(orig_mul, None, &budget_exhausted, |cm| {
                let mut cand = best.clone();
                cand.helpers[i].multiplier = cm;
                eval_cached(&cand)
            });
            if shrunk_mul < orig_mul {
                best.helpers[i].multiplier = shrunk_mul;
                stats.borrow_mut().stride_diff_proxy_reductions += 1;
            }
            if budget_exhausted.get() {
                break;
            }
            let orig_add = best.helpers[i].addend;
            let shrunk_add = shrink_u64_stride_budgeted(orig_add, None, &budget_exhausted, |ca| {
                let mut cand = best.clone();
                cand.helpers[i].addend = ca;
                eval_cached(&cand)
            });
            if shrunk_add < orig_add {
                best.helpers[i].addend = shrunk_add;
                stats.borrow_mut().stride_diff_proxy_reductions += 1;
            }
        }
        if !budget_exhausted.get() {
            let template = best.clone();
            let mut steps_work = template.steps.clone();
            let mut seq_eval = |cand_steps: &[ShrinkStep]| -> bool {
                if budget_exhausted.get() {
                    return false;
                }
                let mut cand = template.clone();
                cand.steps = cand_steps.to_vec();
                eval_cached(&cand)
            };
            shrink_step_scalars_recursive(
                &mut steps_work,
                &budget_exhausted,
                &stats,
                &mut seq_eval,
            );
            best.steps = steps_work;
        }
        if budget_exhausted.get() {
            break;
        }

        // Pass 6: CanonicalAlphaRename.
        let renamed = best.canonical_alpha_renamed();
        if renamed != best && eval_cached(&renamed) {
            best = renamed;
            stats.borrow_mut().alpha_rename_applied += 1;
        }

        if budget_exhausted.get() || best == prev {
            break;
        }
    }

    let (hit_budget, final_confirmed, succeeded) = confirm_final_shrink_outcome(
        budget_exhausted.get(),
        last_full_confirmed_key.borrow().as_str(),
        canonical_shrinkable_case_key(&best).as_str(),
        &eval_count,
        budget,
        start.elapsed(),
        &stats,
        || full_eval(&best),
    );
    let is_one_minimal = !hit_budget && final_confirmed;

    ShrinkableCaseResult {
        original: initial.clone(),
        minimized: best,
        predicate_evaluations: eval_count.get(),
        succeeded,
        is_one_minimal,
        converged_1_minimal: is_one_minimal,
        budget_exhausted: hit_budget,
        pass_stats: stats.into_inner(),
    }
}

/// Infallible canonical cache key for [`FuzzProgram`] (avoids fallible
/// `serde_json` tagged-enum serialization errors collapsing keys to `""`).
pub(crate) fn canonical_fuzz_program_key(prog: &FuzzProgram) -> String {
    format!("{prog:?}")
}

/// Infallible canonical encoder for [`ShrinkableCase`] covering every field,
/// nested step, and `EnvSchedule` in a compact length-prefixed form for fast
/// shrink cache and skeleton hashing.
pub(crate) fn canonical_shrinkable_case_key(case: &ShrinkableCase) -> String {
    let mut out = String::with_capacity(256);
    encode_str_field(&mut out, &case.name);
    let _ = write!(
        out,
        "|w={}|rl={}|sl={:?}|sa={}|",
        case.scalar_width.rust_name(),
        case.return_local,
        case.slice_len,
        case.slice_align,
    );
    let _ = write!(out, "in=[");
    for inp in &case.inputs {
        let _ = write!(
            out,
            "({},{},{},{:?});",
            inp.local_id,
            inp.width.rust_name(),
            inp.value,
            inp.align_hint
        );
    }
    out.push_str("]|sf=[");
    for f in &case.struct_fields {
        let _ = write!(out, "{},", f.rust_name());
    }
    out.push_str("]|h=[");
    for h in &case.helpers {
        let op_tag = match h.op {
            ShrinkHelperOp::AffineMulAdd => "aff",
            ShrinkHelperOp::BitXorAdd => "xor",
            ShrinkHelperOp::AbsDiffBranch => "abs",
        };
        let _ = write!(out, "({},{op_tag},{},{});", h.helper_id, h.multiplier, h.addend);
    }
    out.push_str("]|steps=[");
    encode_shrink_steps_canon(&case.steps, &mut out);
    out.push_str("]|sched=[g:");
    for act in &case.env_schedule.global {
        encode_env_action_canon(act, &mut out);
    }
    out.push_str(";p:");
    for (callee, acts) in &case.env_schedule.per_callee {
        encode_str_field(&mut out, callee);
        out.push(':');
        for act in acts {
            encode_env_action_canon(act, &mut out);
        }
        out.push(';');
    }
    out.push(']');
    out
}

fn encode_str_field(out: &mut String, s: &str) {
    let _ = write!(out, "{}:{s}", s.len());
}

fn encode_env_action_canon(act: &EnvAction, out: &mut String) {
    match act {
        EnvAction::ReturnBytes(bytes) => {
            let _ = write!(out, "rb:{}:", bytes.len());
            for b in bytes {
                let _ = write!(out, "{b:02x}");
            }
            out.push(',');
        }
        EnvAction::Unwind { message } => {
            out.push_str("uw:");
            encode_str_field(out, message);
            out.push(',');
        }
        EnvAction::Abort { reason } => {
            out.push_str("ab:");
            encode_str_field(out, reason);
            out.push(',');
        }
    }
}

fn encode_shrink_steps_canon(steps: &[ShrinkStep], out: &mut String) {
    let _ = write!(out, "{}:[", steps.len());
    for step in steps {
        match step {
            ShrinkStep::Alloc { handle, size, align, local_id } => {
                let _ = write!(out, "A({},{size},{align},{local_id});", handle.0);
            }
            ShrinkStep::Borrow { dst, src, mutable, local_id } => {
                let _ = write!(out, "B({},{},{mutable},{local_id});", dst.0, src.0);
            }
            ShrinkStep::SplitAt { left, right, src, mid, len, align } => {
                let _ = write!(out, "S({},{},{},{mid},{len},{align});", left.0, right.0, src.0);
            }
            ShrinkStep::UseHandle { handle, offset, len, align, local_id } => {
                let _ = write!(out, "U({},{offset},{len},{align},{local_id});", handle.0);
            }
            ShrinkStep::ArithImm { dst_local, op, imm } => {
                let _ = write!(out, "I({dst_local},{},{imm});", fuzz_arith_op_tag(*op));
            }
            ShrinkStep::HelperCall { dst_local, helper_id, block_id, bias, rhs_local } => {
                let _ = write!(out, "H({dst_local},{helper_id},{block_id},{bias},{rhs_local:?});");
            }
            ShrinkStep::BranchMix {
                block_id,
                cond_local,
                taken_then,
                dynamic_even_cond,
                then_steps,
                else_steps,
            } => {
                let _ = write!(out, "M({block_id},{cond_local},{taken_then},{dynamic_even_cond},");
                encode_shrink_steps_canon(then_steps, out);
                out.push(',');
                encode_shrink_steps_canon(else_steps, out);
                out.push_str(");");
            }
            ShrinkStep::BoundedLoop { block_id, iters, induction, body } => {
                let _ = write!(
                    out,
                    "L({block_id},{iters},{:?},",
                    induction.map(|ind| (ind.dst_local, ind.step_mul, ind.addend))
                );
                encode_shrink_steps_canon(body, out);
                out.push_str(");");
            }
            ShrinkStep::IfFalseDecoy { block_id, body } => {
                let _ = write!(out, "D({block_id},");
                encode_shrink_steps_canon(body, out);
                out.push_str(");");
            }
            ShrinkStep::DropGuardWrapper { local_id, body } => {
                let _ = write!(out, "G({local_id},");
                encode_shrink_steps_canon(body, out);
                out.push_str(");");
            }
            ShrinkStep::PaddedRoundTrip { local_id, tag_byte } => {
                let _ = write!(out, "P({local_id},{tag_byte});");
            }
            ShrinkStep::UnwindProbe { callee, dst_local, trigger_unwind, block_id } => {
                out.push_str("W(");
                encode_str_field(out, callee);
                let _ = write!(out, ",{dst_local},{trigger_unwind},{block_id});");
            }
            ShrinkStep::PairOffsetLen { offset, len, align, local_id } => {
                let _ = write!(out, "O({offset},{len},{align},{local_id});");
            }
            ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm } => {
                let _ = write!(out, "X({dst_local},{rhs_local},{xor_imm});");
            }
        }
    }
    out.push(']');
}

/// Compute the 12-hex-character SHA-256 hash of an alpha-renamed,
/// constant-erased [`FuzzProgram`] skeleton.
pub fn canonical_fuzz_program_skeleton_hash(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
) -> String {
    let mut case = ShrinkableCase::from_fuzz_program(prog, schedule).canonical_alpha_renamed();
    erase_shrinkable_constants(&mut case);
    let mut canon = canonical_shrinkable_case_key(&case);
    canon.push_str("|callees=[");
    for step in &prog.steps {
        if let FuzzStep::HelperCall { callee_idx, .. } = step {
            let _ = write!(canon, "fuzz_helper_{},", callee_idx % 3);
        }
    }
    canon.push(']');
    sha256_hex(canon.as_bytes())[..12].to_string()
}

/// Compute the 12-hex-character SHA-256 hash of an alpha-renamed,
/// constant-erased [`ShrinkableCase`] skeleton.
pub fn canonical_shrinkable_case_skeleton_hash(case: &ShrinkableCase) -> String {
    let mut c = case.canonical_alpha_renamed();
    erase_shrinkable_constants(&mut c);
    let canon = canonical_shrinkable_case_key(&c);
    sha256_hex(canon.as_bytes())[..12].to_string()
}

fn erase_shrinkable_constants(case: &mut ShrinkableCase) {
    case.name = "skel".to_string();
    for inp in &mut case.inputs {
        inp.value = 0;
        inp.align_hint = None;
    }
    erase_step_constants(&mut case.steps);
    for h in &mut case.helpers {
        h.multiplier = 0;
        h.addend = 0;
    }
    case.env_schedule.global.iter_mut().for_each(erase_action_constants);
    for acts in case.env_schedule.per_callee.values_mut() {
        acts.iter_mut().for_each(erase_action_constants);
    }
}

fn erase_action_constants(act: &mut EnvAction) {
    match act {
        EnvAction::ReturnBytes(b) => {
            *b = vec![0u8; b.len()];
        }
        EnvAction::Unwind { message } => {
            *message = "u".to_string();
        }
        EnvAction::Abort { reason } => {
            *reason = "a".to_string();
        }
    }
}

fn erase_step_constants(steps: &mut [ShrinkStep]) {
    for step in steps {
        match step {
            ShrinkStep::Alloc { size, .. } => {
                *size = 0;
            }
            ShrinkStep::Borrow { .. } => {}
            ShrinkStep::SplitAt { mid, len, .. } => {
                *mid = 0;
                *len = 0;
            }
            ShrinkStep::UseHandle { offset, len, .. } => {
                *offset = 0;
                *len = 0;
            }
            ShrinkStep::ArithImm { imm, .. } => {
                *imm = 0;
            }
            ShrinkStep::HelperCall { bias, .. } => {
                *bias = 0;
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                erase_step_constants(then_steps);
                erase_step_constants(else_steps);
            }
            ShrinkStep::BoundedLoop { iters, induction, body, .. } => {
                *iters = 0;
                if let Some(ind) = induction {
                    ind.step_mul = 0;
                    ind.addend = 0;
                }
                erase_step_constants(body);
            }
            ShrinkStep::IfFalseDecoy { body, .. } | ShrinkStep::DropGuardWrapper { body, .. } => {
                erase_step_constants(body);
            }
            ShrinkStep::PaddedRoundTrip { tag_byte, .. } => {
                *tag_byte = 0;
            }
            ShrinkStep::UnwindProbe { .. } => {}
            ShrinkStep::PairOffsetLen { offset, len, .. } => {
                *offset = 0;
                *len = 0;
            }
            ShrinkStep::XorLocalImm { xor_imm, .. } => {
                *xor_imm = 0;
            }
        }
    }
}

fn schedule_has_return_bytes_override(schedule: &EnvSchedule) -> bool {
    schedule
        .per_callee
        .values()
        .flatten()
        .chain(schedule.global.iter())
        .any(|act| matches!(act, crate::trace_observer::EnvAction::ReturnBytes(_)))
}

pub(crate) fn verdict_is_metamorphic_duality(verdict: &TraceVerdict) -> bool {
    matches!(
        verdict,
        TraceVerdict::UnsoundAccept { detail } | TraceVerdict::ToolError { detail, .. }
            if detail.starts_with("metamorphic_duality:")
                || detail.contains("source-inlined")
    )
}

pub(crate) fn pinned_metamorphic_relations(
    verdict: &TraceVerdict,
    sig: Option<&ShrinkFailureSignature>,
) -> Vec<String> {
    if let Some(s) = sig {
        if !s.metamorphic_relations.is_empty() {
            return s.metamorphic_relations.clone();
        }
        if s.mismatch_category == "rustc_o0_o2"
            || (s.mismatch_category == "spine_mismatch"
                && s.spine_relation.as_deref() == Some("rustc_o0_vs_o2"))
        {
            return vec!["called_rustc_o0_vs_o2".to_string()];
        }
    }
    match verdict {
        TraceVerdict::UnsoundAccept { detail } | TraceVerdict::ToolError { detail, .. }
            if verdict_is_metamorphic_duality(verdict) =>
        {
            extract_metamorphic_relations_from_detail(detail)
        }
        TraceVerdict::UnsoundAccept { detail }
            if detail.contains("rustc O0 vs O2")
                || detail.contains("rustc-O0 vs rustc-O2")
                || detail.contains("rustc_o0_vs_o2") =>
        {
            vec!["called_rustc_o0_vs_o2".to_string()]
        }
        _ => Vec::new(),
    }
}

/// Render a standalone, zero-external-crate Rust source reproducer
/// (`repro_<bundle_id>.rs`) directly compilable by `rustc` and `miri`,
/// preserving full observable-trace (`anneal_rt`) instrumentation,
/// `FuzzPaddedCarrier` raw-pointer caller-frame checks, scheduled-call actions,
/// unwind `DropGuard` behavior, and (when applicable) the
/// `metamorphic_inlined_twin` comparison harness.
pub fn render_standalone_fuzz_repro_rs(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
    artifact_id: &str,
) -> String {
    render_standalone_fuzz_repro_rs_for_relations(prog, schedule, artifact_id, false, &[])
}

/// Variant of [`render_standalone_fuzz_repro_rs`] allowing witness callers
/// that know the failure is a `metamorphic_duality` bug
/// (`force_metamorphic = true`) to retain the dual
/// `subject` + `subject_inlined` harness even when `schedule` includes helper
/// `ReturnBytes` actions.
pub fn render_standalone_fuzz_repro_rs_with_mode(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
    artifact_id: &str,
    force_metamorphic: bool,
) -> String {
    render_standalone_fuzz_repro_rs_for_relations(
        prog,
        schedule,
        artifact_id,
        force_metamorphic,
        &[],
    )
}

/// Variant of [`render_standalone_fuzz_repro_rs_with_mode`] preserving pinned
/// `metamorphic_relations` for cross-mode (`-O0` vs `-O2`) verification.
pub fn render_standalone_fuzz_repro_rs_for_relations(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
    artifact_id: &str,
    force_metamorphic: bool,
    pinned_relations: &[String],
) -> String {
    let mut case = prog.to_trace_test_case();
    case.env_schedule = resolve_effective_fuzz_schedule(prog, schedule);
    let use_metamorphic_harness = case.metamorphic_inlined_twin.is_some()
        && (force_metamorphic || !schedule_has_return_bytes_override(&case.env_schedule));
    let harness = if use_metamorphic_harness {
        crate::spec::render_standalone_metamorphic_rust_harness_with_relations(
            &case,
            pinned_relations,
        )
    } else {
        crate::spec::render_standalone_rust_harness_with_relations(&case, pinned_relations)
    };
    let mut out = String::with_capacity(harness.len() + 512);
    let _ = writeln!(out, "// Standalone Anneal itree-diff reproducer (id={artifact_id})");
    if !pinned_relations.is_empty() {
        let _ = writeln!(out, "// Pinned metamorphic relations: {}", pinned_relations.join(", "));
    }
    let _ = writeln!(
        out,
        "// Compile (O0): rustc --edition 2024 -C overflow-checks=no -C debug-assertions=no repro_{artifact_id}.rs -o repro_{artifact_id}"
    );
    let _ = writeln!(
        out,
        "// Compile (O2): rustc --edition 2024 -C opt-level=2 -C overflow-checks=no -C debug-assertions=no repro_{artifact_id}.rs -o repro_{artifact_id}_o2"
    );
    if pinned_relations
        .iter()
        .any(|r| r == "called_rustc_o0_vs_o2" || r == "inlined_rustc_o0_vs_o2")
    {
        let _ = writeln!(
            out,
            "// Compare (O0 vs O2): ./repro_{artifact_id} --compare-opt ./repro_{artifact_id}_o2"
        );
    }
    if pinned_relations.iter().any(|r| r.contains("miri")) {
        let _ = writeln!(
            out,
            "// Replay Miri relation via `cargo miri` (or `itree-diff --corpus-dir`)"
        );
    }
    if pinned_relations.iter().any(|r| r.contains("lean")) {
        let _ = writeln!(
            out,
            "// Replay Lean relation via sibling `program_{artifact_id}.mir.lean` + `./repro_{artifact_id} --anneal-meta-{{called,inlined}}` (or `itree-diff --corpus-dir`)"
        );
    }
    out.push_str("#![allow(dead_code, unused_variables, unused_mut, clippy::all)]\n");
    out.push_str(&harness);
    out.push_str("\npub use subject::*;\n");
    out
}

fn collect_shrink_handles_recursive(steps: &[ShrinkStep], out: &mut BTreeSet<HandleId>) {
    for step in steps {
        match step {
            ShrinkStep::Alloc { handle, .. } | ShrinkStep::UseHandle { handle, .. } => {
                out.insert(*handle);
            }
            ShrinkStep::Borrow { dst, src, .. } => {
                out.insert(*dst);
                out.insert(*src);
            }
            ShrinkStep::SplitAt { left, right, src, .. } => {
                out.insert(*left);
                out.insert(*right);
                out.insert(*src);
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                collect_shrink_handles_recursive(then_steps, out);
                collect_shrink_handles_recursive(else_steps, out);
            }
            ShrinkStep::BoundedLoop { body, .. }
            | ShrinkStep::IfFalseDecoy { body, .. }
            | ShrinkStep::DropGuardWrapper { body, .. } => {
                collect_shrink_handles_recursive(body, out);
            }
            _ => {}
        }
    }
}

fn collect_shrink_step_locals_recursive(steps: &[ShrinkStep], out: &mut BTreeSet<usize>) {
    for step in steps {
        match step {
            ShrinkStep::ArithImm { dst_local, .. } | ShrinkStep::UnwindProbe { dst_local, .. } => {
                out.insert(*dst_local);
            }
            ShrinkStep::HelperCall { dst_local, rhs_local, .. } => {
                out.insert(*dst_local);
                if let Some(rl) = rhs_local {
                    out.insert(*rl);
                }
            }
            ShrinkStep::PaddedRoundTrip { local_id, .. }
            | ShrinkStep::PairOffsetLen { local_id, .. } => {
                out.insert(*local_id);
            }
            ShrinkStep::XorLocalImm { dst_local, rhs_local, .. } => {
                out.insert(*dst_local);
                out.insert(*rhs_local);
            }
            ShrinkStep::BranchMix { cond_local, then_steps, else_steps, .. } => {
                out.insert(*cond_local);
                collect_shrink_step_locals_recursive(then_steps, out);
                collect_shrink_step_locals_recursive(else_steps, out);
            }
            ShrinkStep::DropGuardWrapper { local_id, body } => {
                out.insert(*local_id);
                collect_shrink_step_locals_recursive(body, out);
            }
            ShrinkStep::BoundedLoop { induction, body, .. } => {
                if let Some(ind) = induction {
                    out.insert(ind.dst_local);
                }
                collect_shrink_step_locals_recursive(body, out);
            }
            ShrinkStep::IfFalseDecoy { body, .. } => {
                collect_shrink_step_locals_recursive(body, out);
            }
            _ => {}
        }
    }
}

fn shrink_steps_have_observable_calls(steps: &[ShrinkStep]) -> bool {
    steps.iter().any(|s| match s {
        ShrinkStep::HelperCall { .. } | ShrinkStep::UnwindProbe { .. } => true,
        ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
            shrink_steps_have_observable_calls(then_steps)
                || shrink_steps_have_observable_calls(else_steps)
        }
        ShrinkStep::BoundedLoop { body, .. }
        | ShrinkStep::IfFalseDecoy { body, .. }
        | ShrinkStep::DropGuardWrapper { body, .. } => shrink_steps_have_observable_calls(body),
        _ => false,
    })
}

struct ShrinkRenderCtx<'a> {
    local_widths: &'a BTreeMap<usize, IntKind>,
    default_width: IntKind,
    emit_trace_rt: bool,
    per_callee_keys: BTreeSet<String>,
    helper_call_widths: &'a BTreeMap<usize, BTreeSet<IntKind>>,
    unwind_call_widths: &'a BTreeMap<String, BTreeSet<IntKind>>,
    watched_drop_cells: BTreeMap<usize, Vec<String>>,
}

impl ShrinkRenderCtx<'_> {
    fn local_kind(&self, local_id: usize) -> IntKind {
        self.local_widths.get(&local_id).copied().unwrap_or(self.default_width)
    }

    fn local_rust_ty(&self, local_id: usize) -> &'static str {
        self.local_kind(local_id).rust_name()
    }

    fn helper_callee_name(&self, helper_id: usize, dst_width: IntKind) -> String {
        let cand_a = format!("fuzz_helper_{helper_id}");
        let base =
            if self.per_callee_keys.contains(&cand_a) { cand_a } else { format!("h{helper_id}") };
        if self.helper_call_widths.get(&helper_id).is_some_and(|s| s.len() > 1) {
            format!("{base}_{}", dst_width.rust_name())
        } else {
            base
        }
    }

    fn unwind_callee_name(&self, callee: &str, dst_width: IntKind) -> String {
        if self.unwind_call_widths.get(callee).is_some_and(|s| s.len() > 1) {
            format!("{callee}_{}", dst_width.rust_name())
        } else {
            callee.to_string()
        }
    }

    fn push_watch_cell(&mut self, local_id: usize, cell_var: String) {
        self.watched_drop_cells.entry(local_id).or_default().push(cell_var);
    }

    fn pop_watch_cell(&mut self, local_id: usize) {
        if let Some(stack) = self.watched_drop_cells.get_mut(&local_id) {
            stack.pop();
        }
    }

    fn emit_watch_sync(&self, local_id: usize, indent: &str, out: &mut String) {
        if let Some(cells) = self.watched_drop_cells.get(&local_id) {
            for cell in cells {
                let _ = writeln!(out, "{indent}{cell}.set(l{local_id});");
            }
        }
    }
}

/// Render a standalone, zero-external-crate Rust source reproducer for a
/// shrunk [`ShrinkableCase`], backing handles with real heap allocations,
/// `slice::from_raw_parts{,_mut}` reborrows/splits, `DropGuardWrapper` RAII
/// cleanup guards, `PairOffsetLen` slice/alignment reads, scheduled calls
/// (`anneal_rt`), and alignment-checked `read_volatile` memory accesses.
pub fn render_standalone_shrinkable_repro_rs(case: &ShrinkableCase, artifact_id: &str) -> String {
    render_standalone_shrinkable_repro_rs_for_signature(case, artifact_id, None)
}

/// Variant of [`render_standalone_shrinkable_repro_rs`] accepting an optional
/// [`ShrinkFailureSignature`] so promoted witnesses always emit structured
/// `anneal_rt` trace output and `rustc_o0_o2` failures enforce cross-mode
/// `--compare-opt` / sibling `*_o2` parity checking.
pub fn render_standalone_shrinkable_repro_rs_for_signature(
    case: &ShrinkableCase,
    artifact_id: &str,
    signature: Option<&ShrinkFailureSignature>,
) -> String {
    let is_rustc_o0_o2 = signature.is_some_and(|s| {
        s.mismatch_category == "rustc_o0_o2"
            || (s.mismatch_category == "spine_mismatch"
                && s.spine_relation.as_deref() == Some("rustc_o0_vs_o2"))
    });
    let mut out = String::new();
    let _ = writeln!(out, "// Standalone Anneal ShrinkableCase reproducer (id={artifact_id})");
    let _ = writeln!(
        out,
        "// Compile (O0): rustc --edition 2024 -C overflow-checks=no -C debug-assertions=no repro_{artifact_id}.rs -o repro_{artifact_id}"
    );
    let _ = writeln!(
        out,
        "// Compile (O2): rustc --edition 2024 -C opt-level=2 -C overflow-checks=no -C debug-assertions=no repro_{artifact_id}.rs -o repro_{artifact_id}_o2"
    );
    if is_rustc_o0_o2 {
        let _ = writeln!(
            out,
            "// Compare (O0 vs O2): ./repro_{artifact_id} --compare-opt ./repro_{artifact_id}_o2"
        );
    }
    out.push_str(
        "#![allow(dead_code, unused_variables, unused_mut, unused_unsafe, clippy::all)]\n",
    );
    let has_schedule = !case.env_schedule.is_empty();
    let emit_trace_rt =
        has_schedule || shrink_steps_have_observable_calls(&case.steps) || signature.is_some();
    if emit_trace_rt {
        out.push_str(crate::trace_observer::render_embedded_trace_prelude());
        out.push('\n');
    } else {
        out.push('\n');
    }
    out.push_str(
        "#[derive(Clone, Copy)]\n\
         struct ReproHandle {\n\
             ptr: *mut u8,\n\
             len: usize,\n\
             align: usize,\n\
         }\n\
         impl Default for ReproHandle {\n\
             fn default() -> Self {\n\
                 Self { ptr: core::ptr::NonNull::<u8>::dangling().as_ptr(), len: 0, align: 1 }\n\
             }\n\
         }\n\
         struct ReproPool(Vec<(*mut u8, std::alloc::Layout)>);\n\
         impl ReproPool {\n\
             fn alloc(&mut self, size: usize, align: usize) -> ReproHandle {\n\
                 let align_p2 = align.max(1).next_power_of_two();\n\
                 if size == 0 {\n\
                     return ReproHandle {\n\
                         ptr: core::ptr::without_provenance_mut(align_p2),\n\
                         len: 0,\n\
                         align: align_p2,\n\
                     };\n\
                 }\n\
                 let layout = std::alloc::Layout::from_size_align(size, align_p2)\n\
                     .expect(\"valid repro alloc layout\");\n\
                 let ptr = unsafe { std::alloc::alloc_zeroed(layout) };\n\
                 assert!(!ptr.is_null(), \"repro allocation failed\");\n\
                 self.0.push((ptr, layout));\n\
                 ReproHandle { ptr, len: size, align: align_p2 }\n\
             }\n\
         }\n\
         impl Drop for ReproPool {\n\
             fn drop(&mut self) {\n\
                 for (ptr, layout) in self.0.drain(..) {\n\
                     unsafe { std::alloc::dealloc(ptr, layout); }\n\
                 }\n\
             }\n\
         }\n\
         #[repr(align(2))] struct ZstAlign2([u8; 0]);\n\
         #[repr(align(4))] struct ZstAlign4([u8; 0]);\n\
         #[repr(align(8))] struct ZstAlign8([u8; 0]);\n\
         #[repr(align(16))] struct ZstAlign16([u8; 0]);\n\
         #[repr(align(32))] struct ZstAlign32([u8; 0]);\n\
         #[repr(align(64))] struct ZstAlign64([u8; 0]);\n\
         #[repr(C)] #[derive(Clone, Copy)] struct ReproPadded { tag: u8, payload: u32 }\n\n",
    );
    if !case.struct_fields.is_empty() {
        out.push_str("#[repr(C)]\n#[derive(Clone, Copy)]\nstruct ReproRetainedStruct {\n");
        for (idx, kind) in case.struct_fields.iter().enumerate() {
            let _ = writeln!(out, "    f{idx}: {},", kind.rust_name());
        }
        out.push_str("}\n\n");
    }
    for h in &case.helpers {
        let body_expr = match h.op {
            ShrinkHelperOp::AffineMulAdd => format!(
                "a.wrapping_mul({}u64).wrapping_add(b).wrapping_add({}u64)",
                h.multiplier, h.addend
            ),
            ShrinkHelperOp::BitXorAdd => format!("(a ^ b).wrapping_add({}u64)", h.addend),
            ShrinkHelperOp::AbsDiffBranch => format!(
                "if a >= b {{ a.wrapping_sub(b).wrapping_add({}u64) }} else {{ b.wrapping_sub(a).wrapping_add({}u64) }}",
                h.multiplier, h.addend
            ),
        };
        let _ = writeln!(
            out,
            "#[inline(never)]\npub fn h{}(a: u64, b: u64) -> u64 {{\n    {body_expr}\n}}\n",
            h.helper_id
        );
    }

    let mut local_widths: BTreeMap<usize, IntKind> = BTreeMap::new();
    for inp in &case.inputs {
        local_widths.insert(inp.local_id, inp.width);
    }
    let mut referenced_locals = BTreeSet::new();
    collect_shrink_step_locals_recursive(&case.steps, &mut referenced_locals);
    referenced_locals.insert(case.return_local);
    let mut handles = BTreeSet::new();
    collect_shrink_handles_recursive(&case.steps, &mut handles);

    if is_rustc_o0_o2 {
        out.push_str("fn run_shrinkable_subject() {\n    anneal_rt::reset_trace_observer();\n    anneal_rt::reset_schedules();\n");
    } else {
        out.push_str("fn main() {\n");
    }
    let indent = if emit_trace_rt {
        crate::spec::push_env_schedule_setup(&mut out, &case.env_schedule);
        for inp in &case.inputs {
            let lit = inp.width.format_rust_literal(inp.value);
            let _ = writeln!(
                out,
                "    let _entry_{}: {} = {lit};\n\
                 \x20   anneal_rt::record_boundary_slot(anneal_rt::capture_value_bytes(&_entry_{}));",
                inp.local_id,
                inp.width.rust_name(),
                inp.local_id
            );
        }
        out.push_str(
            "    anneal_rt::emit_pre_entry_slots();\n\
             \x20   let run_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {\n",
        );
        "        "
    } else {
        "    "
    };

    let _ = writeln!(out, "{indent}let mut _repro_pool = ReproPool(Vec::new());");
    for inp in &case.inputs {
        let lit = inp.width.format_rust_literal(inp.value);
        let _ =
            writeln!(out, "{indent}let mut l{}: {} = {lit};", inp.local_id, inp.width.rust_name());
    }
    for local_id in referenced_locals {
        if let std::collections::btree_map::Entry::Vacant(slot) = local_widths.entry(local_id) {
            let width = case.scalar_width;
            slot.insert(width);
            let lit = width.format_rust_literal(0);
            let _ = writeln!(out, "{indent}let mut l{local_id}: {} = {lit};", width.rust_name());
        }
    }
    let mut helper_call_widths: BTreeMap<usize, BTreeSet<IntKind>> = BTreeMap::new();
    collect_helper_call_widths(
        &case.steps,
        &local_widths,
        case.scalar_width,
        &mut helper_call_widths,
    );
    let mut unwind_call_widths: BTreeMap<String, BTreeSet<IntKind>> = BTreeMap::new();
    collect_unwind_call_widths(
        &case.steps,
        &local_widths,
        case.scalar_width,
        &mut unwind_call_widths,
    );
    for h in handles {
        let _ = writeln!(out, "{indent}let mut hnd_{} = ReproHandle::default();", h.0);
    }

    let mut ctx = ShrinkRenderCtx {
        local_widths: &local_widths,
        default_width: case.scalar_width,
        emit_trace_rt,
        per_callee_keys: case.env_schedule.per_callee.keys().cloned().collect(),
        helper_call_widths: &helper_call_widths,
        unwind_call_widths: &unwind_call_widths,
        watched_drop_cells: BTreeMap::new(),
    };
    let mut next_var = 0usize;
    if !case.struct_fields.is_empty() {
        let ret_ty = ctx.local_rust_ty(case.return_local);
        let ret_local = case.return_local;
        let field_inits: Vec<String> = case
            .struct_fields
            .iter()
            .enumerate()
            .map(|(idx, kind)| format!("f{idx}: {}", kind.format_rust_literal(0)))
            .collect();
        let _ = writeln!(
            out,
            "{indent}let _ret_struct = std::hint::black_box(ReproRetainedStruct {{ {} }});\n\
             {indent}let _ret_struct_ptr = core::ptr::addr_of!(_ret_struct).cast::<u8>();\n\
             {indent}let _ = std::hint::black_box((\n\
             {indent}    core::mem::size_of::<ReproRetainedStruct>(),\n\
             {indent}    core::mem::align_of::<ReproRetainedStruct>(),\n\
             {indent}));",
            field_inits.join(", ")
        );
        for (idx, kind) in case.struct_fields.iter().enumerate() {
            let fty = kind.rust_name();
            let _ = writeln!(
                out,
                "{indent}let _ret_f{idx} = unsafe {{\n\
                 {indent}    core::ptr::read_volatile(\n\
                 {indent}        _ret_struct_ptr.add(core::mem::offset_of!(ReproRetainedStruct, f{idx})) as *const {fty}\n\
                 {indent}    )\n\
                 {indent}}};\n\
                 {indent}l{ret_local} = l{ret_local}.wrapping_add((_ret_f{idx} as u128) as {ret_ty});"
            );
        }
    }
    if let Some(slice_len) = case.slice_len {
        let slice_align = case.slice_align.max(1);
        let eff_align = slice_align.next_power_of_two();
        let ret_ty = ctx.local_rust_ty(case.return_local);
        let ret_local = case.return_local;
        let _ = writeln!(
            out,
            "{indent}let _top_slice_h = _repro_pool.alloc({slice_len}usize, {eff_align}usize);\n\
             {indent}let _top_slice_ptr = _top_slice_h.ptr;\n\
             {indent}let _slice_top: &[u8] = unsafe {{ std::slice::from_raw_parts(_top_slice_ptr, {slice_len}usize) }};"
        );
        emit_zst_and_typed_align_reads_named(
            indent,
            "_top",
            "_top_slice_ptr",
            slice_len,
            slice_align,
            &mut out,
        );
        let _ = writeln!(
            out,
            "{indent}let _top_slice_fold: u8 = _slice_top.first().copied().unwrap_or(0);\n\
             {indent}let _ = std::hint::black_box((_top_slice_ptr, _slice_top.len(), {slice_align}usize, _top_slice_h.align));\n\
             {indent}l{ret_local} = l{ret_local}.wrapping_add((_top_slice_fold as u128) as {ret_ty});"
        );
    }
    render_shrink_steps_rust(&case.steps, &mut ctx, &mut next_var, indent, &mut out);

    if emit_trace_rt {
        let ret_kind = local_widths.get(&case.return_local).copied().unwrap_or(case.scalar_width);
        let ret_expr = format!("l{}", case.return_local);
        let _ = writeln!(out, "{indent}{ret_expr}\n    }}));");

        let shape = crate::spec::ReturnShape::Scalar { kind: ret_kind };
        let ret_bytes_expr = shape.render_rust_ret_bytes_expr("ret");
        let ret_json_expr = shape.render_rust_to_json_expr("ret");
        let _ = writeln!(
            out,
            "    let (outcome_kind, ret_json, detail): (&str, String, String) = match run_res {{\n\
             \x20       Ok(ret) => {{\n\
             \x20           let _ = std::hint::black_box(&ret);\n\
             \x20           anneal_rt::record_post_return_slot({ret_bytes_expr});\n\
             \x20           (\"returned\", {ret_json_expr}, String::new())\n\
             \x20       }}\n\
             \x20       Err(payload) => {{\n\
             \x20           if let Some(sched_err) = payload.downcast_ref::<anneal_rt::ScheduleDecodeFailed>() {{\n\
             \x20               (\"fault_ub\", \"null\".to_string(), sched_err.0.clone())\n\
             \x20           }} else {{\n\
             \x20               anneal_rt::record_post_unwind_slot();\n\
             \x20               let msg = if let Some(s) = payload.downcast_ref::<&str>() {{\n\
             \x20                   (*s).to_string()\n\
             \x20               }} else if let Some(s) = payload.downcast_ref::<String>() {{\n\
             \x20                   s.clone()\n\
             \x20               }} else {{\n\
             \x20                   \"panic\".to_string()\n\
             \x20               }};\n\
             \x20               (\"unwound\", \"null\".to_string(), msg)\n\
             \x20           }}\n\
             \x20       }}\n\
             \x20   }};\n\
             \x20   let rem = anneal_rt::remaining_schedule_count();\n\
             \x20   if outcome_kind != \"fault_ub\" && rem > 0 {{\n\
             \x20       let rem_msg = format!(\"{{rem}} scheduled EnvAction(s) remained unconsumed at termination\");\n\
             \x20       anneal_rt::finish_json(\"unconsumed_schedule\", \"null\", &rem_msg);\n\
             \x20   }} else {{\n\
             \x20       if outcome_kind == \"fault_ub\" {{\n\
             \x20           anneal_rt::reset_schedules();\n\
             \x20       }}\n\
             \x20       anneal_rt::finish_json(outcome_kind, &ret_json, &detail);\n\
             \x20   }}\n}}"
        );
    } else {
        let ret_expr = format!("l{}", case.return_local);
        let _ = writeln!(out, "    let _ = std::hint::black_box({ret_expr});\n}}");
    }
    if is_rustc_o0_o2 {
        out.push_str(&crate::spec::render_single_opt_peer_compare_fns(
            "run_shrinkable_child_once",
            "discover_shrinkable_sibling_opt_peer",
            "compare_shrinkable_opt_peer",
            "run_shrinkable_subject",
            "rustc_o0_o2 ShrinkableCase",
        ));
    }
    out
}

fn emit_zst_and_typed_align_reads(
    indent: &str,
    vid: usize,
    ptr_var: &str,
    len: usize,
    align: usize,
    out: &mut String,
) {
    let suffix = format!("_{vid}");
    emit_zst_and_typed_align_reads_named(indent, &suffix, ptr_var, len, align, out);
}

fn emit_zst_and_typed_align_reads_named(
    indent: &str,
    slice_suffix: &str,
    ptr_var: &str,
    len: usize,
    align: usize,
    out: &mut String,
) {
    let typed_ty = if align >= 16 && len >= 16 {
        Some("u128")
    } else if align >= 8 && len >= 8 {
        Some("u64")
    } else if align >= 4 && len >= 4 {
        Some("u32")
    } else if align >= 2 && len >= 2 {
        Some("u16")
    } else {
        None
    };
    if let Some(ty) = typed_ty {
        let _ = writeln!(
            out,
            "{indent}std::hint::black_box(unsafe {{ core::ptr::read_volatile({ptr_var} as *const {ty}) }});"
        );
    }
    let zst_ty = match align {
        64.. => Some("ZstAlign64"),
        32.. => Some("ZstAlign32"),
        16.. => Some("ZstAlign16"),
        8.. => Some("ZstAlign8"),
        4.. => Some("ZstAlign4"),
        2.. => Some("ZstAlign2"),
        _ => None,
    };
    if let Some(zst) = zst_ty {
        let _ = writeln!(
            out,
            "{indent}std::hint::black_box(unsafe {{ core::ptr::read_volatile({ptr_var} as *const {zst}) }});"
        );
    }
    if len > 0 {
        let _ = writeln!(
            out,
            "{indent}for _bi{slice_suffix} in 0.._slice{slice_suffix}.len() {{\n\
             {indent}    std::hint::black_box(unsafe {{ core::ptr::read_volatile(_slice{slice_suffix}.as_ptr().add(_bi{slice_suffix})) }});\n\
             {indent}}}"
        );
    }
}

fn render_shrink_steps_rust(
    steps: &[ShrinkStep],
    ctx: &mut ShrinkRenderCtx<'_>,
    next_var: &mut usize,
    indent: &str,
    out: &mut String,
) {
    for step in steps {
        let vid = *next_var;
        *next_var += 1;
        match step {
            ShrinkStep::Alloc { handle, size, align, .. } => {
                let _ = writeln!(
                    out,
                    "{indent}hnd_{} = _repro_pool.alloc({size}usize, {align}usize);",
                    handle.0
                );
            }
            ShrinkStep::Borrow { dst, src, mutable, .. } => {
                if *mutable {
                    let _ = writeln!(
                        out,
                        "{indent}let _reborrow_{vid}: &mut [u8] = unsafe {{ std::slice::from_raw_parts_mut(hnd_{}.ptr, hnd_{}.len) }};\n\
                         {indent}hnd_{} = ReproHandle {{ ptr: _reborrow_{vid}.as_mut_ptr(), len: _reborrow_{vid}.len(), align: hnd_{}.align }};",
                        src.0, src.0, dst.0, src.0
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "{indent}let _reborrow_{vid}: &[u8] = unsafe {{ std::slice::from_raw_parts(hnd_{}.ptr, hnd_{}.len) }};\n\
                         {indent}hnd_{} = ReproHandle {{ ptr: _reborrow_{vid}.as_ptr() as *mut u8, len: _reborrow_{vid}.len(), align: hnd_{}.align }};",
                        src.0, src.0, dst.0, src.0
                    );
                }
            }
            ShrinkStep::SplitAt { left, right, src, mid, len, align } => {
                let eff_align = (*align).max(1);
                let _ = writeln!(
                    out,
                    "{indent}let _split_src_{vid}: &[u8] = unsafe {{ std::slice::from_raw_parts(hnd_{}.ptr, {len}usize) }};\n\
                     {indent}let (_split_l_{vid}, _split_r_{vid}) = unsafe {{ (_split_src_{vid}.get_unchecked(..({mid}usize)), _split_src_{vid}.get_unchecked(({mid}usize)..)) }};\n\
                     {indent}hnd_{} = ReproHandle {{ ptr: _split_l_{vid}.as_ptr() as *mut u8, len: _split_l_{vid}.len(), align: {eff_align}usize }};\n\
                     {indent}hnd_{} = ReproHandle {{ ptr: _split_r_{vid}.as_ptr() as *mut u8, len: _split_r_{vid}.len(), align: {eff_align}usize }};",
                    src.0, left.0, right.0
                );
            }
            ShrinkStep::UseHandle { handle, offset, len, align, .. } => {
                let ptr_var = format!("_ptr_{vid}");
                let _ = writeln!(
                    out,
                    "{indent}let {ptr_var} = unsafe {{ hnd_{}.ptr.add({offset}usize) }};\n\
                     {indent}let _slice_{vid}: &[u8] = unsafe {{ std::slice::from_raw_parts({ptr_var}, {len}usize) }};",
                    handle.0
                );
                emit_zst_and_typed_align_reads(
                    indent,
                    vid,
                    &ptr_var,
                    *len as usize,
                    *align as usize,
                    out,
                );
            }
            ShrinkStep::ArithImm { dst_local, op, imm } => {
                let ty = ctx.local_rust_ty(*dst_local);
                let lhs = format!("l{dst_local}");
                let rhs = format!("({imm}u128 as {ty})");
                let expr = match op {
                    FuzzArithOp::Add => format!("{lhs}.wrapping_add({rhs})"),
                    FuzzArithOp::Sub => format!("{lhs}.wrapping_sub({rhs})"),
                    FuzzArithOp::Xor => format!("{lhs} ^ {rhs}"),
                    FuzzArithOp::BitOr => format!("{lhs} | {rhs}"),
                    FuzzArithOp::BitAndMask => {
                        format!("({lhs} & (0xFFFFu128 as {ty})).wrapping_add({rhs})")
                    }
                };
                let _ = writeln!(out, "{indent}{lhs} = {expr};");
                ctx.emit_watch_sync(*dst_local, indent, out);
            }
            ShrinkStep::HelperCall { dst_local, helper_id, bias, rhs_local, .. } => {
                let width = ctx.local_widths.get(dst_local).copied().unwrap_or(ctx.default_width);
                let ty = width.rust_name();
                let rhs_expr = match rhs_local {
                    Some(rl) => {
                        let rty = ctx.local_rust_ty(*rl);
                        format!("l{rl}.wrapping_add({bias}u128 as {rty}) as u64")
                    }
                    None => format!("{bias}u64"),
                };
                if ctx.emit_trace_rt {
                    let callee = ctx.helper_callee_name(*helper_id, width);
                    let _ = writeln!(
                        out,
                        "{indent}let _hc_a_{vid}: u64 = l{dst_local} as u64;\n\
                         {indent}let _hc_b_{vid}: u64 = {rhs_expr};\n\
                         {indent}l{dst_local} = anneal_rt::handle_scheduled_call(\n\
                         {indent}    {callee:?},\n\
                         {indent}    vec![\n\
                         {indent}        anneal_rt::capture_value_bytes(&_hc_a_{vid}),\n\
                         {indent}        anneal_rt::capture_value_bytes(&_hc_b_{vid}),\n\
                         {indent}    ],\n\
                         {indent}    vec![format!(\"{{_hc_a_{vid}}}\"), format!(\"{{_hc_b_{vid}}}\")],\n\
                         {indent}    || -> {ty} {{ h{helper_id}(_hc_a_{vid}, _hc_b_{vid}) as {ty} }},\n\
                         {indent});"
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "{indent}l{dst_local} = h{helper_id}(l{dst_local} as u64, {rhs_expr}) as {ty};"
                    );
                }
                ctx.emit_watch_sync(*dst_local, indent, out);
            }
            ShrinkStep::BranchMix {
                cond_local,
                taken_then,
                dynamic_even_cond,
                then_steps,
                else_steps,
                ..
            } => {
                let inner_indent = format!("{indent}    ");
                let cond_expr = if *dynamic_even_cond {
                    let cty = ctx.local_rust_ty(*cond_local);
                    format!("(l{cond_local} & (1u128 as {cty})) == (0u128 as {cty})")
                } else {
                    taken_then.to_string()
                };
                let _ = writeln!(out, "{indent}if {cond_expr} {{");
                render_shrink_steps_rust(then_steps, ctx, next_var, &inner_indent, out);
                let _ = writeln!(out, "{indent}}} else {{");
                render_shrink_steps_rust(else_steps, ctx, next_var, &inner_indent, out);
                let _ = writeln!(out, "{indent}}}");
            }
            ShrinkStep::BoundedLoop { iters, induction, body, .. } => {
                let inner_indent = format!("{indent}    ");
                let _ = writeln!(out, "{indent}for _iter_{vid} in 0..{iters}u32 {{");
                if let Some(ind) = induction {
                    let dst_ty = ctx.local_rust_ty(ind.dst_local);
                    let _ = writeln!(
                        out,
                        "{inner_indent}l{dst} = l{dst}.wrapping_add(((_iter_{vid} as u128 as {dst_ty}).wrapping_mul({step_mul}u128 as {dst_ty})).wrapping_add({addend}u128 as {dst_ty}));",
                        dst = ind.dst_local,
                        step_mul = ind.step_mul,
                        addend = ind.addend,
                    );
                    ctx.emit_watch_sync(ind.dst_local, &inner_indent, out);
                }
                render_shrink_steps_rust(body, ctx, next_var, &inner_indent, out);
                let _ = writeln!(out, "{indent}}}");
            }
            ShrinkStep::IfFalseDecoy { body, .. } => {
                let inner_indent = format!("{indent}    ");
                let _ = writeln!(out, "{indent}if false {{");
                render_shrink_steps_rust(body, ctx, next_var, &inner_indent, out);
                let _ = writeln!(out, "{indent}}}");
            }
            ShrinkStep::DropGuardWrapper { local_id, body } => {
                let ty = ctx.local_rust_ty(*local_id);
                let cell_var = format!("_drop_cell_{vid}");
                let inner_indent = format!("{indent}    ");
                let _ = writeln!(
                    out,
                    "{indent}{{\n\
                     {inner_indent}let {cell_var} = core::cell::Cell::new(l{local_id});\n\
                     {inner_indent}struct ReproDropGuard_{vid}<'a>({ty}, &'a core::cell::Cell<{ty}>);\n\
                     {inner_indent}impl Drop for ReproDropGuard_{vid}<'_> {{\n\
                     {inner_indent}    fn drop(&mut self) {{\n\
                     {inner_indent}        let observed = self.1.get();\n\
                     {inner_indent}        let _ok = self.0 == observed;\n\
                     {inner_indent}        let _ = std::hint::black_box((self.0, observed, _ok));\n\
                     {inner_indent}    }}\n\
                     {inner_indent}}}\n\
                     {inner_indent}let _drop_guard_{vid} = ReproDropGuard_{vid}(l{local_id}, &{cell_var});"
                );
                ctx.push_watch_cell(*local_id, cell_var.clone());
                render_shrink_steps_rust(body, ctx, next_var, &inner_indent, out);
                ctx.pop_watch_cell(*local_id);
                let _ = writeln!(out, "{inner_indent}{cell_var}.set(l{local_id});\n{indent}}}");
            }
            ShrinkStep::PaddedRoundTrip { local_id, tag_byte } => {
                let ty = ctx.local_rust_ty(*local_id);
                let _ = writeln!(
                    out,
                    "{indent}let _pad_src_{vid} = std::hint::black_box(ReproPadded {{ \
                     tag: {tag_byte}u8, payload: (l{local_id} as u32) ^ 0xA5A5u32 }});\n\
                     {indent}let _pad_ptr_{vid} = core::ptr::addr_of!(_pad_src_{vid}).cast::<u8>();\n\
                     {indent}let _pad_tag_{vid} = unsafe {{ \
                     core::ptr::read_volatile(_pad_ptr_{vid}.add(core::mem::offset_of!(ReproPadded, tag))) \
                     }};\n\
                     {indent}let _pad_pay_{vid} = unsafe {{ \
                     core::ptr::read_volatile(_pad_ptr_{vid}.add(core::mem::offset_of!(ReproPadded, payload)) \
                     as *const u32) }};\n\
                     {indent}let _pad_rt_{vid} = std::hint::black_box(ReproPadded {{ \
                     tag: _pad_tag_{vid}, payload: _pad_pay_{vid} }});\n\
                     {indent}l{local_id} = l{local_id}.wrapping_add((_pad_rt_{vid}.tag as u128) as {ty});"
                );
                ctx.emit_watch_sync(*local_id, indent, out);
            }
            ShrinkStep::UnwindProbe { callee, dst_local, trigger_unwind, .. } => {
                let width = ctx.local_kind(*dst_local);
                let ty = width.rust_name();
                if ctx.emit_trace_rt {
                    let eff_callee = ctx.unwind_callee_name(callee, width);
                    let trig = if *trigger_unwind { 1u32 } else { 0u32 };
                    let _ = writeln!(
                        out,
                        "{indent}let _unw_v_{vid}: {ty} = l{dst_local};\n\
                         {indent}let _unw_trig_{vid}: u32 = {trig}u32;\n\
                         {indent}l{dst_local} = anneal_rt::handle_scheduled_call(\n\
                         {indent}    {eff_callee:?},\n\
                         {indent}    vec![\n\
                         {indent}        anneal_rt::capture_value_bytes(&_unw_v_{vid}),\n\
                         {indent}        anneal_rt::capture_value_bytes(&_unw_trig_{vid}),\n\
                         {indent}    ],\n\
                         {indent}    vec![format!(\"{{_unw_v_{vid}}}\"), format!(\"{{_unw_trig_{vid}}}\")],\n\
                         {indent}    || -> {ty} {{\n\
                         {indent}        if _unw_trig_{vid} != 0 {{ panic!(\"u\"); }}\n\
                         {indent}        _unw_v_{vid}.wrapping_add(1u128 as {ty})\n\
                         {indent}    }},\n\
                         {indent});"
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "{indent}if {trigger_unwind} {{ panic!(\"u\"); }}\n\
                         {indent}l{dst_local} = l{dst_local}.wrapping_add(1u128 as {ty});"
                    );
                }
                ctx.emit_watch_sync(*dst_local, indent, out);
            }
            ShrinkStep::PairOffsetLen { offset, len, align, local_id } => {
                let ty = ctx.local_rust_ty(*local_id);
                let eff_align = (*align).max(1) as usize;
                let pair_ptr = format!("_pair_ptr_{vid}");
                let _ = writeln!(
                    out,
                    "{indent}let _pair_total_{vid} = ({offset}usize).saturating_add({len}usize).max(({offset}usize).saturating_add(1));\n\
                     {indent}let _pair_h_{vid} = _repro_pool.alloc(_pair_total_{vid}, {eff_align}usize);\n\
                     {indent}let {pair_ptr} = unsafe {{ _pair_h_{vid}.ptr.add({offset}usize) }};\n\
                     {indent}let _slice_{vid}: &[u8] = unsafe {{ std::slice::from_raw_parts({pair_ptr}, {len}usize) }};"
                );
                emit_zst_and_typed_align_reads(
                    indent,
                    vid,
                    &pair_ptr,
                    *len as usize,
                    eff_align,
                    out,
                );
                let _ = writeln!(
                    out,
                    "{indent}let _pair_fold_{vid}: u8 = _slice_{vid}.first().copied().unwrap_or(0);\n\
                     {indent}l{local_id} = l{local_id}.wrapping_add((_pair_fold_{vid} as u128) as {ty});"
                );
                ctx.emit_watch_sync(*local_id, indent, out);
            }
            ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm } => {
                let dst_kind = ctx.local_kind(*dst_local);
                let rhs_kind = ctx.local_kind(*rhs_local);
                let dty = dst_kind.rust_name();
                let rhs_expr = if rhs_kind == dst_kind {
                    format!("l{rhs_local}")
                } else {
                    format!("(l{rhs_local} as {dty})")
                };
                let _ = writeln!(
                    out,
                    "{indent}let _xor_rhs_{vid}: {dty} = {rhs_expr} ^ ({xor_imm}u128 as {dty});\n\
                     {indent}l{dst_local} ^= _xor_rhs_{vid};"
                );
                ctx.emit_watch_sync(*dst_local, indent, out);
            }
        }
    }
}

fn encode_env_schedule_json(sched: &EnvSchedule) -> String {
    serde_json::to_string(sched).unwrap_or_else(|_| "{\"per_callee\":{},\"global\":[]}".to_string())
}

/// Emit a standalone `Trusted.MirAst.Program` Lean 4 bundle
/// (`program_<skel_hash>.mir.lean`).
pub fn render_standalone_mir_lean(
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
    skel_hash: &str,
) -> String {
    let case = prog.to_trace_test_case();
    let caller_body = match &case.lean_program_spec {
        crate::spec::LeanProgramSpec::MultiCallWithCapturedCallees { caller_lean_body, .. } => {
            caller_lean_body.clone()
        }
        crate::spec::LeanProgramSpec::SyntheticMirAst { program_lean_expr, .. } => {
            return format!(
                "import Trusted.MirAst\nimport Trusted.MirSemantics\n\n\
                 -- SkelHash: {skel_hash}\n\
                 def reproProgram : Trusted.MirAst.Program := {program_lean_expr}\n\
                 #check reproProgram\n"
            );
        }
        crate::spec::LeanProgramSpec::CapturedRust { .. } => {
            "{ argumentCount := 0, locals := [.unit], basicBlocks := [{ statements := [], terminator := .return_ }] }".to_string()
        }
    };

    let helper_0 = "{ argumentCount := 2, locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false], basicBlocks := [{ statements := [.assign ⟨3, []⟩ (.binaryOp .mul (.copy ⟨1, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 3)⟩)), .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩))], terminator := .return_ }], identity := \"fuzz_helper_0\" }";
    let helper_1 = "{ argumentCount := 2, locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false], basicBlocks := [{ statements := [.assign ⟨3, []⟩ (.binaryOp .bitXor (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)), .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 17)⟩))], terminator := .return_ }], identity := \"fuzz_helper_1\" }";
    let helper_2 = "{ argumentCount := 2, \
        locals := [.int .i32 false, .int .i32 false, .int .i32 false, .bool, .int .i32 false], \
        basicBlocks := [\
            { statements := [.assign ⟨3, []⟩ (.binaryOp .ge (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))], \
              terminator := .switchInt (.copy ⟨3, []⟩) ⟨[(BitVec.ofNat 128 0, 2)], 1⟩ }, \
            { statements := [\
                .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)), \
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 5)⟩))\
              ], terminator := .return_ }, \
            { statements := [\
                .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)), \
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 9)⟩))\
              ], terminator := .return_ }\
        ], identity := \"fuzz_helper_2\" }";
    let ext_unwind = "{ argumentCount := 2, \
        locals := [.int .i32 false, .int .i32 false, .int .i32 false, .bool], \
        basicBlocks := [\
            { statements := [.assign ⟨3, []⟩ (.binaryOp .eq (.copy ⟨2, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))], \
              terminator := .switchInt (.copy ⟨3, []⟩) ⟨[(BitVec.ofNat 128 1, 1)], 2⟩ }, \
            { statements := [.assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))], \
              terminator := .return_ }, \
            { statements := [], terminator := .unsupported }\
        ], identity := \"fuzz_ext_unwind\" }";
    let ext_probe = "{ argumentCount := 2, \
        locals := [.int .i32 false, .int .i32 false, .int .i32 false, .bool], \
        basicBlocks := [\
            { statements := [.assign ⟨3, []⟩ (.binaryOp .eq (.copy ⟨2, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))], \
              terminator := .switchInt (.copy ⟨3, []⟩) ⟨[(BitVec.ofNat 128 1, 1)], 2⟩ }, \
            { statements := [.assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))], \
              terminator := .return_ }, \
            { statements := [], terminator := .unsupported }\
        ], identity := \"fuzz_ext_probe\" }";

    let resolved_schedule = resolve_effective_fuzz_schedule(prog, schedule);
    let effective_schedule = &resolved_schedule;
    let sched_comment = if effective_schedule.is_empty() {
        String::new()
    } else {
        format!("-- EnvSchedule: {:?}\n", effective_schedule)
    };
    let mut external_callees: BTreeSet<String> = match &case.lean_program_spec {
        crate::spec::LeanProgramSpec::MultiCallWithCapturedCallees { external_callees, .. } => {
            external_callees.iter().cloned().collect()
        }
        _ => BTreeSet::new(),
    };
    external_callees.extend(
        effective_schedule
            .per_callee
            .iter()
            .filter_map(|(callee, q)| (!q.is_empty()).then_some(callee.clone())),
    );
    if !effective_schedule.global.is_empty() {
        external_callees.insert("*".to_string());
    }
    let ext_callees_lean = external_callees
        .iter()
        .map(|s| crate::lean_trace_runner::lean_str_lit(s))
        .collect::<Vec<_>>()
        .join(", ");
    let sched_json_lean =
        crate::lean_trace_runner::lean_str_lit(&encode_env_schedule_json(effective_schedule));

    let (inlined_defs, inlined_checks) = match &case.metamorphic_inlined_twin {
        Some(twin) => {
            let inlined_body = prog.render_lean_inlined_body();
            let entry_lit = crate::lean_trace_runner::lean_str_lit(&twin.entry_fn);
            let rust_lit = crate::lean_trace_runner::lean_str_lit(&twin.pure_rust_source);
            (
                format!(
                    "def reproInlinedCaller : Body :=\n  \
                     {{ ({inlined_body} : Body) with identity := {entry_lit} }}\n\n\
                     def reproInlinedProgram : Program := {{\n  \
                       bodies := [reproInlinedCaller],\n  \
                       entryDefId := 0,\n  \
                       pointerWidthBits := 64,\n  \
                       mirProfileVersion := 1,\n  \
                       scope := .unit\n\
                     }}\n\n\
                     def reproInlinedRustSource : String := {rust_lit}\n\n"
                ),
                "\n#check reproInlinedProgram",
            )
        }
        None => (String::new(), ""),
    };

    format!(
        "import Trusted.MirAst\n\
         import Trusted.MirSemantics\n\n\
         -- Standalone Anneal .mir.lean witness bundle (skel={skel_hash})\n\
         {sched_comment}\
         open Trusted.MirAst Trusted.MirSemantics\n\n\
         def reproCaller : Body :=\n  {{ ({caller_body} : Body) with identity := \"fuzz_entry\" }}\n\n\
         def reproProgram : Program := {{\n\
           bodies := [reproCaller, {helper_0}, {helper_1}, {helper_2}, {ext_unwind}, {ext_probe}],\n\
           entryDefId := 0,\n\
           pointerWidthBits := 64,\n\
           mirProfileVersion := 1,\n\
           scope := .unit\n\
         }}\n\n\
         def reproArgs : List Val := [\n\
           .scalar ⟨.i32, false, BitVec.ofNat 128 {}⟩,\n\
           .scalar ⟨.i32, false, BitVec.ofNat 128 {}⟩\n\
         ]\n\n\
         def reproFuel : Nat := 1024\n\n\
         def reproExternalCallees : List String := [{ext_callees_lean}]\n\n\
         def reproEnvScheduleJson : String := {sched_json_lean}\n\n\
         {inlined_defs}\
         #check reproProgram{inlined_checks}\n",
        prog.input_x, prog.input_y
    )
}

fn mir_int_ty(kind: IntKind) -> String {
    format!(".int {} {}", kind.lean_width(), if kind.is_signed() { "true" } else { "false" })
}

fn first_unlowerable_shrink_step(steps: &[ShrinkStep]) -> Option<&'static str> {
    for step in steps {
        match step {
            ShrinkStep::Alloc { .. } => return Some("Alloc"),
            ShrinkStep::Borrow { .. } => return Some("Borrow"),
            ShrinkStep::SplitAt { .. } => return Some("SplitAt"),
            ShrinkStep::UseHandle { .. } => return Some("UseHandle"),
            ShrinkStep::PairOffsetLen { .. } => return Some("PairOffsetLen"),
            ShrinkStep::PaddedRoundTrip { .. } => return Some("PaddedRoundTrip"),
            ShrinkStep::DropGuardWrapper { .. } => return Some("DropGuardWrapper"),
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                if let Some(bad) = first_unlowerable_shrink_step(then_steps)
                    .or_else(|| first_unlowerable_shrink_step(else_steps))
                {
                    return Some(bad);
                }
            }
            ShrinkStep::BoundedLoop { body, .. } | ShrinkStep::IfFalseDecoy { body, .. } => {
                if let Some(bad) = first_unlowerable_shrink_step(body) {
                    return Some(bad);
                }
            }
            ShrinkStep::UnwindProbe { trigger_unwind: true, .. } => {
                return Some("UnwindProbe(trigger_unwind)");
            }
            ShrinkStep::ArithImm { .. }
            | ShrinkStep::HelperCall { .. }
            | ShrinkStep::UnwindProbe { trigger_unwind: false, .. }
            | ShrinkStep::XorLocalImm { .. } => {}
        }
    }
    None
}

fn collect_unwind_probe_callees(
    steps: &[ShrinkStep],
    out: &mut BTreeMap<String, bool>,
) -> Result<(), String> {
    for step in steps {
        match step {
            ShrinkStep::UnwindProbe { callee, trigger_unwind, .. } => {
                if let Some(&prev) = out.get(callee)
                    && prev != *trigger_unwind
                {
                    return Err(format!(
                        "ShrinkableCase mixes conflicting trigger_unwind flags for `{callee}`"
                    ));
                }
                out.insert(callee.clone(), *trigger_unwind);
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                collect_unwind_probe_callees(then_steps, out)?;
                collect_unwind_probe_callees(else_steps, out)?;
            }
            ShrinkStep::BoundedLoop { body, .. }
            | ShrinkStep::IfFalseDecoy { body, .. }
            | ShrinkStep::DropGuardWrapper { body, .. } => {
                collect_unwind_probe_callees(body, out)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn collect_unwind_call_widths(
    steps: &[ShrinkStep],
    local_widths: &BTreeMap<usize, IntKind>,
    default_width: IntKind,
    out: &mut BTreeMap<String, BTreeSet<IntKind>>,
) {
    for step in steps {
        match step {
            ShrinkStep::UnwindProbe { callee, dst_local, .. } => {
                let kind = local_widths.get(dst_local).copied().unwrap_or(default_width);
                out.entry(callee.clone()).or_default().insert(kind);
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                collect_unwind_call_widths(then_steps, local_widths, default_width, out);
                collect_unwind_call_widths(else_steps, local_widths, default_width, out);
            }
            ShrinkStep::BoundedLoop { body, .. }
            | ShrinkStep::IfFalseDecoy { body, .. }
            | ShrinkStep::DropGuardWrapper { body, .. } => {
                collect_unwind_call_widths(body, local_widths, default_width, out);
            }
            _ => {}
        }
    }
}

fn collect_helper_call_widths(
    steps: &[ShrinkStep],
    local_widths: &BTreeMap<usize, IntKind>,
    default_width: IntKind,
    out: &mut BTreeMap<usize, BTreeSet<IntKind>>,
) {
    for step in steps {
        match step {
            ShrinkStep::HelperCall { dst_local, helper_id, .. } => {
                let kind = local_widths.get(dst_local).copied().unwrap_or(default_width);
                out.entry(*helper_id).or_default().insert(kind);
            }
            ShrinkStep::BranchMix { then_steps, else_steps, .. } => {
                collect_helper_call_widths(then_steps, local_widths, default_width, out);
                collect_helper_call_widths(else_steps, local_widths, default_width, out);
            }
            ShrinkStep::BoundedLoop { body, .. }
            | ShrinkStep::IfFalseDecoy { body, .. }
            | ShrinkStep::DropGuardWrapper { body, .. } => {
                collect_helper_call_widths(body, local_widths, default_width, out);
            }
            _ => {}
        }
    }
}

struct LeanBb {
    stmts: Vec<String>,
    term: String,
    cleanup: bool,
}

struct ShrinkableLeanBuilder<'a> {
    case: &'a ShrinkableCase,
    local_widths: &'a BTreeMap<usize, IntKind>,
    lean_locals: &'a BTreeMap<usize, usize>,
    helper_def_ids: &'a BTreeMap<(usize, IntKind), usize>,
    unwind_def_ids: &'a BTreeMap<(String, IntKind), usize>,
    locals: Vec<String>,
    blocks: Vec<LeanBb>,
    cur_stmts: Vec<String>,
}

impl<'a> ShrinkableLeanBuilder<'a> {
    fn alloc_local(&mut self, mir_ty: impl Into<String>) -> usize {
        let id = self.locals.len();
        self.locals.push(mir_ty.into());
        id
    }

    fn local_kind(&self, rust_local: usize) -> IntKind {
        self.local_widths.get(&rust_local).copied().unwrap_or(self.case.scalar_width)
    }

    fn lower_steps(&mut self, steps: &[ShrinkStep]) -> Result<(), String> {
        for step in steps {
            match step {
                ShrinkStep::ArithImm { dst_local, op, imm } => {
                    let d = self.lean_locals[dst_local];
                    let kind = self.local_kind(*dst_local);
                    let ty = mir_int_ty(kind);
                    let masked_imm = kind.mask_bits(u128::from(*imm));
                    if *op == FuzzArithOp::BitAndMask {
                        let tmp = self.alloc_local(ty.clone());
                        let mask_val = kind.mask_bits(0xFFFFu128);
                        self.cur_stmts.push(format!(
                            ".assign ⟨{tmp}, []⟩ (.binaryOp .bitAnd (.copy ⟨{d}, []⟩) (.constant ⟨{ty}, .scalar (BitVec.ofNat 128 {mask_val})⟩))"
                        ));
                        self.cur_stmts.push(format!(
                            ".assign ⟨{d}, []⟩ (.binaryOp .add (.copy ⟨{tmp}, []⟩) (.constant ⟨{ty}, .scalar (BitVec.ofNat 128 {masked_imm})⟩))"
                        ));
                    } else {
                        self.cur_stmts.push(format!(
                            ".assign ⟨{d}, []⟩ (.binaryOp {} (.copy ⟨{d}, []⟩) (.constant ⟨{ty}, .scalar (BitVec.ofNat 128 {masked_imm})⟩))",
                            op.lean_binop()
                        ));
                    }
                }
                ShrinkStep::HelperCall { dst_local, helper_id, bias, rhs_local, .. } => {
                    let kind = self.local_kind(*dst_local);
                    let Some(&def_id) = self.helper_def_ids.get(&(*helper_id, kind)) else {
                        return Err(format!("missing ShrinkHelper id {helper_id}"));
                    };
                    let d = self.lean_locals[dst_local];
                    let d_ty = mir_int_ty(kind);
                    let arg_op = if kind == IntKind::U64 {
                        format!(".copy ⟨{d}, []⟩")
                    } else {
                        let arg_u64 = self.alloc_local(".int .i64 false");
                        self.cur_stmts.push(format!(
                            ".assign ⟨{arg_u64}, []⟩ (.cast .intToInt (.copy ⟨{d}, []⟩) (.int .i64 false))"
                        ));
                        format!(".copy ⟨{arg_u64}, []⟩")
                    };
                    let rhs_op = if let Some(rl) = rhs_local {
                        let r = self.lean_locals[rl];
                        let r_kind = self.local_kind(*rl);
                        let r_ty = mir_int_ty(r_kind);
                        let masked_bias = r_kind.mask_bits(u128::from(*bias));
                        let r_sum = self.alloc_local(r_ty.clone());
                        self.cur_stmts.push(format!(
                            ".assign ⟨{r_sum}, []⟩ (.binaryOp .add (.copy ⟨{r}, []⟩) (.constant ⟨{r_ty}, .scalar (BitVec.ofNat 128 {masked_bias})⟩))"
                        ));
                        if r_kind == IntKind::U64 {
                            format!(".copy ⟨{r_sum}, []⟩")
                        } else {
                            let r_u64 = self.alloc_local(".int .i64 false");
                            self.cur_stmts.push(format!(
                                ".assign ⟨{r_u64}, []⟩ (.cast .intToInt (.copy ⟨{r_sum}, []⟩) (.int .i64 false))"
                            ));
                            format!(".copy ⟨{r_u64}, []⟩")
                        }
                    } else {
                        format!(".constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 {bias})⟩")
                    };
                    let res_loc = self.alloc_local(d_ty);
                    let next_bb = self.blocks.len() + 1;
                    let term = format!(
                        ".call {def_id} [{arg_op}, {rhs_op}] ⟨{res_loc}, []⟩ (some {next_bb}) .continue_"
                    );
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term,
                        cleanup: false,
                    });
                    self.cur_stmts
                        .push(format!(".assign ⟨{d}, []⟩ (.use (.copy ⟨{res_loc}, []⟩))"));
                }
                ShrinkStep::BranchMix {
                    cond_local,
                    taken_then,
                    dynamic_even_cond,
                    then_steps,
                    else_steps,
                    ..
                } => {
                    let cond_loc = if *dynamic_even_cond {
                        let c = self.lean_locals[cond_local];
                        let c_kind = self.local_kind(*cond_local);
                        let c_ty = mir_int_ty(c_kind);
                        let parity_tmp = self.alloc_local(c_ty.clone());
                        self.cur_stmts.push(format!(
                            ".assign ⟨{parity_tmp}, []⟩ (.binaryOp .bitAnd (.copy ⟨{c}, []⟩) (.constant ⟨{c_ty}, .scalar (BitVec.ofNat 128 1)⟩))"
                        ));
                        parity_tmp
                    } else {
                        let cond_b = self.alloc_local(".bool");
                        let flag = if *taken_then { 1 } else { 0 };
                        self.cur_stmts.push(format!(
                            ".assign ⟨{cond_b}, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 {flag})⟩))"
                        ));
                        cond_b
                    };
                    let hdr_bb = self.blocks.len();
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: String::new(),
                        cleanup: false,
                    });
                    let then_entry = self.blocks.len();
                    self.lower_steps(then_steps)?;
                    let then_tail = self.blocks.len();
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: String::new(),
                        cleanup: false,
                    });
                    let else_entry = self.blocks.len();
                    self.lower_steps(else_steps)?;
                    let else_tail = self.blocks.len();
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: String::new(),
                        cleanup: false,
                    });
                    let join_bb = self.blocks.len();
                    self.blocks[hdr_bb].term = if *dynamic_even_cond {
                        format!(
                            ".switchInt (.copy ⟨{cond_loc}, []⟩) ⟨[(BitVec.ofNat 128 0, {then_entry})], {else_entry}⟩"
                        )
                    } else {
                        format!(
                            ".switchInt (.copy ⟨{cond_loc}, []⟩) ⟨[(BitVec.ofNat 128 0, {else_entry})], {then_entry}⟩"
                        )
                    };
                    self.blocks[then_tail].term = format!(".goto {join_bb}");
                    self.blocks[else_tail].term = format!(".goto {join_bb}");
                }
                ShrinkStep::BoundedLoop { iters, induction, body, .. } => {
                    let iter_loc = self.alloc_local(".int .i32 false");
                    let cond_loc = self.alloc_local(".bool");
                    self.cur_stmts.push(format!(
                        ".assign ⟨{iter_loc}, []⟩ (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))"
                    ));
                    let hdr_bb = self.blocks.len() + 1;
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: format!(".goto {hdr_bb}"),
                        cleanup: false,
                    });
                    self.blocks.push(LeanBb {
                        stmts: Vec::new(),
                        term: String::new(),
                        cleanup: false,
                    });
                    let body_bb = self.blocks.len();
                    if let Some(ind) = induction {
                        let d = self.lean_locals[&ind.dst_local];
                        let d_kind = self.local_kind(ind.dst_local);
                        let d_ty = mir_int_ty(d_kind);
                        let masked_mul = d_kind.mask_bits(u128::from(ind.step_mul));
                        let masked_add = d_kind.mask_bits(u128::from(ind.addend));
                        let iter_d = if d_kind == IntKind::U32 {
                            iter_loc
                        } else {
                            let cast_loc = self.alloc_local(d_ty.clone());
                            self.cur_stmts.push(format!(
                                ".assign ⟨{cast_loc}, []⟩ (.cast .intToInt (.copy ⟨{iter_loc}, []⟩) ({d_ty}))"
                            ));
                            cast_loc
                        };
                        let step_mul_loc = self.alloc_local(d_ty.clone());
                        let delta_loc = self.alloc_local(d_ty.clone());
                        self.cur_stmts.push(format!(
                            ".assign ⟨{step_mul_loc}, []⟩ (.binaryOp .mul (.copy ⟨{iter_d}, []⟩) (.constant ⟨{d_ty}, .scalar (BitVec.ofNat 128 {masked_mul})⟩))"
                        ));
                        self.cur_stmts.push(format!(
                            ".assign ⟨{delta_loc}, []⟩ (.binaryOp .add (.copy ⟨{step_mul_loc}, []⟩) (.constant ⟨{d_ty}, .scalar (BitVec.ofNat 128 {masked_add})⟩))"
                        ));
                        self.cur_stmts.push(format!(
                            ".assign ⟨{d}, []⟩ (.binaryOp .add (.copy ⟨{d}, []⟩) (.copy ⟨{delta_loc}, []⟩))"
                        ));
                    }
                    self.lower_steps(body)?;
                    self.cur_stmts.push(format!(
                        ".assign ⟨{iter_loc}, []⟩ (.binaryOp .add (.copy ⟨{iter_loc}, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))"
                    ));
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: format!(".goto {hdr_bb}"),
                        cleanup: false,
                    });
                    let exit_bb = self.blocks.len();
                    self.blocks[hdr_bb].stmts = vec![format!(
                        ".assign ⟨{cond_loc}, []⟩ (.binaryOp .lt (.copy ⟨{iter_loc}, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 {iters})⟩))"
                    )];
                    self.blocks[hdr_bb].term = format!(
                        ".switchInt (.copy ⟨{cond_loc}, []⟩) ⟨[(BitVec.ofNat 128 0, {exit_bb})], {body_bb}⟩"
                    );
                }
                ShrinkStep::IfFalseDecoy { body, .. } => {
                    let cond_b = self.alloc_local(".bool");
                    self.cur_stmts.push(format!(
                        ".assign ⟨{cond_b}, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))"
                    ));
                    let hdr_bb = self.blocks.len();
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: String::new(),
                        cleanup: false,
                    });
                    let decoy_entry = self.blocks.len();
                    self.lower_steps(body)?;
                    let decoy_tail = self.blocks.len();
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: String::new(),
                        cleanup: false,
                    });
                    let join_bb = self.blocks.len();
                    self.blocks[hdr_bb].term = format!(
                        ".switchInt (.copy ⟨{cond_b}, []⟩) ⟨[(BitVec.ofNat 128 0, {join_bb})], {decoy_entry}⟩"
                    );
                    self.blocks[decoy_tail].term = format!(".goto {join_bb}");
                }
                ShrinkStep::UnwindProbe { callee, dst_local, trigger_unwind, .. } => {
                    if *trigger_unwind {
                        return Err(
                            "unlowerable triggering UnwindProbe in ShrinkableCase".to_string()
                        );
                    }
                    let dst_kind = self.local_kind(*dst_local);
                    let Some(&ext_id) = self.unwind_def_ids.get(&(callee.clone(), dst_kind)) else {
                        return Err(format!(
                            "missing lowered UnwindProbe `{callee}` at width {}",
                            dst_kind.rust_name()
                        ));
                    };
                    let dst_lean = self.lean_locals[dst_local];
                    let dst_ty = mir_int_ty(dst_kind);
                    let u_res = self.alloc_local(dst_ty);
                    let resume_bb = self.blocks.len() + 1;
                    let cleanup_bb = self.blocks.len() + 2;
                    let after_bb = self.blocks.len() + 3;
                    self.blocks.push(LeanBb {
                        stmts: std::mem::take(&mut self.cur_stmts),
                        term: format!(
                            ".call {ext_id} [.copy ⟨{dst_lean}, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩] ⟨{u_res}, []⟩ (some {resume_bb}) (.cleanup {cleanup_bb})"
                        ),
                        cleanup: false,
                    });
                    let resume_stmts =
                        vec![format!(".assign ⟨{dst_lean}, []⟩ (.use (.copy ⟨{u_res}, []⟩))")];
                    self.blocks.push(LeanBb {
                        stmts: resume_stmts,
                        term: format!(".goto {after_bb}"),
                        cleanup: false,
                    });
                    self.blocks.push(LeanBb {
                        stmts: vec![".nop".to_string()],
                        term: ".unwindResume".to_string(),
                        cleanup: true,
                    });
                }
                ShrinkStep::XorLocalImm { dst_local, rhs_local, xor_imm } => {
                    let d = self.lean_locals[dst_local];
                    let r = self.lean_locals[rhs_local];
                    let d_kind = self.local_kind(*dst_local);
                    let r_kind = self.local_kind(*rhs_local);
                    let d_ty = mir_int_ty(d_kind);
                    let masked_imm = d_kind.mask_bits(u128::from(*xor_imm));
                    let rhs_expr = if r_kind == d_kind {
                        format!(".copy ⟨{r}, []⟩")
                    } else {
                        let r_cast = self.alloc_local(d_ty.clone());
                        self.cur_stmts.push(format!(
                            ".assign ⟨{r_cast}, []⟩ (.cast .intToInt (.copy ⟨{r}, []⟩) ({d_ty}))"
                        ));
                        format!(".copy ⟨{r_cast}, []⟩")
                    };
                    let sent_loc = self.alloc_local(d_ty.clone());
                    self.cur_stmts.push(format!(
                        ".assign ⟨{sent_loc}, []⟩ (.binaryOp .bitXor ({rhs_expr}) \
                         (.constant ⟨{d_ty}, .scalar (BitVec.ofNat 128 {masked_imm})⟩))"
                    ));
                    self.cur_stmts.push(format!(
                        ".assign ⟨{d}, []⟩ (.binaryOp .bitXor (.copy ⟨{d}, []⟩) (.copy ⟨{sent_loc}, []⟩))"
                    ));
                }
                ShrinkStep::DropGuardWrapper { .. }
                | ShrinkStep::PaddedRoundTrip { .. }
                | ShrinkStep::Alloc { .. }
                | ShrinkStep::Borrow { .. }
                | ShrinkStep::SplitAt { .. }
                | ShrinkStep::UseHandle { .. }
                | ShrinkStep::PairOffsetLen { .. } => {
                    return Err(
                        "unlowerable guard/padded/handle step in ShrinkableCase".to_string()
                    );
                }
            }
        }
        Ok(())
    }
}

fn collect_reachable_shrinkable_callees(
    steps: &[ShrinkStep],
    local_widths: &BTreeMap<usize, IntKind>,
    default_width: IntKind,
    helpers_out: &mut BTreeMap<usize, BTreeSet<IntKind>>,
    unwinds_out: &mut BTreeMap<String, BTreeSet<IntKind>>,
) {
    for step in steps {
        match step {
            ShrinkStep::HelperCall { dst_local, helper_id, .. } => {
                let kind = local_widths.get(dst_local).copied().unwrap_or(default_width);
                helpers_out.entry(*helper_id).or_default().insert(kind);
            }
            ShrinkStep::UnwindProbe { callee, dst_local, .. } => {
                let kind = local_widths.get(dst_local).copied().unwrap_or(default_width);
                unwinds_out.entry(callee.clone()).or_default().insert(kind);
            }
            ShrinkStep::BranchMix {
                taken_then, dynamic_even_cond, then_steps, else_steps, ..
            } => {
                if *dynamic_even_cond {
                    collect_reachable_shrinkable_callees(
                        then_steps,
                        local_widths,
                        default_width,
                        helpers_out,
                        unwinds_out,
                    );
                    collect_reachable_shrinkable_callees(
                        else_steps,
                        local_widths,
                        default_width,
                        helpers_out,
                        unwinds_out,
                    );
                } else if *taken_then {
                    collect_reachable_shrinkable_callees(
                        then_steps,
                        local_widths,
                        default_width,
                        helpers_out,
                        unwinds_out,
                    );
                } else {
                    collect_reachable_shrinkable_callees(
                        else_steps,
                        local_widths,
                        default_width,
                        helpers_out,
                        unwinds_out,
                    );
                }
            }
            ShrinkStep::BoundedLoop { iters, body, .. } => {
                if *iters > 0 {
                    collect_reachable_shrinkable_callees(
                        body,
                        local_widths,
                        default_width,
                        helpers_out,
                        unwinds_out,
                    );
                }
            }
            ShrinkStep::DropGuardWrapper { body, .. } => {
                collect_reachable_shrinkable_callees(
                    body,
                    local_widths,
                    default_width,
                    helpers_out,
                    unwinds_out,
                );
            }
            ShrinkStep::IfFalseDecoy { .. }
            | ShrinkStep::Alloc { .. }
            | ShrinkStep::Borrow { .. }
            | ShrinkStep::SplitAt { .. }
            | ShrinkStep::UseHandle { .. }
            | ShrinkStep::ArithImm { .. }
            | ShrinkStep::PaddedRoundTrip { .. }
            | ShrinkStep::PairOffsetLen { .. }
            | ShrinkStep::XorLocalImm { .. } => {}
        }
    }
}

/// Reject [`ShrinkableCase`] schedules containing non-empty `per_callee` action
/// queues for unreachable or conflicting callee identities so promoted/rendered
/// artifacts never fail at runtime with `unconsumed_schedule`.
pub(crate) fn validate_shrinkable_case_env_schedule(case: &ShrinkableCase) -> Result<(), String> {
    let mut local_widths: BTreeMap<usize, IntKind> = BTreeMap::new();
    for inp in &case.inputs {
        if local_widths.insert(inp.local_id, inp.width).is_some() {
            return Err(format!("ShrinkableCase has duplicate input local_id {}", inp.local_id));
        }
    }
    let mut reachable_helpers: BTreeMap<usize, BTreeSet<IntKind>> = BTreeMap::new();
    let mut reachable_unwinds: BTreeMap<String, BTreeSet<IntKind>> = BTreeMap::new();
    collect_reachable_shrinkable_callees(
        &case.steps,
        &local_widths,
        case.scalar_width,
        &mut reachable_helpers,
        &mut reachable_unwinds,
    );

    let is_scheduled = !case.env_schedule.is_empty();
    let mut allowed_callees: BTreeSet<String> = BTreeSet::new();
    for h in &case.helpers {
        let Some(widths) = reachable_helpers.get(&h.helper_id) else {
            continue;
        };
        let cand_a = format!("fuzz_helper_{}", h.helper_id);
        let cand_b = format!("h{}", h.helper_id);
        if case.env_schedule.per_callee.contains_key(&cand_a)
            && case.env_schedule.per_callee.contains_key(&cand_b)
        {
            return Err(format!(
                "ShrinkableCase mixes conflicting `{cand_a}` and `{cand_b}` schedule keys"
            ));
        }
        if widths.len() > 1 && is_scheduled {
            let base_ident =
                if case.env_schedule.per_callee.contains_key(&cand_a) { cand_a } else { cand_b };
            return Err(format!(
                "ShrinkableCase calls scheduled helper `{base_ident}` at multiple integer widths"
            ));
        }
        if widths.len() == 1 {
            allowed_callees.insert(cand_a);
            allowed_callees.insert(cand_b);
        }
    }
    for (callee, widths) in &reachable_unwinds {
        if widths.len() > 1 && is_scheduled {
            return Err(format!(
                "ShrinkableCase calls scheduled unwind probe `{callee}` at multiple integer widths"
            ));
        }
        if widths.len() == 1 {
            allowed_callees.insert(callee.clone());
        }
    }
    for (callee, queue) in &case.env_schedule.per_callee {
        if !queue.is_empty() && !allowed_callees.contains(callee) {
            return Err(format!(
                "ShrinkableCase env_schedule has non-empty queue for unreachable callee `{callee}`"
            ));
        }
    }
    Ok(())
}

/// Emit a standalone `Trusted.MirAst.Program` Lean 4 bundle
/// (`program_<skel_hash>.mir.lean`) for a pure scalar/CFG/helper/unwind
/// [`ShrinkableCase`], or return `Err(reason)` if the case uses RAII
/// drop-guard, padded-layout, heap/handle, or struct/slice layout primitives
/// not modeled equivalently in `Trusted.MirAst`.
pub fn render_standalone_shrinkable_mir_lean(
    case: &ShrinkableCase,
    skel_hash: &str,
) -> Result<String, String> {
    if !all_handles_defined_and_typed(&case.steps, &case.helpers) {
        return Err("ShrinkableCase failed static handle/helper validation before Lean lowering"
            .to_string());
    }
    validate_shrinkable_case_env_schedule(case)?;
    if !case.struct_fields.is_empty() {
        return Err(
            "ShrinkableCase uses repr(C) struct_fields layout primitives not lowerable to standalone Trusted.MirAst.Program".to_string(),
        );
    }
    if case.slice_len.is_some() {
        return Err(
            "ShrinkableCase uses heap slice_len primitives not lowerable to standalone Trusted.MirAst.Program".to_string(),
        );
    }
    if case.inputs.iter().any(|inp| inp.align_hint.is_some()) {
        return Err(
            "ShrinkableCase uses align_hint pointer metadata not lowerable to standalone Trusted.MirAst.Program".to_string(),
        );
    }
    if let Some(step_kind) = first_unlowerable_shrink_step(&case.steps) {
        return Err(format!(
            "ShrinkableCase uses `{step_kind}` guard/heap/handle step not lowerable to standalone Trusted.MirAst.Program"
        ));
    }

    let mut local_widths: BTreeMap<usize, IntKind> = BTreeMap::new();
    for inp in &case.inputs {
        if local_widths.insert(inp.local_id, inp.width).is_some() {
            return Err(format!("ShrinkableCase has duplicate input local_id {}", inp.local_id));
        }
    }
    let mut referenced_locals = BTreeSet::new();
    collect_shrink_step_locals_recursive(&case.steps, &mut referenced_locals);
    referenced_locals.insert(case.return_local);

    let ret_kind = local_widths.get(&case.return_local).copied().unwrap_or(case.scalar_width);
    let mut locals = vec![mir_int_ty(ret_kind)];
    let mut lean_locals = BTreeMap::new();
    for (idx, inp) in case.inputs.iter().enumerate() {
        locals.push(mir_int_ty(inp.width));
        lean_locals.insert(inp.local_id, idx + 1);
    }
    let mut init_stmts = Vec::new();
    for &lid in &referenced_locals {
        if let std::collections::btree_map::Entry::Vacant(e) = lean_locals.entry(lid) {
            let kind = local_widths.get(&lid).copied().unwrap_or(case.scalar_width);
            let ty = mir_int_ty(kind);
            let lean_id = locals.len();
            locals.push(ty.clone());
            e.insert(lean_id);
            init_stmts.push(format!(
                ".assign ⟨{lean_id}, []⟩ (.use (.constant ⟨{ty}, .scalar (BitVec.ofNat 128 0)⟩))"
            ));
        }
    }

    let mut helper_call_widths: BTreeMap<usize, BTreeSet<IntKind>> = BTreeMap::new();
    collect_helper_call_widths(
        &case.steps,
        &local_widths,
        case.scalar_width,
        &mut helper_call_widths,
    );

    let mut used_identities = BTreeSet::new();
    used_identities.insert("repro_shrinkable_entry".to_string());
    let mut helper_def_ids = BTreeMap::new();
    let mut body_exprs = Vec::new();
    for h in &case.helpers {
        let cand_a = format!("fuzz_helper_{}", h.helper_id);
        let cand_b = format!("h{}", h.helper_id);
        let has_a = case.env_schedule.per_callee.contains_key(&cand_a);
        let has_b = case.env_schedule.per_callee.contains_key(&cand_b);
        if has_a && has_b {
            return Err(format!(
                "ShrinkableCase mixes conflicting `{cand_a}` and `{cand_b}` schedule keys"
            ));
        }
        let base_ident = if has_a { cand_a } else { cand_b };
        let widths: Vec<IntKind> = helper_call_widths
            .get(&h.helper_id)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_else(|| vec![IntKind::U64]);
        let is_scheduled = !case.env_schedule.is_empty();
        if widths.len() > 1 && is_scheduled {
            return Err(format!(
                "ShrinkableCase calls scheduled helper `{base_ident}` at multiple integer widths"
            ));
        }
        for &w in &widths {
            let ident = if widths.len() == 1 {
                base_ident.clone()
            } else {
                format!("{base_ident}_{}", w.rust_name())
            };
            if !used_identities.insert(ident.clone()) {
                return Err(format!("duplicate helper identity `{ident}`"));
            }
            let dst_ty = mir_int_ty(w);
            let ret_stmt = if w == IntKind::U64 {
                ".assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))".to_string()
            } else {
                format!(".assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨3, []⟩) ({dst_ty}))")
            };
            let def_id = 1 + body_exprs.len();
            helper_def_ids.insert((h.helper_id, w), def_id);
            let ident_lit = crate::lean_trace_runner::lean_str_lit(&ident);
            let helper_body = match h.op {
                ShrinkHelperOp::AffineMulAdd => format!(
                    "{{ argumentCount := 2, \
                     locals := [{dst_ty}, .int .i64 false, .int .i64 false, .int .i64 false], \
                     basicBlocks := [{{ statements := [\
                         .assign ⟨3, []⟩ (.binaryOp .mul (.copy ⟨1, []⟩) (.constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 {})⟩)), \
                         .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩)), \
                         .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 {})⟩)), \
                         {ret_stmt}\
                     ], terminator := .return_ }}], \
                     identity := {ident_lit} }}",
                    h.multiplier, h.addend
                ),
                ShrinkHelperOp::BitXorAdd => format!(
                    "{{ argumentCount := 2, \
                     locals := [{dst_ty}, .int .i64 false, .int .i64 false, .int .i64 false], \
                     basicBlocks := [{{ statements := [\
                         .assign ⟨3, []⟩ (.binaryOp .bitXor (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)), \
                         .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 {})⟩)), \
                         {ret_stmt}\
                     ], terminator := .return_ }}], \
                     identity := {ident_lit} }}",
                    h.addend
                ),
                ShrinkHelperOp::AbsDiffBranch => format!(
                    "{{ argumentCount := 2, \
                     locals := [{dst_ty}, .int .i64 false, .int .i64 false, .int .i64 false, .bool, .int .i64 false], \
                     basicBlocks := [\
                         {{ statements := [.assign ⟨4, []⟩ (.binaryOp .ge (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))], \
                           terminator := .switchInt (.copy ⟨4, []⟩) ⟨[(BitVec.ofNat 128 0, 2)], 1⟩ }}, \
                         {{ statements := [\
                             .assign ⟨5, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)), \
                             .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 {})⟩)), \
                             {ret_stmt}\
                           ], terminator := .return_ }}, \
                         {{ statements := [\
                             .assign ⟨5, []⟩ (.binaryOp .sub (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)), \
                             .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 {})⟩)), \
                             {ret_stmt}\
                           ], terminator := .return_ }}\
                     ], \
                     identity := {ident_lit} }}",
                    h.multiplier, h.addend
                ),
            };
            body_exprs.push(helper_body);
        }
    }

    let mut unwind_callees = BTreeMap::new();
    collect_unwind_probe_callees(&case.steps, &mut unwind_callees)?;
    let mut unwind_call_widths: BTreeMap<String, BTreeSet<IntKind>> = BTreeMap::new();
    collect_unwind_call_widths(
        &case.steps,
        &local_widths,
        case.scalar_width,
        &mut unwind_call_widths,
    );
    let mut unwind_def_ids = BTreeMap::new();
    let is_scheduled = !case.env_schedule.is_empty();
    for (callee, &trig) in &unwind_callees {
        if trig {
            return Err(format!(
                "ShrinkableCase triggering UnwindProbe `{callee}` is not lowerable cleanly to standalone Trusted.MirAst.Program"
            ));
        }
        let widths: Vec<IntKind> = unwind_call_widths
            .get(callee)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_else(|| vec![ret_kind]);
        if widths.len() > 1 && is_scheduled {
            return Err(format!(
                "ShrinkableCase calls scheduled unwind probe `{callee}` at multiple integer widths"
            ));
        }
        for &w in &widths {
            let ident = if widths.len() == 1 {
                callee.clone()
            } else {
                format!("{callee}_{}", w.rust_name())
            };
            if !used_identities.insert(ident.clone()) {
                return Err(format!("unwind callee `{ident}` collides with program body identity"));
            }
            let dst_ty = mir_int_ty(w);
            let dst_one = w.mask_bits(1);
            let def_id = 1 + body_exprs.len();
            unwind_def_ids.insert((callee.clone(), w), def_id);
            let ident_lit = crate::lean_trace_runner::lean_str_lit(&ident);
            body_exprs.push(format!(
                "{{ argumentCount := 2, \
                 locals := [{dst_ty}, {dst_ty}, .int .i32 false, .bool], \
                 basicBlocks := [\
                     {{ statements := [.assign ⟨3, []⟩ (.binaryOp .eq (.copy ⟨2, []⟩) (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))], \
                       terminator := .switchInt (.copy ⟨3, []⟩) ⟨[(BitVec.ofNat 128 1, 1)], 2⟩ }}, \
                     {{ statements := [.assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.constant ⟨{dst_ty}, .scalar (BitVec.ofNat 128 {dst_one})⟩))], \
                       terminator := .return_ }}, \
                     {{ statements := [], terminator := .unsupported }}\
                 ], \
                 identity := {ident_lit} }}"
            ));
        }
    }

    let mut builder = ShrinkableLeanBuilder {
        case,
        local_widths: &local_widths,
        lean_locals: &lean_locals,
        helper_def_ids: &helper_def_ids,
        unwind_def_ids: &unwind_def_ids,
        locals,
        blocks: Vec::new(),
        cur_stmts: init_stmts,
    };
    builder.lower_steps(&case.steps)?;
    let ret_lean = lean_locals[&case.return_local];
    builder.cur_stmts.push(format!(".assign ⟨0, []⟩ (.use (.copy ⟨{ret_lean}, []⟩))"));
    builder.blocks.push(LeanBb {
        stmts: std::mem::take(&mut builder.cur_stmts),
        term: ".return_".to_string(),
        cleanup: false,
    });

    let blocks_lean = builder
        .blocks
        .iter()
        .map(|bb| {
            if bb.cleanup {
                format!(
                    "{{ statements := [{}], terminator := {}, cleanup := true }}",
                    bb.stmts.join(", "),
                    bb.term
                )
            } else {
                format!("{{ statements := [{}], terminator := {} }}", bb.stmts.join(", "), bb.term)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let locals_lean = builder.locals.join(", ");
    let caller_body = format!(
        "{{\n  argumentCount := {},\n  locals := [{locals_lean}],\n  basicBlocks := [{blocks_lean}],\n  identity := \"repro_shrinkable_entry\"\n}}",
        case.inputs.len()
    );

    let mut all_bodies = vec!["reproCaller".to_string()];
    all_bodies.extend(body_exprs);
    let args_lean = case
        .inputs
        .iter()
        .map(|inp| format!(".scalar {}", inp.width.to_lean_scalar(inp.value)))
        .collect::<Vec<_>>()
        .join(", ");

    let mut external_callees: BTreeSet<String> = case
        .env_schedule
        .per_callee
        .iter()
        .filter_map(|(callee, q)| (!q.is_empty()).then_some(callee.clone()))
        .collect();
    if !case.env_schedule.global.is_empty() {
        external_callees.insert("*".to_string());
    }
    let ext_callees_lean = external_callees
        .iter()
        .map(|s| crate::lean_trace_runner::lean_str_lit(s))
        .collect::<Vec<_>>()
        .join(", ");
    let sched_json_lean =
        crate::lean_trace_runner::lean_str_lit(&encode_env_schedule_json(&case.env_schedule));
    let sched_comment = if case.env_schedule.is_empty() {
        String::new()
    } else {
        format!("-- EnvSchedule: {:?}\n", case.env_schedule)
    };

    Ok(format!(
        "import Trusted.MirAst\n\
         import Trusted.MirSemantics\n\n\
         -- Standalone Anneal ShrinkableCase .mir.lean bundle (id={skel_hash})\n\
         {sched_comment}\
         open Trusted.MirAst Trusted.MirSemantics\n\n\
         def reproCaller : Body :=\n  {caller_body}\n\n\
         def reproProgram : Program := {{\n\
           bodies := [{}],\n\
           entryDefId := 0,\n\
           pointerWidthBits := 64,\n\
           mirProfileVersion := 1,\n\
           scope := .unit\n\
         }}\n\n\
         def reproArgs : List Val := [{args_lean}]\n\n\
         def reproFuel : Nat := 1024\n\n\
         def reproExternalCallees : List String := [{ext_callees_lean}]\n\n\
         def reproEnvScheduleJson : String := {sched_json_lean}\n\n\
         #check reproProgram\n",
        all_bodies.join(", ")
    ))
}

/// Authority-bound variant of [`canonical_witness_artifact_id`] that folds
/// concrete `FuzzProgram` constants, effective schedule, signature, terminal
/// verdict, and normalized authority failure details into `<content24>` so
/// distinct canonical bugs never collide onto one witness bundle ID.
pub fn canonical_witness_artifact_id_with_authority(
    skel_hash: &str,
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
    signature: Option<&ShrinkFailureSignature>,
    verdict: &TraceVerdict,
    authority_detail: Option<&str>,
) -> String {
    let mut payload = String::with_capacity(256);
    let _ = write!(payload, "x={}|y={}|steps={:?}", prog.input_x, prog.input_y, prog.steps);
    let eff_sched = resolve_effective_fuzz_schedule(prog, schedule);
    payload.push_str("|sched=");
    payload.push_str(&encode_env_schedule_json(&eff_sched));
    if let Some(sig) = signature {
        payload.push_str("|sig=");
        payload.push_str(&serde_json::to_string(sig).unwrap_or_default());
    }
    let _ = write!(payload, "|verdict={verdict}");
    if let Some(detail) = authority_detail {
        payload.push_str("|auth=");
        payload.push_str(detail);
    }
    let content24 = &sha256_hex(payload.as_bytes())[..24];
    format!("{skel_hash}_{content24}")
}

/// Compute a unique, deterministic artifact identifier
/// (`<skel_hash>_<content24>`) combining the constant-erased skeleton hash with
/// a 24-hex (96-bit) digest over concrete `FuzzProgram` constants, effective
/// schedule, failure signature, and verdict so distinct witnesses sharing a
/// skeleton never clobber each other on disk or collide on `repro_case_id`.
pub fn canonical_witness_artifact_id(
    skel_hash: &str,
    prog: &FuzzProgram,
    schedule: Option<&EnvSchedule>,
    signature: Option<&ShrinkFailureSignature>,
    verdict: &TraceVerdict,
) -> String {
    canonical_witness_artifact_id_with_authority(
        skel_hash, prog, schedule, signature, verdict, None,
    )
}

/// Authority-bound variant of [`canonical_shrinkable_artifact_id`] folding
/// normalized authority fault causes alongside the [`ShrinkableCase`] and
/// signature.
pub fn canonical_shrinkable_artifact_id_with_authority(
    skel_hash: &str,
    case: &ShrinkableCase,
    signature: &ShrinkFailureSignature,
    authority_detail: Option<&str>,
) -> String {
    let mut payload = canonical_shrinkable_case_key(case);
    payload.push_str("|sig=");
    payload.push_str(&serde_json::to_string(signature).unwrap_or_default());
    if let Some(detail) = authority_detail {
        payload.push_str("|auth=");
        payload.push_str(detail);
    }
    let content24 = &sha256_hex(payload.as_bytes())[..24];
    format!("{skel_hash}_{content24}")
}

/// Compute `<skel_hash>_<content24>` for a [`ShrinkableCase`] + signature so
/// distinct constant-erased skeletons remain grouped while reproducer paths
/// stay distinct.
pub fn canonical_shrinkable_artifact_id(
    skel_hash: &str,
    case: &ShrinkableCase,
    signature: &ShrinkFailureSignature,
) -> String {
    canonical_shrinkable_artifact_id_with_authority(skel_hash, case, signature, None)
}

/// Reproducible divergence witness artifact emitted to disk when shrinking a
/// failing case.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessArtifact {
    pub case_id: String,
    pub verdict: TraceVerdict,
    pub original_verdict: TraceVerdict,
    pub shrink: ProgramShrinkResult,
    pub reproducer_rust_source: String,
    #[serde(default)]
    pub signature: Option<ShrinkFailureSignature>,
    #[serde(default)]
    pub minimized_report: Option<Box<CaseReport>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repro_schedule: Option<EnvSchedule>,
    #[serde(default)]
    pub minimized_skeleton_hash: String,
    #[serde(default)]
    pub repro_case_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub report_index: Option<usize>,
}

impl WitnessArtifact {
    pub fn from_shrink(
        case_id: impl Into<String>,
        minimized_verdict: TraceVerdict,
        original_verdict: TraceVerdict,
        shrink: ProgramShrinkResult,
    ) -> Self {
        Self::from_shrink_with_schedule(case_id, minimized_verdict, original_verdict, shrink, None)
    }

    pub fn from_shrink_with_schedule(
        case_id: impl Into<String>,
        minimized_verdict: TraceVerdict,
        original_verdict: TraceVerdict,
        shrink: ProgramShrinkResult,
        schedule: Option<&EnvSchedule>,
    ) -> Self {
        let resolved_schedule = if let Some(s) = schedule {
            Some(s.clone())
        } else {
            let resolved = resolve_effective_fuzz_schedule(&shrink.minimized, None);
            if resolved.is_empty() { None } else { Some(resolved) }
        };
        let eff_ref = resolved_schedule.as_ref();
        let skel_hash = canonical_fuzz_program_skeleton_hash(&shrink.minimized, eff_ref);
        let artifact_id = canonical_witness_artifact_id(
            &skel_hash,
            &shrink.minimized,
            eff_ref,
            None,
            &minimized_verdict,
        );
        let repro_case_id = format!("repro_{artifact_id}");
        let is_metamorphic = verdict_is_metamorphic_duality(&minimized_verdict);
        let pinned_relations = pinned_metamorphic_relations(&minimized_verdict, None);
        let reproducer_rust_source = render_standalone_fuzz_repro_rs_for_relations(
            &shrink.minimized,
            eff_ref,
            &artifact_id,
            is_metamorphic,
            &pinned_relations,
        );
        Self {
            case_id: case_id.into(),
            verdict: minimized_verdict,
            original_verdict,
            shrink,
            reproducer_rust_source,
            signature: None,
            minimized_report: None,
            repro_schedule: resolved_schedule,
            minimized_skeleton_hash: skel_hash,
            repro_case_id,
            report_index: None,
        }
    }

    pub fn with_signature(mut self, sig: ShrinkFailureSignature) -> Self {
        let is_metamorphic = sig.mismatch_category == "metamorphic_duality"
            || verdict_is_metamorphic_duality(&self.verdict);
        let eff_schedule = if let Some(s) = self.repro_schedule.clone() {
            Some(s)
        } else {
            let resolved = resolve_effective_fuzz_schedule(&self.shrink.minimized, None);
            if resolved.is_empty() { None } else { Some(resolved) }
        };
        let skel_hash =
            canonical_fuzz_program_skeleton_hash(&self.shrink.minimized, eff_schedule.as_ref());
        self.minimized_skeleton_hash = skel_hash.clone();
        let artifact_id = canonical_witness_artifact_id(
            &skel_hash,
            &self.shrink.minimized,
            eff_schedule.as_ref(),
            Some(&sig),
            &self.verdict,
        );
        self.repro_case_id = format!("repro_{artifact_id}");
        let pinned_relations = pinned_metamorphic_relations(&self.verdict, Some(&sig));
        self.reproducer_rust_source = render_standalone_fuzz_repro_rs_for_relations(
            &self.shrink.minimized,
            eff_schedule.as_ref(),
            &artifact_id,
            is_metamorphic,
            &pinned_relations,
        );
        self.signature = Some(sig);
        self
    }

    pub fn with_minimized_report(mut self, report: CaseReport) -> Self {
        let min_sig = ShrinkFailureSignature::from_case_report(&report);
        let eff_sig = if report.case_id != self.case_id {
            None
        } else {
            match (self.signature.as_ref(), min_sig.as_ref()) {
                (Some(stored), Some(derived)) if stored != derived => None,
                (Some(stored), _) => Some(stored.clone()),
                (None, Some(derived)) => Some(derived.clone()),
                (None, None) => None,
            }
        };
        if let Some(sig) = eff_sig.as_ref() {
            let eff_schedule = if let Some(s) = self.repro_schedule.clone() {
                Some(s)
            } else {
                let resolved = resolve_effective_fuzz_schedule(&self.shrink.minimized, None);
                if resolved.is_empty() { None } else { Some(resolved) }
            };
            let skel_hash =
                canonical_fuzz_program_skeleton_hash(&self.shrink.minimized, eff_schedule.as_ref());
            self.minimized_skeleton_hash = skel_hash.clone();
            let auth_detail =
                crate::dedup::canonical_case_report_authority_detail_key(sig, &report);
            let artifact_id = canonical_witness_artifact_id_with_authority(
                &skel_hash,
                &self.shrink.minimized,
                eff_schedule.as_ref(),
                Some(sig),
                &report.verdict,
                Some(&auth_detail),
            );
            let is_metamorphic = sig.mismatch_category == "metamorphic_duality"
                || verdict_is_metamorphic_duality(&report.verdict);
            let pinned_relations = pinned_metamorphic_relations(&report.verdict, Some(sig));
            self.repro_case_id = format!("repro_{artifact_id}");
            self.reproducer_rust_source = render_standalone_fuzz_repro_rs_for_relations(
                &self.shrink.minimized,
                eff_schedule.as_ref(),
                &artifact_id,
                is_metamorphic,
                &pinned_relations,
            );
        }
        self.minimized_report = Some(Box::new(report));
        self
    }

    pub fn with_report_index(mut self, report_index: usize) -> Self {
        self.report_index = Some(report_index);
        self
    }

    pub fn write_json(&self, path: &Path) -> Result<(), String> {
        let body = serde_json::to_string_pretty(self)
            .map_err(|e| format!("serialize witness artifact: {e}"))?;
        atomic_write_text(path, &body)
    }
}

/// Self-contained witness bundle (`repro_<bundle_id>.rs` +
/// `program_<bundle_id>.mir.lean` + `witness_<bundle_id>.json`) persisted
/// safely to disk.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessBundle {
    pub skel_hash: String,
    #[serde(default)]
    pub bundle_id: String,
    pub repro_case_id: String,
    pub repro_rust_source: String,
    pub mir_lean_source: String,
    pub artifact: WitnessArtifact,
}

impl WitnessBundle {
    /// Build a verified [`WitnessBundle`], requiring converged 1-minimal
    /// shrink (`succeeded`, `is_one_minimal`, `converged_1_minimal`, and
    /// `!budget_exhausted`), rejecting conflicting explicit schedules against a
    /// stored `repro_schedule`, deriving the failure signature from
    /// `artifact.minimized_report` first when present, and failing closed if
    /// `minimized_report` is non-failing or any stored `artifact.signature`
    /// disagrees with it.
    pub fn try_from_witness(
        mut artifact: WitnessArtifact,
        schedule: Option<&EnvSchedule>,
    ) -> Result<Self, String> {
        if !artifact.shrink.succeeded
            || !artifact.shrink.is_one_minimal
            || !artifact.shrink.converged_1_minimal
            || artifact.shrink.budget_exhausted
        {
            return Err(format!(
                "cannot build WitnessBundle before converged 1-minimal shrink without budget exhaustion (succeeded={}, is_one_minimal={}, converged_1_minimal={}, budget_exhausted={})",
                artifact.shrink.succeeded,
                artifact.shrink.is_one_minimal,
                artifact.shrink.converged_1_minimal,
                artifact.shrink.budget_exhausted
            ));
        }
        if let (Some(explicit), Some(stored)) = (schedule, artifact.repro_schedule.as_ref())
            && explicit != stored
        {
            return Err(format!(
                "explicit schedule conflicts with stored artifact repro_schedule for witness `{}`",
                artifact.case_id
            ));
        }
        artifact.shrink.minimized.validate()?;
        let eff_schedule =
            schedule.cloned().or_else(|| artifact.repro_schedule.clone()).or_else(|| {
                let resolved = resolve_effective_fuzz_schedule(&artifact.shrink.minimized, None);
                if resolved.is_empty() { None } else { Some(resolved) }
            });
        let skel_hash =
            canonical_fuzz_program_skeleton_hash(&artifact.shrink.minimized, eff_schedule.as_ref());
        let (auth_verdict, eff_sig, auth_detail) = if let Some(min_rep) =
            artifact.minimized_report.as_deref()
        {
            if min_rep.case_id != artifact.case_id {
                return Err(format!(
                    "minimized report case_id `{}` does not match witness artifact case_id `{}`",
                    min_rep.case_id, artifact.case_id
                ));
            }
            let derived = ShrinkFailureSignature::from_case_report(min_rep).ok_or_else(|| {
                format!(
                    "minimized report verdict `{}` is not a shrinkable semantic divergence",
                    min_rep.verdict
                )
            })?;
            crate::dedup::validate_case_report_signature_against_authorities(min_rep, &derived)?;
            if let Some(stored) = artifact.signature.as_ref()
                && stored != &derived
            {
                return Err(format!(
                    "stored witness signature {stored:?} conflicts with authoritative minimized_report signature {derived:?}"
                ));
            }
            let detail =
                crate::dedup::canonical_case_report_authority_detail_key(&derived, min_rep);
            (min_rep.verdict.clone(), Some(derived), Some(detail))
        } else {
            let verdict_sig =
                ShrinkFailureSignature::from_verdict_and_legs(&artifact.verdict, None, None)
                    .ok_or_else(|| {
                        format!(
                            "witness artifact verdict `{}` is not a shrinkable semantic divergence",
                            artifact.verdict
                        )
                    })?;
            let sig = if let Some(stored) = artifact.signature.as_ref() {
                if !stored_signature_matches_verdict(stored, &verdict_sig, &artifact.verdict) {
                    return Err(format!(
                        "stored witness signature {stored:?} conflicts with artifact verdict `{}`",
                        artifact.verdict
                    ));
                }
                stored.clone()
            } else {
                verdict_sig
            };
            (artifact.verdict.clone(), Some(sig), None)
        };
        let bundle_id = canonical_witness_artifact_id_with_authority(
            &skel_hash,
            &artifact.shrink.minimized,
            eff_schedule.as_ref(),
            eff_sig.as_ref(),
            &auth_verdict,
            auth_detail.as_deref(),
        );
        let repro_case_id = format!("repro_{bundle_id}");
        let is_metamorphic =
            eff_sig.as_ref().is_some_and(|s| s.mismatch_category == "metamorphic_duality")
                || verdict_is_metamorphic_duality(&auth_verdict);
        let pinned_relations = pinned_metamorphic_relations(&auth_verdict, eff_sig.as_ref());
        let repro_rust_source = render_standalone_fuzz_repro_rs_for_relations(
            &artifact.shrink.minimized,
            eff_schedule.as_ref(),
            &bundle_id,
            is_metamorphic,
            &pinned_relations,
        );
        let mir_lean_source = render_standalone_mir_lean(
            &artifact.shrink.minimized,
            eff_schedule.as_ref(),
            &bundle_id,
        );
        artifact.verdict = auth_verdict;
        artifact.repro_schedule = eff_schedule;
        artifact.minimized_skeleton_hash = skel_hash.clone();
        artifact.signature = eff_sig;
        artifact.repro_case_id = repro_case_id.clone();
        artifact.reproducer_rust_source = repro_rust_source.clone();
        Ok(Self {
            skel_hash,
            bundle_id,
            repro_case_id,
            repro_rust_source,
            mir_lean_source,
            artifact,
        })
    }

    pub fn from_witness(artifact: WitnessArtifact, schedule: Option<&EnvSchedule>) -> Self {
        Self::try_from_witness(artifact, schedule)
            .unwrap_or_else(|err| panic!("invalid WitnessArtifact for WitnessBundle: {err}"))
    }

    /// Persist `repro_<bundle_id>.rs`, `program_<bundle_id>.mir.lean`, and
    /// `witness_<bundle_id>.json` inside `dir`, staging all three temp files
    /// before committing and rolling back prior contents on failure.
    pub fn write_to_dir(&self, dir: &Path) -> Result<WrittenBundlePaths, String> {
        self.write_to_dir_with_extra(dir, &[])
    }

    /// Persist the bundle members together with caller-supplied companion
    /// files (such as `<case_id>.witness.json`) as a single staged group so a
    /// failure in any member preserves all pre-existing files on disk.
    pub(crate) fn write_to_dir_with_extra(
        &self,
        dir: &Path,
        extra_files: &[(&Path, &[u8])],
    ) -> Result<WrittenBundlePaths, String> {
        let expected =
            Self::try_from_witness(self.artifact.clone(), self.artifact.repro_schedule.as_ref())?;
        if self.skel_hash != expected.skel_hash {
            return Err(format!(
                "WitnessBundle skel_hash `{}` does not match canonical artifact hash `{}`",
                self.skel_hash, expected.skel_hash
            ));
        }
        if self.bundle_id != expected.bundle_id {
            return Err(format!(
                "WitnessBundle bundle_id `{}` does not match canonical artifact bundle_id `{}`",
                self.bundle_id, expected.bundle_id
            ));
        }
        if self.repro_case_id != expected.repro_case_id {
            return Err(format!(
                "WitnessBundle repro_case_id `{}` does not match canonical artifact repro_case_id `{}`",
                self.repro_case_id, expected.repro_case_id
            ));
        }
        if self.repro_rust_source != expected.repro_rust_source {
            return Err(
                "WitnessBundle repro_rust_source diverges from canonical artifact".to_string()
            );
        }
        if self.mir_lean_source != expected.mir_lean_source {
            return Err(
                "WitnessBundle mir_lean_source diverges from canonical artifact".to_string()
            );
        }
        if self.artifact != expected.artifact {
            return Err(
                "WitnessBundle artifact fields diverge from canonical normalization".to_string()
            );
        }
        let suffix = &expected.bundle_id;
        if !suffix.contains('_') || !is_valid_bundle_suffix(suffix) {
            return Err(format!("noncanonical WitnessBundle identifier {suffix:?}"));
        }
        for &(extra_path, _) in extra_files {
            let valid_child =
                extra_path.file_name().is_some_and(|name| dir.join(name) == *extra_path);
            if !valid_child {
                return Err(format!(
                    "companion witness path {} escapes witness dir {}",
                    extra_path.display(),
                    dir.display()
                ));
            }
        }
        fs::create_dir_all(dir)
            .map_err(|e| format!("create witness bundle dir {}: {e}", dir.display()))?;
        let repro_rs_path = dir.join(format!("repro_{suffix}.rs"));
        let mir_lean_path = dir.join(format!("program_{suffix}.mir.lean"));
        let witness_json_path = dir.join(format!("witness_{suffix}.json"));
        let witness_body = serde_json::to_string_pretty(&expected.artifact)
            .map_err(|e| format!("serialize witness artifact: {e}"))?;

        let mut staged = Vec::with_capacity(3 + extra_files.len());
        staged.push((
            stage_temp_bytes(dir, expected.repro_rust_source.as_bytes())?,
            repro_rs_path.as_path(),
        ));
        staged.push((
            stage_temp_bytes(dir, expected.mir_lean_source.as_bytes())?,
            mir_lean_path.as_path(),
        ));
        staged.push((stage_temp_bytes(dir, witness_body.as_bytes())?, witness_json_path.as_path()));
        for &(extra_path, extra_bytes) in extra_files {
            let parent = match extra_path.parent() {
                Some(p) if !p.as_os_str().is_empty() => p,
                _ => Path::new("."),
            };
            fs::create_dir_all(parent)
                .map_err(|e| format!("create parent dir {}: {e}", parent.display()))?;
            staged.push((stage_temp_bytes(parent, extra_bytes)?, extra_path));
        }
        commit_staged_bundle_group(staged)?;

        Ok(WrittenBundlePaths { repro_rs_path, mir_lean_path, witness_json_path })
    }
}

/// Paths written by [`WitnessBundle::write_to_dir`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WrittenBundlePaths {
    pub repro_rs_path: std::path::PathBuf,
    pub mir_lean_path: std::path::PathBuf,
    pub witness_json_path: std::path::PathBuf,
}

fn is_valid_caller_frame_relation(rel: &str) -> bool {
    matches!(
        rel,
        "metamorphic_caller_frame_law"
            | "metamorphic_caller_frame_law:called_rustc"
            | "metamorphic_caller_frame_law:inlined_rustc"
            | "metamorphic_caller_frame_law:called_miri"
            | "metamorphic_caller_frame_law:inlined_miri"
            | "metamorphic_caller_frame_law:called_lean"
            | "metamorphic_caller_frame_law:inlined_lean"
    )
}

fn is_known_base_metamorphic_relation(rel: &str) -> bool {
    matches!(
        rel,
        "lean_called_vs_inlined"
            | "called_rustc_o0_vs_o2"
            | "inlined_rustc_o0_vs_o2"
            | "rustc_called_vs_inlined"
            | "called_rustc_vs_lean"
            | "inlined_rustc_vs_lean"
            | "called_miri_vs_lean_ub"
            | "inlined_miri_vs_lean_ub"
            | "called_skipped_ub_lean_accept"
            | "inlined_skipped_ub_lean_accept"
            | "miri_called_vs_inlined"
    )
}

fn metamorphic_relations_match_verdict(
    stored: &[String],
    verdict_rels: &[String],
    verdict: &TraceVerdict,
) -> bool {
    if verdict_rels.is_empty() {
        return true;
    }
    if stored.is_empty() {
        return false;
    }
    let primary_detail = match verdict {
        TraceVerdict::UnsoundAccept { detail } | TraceVerdict::ToolError { detail, .. } => {
            detail.split("; secondary ").next().unwrap_or(detail).trim()
        }
        _ => "",
    };
    let has_unqualified_ub_clause = primary_detail.split("; ").map(str::trim).any(|part| {
        part.contains("UB fault cause mismatch:")
            || part.contains("UB entry-input boundary digest mismatch:")
            || part.contains("UB fault missing authenticated entry-input digest")
    });
    let only_unspecified = verdict_rels.len() == 1 && verdict_rels[0] == "metamorphic_unspecified";

    for s_rel in stored {
        if s_rel == "metamorphic_unspecified" {
            if !only_unspecified {
                return false;
            }
        } else if is_valid_caller_frame_relation(s_rel) {
            let exact = verdict_rels.iter().any(|v| v == s_rel);
            let generic = verdict_rels.iter().any(|v| v == "metamorphic_caller_frame_law");
            if !exact && !generic {
                return false;
            }
        } else if s_rel == "called_miri_vs_lean_ub" || s_rel == "inlined_miri_vs_lean_ub" {
            if !verdict_rels.iter().any(|v| v == s_rel) && !has_unqualified_ub_clause {
                return false;
            }
        } else if is_known_base_metamorphic_relation(s_rel) {
            if !verdict_rels.iter().any(|v| v == s_rel) {
                return false;
            }
        } else {
            return false;
        }
    }

    for v_rel in verdict_rels {
        if v_rel == "metamorphic_unspecified" {
            let ok = stored.iter().any(|s| s == "metamorphic_unspecified")
                || (has_unqualified_ub_clause
                    && stored
                        .iter()
                        .any(|s| s == "called_miri_vs_lean_ub" || s == "inlined_miri_vs_lean_ub"));
            if !ok {
                return false;
            }
        } else if v_rel == "metamorphic_caller_frame_law" {
            if !stored.iter().any(|s| is_valid_caller_frame_relation(s)) {
                return false;
            }
        } else if !stored.iter().any(|s| s == v_rel) {
            return false;
        }
    }

    true
}

fn stored_signature_matches_verdict(
    stored: &ShrinkFailureSignature,
    verdict_sig: &ShrinkFailureSignature,
    verdict: &TraceVerdict,
) -> bool {
    if stored.verdict_kind != verdict_sig.verdict_kind
        || stored.ref_outcome_kind != verdict_sig.ref_outcome_kind
        || stored.lean_outcome_kind != verdict_sig.lean_outcome_kind
        || stored.ref_ub_class != verdict_sig.ref_ub_class
        || stored.lean_ub_class != verdict_sig.lean_ub_class
        || stored.lean_fault_site_kind != verdict_sig.lean_fault_site_kind
        || stored.metamorphic_leg_kinds != verdict_sig.metamorphic_leg_kinds
    {
        return false;
    }
    let category_ok = stored.mismatch_category == verdict_sig.mismatch_category
        || (stored.mismatch_category == "spine_mismatch"
            && matches!(
                (verdict_sig.mismatch_category, stored.spine_relation.as_deref()),
                ("rustc_o0_o2", Some("rustc_o0_vs_o2"))
                    | ("miri_vs_rustc", Some("miri_vs_rustc_o0"))
            ));
    if !category_ok {
        return false;
    }
    if verdict_sig.mismatch_category == "metamorphic_duality" {
        if !metamorphic_relations_match_verdict(
            &stored.metamorphic_relations,
            &verdict_sig.metamorphic_relations,
            verdict,
        ) {
            return false;
        }
    } else if !stored.metamorphic_relations.is_empty() || !stored.metamorphic_leg_kinds.is_empty() {
        return false;
    }
    if stored.mismatch_category == "spine_mismatch" {
        if let Some(expected_rel) = verdict_sig.spine_relation.as_deref()
            && stored.spine_relation.as_deref() != Some(expected_rel)
        {
            return false;
        }
    } else if stored.spine_relation.is_some() {
        return false;
    }
    if verdict_sig.ref_ub_class.is_some() && stored.ref_ub_class != verdict_sig.ref_ub_class {
        return false;
    }
    if stored.ref_ub_class.is_some() && stored.ref_outcome_kind != "fault_ub" {
        return false;
    }
    if verdict_sig.lean_ub_class.is_some() && stored.lean_ub_class != verdict_sig.lean_ub_class {
        return false;
    }
    if stored.lean_ub_class.is_some() && stored.lean_outcome_kind != "fault_ub" {
        return false;
    }
    if stored.mismatch_category == "spurious_lean_ub"
        && stored.lean_outcome_kind != "none"
        && stored.lean_outcome_kind != "fault_ub"
    {
        return false;
    }
    true
}

pub(crate) fn is_valid_bundle_suffix(suffix: &str) -> bool {
    let is_lower_hex = |s: &str| s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    if let Some((skel, content)) = suffix.split_once('_') {
        skel.len() == 12 && is_lower_hex(skel) && content.len() == 24 && is_lower_hex(content)
    } else {
        suffix.len() == 12 && is_lower_hex(suffix)
    }
}

fn stage_temp_bytes(dir: &Path, body: &[u8]) -> Result<tempfile::NamedTempFile, String> {
    let tmp = tempfile::NamedTempFile::new_in(dir)
        .map_err(|e| format!("create atomic temp file in {}: {e}", dir.display()))?;
    fs::write(tmp.path(), body)
        .map_err(|e| format!("write atomic temp {}: {e}", tmp.path().display()))?;
    tmp.as_file()
        .sync_all()
        .map_err(|e| format!("sync atomic temp {}: {e}", tmp.path().display()))?;
    Ok(tmp)
}

pub(crate) fn atomic_write_bytes(path: &Path, body: &[u8]) -> Result<(), String> {
    let parent = match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    fs::create_dir_all(parent)
        .map_err(|e| format!("create parent dir {}: {e}", parent.display()))?;
    let tmp = stage_temp_bytes(parent, body)?;
    tmp.persist(path).map_err(|e| format!("persist {}: {}", path.display(), e.error))?;
    Ok(())
}

pub(crate) fn atomic_write_text(path: &Path, body: &str) -> Result<(), String> {
    atomic_write_bytes(path, body.as_bytes())
}

fn commit_staged_bundle_group(staged: Vec<(tempfile::NamedTempFile, &Path)>) -> Result<(), String> {
    let mut backups: Vec<(&Path, Option<Vec<u8>>)> = Vec::with_capacity(staged.len());
    for (_, dst) in &staged {
        let prev =
            match fs::symlink_metadata(dst) {
                Ok(meta) => {
                    if !meta.is_file() {
                        return Err(format!(
                            "persist {}: destination exists and is not a regular file",
                            dst.display()
                        ));
                    }
                    Some(fs::read(dst).map_err(|e| {
                        format!("read existing {} before replace: {e}", dst.display())
                    })?)
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
                Err(e) => return Err(format!("stat destination {}: {e}", dst.display())),
            };
        backups.push((dst, prev));
    }

    for (idx, (tmp, dst)) in staged.into_iter().enumerate() {
        if let Err(e) = tmp.persist(dst) {
            for (prev_dst, prev_bytes) in backups[..idx].iter().rev() {
                match prev_bytes {
                    Some(bytes) => {
                        let _ = atomic_write_bytes(prev_dst, bytes);
                    }
                    None => {
                        let _ = fs::remove_file(prev_dst);
                    }
                }
            }
            return Err(format!("persist {}: {}", backups[idx].0.display(), e.error));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn confirm_final_shrink_outcome_marks_failed_reproduction_without_budget_exhaustion() {
        let generous =
            ShrinkBudget { max_evals: 8, max_duration: std::time::Duration::from_secs(60) };
        let eval_count = std::cell::Cell::new(1usize);
        let stats = std::cell::RefCell::new(ShrinkPassStats::default());
        let (hit_budget, final_confirmed, succeeded) = confirm_final_shrink_outcome(
            false,
            "old_confirmed_key",
            "new_best_key",
            &eval_count,
            generous,
            std::time::Duration::from_millis(1),
            &stats,
            || false,
        );
        assert!(!hit_budget);
        assert!(!final_confirmed);
        assert!(!succeeded);
        assert_eq!(eval_count.get(), 2);
        assert_eq!(stats.borrow().final_full_confirmations, 1);

        let eval_count_b = std::cell::Cell::new(5usize);
        let stats_b = std::cell::RefCell::new(ShrinkPassStats::default());
        let (hit_budget_b, final_confirmed_b, succeeded_b) = confirm_final_shrink_outcome(
            true,
            "k1",
            "k2",
            &eval_count_b,
            generous,
            std::time::Duration::from_millis(1),
            &stats_b,
            || unreachable!("must not evaluate when budget already exhausted"),
        );
        assert!(hit_budget_b);
        assert!(!final_confirmed_b);
        assert!(succeeded_b);

        // Consuming exact `max_evals` with `budget_hit == false` must still
        // block an extra `full_eval` confirmation pass.
        let exact_budget =
            ShrinkBudget { max_evals: 4, max_duration: std::time::Duration::from_secs(60) };
        let eval_count_exact = std::cell::Cell::new(4usize);
        let stats_exact = std::cell::RefCell::new(ShrinkPassStats::default());
        let (hit_exact, conf_exact, succ_exact) = confirm_final_shrink_outcome(
            false,
            "cached_earlier",
            "best_key",
            &eval_count_exact,
            exact_budget,
            std::time::Duration::from_millis(1),
            &stats_exact,
            || unreachable!("must not confirm past max_evals"),
        );
        assert!(hit_exact);
        assert!(!conf_exact);
        assert!(succ_exact);
        assert_eq!(eval_count_exact.get(), 4);
        assert_eq!(stats_exact.borrow().full_oracle_evaluations, 0);

        // Elapsed wall-clock >= `max_duration` with remaining eval slots must
        // likewise report budget exhaustion instead of calling `full_eval`.
        let eval_count_time = std::cell::Cell::new(2usize);
        let stats_time = std::cell::RefCell::new(ShrinkPassStats::default());
        let (hit_time, conf_time, succ_time) = confirm_final_shrink_outcome(
            false,
            "cached_earlier",
            "best_key",
            &eval_count_time,
            generous,
            generous.max_duration,
            &stats_time,
            || unreachable!("must not confirm past max_duration"),
        );
        assert!(hit_time);
        assert!(!conf_time);
        assert!(succ_time);
        assert_eq!(eval_count_time.get(), 2);
        assert_eq!(stats_time.borrow().full_oracle_evaluations, 0);
    }

    #[test]
    fn commit_staged_bundle_group_rolls_back_created_and_overwritten_files() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let created = tmp.path().join("repro_new.rs");
        let existing = tmp.path().join("program_old.mir.lean");
        fs::write(&existing, b"original-lean-bytes").unwrap();
        let missing_parent = tmp.path().join("nonexistent_subdir").join("witness.json");

        let s0 = stage_temp_bytes(tmp.path(), b"new-rust-bytes").unwrap();
        let s1 = stage_temp_bytes(tmp.path(), b"overwritten-lean-bytes").unwrap();
        let s2 = stage_temp_bytes(tmp.path(), b"witness-json-bytes").unwrap();

        let res = commit_staged_bundle_group(vec![
            (s0, created.as_path()),
            (s1, existing.as_path()),
            (s2, missing_parent.as_path()),
        ]);
        assert!(res.is_err(), "expected third persist to fail on missing parent");
        assert!(!created.exists(), "newly created member must be removed on rollback");
        assert_eq!(
            fs::read(&existing).unwrap(),
            b"original-lean-bytes",
            "pre-existing member must be restored verbatim on rollback"
        );
    }

    #[test]
    fn write_to_dir_with_extra_rejects_escaping_paths_before_creating_dir() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let prog = FuzzProgram {
            seed: 0x3402,
            index: 0,
            input_x: 1,
            input_y: 2,
            steps: vec![FuzzStep::ArithImm { op: FuzzArithOp::Add, imm: 1 }],
            applied_mutators: Vec::new(),
        };
        let sr = shrink_fuzz_program_with_budget(&prog, ShrinkBudget::default(), |p| {
            !p.steps.is_empty()
        });
        let verdict = TraceVerdict::UnsoundAccept { detail: "direct bundle extra guard".into() };
        let art = WitnessArtifact::from_shrink("safe_case", verdict.clone(), verdict, sr);
        let bundle = WitnessBundle::try_from_witness(art, None).unwrap();

        let wdir = tmp.path().join("bundles");
        let sentinel = tmp.path().join("sentinel.witness.json");
        fs::write(&sentinel, b"keep").unwrap();
        for bad_extra in [
            wdir.join("../sentinel.witness.json"),
            tmp.path().join("outside.witness.json"),
            wdir.join("nested").join("child.witness.json"),
            wdir.join(".."),
        ] {
            let err = bundle.write_to_dir_with_extra(&wdir, &[(&bad_extra, b"{}")]).unwrap_err();
            assert!(err.contains("escapes witness dir"), "err={err}");
        }
        assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
        assert!(!wdir.exists());
    }
}
