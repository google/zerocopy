// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Post-shrink semantic bug deduplication, `K <= 8` witness skeleton archive,
//! Semantic Crash Bucketing (`SCB`) post-patch replay classifier, and
//! vendor-neutral `anneal-known-bug/v1` record generation.

use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

use serde::{Deserialize, Serialize};

use crate::{
    CaseReport, RustcDualResult,
    fuzzer::FuzzProgram,
    lean_trace_runner::LeanTraceMode,
    outcome::{
        AuthorityRunResult, MetamorphicStatus, SpineCompareMode, TerminalOutcome, TraceVal,
        TraceVerdict, UbFaultClass, classify_ub_fault_detail, compare_spines,
        compare_ub_fault_results, sha256_hex,
    },
    shrink::{
        ShrinkFailureSignature, ShrinkableCase, WitnessArtifact, all_handles_defined_and_typed,
        canonical_fuzz_program_skeleton_hash, canonical_shrinkable_artifact_id_with_authority,
        canonical_shrinkable_case_skeleton_hash, canonical_witness_artifact_id_with_authority,
        extract_fuzz_program_construct_tags_with_schedule, is_valid_bundle_suffix,
        normalize_lean_fault_site_kind, pinned_metamorphic_relations,
        render_standalone_fuzz_repro_rs_for_relations, render_standalone_mir_lean,
        render_standalone_shrinkable_mir_lean, render_standalone_shrinkable_repro_rs_for_signature,
        sanitize_auth_tag, validate_shrinkable_case_env_schedule, verdict_is_metamorphic_duality,
    },
    trace_observer::{EnvSchedule, ObservableEvent},
};

/// Maximum retained distinct minimal skeleton witnesses per canonical `BugId`
/// (`SCB` post-patch replay bucket cap).
pub const MAX_WITNESSES_PER_BUG: usize = 8;

/// Canonical source identifier for bugs reported by `anneal-itree-diff`.
pub const ITREE_FUZZER_SOURCE: &str = "itree_diff_fuzzer";

/// Canonical schema tag for emitted `KnownBugRecord` rows.
pub const KNOWN_BUG_RECORD_SCHEMA: &str = "anneal-known-bug/v1";

/// Lifecycle status of a canonical deduplicated bug record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BugStatus {
    Open,
    Triaged,
    Fixed,
}

impl BugStatus {
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "open" => Some(Self::Open),
            "triaged" => Some(Self::Triaged),
            "fixed" => Some(Self::Fixed),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::Triaged => "triaged",
            Self::Fixed => "fixed",
        }
    }
}

/// Deterministic normalized authority-outcome key covering `verdict_class`
/// alongside normalized Miri, Lean, and `anneal-mir-eval` fault/refusal
/// diagnostics so artifact IDs never alias distinct canonical bugs.
pub(crate) fn canonical_authorities_detail_key(
    sig: &ShrinkFailureSignature,
    rustc_dual: Option<&RustcDualResult>,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
) -> String {
    let vc = derive_verdict_class_for_authorities(sig, rustc_dual, miri, lean, mir_eval);
    let miri_cause = normalize_miri_ub_cause(miri);
    let lean_cause = normalize_lean_fault_or_accept_kind(lean);
    let mev_cause = normalize_mir_eval_fault_or_accept_kind(mir_eval);
    format!("vc={vc}|miri={miri_cause}|lean={lean_cause}|mev={mev_cause}")
}

/// Convenience wrapper deriving [`canonical_authorities_detail_key`] from an
/// authoritative [`CaseReport`].
pub(crate) fn canonical_case_report_authority_detail_key(
    sig: &ShrinkFailureSignature,
    report: &CaseReport,
) -> String {
    canonical_authorities_detail_key(
        sig,
        Some(&report.rustc_dual),
        report.miri.as_ref(),
        report.lean.as_ref(),
        report.mir_eval.as_ref(),
    )
}

/// Dialect key identifying MIR profile semantics and driver stepping mode.
pub fn dialect_key_for_mode(mode: LeanTraceMode, profile_v2: bool) -> &'static str {
    if profile_v2 {
        "mir_v2_tree_borrows"
    } else {
        match mode {
            LeanTraceMode::StrictVerbatim => "mir_v1_strict",
            LeanTraceMode::CompositionalITree => "mir_v1_itree",
        }
    }
}

/// Normalize Miri's UB diagnostic into a canonical `<ub_class>:<sub_cause>`
/// string with raw pointer addresses, allocation IDs, and numeric offsets
/// stripped so identical root causes hash identically.
pub fn normalize_miri_ub_cause(miri: Option<&AuthorityRunResult>) -> String {
    let Some(m) = miri else {
        return "none".to_string();
    };
    let TerminalOutcome::FaultUb { detail } = &m.outcome else {
        return "none".to_string();
    };
    let cls = classify_ub_fault_detail(detail);
    let cls_slug = ub_fault_class_slug(cls);
    let lower = detail.to_ascii_lowercase();

    let sub = if lower.contains("tree borrows") && lower.contains("write") {
        "tree_borrows_disabled_write"
    } else if lower.contains("tree borrows") && lower.contains("read") {
        "tree_borrows_disabled_read"
    } else if lower.contains("tree borrows") {
        "tree_borrows_forbidden"
    } else if lower.contains("borrow stack") {
        "stacked_borrows_forbidden"
    } else if lower.contains("dangling") || lower.contains("use-after-free") {
        "dangling_or_use_after_free"
    } else if lower.contains("out-of-bounds") {
        "out_of_bounds"
    } else if lower.contains("null pointer") {
        "null_pointer_deref"
    } else if lower.contains("misaligned") || lower.contains("with alignment") {
        "misaligned_pointer"
    } else if lower.contains("immutable allocation") {
        "write_to_immutable"
    } else if lower.contains("uninitialized") {
        "uninitialized_value"
    } else if lower.contains("invalid boolean")
        || lower.contains("constructing invalid value") && lower.contains("bool")
    {
        "invalid_bool"
    } else if lower.contains("invalid char") || lower.contains("surrogate") {
        "invalid_char"
    } else if lower.contains("invalid discriminant") || lower.contains("invalid enum") {
        "invalid_discriminant"
    } else if lower.contains("unchecked_shl")
        || lower.contains("unchecked_shr")
        || lower.contains("overflowing shift")
    {
        "unchecked_shift_overflow"
    } else if lower.contains("unchecked_sub") {
        "unchecked_sub_overflow"
    } else if lower.contains("unchecked_add") {
        "unchecked_add_overflow"
    } else if lower.contains("unchecked_mul") {
        "unchecked_mul_overflow"
    } else if lower.contains("division by zero") || lower.contains("dividing by zero") {
        "div_by_zero"
    } else if lower.contains("remainder by zero") || lower.contains("divisor of zero") {
        "rem_by_zero"
    } else if lower.contains("min / -1") || lower.contains("overflow in signed") {
        "signed_div_overflow"
    } else if lower.contains("unreachable") {
        "unreachable_entered"
    } else if lower.contains("scheduled returnbytes") {
        "scheduled_return_decode"
    } else {
        return format!("{cls_slug}:generic:{}", normalized_diagnostic_digest12(detail));
    };
    format!("{cls_slug}:{sub}")
}

fn strip_volatile_diagnostic_tokens(text: &str) -> String {
    let lower = text.to_ascii_lowercase();
    let bytes = lower.as_bytes();
    let mut out = String::with_capacity(bytes.len());
    let mut i = 0;
    let is_alnum = |b: u8| b.is_ascii_alphanumeric();
    while i < bytes.len() {
        let prev_is_ident = i > 0 && (is_alnum(bytes[i - 1]) || bytes[i - 1] == b'_');
        if !prev_is_ident && bytes[i..].starts_with(b"alloc") {
            let mut j = i + 5;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 5 && (j == bytes.len() || (!is_alnum(bytes[j]) && bytes[j] != b'_')) {
                out.push_str("alloc<id>");
                if j + 1 < bytes.len()
                    && bytes[j] == b'+'
                    && !bytes[j + 1..].starts_with(b"0x")
                    && bytes[j + 1].is_ascii_digit()
                {
                    let mut k = j + 1;
                    while k < bytes.len() && bytes[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k == bytes.len() || (!is_alnum(bytes[k]) && bytes[k] != b'_') {
                        out.push_str("+<n>");
                        i = k;
                        continue;
                    }
                }
                i = j;
                continue;
            }
        }
        if !prev_is_ident && bytes[i..].starts_with(b"0x") {
            let mut j = i + 2;
            while j < bytes.len() && bytes[j].is_ascii_hexdigit() {
                j += 1;
            }
            if j > i + 2 && (j == bytes.len() || (!is_alnum(bytes[j]) && bytes[j] != b'_')) {
                out.push_str("0x<hex>");
                i = j;
                continue;
            }
        }
        if bytes[i] == b'<' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 && j < bytes.len() && bytes[j] == b'>' {
                out.push_str("<tag>");
                i = j + 1;
                continue;
            }
        }
        if !prev_is_ident {
            let kw_len = if bytes[i..].starts_with(b"offset") {
                Some(6)
            } else if bytes[i..].starts_with(b"tag") || bytes[i..].starts_with(b"pid") {
                Some(3)
            } else {
                None
            };
            if let Some(len) = kw_len {
                let delim_pos = i + len;
                if delim_pos < bytes.len() && matches!(bytes[delim_pos], b' ' | b':' | b'=') {
                    let mut p = delim_pos;
                    while p < bytes.len() && matches!(bytes[p], b' ' | b':' | b'=') {
                        p += 1;
                    }
                    if p < bytes.len() && bytes[p].is_ascii_digit() {
                        let mut j = p + 1;
                        while j < bytes.len() && bytes[j].is_ascii_digit() {
                            j += 1;
                        }
                        if j == bytes.len() || (!is_alnum(bytes[j]) && bytes[j] != b'_') {
                            out.push_str(&lower[i..p]);
                            out.push_str("<n>");
                            i = j;
                            continue;
                        }
                    }
                }
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn normalized_diagnostic_digest12(text: &str) -> String {
    let norm = strip_volatile_diagnostic_tokens(text);
    sha256_hex(norm.as_bytes())[..12].to_string()
}

fn trace_val_shape_tag(val: &TraceVal) -> String {
    match val {
        TraceVal::Scalar { kind, .. } => format!("scalar:{}", kind.rust_name()),
        TraceVal::Bool { .. } => "bool".to_string(),
        TraceVal::Char { .. } => "char".to_string(),
        TraceVal::Ordering { .. } => "ordering".to_string(),
        TraceVal::Unit => "unit".to_string(),
        TraceVal::Enum { type_name, .. } => format!("enum:{type_name}"),
        TraceVal::Tuple { fields } => {
            let parts: Vec<String> = fields.iter().map(trace_val_shape_tag).collect();
            format!("tuple({})", parts.join(","))
        }
        TraceVal::PaddedBytes { type_name, bytes } => {
            format!("padded:{type_name}:{}", bytes.len())
        }
    }
}

fn normalize_non_miri_fault_or_refusal_tag(outcome: &TerminalOutcome) -> String {
    let site = normalize_lean_fault_site_kind(outcome);
    match outcome {
        TerminalOutcome::FaultUb { detail } => {
            if site == "unclassified_ub" {
                format!("fault_ub:unclassified_ub:{}", normalized_diagnostic_digest12(detail))
            } else {
                format!("fault_ub:{site}")
            }
        }
        TerminalOutcome::CaptureRefused { reason } => {
            if site == "capture_refused" {
                format!("capture_refused:{}", normalized_diagnostic_digest12(reason))
            } else {
                format!("capture_refused:{site}")
            }
        }
        TerminalOutcome::Returned { .. } => "returned".to_string(),
        TerminalOutcome::Unwound { .. } => "unwound".to_string(),
        TerminalOutcome::Aborted { .. } => "aborted".to_string(),
        TerminalOutcome::Diverged { .. } => "diverged".to_string(),
    }
}

fn twin_outcomes_match(a: &AuthorityRunResult, b: &AuthorityRunResult) -> bool {
    if matches!(a.outcome, TerminalOutcome::FaultUb { .. })
        && matches!(b.outcome, TerminalOutcome::FaultUb { .. })
    {
        compare_ub_fault_results(a, b).is_ok()
    } else {
        a.outcome.semantically_eq(&b.outcome)
    }
}

fn format_twin_leg_token(auth: &AuthorityRunResult, is_miri: bool, eq_group: usize) -> String {
    let base = match &auth.outcome {
        TerminalOutcome::Returned { ret, .. } => {
            format!("returned({})@eq{eq_group}", trace_val_shape_tag(ret))
        }
        TerminalOutcome::Unwound { .. } => format!("unwound@eq{eq_group}"),
        TerminalOutcome::Aborted { .. } => format!("aborted@eq{eq_group}"),
        TerminalOutcome::Diverged { .. } => "diverged".to_string(),
        TerminalOutcome::FaultUb { .. } if is_miri => {
            format!("fault_ub:{}", normalize_miri_ub_cause(Some(auth)))
        }
        TerminalOutcome::FaultUb { .. } | TerminalOutcome::CaptureRefused { .. } => {
            normalize_non_miri_fault_or_refusal_tag(&auth.outcome)
        }
    };
    let mut extras = Vec::new();
    if !auth.caller_frame_law.is_satisfied() {
        let mut flags = String::new();
        if !auth.caller_frame_law.caller_locals_preserved {
            flags.push('L');
        }
        if !auth.caller_frame_law.untouched_alloc_bytes_preserved {
            flags.push('M');
        }
        if !auth.caller_frame_law.padding_mask_respected {
            flags.push('P');
        }
        if flags.is_empty() {
            flags.push('V');
        }
        extras.push(format!("frame[{flags}]"));
    }
    let call_spine: Vec<&'static str> = auth
        .spine
        .erased_call_spine()
        .into_iter()
        .map(|ev| match ev {
            ObservableEvent::CallEnter { .. } => "enter",
            ObservableEvent::CallReturn { .. } => "ret",
            ObservableEvent::CallUnwind { .. } => "unwind",
            ObservableEvent::BranchTag { .. } => "branch",
            ObservableEvent::CallerFrameCheck { .. } => "chk",
        })
        .collect();
    if !call_spine.is_empty() {
        extras.push(format!("calls[{}]", call_spine.join(">")));
    }
    if extras.is_empty() { base } else { format!("{base}+{}", extras.join("+")) }
}

/// Format a deterministic summary of all metamorphic twin legs preserving
/// normalized UB/refusal fault causes, return shape tags, relative cross-leg
/// outcome equivalence groups, caller-frame violation flags, and call-spine
/// structure.
pub(crate) fn format_metamorphic_twin_summary(
    called_rustc: &RustcDualResult,
    called_miri: Option<&AuthorityRunResult>,
    twin_rustc: &RustcDualResult,
    twin_miri: Option<&AuthorityRunResult>,
    called_lean: &AuthorityRunResult,
    inlined_lean: &AuthorityRunResult,
) -> String {
    let legs: [(&str, bool, Option<&AuthorityRunResult>, bool); 8] = [
        ("called_o0", called_rustc.skipped_for_ub, Some(&called_rustc.o0), false),
        ("called_o2", called_rustc.skipped_for_ub, Some(&called_rustc.o2), false),
        ("called_miri", false, called_miri, true),
        ("inlined_o0", twin_rustc.skipped_for_ub, Some(&twin_rustc.o0), false),
        ("inlined_o2", twin_rustc.skipped_for_ub, Some(&twin_rustc.o2), false),
        ("inlined_miri", false, twin_miri, true),
        ("called_lean", false, Some(called_lean), false),
        ("inlined_lean", false, Some(inlined_lean), false),
    ];
    let mut eq_reps: Vec<&AuthorityRunResult> = Vec::new();
    let mut parts = Vec::with_capacity(legs.len());
    for (name, skipped, opt_auth, is_miri) in legs {
        let tok: Cow<'static, str> = if skipped {
            Cow::Borrowed("skipped")
        } else if let Some(auth) = opt_auth {
            let group_id =
                if let Some(idx) = eq_reps.iter().position(|rep| twin_outcomes_match(rep, auth)) {
                    idx
                } else {
                    eq_reps.push(auth);
                    eq_reps.len() - 1
                };
            Cow::Owned(format_twin_leg_token(auth, is_miri, group_id))
        } else {
            Cow::Borrowed("none")
        };
        parts.push(format!("{name}={tok}"));
    }
    parts.join(",")
}

fn ub_fault_class_slug(cls: UbFaultClass) -> &'static str {
    match cls {
        UbFaultClass::ScheduledReturnDecode => "scheduled_return_decode",
        UbFaultClass::UnreachableOrNoUnwind => "unreachable_or_nounwind",
        UbFaultClass::UncheckedShiftOverflow => "unchecked_shift_overflow",
        UbFaultClass::UncheckedArithOrDivOverflow => "unchecked_arith_or_div_overflow",
        UbFaultClass::PointerOrMemoryAccess => "pointer_or_memory_access",
        UbFaultClass::InvalidValueOrUninit => "invalid_value_or_uninit",
        UbFaultClass::Unclassified => "unclassified",
    }
}

/// Normalize Lean outcome into a canonical `lean_fault_or_accept_kind` tag.
pub fn normalize_lean_fault_or_accept_kind(lean: Option<&AuthorityRunResult>) -> String {
    let Some(l) = lean else {
        return "none".to_string();
    };
    normalize_non_miri_fault_or_refusal_tag(&l.outcome)
}

/// Derive canonical `verdict_class` from [`ShrinkFailureSignature`], retaining
/// all minimized authority outcome tags even for non-UB divergences.
pub fn derive_verdict_class(sig: &ShrinkFailureSignature) -> String {
    if sig.verdict_kind == "unsound_accept" {
        if sig.mismatch_category == "metamorphic_duality" && !sig.metamorphic_relations.is_empty() {
            let mut rels: BTreeSet<&str> =
                sig.metamorphic_relations.iter().map(String::as_str).collect();
            if rels.is_empty() {
                rels.insert("metamorphic_unspecified");
            }
            let joined: Vec<&str> = rels.into_iter().collect();
            let legs = sig.metamorphic_leg_kinds.trim();
            if legs.is_empty() {
                format!("unsound_accept:metamorphic_duality:{}", joined.join("+"))
            } else {
                format!("unsound_accept:metamorphic_duality:{}:{}", joined.join("+"), legs)
            }
        } else if sig.mismatch_category == "spine_mismatch"
            && let Some(rel) = sig.spine_relation.as_deref().filter(|s| !s.is_empty())
        {
            format!(
                "unsound_accept:spine_mismatch:{rel}:ref={}:lean={}",
                sig.ref_outcome_kind, sig.lean_outcome_kind
            )
        } else {
            format!(
                "unsound_accept:{}:ref={}:lean={}",
                sig.mismatch_category, sig.ref_outcome_kind, sig.lean_outcome_kind
            )
        }
    } else if sig.verdict_kind == "undeclared_ub_fault" {
        format!(
            "undeclared_ub_fault:spurious_lean_ub:ref={}:lean={}",
            sig.ref_outcome_kind, sig.lean_outcome_kind
        )
    } else {
        format!(
            "{}:{}:ref={}:lean={}",
            sig.verdict_kind, sig.mismatch_category, sig.ref_outcome_kind, sig.lean_outcome_kind
        )
    }
}

/// Normalize optional `anneal-mir-eval` outcome and fault cause into a stable
/// fingerprint tag.
pub fn normalize_mir_eval_fault_or_accept_kind(mir_eval: Option<&AuthorityRunResult>) -> String {
    let Some(me) = mir_eval else {
        return "none".to_string();
    };
    normalize_non_miri_fault_or_refusal_tag(&me.outcome)
}

fn outcome_kind_or_none(auth: Option<&AuthorityRunResult>) -> &'static str {
    auth.map(|a| a.outcome.kind_tag()).unwrap_or("none")
}

fn derive_verdict_class_for_authorities(
    sig: &ShrinkFailureSignature,
    rustc_dual: Option<&RustcDualResult>,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
) -> String {
    let base = derive_verdict_class(sig);
    let mir_eval_norm = normalize_mir_eval_fault_or_accept_kind(mir_eval);
    if sig.mismatch_category == "metamorphic_duality"
        && !sig.metamorphic_leg_kinds.trim().is_empty()
    {
        if mir_eval.is_some() {
            return format!("{base}|mir_eval:{mir_eval_norm}");
        }
        return base;
    }
    let (o0_tag, o2_tag) = match rustc_dual {
        Some(dual) if dual.skipped_for_ub => ("skipped", "skipped"),
        Some(dual) => (dual.o0.outcome.kind_tag(), dual.o2.outcome.kind_tag()),
        None => ("none", "none"),
    };
    let miri_tag = outcome_kind_or_none(miri);
    let lean_tag = outcome_kind_or_none(lean);
    format!(
        "{base}|legs=o0:{o0_tag},o2:{o2_tag},miri:{miri_tag},lean:{lean_tag},mir_eval:{mir_eval_norm}"
    )
}

/// Derive canonical `witness_polarity` tag from a 1-minimal signature.
pub fn derive_witness_polarity(sig: &ShrinkFailureSignature) -> &'static str {
    match sig.mismatch_category {
        "spurious_lean_ub" => "spurious_lean_ub",
        "missed_ub" | "ub_cause_mismatch" => "unsound_missed_ub",
        "spine_mismatch" => "unsound_spine_mismatch",
        "caller_frame_law" => "unsound_caller_frame",
        "metamorphic_duality" => "unsound_metamorphic",
        _ => "unsound_value_mismatch",
    }
}

/// Derive canonical severity tier (`P0`/`P1`/`P2`) from a failure signature.
pub fn derive_severity(sig: &ShrinkFailureSignature) -> &'static str {
    if sig.verdict_kind == "unsound_accept" {
        "P0"
    } else if sig.verdict_kind == "undeclared_ub_fault" {
        "P1"
    } else {
        "P2"
    }
}

/// Multi-view post-1-minimal-shrink canonical semantic fingerprint (`O(1)`,
/// zero LLM/API spend).
///
/// Fields (1)-(6) form the primary root-cause bucket key hashed into
/// `BugId = "ITREE-<CAT>-<12hex>"`, while `minimized_skeleton_hash` serves as
/// the secondary sub-cluster witness key for `K <= 8` SCB replay.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanonicalBugFingerprint {
    // --- Primary Bucket Key ---
    pub branch_scope: String,
    pub dialect_key: String,
    pub verdict_class: String,
    pub mir_construct_sig: Vec<String>,
    pub miri_ub_class: String,
    pub lean_fault_or_accept_kind: String,

    // --- Secondary Sub-Cluster Witness Key ---
    pub minimized_skeleton_hash: String,
}

impl CanonicalBugFingerprint {
    /// Construct a normalized [`CanonicalBugFingerprint`], sorting and
    /// deduplicating `mir_construct_sig`.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        branch_scope: impl Into<String>,
        dialect_key: impl Into<String>,
        verdict_class: impl Into<String>,
        mir_construct_sig: Vec<String>,
        miri_ub_class: impl Into<String>,
        lean_fault_or_accept_kind: impl Into<String>,
        minimized_skeleton_hash: impl Into<String>,
    ) -> Self {
        let dedup_sig: BTreeSet<String> = mir_construct_sig.into_iter().collect();
        Self {
            branch_scope: branch_scope.into(),
            dialect_key: dialect_key.into(),
            verdict_class: verdict_class.into(),
            mir_construct_sig: dedup_sig.into_iter().collect(),
            miri_ub_class: miri_ub_class.into(),
            lean_fault_or_accept_kind: lean_fault_or_accept_kind.into(),
            minimized_skeleton_hash: minimized_skeleton_hash.into(),
        }
    }

    /// Build a [`CanonicalBugFingerprint`] from a verified 1-minimal
    /// [`WitnessArtifact`] and fallback [`CaseReport`], preferring the
    /// minimized candidate's retained [`CaseReport`] on `witness` so
    /// authority outcomes match the minimized reproducer rather than the
    /// pre-shrink input, and failing closed when the shrink did not converge to
    /// 1-minimality.
    pub fn from_1_minimal_witness(
        witness: &WitnessArtifact,
        report: &CaseReport,
        branch_scope: &str,
        dialect_key: &str,
        schedule: Option<&EnvSchedule>,
    ) -> Result<Self, String> {
        if !witness.shrink.succeeded
            || !witness.shrink.is_one_minimal
            || !witness.shrink.converged_1_minimal
            || witness.shrink.budget_exhausted
        {
            return Err(format!(
                "cannot compute canonical BugId before converged 1-minimal shrink without budget exhaustion (succeeded={}, is_one_minimal={}, converged_1_minimal={}, budget_exhausted={})",
                witness.shrink.succeeded,
                witness.shrink.is_one_minimal,
                witness.shrink.converged_1_minimal,
                witness.shrink.budget_exhausted
            ));
        }
        if let (Some(explicit), Some(stored)) = (schedule, witness.repro_schedule.as_ref())
            && explicit != stored
        {
            return Err(format!(
                "explicit schedule conflicts with stored witness repro_schedule for `{}`",
                witness.case_id
            ));
        }
        witness.shrink.minimized.validate()?;
        let (auth_report, sig) = resolve_authoritative_signature(witness, report)?;
        let eff_schedule = schedule.or(witness.repro_schedule.as_ref());
        let construct_sig = extract_fuzz_program_construct_tags_with_schedule(
            &witness.shrink.minimized,
            eff_schedule,
        );
        let skel_hash =
            canonical_fuzz_program_skeleton_hash(&witness.shrink.minimized, eff_schedule);
        Ok(Self::new(
            branch_scope,
            dialect_key,
            derive_verdict_class_for_authorities(
                &sig,
                Some(&auth_report.rustc_dual),
                auth_report.miri.as_ref(),
                auth_report.lean.as_ref(),
                auth_report.mir_eval.as_ref(),
            ),
            construct_sig,
            normalize_miri_ub_cause(auth_report.miri.as_ref()),
            normalize_lean_fault_or_accept_kind(auth_report.lean.as_ref()),
            skel_hash,
        ))
    }

    /// Build a [`CanonicalBugFingerprint`] from a converged [`ShrinkableCase`].
    pub fn from_shrinkable_case(
        case: &ShrinkableCase,
        sig: &ShrinkFailureSignature,
        rustc_dual: Option<&RustcDualResult>,
        miri: Option<&AuthorityRunResult>,
        lean: Option<&AuthorityRunResult>,
        branch_scope: &str,
        dialect_key: &str,
    ) -> Self {
        let canon = case.canonical_alpha_renamed();
        let construct_sig = canon.extract_mir_construct_tags();
        let skel_hash = canonical_shrinkable_case_skeleton_hash(&canon);
        Self::new(
            branch_scope,
            dialect_key,
            derive_verdict_class_for_authorities(sig, rustc_dual, miri, lean, None),
            construct_sig,
            normalize_miri_ub_cause(miri),
            normalize_lean_fault_or_accept_kind(lean),
            skel_hash,
        )
    }

    /// Short uppercase category code (`<= 8` ASCII chars) embedded in
    /// `ITREE-<CAT>-<12hex>`.
    pub fn short_category_code(&self) -> &'static str {
        if self.verdict_class.contains("metamorphic_duality") {
            "METADUAL"
        } else if self.verdict_class.contains("missed_ub") {
            "MISSUB"
        } else if self.verdict_class.contains("ub_cause_mismatch") {
            "UBCAUSE"
        } else if self.verdict_class.contains("spurious_lean_ub") {
            "SPURUB"
        } else if self.verdict_class.contains("spine_mismatch") {
            "SPINEMIS"
        } else if self.verdict_class.contains("caller_frame_law") {
            "CALLFRM"
        } else if self.verdict_class.contains("rustc_o0_o2") {
            "RUSTCOPT"
        } else if self.verdict_class.contains("miri_vs_rustc") {
            "MIRIRUST"
        } else if self.verdict_class.contains("strict_probe_accepted_multicall") {
            "STRICTM"
        } else if self.verdict_class.contains("terminal_outcome_mismatch") {
            "VALMIS"
        } else {
            "SEMDIV"
        }
    }

    /// Deterministic primary bucket `BugId = "ITREE-<CAT>-<12hex>"` computed
    /// over canonical root-cause key fields (`dialect_key`, `verdict_class`,
    /// sorted/deduped `mir_construct_sig`, `miri_ub_class`, and
    /// `lean_fault_or_accept_kind`), independent of `branch_scope` so the same
    /// bug observed on `unstable_only` and `main` merges into `"both"`.
    pub fn bug_id(&self) -> String {
        let mut sorted_sig = self.mir_construct_sig.clone();
        sorted_sig.sort();
        sorted_sig.dedup();
        let canonical = serde_json::json!([
            self.dialect_key,
            self.verdict_class,
            sorted_sig,
            self.miri_ub_class,
            self.lean_fault_or_accept_kind,
        ]);
        let payload = serde_json::to_string(&canonical).unwrap_or_default();
        let hex12 = &sha256_hex(payload.as_bytes())[..12];
        format!("ITREE-{}-{hex12}", self.short_category_code())
    }

    /// Canonical `ReproCaseId = "repro_<minimized_skeleton_hash>"`.
    pub fn repro_case_id(&self) -> String {
        format!("repro_{}", self.minimized_skeleton_hash)
    }
}

/// Retained minimal skeleton witness inside a [`BugBucket`] (capped at
/// `K = 8`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RetainedWitness {
    pub minimized_skeleton_hash: String,
    pub repro_case_id: String,
    pub signature: ShrinkFailureSignature,
    pub fingerprint: CanonicalBugFingerprint,
    #[serde(default)]
    pub program: Option<FuzzProgram>,
    #[serde(default)]
    pub shrinkable_case: Option<ShrinkableCase>,
    #[serde(default)]
    pub repro_schedule: Option<EnvSchedule>,
    pub repro_rust_source: String,
    pub mir_lean_source: String,
    pub first_seen_sha: String,
    pub evals: usize,
    pub converged_1_minimal: bool,
}

/// Provisional unshrunk/budget-cut finding held separately from canonical
/// `BugBucket`s until re-shrunk to 1-minimality.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvisionalFinding {
    pub case_id: String,
    pub verdict: String,
    pub reason: String,
    pub commit_sha: String,
}

/// Outcome of recording a witness into [`BugRegistry`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DedupRecordOutcome {
    /// Net-new canonical `BugId` opened for the first time.
    NewBug { bug_id: String, repro_case_id: String, severity: String },
    /// Existing `BugId` hit with a net-new skeleton added to the `K <= 8` pool.
    NewSkeletonAttached { bug_id: String, repro_case_id: String, retained_count: usize },
    /// Duplicate hit matching an already-known `BugId` and skeleton (or pool
    /// full).
    DuplicateHit { bug_id: String, repro_case_id: String, hit_count: u64 },
    /// Non-1-minimal / provisional failure held out of canonical `BugId` table.
    Provisional { reason: String },
}

/// Sub-cluster archive bucket representing one deduplicated canonical bug.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BugBucket {
    pub bug_id: String,
    pub repo: String,
    pub branch_scope: String,
    pub exposed_on_main: bool,
    pub dialect_key: String,
    pub source: String,
    pub status: BugStatus,
    pub severity: String,
    pub witness_polarity: String,
    pub primary_fingerprint: CanonicalBugFingerprint,
    pub summary: String,
    pub tracking_url: String,
    pub repro_case_id: String,
    pub introduced_sha: String,
    pub fixed_sha: String,
    pub witnesses: Vec<RetainedWitness>,
    pub hit_count: u64,
    #[serde(default)]
    pub split_children: Vec<String>,
}

/// Vendor-neutral public known-bug record
/// (`schema_version = "anneal-known-bug/v1"`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnownBugRecord {
    pub schema_version: String,
    pub repo: String,
    pub bug_id: String,
    pub branch_scope: String,
    pub exposed_on_main: bool,
    pub dialect_key: String,
    pub source: String,
    pub status: String,
    pub severity: String,
    pub witness_polarity: String,
    pub summary: String,
    pub tracking_url: String,
    pub repro_case_id: String,
    pub introduced_sha: String,
    pub fixed_sha: String,
}

/// Known-bug object embedded inside `anneal-itree-semantic-detail/v1` rows.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticsDetailKnownBug {
    pub bug_id: String,
    pub branch_scope: String,
    pub exposed_on_main: bool,
    pub mir_dialect: String,
    pub source: String,
    pub status: String,
    pub severity: String,
    pub witness_polarity: String,
    pub summary: String,
    pub tracking_issue: String,
    pub repro_case_id: String,
    pub introduced_sha: String,
    pub resolved_by_commit: Option<String>,
}

fn validate_branch_scope_and_exposure(
    subject: &str,
    branch_scope: &str,
    exposed_on_main: bool,
) -> Result<(), String> {
    match (branch_scope, exposed_on_main) {
        ("unstable_only", false) | ("main", true) | ("both", true) => Ok(()),
        ("unstable_only", true) => Err(format!(
            "{subject} has contradictory branch_scope=\"unstable_only\" with exposed_on_main=true"
        )),
        ("main" | "both", false) => Err(format!(
            "{subject} has contradictory branch_scope={branch_scope:?} with exposed_on_main=false"
        )),
        (other, _) => Err(format!(
            "{subject} has invalid branch_scope {other:?} (expected \"unstable_only\", \"main\", or \"both\")"
        )),
    }
}

fn validate_bug_lifecycle_fields(
    bug_id: &str,
    branch_scope: &str,
    exposed_on_main: bool,
    status_raw: &str,
    introduced_sha: &str,
    resolution_sha: Option<&str>,
    sha_field: &str,
) -> Result<(), String> {
    if bug_id.trim().is_empty() {
        return Err("known bug record missing bug_id".to_string());
    }
    validate_branch_scope_and_exposure(
        &format!("known bug {bug_id}"),
        branch_scope,
        exposed_on_main,
    )?;
    if !crate::telemetry::is_40_hex_sha(introduced_sha) {
        return Err(format!(
            "known bug {bug_id} introduced_sha must be a 40-character hexadecimal Git SHA, got {introduced_sha:?}"
        ));
    }
    let status = BugStatus::parse(status_raw)
        .ok_or_else(|| format!("known bug {bug_id} has invalid status {status_raw:?}"))?;
    let res_raw = resolution_sha.unwrap_or("");
    let has_sha = !res_raw.trim().is_empty();
    match (status, has_sha) {
        (BugStatus::Fixed, false) => {
            Err(format!("known bug {bug_id} marked fixed without non-empty {sha_field}"))
        }
        (BugStatus::Fixed, true) => {
            if !crate::telemetry::is_valid_git_commit_sha(res_raw) {
                return Err(format!(
                    "known bug {bug_id} {sha_field} must be a non-zero 40-character hexadecimal Git SHA, got {res_raw:?}"
                ));
            }
            Ok(())
        }
        (BugStatus::Open | BugStatus::Triaged, true) => Err(format!(
            "known bug {bug_id} has status {:?} with non-empty {sha_field}",
            status.as_str()
        )),
        (BugStatus::Open | BugStatus::Triaged, false) => {
            if !res_raw.is_empty() {
                return Err(format!(
                    "known bug {bug_id} has status {:?} with whitespace-only {sha_field}",
                    status.as_str()
                ));
            }
            Ok(())
        }
    }
}

impl SemanticsDetailKnownBug {
    /// Enforce structural and lifecycle invariants (non-empty `bug_id`, valid
    /// 40-hex `introduced_sha`, consistent `branch_scope`/`exposed_on_main`,
    /// valid [`BugStatus`] vocabulary, and non-zero 40-hex
    /// `resolved_by_commit` present iff `fixed`) on embedded `known_bugs`.
    pub fn validate(&self) -> Result<(), String> {
        validate_bug_lifecycle_fields(
            &self.bug_id,
            &self.branch_scope,
            self.exposed_on_main,
            &self.status,
            &self.introduced_sha,
            self.resolved_by_commit.as_deref(),
            "resolved_by_commit",
        )
    }
}

impl KnownBugRecord {
    /// Enforce structural and lifecycle invariants (including `schema_version`,
    /// non-empty `bug_id`, valid 40-hex `introduced_sha`, consistent
    /// `branch_scope`/`exposed_on_main`, valid `status` vocabulary, and
    /// non-zero 40-hex `fixed_sha` present iff `fixed`).
    pub fn validate(&self) -> Result<(), String> {
        if self.schema_version != KNOWN_BUG_RECORD_SCHEMA {
            return Err(format!(
                "unexpected known bug schema_version {:?} for bug {}",
                self.schema_version, self.bug_id
            ));
        }
        validate_bug_lifecycle_fields(
            &self.bug_id,
            &self.branch_scope,
            self.exposed_on_main,
            &self.status,
            &self.introduced_sha,
            Some(&self.fixed_sha),
            "fixed_sha",
        )
    }
}

impl BugBucket {
    fn validate_bucket_identity(&self) -> Result<(), String> {
        if self.witnesses.is_empty() {
            return Err(format!("bug bucket {} has no retained witnesses", self.bug_id));
        }
        if self.witnesses.len() > MAX_WITNESSES_PER_BUG {
            return Err(format!(
                "bug bucket {} retains {} witnesses, exceeding MAX_WITNESSES_PER_BUG ({MAX_WITNESSES_PER_BUG})",
                self.bug_id,
                self.witnesses.len()
            ));
        }
        if self.dialect_key.trim().is_empty() {
            return Err(format!("bug bucket {} missing non-empty dialect_key", self.bug_id));
        }
        if self.dialect_key != self.primary_fingerprint.dialect_key {
            return Err(format!(
                "bug bucket {} dialect_key {:?} does not match primary_fingerprint dialect_key {:?}",
                self.bug_id, self.dialect_key, self.primary_fingerprint.dialect_key
            ));
        }
        if self.branch_scope != self.primary_fingerprint.branch_scope {
            return Err(format!(
                "bug bucket {} branch_scope {:?} does not match primary_fingerprint branch_scope {:?}",
                self.bug_id, self.branch_scope, self.primary_fingerprint.branch_scope
            ));
        }
        validate_bug_lifecycle_fields(
            &self.bug_id,
            &self.branch_scope,
            self.exposed_on_main,
            self.status.as_str(),
            &self.introduced_sha,
            Some(&self.fixed_sha),
            "fixed_sha",
        )?;
        let expected_root = self.primary_fingerprint.bug_id();
        let mut retained_scope = String::new();
        for w in &self.witnesses {
            validate_retained_witness_representation(&self.bug_id, w)?;
            let base_vc = derive_verdict_class(&w.signature);
            if w.fingerprint.verdict_class != base_vc
                && !w
                    .fingerprint
                    .verdict_class
                    .strip_prefix(&base_vc)
                    .is_some_and(|rest| rest.starts_with('|'))
            {
                return Err(format!(
                    "bug bucket {} retained witness `{}` signature contradicts verdict_class {:?}",
                    self.bug_id, w.repro_case_id, w.fingerprint.verdict_class
                ));
            }
            let w_exposed = w.fingerprint.branch_scope != "unstable_only";
            validate_branch_scope_and_exposure(
                &format!("bug bucket {} retained witness {}", self.bug_id, w.repro_case_id),
                &w.fingerprint.branch_scope,
                w_exposed,
            )?;
            retained_scope = merge_branch_scope(&retained_scope, &w.fingerprint.branch_scope);
            if w.fingerprint.dialect_key != self.dialect_key {
                return Err(format!(
                    "bug bucket {} retains witness {} with dialect_key {:?} outside bucket dialect_key {:?}",
                    self.bug_id, w.repro_case_id, w.fingerprint.dialect_key, self.dialect_key
                ));
            }
            let w_root = w.fingerprint.bug_id();
            if w_root != expected_root {
                return Err(format!(
                    "bug bucket {} retains witness {} with mismatched root fingerprint {}",
                    self.bug_id, w.repro_case_id, w_root
                ));
            }
        }
        let retained_exposed = retained_scope != "unstable_only";
        if self.branch_scope != retained_scope || self.exposed_on_main != retained_exposed {
            return Err(format!(
                "bug bucket {} branch_scope/exposed_on_main ({:?}, {}) disagrees with retained witness scope union ({:?}, {})",
                self.bug_id,
                self.branch_scope,
                self.exposed_on_main,
                retained_scope,
                retained_exposed
            ));
        }
        let Some(repro_wit) = self.witnesses.iter().find(|w| w.repro_case_id == self.repro_case_id)
        else {
            return Err(format!(
                "bug bucket {} repro_case_id `{}` is absent from retained witnesses",
                self.bug_id, self.repro_case_id
            ));
        };
        let expected_severity = derive_severity(&repro_wit.signature);
        if self.severity != expected_severity {
            return Err(format!(
                "bug bucket {} severity {:?} disagrees with retained witness `{}` severity {:?}",
                self.bug_id, self.severity, self.repro_case_id, expected_severity
            ));
        }
        let expected_polarity = derive_witness_polarity(&repro_wit.signature);
        if self.witness_polarity != expected_polarity {
            return Err(format!(
                "bug bucket {} witness_polarity {:?} disagrees with retained witness `{}` polarity {:?}",
                self.bug_id, self.witness_polarity, self.repro_case_id, expected_polarity
            ));
        }
        if self.bug_id == expected_root {
            return Ok(());
        }
        let Some(suffix) = self.bug_id.strip_prefix(&format!("{expected_root}-")) else {
            return Err(format!(
                "bug bucket bug_id `{}` does not match primary_fingerprint bug_id `{}`",
                self.bug_id, expected_root
            ));
        };
        let is_lower_hex = |s: &str, min_len: usize| {
            s.len() >= min_len && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
        };
        let valid_skel_match = |cand: &str, allow_prefix6: bool| -> bool {
            self.primary_fingerprint.minimized_skeleton_hash == cand
                || (allow_prefix6
                    && skeleton_prefix6(&self.primary_fingerprint.minimized_skeleton_hash) == cand)
                || self.witnesses.iter().any(|w| {
                    w.minimized_skeleton_hash == cand
                        || (allow_prefix6 && skeleton_prefix6(&w.minimized_skeleton_hash) == cand)
                })
        };
        let validate_resplit_tail = |tail: &str| -> Result<(), String> {
            let parts: Vec<&str> = tail.split("-resplit-").collect();
            for mid in &parts[..parts.len() - 1] {
                let skel_part = mid.rsplit_once('-').map_or(*mid, |(h, idx)| {
                    if !idx.is_empty() && idx.bytes().all(|b| b.is_ascii_digit()) {
                        h
                    } else {
                        *mid
                    }
                });
                if !is_lower_hex(skel_part, 6) {
                    return Err(format!(
                        "bug bucket `{}` has invalid intermediate resplit component `{mid}`",
                        self.bug_id
                    ));
                }
            }
            let last = parts[parts.len() - 1];
            let last_skel = last.rsplit_once('-').map_or(last, |(h, idx)| {
                if !idx.is_empty() && idx.bytes().all(|b| b.is_ascii_digit()) { h } else { last }
            });
            if is_lower_hex(last_skel, 6) && valid_skel_match(last_skel, false) {
                return Ok(());
            }
            Err(format!(
                "bug bucket `{}` resplit tail `{last}` does not match retained witness skeleton under `{}`",
                self.bug_id, expected_root
            ))
        };
        if let Some(root_resplit_tail) = suffix.strip_prefix("resplit-") {
            return validate_resplit_tail(root_resplit_tail);
        }
        if !suffix.contains("-resplit-") {
            if is_lower_hex(suffix, 6) && valid_skel_match(suffix, suffix.len() == 6) {
                return Ok(());
            }
            return Err(format!(
                "bug bucket split bug_id `{}` suffix `{suffix}` does not match any retained witness skeleton under `{}`",
                self.bug_id, expected_root
            ));
        }
        let Some((split_parent, rest_tail)) = suffix.split_once("-resplit-") else {
            return Err(format!("bug bucket `{}` has malformed resplit prefix", self.bug_id));
        };
        if !is_lower_hex(split_parent, 6) {
            return Err(format!(
                "bug bucket `{}` has invalid split-parent skeleton `{split_parent}`",
                self.bug_id
            ));
        }
        validate_resplit_tail(rest_tail)
    }

    /// Generate the vendor-neutral `anneal-known-bug/v1` record for this
    /// bucket.
    pub fn to_known_bug_record(&self) -> Result<KnownBugRecord, String> {
        self.validate_bucket_identity()?;
        let rec = KnownBugRecord {
            schema_version: KNOWN_BUG_RECORD_SCHEMA.to_string(),
            repo: self.repo.clone(),
            bug_id: self.bug_id.clone(),
            branch_scope: self.branch_scope.clone(),
            exposed_on_main: self.exposed_on_main,
            dialect_key: self.dialect_key.clone(),
            source: self.source.clone(),
            status: self.status.as_str().to_string(),
            severity: self.severity.clone(),
            witness_polarity: self.witness_polarity.clone(),
            summary: truncate_utf8_bytes(&self.summary, 1024),
            tracking_url: self.tracking_url.clone(),
            repro_case_id: self.repro_case_id.clone(),
            introduced_sha: self.introduced_sha.clone(),
            fixed_sha: self.fixed_sha.clone(),
        };
        rec.validate()?;
        Ok(rec)
    }

    /// Generate the `anneal-itree-semantic-detail/v1` `known_bugs` entry.
    pub fn to_semantics_detail_entry(&self) -> Result<SemanticsDetailKnownBug, String> {
        self.validate_bucket_identity()?;
        let entry = SemanticsDetailKnownBug {
            bug_id: self.bug_id.clone(),
            branch_scope: self.branch_scope.clone(),
            exposed_on_main: self.exposed_on_main,
            mir_dialect: self.dialect_key.clone(),
            source: self.source.clone(),
            status: self.status.as_str().to_string(),
            severity: self.severity.clone(),
            witness_polarity: self.witness_polarity.clone(),
            summary: truncate_utf8_bytes(&self.summary, 1024),
            tracking_issue: self.tracking_url.clone(),
            repro_case_id: self.repro_case_id.clone(),
            introduced_sha: self.introduced_sha.clone(),
            resolved_by_commit: if self.fixed_sha.is_empty() {
                None
            } else {
                Some(self.fixed_sha.clone())
            },
        };
        entry.validate()?;
        Ok(entry)
    }
}

fn validate_retained_witness_representation(
    bucket_id: &str,
    w: &RetainedWitness,
) -> Result<(), String> {
    if !w.converged_1_minimal {
        return Err(format!(
            "bug bucket {bucket_id} retains non-1-minimal witness {}",
            w.repro_case_id
        ));
    }
    validate_signature_shape(&w.signature).map_err(|err| {
        format!("bug bucket {bucket_id} witness {} has invalid signature: {err}", w.repro_case_id)
    })?;
    if w.fingerprint.miri_ub_class != "none" {
        let Some(ref_cls) = w.signature.ref_ub_class else {
            return Err(format!(
                "bug bucket {bucket_id} witness {} has miri_ub_class {:?} without ref_ub_class",
                w.repro_case_id, w.fingerprint.miri_ub_class
            ));
        };
        let expected_prefix = format!("{}:", ub_fault_class_slug(ref_cls));
        if !w.fingerprint.miri_ub_class.starts_with(&expected_prefix) {
            return Err(format!(
                "bug bucket {bucket_id} witness {} ref_ub_class {ref_cls:?} disagrees with miri_ub_class {:?}",
                w.repro_case_id, w.fingerprint.miri_ub_class
            ));
        }
    }
    if w.signature.mismatch_category == "metamorphic_duality"
        && w.signature.metamorphic_relations.is_empty()
    {
        return Err(format!(
            "bug bucket {bucket_id} witness {} uses metamorphic_duality without relations",
            w.repro_case_id
        ));
    }
    let Some(artifact_id) = w.repro_case_id.strip_prefix("repro_") else {
        return Err(format!(
            "bug bucket {bucket_id} witness {:?} missing `repro_` prefix",
            w.repro_case_id
        ));
    };
    if !artifact_id.contains('_') || !is_valid_bundle_suffix(artifact_id) {
        return Err(format!(
            "bug bucket {bucket_id} witness {} has noncanonical artifact suffix {artifact_id:?}",
            w.repro_case_id
        ));
    }
    let (expected_skel, expected_tags, expected_lean, expected_rust) = match (
        &w.program,
        &w.shrinkable_case,
    ) {
        (Some(prog), None) => {
            prog.validate().map_err(|err| {
                format!(
                    "bug bucket {bucket_id} retains invalid minimized FuzzProgram {}: {err}",
                    w.repro_case_id
                )
            })?;
            let eff_sched = w.repro_schedule.as_ref();
            let skel = canonical_fuzz_program_skeleton_hash(prog, eff_sched);
            let tags: Vec<String> =
                extract_fuzz_program_construct_tags_with_schedule(prog, eff_sched)
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
            let lean_src = render_standalone_mir_lean(prog, eff_sched, artifact_id);
            let is_meta = w.signature.mismatch_category == "metamorphic_duality";
            let pinned = pinned_metamorphic_relations(&TraceVerdict::Agree, Some(&w.signature));
            let rust_src = render_standalone_fuzz_repro_rs_for_relations(
                prog,
                eff_sched,
                artifact_id,
                is_meta,
                &pinned,
            );
            (skel, tags, lean_src, rust_src)
        }
        (None, Some(case)) => {
            if !all_handles_defined_and_typed(&case.steps, &case.helpers) {
                return Err(format!(
                    "bug bucket {bucket_id} retains ShrinkableCase {} failing static validation",
                    w.repro_case_id
                ));
            }
            validate_shrinkable_case_env_schedule(case).map_err(|err| {
                format!(
                    "bug bucket {bucket_id} retains ShrinkableCase {} with invalid schedule: {err}",
                    w.repro_case_id
                )
            })?;
            let canon = case.canonical_alpha_renamed();
            if &canon != case {
                return Err(format!(
                    "bug bucket {bucket_id} retains non-canonical ShrinkableCase {}",
                    w.repro_case_id
                ));
            }
            let skel = canonical_shrinkable_case_skeleton_hash(&canon);
            let tags: Vec<String> = canon
                .extract_mir_construct_tags()
                .into_iter()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let lean_src = render_standalone_shrinkable_mir_lean(&canon, artifact_id)?;
            let rust_src = render_standalone_shrinkable_repro_rs_for_signature(
                &canon,
                artifact_id,
                Some(&w.signature),
            );
            (skel, tags, lean_src, rust_src)
        }
        (Some(_), Some(_)) | (None, None) => {
            return Err(format!(
                "bug bucket {bucket_id} witness {} must carry strictly one representation (`program` or `shrinkable_case`)",
                w.repro_case_id
            ));
        }
    };
    if w.minimized_skeleton_hash != expected_skel
        || w.fingerprint.minimized_skeleton_hash != expected_skel
        || !artifact_id.starts_with(&expected_skel)
    {
        return Err(format!(
            "bug bucket {bucket_id} witness {} skeleton disagrees with canonical representation",
            w.repro_case_id
        ));
    }
    if w.fingerprint.mir_construct_sig != expected_tags {
        return Err(format!(
            "bug bucket {bucket_id} witness {} mir_construct_sig disagrees with representation",
            w.repro_case_id
        ));
    }
    if w.mir_lean_source != expected_lean {
        return Err(format!(
            "bug bucket {bucket_id} witness {} mir_lean_source diverges from representation",
            w.repro_case_id
        ));
    }
    if w.repro_rust_source != expected_rust {
        return Err(format!(
            "bug bucket {bucket_id} witness {} repro_rust_source diverges from representation",
            w.repro_case_id
        ));
    }
    Ok(())
}

fn truncate_utf8_bytes(s: &str, max_bytes: usize) -> String {
    if s.len() <= max_bytes {
        return s.to_string();
    }
    let mut end = max_bytes;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    s[..end].to_string()
}

/// Format a bounded (`<= 1024` byte) human-readable known-bug summary.
pub fn format_bug_summary(
    fp: &CanonicalBugFingerprint,
    evals: usize,
    is_one_minimal: bool,
) -> String {
    let constructs = fp.mir_construct_sig.join(",");
    let raw = format!(
        "[mir={constructs}] Miri={} vs Lean={} (skel={}, evals={evals}, 1min={is_one_minimal})",
        fp.miri_ub_class, fp.lean_fault_or_accept_kind, fp.minimized_skeleton_hash
    );
    truncate_utf8_bytes(&raw, 1024)
}

/// Result of `SCB` (`van Tonder et al., ASE 2018`) post-patch witness replay.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScbReplayVerdict {
    /// Every retained skeleton witness now passes at `fixed_sha`.
    AllFixed { bug_id: String, fixed_sha: String, replayed_count: usize },
    /// All retained skeleton witnesses still fail at `fixed_sha`.
    StillOpen {
        bug_id: String,
        fixed_sha: String,
        failing_skeletons: Vec<String>,
        replayed_count: usize,
    },
    /// Partial fix: some witnesses passed while others still fail, splitting
    /// each failing skeleton into `ITREE-<CAT>-<12hex>-<skel6>` so zero bugs
    /// are silently masked.
    Split {
        original_bug_id: String,
        fixed_sha: String,
        fixed_skeletons: Vec<String>,
        split_bugs: Vec<BugBucket>,
        replayed_count: usize,
    },
}

/// Deterministic post-shrink deduplication registry managing `K <= 8` witness
/// retention and SCB post-patch replay splitting.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BugRegistry {
    pub repo: String,
    pub buckets: BTreeMap<String, BugBucket>,
    #[serde(default)]
    pub provisional_cases: Vec<ProvisionalFinding>,
}

impl BugRegistry {
    pub fn new(repo: impl Into<String>) -> Self {
        Self { repo: repo.into(), buckets: BTreeMap::new(), provisional_cases: Vec::new() }
    }

    /// Record a shrunk [`WitnessArtifact`] + [`CaseReport`], gating strictly on
    /// converged 1-minimality (`succeeded`, `is_one_minimal`,
    /// `converged_1_minimal`, and `!budget_exhausted`).
    #[allow(clippy::too_many_arguments)]
    pub fn record_witness(
        &mut self,
        witness: &WitnessArtifact,
        report: &CaseReport,
        branch_scope: &str,
        exposed_on_main: bool,
        dialect_key: &str,
        head_sha: &str,
        schedule: Option<&EnvSchedule>,
    ) -> DedupRecordOutcome {
        if !witness.shrink.succeeded
            || !witness.shrink.is_one_minimal
            || !witness.shrink.converged_1_minimal
            || witness.shrink.budget_exhausted
        {
            let reason = format!(
                "non-1-minimal or budget-exhausted witness deferred to provisional queue (succeeded={}, is_one_minimal={}, converged_1_minimal={}, budget_exhausted={})",
                witness.shrink.succeeded,
                witness.shrink.is_one_minimal,
                witness.shrink.converged_1_minimal,
                witness.shrink.budget_exhausted
            );
            self.provisional_cases.push(ProvisionalFinding {
                case_id: witness.case_id.clone(),
                verdict: format!("{}", witness.verdict),
                reason: reason.clone(),
                commit_sha: head_sha.to_string(),
            });
            return DedupRecordOutcome::Provisional { reason };
        }
        if let Err(err) = witness.shrink.minimized.validate() {
            let reason = format!(
                "invalid minimized FuzzProgram in witness `{}` deferred to provisional queue: {err}",
                witness.case_id
            );
            self.provisional_cases.push(ProvisionalFinding {
                case_id: witness.case_id.clone(),
                verdict: format!("{}", witness.verdict),
                reason: reason.clone(),
                commit_sha: head_sha.to_string(),
            });
            return DedupRecordOutcome::Provisional { reason };
        }
        if let (Some(explicit), Some(stored)) = (schedule, witness.repro_schedule.as_ref())
            && explicit != stored
        {
            let reason = format!(
                "explicit schedule conflicts with stored witness repro_schedule for `{}`",
                witness.case_id
            );
            self.provisional_cases.push(ProvisionalFinding {
                case_id: witness.case_id.clone(),
                verdict: format!("{}", witness.verdict),
                reason: reason.clone(),
                commit_sha: head_sha.to_string(),
            });
            return DedupRecordOutcome::Provisional { reason };
        }
        if let Err(reason) = validate_branch_scope_and_exposure(
            &format!("witness {}", witness.case_id),
            branch_scope,
            exposed_on_main,
        ) {
            self.provisional_cases.push(ProvisionalFinding {
                case_id: witness.case_id.clone(),
                verdict: format!("{}", witness.verdict),
                reason: reason.clone(),
                commit_sha: head_sha.to_string(),
            });
            return DedupRecordOutcome::Provisional { reason };
        }
        if !crate::telemetry::is_40_hex_sha(head_sha) {
            let reason = format!(
                "witness {} head_sha must be a 40-character hexadecimal Git SHA, got {head_sha:?}",
                witness.case_id
            );
            self.provisional_cases.push(ProvisionalFinding {
                case_id: witness.case_id.clone(),
                verdict: format!("{}", witness.verdict),
                reason: reason.clone(),
                commit_sha: head_sha.to_string(),
            });
            return DedupRecordOutcome::Provisional { reason };
        }

        let (auth_report, sig) = match resolve_authoritative_signature(witness, report) {
            Ok(pair) => pair,
            Err(reason) => {
                self.provisional_cases.push(ProvisionalFinding {
                    case_id: witness.case_id.clone(),
                    verdict: format!("{}", witness.verdict),
                    reason: reason.clone(),
                    commit_sha: head_sha.to_string(),
                });
                return DedupRecordOutcome::Provisional { reason };
            }
        };
        let fp = match CanonicalBugFingerprint::from_1_minimal_witness(
            witness,
            auth_report,
            branch_scope,
            dialect_key,
            schedule,
        ) {
            Ok(fp) => fp,
            Err(reason) => {
                self.provisional_cases.push(ProvisionalFinding {
                    case_id: witness.case_id.clone(),
                    verdict: format!("{}", witness.verdict),
                    reason: reason.clone(),
                    commit_sha: head_sha.to_string(),
                });
                return DedupRecordOutcome::Provisional { reason };
            }
        };

        let skel = fp.minimized_skeleton_hash.clone();
        let eff_schedule = schedule.or(witness.repro_schedule.as_ref());
        let auth_detail = witness
            .minimized_report
            .as_deref()
            .map(|min_rep| canonical_case_report_authority_detail_key(&sig, min_rep));
        let id_verdict = &auth_report.verdict;
        let artifact_id = canonical_witness_artifact_id_with_authority(
            &skel,
            &witness.shrink.minimized,
            eff_schedule,
            Some(&sig),
            id_verdict,
            auth_detail.as_deref(),
        );
        let repro_id = format!("repro_{artifact_id}");
        let mir_lean_source =
            render_standalone_mir_lean(&witness.shrink.minimized, eff_schedule, &artifact_id);
        let is_metamorphic = sig.mismatch_category == "metamorphic_duality"
            || verdict_is_metamorphic_duality(id_verdict);
        let pinned_relations = pinned_metamorphic_relations(id_verdict, Some(&sig));
        let repro_rust_source = render_standalone_fuzz_repro_rs_for_relations(
            &witness.shrink.minimized,
            eff_schedule,
            &artifact_id,
            is_metamorphic,
            &pinned_relations,
        );

        let retained = RetainedWitness {
            minimized_skeleton_hash: skel,
            repro_case_id: repro_id,
            signature: sig.clone(),
            fingerprint: fp.clone(),
            program: Some(witness.shrink.minimized.clone()),
            shrinkable_case: None,
            repro_schedule: eff_schedule.cloned(),
            repro_rust_source,
            mir_lean_source,
            first_seen_sha: head_sha.to_string(),
            evals: witness.shrink.predicate_evaluations,
            converged_1_minimal: witness.shrink.is_one_minimal,
        };

        self.insert_retained_witness(fp, sig, retained, exposed_on_main, head_sha)
    }

    /// Record a converged 1-minimal [`ShrinkableCase`] directly, validating
    /// handle/helper invariants and requiring a standalone `Trusted.MirAst`
    /// Lean artifact before promotion out of provisional state.
    #[allow(clippy::too_many_arguments)]
    pub fn record_shrinkable_case(
        &mut self,
        case: &ShrinkableCase,
        sig: &ShrinkFailureSignature,
        rustc_dual: Option<&RustcDualResult>,
        miri: Option<&AuthorityRunResult>,
        lean: Option<&AuthorityRunResult>,
        branch_scope: &str,
        exposed_on_main: bool,
        dialect_key: &str,
        head_sha: &str,
        evals: usize,
        converged_1_minimal: bool,
    ) -> DedupRecordOutcome {
        let mut push_provisional = |reason: String| -> DedupRecordOutcome {
            self.provisional_cases.push(ProvisionalFinding {
                case_id: case.name.clone(),
                verdict: sig.verdict_kind.to_string(),
                reason: reason.clone(),
                commit_sha: head_sha.to_string(),
            });
            DedupRecordOutcome::Provisional { reason }
        };
        if !converged_1_minimal {
            return push_provisional("ShrinkableCase did not converge to 1-minimal".to_string());
        }
        if let Err(reason) =
            validate_branch_scope_and_exposure("ShrinkableCase", branch_scope, exposed_on_main)
        {
            return push_provisional(reason);
        }
        if !crate::telemetry::is_40_hex_sha(head_sha) {
            return push_provisional(format!(
                "ShrinkableCase head_sha must be a 40-character hexadecimal Git SHA, got {head_sha:?}"
            ));
        }
        if !all_handles_defined_and_typed(&case.steps, &case.helpers) {
            return push_provisional(
                "ShrinkableCase failed static handle/helper validation".to_string(),
            );
        }
        if let Err(reason) = validate_shrinkable_case_env_schedule(case) {
            return push_provisional(reason);
        }
        let mut seen_inputs = BTreeSet::new();
        for inp in &case.inputs {
            if !seen_inputs.insert(inp.local_id)
                || inp.align_hint.is_some_and(|a| a == 0 || !a.is_power_of_two())
            {
                return push_provisional(format!(
                    "ShrinkableCase has duplicate input local_id or invalid align_hint at local {}",
                    inp.local_id
                ));
            }
        }
        if case.slice_len.is_some()
            && (case.slice_align == 0 || !case.slice_align.is_power_of_two())
        {
            return push_provisional("ShrinkableCase has invalid slice_align".to_string());
        }
        if let Err(reason) =
            validate_shrinkable_signature_against_authorities(sig, rustc_dual, miri, lean)
        {
            return push_provisional(reason);
        }
        let canon = case.canonical_alpha_renamed();
        let fp = CanonicalBugFingerprint::from_shrinkable_case(
            &canon,
            sig,
            rustc_dual,
            miri,
            lean,
            branch_scope,
            dialect_key,
        );
        let skel = fp.minimized_skeleton_hash.clone();
        let auth_detail = canonical_authorities_detail_key(sig, rustc_dual, miri, lean, None);
        let artifact_id =
            canonical_shrinkable_artifact_id_with_authority(&skel, &canon, sig, Some(&auth_detail));
        let mir_lean_source = match render_standalone_shrinkable_mir_lean(&canon, &artifact_id) {
            Ok(src) => src,
            Err(reason) => return push_provisional(reason),
        };
        let repro_id = format!("repro_{artifact_id}");
        let repro_rust =
            render_standalone_shrinkable_repro_rs_for_signature(&canon, &artifact_id, Some(sig));
        let retained = RetainedWitness {
            minimized_skeleton_hash: skel,
            repro_case_id: repro_id,
            signature: sig.clone(),
            fingerprint: fp.clone(),
            program: None,
            shrinkable_case: Some(canon),
            repro_schedule: None,
            repro_rust_source: repro_rust,
            mir_lean_source,
            first_seen_sha: head_sha.to_string(),
            evals,
            converged_1_minimal,
        };
        self.insert_retained_witness(fp, sig.clone(), retained, exposed_on_main, head_sha)
    }

    fn insert_retained_witness(
        &mut self,
        fp: CanonicalBugFingerprint,
        sig: ShrinkFailureSignature,
        retained: RetainedWitness,
        exposed_on_main: bool,
        head_sha: &str,
    ) -> DedupRecordOutcome {
        let bug_id = fp.bug_id();
        let repro_id = retained.repro_case_id.clone();

        // 1. If a parent bucket already split via SCB, route re-observations
        //    of split skeletons transitively to their split descendant
        //    (reopening if that child had previously been marked Fixed and
        //    regressed) so a Fixed ancestor never swallows active failures.
        match find_split_target(&self.buckets, &bug_id, &retained.minimized_skeleton_hash) {
            SplitRouteTarget::ExistingChild(child_id) => {
                if let Some(child) = self.buckets.get_mut(&child_id) {
                    return attach_or_reopen_bucket(child, &fp, retained, exposed_on_main);
                }
            }
            SplitRouteTarget::NewSplitChild { parent_id, use_full_skel_id } => {
                let split_id = if use_full_skel_id {
                    format!("{bug_id}-{}", retained.minimized_skeleton_hash)
                } else {
                    let skel6 = skeleton_prefix6(&retained.minimized_skeleton_hash);
                    format!("{bug_id}-{skel6}")
                };
                if let Some(existing) = self.buckets.get_mut(&split_id) {
                    let outcome = attach_or_reopen_bucket(existing, &fp, retained, exposed_on_main);
                    if let Some(parent) = self.buckets.get_mut(&parent_id)
                        && !parent.split_children.contains(&split_id)
                    {
                        parent.split_children.push(split_id);
                    }
                    return outcome;
                }
                let severity = derive_severity(&sig).to_string();
                let mut inserted = make_open_bug_bucket(
                    split_id.clone(),
                    &self.repo,
                    fp,
                    &sig,
                    retained,
                    exposed_on_main,
                    head_sha,
                );
                inserted.split_children = Vec::new();
                self.buckets.insert(split_id.clone(), inserted);
                if let Some(parent) = self.buckets.get_mut(&parent_id)
                    && !parent.split_children.contains(&split_id)
                {
                    parent.split_children.push(split_id.clone());
                }
                return DedupRecordOutcome::NewBug {
                    bug_id: split_id,
                    repro_case_id: repro_id,
                    severity,
                };
            }
            SplitRouteTarget::UseRoot => {}
        }

        if let Some(bucket) = self.buckets.get_mut(&bug_id) {
            return attach_or_reopen_bucket(bucket, &fp, retained, exposed_on_main);
        }

        let severity = derive_severity(&sig).to_string();
        let bucket = make_open_bug_bucket(
            bug_id.clone(),
            &self.repo,
            fp,
            &sig,
            retained,
            exposed_on_main,
            head_sha,
        );
        self.buckets.insert(bug_id.clone(), bucket);
        DedupRecordOutcome::NewBug { bug_id, repro_case_id: repro_id, severity }
    }

    /// `SCB` Post-Patch Replay Classifier (`van Tonder et al., ASE 2018`):
    /// Replay every retained skeleton witness (`<= MAX_WITNESSES_PER_BUG` = 8
    /// per bucket) for `bug_id` against `patch_sha`
    /// (`witness_still_fails(w) -> bool`). `AllFixed` is scoped strictly to
    /// that bounded retained skeleton pool.
    ///
    /// - Fails closed if `bug_id` has 0 retained witnesses (never emits
    ///   `AllFixed` on empty buckets).
    /// - If all witnesses pass, marks `bug_id` as `Fixed` with
    ///   `fixed_sha = patch_sha`.
    /// - If all witnesses still fail, keeps `bug_id` `Open` with empty
    ///   `fixed_sha`.
    /// - If some pass and some still fail, deterministically splits each
    ///   still-failing skeleton into `ITREE-<CAT>-<12hex>-<skel6>` (`Open`),
    ///   removes failing witnesses from the parent bucket, and marks the
    ///   parent `Fixed` at `patch_sha`.
    pub fn classify_post_patch_replay<F>(
        &mut self,
        bug_id: &str,
        patch_sha: &str,
        mut witness_still_fails: F,
    ) -> Result<ScbReplayVerdict, String>
    where
        F: FnMut(&RetainedWitness) -> bool,
    {
        if !crate::telemetry::is_valid_git_commit_sha(patch_sha) {
            return Err(format!(
                "SCB post-patch replay requires a non-zero 40-hex Git patch_sha, got {patch_sha:?}"
            ));
        }
        let bucket_snapshot = self
            .buckets
            .get(bug_id)
            .cloned()
            .ok_or_else(|| format!("unknown bug_id `{bug_id}` in BugRegistry"))?;
        bucket_snapshot.validate_bucket_identity()?;

        if bucket_snapshot.witnesses.is_empty() {
            return Err(format!(
                "cannot classify post-patch replay for `{bug_id}` with 0 retained witnesses"
            ));
        }

        let replayed_count = bucket_snapshot.witnesses.len();
        let mut fixed_skeletons = Vec::new();
        let mut failing_witnesses = Vec::new();

        for w in &bucket_snapshot.witnesses {
            if witness_still_fails(w) {
                failing_witnesses.push(w.clone());
            } else {
                fixed_skeletons.push(w.minimized_skeleton_hash.clone());
            }
        }

        if failing_witnesses.is_empty() {
            if let Some(b) = self.buckets.get_mut(bug_id) {
                b.status = BugStatus::Fixed;
                b.fixed_sha = patch_sha.to_string();
            }
            return Ok(ScbReplayVerdict::AllFixed {
                bug_id: bug_id.to_string(),
                fixed_sha: patch_sha.to_string(),
                replayed_count,
            });
        }

        if fixed_skeletons.is_empty() {
            if let Some(b) = self.buckets.get_mut(bug_id) {
                b.status = BugStatus::Open;
                b.fixed_sha.clear();
            }
            let failing_skeletons =
                failing_witnesses.iter().map(|w| w.minimized_skeleton_hash.clone()).collect();
            return Ok(ScbReplayVerdict::StillOpen {
                bug_id: bug_id.to_string(),
                fixed_sha: String::new(),
                failing_skeletons,
                replayed_count,
            });
        }

        // Mixed pass/fail: SCB deterministic split!
        let root_bug_id = bucket_snapshot.primary_fingerprint.bug_id();
        let failing_skels: BTreeSet<String> =
            failing_witnesses.iter().map(|w| w.minimized_skeleton_hash.clone()).collect();
        let mut skels_per_prefix6: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for fw in &failing_witnesses {
            skels_per_prefix6
                .entry(skeleton_prefix6(&fw.minimized_skeleton_hash))
                .or_default()
                .insert(fw.minimized_skeleton_hash.clone());
        }
        let mut split_by_id: BTreeMap<String, BugBucket> = BTreeMap::new();
        let mut child_ids = Vec::new();

        for fw in failing_witnesses {
            let skel6 = skeleton_prefix6(&fw.minimized_skeleton_hash);
            let has_batch_prefix_collision =
                skels_per_prefix6.get(&skel6).is_some_and(|skels| skels.len() > 1);
            let can_use_candidate = |cand: &str| {
                cand != bug_id
                    && !split_by_id.contains_key(cand)
                    && self.buckets.get(cand).is_none_or(|b| {
                        b.status != BugStatus::Fixed
                            && !b.witnesses.is_empty()
                            && b.witnesses
                                .iter()
                                .all(|w| w.minimized_skeleton_hash == fw.minimized_skeleton_hash)
                    })
            };
            let base_split_id = format!("{root_bug_id}-{skel6}");
            let full_split_id = format!("{root_bug_id}-{}", fw.minimized_skeleton_hash);
            let split_id = if !has_batch_prefix_collision && can_use_candidate(&base_split_id) {
                base_split_id
            } else if can_use_candidate(&full_split_id) {
                full_split_id
            } else {
                let mut resplit = format!("{bug_id}-resplit-{}", fw.minimized_skeleton_hash);
                let mut suffix_idx = 1usize;
                while !can_use_candidate(&resplit) {
                    resplit =
                        format!("{bug_id}-resplit-{}-{suffix_idx}", fw.minimized_skeleton_hash);
                    suffix_idx += 1;
                }
                resplit
            };
            let fw_exposed =
                bucket_snapshot.exposed_on_main && fw.fingerprint.branch_scope != "unstable_only";
            if let Some(existing) = split_by_id.get_mut(&split_id) {
                existing.hit_count += 1;
                if fw_exposed {
                    existing.exposed_on_main = true;
                }
                existing.branch_scope =
                    merge_branch_scope(&existing.branch_scope, &fw.fingerprint.branch_scope);
                existing.primary_fingerprint.branch_scope = merge_branch_scope(
                    &existing.primary_fingerprint.branch_scope,
                    &fw.fingerprint.branch_scope,
                );
                if let Some(slot) = existing
                    .witnesses
                    .iter_mut()
                    .find(|w| w.minimized_skeleton_hash == fw.minimized_skeleton_hash)
                {
                    slot.fingerprint.branch_scope = merge_branch_scope(
                        &slot.fingerprint.branch_scope,
                        &fw.fingerprint.branch_scope,
                    );
                } else if existing.witnesses.len() < MAX_WITNESSES_PER_BUG {
                    existing.witnesses.push(fw);
                }
                continue;
            }
            let summary = format_bug_summary(&fw.fingerprint, fw.evals, fw.converged_1_minimal);
            let child = BugBucket {
                bug_id: split_id.clone(),
                repo: bucket_snapshot.repo.clone(),
                branch_scope: fw.fingerprint.branch_scope.clone(),
                exposed_on_main: fw_exposed,
                dialect_key: fw.fingerprint.dialect_key.clone(),
                source: bucket_snapshot.source.clone(),
                status: BugStatus::Open,
                severity: derive_severity(&fw.signature).to_string(),
                witness_polarity: derive_witness_polarity(&fw.signature).to_string(),
                primary_fingerprint: fw.fingerprint.clone(),
                summary,
                tracking_url: String::new(),
                repro_case_id: fw.repro_case_id.clone(),
                introduced_sha: fw.first_seen_sha.clone(),
                fixed_sha: String::new(),
                witnesses: vec![fw],
                hit_count: 1,
                split_children: Vec::new(),
            };
            child_ids.push(split_id.clone());
            split_by_id.insert(split_id, child);
        }

        let mut split_bugs = Vec::with_capacity(split_by_id.len());
        for (split_id, mut child) in split_by_id {
            if let Some(existing) = self.buckets.get_mut(&split_id) {
                for w in child.witnesses.drain(..) {
                    let fp = w.fingerprint.clone();
                    let exposed =
                        bucket_snapshot.exposed_on_main && fp.branch_scope != "unstable_only";
                    let _ = attach_or_reopen_bucket(existing, &fp, w, exposed);
                }
                split_bugs.push(existing.clone());
            } else {
                split_bugs.push(child.clone());
                self.buckets.insert(split_id, child);
            }
        }

        if let Some(orig) = self.buckets.get_mut(bug_id) {
            orig.witnesses.retain(|w| !failing_skels.contains(&w.minimized_skeleton_hash));
            if let Some(retained_primary) = orig.witnesses.first().cloned() {
                let (recomputed_scope, recomputed_exposed) =
                    recompute_retained_scope(&orig.witnesses);
                if !orig.witnesses.iter().any(|w| w.repro_case_id == orig.repro_case_id) {
                    orig.repro_case_id = retained_primary.repro_case_id.clone();
                    orig.primary_fingerprint = retained_primary.fingerprint.clone();
                    orig.severity = derive_severity(&retained_primary.signature).to_string();
                    orig.witness_polarity =
                        derive_witness_polarity(&retained_primary.signature).to_string();
                }
                let summary_witness = orig
                    .witnesses
                    .iter()
                    .find(|w| w.repro_case_id == orig.repro_case_id)
                    .unwrap_or(&retained_primary);
                orig.branch_scope = recomputed_scope.clone();
                orig.exposed_on_main = recomputed_exposed;
                orig.primary_fingerprint.branch_scope = recomputed_scope;
                orig.summary = format_bug_summary(
                    &orig.primary_fingerprint,
                    summary_witness.evals,
                    summary_witness.converged_1_minimal,
                );
            }
            orig.status = BugStatus::Fixed;
            orig.fixed_sha = patch_sha.to_string();
            for cid in child_ids {
                if !orig.split_children.contains(&cid) {
                    orig.split_children.push(cid);
                }
            }
        }

        Ok(ScbReplayVerdict::Split {
            original_bug_id: bug_id.to_string(),
            fixed_sha: patch_sha.to_string(),
            fixed_skeletons,
            split_bugs,
            replayed_count,
        })
    }

    /// Generate sorted `anneal-known-bug/v1` records across all buckets in this
    /// registry.
    pub fn to_known_bug_records(&self) -> Result<Vec<KnownBugRecord>, String> {
        self.buckets.values().map(BugBucket::to_known_bug_record).collect()
    }

    /// Generate sorted `known_bugs` entries for
    /// `anneal-itree-semantic-detail/v1`.
    pub fn to_semantics_detail_entries(&self) -> Result<Vec<SemanticsDetailKnownBug>, String> {
        self.buckets.values().map(BugBucket::to_semantics_detail_entry).collect()
    }
}

enum SplitRouteTarget {
    UseRoot,
    ExistingChild(String),
    NewSplitChild { parent_id: String, use_full_skel_id: bool },
}

fn find_split_target(
    buckets: &BTreeMap<String, BugBucket>,
    root_id: &str,
    skel_hash: &str,
) -> SplitRouteTarget {
    let Some(root) = buckets.get(root_id) else {
        return SplitRouteTarget::UseRoot;
    };
    if root.split_children.is_empty() {
        return SplitRouteTarget::UseRoot;
    }

    // Traverse reachable split descendants, preferring exact witness match.
    let mut stack = root.split_children.clone();
    let mut visited = BTreeSet::new();
    let mut descendants = Vec::new();
    while let Some(cid) = stack.pop() {
        if !visited.insert(cid.clone()) {
            continue;
        }
        if let Some(child) = buckets.get(&cid) {
            if child.witnesses.iter().any(|w| w.minimized_skeleton_hash == skel_hash) {
                return SplitRouteTarget::ExistingChild(cid);
            }
            for gc in &child.split_children {
                stack.push(gc.clone());
            }
            descendants.push(cid);
        }
    }

    if root.witnesses.iter().any(|w| w.minimized_skeleton_hash == skel_hash) {
        return SplitRouteTarget::UseRoot;
    }

    let skel6 = skeleton_prefix6(skel_hash);
    let expected_child = format!("{root_id}-{skel6}");
    if descendants.contains(&expected_child) || buckets.contains_key(&expected_child) {
        // `expected_child` already holds an unrelated skeleton sharing this
        // 6-hex prefix (whether Open or Fixed), so isolate the new skeleton in
        // a full-12-hex split child under `root_id`.
        return SplitRouteTarget::NewSplitChild {
            parent_id: root_id.to_string(),
            use_full_skel_id: true,
        };
    }

    if root.status == BugStatus::Fixed {
        return SplitRouteTarget::NewSplitChild {
            parent_id: root_id.to_string(),
            use_full_skel_id: false,
        };
    }

    SplitRouteTarget::UseRoot
}

fn merge_branch_scope(existing: &str, incoming: &str) -> String {
    if existing.is_empty() {
        incoming.to_string()
    } else if incoming.is_empty() || existing == incoming {
        existing.to_string()
    } else {
        "both".to_string()
    }
}

fn recompute_retained_scope(witnesses: &[RetainedWitness]) -> (String, bool) {
    let mut scope = String::new();
    for w in witnesses {
        scope = merge_branch_scope(&scope, &w.fingerprint.branch_scope);
    }
    let exposed = scope != "unstable_only";
    (scope, exposed)
}

fn pick_scope_preserving_eviction_idx(
    witnesses: &[RetainedWitness],
    protected_repro_id: &str,
    incoming_scope: &str,
    target_scope: &str,
) -> Option<usize> {
    (0..witnesses.len())
        .rev()
        .find(|&evict_idx| {
            if witnesses[evict_idx].repro_case_id == protected_repro_id {
                return false;
            }
            let mut remaining = incoming_scope.to_string();
            for (idx, w) in witnesses.iter().enumerate() {
                if idx != evict_idx {
                    remaining = merge_branch_scope(&remaining, &w.fingerprint.branch_scope);
                }
            }
            remaining == target_scope
        })
        .or_else(|| witnesses.iter().rposition(|w| w.repro_case_id != protected_repro_id))
}

fn attach_or_reopen_bucket(
    bucket: &mut BugBucket,
    fp: &CanonicalBugFingerprint,
    retained: RetainedWitness,
    exposed_on_main: bool,
) -> DedupRecordOutcome {
    bucket.hit_count += 1;
    let merged_scope = merge_branch_scope(&bucket.branch_scope, &fp.branch_scope);
    let scope_widened = merged_scope != bucket.branch_scope;
    if exposed_on_main {
        bucket.exposed_on_main = true;
    }
    bucket.branch_scope = merged_scope;
    bucket.primary_fingerprint.branch_scope =
        merge_branch_scope(&bucket.primary_fingerprint.branch_scope, &bucket.branch_scope);
    let was_fixed = bucket.status == BugStatus::Fixed;
    if was_fixed {
        // Re-observing an active failure against a previously Fixed bucket
        // reopens it while keeping `introduced_sha` and `tracking_url` intact,
        // and retargets primary metadata to the re-observed failing witness.
        bucket.status = BugStatus::Open;
        bucket.fixed_sha.clear();
        bucket.repro_case_id = retained.repro_case_id.clone();
        bucket.primary_fingerprint = fp.clone();
        bucket.primary_fingerprint.branch_scope = bucket.branch_scope.clone();
        bucket.summary = format_bug_summary(
            &bucket.primary_fingerprint,
            retained.evals,
            retained.converged_1_minimal,
        );
        bucket.severity = derive_severity(&retained.signature).to_string();
        bucket.witness_polarity = derive_witness_polarity(&retained.signature).to_string();
    }
    let already_has_skel = bucket
        .witnesses
        .iter()
        .any(|w| w.minimized_skeleton_hash == retained.minimized_skeleton_hash);
    let repro_id = retained.repro_case_id.clone();
    let sync_bucket_scope = |bucket: &mut BugBucket| {
        let (recomputed_scope, recomputed_exposed) = recompute_retained_scope(&bucket.witnesses);
        bucket.branch_scope = recomputed_scope.clone();
        bucket.exposed_on_main = recomputed_exposed;
        bucket.primary_fingerprint.branch_scope = recomputed_scope;
    };
    if !already_has_skel {
        if bucket.witnesses.len() >= MAX_WITNESSES_PER_BUG
            && (was_fixed || scope_widened)
            && let Some(evict_idx) = pick_scope_preserving_eviction_idx(
                &bucket.witnesses,
                &bucket.repro_case_id,
                &fp.branch_scope,
                &bucket.branch_scope,
            )
        {
            // Retain both prior-branch-scope coverage and `repro_case_id` when
            // evicting to admit a reopening or scope-widening skeleton.
            bucket.witnesses.remove(evict_idx);
        }
        if bucket.witnesses.len() < MAX_WITNESSES_PER_BUG {
            bucket.witnesses.push(retained);
            sync_bucket_scope(bucket);
            return DedupRecordOutcome::NewSkeletonAttached {
                bug_id: bucket.bug_id.clone(),
                repro_case_id: repro_id,
                retained_count: bucket.witnesses.len(),
            };
        }
    } else if let Some(slot) = bucket
        .witnesses
        .iter_mut()
        .find(|w| w.minimized_skeleton_hash == retained.minimized_skeleton_hash)
    {
        let merged_scope = merge_branch_scope(&slot.fingerprint.branch_scope, &fp.branch_scope);
        if was_fixed {
            *slot = retained;
        }
        slot.fingerprint.branch_scope = merged_scope;
    }
    sync_bucket_scope(bucket);
    DedupRecordOutcome::DuplicateHit {
        bug_id: bucket.bug_id.clone(),
        repro_case_id: repro_id,
        hit_count: bucket.hit_count,
    }
}

fn make_open_bug_bucket(
    bug_id: String,
    repo: &str,
    fp: CanonicalBugFingerprint,
    sig: &ShrinkFailureSignature,
    retained: RetainedWitness,
    exposed_on_main: bool,
    head_sha: &str,
) -> BugBucket {
    let summary = format_bug_summary(&fp, retained.evals, retained.converged_1_minimal);
    BugBucket {
        bug_id,
        repo: repo.to_string(),
        branch_scope: fp.branch_scope.clone(),
        exposed_on_main,
        dialect_key: fp.dialect_key.clone(),
        source: ITREE_FUZZER_SOURCE.to_string(),
        status: BugStatus::Open,
        severity: derive_severity(sig).to_string(),
        witness_polarity: derive_witness_polarity(sig).to_string(),
        primary_fingerprint: fp,
        summary,
        tracking_url: String::new(),
        repro_case_id: retained.repro_case_id.clone(),
        introduced_sha: head_sha.to_string(),
        fixed_sha: String::new(),
        witnesses: vec![retained],
        hit_count: 1,
        split_children: Vec::new(),
    }
}

fn skeleton_prefix6(skel_hash: &str) -> String {
    skel_hash.chars().take(6).collect()
}

fn resolve_authoritative_signature<'a>(
    witness: &'a WitnessArtifact,
    report: &'a CaseReport,
) -> Result<(&'a CaseReport, ShrinkFailureSignature), String> {
    if let Some(min_rep) = witness.minimized_report.as_deref() {
        if min_rep.case_id != witness.case_id {
            return Err(format!(
                "minimized report case_id `{}` does not match witness case_id `{}`",
                min_rep.case_id, witness.case_id
            ));
        }
        if min_rep.case_id != report.case_id {
            return Err(format!(
                "minimized report case_id `{}` does not match report case_id `{}`",
                min_rep.case_id, report.case_id
            ));
        }
        let sig = ShrinkFailureSignature::from_case_report(min_rep).ok_or_else(|| {
            format!(
                "minimized report verdict `{}` is not a shrinkable semantic divergence",
                min_rep.verdict
            )
        })?;
        validate_case_report_signature_against_authorities(min_rep, &sig)?;
        if let Some(stored) = witness.signature.as_ref()
            && stored != &sig
        {
            return Err(format!(
                "stored witness signature {stored:?} conflicts with authoritative minimized_report signature {sig:?}"
            ));
        }
        return Ok((min_rep, sig));
    }
    if report.case_id != witness.case_id {
        return Err(format!(
            "fallback report case_id `{}` does not match witness case_id `{}`",
            report.case_id, witness.case_id
        ));
    }
    if witness.verdict != report.verdict {
        return Err(format!(
            "reportless witness verdict `{}` does not match fallback report verdict `{}`",
            witness.verdict, report.verdict
        ));
    }
    let sig = ShrinkFailureSignature::from_case_report(report).ok_or_else(|| {
        format!("cannot derive ShrinkFailureSignature from report verdict {}", report.verdict)
    })?;
    validate_case_report_signature_against_authorities(report, &sig)?;
    if let Some(stored) = witness.signature.as_ref()
        && stored != &sig
    {
        return Err(format!(
            "stored witness signature {stored:?} conflicts with fallback report signature {sig:?}"
        ));
    }
    Ok((report, sig))
}

pub(crate) fn validate_case_report_signature_against_authorities(
    report: &CaseReport,
    sig: &ShrinkFailureSignature,
) -> Result<(), String> {
    validate_signature_against_authorities_common(
        sig,
        Some(&report.rustc_dual),
        report.miri.as_ref(),
        report.lean.as_ref(),
        Some(report),
    )
}

fn validate_shrinkable_signature_against_authorities(
    sig: &ShrinkFailureSignature,
    rustc_dual: Option<&RustcDualResult>,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
) -> Result<(), String> {
    validate_signature_against_authorities_common(sig, rustc_dual, miri, lean, None)
}

fn validate_signature_shape(sig: &ShrinkFailureSignature) -> Result<(), String> {
    if !matches!(sig.verdict_kind, "unsound_accept" | "undeclared_ub_fault") {
        return Err(format!("invalid shrinkable verdict_kind {:?}", sig.verdict_kind));
    }
    let valid_outcome_tag = |tag: &str| {
        matches!(
            tag,
            "returned"
                | "unwound"
                | "aborted"
                | "diverged"
                | "fault_ub"
                | "capture_refused"
                | "none"
        )
    };
    if !valid_outcome_tag(sig.ref_outcome_kind) || !valid_outcome_tag(sig.lean_outcome_kind) {
        return Err(format!(
            "invalid outcome_kind in shrinkable signature: ref={:?}, lean={:?}",
            sig.ref_outcome_kind, sig.lean_outcome_kind
        ));
    }
    if !matches!(
        sig.mismatch_category,
        "metamorphic_duality"
            | "strict_probe_accepted_multicall"
            | "caller_frame_law"
            | "rustc_o0_o2"
            | "miri_vs_rustc"
            | "ub_cause_mismatch"
            | "missed_ub"
            | "spine_mismatch"
            | "terminal_outcome_mismatch"
            | "spurious_lean_ub"
    ) {
        return Err(format!("invalid shrinkable mismatch_category {:?}", sig.mismatch_category));
    }
    if (sig.verdict_kind == "undeclared_ub_fault") != (sig.mismatch_category == "spurious_lean_ub")
    {
        return Err(format!(
            "contradictory verdict_kind {:?} and mismatch_category {:?}",
            sig.verdict_kind, sig.mismatch_category
        ));
    }
    if sig.ref_ub_class.is_some() && sig.ref_outcome_kind != "fault_ub" {
        return Err(format!(
            "ref_ub_class {:?} requires ref_outcome_kind = \"fault_ub\" (got {:?})",
            sig.ref_ub_class, sig.ref_outcome_kind
        ));
    }
    if sig.lean_ub_class.is_some() && sig.lean_outcome_kind != "fault_ub" {
        return Err(format!(
            "lean_ub_class {:?} requires lean_outcome_kind = \"fault_ub\" (got {:?})",
            sig.lean_ub_class, sig.lean_outcome_kind
        ));
    }
    if sig.mismatch_category != "metamorphic_duality"
        && (!sig.metamorphic_relations.is_empty() || !sig.metamorphic_leg_kinds.is_empty())
    {
        return Err("non-metamorphic signature unexpectedly carries metamorphic relation metadata"
            .to_string());
    }
    if sig.mismatch_category != "spine_mismatch" && sig.spine_relation.is_some() {
        return Err("non-spine signature unexpectedly carries spine_relation metadata".to_string());
    }
    Ok(())
}

fn validate_signature_against_authorities_common(
    sig: &ShrinkFailureSignature,
    rustc_dual: Option<&RustcDualResult>,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    case_report: Option<&CaseReport>,
) -> Result<(), String> {
    let label = if case_report.is_some() { "CaseReport" } else { "ShrinkableCase" };
    if rustc_dual.is_some_and(|d| {
        !d.skipped_for_ub && (d.o0.tool_error.is_some() || d.o2.tool_error.is_some())
    }) || miri.is_some_and(|m| m.tool_error.is_some())
        || lean.is_some_and(|l| l.tool_error.is_some())
    {
        return Err(format!("{label} authority result contains a tool_error"));
    }
    let miri_reports_ub =
        miri.is_some_and(|m| matches!(m.outcome, TerminalOutcome::FaultUb { .. }));
    let ignore_host_rustc = miri_reports_ub || rustc_dual.is_some_and(|d| d.skipped_for_ub);
    let checked_for_frame: [Option<&AuthorityRunResult>; 5] = [
        if ignore_host_rustc { None } else { rustc_dual.map(|d| &d.o0) },
        if ignore_host_rustc { None } else { rustc_dual.map(|d| &d.o2) },
        miri,
        lean,
        case_report.and_then(|r| r.mir_eval.as_ref()),
    ];
    let any_accepting_frame_violated = checked_for_frame
        .into_iter()
        .flatten()
        .any(|auth| auth.outcome.is_accepting() && !auth.caller_frame_law.is_satisfied());
    if !matches!(sig.mismatch_category, "caller_frame_law" | "metamorphic_duality")
        && any_accepting_frame_violated
    {
        return Err(format!(
            "{label} authority result violated CallerFrameLaw (must remain provisional)"
        ));
    }
    validate_signature_shape(sig)?;

    let eff_ref =
        miri.or_else(|| rustc_dual.and_then(|d| if d.skipped_for_ub { None } else { Some(&d.o0) }));
    let expected_ref_kind = eff_ref.map(|r| r.outcome.kind_tag()).unwrap_or("none");
    let expected_ref_ub = eff_ref.and_then(|r| match &r.outcome {
        TerminalOutcome::FaultUb { detail } => Some(classify_ub_fault_detail(detail)),
        _ => None,
    });
    if sig.ref_outcome_kind != expected_ref_kind || sig.ref_ub_class != expected_ref_ub {
        return Err(format!(
            "shrinkable signature ref mismatch: sig=({}, {:?}) vs authority=({}, {:?})",
            sig.ref_outcome_kind, sig.ref_ub_class, expected_ref_kind, expected_ref_ub
        ));
    }

    let expected_lean_kind = lean.map(|l| l.outcome.kind_tag()).unwrap_or("none");
    let expected_lean_ub = lean.and_then(|l| match &l.outcome {
        TerminalOutcome::FaultUb { detail } => Some(classify_ub_fault_detail(detail)),
        _ => None,
    });
    let expected_lean_site =
        lean.map(|l| normalize_lean_fault_site_kind(&l.outcome)).unwrap_or_default();
    if sig.lean_outcome_kind != expected_lean_kind
        || sig.lean_ub_class != expected_lean_ub
        || sig.lean_fault_site_kind != expected_lean_site
    {
        return Err(format!(
            "shrinkable signature lean mismatch: sig=({}, {:?}, {:?}) vs authority=({}, {:?}, {:?})",
            sig.lean_outcome_kind,
            sig.lean_ub_class,
            sig.lean_fault_site_kind,
            expected_lean_kind,
            expected_lean_ub,
            expected_lean_site
        ));
    }

    let miri_is_ub = miri.is_some_and(|m| matches!(m.outcome, TerminalOutcome::FaultUb { .. }));
    let ref_is_ub = matches!(eff_ref.map(|r| &r.outcome), Some(TerminalOutcome::FaultUb { .. }));
    let skipped_for_ub = rustc_dual.is_some_and(|d| d.skipped_for_ub);
    let lean_is_ub = matches!(lean.map(|l| &l.outcome), Some(TerminalOutcome::FaultUb { .. }));
    let lean_is_refusal =
        matches!(lean.map(|l| &l.outcome), Some(TerminalOutcome::CaptureRefused { .. }));

    let eff_ref_matches_lean = |r: &AuthorityRunResult, l: &AuthorityRunResult| -> bool {
        if l.post_only_mem_digest && !r.post_only_mem_digest {
            r.outcome.semantically_eq_post_only(&l.outcome)
        } else {
            r.outcome.semantically_eq(&l.outcome)
        }
    };

    let ensure_prior_authority_parity = |context: &str| -> Result<(), String> {
        if miri_is_ub {
            return Ok(());
        }
        if let Some(d) = rustc_dual.filter(|d| !d.skipped_for_ub) {
            if !d.parity_ok || !d.o0.outcome.semantically_eq(&d.o2.outcome) {
                return Err(format!(
                    "{context} cannot promote before host rustc O0/O2 parity passes"
                ));
            }
            if let Some(m) = miri.filter(|m| m.outcome.is_accepting())
                && (!m.outcome.semantically_eq(&d.o0.outcome)
                    || compare_spines(
                        "miri",
                        &m.spine,
                        "rustc-O0",
                        &d.o0.spine,
                        SpineCompareMode::FullBranchesAndCalls,
                    )
                    .is_err())
            {
                return Err(format!(
                    "{context} cannot promote before Miri vs rustc-O0 outcome and spine parity pass"
                ));
            }
        }
        Ok(())
    };

    match sig.mismatch_category {
        "missed_ub" => {
            if !ref_is_ub || !lean.is_some_and(|l| l.outcome.is_terminating_accepting()) {
                return Err(
                    "missed_ub signature requires FaultUb reference authority evidence and terminating accepting Lean outcome"
                        .to_string(),
                );
            }
            ensure_prior_authority_parity("missed_ub")?;
        }
        "ub_cause_mismatch" => {
            let (Some(r), Some(l)) = (eff_ref, lean) else {
                return Err("ub_cause_mismatch signature requires both reference and Lean results"
                    .to_string());
            };
            if !ref_is_ub || !lean_is_ub {
                return Err(
                    "ub_cause_mismatch signature requires FaultUb on both reference and Lean"
                        .to_string(),
                );
            }
            ensure_prior_authority_parity("ub_cause_mismatch")?;
            if compare_ub_fault_results(r, l).is_ok() {
                return Err(
                    "ub_cause_mismatch signature contradicts compatible reference and Lean FaultUb results"
                        .to_string(),
                );
            }
        }
        "spurious_lean_ub" => {
            if !lean_is_ub
                || skipped_for_ub
                || !eff_ref.is_some_and(|r| r.outcome.is_terminating_accepting())
            {
                return Err(
                    "spurious_lean_ub signature requires FaultUb on Lean and terminating accepting non-UB reference"
                        .to_string(),
                );
            }
            ensure_prior_authority_parity("spurious_lean_ub")?;
        }
        "rustc_o0_o2"
            if miri_is_ub
                || !rustc_dual.is_some_and(|d| {
                    !d.skipped_for_ub
                        && !d.parity_ok
                        && !d.o0.outcome.semantically_eq(&d.o2.outcome)
                }) =>
        {
            return Err(
                "rustc_o0_o2 signature requires non-UB Miri and non-skipped rustc_dual outcome divergence (`parity_ok = false`)"
                    .to_string(),
            );
        }
        "rustc_o0_o2" => {}
        "miri_vs_rustc"
            if !miri.is_some_and(|m| {
                m.outcome.is_accepting()
                    && rustc_dual.is_some_and(|d| {
                        !d.skipped_for_ub
                            && d.parity_ok
                            && d.o0.outcome.semantically_eq(&d.o2.outcome)
                            && !m.outcome.semantically_eq(&d.o0.outcome)
                    })
            }) =>
        {
            return Err(
                "miri_vs_rustc signature requires non-skipped rustc O0/O2 parity and diverging accepting Miri and rustc-O0 outcomes"
                    .to_string(),
            );
        }
        "miri_vs_rustc" => {}
        "terminal_outcome_mismatch" => {
            let (Some(r), Some(l)) = (eff_ref, lean) else {
                return Err(
                    "terminal_outcome_mismatch signature requires both reference and Lean outcomes"
                        .to_string(),
                );
            };
            if ref_is_ub || lean_is_ub {
                return Err(
                    "terminal_outcome_mismatch cannot mask FaultUb (use missed_ub, ub_cause_mismatch, or spurious_lean_ub)"
                        .to_string(),
                );
            }
            if !r.outcome.is_terminating_accepting() || !l.outcome.is_terminating_accepting() {
                return Err(format!(
                    "terminal_outcome_mismatch signature requires terminating accepting reference and Lean outcomes (got ref={}, lean={})",
                    r.outcome.kind_tag(),
                    l.outcome.kind_tag()
                ));
            }
            ensure_prior_authority_parity("terminal_outcome_mismatch")?;
            if eff_ref_matches_lean(r, l) {
                return Err(
                    "terminal_outcome_mismatch signature contradicts matching reference and Lean outcomes"
                        .to_string(),
                );
            }
        }
        "spine_mismatch" => match sig.spine_relation.as_deref() {
            Some("rustc_o0_vs_o2") => {
                if miri_is_ub {
                    return Err(
                        "spine_mismatch (`rustc_o0_vs_o2`) cannot promote when Miri reports FaultUb"
                            .to_string(),
                    );
                }
                let Some(d) = rustc_dual.filter(|d| !d.skipped_for_ub && !d.parity_ok) else {
                    return Err(
                        "spine_mismatch (`rustc_o0_vs_o2`) requires non-skipped rustc_dual with parity_ok = false"
                            .to_string(),
                    );
                };
                if !d.o0.outcome.semantically_eq(&d.o2.outcome)
                    || compare_spines(
                        "rustc-O0",
                        &d.o0.spine,
                        "rustc-O2",
                        &d.o2.spine,
                        SpineCompareMode::FullBranchesAndCalls,
                    )
                    .is_ok()
                {
                    return Err(
                        "spine_mismatch (`rustc_o0_vs_o2`) requires matching rustc O0/O2 outcomes with diverging spines"
                            .to_string(),
                    );
                }
            }
            Some("miri_vs_rustc_o0") => {
                let (Some(m), Some(d)) = (
                    miri,
                    rustc_dual.filter(|d| {
                        !d.skipped_for_ub
                            && d.parity_ok
                            && d.o0.outcome.semantically_eq(&d.o2.outcome)
                    }),
                ) else {
                    return Err(
                        "spine_mismatch (`miri_vs_rustc_o0`) requires Miri and non-skipped rustc_dual with O0/O2 parity"
                            .to_string(),
                    );
                };
                if !m.outcome.is_accepting()
                    || !m.outcome.semantically_eq(&d.o0.outcome)
                    || compare_spines(
                        "miri",
                        &m.spine,
                        "rustc-O0",
                        &d.o0.spine,
                        SpineCompareMode::FullBranchesAndCalls,
                    )
                    .is_ok()
                {
                    return Err(
                        "spine_mismatch (`miri_vs_rustc_o0`) requires matching accepting outcomes with diverging Miri and rustc-O0 spines"
                            .to_string(),
                    );
                }
            }
            Some(rel) => {
                let (Some(r), Some(l)) = (eff_ref, lean) else {
                    return Err(format!(
                        "spine_mismatch (`{rel}`) requires both reference and Lean outcomes"
                    ));
                };
                let ref_is_refusal = matches!(r.outcome, TerminalOutcome::CaptureRefused { .. });
                if ref_is_ub || lean_is_ub || ref_is_refusal || lean_is_refusal {
                    return Err(format!(
                        "spine_mismatch (`{rel}`) cannot promote UB or CaptureRefused legs"
                    ));
                }
                ensure_prior_authority_parity(&format!("spine_mismatch (`{rel}`)"))?;
                let same_fuel_diverged = matches!(
                    (&r.outcome, &l.outcome),
                    (
                        TerminalOutcome::Diverged { fuel: f1 },
                        TerminalOutcome::Diverged { fuel: f2 },
                    ) if f1 == f2
                );
                let comparable_outcomes = same_fuel_diverged
                    || (!matches!(r.outcome, TerminalOutcome::Diverged { .. })
                        && !matches!(l.outcome, TerminalOutcome::Diverged { .. })
                        && eff_ref_matches_lean(r, l));
                let expected_rel = format!(
                    "{}_vs_{}",
                    sanitize_auth_tag(&r.authority),
                    sanitize_auth_tag(&l.authority)
                );
                if rel != expected_rel
                    || !comparable_outcomes
                    || compare_spines(
                        &r.authority,
                        &r.spine,
                        &l.authority,
                        &l.spine,
                        SpineCompareMode::FullBranchesAndCalls,
                    )
                    .is_ok()
                {
                    return Err(format!(
                        "spine_mismatch (`{rel}`) disagrees with supplied reference/Lean authorities (expected `{expected_rel}` with diverging spines)"
                    ));
                }
            }
            None => {
                return Err(
                    "spine_mismatch signature requires a non-empty spine_relation naming diverging authority spines"
                        .to_string(),
                );
            }
        },
        "strict_probe_accepted_multicall" => {
            let Some(report) = case_report else {
                return Err(
                    "ShrinkableCase does not carry a `lean_strict_probe` authority result; strict_probe_accepted_multicall cases must remain provisional or promote via FuzzProgram WitnessArtifact"
                        .to_string(),
                );
            };
            let primary_exercised_call = lean.is_some_and(|l| {
                l.spine.events.iter().any(|ev| {
                    matches!(
                        ev,
                        ObservableEvent::CallEnter { .. } | ObservableEvent::CallUnwind { .. }
                    )
                })
            });
            let probe_accepted = report.lean_strict_probe.as_ref().is_some_and(|p| {
                p.tool_error.is_none()
                    && !matches!(p.outcome, TerminalOutcome::CaptureRefused { .. })
            });
            if !primary_exercised_call || !probe_accepted {
                return Err(
                    "strict_probe_accepted_multicall CaseReport requires multi-call primary Lean spine and non-refused `lean_strict_probe` result"
                        .to_string(),
                );
            }
        }
        "caller_frame_law" => {
            if case_report.is_none() {
                return Err(
                    "ShrinkableCase does not instrument caller-frame watchers or emit caller_frame_law checks; caller_frame_law cases must remain provisional or promote via FuzzProgram WitnessArtifact"
                        .to_string(),
                );
            }
            if !any_accepting_frame_violated {
                return Err(
                    "caller_frame_law CaseReport requires a non-ignored accepting authority violating CallerFrameLaw"
                        .to_string(),
                );
            }
        }
        "metamorphic_duality" => {
            let Some(report) = case_report else {
                return Err(
                    "ShrinkableCase does not emit source-inlined metamorphic twins; metamorphic_duality cases must remain provisional or promote via FuzzProgram WitnessArtifact"
                        .to_string(),
                );
            };
            let valid_meta = report.metamorphic.as_ref().is_some_and(|m| {
                m.tool_error.is_none()
                    && m.called_lean.tool_error.is_none()
                    && m.inlined_lean.tool_error.is_none()
                    && !m.duality_holds
                    && matches!(m.status, MetamorphicStatus::Failed)
            });
            if !valid_meta {
                return Err(
                    "metamorphic_duality CaseReport requires a Failed primary MetamorphicDualityReceipt without tool errors"
                        .to_string(),
                );
            }
        }
        other => {
            return Err(format!("unexpected signature mismatch_category {other:?}"));
        }
    }
    Ok(())
}
