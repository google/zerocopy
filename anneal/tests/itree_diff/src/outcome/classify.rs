// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Spine comparison and 4-way differential verdict classification.

use super::*;

/// Final differential classification across execution authorities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "verdict", rename_all = "snake_case")]
pub enum TraceVerdict {
    /// Full 4-way agreement with both Miri UB authority and Lean
    /// `Trusted.MirSemantics` active on `TerminalOutcome`, `ObservableSpine`,
    /// and `CallerFrameLaw`. Never emitted when Miri or Lean is unavailable or
    /// disabled.
    Agree,
    /// Degraded parity check without Miri (`miri == None`, e.g. inside trimmed
    /// archive `workspace-tests`): `rustc O0 == O2` and Lean agree (or Lean
    /// conservatively faults on an `expected_ub` case), but Miri UB oracle
    /// confirmation was not run. Excluded from clean `Agree` admission and
    /// fails closed when `--require-miri` / `ANNEAL_ITREE_REQUIRE_MIRI=1` is
    /// set.
    DegradedNoMiri { detail: String },
    /// Degraded parity check without Lean (`lean == None`, e.g. under
    /// `--no-lean`): `rustc O0 == O2` and Miri agreed without critical
    /// failures, but Lean semantic verification was disabled. Excluded from
    /// clean `Agree` admission.
    DegradedNoLean { detail: String },
    /// CRITICAL (P0): Reference authority reports UB or disagrees on terminal
    /// outcome, observable spine, or caller-frame preservation while Lean
    /// accepts.
    UnsoundAccept { detail: String },
    /// Valid forward-simulation conservative over-approximation (`forwardSim`
    /// holds; `biFaultEquiv` gap): Lean faults `.undefined`/`.unsupported`,
    /// exhausts step fuel, or capture refuses where Miri/rustc succeeds.
    /// Explicitly flagged as NEVER licensing UB refutation, and
    /// `undeclared_ub_fault` fails CI gates when Lean reports
    /// `.fault .undefined` on an accepting Miri run without a matching
    /// [`DisclosedGapSpec`] (`docs/testing-architecture.md` §4.2).
    ConservativeOverApprox {
        reason: String,
        ub_refutation_disallowed: bool,
        undeclared_ub_fault: bool,
    },
    /// Expected discrepancy matching an explicitly declared boundary gap.
    DisclosedGapArtifact { gap: DisclosedGapKind, detail: String },
    /// Harness, toolchain, timeout, or protocol failure (never silently
    /// downgraded to `Agree` or `ConservativeOverApprox`).
    ToolError { authority: String, detail: String },
}

impl TraceVerdict {
    pub fn is_critical_failure(&self) -> bool {
        matches!(
            self,
            Self::UnsoundAccept { .. }
                | Self::ToolError { .. }
                | Self::ConservativeOverApprox { undeclared_ub_fault: true, .. }
        )
    }

    pub fn label(&self) -> &'static str {
        match self {
            Self::Agree => "AGREE",
            Self::DegradedNoMiri { .. } => "DEGRADED_NO_MIRI",
            Self::DegradedNoLean { .. } => "DEGRADED_NO_LEAN",
            Self::UnsoundAccept { .. } => "UNSOUND_ACCEPT_P0",
            Self::ConservativeOverApprox { undeclared_ub_fault: true, .. } => {
                "UNDECLARED_UB_FAULT_REGRESSION"
            }
            Self::ConservativeOverApprox { undeclared_ub_fault: false, .. } => {
                "CONSERVATIVE_OVER_APPROX"
            }
            Self::DisclosedGapArtifact { .. } => "DISCLOSED_GAP_ARTIFACT",
            Self::ToolError { .. } => "TOOL_ERROR",
        }
    }
}

impl fmt::Display for TraceVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Agree => write!(f, "Agree"),
            Self::DegradedNoMiri { detail } => write!(f, "DegradedNoMiri: {detail}"),
            Self::DegradedNoLean { detail } => write!(f, "DegradedNoLean: {detail}"),
            Self::UnsoundAccept { detail } => write!(f, "UnsoundAccept(P0): {detail}"),
            Self::ConservativeOverApprox {
                reason,
                ub_refutation_disallowed,
                undeclared_ub_fault,
            } => write!(
                f,
                "ConservativeOverApprox(ub_refutation_disallowed={ub_refutation_disallowed}, undeclared_ub_fault={undeclared_ub_fault}): {reason}"
            ),
            Self::DisclosedGapArtifact { gap, detail } => {
                write!(f, "DisclosedGapArtifact({gap:?}): {detail}")
            }
            Self::ToolError { authority, detail } => {
                write!(f, "ToolError({authority}): {detail}")
            }
        }
    }
}

/// Compare two observable spines according to `mode`, checking call events,
/// `CallerFrameCheck` checkpoints, and (in `FullBranchesAndCalls`) `BranchTag`
/// transitions.
pub fn compare_spines(
    reference_name: &str,
    reference: &ObservableSpine,
    candidate_name: &str,
    candidate: &ObservableSpine,
    mode: SpineCompareMode,
) -> Result<(), String> {
    match mode {
        SpineCompareMode::OutcomeOnly => Ok(()),
        SpineCompareMode::ObsErasedCallsOnly => {
            let ref_stream = normalize_call_events(&reference.erased_branch_spine());
            let cand_stream = normalize_call_events(&candidate.erased_branch_spine());
            if ref_stream != cand_stream {
                return Err(format!(
                    "obs-erased observable spine mismatch: {reference_name}={ref_stream:?} vs {candidate_name}={cand_stream:?}"
                ));
            }
            Ok(())
        }
        SpineCompareMode::FullBranchesAndCalls => {
            let ref_calls = reference.erased_call_spine();
            let cand_calls = candidate.erased_call_spine();
            if ref_calls != cand_calls {
                return Err(format!(
                    "full call spine mismatch: {reference_name}={ref_calls:?} vs {candidate_name}={cand_calls:?}"
                ));
            }
            let ref_frames = reference.caller_frame_checks();
            let cand_frames = candidate.caller_frame_checks();
            if ref_frames != cand_frames {
                return Err(format!(
                    "caller-frame checkpoint spine mismatch: {reference_name}={ref_frames:?} vs {candidate_name}={cand_frames:?}"
                ));
            }
            let ref_branches = reference.branch_tags();
            let cand_branches = candidate.branch_tags();
            if ref_branches != cand_branches {
                return Err(format!(
                    "branch tag spine mismatch: {reference_name}={ref_branches:?} vs {candidate_name}={cand_branches:?}"
                ));
            }
            if reference.events != candidate.events {
                return Err(format!(
                    "full event interleaving spine mismatch: {reference_name}={:?} vs {candidate_name}={:?}",
                    reference.events, candidate.events
                ));
            }
            Ok(())
        }
    }
}

fn format_masked_bytes(bytes: &[Option<u8>]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2 + 2);
    out.push('[');
    for b in bytes {
        match b {
            Some(v) => {
                let _ = write!(out, "{v:02x}");
            }
            None => out.push_str("__"),
        }
    }
    out.push(']');
    out
}

fn normalize_call_events(events: &[ObservableEvent]) -> Vec<String> {
    events
        .iter()
        .map(|ev| match ev {
            ObservableEvent::CallEnter { callee, arg_bytes, arg_reprs } => {
                let bytes_part = arg_bytes
                    .iter()
                    .map(|slot| format_masked_bytes(slot))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("ENTER:{callee}({})[{bytes_part}]", arg_reprs.join(","))
            }
            ObservableEvent::CallReturn { callee, ret_bytes, ret_repr } => {
                format!("RETURN:{callee}={ret_repr}@{}", format_masked_bytes(ret_bytes))
            }
            ObservableEvent::CallUnwind { callee, reason } => {
                format!("UNWIND:{callee}:{}", normalize_unwind_reason(reason))
            }
            ObservableEvent::BranchTag { block, discr, target } => {
                format!("BRANCH:bb{block}({discr})->bb{target}")
            }
            ObservableEvent::CallerFrameCheck {
                point,
                locals_preserved,
                allocs_preserved,
                preserved,
            } => {
                format!("FRAME:{point}:{locals_preserved}:{allocs_preserved}:{preserved}")
            }
        })
        .collect()
}

/// Normalize `CallUnwind.reason` across Rust/Miri panic messages, Lean MIR
/// `.assert` unwind tags, and scheduled `EnvAction::{Unwind,Abort}` payloads so
/// `ObsErasedCallsOnly` preserves unwind causes without coupling to dynamic
/// Rust bounds-check indices.
pub fn normalize_unwind_reason(reason: &str) -> String {
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

/// Classify a 4-way differential run across `rustc -O0`, `rustc -O2`, `miri`,
/// `lean`, and optional `anneal-mir-eval`.
///
/// Enforces:
/// 1. When Miri reports `FaultUb` (or when `rustc_skipped_for_ub` is set),
///    native `rustc` results/errors are never consulted as UB ground truth.
/// 2. When `miri` is `None`, `TraceVerdict::Agree` is NEVER returned; clean
///    non-Miri runs classify as `TraceVerdict::DegradedNoMiri`.
/// 3. When `lean` is `None`, `TraceVerdict::Agree` is NEVER returned; clean
///    Miri-backed runs without Lean classify as `TraceVerdict::DegradedNoLean`.
#[allow(clippy::too_many_arguments)]
pub fn classify_four_way(
    rustc_o0: &AuthorityRunResult,
    rustc_o2: &AuthorityRunResult,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    spine_mode: SpineCompareMode,
    disclosed_gap: Option<&DisclosedGapSpec>,
) -> TraceVerdict {
    classify_four_way_with_ub_guard(
        rustc_o0,
        rustc_o2,
        false,
        miri,
        lean,
        mir_eval,
        spine_mode,
        disclosed_gap,
    )
}

/// Full 4-way classifier accepting `rustc_skipped_for_ub` (set when Miri was
/// unavailable on a known `expected_ub` case so host `rustc` was intentionally
/// not executed on undefined behavior).
#[allow(clippy::too_many_arguments)]
pub fn classify_four_way_with_ub_guard(
    rustc_o0: &AuthorityRunResult,
    rustc_o2: &AuthorityRunResult,
    rustc_skipped_for_ub: bool,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    spine_mode: SpineCompareMode,
    disclosed_gap: Option<&DisclosedGapSpec>,
) -> TraceVerdict {
    let miri_reports_ub =
        miri.is_some_and(|m| matches!(m.outcome, TerminalOutcome::FaultUb { .. }));
    let ignore_host_rustc = miri_reports_ub || rustc_skipped_for_ub;

    // 1. Check tool errors on non-ignored legs (never downgrade ToolError).
    let checked_for_tool_err: [Option<&AuthorityRunResult>; 5] = [
        if ignore_host_rustc { None } else { Some(rustc_o0) },
        if ignore_host_rustc { None } else { Some(rustc_o2) },
        miri,
        lean,
        mir_eval,
    ];
    for auth in checked_for_tool_err.into_iter().flatten() {
        if let Some(detail) = &auth.tool_error {
            return TraceVerdict::ToolError {
                authority: auth.authority.clone(),
                detail: detail.clone(),
            };
        }
    }

    // 2. Caller-frame preservation law check on every non-UB accepting run.
    let checked_for_frame: [Option<&AuthorityRunResult>; 5] = [
        if ignore_host_rustc { None } else { Some(rustc_o0) },
        if ignore_host_rustc { None } else { Some(rustc_o2) },
        miri,
        lean,
        mir_eval,
    ];
    for auth in checked_for_frame.into_iter().flatten() {
        if auth.outcome.is_accepting() && !auth.caller_frame_law.is_satisfied() {
            return TraceVerdict::UnsoundAccept {
                detail: format!(
                    "{} violated CallerFrameLaw: {:?}",
                    auth.authority, auth.caller_frame_law.violations
                ),
            };
        }
    }

    // 3. When host rustc ran on defined-behavior inputs, require O0 == O2.
    if !ignore_host_rustc {
        if !rustc_o0.outcome.semantically_eq(&rustc_o2.outcome) {
            return TraceVerdict::UnsoundAccept {
                detail: format!(
                    "rustc O0 vs O2 terminal outcome divergence: O0={:?} vs O2={:?}",
                    rustc_o0.outcome, rustc_o2.outcome
                ),
            };
        }
        if let Err(msg) =
            compare_spines("rustc-O0", &rustc_o0.spine, "rustc-O2", &rustc_o2.spine, spine_mode)
        {
            return TraceVerdict::UnsoundAccept { detail: format!("rustc O0 vs O2: {msg}") };
        }
    }

    // 4. Branch on Miri availability.
    if let Some(m) = miri {
        // When Miri succeeds cleanly (no UB), cross-check Miri vs rustc-O0.
        if !miri_reports_ub && m.outcome.is_accepting() {
            if !m.outcome.semantically_eq(&rustc_o0.outcome) {
                return TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "miri vs rustc-O0 outcome divergence: miri={:?} vs rustc-O0={:?}",
                        m.outcome, rustc_o0.outcome
                    ),
                };
            }
            if let Err(msg) =
                compare_spines("miri", &m.spine, "rustc-O0", &rustc_o0.spine, spine_mode)
            {
                return TraceVerdict::UnsoundAccept { detail: format!("miri vs rustc-O0: {msg}") };
            }
        }

        let lean_verdict =
            lean.map(|lean_res| classify_pair(m, lean_res, spine_mode, disclosed_gap));
        if let Some(lv) = &lean_verdict
            && lv.is_critical_failure()
        {
            return lv.clone();
        }

        let me_verdict = mir_eval
            .map(|me_res| classify_pair(m, me_res, SpineCompareMode::OutcomeOnly, disclosed_gap));
        if let Some(mv) = &me_verdict
            && mv.is_critical_failure()
        {
            return mv.clone();
        }

        if let Some(lv) = lean_verdict
            && !matches!(lv, TraceVerdict::Agree)
        {
            return lv;
        }

        if let Some(mv) = me_verdict
            && !matches!(mv, TraceVerdict::Agree)
        {
            return mv;
        }

        if lean.is_some() {
            return TraceVerdict::Agree;
        }

        let detail = if miri_reports_ub {
            "Miri detected Undefined Behavior, but Lean authority was disabled".to_string()
        } else {
            "rustc-O0, rustc-O2, and Miri agreed on outcome and spine, but Lean authority was disabled".to_string()
        };
        return TraceVerdict::DegradedNoLean { detail };
    }

    // 5. Degraded mode (`miri == None`): NEVER return `TraceVerdict::Agree`!
    if rustc_skipped_for_ub {
        // Expected-UB case without Miri: host rustc was skipped to avoid UB;
        // verify Lean (and mir_eval) did NOT accept or exhaust step fuel!
        for cand in [lean, mir_eval].into_iter().flatten() {
            if cand.outcome.is_accepting() {
                return TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "expected-UB case accepted by {} ({:?}) while Miri was unavailable",
                        cand.authority, cand.outcome
                    ),
                };
            }
        }
        if let (Some(lean_res), Some(me_res)) = (lean, mir_eval)
            && matches!(lean_res.outcome, TerminalOutcome::FaultUb { .. })
            && matches!(me_res.outcome, TerminalOutcome::FaultUb { .. })
            && let Err(detail) = compare_ub_fault_results(lean_res, me_res)
        {
            return TraceVerdict::UnsoundAccept { detail };
        }
        if let (Some(gap_spec), Some(lean_res)) = (disclosed_gap, lean)
            && gap_spec.matches_lean_outcome(&lean_res.outcome)
        {
            return TraceVerdict::DisclosedGapArtifact {
                gap: gap_spec.kind,
                detail: "expected-UB disclosed gap verified conservatively without Miri"
                    .to_string(),
            };
        }
        let detail = if lean.is_some() {
            "expected-UB probe rejected conservatively by Lean; Miri unavailable"
        } else {
            "expected-UB probe skipped host rustc while both Miri and Lean were unavailable or disabled"
        };
        return TraceVerdict::DegradedNoMiri { detail: detail.to_string() };
    }

    // Defined-behavior case without Miri: check rustc_o0 vs Lean & mir_eval,
    // downgrading `Agree` to `DegradedNoMiri` while ensuring non-critical Lean
    // verdicts never mask critical `mir_eval` failures.
    let lean_verdict =
        lean.map(|lean_res| classify_pair(rustc_o0, lean_res, spine_mode, disclosed_gap));
    if let Some(lv) = &lean_verdict
        && lv.is_critical_failure()
    {
        return lv.clone();
    }

    let me_verdict = mir_eval.map(|me_res| {
        classify_pair(rustc_o0, me_res, SpineCompareMode::OutcomeOnly, disclosed_gap)
    });
    if let Some(mv) = &me_verdict
        && mv.is_critical_failure()
    {
        return mv.clone();
    }

    if let Some(lv) = lean_verdict
        && !matches!(lv, TraceVerdict::Agree)
    {
        return lv;
    }

    if let Some(mv) = me_verdict
        && !matches!(mv, TraceVerdict::Agree)
    {
        return mv;
    }

    let detail = if lean.is_some() {
        "rustc-O0, rustc-O2, and Lean agreed on outcome and spine, but Miri was unavailable"
    } else {
        "rustc-O0 and rustc-O2 agreed on outcome and spine, but Miri and Lean were unavailable or disabled"
    };
    TraceVerdict::DegradedNoMiri { detail: detail.to_string() }
}

/// Compare two `FaultUb` authority results, requiring authenticated
/// entry-input `boundary_slots` parity whenever entry digests are present (and
/// rejecting asymmetric missing entry digests unless a leg omitted
/// `boundary_slots` in value-only mode) alongside compatible UB fault causes.
pub fn compare_ub_fault_results(
    reference: &AuthorityRunResult,
    candidate: &AuthorityRunResult,
) -> Result<(), String> {
    let (
        TerminalOutcome::FaultUb { detail: ref_detail },
        TerminalOutcome::FaultUb { detail: cand_detail },
    ) = (&reference.outcome, &candidate.outcome)
    else {
        return Err(format!(
            "internal error: expected FaultUb outcomes, got {:?} vs {:?}",
            reference.outcome, candidate.outcome
        ));
    };

    match (&reference.entry_mem_digest, &candidate.entry_mem_digest) {
        (Some(r_dig), Some(c_dig)) if r_dig != c_dig => {
            return Err(format!(
                "UB entry-input boundary digest mismatch: {} ({r_dig}) vs {} ({c_dig})",
                reference.authority, candidate.authority
            ));
        }
        (Some(_), Some(_)) | (None, None) => {}
        (Some(_), None) | (None, Some(_)) => {
            let ref_omitted =
                reference.entry_mem_digest.is_none() && reference.post_only_mem_digest;
            let cand_omitted =
                candidate.entry_mem_digest.is_none() && candidate.post_only_mem_digest;
            if !(ref_omitted || cand_omitted) {
                return Err(format!(
                    "UB fault missing authenticated entry-input digest on one authority: {}={:?} vs {}={:?}",
                    reference.authority,
                    reference.entry_mem_digest,
                    candidate.authority,
                    candidate.entry_mem_digest,
                ));
            }
        }
    }

    if ub_fault_causes_compatible(ref_detail, cand_detail) {
        Ok(())
    } else {
        Err(format!(
            "UB fault cause mismatch: {} reported {:?} ({ref_detail}) while {} reported {:?} ({cand_detail})",
            reference.authority,
            classify_ub_fault_detail(ref_detail),
            candidate.authority,
            classify_ub_fault_detail(cand_detail),
        ))
    }
}

fn classify_pair(
    reference: &AuthorityRunResult,
    candidate: &AuthorityRunResult,
    spine_mode: SpineCompareMode,
    disclosed_gap: Option<&DisclosedGapSpec>,
) -> TraceVerdict {
    match (&reference.outcome, &candidate.outcome) {
        // Both hit UB -> require matching entry inputs + compatible UB causes!
        (TerminalOutcome::FaultUb { .. }, TerminalOutcome::FaultUb { .. }) => {
            match compare_ub_fault_results(reference, candidate) {
                Ok(()) => TraceVerdict::Agree,
                Err(detail) => TraceVerdict::UnsoundAccept { detail },
            }
        }
        // Both diverged at the same fuel -> compare spines -> Agree!
        (TerminalOutcome::Diverged { fuel: f1 }, TerminalOutcome::Diverged { fuel: f2 })
            if f1 == f2 =>
        {
            if let Err(msg) = compare_spines(
                &reference.authority,
                &reference.spine,
                &candidate.authority,
                &candidate.spine,
                spine_mode,
            ) {
                TraceVerdict::UnsoundAccept { detail: msg }
            } else {
                TraceVerdict::Agree
            }
        }
        // Candidate exhausted step fuel while reference terminated or hit UB ->
        // conservative fuel incompleteness (never UnsoundAccept).
        (ref_out, TerminalOutcome::Diverged { fuel }) => TraceVerdict::ConservativeOverApprox {
            reason: format!(
                "{} exhausted step fuel ({fuel}) while {} produced {ref_out:?}",
                candidate.authority, reference.authority
            ),
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
        },
        // Reference hit UB, Lean refused capture/unsupported -> conservative
        // (does not accept UB).
        (TerminalOutcome::FaultUb { detail }, TerminalOutcome::CaptureRefused { reason }) => {
            if let Some(gap_spec) = disclosed_gap
                && gap_spec.matches_lean_outcome(&candidate.outcome)
            {
                TraceVerdict::DisclosedGapArtifact {
                    gap: gap_spec.kind,
                    detail: format!(
                        "{} reported UB ({detail}) while {} refused ({reason})",
                        reference.authority, candidate.authority
                    ),
                }
            } else {
                TraceVerdict::ConservativeOverApprox {
                    reason: format!(
                        "{} reported UB ({detail}); {} conservatively refused/unsupported ({reason})",
                        reference.authority, candidate.authority
                    ),
                    ub_refutation_disallowed: true,
                    undeclared_ub_fault: false,
                }
            }
        }
        // CRITICAL P0: Reference hit UB, candidate accepted!
        (TerminalOutcome::FaultUb { detail }, _) => TraceVerdict::UnsoundAccept {
            detail: format!(
                "{} detected UB ({detail}) while {} accepted with {:?}",
                reference.authority, candidate.authority, candidate.outcome
            ),
        },
        // Reference succeeded/unwound/aborted, candidate refused capture or
        // faulted `.unsupported`.
        (ref_out, TerminalOutcome::CaptureRefused { reason }) if ref_out.is_accepting() => {
            if let Some(gap_spec) = disclosed_gap
                && gap_spec.matches_lean_outcome(&candidate.outcome)
            {
                TraceVerdict::DisclosedGapArtifact { gap: gap_spec.kind, detail: reason.clone() }
            } else {
                TraceVerdict::ConservativeOverApprox {
                    reason: format!(
                        "{} succeeded ({ref_out:?}) while {} conservatively refused/unsupported: {reason}",
                        reference.authority, candidate.authority
                    ),
                    ub_refutation_disallowed: true,
                    undeclared_ub_fault: false,
                }
            }
        }
        // Reference succeeded, candidate faulted `.undefined` -> allowed only
        // when `disclosed_gap` matches the specific boundary fault
        // (`docs/testing-architecture.md` §4.2); unmatched or undeclared UB
        // faults set `undeclared_ub_fault: true` and fail CI gates so
        // completeness regressions are never masked.
        (ref_out, TerminalOutcome::FaultUb { detail }) if ref_out.is_accepting() => {
            if let Some(gap_spec) = disclosed_gap
                && gap_spec.matches_lean_outcome(&candidate.outcome)
            {
                TraceVerdict::DisclosedGapArtifact {
                    gap: gap_spec.kind,
                    detail: format!(
                        "{} accepted ({ref_out:?}) while {} faulted declared conservative gap ({detail})",
                        reference.authority, candidate.authority
                    ),
                }
            } else {
                TraceVerdict::ConservativeOverApprox {
                    reason: format!(
                        "{} accepted ({ref_out:?}) while {} faulted undeclared UB ({detail})",
                        reference.authority, candidate.authority
                    ),
                    ub_refutation_disallowed: true,
                    undeclared_ub_fault: true,
                }
            }
        }
        // Both accepted: require exact outcome and spine parity.
        (ref_out, cand_out) => {
            let outcome_matches =
                if candidate.post_only_mem_digest && !reference.post_only_mem_digest {
                    ref_out.semantically_eq_post_only(cand_out)
                } else {
                    ref_out.semantically_eq(cand_out)
                };
            if !outcome_matches {
                return TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "terminal outcome mismatch: {}={ref_out:?} vs {}={cand_out:?}",
                        reference.authority, candidate.authority
                    ),
                };
            }
            if let Err(msg) = compare_spines(
                &reference.authority,
                &reference.spine,
                &candidate.authority,
                &candidate.spine,
                spine_mode,
            ) {
                return TraceVerdict::UnsoundAccept { detail: msg };
            }
            TraceVerdict::Agree
        }
    }
}

/// Compute lowercase 64-char SHA-256 hex digest of `bytes`.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    hex
}
