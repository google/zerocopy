// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic fixed-point delta shrinker (`ddmin` over steps + non-monotonic
//! scalar candidate reduction) and reproducible JSON witness emitter.

use std::{
    collections::BTreeMap,
    fs,
    path::Path,
    time::{Duration, Instant},
};

use serde::{Deserialize, Serialize};

use crate::{
    CaseReport,
    fuzzer::{FuzzProgram, FuzzStep},
    outcome::{AuthorityRunResult, MetamorphicStatus, TraceVerdict},
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

/// Structured failure signature pinning the exact semantic failure class during
/// shrinking so candidates can never drift from missed-UB into a value mismatch
/// or into a `ToolError`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkFailureSignature {
    pub verdict_kind: &'static str,
    pub ref_outcome_kind: &'static str,
    pub lean_outcome_kind: &'static str,
    pub mismatch_category: &'static str,
    #[serde(default)]
    pub metamorphic_relations: Vec<String>,
    #[serde(default)]
    pub metamorphic_leg_kinds: String,
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

impl ShrinkFailureSignature {
    /// Extract a shrinkable semantic failure signature from a full
    /// [`CaseReport`], pinning exact metamorphic failing relations and twin-leg
    /// outcome kinds whenever metamorphic duality failed.
    pub fn from_case_report(report: &CaseReport) -> Option<Self> {
        if let Some(m) = &report.metamorphic
            && m.tool_error.is_some()
        {
            return None;
        }
        let ref_leg = report.miri.as_ref().or(if report.rustc_dual.skipped_for_ub {
            None
        } else {
            Some(&report.rustc_dual.o0)
        });
        let mut sig = Self::from_verdict_and_legs(&report.verdict, ref_leg, report.lean.as_ref())?;
        if let Some(m) = &report.metamorphic
            && matches!(m.status, MetamorphicStatus::Failed)
        {
            if !m.failed_relations.is_empty() {
                sig.metamorphic_relations = m.failed_relations.clone();
            }
            sig.metamorphic_leg_kinds = m.twin_outcome_summary.clone();
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
        match verdict {
            TraceVerdict::UnsoundAccept { detail } => {
                // Check `metamorphic_duality:` / `source-inlined` BEFORE
                // compiler-leg substrings so twin O0/O2 or Miri mismatches are
                // never misbucketed as primary `rustc_o0_o2` / `miri_vs_rustc`.
                let is_metamorphic = detail.starts_with("metamorphic_duality:")
                    || detail.contains("source-inlined")
                    || detail.contains("metamorphic");
                let mismatch_category = if is_metamorphic {
                    "metamorphic_duality"
                } else if detail.contains("StrictVerbatim failed to conservatively refuse") {
                    "strict_probe_accepted_multicall"
                } else if detail.contains("CallerFrameLaw") {
                    "caller_frame_law"
                } else if detail.contains("rustc O0 vs O2") {
                    "rustc_o0_o2"
                } else if detail.contains("miri vs rustc-O0") {
                    "miri_vs_rustc"
                } else if detail.contains("UB fault cause mismatch") {
                    "ub_cause_mismatch"
                } else if detail.contains("detected UB") {
                    "missed_ub"
                } else if detail.contains("spine mismatch")
                    || detail.contains("event interleaving mismatch")
                {
                    "spine_mismatch"
                } else {
                    "terminal_outcome_mismatch"
                };
                let metamorphic_relations = if is_metamorphic {
                    extract_metamorphic_relations_from_detail(detail)
                } else {
                    Vec::new()
                };
                Some(Self {
                    verdict_kind: "unsound_accept",
                    ref_outcome_kind: ref_kind,
                    lean_outcome_kind: lean_kind,
                    mismatch_category,
                    metamorphic_relations,
                    metamorphic_leg_kinds: String::new(),
                })
            }
            TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: true, .. } => Some(Self {
                verdict_kind: "undeclared_ub_fault",
                ref_outcome_kind: ref_kind,
                lean_outcome_kind: lean_kind,
                mismatch_category: "spurious_lean_ub",
                metamorphic_relations: Vec::new(),
                metamorphic_leg_kinds: String::new(),
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

/// Complete result of shrinking a failing [`FuzzProgram`], iterating step-list
/// 1-minimal `ddmin` and non-monotonic scalar candidate reduction to a combined
/// fixed point under [`ShrinkBudget`].
///
/// `is_one_minimal` is `true` strictly when a complete fixed-point sweep over
/// single-step deletions (`ddmin`) and the scalar candidate neighborhood
/// (`smaller_u32_candidates`) produces zero further reductions without hitting
/// [`ShrinkBudget`] (without assuming threshold monotonicity over scalars).
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
}

/// Deterministically shrink a [`FuzzProgram`] under [`ShrinkBudget::default`].
pub fn shrink_fuzz_program<F>(initial: &FuzzProgram, predicate: F) -> ProgramShrinkResult
where
    F: FnMut(&FuzzProgram) -> bool,
{
    shrink_fuzz_program_with_budget(initial, ShrinkBudget::default(), predicate)
}

/// Deterministically shrink a [`FuzzProgram`] to a combined fixed point under
/// `budget`: iterates Stage 1 (`ddmin` over `prog.steps`), Stage 2
/// (`input_x`/`input_y` non-monotonic candidate narrowing), and Stage 3
/// (step-immediate non-monotonic candidate narrowing) until a full sweep over
/// statement deletions and all smaller scalar candidates produces zero
/// reductions, or `budget` (`max_evals` / `max_duration`) cuts off evaluation
/// (`is_one_minimal = false`).
pub fn shrink_fuzz_program_with_budget<F>(
    initial: &FuzzProgram,
    budget: ShrinkBudget,
    mut predicate: F,
) -> ProgramShrinkResult
where
    F: FnMut(&FuzzProgram) -> bool,
{
    let start = Instant::now();
    let mut cache: BTreeMap<String, bool> = BTreeMap::new();
    let eval_count = std::cell::Cell::new(0usize);
    let budget_exhausted = std::cell::Cell::new(false);

    let mut eval_cached = |p: &FuzzProgram| -> bool {
        let key = serde_json::to_string(p).unwrap_or_default();
        if let Some(&cached) = cache.get(&key) {
            return cached;
        }
        let seen = eval_count.get();
        if seen > 0 && (seen >= budget.max_evals || start.elapsed() >= budget.max_duration) {
            budget_exhausted.set(true);
            return false;
        }
        eval_count.set(seen + 1);
        let res = predicate(p);
        cache.insert(key, res);
        res
    };

    if budget.max_evals == 0 || !eval_cached(initial) {
        return ProgramShrinkResult {
            original: initial.clone(),
            minimized: initial.clone(),
            original_steps: initial.steps.len(),
            minimized_steps: initial.steps.len(),
            predicate_evaluations: eval_count.get(),
            succeeded: false,
            is_one_minimal: false,
            budget_exhausted: budget.max_evals == 0,
        };
    }

    let mut best = initial.clone();

    loop {
        let prev = best.clone();

        // Stage 1: 1-minimal ddmin on `best.steps` at current inputs.
        let template = best.clone();
        let seq_res = shrink_sequence_1_minimal(&best.steps, |cand_steps| {
            let mut cand = template.clone();
            cand.steps = cand_steps.to_vec();
            eval_cached(&cand)
        });
        best.steps = seq_res.minimized;
        if budget_exhausted.get() {
            break;
        }

        // Stage 2: non-monotonic candidate shrink on `input_x` and `input_y`.
        best.input_x = shrink_u32_non_monotonic(best.input_x, |v| {
            let mut cand = best.clone();
            cand.input_x = v;
            eval_cached(&cand)
        });
        if budget_exhausted.get() {
            break;
        }
        best.input_y = shrink_u32_non_monotonic(best.input_y, |v| {
            let mut cand = best.clone();
            cand.input_y = v;
            eval_cached(&cand)
        });
        if budget_exhausted.get() {
            break;
        }

        // Stage 3: non-monotonic candidate shrink on step immediates.
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
                    FuzzStep::ArithImm { op, imm: s }
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
                    let t = shrink_u32_non_monotonic(then_imm, |v| {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::BranchMix { then_imm: v, else_imm };
                        eval_cached(&cand)
                    });
                    let e = shrink_u32_non_monotonic(else_imm, |v| {
                        let mut cand = best.clone();
                        cand.steps[idx] = FuzzStep::BranchMix { then_imm: t, else_imm: v };
                        eval_cached(&cand)
                    });
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
            best.steps[idx] = shrunk;
        }

        if budget_exhausted.get() || best == prev {
            break;
        }
    }

    let hit_budget = budget_exhausted.get();
    ProgramShrinkResult {
        original: initial.clone(),
        original_steps: initial.steps.len(),
        minimized_steps: best.steps.len(),
        minimized: best,
        predicate_evaluations: eval_count.get(),
        succeeded: true,
        is_one_minimal: !hit_budget,
        budget_exhausted: hit_budget,
    }
}

/// Enumerate strictly smaller `u32` candidates (`cand < v`) sorted in ascending
/// magnitude without assuming threshold monotonicity: includes `0..=12`, powers
/// of two and `(1 << k) - 1`, dyadic/midpoint fractions (`v / 8`, `v / 4`,
/// `(3 * v) / 8`, `v / 2`, `(5 * v) / 8`, `(3 * v) / 4`, `(7 * v) / 8`),
/// decimal quotients (`v / 100`, `v / 10`), byte-masked prefixes and byte
/// shifts, single-bit clears `v & !(1 << k)`, and immediate predecessors toward
/// `0` (`v - 8`, `v - 4`, `v - 2`, `v - 1`).
pub fn smaller_u32_candidates(v: u32) -> Vec<u32> {
    if v == 0 {
        return Vec::new();
    }
    let mut cands = Vec::with_capacity(48);
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
    cands.retain(|&c| c < v);
    cands.sort_unstable();
    cands.dedup();
    cands
}

/// Narrow an unsigned `u32` scalar to a fixed point over
/// [`smaller_u32_candidates`] without discarding smaller candidates when a
/// midpoint fails to reproduce `pred`.
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

/// Enumerate signed `i32` candidates strictly simpler than `v` under the
/// well-founded order `(|a|, a < 0) < (|v|, v < 0)` (smaller magnitude first,
/// preferring `+m` over `-m`), including `0`, `1`, `-1`, sign-flip `|v|`,
/// signed dyadic fractions and bit clears, and unit steps `v - 1` / `v + 1`
/// toward `0`.
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

/// Reproducible divergence witness artifact emitted to disk when shrinking a
/// failing case.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessArtifact {
    pub case_id: String,
    pub verdict: TraceVerdict,
    pub original_verdict: TraceVerdict,
    pub shrink: ProgramShrinkResult,
    pub reproducer_rust_source: String,
}

impl WitnessArtifact {
    pub fn from_shrink(
        case_id: impl Into<String>,
        minimized_verdict: TraceVerdict,
        original_verdict: TraceVerdict,
        shrink: ProgramShrinkResult,
    ) -> Self {
        let reproducer_rust_source =
            shrink.minimized.to_trace_test_case().traced_rust_source.unwrap_or_default();
        Self {
            case_id: case_id.into(),
            verdict: minimized_verdict,
            original_verdict,
            shrink,
            reproducer_rust_source,
        }
    }

    pub fn write_json(&self, path: &Path) -> Result<(), String> {
        if let Some(parent) = path.parent()
            && !parent.as_os_str().is_empty()
        {
            fs::create_dir_all(parent)
                .map_err(|e| format!("create witness parent dir {}: {e}", parent.display()))?;
        }
        let body = serde_json::to_string_pretty(self)
            .map_err(|e| format!("serialize witness artifact: {e}"))?;
        fs::write(path, body).map_err(|e| format!("write witness {}: {e}", path.display()))
    }
}
