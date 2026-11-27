// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Structural and input counterexample shrinker for [`GenProgram`].
//!
//! Operates recursively on the typed Profile v1 IR so every intermediate
//! candidate renders to syntactically and type-valid Rust:
//! 1. Recursive `ddmin` statement deletion across top-level and all nested
//!    `if`/`else` and `while` statement blocks;
//! 2. Recursive branch collapse (`if`/`else` -> single branch or empty `else`),
//!    loop unrolling, `break`/`continue` guard removal, loop-bound shrinking
//!    toward `0`/`1`, and `MoveReinit` -> `Assign` lowering;
//! 3. Recursive top-down expression simplification across return expressions,
//!    nested statements, loop `break`/`continue` guards, `match` scrutinees and
//!    arms, and local initializers;
//! 4. Dead local/parameter elimination (with index remapping) and `unsafe fn`
//!    qualifier minimization;
//! 5. Input argument narrowing via ascending non-monotonic candidate
//!    enumeration (`0..=12`, powers of two, byte/word masks, dyadic eighths,
//!    single-bit clears, sign flips, and immediate neighbors toward `0`, never
//!    discarding smaller candidates when an intermediate probe is not
//!    preserved).
//!
//! Deterministic under step-bounded budgets (`max_steps`), with
//! `max_duration_secs` enforced both between and inside external oracle
//! evaluations (setting `converged_1_minimal = false` if reached) and
//! memoization keyed by `(rendered_source, args)`. `converged_1_minimal`
//! certifies a fixed point across all 1-step structural deletions and the
//! non-monotonic scalar candidate neighborhood without budget exhaustion or
//! inconclusive probes.

use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

use serde::{Deserialize, Serialize};

use crate::{
    r#gen::{GenExpr, GenLocal, GenParam, GenProgram, GenStmt, GenType},
    verdict::{IntKind, MirValue, OrderingKind},
};

/// Budget bounds controlling counterexample minimization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkConfig {
    /// Maximum uncached oracle evaluations allowed before stopping early.
    pub max_steps: usize,
    /// Maximum wall-clock seconds allowed before stopping early.
    pub max_duration_secs: u64,
}

impl Default for ShrinkConfig {
    fn default() -> Self {
        Self { max_steps: 256, max_duration_secs: 90 }
    }
}

/// Diagnostic trace emitted after shrinking a failing [`GenProgram`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkTrace {
    pub original_nodes: usize,
    pub shrunk_nodes: usize,
    pub steps_evaluated: usize,
    pub oracle_runs: usize,
    pub cache_hits: usize,
    /// True iff all 5 passes reached a local 1-step fixed point over
    /// statement/expression deletions and the non-monotonic scalar candidate
    /// neighborhood with zero budget exhaustion and zero inconclusive probes.
    pub converged_1_minimal: bool,
    pub minimized_source: String,
    pub minimized_args: Vec<MirValue>,
}

/// Tri-state outcome of a single shrinker probe.
///
/// `Inconclusive` represents infrastructure errors or subprocess timeouts that
/// neither confirm nor refute candidate minimality; inconclusive probes are
/// never memo-cached and force `converged_1_minimal = false`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShrinkOutcome {
    Preserved,
    NotPreserved,
    Inconclusive,
}

/// Conversion trait allowing shrink predicates to return either `bool` or
/// [`ShrinkOutcome`].
pub trait IntoShrinkOutcome {
    fn into_shrink_outcome(self) -> ShrinkOutcome;
}

impl IntoShrinkOutcome for ShrinkOutcome {
    fn into_shrink_outcome(self) -> Self {
        self
    }
}

impl IntoShrinkOutcome for bool {
    fn into_shrink_outcome(self) -> ShrinkOutcome {
        if self { ShrinkOutcome::Preserved } else { ShrinkOutcome::NotPreserved }
    }
}

/// Deterministic memoizing wrapper around a failure predicate so repeated
/// equivalent candidates never re-invoke expensive multi-leg oracles.
pub struct MemoizedOracle<F> {
    inner: F,
    cache: BTreeMap<(String, String), bool>,
    pub oracle_runs: usize,
    pub cache_hits: usize,
    pub max_steps: usize,
    deadline: Instant,
    pub budget_exhausted: bool,
    pub had_inconclusive: bool,
}

impl<F: FnMut(&GenProgram) -> ShrinkOutcome> MemoizedOracle<F> {
    pub fn new(inner: F, config: &ShrinkConfig) -> Self {
        let deadline = Instant::now() + Duration::from_secs(config.max_duration_secs.max(1));
        Self::new_until(inner, config, deadline)
    }

    pub fn new_until(inner: F, config: &ShrinkConfig, deadline: Instant) -> Self {
        Self {
            inner,
            cache: BTreeMap::new(),
            oracle_runs: 0,
            cache_hits: 0,
            max_steps: config.max_steps,
            deadline,
            budget_exhausted: false,
            had_inconclusive: false,
        }
    }

    pub fn deadline(&self) -> Instant {
        self.deadline
    }

    pub fn total_steps(&self) -> usize {
        self.oracle_runs + self.cache_hits
    }

    pub fn eval(&mut self, prog: &GenProgram) -> Option<bool> {
        let key = program_cache_key(prog);
        if let Some(&hit) = self.cache.get(&key) {
            self.cache_hits += 1;
            return Some(hit);
        }
        if self.oracle_runs >= self.max_steps || Instant::now() >= self.deadline {
            self.budget_exhausted = true;
            return None;
        }
        self.oracle_runs += 1;
        match (self.inner)(prog) {
            ShrinkOutcome::Preserved => {
                self.cache.insert(key, true);
                Some(true)
            }
            ShrinkOutcome::NotPreserved => {
                self.cache.insert(key, false);
                Some(false)
            }
            ShrinkOutcome::Inconclusive => {
                self.had_inconclusive = true;
                if Instant::now() >= self.deadline {
                    self.budget_exhausted = true;
                    return None;
                }
                Some(false)
            }
        }
    }
}

fn program_cache_key(prog: &GenProgram) -> (String, String) {
    let src = prog.render_fn_item();
    let args_key = prog.args().iter().map(ToString::to_string).collect::<Vec<_>>().join(",");
    (src, args_key)
}

/// Shrink `initial` to a recursive 1-minimal [`GenProgram`] preserving
/// `predicate(&cand) == ShrinkOutcome::Preserved`.
///
/// Returns `(minimized_program, ShrinkTrace)`. If `predicate(initial)` does not
/// preserve the failure on entry, returns `(initial.clone(), ...)` with
/// `converged_1_minimal: false`.
pub fn shrink_program<F, R>(
    initial: &GenProgram,
    config: &ShrinkConfig,
    mut predicate: F,
) -> (GenProgram, ShrinkTrace)
where
    F: FnMut(&GenProgram) -> R,
    R: IntoShrinkOutcome,
{
    shrink_program_with_deadline(initial, config, |prog, _deadline| predicate(prog))
}

/// Deadline-aware variant of [`shrink_program`] that supplies the campaign's
/// wall-clock cutoff `Instant` to `predicate` so external subprocess legs can
/// clamp their execution timeouts to the remaining shrink budget.
pub fn shrink_program_with_deadline<F, R>(
    initial: &GenProgram,
    config: &ShrinkConfig,
    mut predicate: F,
) -> (GenProgram, ShrinkTrace)
where
    F: FnMut(&GenProgram, Instant) -> R,
    R: IntoShrinkOutcome,
{
    let original_nodes = initial.node_count();
    let deadline = Instant::now() + Duration::from_secs(config.max_duration_secs.max(1));
    let mut oracle = MemoizedOracle::new_until(
        |prog: &GenProgram| predicate(prog, deadline).into_shrink_outcome(),
        config,
        deadline,
    );

    let initial_holds = oracle.eval(initial).unwrap_or(false);
    if !initial_holds {
        let trace = ShrinkTrace {
            original_nodes,
            shrunk_nodes: original_nodes,
            steps_evaluated: oracle.total_steps(),
            oracle_runs: oracle.oracle_runs,
            cache_hits: oracle.cache_hits,
            converged_1_minimal: false,
            minimized_source: initial.render_standalone(),
            minimized_args: initial.args(),
        };
        return (initial.clone(), trace);
    }

    let mut best = initial.clone();
    let mut last_param_converged_key: Option<(String, String)> = None;

    loop {
        let mut improved = false;

        // Pass 1: Statement deletion (ddmin) across top-level body.
        if shrink_top_level_stmts(&mut best, &mut oracle) {
            improved = true;
        }
        if oracle.budget_exhausted {
            break;
        }

        // Pass 2: Recursive branch collapse, loop unrolling / bound / guard
        // shrinking, MoveReinit lowering, and nested block ddmin.
        if shrink_stmt_structures(&mut best, &mut oracle) {
            improved = true;
        }
        if oracle.budget_exhausted {
            break;
        }

        // Pass 3: Recursive expression simplification (return expr, all nested
        // statements, loop guards, match scrutinees/arms, and local inits).
        if shrink_all_expressions(&mut best, &mut oracle) {
            improved = true;
        }
        if oracle.budget_exhausted {
            break;
        }

        // Pass 4: Unused local and parameter elimination.
        if shrink_unused_locals_and_params(&mut best, &mut oracle) {
            improved = true;
        }
        if oracle.budget_exhausted {
            break;
        }

        // Pass 5: Concrete input argument narrowing via ascending non-monotonic
        // candidate enumeration (`0..=12`, powers of two, byte/word masks,
        // dyadic eighths, single-bit clears, sign flips, and immediate
        // neighbors toward `0`). Skip if Passes 1-4 left `best` unchanged since
        // Pass 5 last ran.
        if last_param_converged_key.as_ref() != Some(&program_cache_key(&best)) {
            if shrink_param_values(&mut best, &mut oracle) {
                improved = true;
            }
            if !oracle.budget_exhausted {
                last_param_converged_key = Some(program_cache_key(&best));
            }
        }
        if oracle.budget_exhausted || !improved {
            break;
        }
    }

    let converged_1_minimal = !oracle.budget_exhausted && !oracle.had_inconclusive;
    let trace = ShrinkTrace {
        original_nodes,
        shrunk_nodes: best.node_count(),
        steps_evaluated: oracle.total_steps(),
        oracle_runs: oracle.oracle_runs,
        cache_hits: oracle.cache_hits,
        converged_1_minimal,
        minimized_source: best.render_standalone(),
        minimized_args: best.args(),
    };
    (best, trace)
}

/// Delta-debugging (`ddmin`) subsequence minimizer for statement vectors.
fn ddmin_stmts<F>(
    stmts: &[GenStmt],
    build_prog: &mut dyn FnMut(&[GenStmt]) -> GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> Option<Vec<GenStmt>>
where
    F: FnMut(&GenProgram) -> ShrinkOutcome,
{
    if stmts.is_empty() {
        return None;
    }

    let empty_prog = build_prog(&[]);
    if oracle.eval(&empty_prog)? {
        return Some(Vec::new());
    }

    let mut best = stmts.to_vec();
    let mut changed = false;
    let mut chunk_size = best.len().div_ceil(2);

    loop {
        let mut pos = 0usize;
        let mut sweep_improved = false;
        while pos < best.len() {
            let end = (pos + chunk_size).min(best.len());
            if end - pos == best.len() {
                break;
            }
            let mut cand_stmts = Vec::with_capacity(best.len() - (end - pos));
            cand_stmts.extend_from_slice(&best[..pos]);
            cand_stmts.extend_from_slice(&best[end..]);
            let cand_prog = build_prog(&cand_stmts);
            match oracle.eval(&cand_prog) {
                Some(true) => {
                    best = cand_stmts;
                    changed = true;
                    sweep_improved = true;
                }
                Some(false) => {
                    pos += 1;
                }
                None => return if changed { Some(best) } else { None },
            }
        }
        if chunk_size == 1 {
            if !sweep_improved {
                break;
            }
            if best.len() >= 2 {
                chunk_size = best.len().div_ceil(2);
            }
        } else {
            chunk_size = chunk_size.div_ceil(2).min(best.len().div_ceil(2)).max(1);
        }
    }

    if changed { Some(best) } else { None }
}

fn shrink_top_level_stmts<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    best: &mut GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let base = best.clone();
    let mut build = |cand: &[GenStmt]| {
        let mut p = base.clone();
        p.body = cand.to_vec();
        p
    };
    if let Some(min_body) = ddmin_stmts(&base.body, &mut build, oracle) {
        best.body = min_body;
        return true;
    }
    false
}

fn shrink_stmt_structures<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    best: &mut GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let base = best.clone();
    let mut work = best.body.clone();
    let mut build = |cand: &[GenStmt]| {
        let mut p = base.clone();
        p.body = cand.to_vec();
        p
    };
    if shrink_stmt_list_structures(&mut work, &mut build, oracle) {
        best.body = work;
        return true;
    }
    false
}

fn shrink_stmt_list_structures<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    stmts: &mut Vec<GenStmt>,
    build_list: &mut dyn FnMut(&[GenStmt]) -> GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let mut improved = false;

    if let Some(shrunk) = ddmin_stmts(stmts, build_list, oracle) {
        *stmts = shrunk;
        improved = true;
    }
    if oracle.budget_exhausted {
        return improved;
    }

    let mut idx = 0usize;
    while idx < stmts.len() {
        if oracle.budget_exhausted {
            break;
        }
        let stmt = stmts[idx].clone();
        match stmt {
            GenStmt::MoveReinit { local, expr } => {
                let mut cand = stmts.clone();
                cand[idx] = GenStmt::Assign { local, expr };
                if oracle.eval(&build_list(&cand)) == Some(true) {
                    *stmts = cand;
                    improved = true;
                    continue;
                }
            }
            GenStmt::IfElse { cond, mut then_body, mut else_body } => {
                // 1. Try collapsing `if cond { A } else { B }` to `A` alone.
                let mut cand_then = stmts.clone();
                cand_then.splice(idx..=idx, then_body.clone());
                if oracle.eval(&build_list(&cand_then)) == Some(true) {
                    *stmts = cand_then;
                    improved = true;
                    continue;
                }
                if oracle.budget_exhausted {
                    break;
                }

                // 2. Try collapsing to `B` alone.
                let mut cand_else = stmts.clone();
                cand_else.splice(idx..=idx, else_body.clone());
                if oracle.eval(&build_list(&cand_else)) == Some(true) {
                    *stmts = cand_else;
                    improved = true;
                    continue;
                }
                if oracle.budget_exhausted {
                    break;
                }

                // 3. If `else_body` is non-empty, try dropping it.
                if !else_body.is_empty() {
                    let mut cand_no_else = stmts.clone();
                    cand_no_else[idx] = GenStmt::IfElse {
                        cond: cond.clone(),
                        then_body: then_body.clone(),
                        else_body: Vec::new(),
                    };
                    if oracle.eval(&build_list(&cand_no_else)) == Some(true) {
                        *stmts = cand_no_else;
                        improved = true;
                        continue;
                    }
                    if oracle.budget_exhausted {
                        break;
                    }
                }

                // 4. Recursively shrink `then_body` structures + ddmin.
                {
                    let snap = stmts.clone();
                    let cond_c = cond.clone();
                    let eb_c = else_body.clone();
                    let mut build_then = |sub: &[GenStmt]| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::IfElse {
                            cond: cond_c.clone(),
                            then_body: sub.to_vec(),
                            else_body: eb_c.clone(),
                        };
                        build_list(&next)
                    };
                    if shrink_stmt_list_structures(&mut then_body, &mut build_then, oracle) {
                        stmts[idx] = GenStmt::IfElse {
                            cond: cond.clone(),
                            then_body: then_body.clone(),
                            else_body: else_body.clone(),
                        };
                        improved = true;
                        if oracle.budget_exhausted {
                            break;
                        }
                    }
                }

                // 5. Recursively shrink `else_body` structures + ddmin.
                if !else_body.is_empty() && !oracle.budget_exhausted {
                    let snap = stmts.clone();
                    let cond_c = cond.clone();
                    let tb_c = then_body.clone();
                    let mut build_else = |sub: &[GenStmt]| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::IfElse {
                            cond: cond_c.clone(),
                            then_body: tb_c.clone(),
                            else_body: sub.to_vec(),
                        };
                        build_list(&next)
                    };
                    if shrink_stmt_list_structures(&mut else_body, &mut build_else, oracle) {
                        stmts[idx] = GenStmt::IfElse { cond, then_body, else_body };
                        improved = true;
                        if oracle.budget_exhausted {
                            break;
                        }
                    }
                }
            }
            GenStmt::WhileLoop { bound, mut body, break_cond, continue_cond } => {
                // 1. Try unrolling the loop into its body statements once.
                let mut cand_unroll = stmts.clone();
                cand_unroll.splice(idx..=idx, body.clone());
                if oracle.eval(&build_list(&cand_unroll)) == Some(true) {
                    *stmts = cand_unroll;
                    improved = true;
                    continue;
                }
                if oracle.budget_exhausted {
                    break;
                }

                // 2. Try dropping `break_cond` / `continue_cond`.
                if break_cond.is_some() {
                    let mut cand = stmts.clone();
                    cand[idx] = GenStmt::WhileLoop {
                        bound,
                        body: body.clone(),
                        break_cond: None,
                        continue_cond: continue_cond.clone(),
                    };
                    if oracle.eval(&build_list(&cand)) == Some(true) {
                        *stmts = cand;
                        improved = true;
                        continue;
                    }
                    if oracle.budget_exhausted {
                        break;
                    }
                }
                if continue_cond.is_some() {
                    let mut cand = stmts.clone();
                    cand[idx] = GenStmt::WhileLoop {
                        bound,
                        body: body.clone(),
                        break_cond: break_cond.clone(),
                        continue_cond: None,
                    };
                    if oracle.eval(&build_list(&cand)) == Some(true) {
                        *stmts = cand;
                        improved = true;
                        continue;
                    }
                    if oracle.budget_exhausted {
                        break;
                    }
                }

                // 3. Shrink `bound` toward `0`, `1`, `bound / 2`, `bound - 1`.
                if bound > 0 {
                    let mut bound_cands = vec![0u32];
                    if bound > 1 {
                        bound_cands.push(1);
                    }
                    if bound / 2 > 1 {
                        bound_cands.push(bound / 2);
                    }
                    if bound > 1 && !bound_cands.contains(&(bound - 1)) {
                        bound_cands.push(bound - 1);
                    }
                    let mut shrank_bound = false;
                    for b in bound_cands {
                        if b >= bound {
                            continue;
                        }
                        let mut cand = stmts.clone();
                        cand[idx] = GenStmt::WhileLoop {
                            bound: b,
                            body: body.clone(),
                            break_cond: break_cond.clone(),
                            continue_cond: continue_cond.clone(),
                        };
                        match oracle.eval(&build_list(&cand)) {
                            Some(true) => {
                                *stmts = cand;
                                improved = true;
                                shrank_bound = true;
                                break;
                            }
                            Some(false) => {}
                            None => return improved,
                        }
                    }
                    if shrank_bound {
                        continue;
                    }
                }

                // 4. Recursively shrink nested loop body structures + ddmin.
                if !oracle.budget_exhausted {
                    let snap = stmts.clone();
                    let bc_c = break_cond.clone();
                    let cc_c = continue_cond.clone();
                    let mut build_body = |sub: &[GenStmt]| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::WhileLoop {
                            bound,
                            body: sub.to_vec(),
                            break_cond: bc_c.clone(),
                            continue_cond: cc_c.clone(),
                        };
                        build_list(&next)
                    };
                    if shrink_stmt_list_structures(&mut body, &mut build_body, oracle) {
                        stmts[idx] = GenStmt::WhileLoop { bound, body, break_cond, continue_cond };
                        improved = true;
                        if oracle.budget_exhausted {
                            break;
                        }
                    }
                }
            }
            _ => {}
        }
        idx += 1;
    }
    improved
}

/// Strictly well-founded lexicographic complexity rank `(tier, primary, sub)`
/// with zero `u128` saturation across the full `0..=u128::MAX` range.
type Rank = (u8, u128, u8);

fn expr_rank(expr: &GenExpr) -> Rank {
    let nodes = expr.node_count();
    if nodes > 1 {
        return (10, nodes as u128, 0);
    }
    match expr {
        GenExpr::Lit(v) => {
            let (vt, vp, vs) = value_rank(v);
            (vt.min(3), vp, vs)
        }
        GenExpr::Param(i) => (4, *i as u128, 0),
        GenExpr::Local(i) => (5, *i as u128, 0),
        _ => (10, 1, 0),
    }
}

/// Strictly well-founded complexity rank for a concrete [`MirValue`].
fn value_rank(v: &MirValue) -> Rank {
    match v {
        MirValue::Unit => (0, 0, 0),
        MirValue::Bool { value: false } => (0, 0, 0),
        MirValue::Bool { value: true } => (0, 1, 0),
        MirValue::Ordering { value: OrderingKind::Equal } => (0, 0, 0),
        MirValue::Ordering { value: OrderingKind::Less } => (0, 1, 0),
        MirValue::Ordering { value: OrderingKind::Greater } => (0, 2, 0),
        MirValue::Char { scalar } => match *scalar {
            0 => (0, 0, 0),
            0x41 => (0, 1, 0),
            other => (1, u128::from(other), 0),
        },
        MirValue::Enum { variant_index, .. } => (0, *variant_index as u128, 0),
        MirValue::Int { int_kind, bits } => int_value_rank(*int_kind, *bits),
        MirValue::OverflowPair { int_kind, bits, overflow } => {
            let (t, p, s) = int_value_rank(*int_kind, *bits);
            (t, p, s.saturating_mul(2) + u8::from(*overflow))
        }
    }
}

fn int_value_rank(kind: IntKind, bits: u128) -> Rank {
    let masked = bits & kind.mask();
    if masked == 0 {
        return (0, 0, 0);
    }
    if masked == 1 {
        return (0, 1, 0);
    }
    if kind.is_signed() {
        let sv = kind.to_signed_i128(masked);
        if sv == -1 {
            return (0, 2, 0);
        }
        let mag = sv.unsigned_abs();
        return if sv > 0 { (1, mag, 0) } else { (1, mag, 1) };
    }
    (1, masked, 0)
}

/// Generate strictly simpler same-type replacement candidates for `expr`.
fn expr_simplifications(expr: &GenExpr, params: &[GenParam], locals: &[GenLocal]) -> Vec<GenExpr> {
    let target_ty = expr.ty(params, locals);
    let cur_rank = expr_rank(expr);
    let mut cands: Vec<GenExpr> = Vec::new();

    // 1. Canonical typed literals (`0`, `1`, `-1`, `false`, `'A'`, etc.).
    for lit in canonical_literals(target_ty) {
        let e = GenExpr::Lit(lit);
        if expr_rank(&e) < cur_rank {
            cands.push(e);
        }
    }

    // 2. Direct same-type sub-expressions.
    match expr {
        GenExpr::BinArith { lhs, rhs, .. } | GenExpr::SysrootNum { lhs, rhs, .. } => {
            cands.push((**lhs).clone());
            cands.push((**rhs).clone());
        }
        GenExpr::Shift { lhs, .. } => {
            cands.push((**lhs).clone());
        }
        GenExpr::Unary { operand, .. } => {
            cands.push((**operand).clone());
        }
        GenExpr::BoolLogic { lhs, rhs, .. } => {
            cands.push((**lhs).clone());
            cands.push((**rhs).clone());
        }
        GenExpr::MatchOrdering { less, equal, greater, .. } => {
            cands.push((**less).clone());
            cands.push((**equal).clone());
            cands.push((**greater).clone());
        }
        GenExpr::MatchEnum { arms, .. } => {
            for arm in arms {
                cands.push(arm.clone());
            }
        }
        GenExpr::MatchInt { scrutinee, scrutinee_ty, ty, arms, otherwise } => {
            cands.push((**otherwise).clone());
            for (_, arm) in arms {
                cands.push(arm.clone());
            }
            for drop_idx in 0..arms.len() {
                let mut smaller = arms.clone();
                smaller.remove(drop_idx);
                cands.push(GenExpr::MatchInt {
                    scrutinee: scrutinee.clone(),
                    scrutinee_ty: *scrutinee_ty,
                    ty: *ty,
                    arms: smaller,
                    otherwise: otherwise.clone(),
                });
            }
        }
        GenExpr::MatchChar { scrutinee, ty, arms, otherwise } => {
            cands.push((**otherwise).clone());
            for (_, arm) in arms {
                cands.push(arm.clone());
            }
            for drop_idx in 0..arms.len() {
                let mut smaller = arms.clone();
                smaller.remove(drop_idx);
                cands.push(GenExpr::MatchChar {
                    scrutinee: scrutinee.clone(),
                    ty: *ty,
                    arms: smaller,
                    otherwise: otherwise.clone(),
                });
            }
        }
        GenExpr::Cast { expr: inner, src_ty, dst_ty } if src_ty == dst_ty => {
            cands.push((**inner).clone());
        }
        _ => {}
    }

    // 3. In-scope parameters and Copy locals of matching type.
    for (idx, p) in params.iter().enumerate() {
        if p.ty == target_ty && !matches!(p.ty, GenType::Enum(_)) {
            let e = GenExpr::Param(idx);
            if expr_rank(&e) < cur_rank {
                cands.push(e);
            }
        }
    }
    for (idx, l) in locals.iter().enumerate() {
        if l.ty == target_ty && !matches!(l.ty, GenType::Enum(_)) {
            let e = GenExpr::Local(idx);
            if expr_rank(&e) < cur_rank {
                cands.push(e);
            }
        }
    }

    cands.retain(|c| expr_rank(c) < cur_rank && c != expr);
    cands
}

fn canonical_literals(ty: GenType) -> Vec<MirValue> {
    match ty {
        GenType::Int(k) => {
            let mut out = vec![
                MirValue::Int { int_kind: k, bits: 0 },
                MirValue::Int { int_kind: k, bits: 1 },
            ];
            if k.is_signed() {
                out.push(MirValue::Int { int_kind: k, bits: k.mask() });
                out.push(MirValue::Int { int_kind: k, bits: 1u128 << (k.bits() - 1) });
            } else {
                out.push(MirValue::Int { int_kind: k, bits: k.mask() });
            }
            out
        }
        GenType::Bool => vec![MirValue::Bool { value: false }, MirValue::Bool { value: true }],
        GenType::Char => {
            vec![MirValue::Char { scalar: 0 }, MirValue::Char { scalar: u32::from(b'A') }]
        }
        GenType::Ordering => vec![
            MirValue::Ordering { value: OrderingKind::Equal },
            MirValue::Ordering { value: OrderingKind::Less },
            MirValue::Ordering { value: OrderingKind::Greater },
        ],
        GenType::Unit => vec![MirValue::Unit],
        GenType::Enum(ek) => vec![ek.mir_value(0)],
    }
}

fn shrink_expr_in_place<F>(
    cur: &mut GenExpr,
    params: &[GenParam],
    locals: &[GenLocal],
    build: &mut dyn FnMut(&GenExpr) -> GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool
where
    F: FnMut(&GenProgram) -> ShrinkOutcome,
{
    if oracle.budget_exhausted {
        return false;
    }

    // 1. Try simplifying the root expression itself first.
    let root_cands = expr_simplifications(cur, params, locals);
    for cand_expr in root_cands {
        let prog = build(&cand_expr);
        match oracle.eval(&prog) {
            Some(true) => {
                *cur = cand_expr;
                return true;
            }
            Some(false) => {}
            None => return false,
        }
    }

    // 2. Otherwise recursively try simplifying child expressions and arms.
    let mut improved = false;
    let snapshot = cur.clone();
    match cur {
        GenExpr::BinArith { lhs, rhs, .. }
        | GenExpr::Shift { lhs, rhs, .. }
        | GenExpr::SysrootNum { lhs, rhs, .. }
        | GenExpr::Cmp { lhs, rhs, .. }
        | GenExpr::BoolLogic { lhs, rhs, .. }
        | GenExpr::ThreeWayCmp { lhs, rhs } => {
            let mut l_clone = (**lhs).clone();
            let r_snap = (**rhs).clone();
            let mut build_l = |new_l: &GenExpr| {
                let mut e = snapshot.clone();
                replace_bin_children(&mut e, Some(new_l.clone()), Some(r_snap.clone()));
                build(&e)
            };
            if shrink_expr_in_place(&mut l_clone, params, locals, &mut build_l, oracle) {
                **lhs = l_clone;
                improved = true;
            }
            if !oracle.budget_exhausted {
                let l_now = (**lhs).clone();
                let mut r_clone = (**rhs).clone();
                let mut build_r = |new_r: &GenExpr| {
                    let mut e = snapshot.clone();
                    replace_bin_children(&mut e, Some(l_now.clone()), Some(new_r.clone()));
                    build(&e)
                };
                if shrink_expr_in_place(&mut r_clone, params, locals, &mut build_r, oracle) {
                    **rhs = r_clone;
                    improved = true;
                }
            }
        }
        GenExpr::Unary { op, ty, operand } => {
            let op_copy = *op;
            let ty_copy = *ty;
            let mut inner = (**operand).clone();
            let mut build_inner = |new_op: &GenExpr| {
                build(&GenExpr::Unary {
                    op: op_copy,
                    ty: ty_copy,
                    operand: Box::new(new_op.clone()),
                })
            };
            if shrink_expr_in_place(&mut inner, params, locals, &mut build_inner, oracle) {
                **operand = inner;
                improved = true;
            }
        }
        GenExpr::Cast { expr: inner_box, src_ty, dst_ty } => {
            let src_copy = *src_ty;
            let dst_copy = *dst_ty;
            let mut inner = (**inner_box).clone();
            let mut build_inner = |new_in: &GenExpr| {
                build(&GenExpr::Cast {
                    expr: Box::new(new_in.clone()),
                    src_ty: src_copy,
                    dst_ty: dst_copy,
                })
            };
            if shrink_expr_in_place(&mut inner, params, locals, &mut build_inner, oracle) {
                **inner_box = inner;
                improved = true;
            }
        }
        GenExpr::MatchOrdering { scrutinee, ty, less, equal, greater } => {
            let ty_copy = *ty;
            let mut s_val = (**scrutinee).clone();
            {
                let (l_s, e_s, g_s) = ((**less).clone(), (**equal).clone(), (**greater).clone());
                let mut build_s = |new_s: &GenExpr| {
                    build(&GenExpr::MatchOrdering {
                        scrutinee: Box::new(new_s.clone()),
                        ty: ty_copy,
                        less: Box::new(l_s.clone()),
                        equal: Box::new(e_s.clone()),
                        greater: Box::new(g_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut s_val, params, locals, &mut build_s, oracle) {
                    **scrutinee = s_val.clone();
                    improved = true;
                }
            }
            if !oracle.budget_exhausted {
                let mut l_val = (**less).clone();
                let (s_now, e_s, g_s) =
                    ((**scrutinee).clone(), (**equal).clone(), (**greater).clone());
                let mut build_l = |nl: &GenExpr| {
                    build(&GenExpr::MatchOrdering {
                        scrutinee: Box::new(s_now.clone()),
                        ty: ty_copy,
                        less: Box::new(nl.clone()),
                        equal: Box::new(e_s.clone()),
                        greater: Box::new(g_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut l_val, params, locals, &mut build_l, oracle) {
                    **less = l_val;
                    improved = true;
                }
            }
            if !oracle.budget_exhausted {
                let mut e_val = (**equal).clone();
                let (s_now, l_s, g_s) =
                    ((**scrutinee).clone(), (**less).clone(), (**greater).clone());
                let mut build_e = |ne: &GenExpr| {
                    build(&GenExpr::MatchOrdering {
                        scrutinee: Box::new(s_now.clone()),
                        ty: ty_copy,
                        less: Box::new(l_s.clone()),
                        equal: Box::new(ne.clone()),
                        greater: Box::new(g_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut e_val, params, locals, &mut build_e, oracle) {
                    **equal = e_val;
                    improved = true;
                }
            }
            if !oracle.budget_exhausted {
                let mut g_val = (**greater).clone();
                let (s_now, l_s, e_s) =
                    ((**scrutinee).clone(), (**less).clone(), (**equal).clone());
                let mut build_g = |ng: &GenExpr| {
                    build(&GenExpr::MatchOrdering {
                        scrutinee: Box::new(s_now.clone()),
                        ty: ty_copy,
                        less: Box::new(l_s.clone()),
                        equal: Box::new(e_s.clone()),
                        greater: Box::new(ng.clone()),
                    })
                };
                if shrink_expr_in_place(&mut g_val, params, locals, &mut build_g, oracle) {
                    **greater = g_val;
                    improved = true;
                }
            }
        }
        GenExpr::MatchEnum { param_idx, enum_kind, ty, arms } => {
            let pidx = *param_idx;
            let ek = *enum_kind;
            let ty_copy = *ty;
            for arm_idx in 0..arms.len() {
                if oracle.budget_exhausted {
                    break;
                }
                let arms_snap = arms.clone();
                let mut arm_val = arms[arm_idx].clone();
                let mut build_arm = |na: &GenExpr| {
                    let mut next = arms_snap.clone();
                    next[arm_idx] = na.clone();
                    build(&GenExpr::MatchEnum {
                        param_idx: pidx,
                        enum_kind: ek,
                        ty: ty_copy,
                        arms: next,
                    })
                };
                if shrink_expr_in_place(&mut arm_val, params, locals, &mut build_arm, oracle) {
                    arms[arm_idx] = arm_val;
                    improved = true;
                }
            }
        }
        GenExpr::MatchInt { scrutinee, scrutinee_ty, ty, arms, otherwise } => {
            let sty = *scrutinee_ty;
            let ty_copy = *ty;
            {
                let mut s_val = (**scrutinee).clone();
                let arms_s = arms.clone();
                let oth_s = (**otherwise).clone();
                let mut build_s = |ns: &GenExpr| {
                    build(&GenExpr::MatchInt {
                        scrutinee: Box::new(ns.clone()),
                        scrutinee_ty: sty,
                        ty: ty_copy,
                        arms: arms_s.clone(),
                        otherwise: Box::new(oth_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut s_val, params, locals, &mut build_s, oracle) {
                    **scrutinee = s_val;
                    improved = true;
                }
            }
            for arm_idx in 0..arms.len() {
                if oracle.budget_exhausted {
                    break;
                }
                let s_now = (**scrutinee).clone();
                let arms_s = arms.clone();
                let oth_s = (**otherwise).clone();
                let mut arm_val = arms[arm_idx].1.clone();
                let mut build_arm = |na: &GenExpr| {
                    let mut next = arms_s.clone();
                    next[arm_idx].1 = na.clone();
                    build(&GenExpr::MatchInt {
                        scrutinee: Box::new(s_now.clone()),
                        scrutinee_ty: sty,
                        ty: ty_copy,
                        arms: next,
                        otherwise: Box::new(oth_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut arm_val, params, locals, &mut build_arm, oracle) {
                    arms[arm_idx].1 = arm_val;
                    improved = true;
                }
            }
            if !oracle.budget_exhausted {
                let s_now = (**scrutinee).clone();
                let arms_s = arms.clone();
                let mut oth_val = (**otherwise).clone();
                let mut build_oth = |no: &GenExpr| {
                    build(&GenExpr::MatchInt {
                        scrutinee: Box::new(s_now.clone()),
                        scrutinee_ty: sty,
                        ty: ty_copy,
                        arms: arms_s.clone(),
                        otherwise: Box::new(no.clone()),
                    })
                };
                if shrink_expr_in_place(&mut oth_val, params, locals, &mut build_oth, oracle) {
                    **otherwise = oth_val;
                    improved = true;
                }
            }
        }
        GenExpr::MatchChar { scrutinee, ty, arms, otherwise } => {
            let ty_copy = *ty;
            {
                let mut s_val = (**scrutinee).clone();
                let arms_s = arms.clone();
                let oth_s = (**otherwise).clone();
                let mut build_s = |ns: &GenExpr| {
                    build(&GenExpr::MatchChar {
                        scrutinee: Box::new(ns.clone()),
                        ty: ty_copy,
                        arms: arms_s.clone(),
                        otherwise: Box::new(oth_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut s_val, params, locals, &mut build_s, oracle) {
                    **scrutinee = s_val;
                    improved = true;
                }
            }
            for arm_idx in 0..arms.len() {
                if oracle.budget_exhausted {
                    break;
                }
                let s_now = (**scrutinee).clone();
                let arms_s = arms.clone();
                let oth_s = (**otherwise).clone();
                let mut arm_val = arms[arm_idx].1.clone();
                let mut build_arm = |na: &GenExpr| {
                    let mut next = arms_s.clone();
                    next[arm_idx].1 = na.clone();
                    build(&GenExpr::MatchChar {
                        scrutinee: Box::new(s_now.clone()),
                        ty: ty_copy,
                        arms: next,
                        otherwise: Box::new(oth_s.clone()),
                    })
                };
                if shrink_expr_in_place(&mut arm_val, params, locals, &mut build_arm, oracle) {
                    arms[arm_idx].1 = arm_val;
                    improved = true;
                }
            }
            if !oracle.budget_exhausted {
                let s_now = (**scrutinee).clone();
                let arms_s = arms.clone();
                let mut oth_val = (**otherwise).clone();
                let mut build_oth = |no: &GenExpr| {
                    build(&GenExpr::MatchChar {
                        scrutinee: Box::new(s_now.clone()),
                        ty: ty_copy,
                        arms: arms_s.clone(),
                        otherwise: Box::new(no.clone()),
                    })
                };
                if shrink_expr_in_place(&mut oth_val, params, locals, &mut build_oth, oracle) {
                    **otherwise = oth_val;
                    improved = true;
                }
            }
        }
        _ => {}
    }
    improved
}

fn replace_bin_children(expr: &mut GenExpr, new_l: Option<GenExpr>, new_r: Option<GenExpr>) {
    match expr {
        GenExpr::BinArith { lhs, rhs, .. }
        | GenExpr::Shift { lhs, rhs, .. }
        | GenExpr::SysrootNum { lhs, rhs, .. }
        | GenExpr::Cmp { lhs, rhs, .. }
        | GenExpr::BoolLogic { lhs, rhs, .. }
        | GenExpr::ThreeWayCmp { lhs, rhs } => {
            if let Some(l) = new_l {
                **lhs = l;
            }
            if let Some(r) = new_r {
                **rhs = r;
            }
        }
        _ => {}
    }
}

fn shrink_all_expressions<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    best: &mut GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let mut improved = false;

    // 1. Return expression.
    let base_ret = best.clone();
    let mut ret_expr = best.ret_expr.clone();
    let mut build_ret = |e: &GenExpr| {
        let mut p = base_ret.clone();
        p.ret_expr = e.clone();
        p
    };
    if shrink_expr_in_place(
        &mut ret_expr,
        &base_ret.params,
        &base_ret.locals,
        &mut build_ret,
        oracle,
    ) {
        best.ret_expr = ret_expr;
        improved = true;
    }
    if oracle.budget_exhausted {
        return improved;
    }

    // 2. Recursive statement expressions across top-level and nested blocks.
    {
        let base_s = best.clone();
        let mut work_body = best.body.clone();
        let mut build_body = |cand: &[GenStmt]| {
            let mut p = base_s.clone();
            p.body = cand.to_vec();
            p
        };
        if shrink_stmt_list_expressions(
            &mut work_body,
            &base_s.params,
            &base_s.locals,
            &mut build_body,
            oracle,
        ) {
            best.body = work_body;
            improved = true;
        }
    }
    if oracle.budget_exhausted {
        return improved;
    }

    // 3. Local initializers (local `idx` initializer may only reference
    // parameters or earlier locals `0..idx`).
    for idx in 0..best.locals.len() {
        if oracle.budget_exhausted {
            break;
        }
        let base_l = best.clone();
        let mut init_e = base_l.locals[idx].init.clone();
        let earlier_locals = &base_l.locals[..idx];
        let mut build_l = |ne: &GenExpr| {
            let mut p = base_l.clone();
            p.locals[idx].init = ne.clone();
            p
        };
        if shrink_expr_in_place(&mut init_e, &base_l.params, earlier_locals, &mut build_l, oracle) {
            best.locals[idx].init = init_e;
            improved = true;
        }
    }

    improved
}

fn shrink_stmt_list_expressions<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    stmts: &mut [GenStmt],
    params: &[GenParam],
    locals: &[GenLocal],
    build_list: &mut dyn FnMut(&[GenStmt]) -> GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let mut improved = false;
    for idx in 0..stmts.len() {
        if oracle.budget_exhausted {
            break;
        }
        let snap = stmts.to_vec();
        match &snap[idx] {
            GenStmt::Assign { local, expr } => {
                let loc = *local;
                let mut e = expr.clone();
                let mut build_s = |ne: &GenExpr| {
                    let mut next = snap.clone();
                    next[idx] = GenStmt::Assign { local: loc, expr: ne.clone() };
                    build_list(&next)
                };
                if shrink_expr_in_place(&mut e, params, locals, &mut build_s, oracle) {
                    stmts[idx] = GenStmt::Assign { local: loc, expr: e };
                    improved = true;
                }
            }
            GenStmt::MoveReinit { local, expr } => {
                let loc = *local;
                let mut e = expr.clone();
                let mut build_s = |ne: &GenExpr| {
                    let mut next = snap.clone();
                    next[idx] = GenStmt::MoveReinit { local: loc, expr: ne.clone() };
                    build_list(&next)
                };
                if shrink_expr_in_place(&mut e, params, locals, &mut build_s, oracle) {
                    stmts[idx] = GenStmt::MoveReinit { local: loc, expr: e };
                    improved = true;
                }
            }
            GenStmt::IfElse { cond, then_body, else_body } => {
                let mut cur_cond = cond.clone();
                let mut cur_then = then_body.clone();
                let mut cur_else = else_body.clone();
                {
                    let tb = cur_then.clone();
                    let eb = cur_else.clone();
                    let mut build_c = |nc: &GenExpr| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::IfElse {
                            cond: nc.clone(),
                            then_body: tb.clone(),
                            else_body: eb.clone(),
                        };
                        build_list(&next)
                    };
                    if shrink_expr_in_place(&mut cur_cond, params, locals, &mut build_c, oracle) {
                        improved = true;
                    }
                }
                if !oracle.budget_exhausted {
                    let c_now = cur_cond.clone();
                    let eb = cur_else.clone();
                    let mut build_tb = |nt: &[GenStmt]| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::IfElse {
                            cond: c_now.clone(),
                            then_body: nt.to_vec(),
                            else_body: eb.clone(),
                        };
                        build_list(&next)
                    };
                    if shrink_stmt_list_expressions(
                        &mut cur_then,
                        params,
                        locals,
                        &mut build_tb,
                        oracle,
                    ) {
                        improved = true;
                    }
                }
                if !cur_else.is_empty() && !oracle.budget_exhausted {
                    let c_now = cur_cond.clone();
                    let tb = cur_then.clone();
                    let mut build_eb = |ne: &[GenStmt]| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::IfElse {
                            cond: c_now.clone(),
                            then_body: tb.clone(),
                            else_body: ne.to_vec(),
                        };
                        build_list(&next)
                    };
                    if shrink_stmt_list_expressions(
                        &mut cur_else,
                        params,
                        locals,
                        &mut build_eb,
                        oracle,
                    ) {
                        improved = true;
                    }
                }
                stmts[idx] =
                    GenStmt::IfElse { cond: cur_cond, then_body: cur_then, else_body: cur_else };
            }
            GenStmt::WhileLoop { bound, body, break_cond, continue_cond } => {
                let bnd = *bound;
                let mut cur_body = body.clone();
                let mut cur_bc = break_cond.clone();
                let mut cur_cc = continue_cond.clone();
                if let Some(mut bc_e) = cur_bc.clone() {
                    let body_s = cur_body.clone();
                    let cc_s = cur_cc.clone();
                    let mut build_bc = |nbc: &GenExpr| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::WhileLoop {
                            bound: bnd,
                            body: body_s.clone(),
                            break_cond: Some(nbc.clone()),
                            continue_cond: cc_s.clone(),
                        };
                        build_list(&next)
                    };
                    if shrink_expr_in_place(&mut bc_e, params, locals, &mut build_bc, oracle) {
                        cur_bc = Some(bc_e);
                        improved = true;
                    }
                }
                if !oracle.budget_exhausted
                    && let Some(mut cc_e) = cur_cc.clone()
                {
                    let body_s = cur_body.clone();
                    let bc_s = cur_bc.clone();
                    let mut build_cc = |ncc: &GenExpr| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::WhileLoop {
                            bound: bnd,
                            body: body_s.clone(),
                            break_cond: bc_s.clone(),
                            continue_cond: Some(ncc.clone()),
                        };
                        build_list(&next)
                    };
                    if shrink_expr_in_place(&mut cc_e, params, locals, &mut build_cc, oracle) {
                        cur_cc = Some(cc_e);
                        improved = true;
                    }
                }
                if !oracle.budget_exhausted {
                    let bc_s = cur_bc.clone();
                    let cc_s = cur_cc.clone();
                    let mut build_b = |nb: &[GenStmt]| {
                        let mut next = snap.clone();
                        next[idx] = GenStmt::WhileLoop {
                            bound: bnd,
                            body: nb.to_vec(),
                            break_cond: bc_s.clone(),
                            continue_cond: cc_s.clone(),
                        };
                        build_list(&next)
                    };
                    if shrink_stmt_list_expressions(
                        &mut cur_body,
                        params,
                        locals,
                        &mut build_b,
                        oracle,
                    ) {
                        improved = true;
                    }
                }
                stmts[idx] = GenStmt::WhileLoop {
                    bound: bnd,
                    body: cur_body,
                    break_cond: cur_bc,
                    continue_cond: cur_cc,
                };
            }
            _ => {}
        }
    }
    improved
}

fn shrink_unused_locals_and_params<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    best: &mut GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let mut improved = false;

    // 1. Delete any local not referenced by body, ret_expr, or later inits.
    loop {
        if oracle.budget_exhausted {
            break;
        }
        let mut used_params = BTreeSet::new();
        let mut used_locals = BTreeSet::new();
        for s in &best.body {
            s.collect_refs(&mut used_params, &mut used_locals);
        }
        best.ret_expr.collect_refs(&mut used_params, &mut used_locals);
        for l in &best.locals {
            l.init.collect_refs(&mut used_params, &mut used_locals);
        }

        let dead_locals: Vec<usize> =
            (0..best.locals.len()).rev().filter(|i| !used_locals.contains(i)).collect();
        let mut removed_any = false;
        for drop_idx in dead_locals {
            let mut cand = best.clone();
            remove_local(&mut cand, drop_idx);
            match oracle.eval(&cand) {
                Some(true) => {
                    *best = cand;
                    improved = true;
                    removed_any = true;
                    break;
                }
                Some(false) => {}
                None => return improved,
            }
        }
        if !removed_any {
            break;
        }
    }

    // 2. Delete any parameter not referenced anywhere in locals, body, or
    // ret_expr.
    loop {
        if oracle.budget_exhausted {
            break;
        }
        let mut used_params = BTreeSet::new();
        let mut used_locals = BTreeSet::new();
        for l in &best.locals {
            l.init.collect_refs(&mut used_params, &mut used_locals);
        }
        for s in &best.body {
            s.collect_refs(&mut used_params, &mut used_locals);
        }
        best.ret_expr.collect_refs(&mut used_params, &mut used_locals);

        let dead_params: Vec<usize> =
            (0..best.params.len()).rev().filter(|i| !used_params.contains(i)).collect();
        let mut removed_any = false;
        for drop_idx in dead_params {
            let mut cand = best.clone();
            remove_param(&mut cand, drop_idx);
            match oracle.eval(&cand) {
                Some(true) => {
                    *best = cand;
                    improved = true;
                    removed_any = true;
                    break;
                }
                Some(false) => {}
                None => return improved,
            }
        }
        if !removed_any {
            break;
        }
    }

    // 3. Drop the `unsafe fn` qualifier when no remaining expression or
    // statement syntactically uses `unsafe` and the oracle still reproduces.
    if !oracle.budget_exhausted && best.is_unsafe && !best.has_syntactic_unsafe() {
        let mut cand = best.clone();
        cand.is_unsafe = false;
        match oracle.eval(&cand) {
            Some(true) => {
                *best = cand;
                improved = true;
            }
            Some(false) => {}
            None => return improved,
        }
    }

    improved
}

fn remove_local(prog: &mut GenProgram, drop_idx: usize) {
    let old_n_params = prog.params.len();
    let old_n_locals = prog.locals.len();
    let param_map: Vec<Option<usize>> = (0..old_n_params).map(Some).collect();
    let mut local_map: Vec<Option<usize>> = Vec::with_capacity(old_n_locals);
    let mut next_id = 0usize;
    for i in 0..old_n_locals {
        if i == drop_idx {
            local_map.push(None);
        } else {
            local_map.push(Some(next_id));
            next_id += 1;
        }
    }
    prog.locals.remove(drop_idx);
    for l in &mut prog.locals {
        l.init.remap_indices(&param_map, &local_map);
    }
    for s in &mut prog.body {
        s.remap_indices(&param_map, &local_map);
    }
    prog.ret_expr.remap_indices(&param_map, &local_map);
}

fn remove_param(prog: &mut GenProgram, drop_idx: usize) {
    let old_n_params = prog.params.len();
    let old_n_locals = prog.locals.len();
    let mut param_map: Vec<Option<usize>> = Vec::with_capacity(old_n_params);
    let mut next_id = 0usize;
    for i in 0..old_n_params {
        if i == drop_idx {
            param_map.push(None);
        } else {
            param_map.push(Some(next_id));
            next_id += 1;
        }
    }
    let local_map: Vec<Option<usize>> = (0..old_n_locals).map(Some).collect();
    prog.params.remove(drop_idx);
    for l in &mut prog.locals {
        l.init.remap_indices(&param_map, &local_map);
    }
    for s in &mut prog.body {
        s.remap_indices(&param_map, &local_map);
    }
    prog.ret_expr.remap_indices(&param_map, &local_map);
}

fn shrink_param_values<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    best: &mut GenProgram,
    oracle: &mut MemoizedOracle<F>,
) -> bool {
    let n = best.params.len();
    if n == 0 {
        return false;
    }
    let mut improved = false;
    let mut converged = vec![false; n];
    while !converged.iter().all(|&c| c) {
        for idx in 0..n {
            if converged[idx] {
                continue;
            }
            if oracle.budget_exhausted {
                return improved;
            }
            let (did_narrow, finished_scan) = narrow_single_param(best, idx, oracle);
            if did_narrow {
                improved = true;
                converged.fill(false);
            }
            if finished_scan {
                converged[idx] = true;
            }
            if oracle.budget_exhausted || !finished_scan {
                return improved;
            }
        }
    }
    improved
}

fn narrow_single_param<F: FnMut(&GenProgram) -> ShrinkOutcome>(
    best: &mut GenProgram,
    idx: usize,
    oracle: &mut MemoizedOracle<F>,
) -> (bool, bool) {
    let mut improved = false;
    loop {
        if oracle.budget_exhausted {
            return (improved, false);
        }
        let cur_val = best.params[idx].value.clone();
        let cur_rank = value_rank(&cur_val);
        let cands = value_narrowing_candidates(&cur_val);
        let mut accepted = false;
        for cand_val in cands {
            if value_rank(&cand_val) >= cur_rank {
                continue;
            }
            let mut cand = best.clone();
            cand.params[idx].value = cand_val;
            match oracle.eval(&cand) {
                Some(true) => {
                    *best = cand;
                    improved = true;
                    accepted = true;
                    break;
                }
                Some(false) => {}
                None => return (improved, false),
            }
        }
        if !accepted {
            return (improved, true);
        }
    }
}

/// Strictly simpler candidate values in ascending [`value_rank`] order without
/// monotonicity assumptions (a rejected intermediate probe never prunes
/// remaining candidates).
fn int_narrowing_candidates(k: IntKind, cur_bits: u128) -> Vec<MirValue> {
    let mask = k.mask();
    let cur_masked = cur_bits & mask;
    if cur_masked == 0 {
        return Vec::new();
    }
    let cur_val = MirValue::Int { int_kind: k, bits: cur_masked };
    let cur_rank = value_rank(&cur_val);

    let mag = if k.is_signed() { k.to_signed_i128(cur_masked).unsigned_abs() } else { cur_masked };

    let mut mags = BTreeSet::new();
    for small in 0u128..=12 {
        if small < mag {
            mags.insert(small);
        }
    }

    const SPARSE_POW2_BITS: &[u32] = &[4, 5, 6, 7, 8, 12, 16, 24, 31, 32, 48, 63, 64, 96, 127];
    for &b in SPARSE_POW2_BITS {
        if b < k.bits() {
            let p = 1u128 << b;
            if p < mag {
                mags.insert(p);
            }
        }
    }
    if mag >= 2 {
        let top_bit = 127 - mag.leading_zeros();
        let highest_pow2 = 1u128 << top_bit;
        for shift in [0u32, 1, 2] {
            let p = highest_pow2 >> shift;
            if p > 0 && p < mag {
                mags.insert(p);
            }
        }
    }

    for byte_mask in [0xFFu128, 0xFFFF, 0xFFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF] {
        if byte_mask < mag {
            mags.insert(byte_mask);
        }
    }

    for num in 1u128..=7 {
        let dyadic = (mag >> 3) * num + (((mag & 7) * num) >> 3);
        if dyadic < mag {
            mags.insert(dyadic);
        }
    }

    let set_bits: Vec<u32> = (0..k.bits()).filter(|&b| ((mag >> b) & 1) == 1).collect();
    if set_bits.len() <= 16 {
        for b in set_bits {
            mags.insert(mag & !(1u128 << b));
        }
    } else {
        for &b in set_bits.iter().take(8).chain(set_bits.iter().rev().take(8)) {
            mags.insert(mag & !(1u128 << b));
        }
    }

    mags.insert(mag.saturating_sub(2));
    mags.insert(mag.saturating_sub(1));

    let mut out = Vec::new();
    if !k.is_signed() {
        for m in mags {
            out.push(MirValue::Int { int_kind: k, bits: m & mask });
        }
    } else {
        let sv = k.to_signed_i128(cur_masked);
        let max_pos = (1u128 << (k.bits() - 1)) - 1;
        if sv > 0 {
            if sv > 1 {
                out.push(MirValue::Int { int_kind: k, bits: mask }); // -1
            }
            for m in mags {
                if m <= max_pos {
                    out.push(MirValue::Int { int_kind: k, bits: m & mask });
                }
            }
        } else {
            out.push(MirValue::Int { int_kind: k, bits: mag.min(max_pos) & mask });
            for small in 0u128..=12 {
                if small <= max_pos && small <= mag {
                    out.push(MirValue::Int { int_kind: k, bits: small & mask });
                }
            }
            for m in mags {
                if m >= 1 && m < mag {
                    let neg_bits = 0u128.wrapping_sub(m) & mask;
                    out.push(MirValue::Int { int_kind: k, bits: neg_bits });
                }
            }
        }
    }

    out.retain(|v| value_rank(v) < cur_rank);
    out.sort_by_key(value_rank);
    out.dedup();
    out
}

/// Strictly simpler candidate values for scalar and enum parameters.
fn value_narrowing_candidates(val: &MirValue) -> Vec<MirValue> {
    let mut out = Vec::new();
    match val {
        MirValue::Int { int_kind, bits } => {
            return int_narrowing_candidates(*int_kind, *bits);
        }
        MirValue::Bool { value: true } => {
            out.push(MirValue::Bool { value: false });
        }
        MirValue::Char { scalar } => {
            let mut raw = vec![0u32, u32::from(b'A')];
            if *scalar > 1 {
                let half = *scalar / 2;
                if char::from_u32(half).is_some() {
                    raw.push(half);
                }
                let prev = if *scalar == 0xE000 { 0xD7FF } else { *scalar - 1 };
                if char::from_u32(prev).is_some() {
                    raw.push(prev);
                }
            }
            let cur_rank = value_rank(val);
            for sc in raw {
                let mv = MirValue::Char { scalar: sc };
                if value_rank(&mv) < cur_rank && !out.contains(&mv) {
                    out.push(mv);
                }
            }
        }
        MirValue::Ordering { value } => {
            if *value != OrderingKind::Equal {
                out.push(MirValue::Ordering { value: OrderingKind::Equal });
            }
            if *value == OrderingKind::Greater {
                out.push(MirValue::Ordering { value: OrderingKind::Less });
            }
        }
        MirValue::Enum { enum_type, variant_index, .. } if *variant_index > 0 => {
            if let Some(ek) =
                crate::r#gen::GenEnumKind::ALL.iter().copied().find(|k| k.rust_name() == enum_type)
            {
                out.push(ek.mir_value(0));
                if *variant_index > 1 {
                    out.push(ek.mir_value(variant_index - 1));
                }
            }
        }
        _ => {}
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r#gen::{
        GenArithOp, GenBoolBinOp, GenCategory, GenCmpOp, GenLocal, GenParam, GenSysrootNumOp,
        GenType,
    };

    fn sample_multi_stmt_program() -> GenProgram {
        // 4 statements (decoys, branch, loop, move-reinit) + 3 parameters.
        GenProgram {
            case_id: "shrink_unit".to_owned(),
            fn_name: "shrink_target".to_owned(),
            master_seed: 1,
            case_index: 0,
            category: GenCategory::TargetedUbProbe,
            is_unsafe: true,
            params: vec![
                GenParam {
                    ty: GenType::Int(IntKind::I32),
                    value: MirValue::Int { int_kind: IntKind::I32, bits: i32::MAX as u128 },
                },
                GenParam {
                    ty: GenType::Int(IntKind::I32),
                    value: MirValue::Int { int_kind: IntKind::I32, bits: 17 },
                },
                GenParam {
                    ty: GenType::Int(IntKind::U32),
                    value: MirValue::Int { int_kind: IntKind::U32, bits: 999 },
                },
            ],
            locals: vec![
                GenLocal { ty: GenType::Int(IntKind::I32), init: GenExpr::Param(0) },
                GenLocal { ty: GenType::Int(IntKind::U32), init: GenExpr::Param(2) },
            ],
            body: vec![
                GenStmt::Assign {
                    local: 1,
                    expr: GenExpr::BinArith {
                        op: GenArithOp::Add,
                        ty: IntKind::U32,
                        lhs: Box::new(GenExpr::Local(1)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::U32,
                            bits: 7,
                        })),
                    },
                },
                GenStmt::WhileLoop {
                    bound: 8,
                    body: vec![GenStmt::Assign {
                        local: 1,
                        expr: GenExpr::BinArith {
                            op: GenArithOp::BitXor,
                            ty: IntKind::U32,
                            lhs: Box::new(GenExpr::Local(1)),
                            rhs: Box::new(GenExpr::Lit(MirValue::Int {
                                int_kind: IntKind::U32,
                                bits: 3,
                            })),
                        },
                    }],
                    break_cond: None,
                    continue_cond: None,
                },
                GenStmt::IfElse {
                    cond: GenExpr::Cmp {
                        op: GenCmpOp::Gt,
                        lhs: Box::new(GenExpr::Local(1)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::U32,
                            bits: 0,
                        })),
                    },
                    then_body: vec![GenStmt::Assign {
                        local: 0,
                        expr: GenExpr::SysrootNum {
                            op: GenSysrootNumOp::UncheckedAdd,
                            ty: IntKind::I32,
                            lhs: Box::new(GenExpr::Local(0)),
                            rhs: Box::new(GenExpr::Param(1)),
                            guarded: false,
                        },
                    }],
                    else_body: vec![GenStmt::Assign {
                        local: 1,
                        expr: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 5 }),
                    }],
                },
                GenStmt::MoveReinit {
                    local: 1,
                    expr: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 42 }),
                },
            ],
            ret_ty: GenType::Int(IntKind::I32),
            ret_expr: GenExpr::Local(0),
            fuel: 300,
        }
    }

    #[test]
    fn shrinker_collapses_branch_deletes_decoys_and_narrows_inputs_to_1_minimal() {
        let initial = sample_multi_stmt_program();
        // Simulated broken-oracle predicate: fails whenever the program
        // executes an unguarded `unchecked_add` with `p0 == i32::MAX` and
        // `p1 > 0`.
        let (min_prog, trace) = shrink_program(
            &initial,
            &ShrinkConfig { max_steps: 400, max_duration_secs: 30 },
            |p| {
                let src = p.render_fn_item();
                src.contains("unchecked_add")
                    && p.params.iter().any(|arg| {
                        matches!(
                            arg.value,
                            MirValue::Int { int_kind: IntKind::I32, bits }
                                if bits == i32::MAX as u128
                        )
                    })
                    && p.params.iter().any(|arg| {
                        matches!(
                            arg.value,
                            MirValue::Int { int_kind: IntKind::I32, bits }
                                if (bits as i32) > 0 && bits != i32::MAX as u128
                        )
                    })
                    && p.body.iter().any(|s| {
                        matches!(
                            s,
                            GenStmt::Assign {
                                expr: GenExpr::SysrootNum {
                                    op: GenSysrootNumOp::UncheckedAdd,
                                    guarded: false,
                                    ..
                                },
                                ..
                            }
                        ) || matches!(
                            s,
                            GenStmt::IfElse { then_body, .. }
                                if then_body.iter().any(|inner| matches!(
                                    inner,
                                    GenStmt::Assign {
                                        expr: GenExpr::SysrootNum {
                                            op: GenSysrootNumOp::UncheckedAdd,
                                            guarded: false,
                                            ..
                                        },
                                        ..
                                    }
                                ))
                        )
                    })
            },
        );

        assert!(trace.converged_1_minimal, "expected 1-minimal convergence: {trace:#?}");
        assert!(
            trace.shrunk_nodes < trace.original_nodes,
            "expected node reduction: {} -> {}",
            trace.original_nodes,
            trace.shrunk_nodes
        );
        // Loop, unused local `v1`, unused param `p2`, and `if/else` wrapper
        // must all disappear.
        assert_eq!(min_prog.body.len(), 1, "shrunk body: {:?}", min_prog.body);
        assert!(
            matches!(
                &min_prog.body[0],
                GenStmt::Assign {
                    expr: GenExpr::SysrootNum {
                        op: GenSysrootNumOp::UncheckedAdd,
                        guarded: false,
                        ..
                    },
                    ..
                }
            ),
            "expected collapsed single unchecked_add stmt, got {:?}",
            min_prog.body[0]
        );
        assert!(
            min_prog.params.len() <= 2,
            "expected unused u32 param dropped: {:?}",
            min_prog.params
        );
        assert!(trace.minimized_source.contains("unchecked_add"));
        assert!(!trace.minimized_source.contains("while"));
        assert!(!trace.minimized_source.contains("if "));
    }

    #[test]
    fn shrinker_narrows_numeric_param_and_loop_bound_precisely() {
        let prog = GenProgram {
            case_id: "bound_narrow".to_owned(),
            fn_name: "bound_narrow".to_owned(),
            master_seed: 2,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![GenParam {
                ty: GenType::Int(IntKind::I32),
                value: MirValue::Int { int_kind: IntKind::I32, bits: 98765 },
            }],
            locals: vec![GenLocal { ty: GenType::Int(IntKind::I32), init: GenExpr::Param(0) }],
            body: vec![GenStmt::WhileLoop {
                bound: 15,
                body: vec![GenStmt::Assign {
                    local: 0,
                    expr: GenExpr::BinArith {
                        op: GenArithOp::Add,
                        ty: IntKind::I32,
                        lhs: Box::new(GenExpr::Local(0)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::I32,
                            bits: 1,
                        })),
                    },
                }],
                break_cond: None,
                continue_cond: None,
            }],
            ret_ty: GenType::Int(IntKind::I32),
            ret_expr: GenExpr::Local(0),
            fuel: 300,
        };

        // Failure requires `bound >= 3` and `param0 >= 5`.
        let (min_prog, trace) = shrink_program(&prog, &ShrinkConfig::default(), |p| {
            let has_loop_ge3 =
                p.body.iter().any(|s| matches!(s, GenStmt::WhileLoop { bound, .. } if *bound >= 3));
            let arg_ge5 = p.params.first().is_some_and(|a| match a.value {
                MirValue::Int { int_kind, bits } => int_kind.to_signed_i128(bits) >= 5,
                _ => false,
            });
            has_loop_ge3 && arg_ge5
        });

        assert!(trace.converged_1_minimal);
        assert!(matches!(min_prog.body.first(), Some(GenStmt::WhileLoop { bound: 3, .. })));
        assert_eq!(min_prog.params[0].value, MirValue::Int { int_kind: IntKind::I32, bits: 5 });
    }

    #[test]
    fn shrinker_recurses_into_nested_if_while_guards_match_arms_and_u128_max() {
        let threshold = u128::MAX - 2;
        let prog = GenProgram {
            case_id: "nested_shrink".to_owned(),
            fn_name: "nested_shrink".to_owned(),
            master_seed: 3,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![GenParam {
                ty: GenType::Int(IntKind::U128),
                value: MirValue::Int { int_kind: IntKind::U128, bits: u128::MAX },
            }],
            locals: vec![GenLocal { ty: GenType::Int(IntKind::U128), init: GenExpr::Param(0) }],
            body: vec![GenStmt::WhileLoop {
                bound: 5,
                body: vec![
                    GenStmt::Assign {
                        local: 0,
                        expr: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U128, bits: 99 }),
                    },
                    GenStmt::IfElse {
                        cond: GenExpr::BoolLogic {
                            op: GenBoolBinOp::Or,
                            lhs: Box::new(GenExpr::Lit(MirValue::Bool { value: true })),
                            rhs: Box::new(GenExpr::Lit(MirValue::Bool { value: false })),
                        },
                        then_body: vec![
                            GenStmt::Assign {
                                local: 0,
                                expr: GenExpr::Lit(MirValue::Int {
                                    int_kind: IntKind::U128,
                                    bits: 77,
                                }),
                            },
                            GenStmt::Assign {
                                local: 0,
                                expr: GenExpr::MatchOrdering {
                                    scrutinee: Box::new(GenExpr::Lit(MirValue::Ordering {
                                        value: OrderingKind::Greater,
                                    })),
                                    ty: GenType::Int(IntKind::U128),
                                    less: Box::new(GenExpr::BinArith {
                                        op: GenArithOp::Add,
                                        ty: IntKind::U128,
                                        lhs: Box::new(GenExpr::Param(0)),
                                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                                            int_kind: IntKind::U128,
                                            bits: 42,
                                        })),
                                    }),
                                    equal: Box::new(GenExpr::Param(0)),
                                    greater: Box::new(GenExpr::BinArith {
                                        op: GenArithOp::BitXor,
                                        ty: IntKind::U128,
                                        lhs: Box::new(GenExpr::Param(0)),
                                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                                            int_kind: IntKind::U128,
                                            bits: 123,
                                        })),
                                    }),
                                },
                            },
                        ],
                        else_body: vec![GenStmt::Assign {
                            local: 0,
                            expr: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U128, bits: 8 }),
                        }],
                    },
                ],
                break_cond: Some(GenExpr::BoolLogic {
                    op: GenBoolBinOp::And,
                    lhs: Box::new(GenExpr::Lit(MirValue::Bool { value: false })),
                    rhs: Box::new(GenExpr::Lit(MirValue::Bool { value: true })),
                }),
                continue_cond: None,
            }],
            ret_ty: GenType::Int(IntKind::U128),
            ret_expr: GenExpr::Local(0),
            fuel: 400,
        };

        // Require the `WhileLoop` + nested `IfElse` + `MatchOrdering` +
        // `break_cond` to remain present AND `param0 >= u128::MAX - 2`, while
        // shrinking all nested decoy statements, `else_body`, `break_cond`,
        // `MatchOrdering` arm expressions, and narrowing `u128::MAX` ->
        // `u128::MAX - 2`.
        let (min_prog, trace) = shrink_program(
            &prog,
            &ShrinkConfig { max_steps: 512, max_duration_secs: 30 },
            |p| {
                let param_ok = p.params.first().is_some_and(|a| {
                    matches!(a.value, MirValue::Int { int_kind: IntKind::U128, bits } if bits >= threshold)
                });
                let struct_ok = matches!(
                    p.body.as_slice(),
                    [GenStmt::WhileLoop { body, break_cond: Some(_), .. }]
                        if body.iter().any(|s| matches!(
                            s,
                            GenStmt::IfElse { then_body, .. }
                                if then_body.iter().any(|ts| matches!(
                                    ts,
                                    GenStmt::Assign { expr: GenExpr::MatchOrdering { .. }, .. }
                                ))
                        ))
                );
                param_ok && struct_ok
            },
        );

        assert!(trace.converged_1_minimal, "expected recursive convergence: {trace:#?}");
        assert_eq!(
            min_prog.params[0].value,
            MirValue::Int { int_kind: IntKind::U128, bits: threshold }
        );
        let GenStmt::WhileLoop { bound, body, break_cond, .. } = &min_prog.body[0] else {
            panic!("expected WhileLoop");
        };
        assert_eq!(*bound, 0);
        assert_eq!(*break_cond, Some(GenExpr::Lit(MirValue::Bool { value: false })));
        assert_eq!(body.len(), 1, "nested decoy in loop must be deleted: {body:?}");
        let GenStmt::IfElse { cond, then_body, else_body } = &body[0] else {
            panic!("expected nested IfElse");
        };
        assert_eq!(*cond, GenExpr::Lit(MirValue::Bool { value: false }));
        assert!(else_body.is_empty(), "nested else_body must be dropped");
        assert_eq!(then_body.len(), 1, "nested decoy in then_body must be deleted");
        let GenStmt::Assign { expr: GenExpr::MatchOrdering { greater, .. }, .. } = &then_body[0]
        else {
            panic!("expected nested MatchOrdering");
        };
        assert_eq!(**greater, GenExpr::Lit(MirValue::Int { int_kind: IntKind::U128, bits: 0 }));
    }

    #[test]
    fn shrinker_returns_non_converged_when_initial_predicate_is_false() {
        let prog = sample_multi_stmt_program();
        let (out, trace) = shrink_program(&prog, &ShrinkConfig::default(), |_| false);
        assert!(!trace.converged_1_minimal);
        assert_eq!(out, prog);
        assert_eq!(trace.oracle_runs, 1);
    }

    #[test]
    fn nonmonotonic_int_narrowing_reaches_u64_high_bit_threshold_under_80_steps_and_tracks_inconclusive()
     {
        let threshold = 1u64 << 63;
        let prog = GenProgram {
            case_id: "u64_narrow".to_owned(),
            fn_name: "u64_narrow".to_owned(),
            master_seed: 7,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![GenParam {
                ty: GenType::Int(IntKind::U64),
                value: MirValue::Int {
                    int_kind: IntKind::U64,
                    bits: u128::from(0xFFFF_FFFF_FFFF_FFF0u64),
                },
            }],
            locals: vec![],
            body: vec![],
            ret_ty: GenType::Int(IntKind::I64),
            ret_expr: GenExpr::Cast {
                expr: Box::new(GenExpr::Param(0)),
                src_ty: GenType::Int(IntKind::U64),
                dst_ty: GenType::Int(IntKind::I64),
            },
            fuel: 100,
        };

        let (min_prog, trace) = shrink_program(&prog, &ShrinkConfig::default(), |p| {
            p.params.first().is_some_and(|a| {
                matches!(
                    a.value,
                    MirValue::Int { int_kind: IntKind::U64, bits } if bits >= u128::from(threshold)
                )
            })
        });
        assert!(trace.converged_1_minimal, "expected convergence: {trace:#?}");
        assert_eq!(
            min_prog.params[0].value,
            MirValue::Int { int_kind: IntKind::U64, bits: u128::from(threshold) }
        );
        assert!(
            trace.steps_evaluated < 80,
            "expected non-monotonic narrowing in < 80 steps, got {}",
            trace.steps_evaluated
        );

        // Verify `ShrinkOutcome::Inconclusive` is never cached and forces
        // `converged_1_minimal = false`.
        let mut zero_probe_calls = 0usize;
        let mut oracle = MemoizedOracle::new(
            |p: &GenProgram| match p.params[0].value {
                MirValue::Int { bits: 0, .. } => {
                    zero_probe_calls += 1;
                    ShrinkOutcome::Inconclusive
                }
                MirValue::Int { bits, .. } if bits >= u128::from(threshold) => {
                    ShrinkOutcome::Preserved
                }
                _ => ShrinkOutcome::NotPreserved,
            },
            &ShrinkConfig::default(),
        );
        let mut cand_zero = prog.clone();
        cand_zero.params[0].value = MirValue::Int { int_kind: IntKind::U64, bits: 0 };
        assert_eq!(oracle.eval(&cand_zero), Some(false));
        assert_eq!(oracle.eval(&cand_zero), Some(false));
        assert!(oracle.had_inconclusive);
        assert_eq!(oracle.cache_hits, 0);
        drop(oracle);
        assert_eq!(zero_probe_calls, 2, "Inconclusive probes must not be memo-cached");

        let (_min_inc, inc_trace) = shrink_program(&prog, &ShrinkConfig::default(), |p| {
            match p.params.first().map(|a| &a.value) {
                Some(MirValue::Int { bits: 0, .. }) => ShrinkOutcome::Inconclusive,
                Some(MirValue::Int { bits, .. }) if *bits >= u128::from(threshold) => {
                    ShrinkOutcome::Preserved
                }
                _ => ShrinkOutcome::NotPreserved,
            }
        });
        assert!(
            !inc_trace.converged_1_minimal,
            "any Inconclusive probe must force converged_1_minimal = false"
        );
    }

    #[test]
    fn nonmonotonic_int_narrowing_finds_smaller_islands_when_midpoints_fail() {
        let make_u32_prog = |initial: u128| GenProgram {
            case_id: "nonmono_u32".to_owned(),
            fn_name: "nonmono_u32".to_owned(),
            master_seed: 11,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![GenParam {
                ty: GenType::Int(IntKind::U32),
                value: MirValue::Int { int_kind: IntKind::U32, bits: initial },
            }],
            locals: vec![],
            body: vec![],
            ret_ty: GenType::Int(IntKind::U32),
            ret_expr: GenExpr::Param(0),
            fuel: 100,
        };

        // Failure holds at 100 and 8, but not at midpoint 50.
        let prog_8 = make_u32_prog(100);
        let (min_8, trace_8) = shrink_program(&prog_8, &ShrinkConfig::default(), |p| {
            matches!(
                p.params.first().map(|a| &a.value),
                Some(MirValue::Int { int_kind: IntKind::U32, bits: 8 | 100 })
            )
        });
        assert!(trace_8.converged_1_minimal);
        assert_eq!(min_8.params[0].value, MirValue::Int { int_kind: IntKind::U32, bits: 8 });

        // Failure holds at 100 and single-bit-clear 68 (`100 & !(1 << 5)`), so
        // all probes <= 64 (including 0..=12 and midpoint 50) return false.
        let (min_68, trace_68) = shrink_program(&prog_8, &ShrinkConfig::default(), |p| {
            matches!(
                p.params.first().map(|a| &a.value),
                Some(MirValue::Int { int_kind: IntKind::U32, bits: 68 | 100 })
            )
        });
        assert!(trace_68.converged_1_minimal);
        assert_eq!(min_68.params[0].value, MirValue::Int { int_kind: IntKind::U32, bits: 68 });

        // Negative signed island: holds at -100 and -8, not at -50.
        let neg_100_bits = 0u128.wrapping_sub(100) & IntKind::I32.mask();
        let neg_8_bits = 0u128.wrapping_sub(8) & IntKind::I32.mask();
        let prog_neg = GenProgram {
            case_id: "nonmono_i32".to_owned(),
            fn_name: "nonmono_i32".to_owned(),
            master_seed: 12,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![GenParam {
                ty: GenType::Int(IntKind::I32),
                value: MirValue::Int { int_kind: IntKind::I32, bits: neg_100_bits },
            }],
            locals: vec![],
            body: vec![],
            ret_ty: GenType::Int(IntKind::I32),
            ret_expr: GenExpr::Param(0),
            fuel: 100,
        };
        let (min_neg, trace_neg) = shrink_program(&prog_neg, &ShrinkConfig::default(), |p| {
            matches!(
                p.params.first().map(|a| &a.value),
                Some(MirValue::Int { int_kind: IntKind::I32, bits })
                    if *bits == neg_100_bits || *bits == neg_8_bits
            )
        });
        assert!(trace_neg.converged_1_minimal);
        assert_eq!(
            min_neg.params[0].value,
            MirValue::Int { int_kind: IntKind::I32, bits: neg_8_bits }
        );
    }

    #[test]
    fn shrink_program_with_deadline_clamps_slow_oracle_and_halts_on_budget() {
        let prog = GenProgram {
            case_id: "deadline_probe".to_owned(),
            fn_name: "deadline_probe".to_owned(),
            master_seed: 19,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![GenParam {
                ty: GenType::Int(IntKind::U32),
                value: MirValue::Int { int_kind: IntKind::U32, bits: 100 },
            }],
            locals: vec![],
            body: vec![],
            ret_ty: GenType::Int(IntKind::U32),
            ret_expr: GenExpr::Param(0),
            fuel: 100,
        };

        let started = Instant::now();
        let mut calls = 0usize;
        let (_min, trace) = shrink_program_with_deadline(
            &prog,
            &ShrinkConfig { max_steps: 256, max_duration_secs: 1 },
            |cand, deadline| {
                calls += 1;
                if cand.ret_expr == GenExpr::Param(0)
                    && matches!(
                        cand.params.first().map(|a| &a.value),
                        Some(MirValue::Int { bits: 100, .. })
                    )
                {
                    return ShrinkOutcome::Preserved;
                }
                // Simulate a stalled child leg whose supervisor clamps its
                // timeout to `deadline`.
                let rem = deadline.saturating_duration_since(Instant::now());
                std::thread::sleep(rem);
                ShrinkOutcome::Inconclusive
            },
        );
        assert!(
            started.elapsed() < Duration::from_secs(3),
            "shrinker failed to stop promptly at 1s deadline: {:?}",
            started.elapsed()
        );
        assert_eq!(calls, 2, "must halt immediately after the stalled candidate hits deadline");
        assert!(!trace.converged_1_minimal);
    }

    #[test]
    fn shrink_param_values_reaches_fixpoint_across_interacting_parameters() {
        let prog = GenProgram {
            case_id: "coupled_params".to_owned(),
            fn_name: "coupled_params".to_owned(),
            master_seed: 23,
            case_index: 0,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params: vec![
                GenParam {
                    ty: GenType::Int(IntKind::U32),
                    value: MirValue::Int { int_kind: IntKind::U32, bits: 8 },
                },
                GenParam {
                    ty: GenType::Int(IntKind::U32),
                    value: MirValue::Int { int_kind: IntKind::U32, bits: 8 },
                },
            ],
            locals: vec![],
            body: vec![],
            ret_ty: GenType::Int(IntKind::U32),
            ret_expr: GenExpr::BinArith {
                op: GenArithOp::Add,
                ty: IntKind::U32,
                lhs: Box::new(GenExpr::Param(0)),
                rhs: Box::new(GenExpr::Param(1)),
            },
            fuel: 100,
        };

        // Alternating staircase: reducing `p1` unlocks reducing `p0`, which in
        // turn unlocks reducing `p1` down to `(0, 0)`.
        let allowed =
            [(8u128, 8u128), (8, 4), (4, 4), (4, 2), (2, 2), (2, 1), (1, 1), (1, 0), (0, 0)];
        let (min, trace) = shrink_program(
            &prog,
            &ShrinkConfig { max_steps: 256, max_duration_secs: 10 },
            |cand| {
                let p0 = match cand.params.first().map(|p| &p.value) {
                    Some(MirValue::Int { bits, .. }) => *bits,
                    _ => return false,
                };
                let p1 = match cand.params.get(1).map(|p| &p.value) {
                    Some(MirValue::Int { bits, .. }) => *bits,
                    _ => return false,
                };
                matches!(
                    &cand.ret_expr,
                    GenExpr::BinArith { lhs, rhs, .. }
                        if matches!(lhs.as_ref(), GenExpr::Param(0))
                            && matches!(rhs.as_ref(), GenExpr::Param(1))
                ) && allowed.contains(&(p0, p1))
            },
        );
        assert!(trace.converged_1_minimal);
        assert_eq!(min.params[0].value, MirValue::Int { int_kind: IntKind::U32, bits: 0 });
        assert_eq!(min.params[1].value, MirValue::Int { int_kind: IntKind::U32, bits: 0 });
    }
}
