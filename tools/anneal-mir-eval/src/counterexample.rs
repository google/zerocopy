// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic pre-proof concrete counterexample probing over captured MIR
//! bodies using boundary enumeration and SplitMix64 sampling.
//!
//! Supports both Profile v1 value arguments and Profile v2 pointer/reference/
//! slice queries with caller-supplied memory, and tags every Undefined Behavior
//! witness with [`WitnessClass`] (`replayable_miri_ub` vs
//! `model_only_unreplayed`).

mod boundary;
mod random;

use alloc::{boxed::Box, format, string::String, vec::Vec};
use core::fmt;

use serde::{Deserialize, Serialize};

use self::{
    boundary::boundary_candidates_for_ty,
    random::{SplitMix64, random_candidate_for_ty},
};
use crate::{
    eval::{
        EvalConfig, Outcome, StepTrace, TerminalOut, eval_body_with_caller_mem, sysroot_num_body,
        validate_body_in_program, validate_program_config,
    },
    ir::Program,
    memory::{Allocation, CallerMemory},
    value::{FaultDetail, FaultKind, PtrVal, Val, WitnessClass},
};

/// Configuration for deterministic bounded pre-proof probing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProbeConfig {
    pub max_cases: usize,
    pub fuel: usize,
    pub seed: u64,
}

impl Default for ProbeConfig {
    fn default() -> Self {
        Self { max_cases: 256, fuel: 100_000, seed: 0x9e37_79b9_7f4a_7c15 }
    }
}

fn is_false(b: &bool) -> bool {
    !*b
}

/// Structured MIR location where a fault, abort, unwind, or fuel limit hit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceLocation {
    pub step: usize,
    pub def_id: usize,
    #[serde(default, skip_serializing_if = "is_false")]
    pub is_sysroot: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub body_identity: Option<String>,
    pub block_idx: usize,
    pub stmt_idx: usize,
    pub is_terminator: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
}

impl TraceLocation {
    /// Format a compact site tag, suppressing `body[id]` for `entry_body_id`.
    pub fn format_site(&self, entry_body_id: Option<usize>) -> String {
        let id = self.body_identity.as_deref().filter(|s| !s.is_empty());
        let pfx = if self.is_sysroot {
            format!("{} ", id.unwrap_or("sysroot"))
        } else if entry_body_id.is_some_and(|e| e != self.def_id) {
            let b = self.def_id;
            id.map_or_else(|| format!("body[{b}] "), |s| format!("body[{b}] ({s}) "))
        } else {
            String::new()
        };
        match (self.kind.as_deref(), self.is_terminator) {
            (Some("entry"), _) => format!("{pfx}entry"),
            (_, true) => format!("{pfx}bb{}:term", self.block_idx),
            (_, false) => format!("{pfx}bb{}:stmt{}", self.block_idx, self.stmt_idx),
        }
    }
}

impl fmt::Display for TraceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format_site(None))
    }
}

/// Extract the non-return site (`Fault`/`Aborted`/`Unwound`/`OutOfFuel`) of `trace`
/// using `program` to resolve `body_identity` and statement-vs-terminator status.
pub fn trace_location(program: &Program, trace: &StepTrace) -> Option<TraceLocation> {
    let fb = match &trace.outcome {
        Outcome::Returned(TerminalOut::Returned { .. }) => return None,
        Outcome::OutOfFuel => "out_of_fuel",
        Outcome::Fault(_) => "fault",
        Outcome::Aborted { .. } => "abort",
        Outcome::Returned(TerminalOut::Unwound { .. }) => "terminal",
    };
    let fr = trace.final_state.as_ref().and_then(|s| s.frames.last());
    let (n, ev) = (trace.steps_executed, trace.events.last());
    let (step, def_id, block_idx, stmt_idx, kind) = match (fb, fr, ev) {
        ("out_of_fuel", Some(f), _) => (n, f.def_id, f.block_idx, f.stmt_idx, fb),
        ("out_of_fuel", None, Some(e)) => (e.step, e.def_id, e.block_idx, e.stmt_idx, fb),
        (_, _, Some(e)) => (e.step, e.def_id, e.block_idx, e.stmt_idx, e.kind.as_str()),
        (_, Some(f), None) => (n.saturating_sub(1), f.def_id, f.block_idx, f.stmt_idx, fb),
        _ => (0, trace.body_id, 0, 0, "entry"),
    };
    let site = (def_id, block_idx, stmt_idx);
    let sys_op =
        fr.and_then(|f| f.sysroot_op.filter(|_| (f.def_id, f.block_idx, f.stmt_idx) == site));
    let sys_body = sys_op.map(sysroot_num_body);
    let body_ref = sys_body.as_ref().or_else(|| program.bodies.get(def_id));
    let is_terminator = match body_ref {
        _ if kind == "entry" => false,
        Some(b) => stmt_idx >= b.blocks.get(block_idx)?.statements.len(),
        None => return None,
    };
    let tid = (def_id == trace.body_id && !trace.identity.is_empty()).then_some(&trace.identity);
    Some(TraceLocation {
        step,
        def_id,
        is_sysroot: sys_op.is_some(),
        body_identity: body_ref.map(|b| &b.identity).or(tid).cloned(),
        block_idx,
        stmt_idx,
        is_terminator,
        kind: Some(kind.into()),
    })
}

/// Concrete failing or bounded input query and its execution trace.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counterexample {
    pub args: Vec<Val>,
    #[serde(default, skip_serializing_if = "CallerMemory::is_empty")]
    pub caller_mem: CallerMemory,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witness_class: Option<WitnessClass>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witness_note: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fault_location: Option<TraceLocation>,
    pub trace: StepTrace,
}

impl Counterexample {
    /// Build from `(args, caller_mem, trace)` (`fault_location` is `None`;
    /// use [`Self::from_trace_in_program`] when a [`Program`] is available).
    pub fn from_trace(args: Vec<Val>, caller_mem: CallerMemory, trace: StepTrace) -> Self {
        let (witness_class, witness_note) = match &trace.outcome {
            Outcome::Fault(f) if f.kind == FaultKind::Undefined => {
                (f.witness_class(), f.model_only_note().map(String::from))
            }
            _ => (None, None),
        };
        Self { args, caller_mem, witness_class, witness_note, fault_location: None, trace }
    }

    /// Program-aware variant resolving callee names and terminator flags.
    pub fn from_trace_in_program(
        p: &Program,
        args: Vec<Val>,
        caller_mem: CallerMemory,
        trace: StepTrace,
    ) -> Self {
        let mut ce = Self::from_trace(args, caller_mem, trace);
        ce.fault_location = trace_location(p, &ce.trace);
        ce
    }
}

/// Summary report across all tested concrete inputs for one body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProbeReport {
    pub body_id: usize,
    pub identity: String,
    pub is_unsafe: bool,
    #[serde(default)]
    pub skipped_unsafe: bool,
    pub uninhabited_params: bool,
    pub unsupported_param_shape: bool,
    pub cases_run: usize,
    pub returned_count: usize,
    pub unwound_count: usize,
    pub aborted_count: usize,
    pub undefined_count: usize,
    #[serde(default)]
    pub replayable_ub_count: usize,
    #[serde(default)]
    pub model_only_unreplayed_ub_count: usize,
    pub unsupported_count: usize,
    pub out_of_fuel_count: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_unwound: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_aborted: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_undefined: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_replayable_undefined: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_model_only_undefined: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_unsupported: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_out_of_fuel: Option<Counterexample>,
}

impl ProbeReport {
    /// Build a zero-case report representing an `unsafe fn` body skipped by
    /// the CLI unless `--include-unsafe` is passed.
    pub fn skipped_unsafe_body(body_id: usize, identity: String) -> Self {
        Self {
            body_id,
            identity,
            is_unsafe: true,
            skipped_unsafe: true,
            uninhabited_params: false,
            unsupported_param_shape: false,
            cases_run: 0,
            returned_count: 0,
            unwound_count: 0,
            aborted_count: 0,
            undefined_count: 0,
            replayable_ub_count: 0,
            model_only_unreplayed_ub_count: 0,
            unsupported_count: 0,
            out_of_fuel_count: 0,
            first_unwound: None,
            first_aborted: None,
            first_undefined: None,
            first_replayable_undefined: None,
            first_model_only_undefined: None,
            first_unsupported: None,
            first_out_of_fuel: None,
        }
    }
}

/// Template for one candidate argument together with any caller allocations it
/// needs. Allocation ids inside `allocs` are local placeholders (`1..=k`) that
/// [`materialize_case`] remaps to pairwise-disjoint ids across all parameters
/// of a single query.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ArgCandidate {
    val: Val,
    allocs: Vec<Allocation>,
}

impl ArgCandidate {
    fn pure(val: Val) -> Self {
        Self { val, allocs: Vec::new() }
    }
}

fn remap_val_allocs(val: &Val, delta: u64) -> Val {
    match val {
        Val::Ptr(p) => Val::Ptr(PtrVal { alloc_id: p.alloc_id.map(|id| id + delta), ..*p }),
        Val::SlicePtr { ptr, len } => Val::SlicePtr {
            ptr: PtrVal { alloc_id: ptr.alloc_id.map(|id| id + delta), ..*ptr },
            len: *len,
        },
        Val::Tuple(vs) => Val::Tuple(vs.iter().map(|v| remap_val_allocs(v, delta)).collect()),
        Val::OptionVal(Some(inner)) => {
            Val::OptionVal(Some(Box::new(remap_val_allocs(inner, delta))))
        }
        other => other.clone(),
    }
}

fn materialize_case(candidates: &[ArgCandidate]) -> (Vec<Val>, CallerMemory) {
    let mut args = Vec::with_capacity(candidates.len());
    let mut allocations = Vec::new();
    let mut next_alloc_id: u64 = 2;
    for cand in candidates {
        if cand.allocs.is_empty() {
            args.push(cand.val.clone());
        } else {
            let base_offset = next_alloc_id - 1;
            let mut max_local = 0u64;
            for alloc in &cand.allocs {
                max_local = max_local.max(alloc.alloc_id);
                let mut cloned = alloc.clone();
                cloned.alloc_id += base_offset;
                allocations.push(cloned);
            }
            args.push(remap_val_allocs(&cand.val, base_offset));
            next_alloc_id += max_local;
        }
    }
    (args, CallerMemory { allocations })
}

fn shift_val_allocs_down(val: &Val, delta: u64) -> Val {
    match val {
        Val::Ptr(p) => Val::Ptr(PtrVal { alloc_id: p.alloc_id.map(|id| id - delta), ..*p }),
        Val::SlicePtr { ptr, len } => Val::SlicePtr {
            ptr: PtrVal { alloc_id: ptr.alloc_id.map(|id| id - delta), ..*ptr },
            len: *len,
        },
        Val::Tuple(vs) => Val::Tuple(vs.iter().map(|v| shift_val_allocs_down(v, delta)).collect()),
        Val::OptionVal(Some(inner)) => {
            Val::OptionVal(Some(Box::new(shift_val_allocs_down(inner, delta))))
        }
        other => other.clone(),
    }
}

fn push_cartesian_prefix(
    pools: &[Vec<ArgCandidate>],
    budget: usize,
    idx: usize,
    cur: &mut Vec<ArgCandidate>,
    out: &mut Vec<(Vec<Val>, CallerMemory)>,
) {
    if out.len() >= budget {
        return;
    }
    if idx == pools.len() {
        out.push(materialize_case(cur));
        return;
    }
    for cand in &pools[idx] {
        if out.len() >= budget {
            break;
        }
        cur.push(cand.clone());
        push_cartesian_prefix(pools, budget, idx + 1, cur, out);
        cur.pop();
    }
}

/// Probe body `body_id` in `program` across boundary and deterministic
/// pseudorandom inputs without skipping `unsafe fn` bodies.
pub fn probe_body(
    program: &Program,
    body_id: usize,
    probe: &ProbeConfig,
    config: &EvalConfig,
) -> ProbeReport {
    probe_body_with_policy(program, body_id, probe, config, false)
}

/// Probe `body_id` in `program` after validating program and static body-entry
/// invariants (`validate_program_config` and `validate_body_in_program`).
///
/// When `skip_unsafe` is `true`, statically admitted `body.is_unsafe` entries
/// return [`ProbeReport::skipped_unsafe_body`] before input generation; invalid
/// `unsafe` bodies still report `unsupported_count = 1`.
pub fn probe_body_with_policy(
    program: &Program,
    body_id: usize,
    probe: &ProbeConfig,
    config: &EvalConfig,
    skip_unsafe: bool,
) -> ProbeReport {
    let body_opt = program.bodies.get(body_id);
    let identity = body_opt.map(|b| b.identity.clone()).unwrap_or_default();
    let is_unsafe = body_opt.is_some_and(|b| b.is_unsafe);
    let mut report = ProbeReport {
        body_id,
        identity,
        is_unsafe,
        skipped_unsafe: false,
        uninhabited_params: false,
        unsupported_param_shape: false,
        cases_run: 0,
        returned_count: 0,
        unwound_count: 0,
        aborted_count: 0,
        undefined_count: 0,
        replayable_ub_count: 0,
        model_only_unreplayed_ub_count: 0,
        unsupported_count: 0,
        out_of_fuel_count: 0,
        first_unwound: None,
        first_aborted: None,
        first_undefined: None,
        first_replayable_undefined: None,
        first_model_only_undefined: None,
        first_unsupported: None,
        first_out_of_fuel: None,
    };
    let record_unsupported = |report: &mut ProbeReport, fault: FaultDetail| {
        report.unsupported_count += 1;
        if report.first_unsupported.is_none() {
            report.first_unsupported = Some(Counterexample::from_trace_in_program(
                program,
                Vec::new(),
                CallerMemory::default(),
                StepTrace {
                    body_id,
                    identity: report.identity.clone(),
                    steps_executed: 0,
                    fuel_limit: probe.fuel,
                    outcome: Outcome::Fault(fault),
                    events: Vec::new(),
                    final_state: None,
                },
            ));
        }
    };
    if let Err(fault) = validate_program_config(program, config) {
        record_unsupported(&mut report, fault);
        return report;
    }
    let Some(body) = body_opt else {
        report.unsupported_param_shape = true;
        record_unsupported(&mut report, FaultDetail::unsupported("entry body id out of bounds"));
        return report;
    };
    if let Err(fault) = validate_body_in_program(program, body, config) {
        record_unsupported(&mut report, fault);
        return report;
    }
    if skip_unsafe && body.is_unsafe {
        return ProbeReport::skipped_unsafe_body(body_id, body.identity.clone());
    }
    let Some(param_tys) = body.param_tys() else {
        report.unsupported_param_shape = true;
        record_unsupported(
            &mut report,
            FaultDetail::unsupported("argument count exceeds local count"),
        );
        return report;
    };

    // Validate every parameter shape before short-circuiting on uninhabited
    // parameters (`!` or a tuple containing `!`) so an unsupported parameter
    // after `!` still reports `unsupported_param_shape`.
    let mut pools = Vec::with_capacity(param_tys.len());
    let mut has_uninhabited = false;
    for ty in param_tys {
        let Some(pool) = boundary_candidates_for_ty(ty, config.enable_profile_v2(), config.endian)
        else {
            report.unsupported_param_shape = true;
            return report;
        };
        if pool.is_empty() {
            has_uninhabited = true;
        }
        pools.push(pool);
    }
    if has_uninhabited {
        report.uninhabited_params = true;
        return report;
    }

    let mut cases: Vec<(Vec<Val>, CallerMemory)> = Vec::new();
    let cartesian_budget = if param_tys.is_empty() { 1 } else { probe.max_cases / 2 + 1 };
    let mut cur = Vec::with_capacity(param_tys.len());
    push_cartesian_prefix(&pools, cartesian_budget.min(probe.max_cases), 0, &mut cur, &mut cases);

    let mut rng = SplitMix64::new(probe.seed);
    let mut attempts = 0usize;
    let max_attempts = probe.max_cases.saturating_mul(4).max(16);
    while !param_tys.is_empty() && cases.len() < probe.max_cases && attempts < max_attempts {
        attempts += 1;
        let mut cands = Vec::with_capacity(param_tys.len());
        let mut ok = true;
        for (ty, pool) in param_tys.iter().zip(pools.iter()) {
            match random_candidate_for_ty(
                ty,
                pool,
                &mut rng,
                config.enable_profile_v2(),
                config.endian,
            ) {
                Some(c) => cands.push(c),
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            break;
        }
        let materialized = materialize_case(&cands);
        if !cases.contains(&materialized) {
            cases.push(materialized);
        }
    }

    let mk_ce = |args, caller_mem, trace| {
        Counterexample::from_trace_in_program(program, args, caller_mem, trace)
    };
    for (args, caller_mem) in cases {
        let trace = eval_body_with_caller_mem(
            program,
            body_id,
            &args,
            caller_mem.clone(),
            probe.fuel,
            config,
        );
        report.cases_run += 1;
        match &trace.outcome {
            Outcome::Returned(TerminalOut::Returned { .. }) => report.returned_count += 1,
            Outcome::Returned(TerminalOut::Unwound { .. }) => {
                report.unwound_count += 1;
                if report.first_unwound.is_none() {
                    report.first_unwound = Some(mk_ce(args, caller_mem, trace));
                }
            }
            Outcome::Aborted { .. } => {
                report.aborted_count += 1;
                if report.first_aborted.is_none() {
                    report.first_aborted = Some(mk_ce(args, caller_mem, trace));
                }
            }
            Outcome::Fault(fault) => match fault.kind {
                FaultKind::Undefined => {
                    report.undefined_count += 1;
                    let class = fault.witness_class().unwrap_or(WitnessClass::ModelOnlyUnreplayed);
                    let ce = mk_ce(args, caller_mem, trace);
                    match class {
                        WitnessClass::ReplayableMiriUb => {
                            report.replayable_ub_count += 1;
                            if report.first_replayable_undefined.is_none() {
                                report.first_replayable_undefined = Some(ce.clone());
                            }
                        }
                        WitnessClass::ModelOnlyUnreplayed => {
                            report.model_only_unreplayed_ub_count += 1;
                            if report.first_model_only_undefined.is_none() {
                                report.first_model_only_undefined = Some(ce.clone());
                            }
                        }
                    }
                    if report.first_undefined.is_none() {
                        report.first_undefined = Some(ce);
                    }
                }
                FaultKind::Unsupported => {
                    report.unsupported_count += 1;
                    if report.first_unsupported.is_none() {
                        report.first_unsupported = Some(mk_ce(args, caller_mem, trace));
                    }
                }
            },
            Outcome::OutOfFuel => {
                report.out_of_fuel_count += 1;
                if report.first_out_of_fuel.is_none() {
                    report.first_out_of_fuel = Some(mk_ce(args, caller_mem, trace));
                }
            }
        }
    }
    report
}
