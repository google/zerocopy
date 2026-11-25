// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic pre-proof concrete counterexample probing over captured MIR
//! bodies using boundary enumeration and SplitMix64 sampling.

use alloc::{string::String, vec, vec::Vec};

use serde::{Deserialize, Serialize};

use crate::{
    eval::{
        EvalConfig, Outcome, StepTrace, TerminalOut, eval_body_with_config, validate_body_entry,
        validate_program_config,
    },
    ir::{IntTy, Program, Ty},
    value::{FaultDetail, FaultKind, OrderingVal, ScalarVal, Val, enum_admitted},
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

/// Concrete failing or bounded input tuple and its execution trace.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counterexample {
    pub args: Vec<Val>,
    pub trace: StepTrace,
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
    pub unsupported_count: usize,
    pub out_of_fuel_count: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_unwound: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_aborted: Option<Counterexample>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_undefined: Option<Counterexample>,
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
            unsupported_count: 0,
            out_of_fuel_count: 0,
            first_unwound: None,
            first_aborted: None,
            first_undefined: None,
            first_unsupported: None,
            first_out_of_fuel: None,
        }
    }
}

struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn next_u128(&mut self) -> u128 {
        let hi = u128::from(self.next_u64());
        let lo = u128::from(self.next_u64());
        (hi << 64) | lo
    }

    fn choose_index(&mut self, len: usize) -> usize {
        if len <= 1 { 0 } else { (self.next_u64() % (len as u64)) as usize }
    }
}

fn boundary_values_for_int(ity: IntTy) -> Vec<Val> {
    let bits = ity.width.bits();
    let mask = ity.width.mask();
    let mut raw_candidates: Vec<u128> = Vec::new();
    let mut push = |raw: u128| {
        let masked = raw & mask;
        if !raw_candidates.contains(&masked) {
            raw_candidates.push(masked);
        }
    };

    push(0);
    push(1);
    push(2);
    push(u128::from(bits.saturating_sub(1)));
    push(u128::from(bits));
    if ity.signed {
        let smin_bits = if bits == 128 { 1u128 << 127 } else { 1u128 << (bits - 1) };
        let smax_bits = smin_bits - 1;
        push(u128::MAX); // -1
        push(mask.wrapping_sub(1)); // -2
        push(smin_bits);
        push(smin_bits.wrapping_add(1));
        push(smax_bits);
        push(smax_bits.saturating_sub(1));
        push((-(bits as i128)) as u128);
    } else {
        push(mask);
        push(mask.saturating_sub(1));
        push(mask / 2);
        push((mask / 2).saturating_add(1));
    }
    for shift in [4u32, 7, 8, 15, 16, 31, 32, 63, 64] {
        if shift < bits {
            push(1u128 << shift);
            push((1u128 << shift) - 1);
        }
    }

    raw_candidates
        .into_iter()
        .map(|raw| Val::Scalar(ScalarVal::new(ity.width, ity.signed, raw)))
        .collect()
}

fn boundary_values_for_ty(ty: &Ty, enable_profile_v2: bool) -> Option<Vec<Val>> {
    if let Some(ity) = ty.as_overflow_pair() {
        let mut out = Vec::new();
        for int_val in boundary_values_for_int(ity) {
            if let Val::Scalar(sv) = int_val {
                out.push(Val::overflow_pair(sv, false));
                out.push(Val::overflow_pair(sv, true));
            }
        }
        return Some(out);
    }
    match ty {
        Ty::Never => Some(Vec::new()),
        Ty::Unit => Some(vec![Val::Unit]),
        Ty::Bool => Some(vec![Val::Bool(false), Val::Bool(true)]),
        Ty::Ordering => Some(vec![
            Val::Ordering(OrderingVal::Less),
            Val::Ordering(OrderingVal::Equal),
            Val::Ordering(OrderingVal::Greater),
        ]),
        Ty::Char => Some(vec![
            Val::Char('\0'),
            Val::Char('a'),
            Val::Char('A'),
            Val::Char('\u{7f}'),
            Val::Char('\u{80}'),
            Val::Char('\u{d7ff}'),
            Val::Char('\u{e000}'),
            Val::Char('\u{10ffff}'),
        ]),
        Ty::Int(ity) => Some(boundary_values_for_int(*ity)),
        Ty::Enum(ety) => {
            if !enum_admitted(ety) {
                return None;
            }
            let cap = ety.discriminants.len().min(16);
            Some((0..cap).map(|variant| Val::EnumVal { ty: ety.clone(), variant }).collect())
        }
        Ty::Tuple { fields } if enable_profile_v2 => {
            if fields.is_empty() {
                return Some(vec![Val::Tuple(Vec::new())]);
            }
            let mut per_field = Vec::with_capacity(fields.len());
            let mut uninhabited = false;
            for f in fields {
                // Validate every field shape before short-circuiting on an
                // uninhabited field (so `(Never, Unsupported)` returns `None`,
                // not `Some([])`).
                let vals = boundary_values_for_ty(f, true)?;
                if vals.is_empty() {
                    uninhabited = true;
                }
                per_field.push(vals);
            }
            if uninhabited {
                return Some(Vec::new());
            }
            let max_len = per_field.iter().map(Vec::len).max().unwrap_or(1);
            let mut tuples = Vec::with_capacity(max_len);
            for i in 0..max_len {
                let elem = per_field.iter().map(|vs| vs[i % vs.len()].clone()).collect();
                tuples.push(Val::Tuple(elem));
            }
            Some(tuples)
        }
        _ => None,
    }
}

fn random_val_for_ty(
    ty: &Ty,
    boundary_pool: &[Val],
    rng: &mut SplitMix64,
    enable_profile_v2: bool,
) -> Option<Val> {
    if !boundary_pool.is_empty() && (rng.next_u64() & 1) == 0 {
        return Some(boundary_pool[rng.choose_index(boundary_pool.len())].clone());
    }
    if let Some(ity) = ty.as_overflow_pair() {
        let bits = rng.next_u128() & ity.width.mask();
        let sv = ScalarVal::new(ity.width, ity.signed, bits);
        return Some(Val::overflow_pair(sv, (rng.next_u64() & 1) == 1));
    }
    match ty {
        Ty::Never => None,
        Ty::Unit => Some(Val::Unit),
        Ty::Bool => Some(Val::Bool((rng.next_u64() & 1) == 1)),
        Ty::Ordering => Some(match rng.next_u64() % 3 {
            0 => Val::Ordering(OrderingVal::Less),
            1 => Val::Ordering(OrderingVal::Equal),
            _ => Val::Ordering(OrderingVal::Greater),
        }),
        Ty::Char => {
            let candidate = rng.next_u64() % 0x11_0000;
            let val = char::from_u32(candidate as u32).unwrap_or('a');
            Some(Val::Char(val))
        }
        Ty::Int(ity) => Some(Val::Scalar(ScalarVal::new(ity.width, ity.signed, rng.next_u128()))),
        Ty::Enum(ety) if enum_admitted(ety) => {
            let idx = rng.choose_index(ety.discriminants.len());
            Some(Val::EnumVal { ty: ety.clone(), variant: idx })
        }
        Ty::Tuple { fields } if enable_profile_v2 => {
            let mut out = Vec::with_capacity(fields.len());
            for f in fields {
                let pool = boundary_values_for_ty(f, true)?;
                out.push(random_val_for_ty(f, &pool, rng, true)?);
            }
            Some(Val::Tuple(out))
        }
        _ => None,
    }
}

fn push_cartesian_prefix(
    pools: &[Vec<Val>],
    budget: usize,
    idx: usize,
    cur: &mut Vec<Val>,
    out: &mut Vec<Vec<Val>>,
) {
    if out.len() >= budget {
        return;
    }
    if idx == pools.len() {
        out.push(cur.clone());
        return;
    }
    for v in &pools[idx] {
        if out.len() >= budget {
            break;
        }
        cur.push(v.clone());
        push_cartesian_prefix(pools, budget, idx + 1, cur, out);
        cur.pop();
    }
}

/// Probe body `body_id` across boundary and deterministic pseudorandom inputs.
///
/// Probe `body_id` in `program` across boundary and random inputs without
/// skipping `unsafe fn` bodies.
///
/// Note: `probe_body` explores unconstrained boundary/random inputs without
/// knowledge of caller safety preconditions; callers probing `body.is_unsafe`
/// functions must interpret reported `undefined_count` values against those
/// preconditions (the CLI skips statically valid `is_unsafe` bodies unless
/// `--include-unsafe` is passed).
pub fn probe_body(
    program: &Program,
    body_id: usize,
    probe: &ProbeConfig,
    config: &EvalConfig,
) -> ProbeReport {
    probe_body_with_policy(program, body_id, probe, config, false)
}

/// Probe `body_id` in `program` after validating program and static body-entry
/// invariants (`validate_program_config` and `validate_body_entry`).
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
        unsupported_count: 0,
        out_of_fuel_count: 0,
        first_unwound: None,
        first_aborted: None,
        first_undefined: None,
        first_unsupported: None,
        first_out_of_fuel: None,
    };
    let record_unsupported = |report: &mut ProbeReport, fault: FaultDetail| {
        report.unsupported_count += 1;
        if report.first_unsupported.is_none() {
            report.first_unsupported = Some(Counterexample {
                args: Vec::new(),
                trace: StepTrace {
                    body_id,
                    identity: report.identity.clone(),
                    steps_executed: 0,
                    fuel_limit: probe.fuel,
                    outcome: Outcome::Fault(fault),
                    events: Vec::new(),
                    final_state: None,
                },
            });
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
    if let Err(fault) = validate_body_entry(body, config) {
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
        let Some(pool) = boundary_values_for_ty(ty, config.enable_profile_v2()) else {
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

    let mut cases: Vec<Vec<Val>> = Vec::new();
    let cartesian_budget = if param_tys.is_empty() { 1 } else { probe.max_cases / 2 + 1 };
    let mut cur = Vec::with_capacity(param_tys.len());
    push_cartesian_prefix(&pools, cartesian_budget.min(probe.max_cases), 0, &mut cur, &mut cases);

    let mut rng = SplitMix64::new(probe.seed);
    let mut attempts = 0usize;
    let max_attempts = probe.max_cases.saturating_mul(4).max(16);
    while !param_tys.is_empty() && cases.len() < probe.max_cases && attempts < max_attempts {
        attempts += 1;
        let mut tuple = Vec::with_capacity(param_tys.len());
        let mut ok = true;
        for (ty, pool) in param_tys.iter().zip(pools.iter()) {
            match random_val_for_ty(ty, pool, &mut rng, config.enable_profile_v2()) {
                Some(v) => tuple.push(v),
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            break;
        }
        if !cases.contains(&tuple) {
            cases.push(tuple);
        }
    }

    for args in cases {
        let trace = eval_body_with_config(program, body_id, &args, probe.fuel, config);
        report.cases_run += 1;
        match &trace.outcome {
            Outcome::Returned(TerminalOut::Returned { .. }) => report.returned_count += 1,
            Outcome::Returned(TerminalOut::Unwound { .. }) => {
                report.unwound_count += 1;
                if report.first_unwound.is_none() {
                    report.first_unwound = Some(Counterexample { args, trace });
                }
            }
            Outcome::Aborted { .. } => {
                report.aborted_count += 1;
                if report.first_aborted.is_none() {
                    report.first_aborted = Some(Counterexample { args, trace });
                }
            }
            Outcome::Fault(fault) => match fault.kind {
                FaultKind::Undefined => {
                    report.undefined_count += 1;
                    if report.first_undefined.is_none() {
                        report.first_undefined = Some(Counterexample { args, trace });
                    }
                }
                FaultKind::Unsupported => {
                    report.unsupported_count += 1;
                    if report.first_unsupported.is_none() {
                        report.first_unsupported = Some(Counterexample { args, trace });
                    }
                }
            },
            Outcome::OutOfFuel => {
                report.out_of_fuel_count += 1;
                if report.first_out_of_fuel.is_none() {
                    report.first_out_of_fuel = Some(Counterexample { args, trace });
                }
            }
        }
    }
    report
}
