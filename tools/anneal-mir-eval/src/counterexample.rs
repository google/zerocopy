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

use alloc::{boxed::Box, format, string::String, vec, vec::Vec};
use core::fmt;

use serde::{Deserialize, Serialize};

use crate::{
    eval::{
        EvalConfig, Outcome, StepTrace, TerminalOut, eval_body_with_caller_mem, sysroot_num_body,
        validate_body_in_program, validate_program_config,
    },
    ir::{IntTy, IntWidth, Mutability, Program, Ty},
    memory::{Allocation, CallerMemory, TargetEndian, encode_val, int_layout, layout_of_ty},
    value::{
        AllocByte, FaultDetail, FaultKind, OrderingVal, PtrVal, ScalarVal, Val, WitnessClass,
        enum_admitted, is_supported_v2_local_ty,
    },
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

fn sample_slice_bytes(elem_size: usize, elem_count: usize) -> Vec<AllocByte> {
    let total = elem_size * elem_count;
    (0..total)
        .map(|i| AllocByte::Init { byte: ((i * 37 + 0x11) & 0xff) as u8, prov: None })
        .collect()
}

fn boundary_candidates_for_ref(
    mutability: Mutability,
    pointee: &Ty,
    endian: TargetEndian,
) -> Option<Vec<ArgCandidate>> {
    match pointee {
        Ty::Slice { elem } => {
            let Ty::Int(ity) = elem.as_ref() else {
                return None;
            };
            let lay = int_layout(ity.width);
            let elem_size = lay.size as usize;
            let align_addr = 1u64 << lay.align_log2;
            let mut out = Vec::new();
            // 1. Empty dangling slice (`NonNull::dangling()`, `len = 0`).
            out.push(ArgCandidate::pure(Val::SlicePtr {
                ptr: PtrVal { alloc_id: None, offset_bytes: align_addr, width: IntWidth::Isize },
                len: 0,
            }));
            // 2. Empty live allocation slice (`len = 0`).
            out.push(ArgCandidate {
                val: Val::SlicePtr {
                    ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                    len: 0,
                },
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability,
                    bytes: Vec::new(),
                    live: true,
                }],
            });
            // 3. Single-element and 4-element initialized slices.
            for count in [1usize, 4usize] {
                out.push(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                        len: count as u64,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability,
                        bytes: sample_slice_bytes(elem_size, count),
                        live: true,
                    }],
                });
            }
            // 4. Non-zero offset subslice (offset = elem_size, len = 2 of 4).
            out.push(ArgCandidate {
                val: Val::SlicePtr {
                    ptr: PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: lay.size,
                        width: IntWidth::Isize,
                    },
                    len: 2,
                },
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability,
                    bytes: sample_slice_bytes(elem_size, 4),
                    live: true,
                }],
            });
            Some(out)
        }
        Ty::Str => {
            // Shared `&str`: an empty dangling string, ASCII, multi-byte
            // UTF-8, a substring at a non-zero offset, and initialized
            // non-UTF-8 bytes. `ValidEntryArgsV2` admits the last one because
            // `refValidInMem` requires only initialized bytes.
            let mut out = vec![ArgCandidate::pure(Val::SlicePtr {
                ptr: PtrVal { alloc_id: None, offset_bytes: 1, width: IntWidth::Isize },
                len: 0,
            })];
            let multi_byte = "\u{e9}\u{1f600}".as_bytes();
            let offset = "xy\u{20ac}".as_bytes();
            for (bytes, offset_bytes, len) in
                [(&b"a"[..], 0, 1), (multi_byte, 0, 6), (offset, 2, 3), (&[0xFF, 0xC0][..], 0, 2)]
            {
                out.push(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes, width: IntWidth::Isize },
                        len,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: 0,
                        mutability,
                        bytes: bytes
                            .iter()
                            .map(|&byte| AllocByte::Init { byte, prov: None })
                            .collect(),
                        live: true,
                    }],
                });
            }
            Some(out)
        }
        other => {
            let lay = layout_of_ty(other, true)?;
            let pointee_vals = boundary_candidates_for_ty(other, true, endian)?;
            if pointee_vals.is_empty() {
                // `&!` / `&mut !` is uninhabited because `refValidInMem`
                // requires a valid pointee value.
                return Some(Vec::new());
            }
            let mut out = Vec::new();
            if lay.size == 0 {
                // Valid dangling ZST reference (`NonNull::dangling()`).
                out.push(ArgCandidate::pure(Val::Ptr(PtrVal {
                    alloc_id: None,
                    offset_bytes: 1u64 << lay.align_log2,
                    width: IntWidth::Isize,
                })));
            }
            for cand in pointee_vals.into_iter().take(4) {
                let bytes = encode_val(endian, other, &cand.val, true).ok()?;
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability,
                        bytes,
                        live: true,
                    }],
                });
            }
            Some(out)
        }
    }
}

fn boundary_candidates_for_raw_ptr(
    mutability: Mutability,
    pointee: &Ty,
    endian: TargetEndian,
) -> Option<Vec<ArgCandidate>> {
    match pointee {
        Ty::Slice { elem } => {
            let Ty::Int(ity) = elem.as_ref() else {
                return None;
            };
            let lay = int_layout(ity.width);
            let elem_size = lay.size as usize;
            let mut out = Vec::new();
            // Valid live 4-element raw slice pointer.
            out.push(ArgCandidate {
                val: Val::SlicePtr {
                    ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                    len: 4,
                },
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability: Mutability::Mut,
                    bytes: sample_slice_bytes(elem_size, 4),
                    live: true,
                }],
            });
            // Null raw slice pointers (empty and non-empty).
            for len in [0u64, 4u64] {
                out.push(ArgCandidate::pure(Val::SlicePtr {
                    ptr: PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize },
                    len,
                }));
            }
            // Dangling provenance-free raw slice pointer.
            out.push(ArgCandidate::pure(Val::SlicePtr {
                ptr: PtrVal {
                    alloc_id: None,
                    offset_bytes: 1u64 << lay.align_log2,
                    width: IntWidth::Isize,
                },
                len: 0,
            }));
            Some(out)
        }
        other => {
            let lay = layout_of_ty(other, true)?;
            let mut out = Vec::new();
            // 1. Valid live mutable aligned allocation (for inhabited pointee).
            if let Some(pointee_cands) = boundary_candidates_for_ty(other, true, endian)
                && let Some(first) = pointee_cands.first()
                && let Ok(bytes) = encode_val(endian, other, &first.val, true)
            {
                let mut padded = bytes.clone();
                if lay.size > 0 {
                    padded.extend_from_slice(&bytes);
                }
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Mut,
                        bytes: padded,
                        live: true,
                    }],
                });
            }
            // 2. Null raw pointer.
            out.push(ArgCandidate::pure(Val::Ptr(PtrVal {
                alloc_id: None,
                offset_bytes: 0,
                width: IntWidth::Isize,
            })));
            // 3. Non-null dangling aligned provenance-free pointer.
            out.push(ArgCandidate::pure(Val::Ptr(PtrVal {
                alloc_id: None,
                offset_bytes: 1u64 << lay.align_log2,
                width: IntWidth::Isize,
            })));
            // 4. Dead (deallocated) allocation.
            out.push(ArgCandidate {
                val: Val::Ptr(PtrVal {
                    alloc_id: Some(1),
                    offset_bytes: 0,
                    width: IntWidth::Isize,
                }),
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability: Mutability::Mut,
                    bytes: vec![AllocByte::Init { byte: 0, prov: None }; lay.size as usize],
                    live: false,
                }],
            });
            // 5. Out-of-bounds offset inside live allocation.
            out.push(ArgCandidate {
                val: Val::Ptr(PtrVal {
                    alloc_id: Some(1),
                    offset_bytes: lay.size.max(1),
                    width: IntWidth::Isize,
                }),
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability: Mutability::Mut,
                    bytes: vec![AllocByte::Init { byte: 0, prov: None }; lay.size as usize],
                    live: true,
                }],
            });
            // 6. Misaligned pointer when ABI alignment > 1.
            if lay.align_log2 > 0 {
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 1,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Mut,
                        bytes: vec![
                            AllocByte::Init { byte: 0, prov: None };
                            (lay.size as usize) + 4
                        ],
                        live: true,
                    }],
                });
            }
            // 7. Immutable allocation for `*mut T` (catches WriteToReadOnly).
            if mutability == Mutability::Mut && lay.size > 0 {
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Shared,
                        bytes: vec![AllocByte::Init { byte: 0, prov: None }; lay.size as usize],
                        live: true,
                    }],
                });
            }
            // 8. Uninitialized allocation for non-ZST pointee.
            if lay.size > 0 {
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Mut,
                        bytes: vec![AllocByte::Uninit; lay.size as usize],
                        live: true,
                    }],
                });
            }
            Some(out)
        }
    }
}

fn boundary_candidates_for_ty(
    ty: &Ty,
    enable_profile_v2: bool,
    endian: TargetEndian,
) -> Option<Vec<ArgCandidate>> {
    if let Some(ity) = ty.as_overflow_pair() {
        let mut out = Vec::new();
        for int_val in boundary_values_for_int(ity) {
            if let Val::Scalar(sv) = int_val {
                out.push(ArgCandidate::pure(Val::overflow_pair(sv, false)));
                out.push(ArgCandidate::pure(Val::overflow_pair(sv, true)));
            }
        }
        return Some(out);
    }
    match ty {
        Ty::Never => Some(Vec::new()),
        Ty::Unit => Some(vec![ArgCandidate::pure(Val::Unit)]),
        Ty::Bool => {
            Some(vec![ArgCandidate::pure(Val::Bool(false)), ArgCandidate::pure(Val::Bool(true))])
        }
        Ty::Ordering => Some(vec![
            ArgCandidate::pure(Val::Ordering(OrderingVal::Less)),
            ArgCandidate::pure(Val::Ordering(OrderingVal::Equal)),
            ArgCandidate::pure(Val::Ordering(OrderingVal::Greater)),
        ]),
        Ty::Char => Some(
            ['\0', 'a', 'A', '\u{7f}', '\u{80}', '\u{d7ff}', '\u{e000}', '\u{10ffff}']
                .into_iter()
                .map(|c| ArgCandidate::pure(Val::Char(c)))
                .collect(),
        ),
        Ty::Int(ity) => {
            Some(boundary_values_for_int(*ity).into_iter().map(ArgCandidate::pure).collect())
        }
        Ty::Enum(ety) => {
            if !enum_admitted(ety) {
                return None;
            }
            let cap = ety.discriminants.len().min(16);
            Some(
                (0..cap)
                    .map(|variant| ArgCandidate::pure(Val::EnumVal { ty: ety.clone(), variant }))
                    .collect(),
            )
        }
        Ty::RangeTo { elem } if enable_profile_v2 && elem.is_usize() => Some(
            [0u64, 1, 2, 4, u64::MAX / 2, u64::MAX]
                .into_iter()
                .map(|end| ArgCandidate::pure(Val::RangeTo(end)))
                .collect(),
        ),
        Ty::RangeFrom { elem } if enable_profile_v2 && elem.is_usize() => Some(
            [0u64, 1, 2, 4, u64::MAX / 2, u64::MAX]
                .into_iter()
                .map(|start| ArgCandidate::pure(Val::RangeFrom(start)))
                .collect(),
        ),
        Ty::Ref { mutability, pointee } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            boundary_candidates_for_ref(*mutability, pointee, endian)
        }
        Ty::RawPtr { mutability, pointee } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            boundary_candidates_for_raw_ptr(*mutability, pointee, endian)
        }
        Ty::Tuple { fields } if enable_profile_v2 => {
            if fields.is_empty() {
                return Some(vec![ArgCandidate::pure(Val::Tuple(Vec::new()))]);
            }
            let mut per_field = Vec::with_capacity(fields.len());
            let mut uninhabited = false;
            for f in fields {
                // Validate every field shape before short-circuiting on an
                // uninhabited field (so `(Never, Unsupported)` returns `None`,
                // not `Some([])`).
                let vals = boundary_candidates_for_ty(f, true, endian)?;
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
                let mut field_cands = Vec::with_capacity(per_field.len());
                for vs in &per_field {
                    field_cands.push(vs[i % vs.len()].clone());
                }
                let (vals, cm) = materialize_case(&field_cands);
                // Re-base allocation ids back to `1..=k` for template storage.
                let base_shift = 1u64;
                let norm_vals: Vec<Val> =
                    vals.into_iter().map(|v| shift_val_allocs_down(&v, base_shift)).collect();
                let norm_allocs: Vec<Allocation> = cm
                    .allocations
                    .into_iter()
                    .map(|mut a| {
                        a.alloc_id -= base_shift;
                        a
                    })
                    .collect();
                tuples.push(ArgCandidate { val: Val::Tuple(norm_vals), allocs: norm_allocs });
            }
            Some(tuples)
        }
        Ty::Option { elem } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            let inner_cands = boundary_candidates_for_ty(elem, true, endian)?;
            let mut out = Vec::with_capacity(1 + inner_cands.len());
            out.push(ArgCandidate::pure(Val::OptionVal(None)));
            for cand in inner_cands {
                out.push(ArgCandidate {
                    val: Val::OptionVal(Some(Box::new(cand.val))),
                    allocs: cand.allocs,
                });
            }
            Some(out)
        }
        _ => None,
    }
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

fn random_candidate_for_ty(
    ty: &Ty,
    boundary_pool: &[ArgCandidate],
    rng: &mut SplitMix64,
    enable_profile_v2: bool,
    endian: TargetEndian,
) -> Option<ArgCandidate> {
    if !boundary_pool.is_empty() && (rng.next_u64() & 1) == 0 {
        return Some(boundary_pool[rng.choose_index(boundary_pool.len())].clone());
    }
    if let Some(ity) = ty.as_overflow_pair() {
        let bits = rng.next_u128() & ity.width.mask();
        let sv = ScalarVal::new(ity.width, ity.signed, bits);
        return Some(ArgCandidate::pure(Val::overflow_pair(sv, (rng.next_u64() & 1) == 1)));
    }
    match ty {
        Ty::Never => None,
        Ty::Unit => Some(ArgCandidate::pure(Val::Unit)),
        Ty::Bool => Some(ArgCandidate::pure(Val::Bool((rng.next_u64() & 1) == 1))),
        Ty::Ordering => Some(ArgCandidate::pure(match rng.next_u64() % 3 {
            0 => Val::Ordering(OrderingVal::Less),
            1 => Val::Ordering(OrderingVal::Equal),
            _ => Val::Ordering(OrderingVal::Greater),
        })),
        Ty::Char => {
            let candidate = rng.next_u64() % 0x11_0000;
            let val = char::from_u32(candidate as u32).unwrap_or('a');
            Some(ArgCandidate::pure(Val::Char(val)))
        }
        Ty::Int(ity) => Some(ArgCandidate::pure(Val::Scalar(ScalarVal::new(
            ity.width,
            ity.signed,
            rng.next_u128(),
        )))),
        Ty::Enum(ety) if enum_admitted(ety) => {
            let idx = rng.choose_index(ety.discriminants.len());
            Some(ArgCandidate::pure(Val::EnumVal { ty: ety.clone(), variant: idx }))
        }
        Ty::RangeTo { elem } if enable_profile_v2 && elem.is_usize() => {
            Some(ArgCandidate::pure(Val::RangeTo(rng.next_u64() % 16)))
        }
        Ty::RangeFrom { elem } if enable_profile_v2 && elem.is_usize() => {
            Some(ArgCandidate::pure(Val::RangeFrom(rng.next_u64() % 16)))
        }
        Ty::Ref { mutability, pointee } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            if let Ty::Slice { elem } = pointee.as_ref()
                && let Ty::Int(ity) = elem.as_ref()
            {
                let lay = int_layout(ity.width);
                let count = (rng.next_u64() % 9) as usize;
                let total = (lay.size as usize) * count;
                let bytes: Vec<AllocByte> = (0..total)
                    .map(|_| AllocByte::Init { byte: (rng.next_u64() & 0xff) as u8, prov: None })
                    .collect();
                return Some(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                        len: count as u64,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: *mutability,
                        bytes,
                        live: true,
                    }],
                });
            }
            if **pointee == Ty::Str {
                // A random valid UTF-8 string of up to 8 one- to four-byte
                // characters.
                const CHARS: [char; 5] = ['a', 'Z', '\u{e9}', '\u{20ac}', '\u{1f600}'];
                let count = (rng.next_u64() % 9) as usize;
                let mut text = String::new();
                for _ in 0..count {
                    text.push(CHARS[rng.choose_index(CHARS.len())]);
                }
                return Some(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                        len: text.len() as u64,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: 0,
                        mutability: *mutability,
                        bytes: text
                            .bytes()
                            .map(|byte| AllocByte::Init { byte, prov: None })
                            .collect(),
                        live: true,
                    }],
                });
            }
            (!boundary_pool.is_empty())
                .then(|| boundary_pool[rng.choose_index(boundary_pool.len())].clone())
        }
        Ty::RawPtr { .. } if enable_profile_v2 && is_supported_v2_local_ty(ty) => (!boundary_pool
            .is_empty())
        .then(|| boundary_pool[rng.choose_index(boundary_pool.len())].clone()),
        Ty::Tuple { fields } if enable_profile_v2 => {
            let mut field_cands = Vec::with_capacity(fields.len());
            for f in fields {
                let pool = boundary_candidates_for_ty(f, true, endian)?;
                field_cands.push(random_candidate_for_ty(f, &pool, rng, true, endian)?);
            }
            let (vals, cm) = materialize_case(&field_cands);
            let norm_vals: Vec<Val> =
                vals.into_iter().map(|v| shift_val_allocs_down(&v, 1)).collect();
            let norm_allocs: Vec<Allocation> = cm
                .allocations
                .into_iter()
                .map(|mut a| {
                    a.alloc_id -= 1;
                    a
                })
                .collect();
            Some(ArgCandidate { val: Val::Tuple(norm_vals), allocs: norm_allocs })
        }
        Ty::Option { elem } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            if (rng.next_u64() & 3) == 0 {
                return Some(ArgCandidate::pure(Val::OptionVal(None)));
            }
            let pool = boundary_candidates_for_ty(elem, true, endian)?;
            if pool.is_empty() {
                return Some(ArgCandidate::pure(Val::OptionVal(None)));
            }
            let inner = random_candidate_for_ty(elem, &pool, rng, true, endian)?;
            Some(ArgCandidate {
                val: Val::OptionVal(Some(Box::new(inner.val))),
                allocs: inner.allocs,
            })
        }
        _ => None,
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
