// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure, I/O-free concrete Rust evaluator and pre-proof counterexample stepper
//! for MIR IR captured by `anneal-rustc-capture` (schema version 5, Profile v1
//! and Profile v2).
//!
//! Semantics align 1:1 with `Trusted.MirSemantics`:
//! - Profile v1 executes scalar, enum, and overflow-pair bodies with
//!   multi-frame intra-crate `Call` (refusing `unsafe fn` callees) and pinned
//!   `core::num` `SysrootCall` frames.
//! - Profile v2 executes single-frame pointer, reference, slice, `RangeTo`/
//!   `RangeFrom`, `CoreCall`, `Assert`, and single-level `PartialTuple` bodies
//!   over explicit `CallerMemory`.
//! - Byte-level memory reads and writes (`MemoryState::{read_bytes,
//!   write_bytes, write_uninit}`) always resolve `alloc_id` first and check
//!   alignment even at size 0, matching `Trusted.MirSemantics.Memory`.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod counterexample;
pub mod eval;
pub mod ir;
pub mod memory;
pub mod ops;
pub mod value;

pub use counterexample::{
    Counterexample, ProbeConfig, ProbeReport, probe_body, probe_body_with_policy,
};
pub use eval::{
    CallReturnTarget, EvalConfig, EvalProfile, FrameState, LocalSlot, MachineState, Outcome, Query,
    StepEvent, StepOutcome, StepTrace, TerminalOut, body_mixes_refs_and_raw_ptrs_v2, eval_body,
    eval_body_auto, eval_body_by_identity, eval_body_with_caller_mem, eval_body_with_config,
    eval_body_with_query, is_undefined_fault, sysroot_num_bin_op, sysroot_num_body,
    validate_body_entry, validate_body_in_program, validate_program_config,
};
pub use ir::{
    AggregateKind, AssertKind, BinOp, Block, Body, CAPTURE_SCHEMA_VERSION, CaptureInput, CastKind,
    ConstLit, CoreCallOp, EnumTagRepr, EnumTy, Instantiation, IntTy, IntWidth, Manifest,
    Mutability, Operand, Place, Program, ProjectionElem, Rvalue, Scope, Statement, StdlibCrate,
    SysrootNumKind, SysrootNumOp, Terminator, Ty, UnOp, UnwindAction,
};
pub use memory::{
    Allocation, CallerMemory, ISIZE_MAX_BYTES, LayoutData, MemPlace, MemoryState, RefAccessSpan,
    TargetEndian, decode_val, deinit_indirect, encode_val, eval_const_lit, int_layout,
    is_slice_all_init, layout_of_ty, load_indirect, offset_is_aligned, overflow_pair_layout,
    ptr_add_in_mem, read_ptr_prov, ref_access_spans, ref_access_spans_list, ref_valid_in_mem,
    refs_stay_in_caller_mem, refs_valid_in_mem, refs_valid_in_mem_list, slice_from_raw_parts_check,
    slice_get_unchecked_check, spans_pairwise_disjoint, store_indirect, valid_caller_memory,
};
pub use ops::{eval_bin_op, eval_int_to_int_cast, eval_un_op};
pub use value::{
    AllocByte, FaultDetail, FaultKind, OrderingVal, PtrVal, ScalarVal, UbClass, Val, WitnessClass,
    check_args_match, check_val, enum_admitted, is_int_like_ty, is_primitive_readable_ty,
    is_supported_local_ty, is_supported_v1_local_ty, is_supported_v2_local_ty, is_unicode_scalar,
    is_zst_enum_ty, val_ty,
};
