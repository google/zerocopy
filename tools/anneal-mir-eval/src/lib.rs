// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure, I/O-free concrete Rust evaluator and pre-proof counterexample stepper
//! for MIR IR captured by `anneal-rustc-capture` (schema version 4, Profile v1,
//! and opt-in Profile v2 extensions).
//!
//! Semantics align with `Trusted.MirSemantics`: 1-aligned zero-sized memory
//! accesses (`size == 0 && align_log2 == 0`, covering all Profile v1 ZSTs)
//! succeed without allocation lookup, while over-aligned zero-sized accesses
//! (`size == 0 && align_log2 > 0`) follow `rustc`'s `get_place_alloc` /
//! `get_place_alloc_mut` by checking allocation existence and alignment.

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
    CallReturnTarget, EvalConfig, EvalProfile, FrameState, LocalSlot, MachineState, Outcome,
    StepEvent, StepOutcome, StepTrace, TerminalOut, eval_body, eval_body_auto,
    eval_body_by_identity, eval_body_with_config, validate_body_entry, validate_program_config,
};
pub use ir::{
    AggregateKind, AssertKind, BinOp, Block, Body, CAPTURE_SCHEMA_VERSION, CaptureInput, CastKind,
    ConstLit, EnumTagRepr, EnumTy, Instantiation, IntTy, IntWidth, Manifest, Mutability, Operand,
    Program, ProjectionElem, Rvalue, Scope, Statement, Terminator, Ty, UnOp, UnwindAction,
};
pub use memory::{
    Allocation, CallerMemory, LayoutData, MemPlace, MemoryState, TargetEndian, decode_val,
    encode_val, eval_const_lit, layout_of_ty, load_indirect, store_indirect,
};
pub use ops::{eval_bin_op, eval_int_to_int_cast, eval_un_op};
pub use value::{
    AllocByte, FaultDetail, FaultKind, OrderingVal, PtrVal, ScalarVal, Val, check_args_match,
    check_val, enum_admitted, is_int_like_ty, is_primitive_readable_ty, is_supported_local_ty,
    is_unicode_scalar, is_zst_enum_ty, val_ty,
};
