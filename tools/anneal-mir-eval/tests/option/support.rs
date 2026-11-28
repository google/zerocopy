// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Program builders, outcome accessors, and shared values for the
//! `option` tests.

use std::collections::BTreeSet;

use anneal_mir_eval::{
    AllocByte, Allocation, Block, Body, CallerMemory, CoreCallOp, EvalConfig, FaultDetail,
    FaultKind, IntTy, IntWidth, Mutability, Operand, Outcome, PanicStrategy, Place, Program,
    ProjectionElem, Rvalue, Scope, Statement, TargetEndian, TerminalOut, Terminator, Ty,
    UnwindAction, Val, eval_body_with_config,
};

pub(super) const U8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
pub(super) const I8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: true });
pub(super) const USIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
pub(super) const ISIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: true });

pub(super) fn opt(ty: Ty) -> Ty {
    Ty::Option { elem: Box::new(ty) }
}

pub(super) fn copy(local: u32) -> Operand {
    Operand::Copy { local, projection: Vec::new() }
}

pub(super) fn assign(local: u32, value: Rvalue) -> Statement {
    Statement::Assign { local, projection: Vec::new(), value }
}

pub(super) fn ret_block(statements: Vec<Statement>) -> Block {
    Block { statements, terminator: Terminator::Ret, cleanup: false }
}

pub(super) fn v2_program(arg_count: usize, local_tys: Vec<Ty>, blocks: Vec<Block>) -> Program {
    let mut roots = BTreeSet::new();
    roots.insert("test::entry".into());
    Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        bodies: vec![Body {
            arg_count,
            is_unsafe: false,
            local_tys,
            blocks,
            identity: "test::entry".into(),
        }],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        panic: PanicStrategy::Unwind,
        has_local_panic_handler: true,
    }
}

pub(super) fn run(prog: &Program, args: &[Val]) -> Outcome {
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    eval_body_with_config(prog, 0, args, 256, &cfg).outcome
}

pub(super) fn returned(outcome: Outcome) -> Val {
    match outcome {
        Outcome::Returned(TerminalOut::Returned { ret, .. }) => ret,
        other => panic!("expected a normal return, got {other:?}"),
    }
}

pub(super) fn fault_detail(outcome: Outcome) -> FaultDetail {
    match outcome {
        Outcome::Fault(detail) => detail,
        other => panic!("expected a fault, got {other:?}"),
    }
}

pub(super) fn fault_kind(outcome: Outcome) -> FaultKind {
    fault_detail(outcome).kind
}

pub(super) fn some(v: Val) -> Val {
    Val::OptionVal(Some(Box::new(v)))
}

pub(super) const NONE: Val = Val::OptionVal(None);

/// `fn(a: T, b: T) -> Option<T> { a.<op>(b) }` as one `CoreCall` body.
pub(super) fn checked_prog(op: CoreCallOp, arg_ty: Ty, dst_ty: Ty) -> Program {
    v2_program(
        2,
        vec![dst_ty, arg_ty.clone(), arg_ty],
        vec![
            Block {
                statements: Vec::new(),
                terminator: Terminator::CoreCall {
                    op,
                    args: vec![copy(1), copy(2)],
                    dst: Place { local: 0, projection: Vec::new() },
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
                cleanup: false,
            },
            ret_block(Vec::new()),
        ],
    )
}

pub(super) fn payload_proj(fty: Ty) -> Vec<ProjectionElem> {
    vec![
        ProjectionElem::Downcast { variant_idx: 1 },
        ProjectionElem::Field { field_idx: 0, ty: fty },
    ]
}

pub(super) fn caller_mem_with_bytes(n: usize) -> CallerMemory {
    CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 0,
            mutability: Mutability::Shared,
            bytes: vec![AllocByte::Init { byte: 0, prov: None }; n],
            live: true,
        }],
    }
}
