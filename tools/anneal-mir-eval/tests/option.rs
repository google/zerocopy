// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Profile v2 `Option<T>` values, `Option` payload projections, and the
//! checked-arithmetic and `Option::unwrap` core calls, mirroring
//! `Trusted.MirSemantics` (`evalRvalueV2`'s `.aggregateOption` arm,
//! `evalOptionDiscriminantOfVal`, `projectValFieldV2`, and `execCoreCallOp`).

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use anneal_mir_eval::{
    AllocByte, Allocation, Block, Body, CallerMemory, CaptureInput, ConstLit, CoreCallOp,
    EvalConfig, FaultDetail, FaultKind, IntTy, IntWidth, MemoryState, Mutability, Operand, Outcome,
    PanicStrategy, Place, ProbeConfig, Program, ProjectionElem, PtrVal, Query, RodataByte, Rvalue,
    ScalarVal, Scope, Statement, TargetEndian, TerminalOut, Terminator, Ty, UbClass, UnwindAction,
    Val, WitnessClass, eval_body_with_caller_mem, eval_body_with_config, has_escaping_rodata_ptr,
    probe_body,
};

const U8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
const I8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: true });
const USIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
const ISIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: true });

fn opt(ty: Ty) -> Ty {
    Ty::Option { elem: Box::new(ty) }
}

fn copy(local: u32) -> Operand {
    Operand::Copy { local, projection: Vec::new() }
}

fn assign(local: u32, value: Rvalue) -> Statement {
    Statement::Assign { local, projection: Vec::new(), value }
}

fn ret_block(statements: Vec<Statement>) -> Block {
    Block { statements, terminator: Terminator::Ret, cleanup: false }
}

fn v2_program(arg_count: usize, local_tys: Vec<Ty>, blocks: Vec<Block>) -> Program {
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

fn run(prog: &Program, args: &[Val]) -> Outcome {
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    eval_body_with_config(prog, 0, args, 256, &cfg).outcome
}

fn returned(outcome: Outcome) -> Val {
    match outcome {
        Outcome::Returned(TerminalOut::Returned { ret, .. }) => ret,
        other => panic!("expected a normal return, got {other:?}"),
    }
}

fn fault_detail(outcome: Outcome) -> FaultDetail {
    match outcome {
        Outcome::Fault(detail) => detail,
        other => panic!("expected a fault, got {other:?}"),
    }
}

fn fault_kind(outcome: Outcome) -> FaultKind {
    fault_detail(outcome).kind
}

fn some(v: Val) -> Val {
    Val::OptionVal(Some(Box::new(v)))
}

const NONE: Val = Val::OptionVal(None);

/// `fn(a: T, b: T) -> Option<T> { a.<op>(b) }` as one `CoreCall` body.
fn checked_prog(op: CoreCallOp, arg_ty: Ty, dst_ty: Ty) -> Program {
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

#[test]
fn checked_arithmetic_returns_none_exactly_on_overflow() {
    let u8_ity = IntTy { width: IntWidth::I8, signed: false };
    let i8_ity = IntTy { width: IntWidth::I8, signed: true };
    let usize_ity = IntTy { width: IntWidth::Isize, signed: false };
    let u8v = |v: u8| Val::u8(v);
    let i8v = |v: i8| Val::Scalar(ScalarVal::new(IntWidth::I8, true, v as u8 as u128));
    let usz = |v: u64| Val::usize_val(v);
    let cases: Vec<(CoreCallOp, Ty, Val, Val, Val)> = vec![
        (CoreCallOp::NumCheckedAdd(u8_ity), U8_TY, u8v(1), u8v(2), some(u8v(3))),
        (CoreCallOp::NumCheckedAdd(u8_ity), U8_TY, u8v(255), u8v(0), some(u8v(255))),
        (CoreCallOp::NumCheckedAdd(u8_ity), U8_TY, u8v(200), u8v(56), NONE),
        (CoreCallOp::NumCheckedSub(u8_ity), U8_TY, u8v(0), u8v(1), NONE),
        (CoreCallOp::NumCheckedSub(u8_ity), U8_TY, u8v(7), u8v(7), some(u8v(0))),
        (CoreCallOp::NumCheckedSub(i8_ity), I8_TY, i8v(-128), i8v(1), NONE),
        (CoreCallOp::NumCheckedSub(i8_ity), I8_TY, i8v(-127), i8v(1), some(i8v(-128))),
        (CoreCallOp::NumCheckedAdd(i8_ity), I8_TY, i8v(127), i8v(1), NONE),
        (CoreCallOp::NumCheckedMul(i8_ity), I8_TY, i8v(-128), i8v(-1), NONE),
        (CoreCallOp::NumCheckedMul(i8_ity), I8_TY, i8v(-64), i8v(2), some(i8v(-128))),
        (CoreCallOp::NumCheckedMul(usize_ity), USIZE_TY, usz(1 << 32), usz(1 << 32), NONE),
        (
            CoreCallOp::NumCheckedMul(usize_ity),
            USIZE_TY,
            usz(u64::MAX / 3),
            usz(3),
            some(usz(u64::MAX)),
        ),
    ];
    for (op, ty, a, b, expected) in cases {
        let prog = checked_prog(op.clone(), ty.clone(), opt(ty));
        assert_eq!(returned(run(&prog, &[a.clone(), b.clone()])), expected, "{op:?}({a:?}, {b:?})");
    }

    // Argument signedness and destination type are checked against the op.
    let mismatched_args = checked_prog(CoreCallOp::NumCheckedAdd(u8_ity), I8_TY, opt(U8_TY));
    assert_eq!(fault_kind(run(&mismatched_args, &[i8v(1), i8v(1)])), FaultKind::Unsupported);
    // An overflowing result is `None`, which carries no signedness, so only
    // the argument check rejects it.
    assert_eq!(fault_kind(run(&mismatched_args, &[i8v(127), i8v(1)])), FaultKind::Unsupported);
    let non_option_dst = checked_prog(CoreCallOp::NumCheckedAdd(u8_ity), U8_TY, U8_TY);
    assert_eq!(fault_kind(run(&non_option_dst, &[u8v(1), u8v(1)])), FaultKind::Unsupported);
}

/// `fn(x: Option<u8>) -> isize { discriminant(x) }`.
#[test]
fn option_discriminant_is_isize_variant_index() {
    let prog = v2_program(
        1,
        vec![ISIZE_TY, opt(U8_TY)],
        vec![ret_block(vec![assign(
            0,
            Rvalue::Discriminant { place: Place { local: 1, projection: Vec::new() } },
        )])],
    );
    let isize_val = |v: u128| Val::Scalar(ScalarVal::new(IntWidth::Isize, true, v));
    assert_eq!(returned(run(&prog, &[NONE])), isize_val(0));
    assert_eq!(returned(run(&prog, &[some(Val::u8(9))])), isize_val(1));

    // `discriminantTypesValidV2` requires an `isize` destination.
    let bad_dst = v2_program(
        1,
        vec![USIZE_TY, opt(U8_TY)],
        vec![ret_block(vec![assign(
            0,
            Rvalue::Discriminant { place: Place { local: 1, projection: Vec::new() } },
        )])],
    );
    assert_eq!(fault_kind(run(&bad_dst, &[NONE])), FaultKind::Unsupported);
}

fn payload_proj(fty: Ty) -> Vec<ProjectionElem> {
    vec![
        ProjectionElem::Downcast { variant_idx: 1 },
        ProjectionElem::Field { field_idx: 0, ty: fty },
    ]
}

/// `fn(x: Option<T>) -> T { (x as Some).0 }`.
#[test]
fn option_payload_projection_reads_some_and_is_ub_on_none() {
    let read_payload = |elem_ty: Ty, operand: Operand| {
        v2_program(
            1,
            vec![elem_ty.clone(), opt(elem_ty)],
            vec![ret_block(vec![assign(0, Rvalue::Use { operand, with_retag: false })])],
        )
    };
    let copy_payload =
        read_payload(U8_TY, Operand::Copy { local: 1, projection: payload_proj(U8_TY) });
    assert_eq!(returned(run(&copy_payload, &[some(Val::u8(42))])), Val::u8(42));
    let none_u8 = fault_detail(run(&copy_payload, &[NONE]));
    assert_eq!(none_u8.kind, FaultKind::Undefined);
    assert_eq!(none_u8.ub_class, Some(UbClass::InactiveOptionPayloadRead));
    assert_eq!(none_u8.witness_class(), Some(WitnessClass::ReplayableMiriUb));

    // Zero-sized `Option<()>` payload copy on `None` is a conservative
    // model-only UB class because Miri accepts reading zero bytes of `()`.
    let copy_unit_payload =
        read_payload(Ty::Unit, Operand::Copy { local: 1, projection: payload_proj(Ty::Unit) });
    assert_eq!(returned(run(&copy_unit_payload, &[some(Val::Unit)])), Val::Unit);
    let none_unit = fault_detail(run(&copy_unit_payload, &[NONE]));
    assert_eq!(none_unit.kind, FaultKind::Undefined);
    assert_eq!(none_unit.ub_class, Some(UbClass::ZstOptionNonePayloadRead));
    assert_eq!(none_unit.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));

    // `readPlaceV2` refuses moves through `.downcast`.
    let move_payload =
        read_payload(U8_TY, Operand::Move { local: 1, projection: payload_proj(U8_TY) });
    assert_eq!(fault_kind(run(&move_payload, &[some(Val::u8(42))])), FaultKind::Unsupported);

    // Only variant 1 followed by field 0 of the payload type is a payload path.
    for proj in [
        vec![
            ProjectionElem::Downcast { variant_idx: 0 },
            ProjectionElem::Field { field_idx: 0, ty: U8_TY },
        ],
        payload_proj(I8_TY),
        vec![ProjectionElem::Downcast { variant_idx: 1 }],
    ] {
        let prog = read_payload(U8_TY, Operand::Copy { local: 1, projection: proj.clone() });
        assert_eq!(
            fault_kind(run(&prog, &[some(Val::u8(42))])),
            FaultKind::Unsupported,
            "{proj:?}"
        );
    }
}

/// `fn(x: u8) -> Option<u8>` building `None` and `Some(x)`.
#[test]
fn aggregate_option_builds_none_and_some() {
    let build = |variant_idx: u64, payload: Option<Operand>, dst: Ty| {
        v2_program(
            1,
            vec![dst, U8_TY],
            vec![ret_block(vec![assign(
                0,
                Rvalue::AggregateOption {
                    variant_idx,
                    inner_ty: U8_TY,
                    payload: payload.map(Box::new),
                },
            )])],
        )
    };
    assert_eq!(returned(run(&build(0, None, opt(U8_TY)), &[Val::u8(5)])), NONE);
    assert_eq!(
        returned(run(&build(1, Some(copy(1)), opt(U8_TY)), &[Val::u8(5)])),
        some(Val::u8(5))
    );
    for prog in [
        build(1, None, opt(U8_TY)),
        build(0, Some(copy(1)), opt(U8_TY)),
        build(2, Some(copy(1)), opt(U8_TY)),
        build(0, None, opt(I8_TY)),
    ] {
        assert_eq!(fault_kind(run(&prog, &[Val::u8(5)])), FaultKind::Unsupported);
    }
}

/// `fn(x: Option<u8>) -> u8 { x.unwrap() }`.
#[test]
fn option_unwrap_returns_payload_and_fails_closed_on_none() {
    let prog = v2_program(
        1,
        vec![U8_TY, opt(U8_TY)],
        vec![
            Block {
                statements: Vec::new(),
                terminator: Terminator::CoreCall {
                    op: CoreCallOp::OptionUnwrap { inner: U8_TY },
                    args: vec![copy(1)],
                    dst: Place { local: 0, projection: Vec::new() },
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
                cleanup: false,
            },
            ret_block(Vec::new()),
        ],
    );
    assert_eq!(returned(run(&prog, &[some(Val::u8(3))])), Val::u8(3));
    // `corePanicTrap` is `.unsupported`.
    assert_eq!(fault_kind(run(&prog, &[NONE])), FaultKind::Unsupported);
}

/// Option types outside `isOptionPayloadSupportedV2` (nested options) and the
/// captured-but-unmodeled core calls fail closed.
#[test]
fn unmodeled_option_shapes_fail_closed() {
    let nested = v2_program(
        0,
        vec![opt(opt(U8_TY))],
        vec![ret_block(vec![assign(
            0,
            Rvalue::AggregateOption { variant_idx: 0, inner_ty: opt(U8_TY), payload: None },
        )])],
    );
    assert_eq!(fault_kind(run(&nested, &[])), FaultKind::Unsupported);

    let opt_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(opt(U8_TY)) };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    // `&Option<u8>` is rejected at body-entry validation (`steps_executed` 0)
    // because `Option<T>` has no memory layout in this evaluator.
    let bad_local_prog = v2_program(1, vec![Ty::Bool, opt_ref], vec![ret_block(Vec::new())]);
    let mut mem = caller_mem_with_bytes(2);
    mem.allocations[0].bytes[0] = AllocByte::Init { byte: 1, prov: None };
    mem.allocations[0].bytes[1] = AllocByte::Init { byte: 7, prov: None };
    let ptr = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    let entry_trace = eval_body_with_caller_mem(&bad_local_prog, 0, &[ptr], mem, 256, &cfg);
    assert_eq!(entry_trace.steps_executed, 0);
    assert_eq!(fault_kind(entry_trace.outcome), FaultKind::Unsupported);

    // With supported immediate `Option<u8>` locals, `OptionIsSome`,
    // `OptionIsNone`, and `OptionTake` reach `exec_core_call_op` and fail
    // closed at the terminator step.
    for (op, dst_ty) in [
        (CoreCallOp::OptionIsSome { inner: U8_TY }, Ty::Bool),
        (CoreCallOp::OptionIsNone { inner: U8_TY }, Ty::Bool),
        (CoreCallOp::OptionTake { inner: U8_TY }, opt(U8_TY)),
    ] {
        let prog = v2_program(
            1,
            vec![dst_ty, opt(U8_TY)],
            vec![
                Block {
                    statements: Vec::new(),
                    terminator: Terminator::CoreCall {
                        op: op.clone(),
                        args: vec![copy(1)],
                        dst: Place { local: 0, projection: Vec::new() },
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                ret_block(Vec::new()),
            ],
        );
        let trace = eval_body_with_config(&prog, 0, &[some(Val::u8(7))], 256, &cfg);
        assert_eq!(trace.steps_executed, 1, "{op:?}");
        assert_eq!(fault_kind(trace.outcome), FaultKind::Unsupported, "{op:?}");
    }
}

/// Every `CoreCallOp`, `Ty`, `ProjectionElem`, and `Rvalue` shape that
/// `anneal-rustc-capture` serializes parses, so manifests using one load and
/// fail closed with `Unsupported` instead of failing to deserialize.
#[test]
fn capture_core_call_and_option_shapes_parse() {
    let int = r#""width": "i32", "signed": false"#;
    let ty = r#"{"kind": "int", "width": "i8", "signed": false}"#;
    let ops = [
        r#"{"kind": "slice_index_range", "mutability": "shared", "elem": TY}"#.replace("TY", ty),
        r#"{"kind": "slice_index_range_from", "mutability": "mut", "elem": TY}"#.replace("TY", ty),
        r#"{"kind": "slice_is_empty", "elem": TY}"#.replace("TY", ty),
        r#"{"kind": "slice_split_at", "mutability": "shared", "elem": TY}"#.replace("TY", ty),
        format!(r#"{{"kind": "num_is_multiple_of", {int}}}"#),
        format!(r#"{{"kind": "num_checked_add", {int}}}"#),
        format!(r#"{{"kind": "num_checked_mul", {int}}}"#),
        format!(r#"{{"kind": "num_checked_sub", {int}}}"#),
        format!(r#"{{"kind": "num_saturating_add", {int}}}"#),
        format!(r#"{{"kind": "num_wrapping_shl", {int}}}"#),
        format!(r#"{{"kind": "num_wrapping_shr", {int}}}"#),
        format!(r#"{{"kind": "num_leading_zeros", {int}}}"#),
        format!(r#"{{"kind": "num_overflowing_add", {int}}}"#),
        format!(r#"{{"kind": "num_overflowing_sub", {int}}}"#),
        format!(r#"{{"kind": "cmp_min", {int}}}"#),
        format!(r#"{{"kind": "cmp_max", {int}}}"#),
        r#"{"kind": "mem_replace", "ty": TY}"#.replace("TY", ty),
        r#"{"kind": "option_is_some", "inner": TY}"#.replace("TY", ty),
        r#"{"kind": "option_is_none", "inner": TY}"#.replace("TY", ty),
        r#"{"kind": "option_take", "inner": TY}"#.replace("TY", ty),
        r#"{"kind": "option_unwrap", "inner": TY}"#.replace("TY", ty),
    ];
    for op in ops {
        serde_json::from_str::<CoreCallOp>(&op).unwrap_or_else(|e| panic!("{op}: {e}"));
    }
    let range: Ty = serde_json::from_str(
        r#"{"kind": "range", "elem": {"kind": "int", "width": "isize", "signed": false}}"#,
    )
    .unwrap();
    assert!(matches!(range, Ty::Range { .. }));
    let downcast: ProjectionElem =
        serde_json::from_str(r#"{"kind": "downcast", "variant_idx": 1}"#).unwrap();
    assert_eq!(downcast, ProjectionElem::Downcast { variant_idx: 1 });
    let agg_range: Rvalue = serde_json::from_str(
        r#"{"kind": "aggregate_range", "elem_ty": {"kind": "int", "width": "isize", "signed": false},
            "start": {"kind": "copy", "local": 1}, "end": {"kind": "copy", "local": 2}}"#,
    )
    .unwrap();
    assert!(matches!(agg_range, Rvalue::AggregateRange { .. }));
}

/// The reference implementation of the captured fixture below
/// (`fixtures/option_checked_split_capture.json`, captured as crate
/// `hybrid_pilot`). It keeps the captured source's explicit `match`es so that
/// it reads line for line against the capture, except that the final split
/// uses the safe `bytes.get(..size)` where the captured source has
/// `Some(unsafe { bytes.get_unchecked(..size) })`.
#[allow(clippy::question_mark)]
fn split_dst_prefix(bytes: &[u8]) -> Option<&[u8]> {
    let len = bytes.len();
    if len < 4 {
        return None;
    }
    let avail = len - 4;
    let elems = (avail & !3usize) / 6;
    let tb = match elems.checked_mul(6) {
        Some(v) => v,
        None => return None,
    };
    let rem = tb % 4;
    let pad = if rem == 0 { 0 } else { 4 - rem };
    let size = match tb.checked_add(pad) {
        Some(v) => match v.checked_add(4) {
            Some(s) => s,
            None => return None,
        },
        None => return None,
    };
    if size > len {
        return None;
    }
    let tb1 = tb + 6;
    let rem1 = tb1 % 4;
    let pad1 = if rem1 == 0 { 0 } else { 4 - rem1 };
    let next = tb1 + pad1 + 4;
    if next <= len {
        return None;
    }
    bytes.get(..size)
}

/// End to end on a real capture: `checked_mul`/`checked_add` core calls,
/// `Discriminant` and `SwitchInt` over `Option<usize>`, `.downcast 1`
/// payload copies, `AggregateOption` into an `Option<&[u8]>` return, and a
/// gated `get_unchecked(..size)`, differentially against the Rust source.
#[test]
fn captured_option_checked_split_matches_rust() {
    const CAPTURE_JSON: &str = include_str!("fixtures/option_checked_split_capture.json");
    let CaptureInput::Manifest(manifest) = CaptureInput::from_json_str(CAPTURE_JSON).unwrap()
    else {
        panic!("expected schema-v5 capture manifest");
    };
    let program = &manifest.program;
    assert_eq!(program.bodies[0].identity, "rust-path-v1::split_dst_prefix");
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    for n in 0..=64usize {
        let bytes = vec![0u8; n];
        let expected = split_dst_prefix(&bytes).map(<[u8]>::len);
        let trace = eval_body_with_caller_mem(
            program,
            0,
            &[Val::SlicePtr {
                ptr: PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize },
                len: n as u64,
            }],
            caller_mem_with_bytes(n),
            10_000,
            &cfg,
        );
        let got = match trace.outcome {
            Outcome::Returned(TerminalOut::Returned { ret: Val::OptionVal(None), .. }) => None,
            Outcome::Returned(TerminalOut::Returned {
                ret: Val::OptionVal(Some(inner)), ..
            }) => match *inner {
                Val::SlicePtr { ptr, len } => {
                    assert_eq!((ptr.alloc_id, ptr.offset_bytes), (Some(2), 0));
                    Some(len as usize)
                }
                other => panic!("unexpected payload {other:?}"),
            },
            other => panic!("n = {n}: unexpected outcome {other:?}"),
        };
        assert_eq!(got, expected, "n = {n}");
    }
}

fn caller_mem_with_bytes(n: usize) -> CallerMemory {
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

/// Exercise all five `Option` walker and allocation-id arms in `memory.rs`:
/// `max_val_ptr_alloc_id`, `refs_valid_in_mem`, `collect_ref_access_spans`,
/// `collect_ptr_or_ref_alloc_ids` (`has_escaping_rodata_ptr`), and
/// `refs_stay_in_caller_mem`.
#[test]
fn option_reference_and_pointer_walkers_reject_invalid_aliasing_and_escaping_payloads() {
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let shared_u8_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U8_TY) };
    let mut_u8_ref = Ty::Ref { mutability: Mutability::Mut, pointee: Box::new(U8_TY) };
    let const_u8_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U8_TY) };
    let shared_str_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(Ty::Str) };

    // 1. `max_val_ptr_alloc_id`: a dangling `Some(*const u8)` carrying
    //    `alloc_id = 2` must advance `entry_memory_for_args_v2`'s
    //    `next_alloc_id` past `2` so a promoted callee stack local does not
    //    reuse `alloc_id = 2` and turn a dangling dereference into `Returned`.
    let raw_ptr_deref_prog = v2_program(
        1,
        vec![U8_TY, opt(const_u8_ptr.clone()), U8_TY, const_u8_ptr.clone(), const_u8_ptr.clone()],
        vec![
            Block {
                statements: vec![
                    Statement::StorageLive { local: 2 },
                    assign(
                        2,
                        Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U8_TY,
                                lit: ConstLit::Scalar { bits: 77 },
                            },
                            with_retag: false,
                        },
                    ),
                    assign(
                        3,
                        Rvalue::AddressOf {
                            mutability: Mutability::Shared,
                            place: Place { local: 2, projection: Vec::new() },
                        },
                    ),
                ],
                terminator: Terminator::CoreCall {
                    op: CoreCallOp::OptionUnwrap { inner: const_u8_ptr.clone() },
                    args: vec![copy(1)],
                    dst: Place { local: 4, projection: Vec::new() },
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
                cleanup: false,
            },
            ret_block(vec![assign(
                0,
                Rvalue::Use {
                    operand: Operand::CopyPlace {
                        place: Place { local: 4, projection: vec![ProjectionElem::Deref] },
                    },
                    with_retag: false,
                },
            )]),
        ],
    );
    let dangling_arg =
        some(Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize }));
    let dangling_fault = fault_detail(
        eval_body_with_caller_mem(
            &raw_ptr_deref_prog,
            0,
            &[dangling_arg],
            CallerMemory::default(),
            256,
            &cfg,
        )
        .outcome,
    );
    assert_eq!(dangling_fault.kind, FaultKind::Undefined);
    assert_eq!(dangling_fault.ub_class, Some(UbClass::DanglingOrUnknownAllocAccess));

    let max_id_arg = some(Val::Ptr(PtrVal {
        alloc_id: Some(u64::MAX),
        offset_bytes: 0,
        width: IntWidth::Isize,
    }));
    assert_eq!(
        fault_kind(
            eval_body_with_caller_mem(
                &raw_ptr_deref_prog,
                0,
                &[max_id_arg],
                CallerMemory::default(),
                256,
                &cfg,
            )
            .outcome
        ),
        FaultKind::Unsupported
    );

    // 2. `refs_valid_in_mem`: invalid reference inside entry `Some(&u8)` is UB.
    let accept_opt_ref =
        v2_program(1, vec![Ty::Unit, opt(shared_u8_ref.clone())], vec![ret_block(Vec::new())]);
    let null_ref =
        some(Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize }));
    let invalid_entry = fault_detail(run(&accept_opt_ref, &[null_ref]));
    assert_eq!(invalid_entry.kind, FaultKind::Undefined);
    assert_eq!(invalid_entry.ub_class, Some(UbClass::EntryInvalidRefArg));

    // 3. `collect_ref_access_spans`: two individually valid `Some(&mut u8)`
    //    entry arguments aliasing the same mutable caller byte are UB.
    let accept_two_mut_opts = v2_program(
        2,
        vec![Ty::Unit, opt(mut_u8_ref.clone()), opt(mut_u8_ref)],
        vec![ret_block(Vec::new())],
    );
    let mut_mem = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 0,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Init { byte: 5, prov: None }],
            live: true,
        }],
    };
    let valid_mut =
        some(Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize }));
    let overlap_fault = fault_detail(
        eval_body_with_caller_mem(
            &accept_two_mut_opts,
            0,
            &[valid_mut.clone(), valid_mut],
            mut_mem,
            256,
            &cfg,
        )
        .outcome,
    );
    assert_eq!(overlap_fault.kind, FaultKind::Undefined);
    assert_eq!(overlap_fault.ub_class, Some(UbClass::EntryInvalidRefArg));

    // 4. `collect_ptr_or_ref_alloc_ids` (`has_escaping_rodata_ptr`): returning
    //    `Some(&str)` backed by callee `.rodata` fails closed with
    //    `Unsupported` before `refs_stay_in_caller_mem` would classify it as
    //    `Undefined`; `has_escaping_rodata_ptr` also spots `Some(*const u8)`.
    let rodata_prog = v2_program(
        0,
        vec![opt(shared_str_ref.clone()), shared_str_ref.clone()],
        vec![ret_block(vec![
            assign(
                1,
                Rvalue::Use {
                    operand: Operand::Constant {
                        ty: shared_str_ref.clone(),
                        lit: ConstLit::RodataRef {
                            bytes: vec![
                                RodataByte::Init { byte: b'h' },
                                RodataByte::Init { byte: b'i' },
                            ],
                            align_log2: 0,
                            offset_bytes: 0,
                            slice_len: Some(2),
                        },
                    },
                    with_retag: false,
                },
            ),
            assign(
                0,
                Rvalue::AggregateOption {
                    variant_idx: 1,
                    inner_ty: shared_str_ref,
                    payload: Some(Box::new(copy(1))),
                },
            ),
        ])],
    );
    assert_eq!(fault_kind(run(&rodata_prog, &[])), FaultKind::Unsupported);

    let mut rodata_mem = MemoryState::entry_memory();
    let rodata_id =
        rodata_mem.try_allocate_rodata(vec![AllocByte::Init { byte: 1, prov: None }], 0).unwrap();
    let some_rodata_raw = some(Val::Ptr(PtrVal {
        alloc_id: Some(rodata_id),
        offset_bytes: 0,
        width: IntWidth::Isize,
    }));
    assert!(has_escaping_rodata_ptr(
        &CallerMemory::default(),
        &rodata_mem,
        &opt(const_u8_ptr),
        &some_rodata_raw,
    ));

    // 5. `refs_stay_in_caller_mem`: returning `Some(&local)` to a still-live
    //    initialized callee stack local is `Undefined` (`StackRefEscaped`).
    let escaping_stack_prog = v2_program(
        0,
        vec![opt(shared_u8_ref.clone()), U8_TY, shared_u8_ref.clone()],
        vec![ret_block(vec![
            assign(
                1,
                Rvalue::Use {
                    operand: Operand::Constant { ty: U8_TY, lit: ConstLit::Scalar { bits: 7 } },
                    with_retag: false,
                },
            ),
            assign(
                2,
                Rvalue::Ref {
                    mutability: Mutability::Shared,
                    place: Place { local: 1, projection: Vec::new() },
                },
            ),
            assign(
                0,
                Rvalue::AggregateOption {
                    variant_idx: 1,
                    inner_ty: shared_u8_ref,
                    payload: Some(Box::new(copy(2))),
                },
            ),
        ])],
    );
    let escaped = fault_detail(run(&escaping_stack_prog, &[]));
    assert_eq!(escaped.kind, FaultKind::Undefined);
    assert_eq!(escaped.ub_class, Some(UbClass::StackRefEscaped));
    assert_eq!(escaped.witness_class(), Some(WitnessClass::ReplayableMiriUb));
}

#[test]
fn probe_generates_none_and_some_candidates_for_option_parameters() {
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let probe_cfg = ProbeConfig { max_cases: 32, fuel: 256, seed: 1 };

    // A body that reads `(x as Some).0` without checking `Discriminant(x)`
    // faults on the `None` boundary candidate with `ReplayableMiriUb`.
    let unchecked_some_read = v2_program(
        1,
        vec![U8_TY, opt(U8_TY)],
        vec![ret_block(vec![assign(
            0,
            Rvalue::Use {
                operand: Operand::Copy { local: 1, projection: payload_proj(U8_TY) },
                with_retag: false,
            },
        )])],
    );
    let u8_report = probe_body(&unchecked_some_read, 0, &probe_cfg, &cfg);
    assert!(!u8_report.unsupported_param_shape);
    assert!(u8_report.cases_run >= 2);
    assert!(u8_report.returned_count >= 1);
    assert!(u8_report.replayable_ub_count >= 1);

    // Reference-carrying `Option<&[u8]>` parameter materializes valid caller
    // allocations for `Some` alongside `None`.
    let byte_slice_ref = Ty::Ref {
        mutability: Mutability::Shared,
        pointee: Box::new(Ty::Slice { elem: Box::new(U8_TY) }),
    };
    let discr_slice_opt = v2_program(
        1,
        vec![ISIZE_TY, opt(byte_slice_ref)],
        vec![ret_block(vec![assign(
            0,
            Rvalue::Discriminant { place: Place { local: 1, projection: Vec::new() } },
        )])],
    );
    let slice_report = probe_body(&discr_slice_opt, 0, &probe_cfg, &cfg);
    assert!(!slice_report.unsupported_param_shape);
    assert!(slice_report.cases_run >= 4);
    assert_eq!(slice_report.returned_count, slice_report.cases_run);
    assert_eq!(slice_report.undefined_count, 0);

    // `Option<&!>` is inhabited solely by `None` (not uninhabited).
    let never_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(Ty::Never) };
    let never_opt_prog = v2_program(1, vec![Ty::Unit, opt(never_ref)], vec![ret_block(Vec::new())]);
    let never_report = probe_body(&never_opt_prog, 0, &probe_cfg, &cfg);
    assert!(!never_report.unsupported_param_shape);
    assert!(!never_report.uninhabited_params);
    assert_eq!(never_report.cases_run, 1);
    assert_eq!(never_report.returned_count, 1);
}

#[test]
fn query_json_deserializes_documented_option_val_examples() {
    let raw = r#"{
      "args": [
        { "kind": "option_val", "value": null },
        {
          "kind": "option_val",
          "value": {
            "kind": "ptr",
            "value": { "alloc_id": 2, "offset_bytes": 0, "width": "isize" }
          }
        }
      ],
      "caller_mem": {
        "allocations": [
          {
            "alloc_id": 2,
            "align_log2": 0,
            "mutability": "shared",
            "bytes": [{ "kind": "init", "byte": 9, "prov": null }],
            "live": true
          }
        ]
      }
    }"#;
    let query: Query = serde_json::from_str(raw).unwrap();
    assert_eq!(query.args[0], NONE);
    let shared_u8_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U8_TY) };
    let prog = v2_program(
        2,
        vec![ISIZE_TY, opt(U8_TY), opt(shared_u8_ref)],
        vec![ret_block(vec![assign(
            0,
            Rvalue::Discriminant { place: Place { local: 2, projection: Vec::new() } },
        )])],
    );
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let trace = eval_body_with_caller_mem(&prog, 0, &query.args, query.caller_mem, 64, &cfg);
    assert_eq!(returned(trace.outcome), Val::isize_val(1));
}
