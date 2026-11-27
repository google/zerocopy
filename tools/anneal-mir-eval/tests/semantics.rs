// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Comprehensive unit and `Trusted.MirSemantics.CanaryFixtures` parity tests
//! for `anneal-mir-eval`.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use anneal_mir_eval::{
    AggregateKind, AllocByte, Allocation, AssertKind, BinOp, Block, Body, CallReturnTarget,
    CallerMemory, CaptureInput, CastKind, ConstLit, CoreCallOp, EnumTagRepr, EnumTy, EvalConfig,
    FaultDetail, FaultKind, FrameState, IntTy, IntWidth, LayoutData, LocalSlot, MachineState,
    Mutability, Operand, OrderingVal, Outcome, Place, ProbeConfig, Program, ProjectionElem, PtrVal,
    RodataByte, Rvalue, ScalarVal, Scope, Statement, StdlibCrate, StepOutcome, StepTrace,
    SysrootNumKind, SysrootNumOp, TargetEndian, TerminalOut, Terminator, Ty, UbClass, UnOp,
    UnwindAction, Val, WitnessClass, check_val, decode_val, encode_val, eval_body, eval_body_auto,
    eval_body_by_identity, eval_body_with_caller_mem, eval_body_with_config, layout_of_ty,
    load_indirect, memory, probe_body, probe_body_with_policy, store_indirect, validate_body_entry,
    validate_program_config,
};

const U8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
const I8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: true });
const U16_TY: Ty = Ty::Int(IntTy { width: IntWidth::I16, signed: false });
const U32_TY: Ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
const USIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
const ISIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: true });

fn single_unit_program(bodies: Vec<Body>) -> Program {
    let mut roots = BTreeSet::new();
    roots.insert("test::entry".into());
    Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        bodies,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 1,
        overflow_checks: false,
    }
}

fn mk_binop_prog(op: BinOp, ret_ty: Ty, lhs_ty: Ty, rhs_ty: Ty) -> Program {
    single_unit_program(vec![Body {
        arg_count: 2,
        is_unsafe: false,
        local_tys: vec![ret_ty, lhs_ty, rhs_ty],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Binary {
                    op,
                    left: Operand::Copy { local: 1, projection: Vec::new() },
                    right: Operand::Copy { local: 2, projection: Vec::new() },
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::binop".into(),
    }])
}

fn mk_unop_prog(op: UnOp, ty: Ty) -> Program {
    single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![ty.clone(), ty],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Unary {
                    op,
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::unop".into(),
    }])
}

fn assert_returned(trace: &anneal_mir_eval::StepTrace, expected: Val) {
    match &trace.outcome {
        Outcome::Returned(TerminalOut::Returned { ret, .. }) => {
            assert_eq!(*ret, expected, "unexpected return value in trace: {trace:?}");
        }
        other => panic!("expected Returned({expected:?}), got {other:?}"),
    }
}

fn assert_fault(trace: &anneal_mir_eval::StepTrace, expected: FaultKind) {
    match &trace.outcome {
        Outcome::Fault(detail) => {
            assert_eq!(detail.kind, expected, "unexpected fault kind: {detail:?}");
        }
        other => panic!("expected Fault({expected:?}), got {other:?}"),
    }
}

fn canary_repr_u8_enum() -> EnumTy {
    EnumTy {
        id: 1,
        discr_width: IntWidth::I8,
        discr_signed: false,
        tag_repr: EnumTagRepr::Scalar(IntTy { width: IntWidth::I8, signed: false }),
        discriminants: vec![10, 20],
    }
}

fn canary_signed_tag_enum() -> EnumTy {
    EnumTy {
        id: 2,
        discr_width: IntWidth::Isize,
        discr_signed: true,
        tag_repr: EnumTagRepr::Scalar(IntTy { width: IntWidth::I8, signed: true }),
        discriminants: vec![u64::MAX as u128, 1],
    }
}

fn canary_single_zst_enum() -> EnumTy {
    EnumTy {
        id: 3,
        discr_width: IntWidth::Isize,
        discr_signed: true,
        tag_repr: EnumTagRepr::ZeroSized,
        discriminants: vec![42],
    }
}

#[test]
fn canary_d1_d2_basic_and_unit() {
    let add_prog = mk_binop_prog(BinOp::Add, U32_TY, U32_TY, U32_TY);
    assert_returned(&eval_body(&add_prog, 0, &[Val::u32(30), Val::u32(12)], 64), Val::u32(42));

    let empty_unit = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
        identity: "test::empty_unit".into(),
    }]);
    assert_returned(&eval_body(&empty_unit, 0, &[], 64), Val::Unit);
}

#[test]
fn canary_stmts_and_control_flow() {
    let prog = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, U32_TY, U32_TY],
        blocks: vec![
            Block {
                statements: vec![
                    Statement::Nop,
                    Statement::StorageLive { local: 2 },
                    Statement::StorageDead { local: 2 },
                    Statement::StorageLive { local: 2 },
                    Statement::Assign {
                        local: 2,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 1, projection: Vec::new() },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Goto { block: 1 },
                cleanup: false,
            },
            Block {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    operand: Operand::Move { local: 2, projection: Vec::new() },
                    targets: vec![(10, 2)],
                    otherwise: 3,
                },
                cleanup: false,
            },
            Block {
                statements: vec![
                    Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 100 },
                            },
                            with_retag: false,
                        },
                    },
                    Statement::StorageDead { local: 2 },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            },
            Block {
                statements: vec![
                    Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 200 },
                            },
                            with_retag: false,
                        },
                    },
                    Statement::StorageDead { local: 2 },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            },
        ],
        identity: "test::stmts_and_cf".into(),
    }]);

    assert_returned(&eval_body(&prog, 0, &[Val::u32(10)], 64), Val::u32(100));
    assert_returned(&eval_body(&prog, 0, &[Val::u32(99)], 64), Val::u32(200));
}

#[test]
fn canary_all_int_width_wrapping_boundaries() {
    let widths = [
        IntWidth::I8,
        IntWidth::I16,
        IntWidth::I32,
        IntWidth::I64,
        IntWidth::I128,
        IntWidth::Isize,
    ];
    for w in widths {
        let u_ty = Ty::Int(IntTy { width: w, signed: false });
        let s_ty = Ty::Int(IntTy { width: w, signed: true });
        let u_max = w.mask();
        let s_min_bits = 1u128 << (w.bits() - 1);
        let s_max_bits = s_min_bits - 1;

        let u_prog = mk_binop_prog(BinOp::Add, u_ty.clone(), u_ty.clone(), u_ty);
        assert_returned(
            &eval_body(
                &u_prog,
                0,
                &[
                    Val::Scalar(ScalarVal::new(w, false, u_max)),
                    Val::Scalar(ScalarVal::new(w, false, 1)),
                ],
                32,
            ),
            Val::Scalar(ScalarVal::new(w, false, 0)),
        );

        let s_prog = mk_binop_prog(BinOp::Add, s_ty.clone(), s_ty.clone(), s_ty);
        assert_returned(
            &eval_body(
                &s_prog,
                0,
                &[
                    Val::Scalar(ScalarVal::new(w, true, s_max_bits)),
                    Val::Scalar(ScalarVal::new(w, true, 1)),
                ],
                32,
            ),
            Val::Scalar(ScalarVal::new(w, true, s_min_bits)),
        );
    }
}

#[test]
fn canary_arithmetic_overflow_div_rem_and_shift_ub() {
    let div_zero = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, U32_TY],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Binary {
                    op: BinOp::Div,
                    left: Operand::Copy { local: 1, projection: Vec::new() },
                    right: Operand::Constant { ty: U32_TY, lit: ConstLit::Scalar { bits: 0 } },
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::div_zero".into(),
    }]);
    assert_fault(&eval_body(&div_zero, 0, &[Val::u32(10)], 32), FaultKind::Undefined);

    let rem_overflow = mk_binop_prog(BinOp::Rem, I8_TY, I8_TY, I8_TY);
    assert_fault(
        &eval_body(&rem_overflow, 0, &[Val::i8(-128), Val::i8(-1)], 32),
        FaultKind::Undefined,
    );
    assert_returned(&eval_body(&rem_overflow, 0, &[Val::i8(-7), Val::i8(3)], 32), Val::i8(-1));

    let add_unchecked = mk_binop_prog(BinOp::AddUnchecked, U32_TY, U32_TY, U32_TY);
    assert_fault(
        &eval_body(&add_unchecked, 0, &[Val::u32(u32::MAX), Val::u32(1)], 32),
        FaultKind::Undefined,
    );

    let shl_wrapped = mk_binop_prog(BinOp::Shl, U32_TY, U32_TY, I8_TY);
    assert_returned(
        &eval_body(&shl_wrapped, 0, &[Val::u32(1), Val::i8(-1)], 32),
        Val::u32(0x8000_0000),
    );

    let shr_unchecked = mk_binop_prog(BinOp::ShrUnchecked, I8_TY, I8_TY, I8_TY);
    assert_returned(&eval_body(&shr_unchecked, 0, &[Val::i8(-4), Val::i8(1)], 32), Val::i8(-2));
    assert_fault(
        &eval_body(&shr_unchecked, 0, &[Val::i8(-4), Val::i8(-1)], 32),
        FaultKind::Undefined,
    );
    assert_fault(
        &eval_body(&shr_unchecked, 0, &[Val::i8(-4), Val::i8(8)], 32),
        FaultKind::Undefined,
    );

    let add_ovf = mk_binop_prog(
        BinOp::AddWithOverflow,
        Ty::OverflowPair(IntTy { width: IntWidth::I8, signed: false }),
        U8_TY,
        U8_TY,
    );
    assert_returned(
        &eval_body(&add_ovf, 0, &[Val::u8(200), Val::u8(100)], 32),
        Val::overflow_pair(ScalarVal::new(IntWidth::I8, false, 44), true),
    );
}

#[test]
fn canary_unop_casts_cmp_and_chars() {
    let not_u8 = mk_unop_prog(UnOp::Not, U8_TY);
    assert_returned(&eval_body(&not_u8, 0, &[Val::u8(0x0f)], 32), Val::u8(0xf0));

    let neg_i8 = mk_unop_prog(UnOp::Neg, I8_TY);
    assert_returned(&eval_body(&neg_i8, 0, &[Val::i8(-128)], 32), Val::i8(-128));

    let neg_u8 = mk_unop_prog(UnOp::Neg, U8_TY);
    assert_fault(&eval_body(&neg_u8, 0, &[Val::u8(1)], 32), FaultKind::Unsupported);

    // Sign-extending i8 -> u32 cast
    let cast_prog = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, I8_TY],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    ty: U32_TY,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::cast_i8_u32".into(),
    }]);
    assert_returned(&eval_body(&cast_prog, 0, &[Val::i8(-1)], 32), Val::u32(u32::MAX));

    // u8 as char succeeds, u16 as char faults Unsupported
    let u8_to_char = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![Ty::Char, U8_TY],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    ty: Ty::Char,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::u8_to_char".into(),
    }]);
    assert_returned(&eval_body(&u8_to_char, 0, &[Val::u8(65)], 32), Val::Char('A'));

    let u16_to_char = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![Ty::Char, U16_TY],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    ty: Ty::Char,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::u16_to_char".into(),
    }]);
    assert_fault(&eval_body(&u16_to_char, 0, &[Val::u16(256)], 32), FaultKind::Unsupported);

    // Cmp + Ordering discriminant
    let cmp_prog = single_unit_program(vec![Body {
        arg_count: 2,
        is_unsafe: false,
        local_tys: vec![I8_TY, U32_TY, U32_TY, Ty::Ordering],
        blocks: vec![Block {
            statements: vec![
                Statement::Assign {
                    local: 3,
                    projection: Vec::new(),
                    value: Rvalue::Binary {
                        op: BinOp::Cmp,
                        left: Operand::Copy { local: 1, projection: Vec::new() },
                        right: Operand::Copy { local: 2, projection: Vec::new() },
                    },
                },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Discriminant { place: Place::local(3) },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::cmp_discr".into(),
    }]);
    assert_returned(&eval_body(&cmp_prog, 0, &[Val::u32(1), Val::u32(2)], 32), Val::i8(-1));
    assert_returned(&eval_body(&cmp_prog, 0, &[Val::u32(2), Val::u32(2)], 32), Val::i8(0));
    assert_returned(&eval_body(&cmp_prog, 0, &[Val::u32(3), Val::u32(2)], 32), Val::i8(1));

    // Invalid char constant + invalid char switch case
    let invalid_char_const = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Char],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Use {
                    operand: Operand::Constant {
                        ty: Ty::Char,
                        lit: ConstLit::Scalar { bits: 0xd800 },
                    },
                    with_retag: false,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::invalid_char_const".into(),
    }]);
    assert_fault(&eval_body(&invalid_char_const, 0, &[], 32), FaultKind::Undefined);
}

#[test]
fn canary_enums_storage_unreachable_and_unsupported() {
    let repr_u8 = canary_repr_u8_enum();
    let enum_u8 = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![U8_TY, Ty::Enum(repr_u8.clone())],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::Assign {
                    local: 1,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: Ty::Enum(repr_u8.clone()),
                            lit: ConstLit::Scalar { bits: 20 },
                        },
                        with_retag: false,
                    },
                },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Discriminant { place: Place::local(1) },
                },
                Statement::StorageDead { local: 1 },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::enum_repr_u8".into(),
    }]);
    assert_returned(&eval_body(&enum_u8, 0, &[], 32), Val::u8(20));

    let signed_enum = canary_signed_tag_enum();
    let enum_signed = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![ISIZE_TY, Ty::Enum(signed_enum.clone())],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::Assign {
                    local: 1,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: Ty::Enum(signed_enum),
                            lit: ConstLit::Scalar { bits: 255 },
                        },
                        with_retag: false,
                    },
                },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Discriminant { place: Place::local(1) },
                },
                Statement::StorageDead { local: 1 },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::enum_signed".into(),
    }]);
    assert_returned(&eval_body(&enum_signed, 0, &[], 32), Val::isize_val(-1));

    let single_zst = canary_single_zst_enum();
    let zst_ret = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Enum(single_zst.clone())],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
        identity: "test::zst_enum_ret".into(),
    }]);
    assert_returned(&eval_body(&zst_ret, 0, &[], 32), Val::EnumVal { ty: single_zst, variant: 0 });

    let invalid_tag = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![U8_TY, Ty::Enum(repr_u8.clone())],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::Assign {
                    local: 1,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: Ty::Enum(repr_u8.clone()),
                            lit: ConstLit::Scalar { bits: 1 },
                        },
                        with_retag: false,
                    },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::invalid_tag".into(),
    }]);
    assert_fault(&eval_body(&invalid_tag, 0, &[], 32), FaultKind::Undefined);

    let uninit_discr = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![U8_TY, Ty::Enum(repr_u8)],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Discriminant { place: Place::local(1) },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::uninit_discr".into(),
    }]);
    assert_fault(&eval_body(&uninit_discr, 0, &[], 32), FaultKind::Undefined);

    let storage_dead_ret = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block {
            statements: vec![Statement::StorageDead { local: 0 }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::dead_ret_place".into(),
    }]);
    assert_fault(&eval_body(&storage_dead_ret, 0, &[], 32), FaultKind::Unsupported);

    let unreachable = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block {
            statements: vec![],
            terminator: Terminator::Unreachable,
            cleanup: false,
        }],
        identity: "test::unreachable".into(),
    }]);
    assert_fault(&eval_body(&unreachable, 0, &[], 32), FaultKind::Undefined);

    let unsupported_stmt = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block {
            statements: vec![Statement::Unsupported],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::unsupported_stmt".into(),
    }]);
    assert_fault(&eval_body(&unsupported_stmt, 0, &[], 32), FaultKind::Unsupported);
}

#[test]
fn canary_memory_lifecycle_and_force_allocation() {
    let prog = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, U32_TY, U32_TY],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 2 },
                Statement::Assign {
                    local: 2,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1, projection: Vec::new() },
                        with_retag: false,
                    },
                },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 2, projection: Vec::new() },
                        with_retag: false,
                    },
                },
                Statement::StorageDead { local: 2 },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::mem_lifecycle".into(),
    }]);

    let cfg = EvalConfig::profile_v1();
    let mut state = MachineState::init(&prog, 0, &[Val::u32(0x0102_0304)], &cfg).unwrap();
    // Step 0: StorageLive(2)
    assert!(matches!(state.step(&prog, &cfg), anneal_mir_eval::StepOutcome::Stepped { .. }));
    // Force _2 to stack memory -> alloc_id == 2
    let mplace = state.force_allocation(&prog, 2, &cfg).unwrap();
    assert_eq!(mplace.alloc_id, 2);
    // Step 1: _2 = copy _1
    assert!(matches!(state.step(&prog, &cfg), anneal_mir_eval::StepOutcome::Stepped { .. }));
    // Check Profile v1 big-endian byte layout [1, 2, 3, 4]
    let alloc = state.mem.allocations.iter().find(|a| a.alloc_id == 2).unwrap();
    assert!(alloc.live);
    assert_eq!(
        alloc.bytes,
        vec![
            AllocByte::Init { byte: 1, prov: None },
            AllocByte::Init { byte: 2, prov: None },
            AllocByte::Init { byte: 3, prov: None },
            AllocByte::Init { byte: 4, prov: None },
        ]
    );
    // Step 2: _0 = copy _2; Step 3: StorageDead(2) -> alloc dead; Step 4: Ret
    assert!(matches!(state.step(&prog, &cfg), anneal_mir_eval::StepOutcome::Stepped { .. }));
    assert!(matches!(state.step(&prog, &cfg), anneal_mir_eval::StepOutcome::Stepped { .. }));
    assert!(!state.mem.allocations.iter().find(|a| a.alloc_id == 2).unwrap().live);
    match state.step(&prog, &cfg) {
        anneal_mir_eval::StepOutcome::Done(TerminalOut::Returned { ret, .. }) => {
            assert_eq!(ret, Val::u32(0x0102_0304));
        }
        other => panic!("expected Done(0x0102_0304), got {other:?}"),
    }

    // Indirect ill-typed Use fails with Unsupported (type check before indirect load)
    let ill_typed = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![U32_TY, Ty::Bool],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1, projection: Vec::new() },
                        with_retag: false,
                    },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::ill_typed_indirect".into(),
    }]);
    let mut ill_state = MachineState::init(&ill_typed, 0, &[], &cfg).unwrap();
    let _ = ill_state.step(&ill_typed, &cfg);
    ill_state.force_allocation(&ill_typed, 1, &cfg).unwrap();
    match ill_state.step(&ill_typed, &cfg) {
        anneal_mir_eval::StepOutcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported),
        other => panic!("expected Fault(Unsupported), got {other:?}"),
    }
}

#[test]
fn fuel_limit_and_json_roundtrip_edge_cases() {
    let infinite_loop = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block {
            statements: vec![],
            terminator: Terminator::Goto { block: 0 },
            cleanup: false,
        }],
        identity: "test::infinite".into(),
    }]);
    let trace = eval_body(&infinite_loop, 0, &[], 5);
    assert_eq!(trace.steps_executed, 5);
    assert_eq!(trace.outcome, Outcome::OutOfFuel);

    let max_u128_json = r#"{
        "scope": { "kind": "crate" },
        "pointer_width_bits": 64,
        "mir_profile_version": 1,
        "bodies": [{
            "arg_count": 0,
            "is_unsafe": false,
            "identity": "test::max_u128",
            "local_tys": [{ "kind": "int", "width": "i128", "signed": false }],
            "blocks": [{
                "statements": [{
                    "kind": "assign",
                    "local": 0,
                    "value": {
                        "kind": "use",
                        "operand": {
                            "kind": "constant",
                            "ty": { "kind": "int", "width": "i128", "signed": false },
                            "lit": { "kind": "scalar", "bits": "340282366920938463463374607431768211455" }
                        },
                        "with_retag": false
                    }
                }],
                "terminator": { "kind": "ret" }
            }]
        }]
    }"#;
    let parsed = CaptureInput::from_json_str(max_u128_json).unwrap().into_program();
    assert_returned(
        &eval_body_by_identity(&parsed, "test::max_u128", &[], 32).unwrap(),
        Val::u128(u128::MAX),
    );

    // Incomplete standalone program JSON missing required version/width fields fails closed.
    let incomplete_json = r#"{ "scope": { "kind": "crate" }, "bodies": [] }"#;
    assert!(CaptureInput::from_json_str(incomplete_json).is_err());

    // Schema v5 manifest round-trip and rejection of unsupported schema_version
    // and overflow_checks mismatches.
    let h = "c".repeat(64);
    let manifest_json = format!(
        r#"{{
            "schema_version": 5,
            "compiler": {{
                "commit": "0123456789abcdef",
                "version": "1.100.0",
                "sysroot": "/sysroot",
                "rustc_sha256": "{h}",
                "driver": {{
                    "linkage": "static_exe",
                    "driver_sha256": "{h}",
                    "dso_digests": {{}}
                }}
            }},
            "configuration": {{
                "crate_root": "src/lib.rs",
                "crate_name": "demo",
                "crate_type": "bin",
                "panic": "abort",
                "edition": "2024",
                "target": "aarch64-unknown-none",
                "cfg": [],
                "env": {{}},
                "opt_level": 2,
                "debug_assertions": false,
                "overflow_checks": true,
                "mir_preserve_ub": true,
                "pointer_bits": 64,
                "endian": "little",
                "stdlib_crate": "core",
                "declared_source_files": ["src/lib.rs"]
            }},
            "source_files": [],
            "census": [],
            "selected": [],
            "unsupported": [],
            "program": {{
                "scope": {{ "kind": "crate" }},
                "overflow_checks": true,
                "bodies": [{{
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "test::manifest_unit",
                    "local_tys": [{{ "kind": "unit" }}],
                    "blocks": [{{ "statements": [], "terminator": {{ "kind": "ret" }} }}]
                }}]
            }}
        }}"#
    );
    let parsed_manifest = CaptureInput::from_json_str(&manifest_json).unwrap();
    let m = parsed_manifest.manifest().unwrap();
    assert_eq!(m.configuration.endian, "little");
    assert_eq!(m.configuration.stdlib_crate, Some(StdlibCrate::Core));
    assert!(m.configuration.overflow_checks);
    let manifest_prog = parsed_manifest.into_program();
    assert_eq!(manifest_prog.pointer_width_bits, 64);
    assert!(manifest_prog.overflow_checks);
    assert_returned(&eval_body(&manifest_prog, 0, &[], 16), Val::Unit);

    let bad_manifest_v4 = manifest_json.replace("\"schema_version\": 5", "\"schema_version\": 4");
    assert!(CaptureInput::from_json_str(&bad_manifest_v4).is_err());
    let bad_manifest_v6 = manifest_json.replace("\"schema_version\": 5", "\"schema_version\": 6");
    assert!(CaptureInput::from_json_str(&bad_manifest_v6).is_err());
    let bad_ovf =
        manifest_json.replacen("\"overflow_checks\": true", "\"overflow_checks\": false", 1);
    let ovf_err = CaptureInput::from_json_str(&bad_ovf).unwrap_err();
    assert!(ovf_err.contains("overflow_checks mismatch"), "{ovf_err}");
}

#[test]
fn profile_v1_intra_crate_calls_and_sysroot_num_ops() {
    let mut roots = BTreeSet::new();
    roots.insert("test::caller".into());
    let ovf_ty = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
    let prog = Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 1,
        overflow_checks: false,
        bodies: vec![
            // Body 0: calls safe `checked_inc(_1, 1)` returning `(u32, bool)`.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![ovf_ty.clone(), U32_TY],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::Call {
                            callee: 1,
                            args: vec![
                                Operand::Copy { local: 1, projection: Vec::new() },
                                Operand::Constant { ty: U32_TY, lit: ConstLit::Scalar { bits: 1 } },
                            ],
                            dst_local: 0,
                            dst_projection: Vec::new(),
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                ],
                identity: "test::caller".into(),
            },
            // Body 1: safe callee performing AddWithOverflow.
            Body {
                arg_count: 2,
                is_unsafe: false,
                local_tys: vec![ovf_ty, U32_TY, U32_TY],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Binary {
                            op: BinOp::AddWithOverflow,
                            left: Operand::Copy { local: 1, projection: Vec::new() },
                            right: Operand::Copy { local: 2, projection: Vec::new() },
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::checked_inc".into(),
            },
        ],
    };

    assert_returned(
        &eval_body(&prog, 0, &[Val::u32(41)], 64),
        Val::overflow_pair(ScalarVal::new(IntWidth::I32, false, 42), false),
    );
    assert_returned(
        &eval_body(&prog, 0, &[Val::u32(u32::MAX)], 64),
        Val::overflow_pair(ScalarVal::new(IntWidth::I32, false, 0), true),
    );

    // Profile v1 refuses intra-crate `Call` to an `unsafe fn` callee.
    let mut unsafe_callee_prog = prog.clone();
    unsafe_callee_prog.bodies[1].is_unsafe = true;
    assert_fault(&eval_body(&unsafe_callee_prog, 0, &[Val::u32(1)], 64), FaultKind::Unsupported);

    // Profile v1 refuses `Call` whose `Move` operand aliases `dst`
    // (`moveDefinitelyDisjoint`).
    let aliasing_move = single_unit_program(vec![
        Body {
            arg_count: 1,
            is_unsafe: false,
            local_tys: vec![U32_TY, U32_TY],
            blocks: vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::Call {
                        callee: 1,
                        args: vec![Operand::Move { local: 1, projection: Vec::new() }],
                        dst_local: 1,
                        dst_projection: Vec::new(),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 1, projection: Vec::new() },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                },
            ],
            identity: "test::alias_caller".into(),
        },
        Body {
            arg_count: 1,
            is_unsafe: false,
            local_tys: vec![U32_TY, U32_TY],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1, projection: Vec::new() },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            identity: "test::id_u32".into(),
        },
    ]);
    assert_fault(&eval_body(&aliasing_move, 0, &[Val::u32(7)], 64), FaultKind::Unsupported);

    // Profile v1 refuses `UnwindAction::Cleanup` on calls.
    let mut cleanup_call = prog.clone();
    if let Terminator::Call { unwind, .. } = &mut cleanup_call.bodies[0].blocks[0].terminator {
        *unwind = UnwindAction::Cleanup { block: 2 };
    }
    assert_fault(&eval_body(&cleanup_call, 0, &[Val::u32(1)], 64), FaultKind::Unsupported);

    // Diverging call (`target: None`) that returns faults
    // `Undefined(DivergingCallReturned)`.
    let diverging_return = single_unit_program(vec![
        Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit],
            blocks: vec![Block {
                statements: vec![],
                terminator: Terminator::Call {
                    callee: 1,
                    args: vec![],
                    dst_local: 0,
                    dst_projection: Vec::new(),
                    target: None,
                    unwind: UnwindAction::Continue,
                },
                cleanup: false,
            }],
            identity: "test::diverging_caller".into(),
        },
        Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit],
            blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
            identity: "test::unit_callee".into(),
        },
    ]);
    let div_trace = eval_body(&diverging_return, 0, &[], 64);
    match &div_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::DivergingCallReturned));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("expected Undefined(DivergingCallReturned), got {other:?}"),
    }

    // Deep recursion beyond 256 frames succeeds when fuel suffices, and
    // diverging recursion terminates with `Outcome::OutOfFuel` (matching
    // `Trusted.MirSemantics.evalCallTerminator` with no artificial depth cap).
    let countdown_prog = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, U32_TY, U32_TY],
        blocks: vec![
            Block {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    targets: vec![(0, 1)],
                    otherwise: 2,
                },
                cleanup: false,
            },
            Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: U32_TY,
                            lit: ConstLit::Scalar { bits: 0 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            },
            Block {
                statements: vec![Statement::Assign {
                    local: 2,
                    projection: Vec::new(),
                    value: Rvalue::Binary {
                        op: BinOp::Sub,
                        left: Operand::Copy { local: 1, projection: Vec::new() },
                        right: Operand::Constant { ty: U32_TY, lit: ConstLit::Scalar { bits: 1 } },
                    },
                }],
                terminator: Terminator::Call {
                    callee: 0,
                    args: vec![Operand::Copy { local: 2, projection: Vec::new() }],
                    dst_local: 0,
                    dst_projection: Vec::new(),
                    target: Some(3),
                    unwind: UnwindAction::Continue,
                },
                cleanup: false,
            },
            Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
        ],
        identity: "test::countdown".into(),
    }]);
    assert_returned(&eval_body(&countdown_prog, 0, &[Val::u32(256)], 100_000), Val::u32(0));

    let diverge_prog = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![
            Block {
                statements: vec![],
                terminator: Terminator::Call {
                    callee: 0,
                    args: vec![],
                    dst_local: 0,
                    dst_projection: Vec::new(),
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
                cleanup: false,
            },
            Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
        ],
        identity: "test::diverge".into(),
    }]);
    let div_fuel = eval_body(&diverge_prog, 0, &[], 600);
    assert_eq!(div_fuel.outcome, Outcome::OutOfFuel);
    assert_eq!(div_fuel.steps_executed, 600);

    // All 6 pinned `SysrootCall` ops (`Unchecked{Add,Sub,Mul}` and
    // `Wrapping{Add,Sub,Mul}`).
    let mk_sysroot = |kind: SysrootNumKind, signed: bool| {
        let ity = IntTy { width: IntWidth::I8, signed };
        let ty = Ty::Int(ity);
        single_unit_program(vec![Body {
            arg_count: 2,
            is_unsafe: false,
            local_tys: vec![ty.clone(), ty.clone(), ty],
            blocks: vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::SysrootCall {
                        op: SysrootNumOp { kind, ty: ity },
                        args: vec![
                            Operand::Copy { local: 1, projection: Vec::new() },
                            Operand::Copy { local: 2, projection: Vec::new() },
                        ],
                        dst_local: 0,
                        dst_projection: Vec::new(),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
            ],
            identity: "test::sysroot_op".into(),
        }])
    };
    let uadd = mk_sysroot(SysrootNumKind::UncheckedAdd, false);
    assert_returned(&eval_body(&uadd, 0, &[Val::u8(200), Val::u8(55)], 32), Val::u8(255));
    let uadd_ub = eval_body(&uadd, 0, &[Val::u8(200), Val::u8(56)], 32);
    match &uadd_ub.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::UncheckedArithOverflow));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected UncheckedArithOverflow, got {other:?}"),
    }
    let usub = mk_sysroot(SysrootNumKind::UncheckedSub, false);
    assert_returned(&eval_body(&usub, 0, &[Val::u8(10), Val::u8(4)], 32), Val::u8(6));
    assert_fault(&eval_body(&usub, 0, &[Val::u8(4), Val::u8(10)], 32), FaultKind::Undefined);
    let umul = mk_sysroot(SysrootNumKind::UncheckedMul, true);
    assert_returned(&eval_body(&umul, 0, &[Val::i8(-10), Val::i8(12)], 32), Val::i8(-120));
    assert_fault(&eval_body(&umul, 0, &[Val::i8(20), Val::i8(10)], 32), FaultKind::Undefined);
    let wadd = mk_sysroot(SysrootNumKind::WrappingAdd, false);
    assert_returned(&eval_body(&wadd, 0, &[Val::u8(250), Val::u8(10)], 32), Val::u8(4));
    let wsub = mk_sysroot(SysrootNumKind::WrappingSub, false);
    assert_returned(&eval_body(&wsub, 0, &[Val::u8(2), Val::u8(5)], 32), Val::u8(253));
    let wmul = mk_sysroot(SysrootNumKind::WrappingMul, false);
    assert_returned(&eval_body(&wmul, 0, &[Val::u8(16), Val::u8(17)], 32), Val::u8(16));
}

#[test]
fn counterexample_prober_finds_ub_and_validates_safe_fn() {
    let unsafe_guarded = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: true,
        local_tys: vec![U32_TY, Ty::Bool],
        blocks: vec![
            Block {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
                cleanup: false,
            },
            Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: U32_TY,
                            lit: ConstLit::Scalar { bits: 42 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            },
            Block { statements: vec![], terminator: Terminator::Unreachable, cleanup: false },
        ],
        identity: "canary::unsafe_guarded".into(),
    }]);

    let report = probe_body(
        &unsafe_guarded,
        0,
        &ProbeConfig { max_cases: 16, fuel: 100, seed: 1 },
        &EvalConfig::profile_v1(),
    );
    assert_eq!(report.undefined_count, 1);
    assert_eq!(report.returned_count, 1);
    assert_eq!(report.first_undefined.unwrap().args, vec![Val::Bool(false)]);

    let safe_add = mk_binop_prog(BinOp::Add, U32_TY, U32_TY, U32_TY);
    let safe_report = probe_body(&safe_add, 0, &ProbeConfig::default(), &EvalConfig::profile_v1());
    assert_eq!(safe_report.undefined_count, 0);
    assert_eq!(safe_report.unsupported_count, 0);
    assert_eq!(safe_report.cases_run, 256);

    // Ensure every Val & Outcome variant round-trips cleanly through serde_json,
    // including lossless decimal encoding of u128::MAX.
    let ety = canary_repr_u8_enum();
    let sample_vals = vec![
        Val::u128(u128::MAX),
        Val::Ptr(PtrVal { alloc_id: Some(7), offset_bytes: 16, width: IntWidth::Isize }),
        Val::Bool(true),
        Val::Char('Z'),
        Val::Ordering(OrderingVal::Less),
        Val::Unit,
        Val::EnumVal { ty: ety, variant: 1 },
        Val::overflow_pair(ScalarVal::new(IntWidth::I64, false, u64::MAX as u128), true),
        Val::Bytes(vec![AllocByte::Uninit, AllocByte::Init { byte: 0xab, prov: Some(2) }]),
    ];
    for val in sample_vals {
        let encoded = serde_json::to_string(&val).unwrap();
        let decoded: Val = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded, val);
    }
    let max_scalar_json = serde_json::to_string(&Val::u128(u128::MAX)).unwrap();
    assert!(max_scalar_json.contains("\"340282366920938463463374607431768211455\""));

    let outcomes = vec![
        Outcome::Returned(TerminalOut::Returned {
            ret: Val::Bool(false),
            caller_mem: CallerMemory::default(),
        }),
        Outcome::Returned(TerminalOut::Unwound { caller_mem: CallerMemory::default() }),
        Outcome::Fault(FaultDetail::undefined("sample ub")),
        Outcome::Fault(FaultDetail::unsupported("sample unsup")),
        Outcome::OutOfFuel,
    ];
    for (idx, outcome) in outcomes.into_iter().enumerate() {
        let trace = StepTrace {
            body_id: idx,
            identity: "test::rt".into(),
            steps_executed: 1,
            fuel_limit: 16,
            outcome,
            events: Vec::new(),
            final_state: None,
        };
        let encoded = serde_json::to_string(&trace).unwrap();
        let decoded: StepTrace = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded.outcome, trace.outcome);
    }
}

#[test]
fn canary_switch_int_place_mention_cleanup_and_indirect_move() {
    // 1. PlaceMention on an in-bounds sized (even dead) local is a no-op;
    //    Cleanup block Return is Unsupported.
    let place_mention = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit, U32_TY],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::StorageDead { local: 1 },
                Statement::PlaceMention { local: 1, projection: Vec::new() },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::place_mention".into(),
    }]);
    assert_returned(&eval_body(&place_mention, 0, &[], 32), Val::Unit);

    let cleanup_ret = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: true }],
        identity: "test::cleanup_ret".into(),
    }]);
    assert_fault(&eval_body(&cleanup_ret, 0, &[], 32), FaultKind::Unsupported);

    // 2. Bool SwitchInt edge cases (2 -> Undefined, 256 -> Unsupported)
    let bool_sw_ub = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, Ty::Bool],
        blocks: vec![
            Block {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    targets: vec![(2, 1)],
                    otherwise: 1,
                },
                cleanup: false,
            },
            Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: U32_TY,
                            lit: ConstLit::Scalar { bits: 0 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            },
        ],
        identity: "test::bool_sw_ub".into(),
    }]);
    assert_fault(&eval_body(&bool_sw_ub, 0, &[Val::Bool(true)], 32), FaultKind::Undefined);

    // 3. OverflowPair SwitchInt empty -> otherwise, non-empty -> Unsupported
    let ovf_ty = Ty::OverflowPair(IntTy { width: IntWidth::I8, signed: false });
    let ovf_sw_empty = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, ovf_ty],
        blocks: vec![
            Block {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    targets: vec![],
                    otherwise: 1,
                },
                cleanup: false,
            },
            Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: U32_TY,
                            lit: ConstLit::Scalar { bits: 77 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            },
        ],
        identity: "test::ovf_sw".into(),
    }]);
    assert_returned(
        &eval_body(
            &ovf_sw_empty,
            0,
            &[Val::overflow_pair(ScalarVal::new(IntWidth::I8, false, 1), false)],
            32,
        ),
        Val::u32(77),
    );

    // 4. Indirect Move + StorageLive(1) + Indirect _0 return (`progMemIndirectOps`)
    let indirect_ops = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![U32_TY, U32_TY],
        blocks: vec![Block {
            statements: vec![
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Move { local: 1, projection: Vec::new() },
                        with_retag: false,
                    },
                },
                Statement::StorageLive { local: 1 },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::indirect_ops".into(),
    }]);
    let cfg = EvalConfig::profile_v1();
    let mut state = MachineState::init(&indirect_ops, 0, &[Val::u32(0xDEAD_BEEF)], &cfg).unwrap();
    let p0 = state.force_allocation(&indirect_ops, 0, &cfg).unwrap();
    let p1 = state.force_allocation(&indirect_ops, 1, &cfg).unwrap();
    assert_eq!(p0.alloc_id, 2);
    assert_eq!(p1.alloc_id, 3);
    assert!(matches!(
        state.step(&indirect_ops, &cfg),
        anneal_mir_eval::StepOutcome::Stepped { .. }
    ));
    // Move deinitialized `_1`'s stack bytes to Uninit
    let alloc1 = state.mem.allocations.iter().find(|a| a.alloc_id == p1.alloc_id).unwrap();
    assert!(alloc1.live);
    assert!(alloc1.bytes.iter().all(|b| matches!(b, AllocByte::Uninit)));
    // StorageLive(1) deallocates old allocation `p1`
    assert!(matches!(
        state.step(&indirect_ops, &cfg),
        anneal_mir_eval::StepOutcome::Stepped { .. }
    ));
    assert!(!state.mem.allocations.iter().find(|a| a.alloc_id == p1.alloc_id).unwrap().live);
    match state.step(&indirect_ops, &cfg) {
        anneal_mir_eval::StepOutcome::Done(TerminalOut::Returned { ret, .. }) => {
            assert_eq!(ret, Val::u32(0xDEAD_BEEF));
        }
        other => panic!("expected Done(0xDEAD_BEEF), got {other:?}"),
    }
}

#[test]
fn strict_profile_v1_rejections_and_semantic_edge_precedence() {
    let mut bad_ver = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
        identity: "test::v2_prog".into(),
    }]);
    bad_ver.mir_profile_version = 2;
    assert_fault(&eval_body(&bad_ver, 0, &[], 16), FaultKind::Unsupported);
    // Automatic profile selection (`EvalConfig::for_program` and
    // `eval_body_auto`) dispatches `mir_profile_version == 2` to Profile v2
    // while strict `EvalConfig::profile_v1()` continues to fail closed.
    let auto_cfg = EvalConfig::for_program(&bad_ver, None).unwrap();
    assert!(auto_cfg.enable_profile_v2());
    assert_returned(&eval_body_auto(&bad_ver, 0, &[], 16), Val::Unit);
    assert_returned(
        &eval_body_with_config(&bad_ver, 0, &[], 16, &EvalConfig::profile_v2(TargetEndian::Little)),
        Val::Unit,
    );

    let mut bad_ptr_bits = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
        identity: "test::32bit".into(),
    }]);
    bad_ptr_bits.pointer_width_bits = 32;
    assert_fault(&eval_body(&bad_ptr_bits, 0, &[], 16), FaultKind::Unsupported);

    let non_empty_caller_mem = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 1,
            align_log2: 0,
            mutability: Mutability::Shared,
            bytes: vec![],
            live: true,
        }],
    };
    let empty_prog = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
        identity: "test::caller_mem".into(),
    }]);
    let err = MachineState::init_with_caller_mem(
        &empty_prog,
        0,
        &[],
        non_empty_caller_mem,
        &EvalConfig::profile_v1(),
    )
    .unwrap_err();
    assert_eq!(err.kind, FaultKind::Unsupported);

    // Dead projected Rvalue::Discriminant faults Undefined before Unsupported.
    let repr_u8 = canary_repr_u8_enum();
    let dead_proj_discr = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![U8_TY, Ty::Enum(repr_u8)],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 1 },
                Statement::StorageDead { local: 1 },
                Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Discriminant {
                        place: Place { local: 1, projection: vec![ProjectionElem::Unsupported] },
                    },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::dead_proj_discr".into(),
    }]);
    assert_fault(&eval_body(&dead_proj_discr, 0, &[], 16), FaultKind::Undefined);

    // Normalized Tuple overflow pair treats WithRetag::Yes as a no-op.
    let norm_ovf = Ty::Tuple { fields: vec![U32_TY, Ty::Bool] };
    let retag_norm_ovf = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![norm_ovf.clone(), norm_ovf],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Use {
                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                    with_retag: true,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: "test::retag_norm_ovf".into(),
    }]);
    let arg_pair = Val::overflow_pair(ScalarVal::new(IntWidth::I32, false, 7), false);
    assert_returned(&eval_body(&retag_norm_ovf, 0, std::slice::from_ref(&arg_pair), 16), arg_pair);
}

#[test]
fn profile_v2_refuses_call_sysroot_call_and_panicking_assert() {
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);

    // 1. Profile v2 refuses `Terminator::Call` (`Unsupported`).
    let prog_call = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::Call {
                            callee: 1,
                            args: vec![],
                            dst_local: 0,
                            dst_projection: Vec::new(),
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                ],
                identity: "test::v2_caller".into(),
            },
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit],
                blocks: vec![Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::v2_callee".into(),
            },
        ],
    };
    assert_fault(&eval_body_with_config(&prog_call, 0, &[], 32, &v2_cfg), FaultKind::Unsupported);

    // 2. Profile v2 refuses `Terminator::SysrootCall` (`Unsupported`).
    let prog_sysroot = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![U8_TY],
            blocks: vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::SysrootCall {
                        op: SysrootNumOp {
                            kind: SysrootNumKind::WrappingAdd,
                            ty: IntTy { width: IntWidth::I8, signed: false },
                        },
                        args: vec![
                            Operand::Constant { ty: U8_TY, lit: ConstLit::Scalar { bits: 1 } },
                            Operand::Constant { ty: U8_TY, lit: ConstLit::Scalar { bits: 2 } },
                        ],
                        dst_local: 0,
                        dst_projection: Vec::new(),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
            ],
            identity: "test::v2_sysroot".into(),
        }],
    };
    assert_fault(
        &eval_body_with_config(&prog_sysroot, 0, &[], 32, &v2_cfg),
        FaultKind::Unsupported,
    );

    // 3. Profile v2 `Assert`: passing advances to `target`; failed
    //    `NullPtrDeref`/`MisalignedPtrDeref` faults `Undefined`
    //    (`CheckPtrAssertOnly`, `ModelOnlyUnreplayed`); failed panicking
    //    asserts (`BoundsCheck`, `Overflow`) fault `Unsupported`.
    let mk_assert_prog = |cond: u128, msg: AssertKind| Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit],
            blocks: vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant {
                            ty: Ty::Bool,
                            lit: ConstLit::Scalar { bits: cond },
                        },
                        expected: true,
                        msg,
                        target: 1,
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
            ],
            identity: "test::v2_assert".into(),
        }],
    };
    assert_returned(
        &eval_body_with_config(&mk_assert_prog(1, AssertKind::NullPtrDeref), 0, &[], 32, &v2_cfg),
        Val::Unit,
    );
    for msg in [AssertKind::NullPtrDeref, AssertKind::MisalignedPtrDeref] {
        let trace = eval_body_with_config(&mk_assert_prog(0, msg), 0, &[], 32, &v2_cfg);
        match &trace.outcome {
            Outcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined);
                assert_eq!(f.ub_class, Some(UbClass::CheckPtrAssertOnly));
                assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
            }
            other => panic!("expected Undefined(CheckPtrAssertOnly), got {other:?}"),
        }
    }
    for msg in [AssertKind::BoundsCheck, AssertKind::Overflow { op: BinOp::Add }] {
        assert_fault(
            &eval_body_with_config(&mk_assert_prog(0, msg), 0, &[], 32, &v2_cfg),
            FaultKind::Unsupported,
        );
    }
}

#[test]
fn profile_v2_partial_tuple_move_preserves_sibling_fields() {
    let pair_ty = Ty::Tuple { fields: vec![U32_TY, Ty::Bool] };
    let nested_ty = Ty::Tuple { fields: vec![pair_ty.clone(), Ty::Bool] };
    let mut roots = BTreeSet::new();
    roots.insert("test::partial_move".into());
    roots.insert("test::moved_field_undef".into());
    roots.insert("test::nested_move_unsup".into());
    roots.insert("test::nested_copy_ok".into());
    let prog = Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            // Body 0: `_2 = move (_1.0); _0 = move (_1.1);` on `(u32, bool)` succeeds.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![Ty::Bool, pair_ty.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 1,
                                        ty: Ty::Bool,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::partial_move".into(),
            },
            // Body 1: single-level move `_2 = move (_1.0)` followed by
            // re-reading `_1.0` faults `Undefined(MoveDeinitLocalRead)`.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![U32_TY, pair_ty.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::moved_field_undef".into(),
            },
            // Body 2: nested field move `move ((_1.0).0)` faults `Unsupported`
            // matching `Step.lean` single-level `PartialTuple`.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![U32_TY, nested_ty.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Move {
                                local: 1,
                                projection: vec![
                                    ProjectionElem::Field { field_idx: 0, ty: pair_ty.clone() },
                                    ProjectionElem::Field { field_idx: 0, ty: U32_TY },
                                ],
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::nested_move_unsup".into(),
            },
            // Body 3: nested field copy `copy ((_1.0).0)` succeeds.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![U32_TY, nested_ty],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy {
                                local: 1,
                                projection: vec![
                                    ProjectionElem::Field { field_idx: 0, ty: pair_ty },
                                    ProjectionElem::Field { field_idx: 0, ty: U32_TY },
                                ],
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::nested_copy_ok".into(),
            },
        ],
    };
    let pair_val = Val::Tuple(vec![Val::u32(42), Val::Bool(true)]);
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    assert_returned(
        &eval_body_with_config(&prog, 0, std::slice::from_ref(&pair_val), 16, &v2_cfg),
        Val::Bool(true),
    );
    match &eval_body_with_config(&prog, 1, std::slice::from_ref(&pair_val), 16, &v2_cfg).outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::MoveDeinitLocalRead));
        }
        other => panic!("expected Undefined(MoveDeinitLocalRead), got {other:?}"),
    }

    let nested_val = Val::Tuple(vec![pair_val, Val::Bool(false)]);
    assert_fault(
        &eval_body_with_config(&prog, 2, std::slice::from_ref(&nested_val), 16, &v2_cfg),
        FaultKind::Unsupported,
    );
    assert_returned(&eval_body_with_config(&prog, 3, &[nested_val], 16, &v2_cfg), Val::u32(42));
}

#[test]
fn profile_v2_empty_tuple_aggregate_and_probe_distinguish_unit() {
    let empty_tuple_ty = Ty::Tuple { fields: Vec::new() };
    let prog = Program {
        scope: Scope::SelectedUnit {
            roots: [
                "test::make_empty_tuple".into(),
                "test::make_unit".into(),
                "test::id_empty_tuple".into(),
                "test::mismatched_empty_agg".into(),
            ]
            .into_iter()
            .collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![empty_tuple_ty.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::AggregateTuple { fields: Vec::new() },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::make_empty_tuple".into(),
            },
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Aggregate {
                            aggregate_kind: AggregateKind::Tuple,
                            fields: Vec::new(),
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::make_unit".into(),
            },
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![empty_tuple_ty.clone(), empty_tuple_ty],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 1, projection: Vec::new() },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::id_empty_tuple".into(),
            },
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Tuple { fields: vec![U32_TY] }],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::AggregateTuple { fields: Vec::new() },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::mismatched_empty_agg".into(),
            },
        ],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
    };

    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    assert_returned(&eval_body_with_config(&prog, 0, &[], 16, &cfg), Val::Tuple(Vec::new()));
    assert_returned(&eval_body_with_config(&prog, 1, &[], 16, &cfg), Val::Unit);
    assert_fault(&eval_body_with_config(&prog, 3, &[], 16, &cfg), FaultKind::Unsupported);

    let report = probe_body(&prog, 2, &ProbeConfig::default(), &cfg);
    assert!(!report.unsupported_param_shape);
    assert!(report.cases_run > 0);
    assert_eq!(report.returned_count, report.cases_run);
    assert_eq!(report.unsupported_count, 0);
}

#[test]
fn partial_tuple_force_allocation_rejects_partial_and_avoids_leak_on_error() {
    let overflow_ty = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
    let bad_prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["test::bad_force".into()].into_iter().collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit, overflow_ty, Ty::Tuple { fields: vec![U32_TY, U32_TY] }],
            blocks: vec![Block {
                statements: Vec::new(),
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            identity: "test::bad_force".into(),
        }],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut err_state = MachineState::init(&bad_prog, 0, &[], &cfg).unwrap();
    let base_allocs = err_state.mem.allocations.len();

    // `force_allocation` on `LocalSlot::PartialTuple` fails closed with
    // `Unsupported` without leaking an allocation (matching `Step.lean`).
    err_state.frames[0].locals[1] =
        LocalSlot::PartialTuple { fields: vec![Some(Val::u32(1)), None] };
    assert_eq!(
        err_state.force_allocation(&bad_prog, 1, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_eq!(err_state.mem.allocations.len(), base_allocs);

    // Mismatched immediate value also fails closed without leaking.
    err_state.frames[0].locals[1] = LocalSlot::Immediate { val: Some(Val::Bool(false)) };
    assert_eq!(
        err_state.force_allocation(&bad_prog, 1, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_eq!(err_state.mem.allocations.len(), base_allocs);

    // General tuple `(u32, u32)` has no layout in `Trusted.MirSemantics`.
    err_state.frames[0].locals[2] =
        LocalSlot::PartialTuple { fields: vec![Some(Val::u32(1)), Some(Val::u32(2))] };
    assert_eq!(
        err_state.force_allocation(&bad_prog, 2, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_eq!(err_state.mem.allocations.len(), base_allocs);

    // Valid immediate overflow pair promotes into stack memory cleanly.
    err_state.frames[0].locals[1] = LocalSlot::Immediate {
        val: Some(Val::overflow_pair(ScalarVal::new(IntWidth::I32, false, 0x0102_0304), true)),
    };
    let place = err_state.force_allocation(&bad_prog, 1, &cfg).unwrap();
    let bytes = err_state.mem.read_bytes(place, 8, 2).unwrap();
    assert_eq!(
        decode_val(
            TargetEndian::Little,
            &Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false }),
            &bytes,
            true,
        )
        .unwrap(),
        Some(Val::overflow_pair(ScalarVal::new(IntWidth::I32, false, 0x0102_0304), true))
    );
}

#[test]
fn pointer_and_ref_layout_and_encoding_match_profile_v1_vs_v2() {
    let ref_ty = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let raw_ty = Ty::RawPtr { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let slice_ref_ty = Ty::Ref {
        mutability: Mutability::Shared,
        pointee: Box::new(Ty::Slice { elem: Box::new(U8_TY) }),
    };
    let mut mem = anneal_mir_eval::MemoryState::default();
    let place = mem.allocate_stack(LayoutData { size: 8, align_log2: 3 });

    // Profile v1: references and raw pointers have no layout.
    for ty in [&ref_ty, &raw_ty, &slice_ref_ty] {
        assert_eq!(layout_of_ty(ty, false), None);
        assert_eq!(
            decode_val(TargetEndian::Little, ty, &[AllocByte::Uninit; 8], false).unwrap_err().kind,
            FaultKind::Unsupported
        );
        assert_eq!(
            load_indirect(&mem, TargetEndian::Little, ty, place, false).unwrap_err().kind,
            FaultKind::Unsupported
        );
        assert_eq!(
            memory::deinit_indirect(&mut mem, ty, place, false).unwrap_err().kind,
            FaultKind::Unsupported
        );
    }

    // Profile v2: thin pointers have `⟨8, 3⟩`, wide slice pointers have
    // `⟨16, 3⟩`, and uniform provenance round-trips through byte memory.
    assert_eq!(layout_of_ty(&ref_ty, true), Some(LayoutData { size: 8, align_log2: 3 }));
    assert_eq!(layout_of_ty(&raw_ty, true), Some(LayoutData { size: 8, align_log2: 3 }));
    assert_eq!(layout_of_ty(&slice_ref_ty, true), Some(LayoutData { size: 16, align_log2: 3 }));
    assert_eq!(
        layout_of_ty(&Ty::RangeTo { elem: Box::new(USIZE_TY) }, true),
        Some(LayoutData { size: 8, align_log2: 3 })
    );

    let thin_val = Val::Ptr(PtrVal { alloc_id: Some(7), offset_bytes: 16, width: IntWidth::Isize });
    store_indirect(&mut mem, TargetEndian::Little, &raw_ty, place, &thin_val, true).unwrap();
    assert_eq!(
        load_indirect(&mem, TargetEndian::Little, &raw_ty, place, true).unwrap(),
        Some(thin_val.clone())
    );
    // Uninitialized pointer bytes decode as `Ok(None)`.
    assert_eq!(decode_val(TargetEndian::Little, &raw_ty, &[AllocByte::Uninit; 8], true), Ok(None));
    // Mixed provenance across pointer bytes drops provenance
    // (`alloc_id: None`).
    let mut mixed_bytes = encode_val(TargetEndian::Little, &raw_ty, &thin_val, true).unwrap();
    if let AllocByte::Init { prov, .. } = &mut mixed_bytes[7] {
        *prov = Some(99);
    }
    assert_eq!(
        decode_val(TargetEndian::Little, &raw_ty, &mixed_bytes, true).unwrap(),
        Some(Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 16, width: IntWidth::Isize }))
    );

    // Wide slice pointer round-trip through 16-byte stack allocation.
    let wide_place = mem.allocate_stack(LayoutData { size: 16, align_log2: 3 });
    let wide_val = Val::SlicePtr {
        ptr: PtrVal { alloc_id: Some(5), offset_bytes: 4, width: IntWidth::Isize },
        len: 12,
    };
    store_indirect(&mut mem, TargetEndian::Little, &slice_ref_ty, wide_place, &wide_val, true)
        .unwrap();
    assert_eq!(
        load_indirect(&mem, TargetEndian::Little, &slice_ref_ty, wide_place, true).unwrap(),
        Some(wide_val)
    );

    // Profile v2 `force_allocation` succeeds on raw pointer locals.
    let prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["test::raw_ptr_local".into()].into_iter().collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit, raw_ty],
            blocks: vec![Block {
                statements: Vec::new(),
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            identity: "test::raw_ptr_local".into(),
        }],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut state = MachineState::init(&prog, 0, &[], &cfg).unwrap();
    let ptr_place = state.force_allocation(&prog, 1, &cfg).unwrap();
    assert_eq!(state.mem.read_bytes(ptr_place, 8, 3).unwrap(), vec![AllocByte::Uninit; 8]);
}

#[test]
fn ret_with_malformed_single_frame_return_to_faults_instead_of_panicking() {
    let prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["test::ret".into()].into_iter().collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit],
            blocks: vec![Block {
                statements: Vec::new(),
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            identity: "test::ret".into(),
        }],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut state = MachineState::init(&prog, 0, &[], &cfg).unwrap();
    state.frames[0] = FrameState {
        def_id: 0,
        block_idx: 0,
        stmt_idx: 0,
        locals: vec![LocalSlot::Immediate { val: Some(Val::Unit) }],
        sysroot_op: None,
        return_to: Some(CallReturnTarget {
            block_idx: Some(0),
            dst_local: 0,
            dst_projection: Vec::new(),
        }),
    };
    match state.step(&prog, &cfg) {
        StepOutcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported),
        other => panic!("expected Fault(Unsupported), got {other:?}"),
    }
}

#[test]
fn zst_unit_slot_and_partial_tuple_unit_move_match_trusted_mir_semantics() {
    let u32_unit = Ty::Tuple { fields: vec![U32_TY, Ty::Unit] };
    let all_zst_pair = Ty::Tuple { fields: vec![Ty::Unit, Ty::Unit] };
    let prog = Program {
        scope: Scope::SelectedUnit {
            roots: [
                "test::move_unit_field_twice".into(),
                "test::copy_uninit_zst_field".into(),
                "test::copy_uninit_all_zst_tuple".into(),
                "test::copy_uninit_unit_local".into(),
            ]
            .into_iter()
            .collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![
            // Body 0: moving a `Unit` field from an initialized `(u32, ())`
            // keeps `Some(Val::Unit)` in `PartialTuple` (`Step.lean`),
            // so a second move of field 1 and moving sibling field 0 succeed.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![U32_TY, u32_unit.clone(), Ty::Unit],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 1,
                                        ty: Ty::Unit,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 1,
                                        ty: Ty::Unit,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::move_unit_field_twice".into(),
            },
            // Body 1: reading an uninitialized `(u32, ())` faults Undefined.
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit, u32_unit],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 1,
                                        ty: Ty::Unit,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::copy_uninit_zst_field".into(),
            },
            // Body 2: `live_uninit_slot` does NOT pre-initialize `((), ())`
            // (`Enum.lean:430-435`), so copying before writing faults UB.
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![all_zst_pair.clone(), all_zst_pair],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::copy_uninit_all_zst_tuple".into(),
            },
            // Body 3: `live_uninit_slot` DOES initialize bare `Ty::Unit`.
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit, Ty::Unit],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::copy_uninit_unit_local".into(),
            },
        ],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
    };

    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let pair = Val::Tuple(vec![Val::u32(99), Val::Unit]);
    assert_returned(&eval_body_with_config(&prog, 0, &[pair], 16, &cfg), Val::u32(99));
    assert_fault(&eval_body_with_config(&prog, 1, &[], 16, &cfg), FaultKind::Undefined);
    assert_fault(&eval_body_with_config(&prog, 2, &[], 16, &cfg), FaultKind::Undefined);
    assert_returned(&eval_body_with_config(&prog, 3, &[], 16, &cfg), Val::Unit);
}

#[test]
fn profile_v2_version_bounds_ptr_checks_and_entry_ref_validity() {
    // Unsupported `mir_profile_version` (0 or >= 3) must fail closed under
    // both `EvalConfig::for_program` and explicit `EvalConfig::profile_v2`.
    let mut unit_prog = single_unit_program(vec![Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
        identity: "test::ver_check".into(),
    }]);
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    for bad in [0u32, 3, 99] {
        unit_prog.mir_profile_version = bad;
        assert!(EvalConfig::for_program(&unit_prog, None).is_err(), "ver={bad}");
        assert_fault(&eval_body_auto(&unit_prog, 0, &[], 16), FaultKind::Unsupported);
        assert_fault(
            &eval_body_with_config(&unit_prog, 0, &[], 16, &v2_cfg),
            FaultKind::Unsupported,
        );
    }

    // `checkValV2` (`Enum.lean:517-520`) checks pointer width (`isize`) and
    // thin-vs-wide shape structurally, while entry ref validity
    // (`refs_valid_in_mem`) catches null/dangling/misaligned/uninit `&u32` as
    // `Undefined(EntryInvalidRefArg)`.
    let ref_ty = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let raw_ty = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let null_isize = Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize });
    let live_isize =
        Val::Ptr(PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize });
    let bad_i8 = Val::Ptr(PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::I8 });
    let bad_i64 = Val::Ptr(PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::I64 });

    assert!(check_val(&null_isize, &ref_ty, true));
    assert!(!check_val(&bad_i8, &ref_ty, true));
    assert!(!check_val(&bad_i64, &ref_ty, true));
    assert!(check_val(&live_isize, &ref_ty, true));
    assert!(check_val(&null_isize, &raw_ty, true));
    assert!(!check_val(&bad_i8, &raw_ty, true));
    assert!(!check_val(&bad_i64, &raw_ty, true));

    let ref_prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["test::take_ref".into()].into_iter().collect(),
            instantiations: BTreeSet::new(),
        },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            local_tys: vec![Ty::Unit, ref_ty],
            blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
            identity: "test::take_ref".into(),
        }],
    };
    let null_trace = eval_body_with_config(&ref_prog, 0, &[null_isize], 16, &v2_cfg);
    match &null_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::EntryInvalidRefArg));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("expected Undefined(EntryInvalidRefArg), got {other:?}"),
    }
    assert_fault(
        &eval_body_with_config(&ref_prog, 0, &[bad_i8], 16, &v2_cfg),
        FaultKind::Unsupported,
    );
}

#[test]
fn zero_sized_memory_ops_check_allocation_and_alignment_only() {
    use anneal_mir_eval::{Allocation, MemPlace, MemoryState};

    let mut mem = MemoryState {
        next_alloc_id: 10,
        allocations: vec![
            Allocation {
                alloc_id: 2,
                align_log2: 2,
                mutability: Mutability::Mut,
                bytes: vec![AllocByte::Uninit; 4],
                live: true,
            },
            Allocation {
                alloc_id: 3,
                align_log2: 2,
                mutability: Mutability::Mut,
                bytes: vec![AllocByte::Uninit; 4],
                live: false,
            },
            Allocation {
                alloc_id: 4,
                align_log2: 1,
                mutability: Mutability::Mut,
                bytes: vec![AllocByte::Uninit; 4],
                live: true,
            },
            Allocation {
                alloc_id: 5,
                align_log2: 1,
                mutability: Mutability::Mut,
                bytes: vec![AllocByte::Uninit; 4],
                live: false,
            },
            Allocation {
                alloc_id: 6,
                align_log2: 2,
                mutability: Mutability::Shared,
                bytes: vec![AllocByte::Uninit; 4],
                live: true,
            },
        ],
    };

    // `Trusted.MirSemantics.Memory` (`Memory.lean:215-289`) resolves
    // `findAllocation` before the `size == 0` branch, so an unknown `alloc_id`
    // faults `Undefined` even when `size == 0 && align_log2 == 0`.
    let missing = MemPlace { alloc_id: 99, offset: 0 };
    assert_eq!(mem.read_bytes(missing, 0, 0).unwrap_err().kind, FaultKind::Undefined);
    assert_eq!(mem.write_bytes(missing, 0, &[]).unwrap_err().kind, FaultKind::Undefined);
    assert_eq!(mem.write_uninit(missing, 0, 0).unwrap_err().kind, FaultKind::Undefined);
    assert_eq!(mem.read_bytes(missing, 0, 2).unwrap_err().kind, FaultKind::Undefined);
    assert_eq!(mem.write_bytes(missing, 2, &[]).unwrap_err().kind, FaultKind::Undefined);
    assert_eq!(mem.write_uninit(missing, 0, 2).unwrap_err().kind, FaultKind::Undefined);

    // Misaligned `size == 0` must fail on live, dead, under-aligned, and OOB
    // allocations across read_bytes, write_bytes, and write_uninit.
    for place in [
        MemPlace { alloc_id: 2, offset: 2 },  // live, unaligned offset
        MemPlace { alloc_id: 3, offset: 2 },  // dead, unaligned offset
        MemPlace { alloc_id: 4, offset: 0 },  // live, alloc align 1 < req align 2
        MemPlace { alloc_id: 5, offset: 0 },  // dead, alloc align 1 < req align 2
        MemPlace { alloc_id: 2, offset: 14 }, // OOB, unaligned offset
    ] {
        assert_eq!(mem.read_bytes(place, 0, 2).unwrap_err().kind, FaultKind::Undefined);
        assert_eq!(mem.write_bytes(place, 2, &[]).unwrap_err().kind, FaultKind::Undefined);
        assert_eq!(mem.write_uninit(place, 0, 2).unwrap_err().kind, FaultKind::Undefined);
    }

    // Aligned `size == 0` succeeds on dead, OOB, and immutable allocations.
    for place in [
        MemPlace { alloc_id: 3, offset: 0 },  // dead alloc, aligned
        MemPlace { alloc_id: 2, offset: 16 }, // OOB offset, aligned
        MemPlace { alloc_id: 6, offset: 0 },  // immutable alloc, aligned
    ] {
        assert_eq!(mem.read_bytes(place, 0, 2).unwrap(), Vec::<AllocByte>::new());
        assert_eq!(mem.write_bytes(place, 2, &[]), Ok(()));
        assert_eq!(mem.write_uninit(place, 0, 2), Ok(()));
    }

    // Non-zero reads/writes still fail on dead, OOB, and immutable allocations.
    assert_eq!(
        mem.read_bytes(MemPlace { alloc_id: 3, offset: 0 }, 4, 2).unwrap_err().kind,
        FaultKind::Undefined
    );
    assert_eq!(
        mem.read_bytes(MemPlace { alloc_id: 2, offset: 4 }, 4, 2).unwrap_err().kind,
        FaultKind::Undefined
    );
    assert_eq!(
        mem.write_bytes(MemPlace { alloc_id: 6, offset: 0 }, 4, &[AllocByte::Uninit; 4])
            .unwrap_err()
            .kind,
        FaultKind::Undefined
    );

    // 64-bit offsets/alignment beyond 32 bits do not truncate on 32-bit hosts.
    let high_align = Allocation {
        alloc_id: 7,
        align_log2: 33,
        mutability: Mutability::Mut,
        bytes: vec![AllocByte::Uninit; 4],
        live: true,
    };
    mem.allocations.push(high_align);
    assert_eq!(
        mem.read_bytes(MemPlace { alloc_id: 7, offset: 1u64 << 32 }, 0, 33).unwrap_err().kind,
        FaultKind::Undefined
    );
    assert_eq!(
        mem.read_bytes(MemPlace { alloc_id: 7, offset: 1u64 << 33 }, 0, 33).unwrap(),
        Vec::<AllocByte>::new()
    );
}

#[test]
fn profile_v2_ill_typed_tuple_and_call_fault_unsupported_before_uninit_ub() {
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);

    // Tuple aggregate assigning an uninitialized `bool` into a `u32` local
    // must classify as `FaultKind::Unsupported` rather than `Undefined`.
    let bad_tuple = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            identity: "rust-path-v1::bad_tuple".into(),
            local_tys: vec![U32_TY, Ty::Bool],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: vec![],
                    value: Rvalue::AggregateTuple {
                        fields: vec![Operand::Copy { local: 1, projection: vec![] }],
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    match eval_body_with_config(&bad_tuple, 0, &[], 100, &cfg).outcome {
        Outcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported, "{f:?}"),
        other => panic!("expected Unsupported fault, got {other:?}"),
    }

    // `Terminator::Call` with mismatched arity/type and an uninitialized local
    // must classify as `FaultKind::Unsupported` rather than `Undefined`.
    let bad_call = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: false,
                identity: "rust-path-v1::caller".into(),
                local_tys: vec![U32_TY, Ty::Bool],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::Call {
                            callee: 1,
                            args: vec![Operand::Copy { local: 1, projection: vec![] }],
                            dst_local: 0,
                            dst_projection: vec![],
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                ],
            },
            Body {
                arg_count: 1,
                is_unsafe: false,
                identity: "rust-path-v1::callee".into(),
                local_tys: vec![U32_TY, U32_TY],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: vec![],
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 1, projection: vec![] },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
        ],
    };
    match eval_body_with_config(&bad_call, 0, &[], 100, &cfg).outcome {
        Outcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported, "{f:?}"),
        other => panic!("expected Unsupported fault, got {other:?}"),
    }
}

#[test]
fn real_zerocopy_01_usize_pointer_metadata_capture_evaluates_and_probes_cleanly() {
    // Captured verbatim from `zerocopy/proofs/01_usize_pointer_metadata` via
    // `anneal-rustc-capture` (schema version 5, Profile v1) with unselected
    // census rows elided and host paths normalized.
    const CAPTURE_JSON: &str =
        include_str!("fixtures/zerocopy_01_usize_pointer_metadata_capture.json");
    let input = CaptureInput::from_json_str(CAPTURE_JSON).unwrap();
    let CaptureInput::Manifest(manifest) = input else {
        panic!("expected schema-v5 capture manifest");
    };
    assert_eq!(manifest.schema_version, anneal_mir_eval::CAPTURE_SCHEMA_VERSION);
    assert_eq!(manifest.configuration.crate_name, "zerocopy");
    assert_eq!(manifest.program.bodies.len(), 2);

    let endian = TargetEndian::from_manifest_str(&manifest.configuration.endian);
    let cfg = EvalConfig::for_program(&manifest.program, endian).unwrap();
    for (body_id, expected_ident) in [
        (0usize, "rust-path-v1::<usize as PointerMetadata>::from_elem_count"),
        (1usize, "rust-path-v1::<usize as PointerMetadata>::to_elem_count"),
    ] {
        assert_eq!(manifest.program.bodies[body_id].identity, expected_ident);
        for sample in [0u128, 1, 42, u64::MAX as u128] {
            let arg = Val::Scalar(ScalarVal::new(IntWidth::Isize, false, sample));
            let trace = eval_body_with_config(
                &manifest.program,
                body_id,
                std::slice::from_ref(&arg),
                64,
                &cfg,
            );
            match trace.outcome {
                Outcome::Returned(TerminalOut::Returned { ret, .. }) => assert_eq!(ret, arg),
                other => panic!("expected Returned({arg:?}), got {other:?}"),
            }
        }
        let report = probe_body(
            &manifest.program,
            body_id,
            &ProbeConfig { max_cases: 32, fuel: 128, seed: 1 },
            &cfg,
        );
        assert!(report.cases_run > 0);
        assert_eq!(report.returned_count, report.cases_run);
        assert_eq!(report.undefined_count, 0);
        assert_eq!(report.unsupported_count, 0);
        assert_eq!(report.out_of_fuel_count, 0);
    }
}

#[test]
fn manifest_syncs_and_cross_checks_pointer_bits_in_from_json_str() {
    const CAPTURE_JSON: &str =
        include_str!("fixtures/zerocopy_01_usize_pointer_metadata_capture.json");
    let manifest_32 = CAPTURE_JSON.replacen("\"pointer_bits\": 64", "\"pointer_bits\": 32", 1);
    assert_ne!(manifest_32, CAPTURE_JSON, "fixture must contain pointer_bits: 64");
    let CaptureInput::Manifest(manifest) = CaptureInput::from_json_str(&manifest_32).unwrap()
    else {
        panic!("expected manifest");
    };
    // Direct `&manifest.program` callers must observe
    // `pointer_width_bits == 32`.
    assert_eq!(manifest.program.pointer_width_bits, 32);
    let trace = eval_body_with_config(
        &manifest.program,
        0,
        &[Val::Scalar(ScalarVal::new(IntWidth::Isize, false, 1))],
        16,
        &EvalConfig::profile_v1(),
    );
    match trace.outcome {
        Outcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported),
        other => panic!("expected Unsupported on 32-bit manifest program, got {other:?}"),
    }

    // Explicit mismatched `program.pointer_width_bits` is rejected at parse
    // time.
    let mismatched =
        manifest_32.replacen("\"program\": {", "\"program\": { \"pointer_width_bits\": 64,", 1);
    assert_ne!(mismatched, manifest_32);
    let err = CaptureInput::from_json_str(&mismatched).unwrap_err();
    assert!(err.contains("pointer width mismatch"), "{err}");
}

#[test]
fn probe_body_validates_program_body_and_all_params_before_uninhabited_or_zero_cases() {
    let u32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
    let unsupported_ty = Ty::Unsupported {};
    let ret_block = Block { statements: vec![], terminator: Terminator::Ret, cleanup: false };

    // 1. Uninhabited `!` param must still report unsupported program config
    //    (`pointer_width_bits == 32`, `mir_profile_version == 2` under v1).
    let never_body = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::never".into(),
        local_tys: vec![Ty::Unit, Ty::Never],
        blocks: vec![ret_block.clone()],
    };
    let prog_32 = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 32,
        mir_profile_version: 1,
        overflow_checks: false,
        bodies: vec![never_body.clone()],
    };
    let r32 = probe_body(&prog_32, 0, &ProbeConfig::default(), &EvalConfig::profile_v1());
    assert_eq!(r32.unsupported_count, 1);
    assert!(!r32.uninhabited_params);

    let prog_v2 = Program { pointer_width_bits: 64, mir_profile_version: 2, ..prog_32.clone() };
    let rv2 = probe_body(&prog_v2, 0, &ProbeConfig::default(), &EvalConfig::profile_v1());
    assert_eq!(rv2.unsupported_count, 1);

    // 2. Uninhabited `!` param must still reject invalid body (`blocks: []`
    //    or unsupported local).
    let empty_blocks = Body { blocks: vec![], ..never_body.clone() };
    let prog_empty = Program {
        pointer_width_bits: 64,
        mir_profile_version: 1,
        bodies: vec![empty_blocks],
        ..prog_32.clone()
    };
    let rempty = probe_body(&prog_empty, 0, &ProbeConfig::default(), &EvalConfig::profile_v1());
    assert_eq!(rempty.unsupported_count, 1);

    // 3. `ProbeConfig { max_cases: 0, .. }` still validates program and body.
    let zero_cfg = ProbeConfig { max_cases: 0, fuel: 16, seed: 1 };
    let bad_local_body = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::bad_local".into(),
        local_tys: vec![Ty::Unit, u32_ty.clone(), unsupported_ty.clone()],
        blocks: vec![ret_block.clone()],
    };
    let prog_bad_local = Program {
        pointer_width_bits: 64,
        mir_profile_version: 1,
        bodies: vec![bad_local_body],
        ..prog_32.clone()
    };
    let rzero = probe_body(&prog_bad_local, 0, &zero_cfg, &EvalConfig::profile_v1());
    assert_eq!(rzero.unsupported_count, 1);

    // 4. Tuple `(Never, RawPtr)` is supported in Profile v2 (uninhabited
    //    without unsupported error), while `(Never, Unsupported)` fails static
    //    admission (`unsupported_count == 1`, not short-circuited).
    let raw_ptr_ty =
        Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(u32_ty.clone()) };
    let tuple_never_ptr = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::tuple_never_ptr".into(),
        local_tys: vec![Ty::Unit, Ty::Tuple { fields: vec![Ty::Never, raw_ptr_ty] }],
        blocks: vec![ret_block.clone()],
    };
    let prog_tuple = Program {
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![tuple_never_ptr],
        ..prog_32.clone()
    };
    let rtuple = probe_body(
        &prog_tuple,
        0,
        &ProbeConfig::default(),
        &EvalConfig::profile_v2(TargetEndian::Little),
    );
    assert!(!rtuple.unsupported_param_shape);
    assert!(rtuple.uninhabited_params);
    assert_eq!(rtuple.unsupported_count, 0);

    let tuple_never_unsup = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::tuple_never_unsup".into(),
        local_tys: vec![Ty::Unit, Ty::Tuple { fields: vec![Ty::Never, unsupported_ty] }],
        blocks: vec![ret_block],
    };
    let prog_unsup = Program {
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![tuple_never_unsup],
        ..prog_32
    };
    let runsup = probe_body(
        &prog_unsup,
        0,
        &ProbeConfig::default(),
        &EvalConfig::profile_v2(TargetEndian::Little),
    );
    assert_eq!(runsup.unsupported_count, 1);
    assert!(!runsup.uninhabited_params);
}

#[test]
fn profile_v2_deref_cast_and_discriminant_dst_ty_validation() {
    let u8_ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
    let u16_ty = Ty::Int(IntTy { width: IntWidth::I16, signed: false });
    let u32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
    let mut_u32_ref = Ty::Ref { mutability: Mutability::Mut, pointee: Box::new(u32_ty.clone()) };
    let dst_tuple = Ty::Tuple { fields: vec![u32_ty.clone(), Ty::Bool] };
    let enum_u8 = canary_repr_u8_enum();

    // 1. `*_1 = Cast(IntToInt, Copy(_2), u16)` with `_1: &mut u32` and
    //    uninitialized `_2: u8`: passes `place_static_ty_v2` and
    //    `resolve_place_dest_v2`, then `eval_rvalue_v2` rejects `u32 != u16`
    //    with `Unsupported` BEFORE checking `_2` initialization (`Undefined`).
    let deref_cast_body = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::deref_cast_mismatch".into(),
        local_tys: vec![Ty::Unit, mut_u32_ref.clone(), u8_ty],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 2 },
                Statement::AssignPlace {
                    place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                    value: Rvalue::Cast {
                        cast_kind: CastKind::IntToInt,
                        operand: Operand::Copy { local: 2, projection: vec![] },
                        ty: u16_ty,
                    },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
    };
    // 2. Unprojected `_0 = Discriminant(_1)` with `_0: u32` and `_1: Enum(u8)`
    //    fails static `discriminant_types_valid` at `initStateV2`
    //    (`Unsupported`).
    let unproj_discr_body = Body {
        arg_count: 0,
        is_unsafe: false,
        identity: "demo::unproj_discr_mismatch".into(),
        local_tys: vec![u32_ty.clone(), Ty::Enum(enum_u8.clone())],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: vec![],
                value: Rvalue::Discriminant { place: Place::local(1) },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
    };
    // 3. `*_1 = Discriminant(_2)` with `_1: &mut u32` and initialized enum `_2`
    //    reaches `write_place_dest_v2` and faults `Unsupported` (`u8 != u32`),
    //    while uninitialized `_2` faults `Undefined` in
    //    `eval_discriminant_rvalue` (matching `Step.lean:1561-1583`).
    let deref_discr_init_body = Body {
        arg_count: 2,
        is_unsafe: false,
        identity: "demo::deref_discr_mismatch".into(),
        local_tys: vec![Ty::Unit, mut_u32_ref.clone(), Ty::Enum(enum_u8.clone())],
        blocks: vec![Block {
            statements: vec![Statement::AssignPlace {
                place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                value: Rvalue::Discriminant { place: Place::local(2) },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
    };
    let deref_discr_uninit_body = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::deref_discr_uninit".into(),
        local_tys: vec![Ty::Unit, mut_u32_ref, Ty::Enum(enum_u8.clone())],
        blocks: vec![Block {
            statements: vec![
                Statement::StorageLive { local: 2 },
                Statement::AssignPlace {
                    place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                    value: Rvalue::Discriminant { place: Place::local(2) },
                },
            ],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
    };
    // 4. `(_0.0) = ...` (`ProjectionElem::Field` destination) is rejected
    //    fail-closed by `place_static_ty_v2` (`Unsupported`).
    let field_dest_body = Body {
        arg_count: 0,
        is_unsafe: false,
        identity: "demo::field_dest_unsupported".into(),
        local_tys: vec![dst_tuple, u32_ty.clone()],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: vec![ProjectionElem::Field { field_idx: 0, ty: u32_ty.clone() }],
                value: Rvalue::Use {
                    operand: Operand::Constant { ty: u32_ty, lit: ConstLit::Scalar { bits: 1 } },
                    with_retag: false,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
    };

    let prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            deref_cast_body,
            unproj_discr_body,
            deref_discr_init_body,
            deref_discr_uninit_body,
            field_dest_body,
        ],
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Mut,
            bytes: encode_val(TargetEndian::Little, &U32_TY, &Val::u32(0), true).unwrap(),
            live: true,
        }],
    };
    let ptr = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    let expect_fault_reason =
        |trace: &StepTrace, kind: FaultKind, needle: &str| match &trace.outcome {
            Outcome::Fault(f) => {
                assert_eq!(f.kind, kind, "unexpected fault kind: {f:?}");
                assert!(
                    f.reason.contains(needle),
                    "expected reason containing {needle:?}, got {:?}",
                    f.reason
                );
            }
            other => panic!("expected Fault({kind:?}, *{needle}*), got {other:?}"),
        };
    expect_fault_reason(
        &eval_body_with_caller_mem(&prog, 0, std::slice::from_ref(&ptr), cm.clone(), 32, &cfg),
        FaultKind::Unsupported,
        "invalid IntToInt cast types",
    );
    expect_fault_reason(
        &eval_body_with_config(&prog, 1, &[], 32, &cfg),
        FaultKind::Unsupported,
        "discriminant assignment destination type invalid",
    );
    expect_fault_reason(
        &eval_body_with_caller_mem(
            &prog,
            2,
            &[ptr.clone(), Val::EnumVal { ty: enum_u8, variant: 0 }],
            cm.clone(),
            32,
            &cfg,
        ),
        FaultKind::Unsupported,
        "assigned value disagrees with Profile v2 destination type",
    );
    match &eval_body_with_caller_mem(&prog, 3, &[ptr], cm, 32, &cfg).outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::UninitLocalRead));
        }
        other => panic!("expected Undefined(UninitLocalRead), got {other:?}"),
    }
    expect_fault_reason(
        &eval_body_with_config(&prog, 4, &[], 32, &cfg),
        FaultKind::Unsupported,
        "assignment destination place has no Profile v2 static type",
    );
}

#[test]
fn validate_rejects_empty_bodies_oob_entry_empty_identity_and_invalid_skipped_unsafe() {
    let cfg = EvalConfig::profile_v1();
    let empty_prog = single_unit_program(vec![]);
    assert_eq!(
        validate_program_config(&empty_prog, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    let r_empty = probe_body_with_policy(&empty_prog, 0, &ProbeConfig::default(), &cfg, true);
    assert_eq!(r_empty.unsupported_count, 1);
    assert!(!r_empty.skipped_unsafe);

    let valid_unsafe = Body {
        arg_count: 0,
        is_unsafe: true,
        identity: "demo::valid_unsafe".into(),
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
    };
    let oob_entry_prog =
        Program { entry_def_id: 1, ..single_unit_program(vec![valid_unsafe.clone()]) };
    assert_eq!(
        validate_program_config(&oob_entry_prog, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );

    // Valid unsafe body is skipped cleanly when `skip_unsafe` is enabled.
    let prog_valid_unsafe = single_unit_program(vec![valid_unsafe.clone()]);
    let r_skip_ok =
        probe_body_with_policy(&prog_valid_unsafe, 0, &ProbeConfig::default(), &cfg, true);
    assert!(r_skip_ok.skipped_unsafe);
    assert_eq!(r_skip_ok.unsupported_count, 0);

    // Empty identity (safe or unsafe) fails `validate_body_entry` and `probe`.
    for is_unsafe in [false, true] {
        let empty_id_body = Body { identity: String::new(), is_unsafe, ..valid_unsafe.clone() };
        assert_eq!(
            validate_body_entry(&empty_id_body, &cfg).unwrap_err().kind,
            FaultKind::Unsupported
        );
        let prog_empty_id = single_unit_program(vec![empty_id_body]);
        assert!(matches!(
            eval_body_with_config(&prog_empty_id, 0, &[], 32, &cfg).outcome,
            Outcome::Fault(f) if f.kind == FaultKind::Unsupported
        ));
        for skip in [false, true] {
            let r = probe_body_with_policy(&prog_empty_id, 0, &ProbeConfig::default(), &cfg, skip);
            assert_eq!(r.unsupported_count, 1);
            assert!(!r.skipped_unsafe);
        }
    }

    // Invalid unsafe bodies (`blocks: []` or `Ty::Unsupported`) must fail
    // closed even when `skip_unsafe` is enabled.
    let invalid_unsafe_blocks = Body { blocks: vec![], ..valid_unsafe.clone() };
    let invalid_unsafe_ty = Body { local_tys: vec![Ty::Unsupported], ..valid_unsafe };
    for bad in [invalid_unsafe_blocks, invalid_unsafe_ty] {
        let prog_bad = single_unit_program(vec![bad]);
        let r = probe_body_with_policy(&prog_bad, 0, &ProbeConfig::default(), &cfg, true);
        assert_eq!(r.unsupported_count, 1);
        assert!(!r.skipped_unsafe);
    }

    // Pairwise duplicate body identities must fail `validate_program_config`,
    // `eval_body_by_identity`, and `probe_body_with_policy`.
    let dup_a = Body {
        arg_count: 0,
        is_unsafe: false,
        identity: "rust-path-v1::demo::dup".into(),
        local_tys: vec![Ty::Unit],
        blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
    };
    let dup_b = dup_a.clone();
    let dup_prog = single_unit_program(vec![dup_a, dup_b]);
    assert_eq!(validate_program_config(&dup_prog, &cfg).unwrap_err().kind, FaultKind::Unsupported);
    assert!(matches!(
        eval_body_by_identity(&dup_prog, "rust-path-v1::demo::dup", &[], 32).unwrap().outcome,
        Outcome::Fault(f) if f.kind == FaultKind::Unsupported
    ));
    let r_dup = probe_body_with_policy(&dup_prog, 0, &ProbeConfig::default(), &cfg, false);
    assert_eq!(r_dup.unsupported_count, 1);
}

#[test]
fn profile_v2_pointers_slices_retag_refs_casts_offset_and_core_calls() {
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut_u32_ref = Ty::Ref { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let shared_u32_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let const_u32_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let mut_u32_ptr = Ty::RawPtr { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let slice_u8_ref = Ty::Ref {
        mutability: Mutability::Shared,
        pointee: Box::new(Ty::Slice { elem: Box::new(U8_TY) }),
    };

    // 1. Mutable caller memory mutation through `*mut_ref`, `AssignPlace`
    //    resolving destination BEFORE evaluating rvalue (`*_1 = val` after
    //    reading `*_1`), plus `extract_caller_memory` returning mutated bytes.
    let inc_in_place = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            identity: "test::inc_in_place".into(),
            local_tys: vec![U32_TY, mut_u32_ref.clone(), U32_TY],
            blocks: vec![Block {
                statements: vec![
                    Statement::AssignPlace {
                        place: Place { local: 2, projection: Vec::new() },
                        value: Rvalue::UseRetag {
                            operand: Operand::CopyPlace {
                                place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                            },
                        },
                    },
                    Statement::AssignPlace {
                        place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        value: Rvalue::Binary {
                            op: BinOp::Add,
                            left: Operand::CopyPlace {
                                place: Place { local: 2, projection: Vec::new() },
                            },
                            right: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 5 },
                            },
                        },
                    },
                    Statement::AssignPlace {
                        place: Place { local: 0, projection: Vec::new() },
                        value: Rvalue::Use {
                            operand: Operand::CopyPlace {
                                place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                            },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    let cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Mut,
            bytes: encode_val(TargetEndian::Little, &U32_TY, &Val::u32(10), true).unwrap(),
            live: true,
        }],
    };
    let ptr_arg = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    let trace = eval_body_with_caller_mem(&inc_in_place, 0, &[ptr_arg], cm, 32, &cfg);
    match trace.outcome {
        Outcome::Returned(TerminalOut::Returned { ret, caller_mem }) => {
            assert_eq!(ret, Val::u32(15));
            assert_eq!(
                decode_val(TargetEndian::Little, &U32_TY, &caller_mem.allocations[0].bytes, true)
                    .unwrap(),
                Some(Val::u32(15))
            );
        }
        other => panic!("expected Returned(15) with updated caller_mem, got {other:?}"),
    }

    // 2. `AssignPlace` 3-phase ordering (`resolvePlaceDestV2 -> evalRvalueV2 ->
    //    writePlaceDestV2`):
    //    - `*_uninit = 10 / 0` faults `UninitLocalRead` (dest resolved first),
    //    - `*_null = 10 / 0` faults `DivByZero` (rvalue before deref store),
    //    - `*_null = 42` faults `NullOrNoProvPtrAccess` (store checks null),
    //    - `MovePlace [Deref]` fails closed `Unsupported`.
    let resolve_order = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: true,
                identity: "test::uninit_dest_before_rvalue".into(),
                local_tys: vec![Ty::Unit, mut_u32_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::AssignPlace {
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                            value: Rvalue::Binary {
                                op: BinOp::Div,
                                left: Operand::Constant {
                                    ty: U32_TY,
                                    lit: ConstLit::Scalar { bits: 10 },
                                },
                                right: Operand::Constant {
                                    ty: U32_TY,
                                    lit: ConstLit::Scalar { bits: 0 },
                                },
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::null_dest_after_div0".into(),
                local_tys: vec![Ty::Unit, mut_u32_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::AssignPlace {
                        place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        value: Rvalue::Binary {
                            op: BinOp::Div,
                            left: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 10 },
                            },
                            right: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 0 },
                            },
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::null_dest_store".into(),
                local_tys: vec![Ty::Unit, mut_u32_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::AssignPlace {
                        place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 42 },
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::move_through_deref_unsup".into(),
                local_tys: vec![U32_TY, mut_u32_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::AssignPlace {
                        place: Place { local: 0, projection: Vec::new() },
                        value: Rvalue::Use {
                            operand: Operand::MovePlace {
                                place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
        ],
    };
    let null_ptr = Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize });
    match &eval_body_with_config(&resolve_order, 0, &[], 32, &cfg).outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::UninitLocalRead));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected UninitLocalRead before DivByZero, got {other:?}"),
    }
    match &eval_body_with_config(&resolve_order, 1, std::slice::from_ref(&null_ptr), 32, &cfg)
        .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::DivByZero));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected DivByZero before deref store, got {other:?}"),
    }
    match &eval_body_with_config(&resolve_order, 2, std::slice::from_ref(&null_ptr), 32, &cfg)
        .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::NullOrNoProvPtrAccess));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected NullOrNoProvPtrAccess on null deref store, got {other:?}"),
    }
    assert_fault(
        &eval_body_with_config(&resolve_order, 3, &[null_ptr], 32, &cfg),
        FaultKind::Unsupported,
    );

    // 3. `PtrMetadata`, `SliceLen`, `SliceGetUncheckedRange{To,From}`,
    //    `UsizeUncheckedSub`, `AggregateRangeTo`, `AggregateRangeFrom`.
    let range_to_ty = Ty::RangeTo { elem: Box::new(USIZE_TY) };
    let range_from_ty = Ty::RangeFrom { elem: Box::new(USIZE_TY) };
    let slice_ops_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 2,
            is_unsafe: false,
            identity: "test::slice_core_calls".into(),
            local_tys: vec![
                Ty::Tuple {
                    fields: vec![USIZE_TY, USIZE_TY, slice_u8_ref.clone(), slice_u8_ref.clone()],
                },
                slice_u8_ref.clone(),
                USIZE_TY,
                USIZE_TY,
                USIZE_TY,
                range_to_ty,
                range_from_ty,
                slice_u8_ref.clone(),
                slice_u8_ref,
            ],
            blocks: vec![
                Block {
                    statements: vec![Statement::Assign {
                        local: 3,
                        projection: Vec::new(),
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::Copy { local: 1, projection: Vec::new() },
                        },
                    }],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::SliceLen,
                        args: vec![Operand::Copy { local: 1, projection: Vec::new() }],
                        dst: Place { local: 4, projection: Vec::new() },
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block {
                    statements: vec![Statement::Assign {
                        local: 5,
                        projection: Vec::new(),
                        value: Rvalue::AggregateRangeTo {
                            elem_ty: USIZE_TY,
                            end: Operand::Copy { local: 2, projection: Vec::new() },
                        },
                    }],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::SliceGetUncheckedRangeTo,
                        args: vec![
                            Operand::Copy { local: 1, projection: Vec::new() },
                            Operand::Move { local: 5, projection: Vec::new() },
                        ],
                        dst: Place { local: 7, projection: Vec::new() },
                        target: Some(2),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block {
                    statements: vec![Statement::Assign {
                        local: 6,
                        projection: Vec::new(),
                        value: Rvalue::AggregateRangeFrom {
                            elem_ty: USIZE_TY,
                            start: Operand::Copy { local: 2, projection: Vec::new() },
                        },
                    }],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::SliceGetUncheckedRangeFrom,
                        args: vec![
                            Operand::Copy { local: 1, projection: Vec::new() },
                            Operand::Move { local: 6, projection: Vec::new() },
                        ],
                        dst: Place { local: 8, projection: Vec::new() },
                        target: Some(3),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::UsizeUncheckedSub,
                        args: vec![
                            Operand::Copy { local: 4, projection: Vec::new() },
                            Operand::Copy { local: 2, projection: Vec::new() },
                        ],
                        dst: Place { local: 4, projection: Vec::new() },
                        target: Some(4),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::AggregateTuple {
                            fields: vec![
                                Operand::Copy { local: 3, projection: Vec::new() },
                                Operand::Copy { local: 4, projection: Vec::new() },
                                Operand::Copy { local: 7, projection: Vec::new() },
                                Operand::Copy { local: 8, projection: Vec::new() },
                            ],
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                },
            ],
        }],
    };
    let slice_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 0,
            mutability: Mutability::Shared,
            bytes: vec![
                AllocByte::Init { byte: 10, prov: None },
                AllocByte::Init { byte: 20, prov: None },
                AllocByte::Init { byte: 30, prov: None },
                AllocByte::Init { byte: 40, prov: None },
            ],
            live: true,
        }],
    };
    let slice_val = Val::SlicePtr {
        ptr: PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize },
        len: 4,
    };
    assert_returned(
        &eval_body_with_caller_mem(
            &slice_ops_prog,
            0,
            &[slice_val.clone(), Val::usize_val(1)],
            slice_cm.clone(),
            64,
            &cfg,
        ),
        Val::Tuple(vec![
            Val::usize_val(4),
            Val::usize_val(3),
            Val::SlicePtr {
                ptr: PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize },
                len: 1,
            },
            Val::SlicePtr {
                ptr: PtrVal { alloc_id: Some(2), offset_bytes: 1, width: IntWidth::Isize },
                len: 3,
            },
        ]),
    );
    // Out-of-bounds `mid = 5` on length-4 slice triggers ReplayableMiriUb!
    match &eval_body_with_caller_mem(
        &slice_ops_prog,
        0,
        &[slice_val, Val::usize_val(5)],
        slice_cm,
        64,
        &cfg,
    )
    .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::SliceGetUncheckedOutOfBounds));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected Undefined(SliceGetUncheckedOutOfBounds), got {other:?}"),
    }

    // 4. `BinOp::Offset`, `CoreCallOp::PtrAdd`, `IntToPtr`, `PtrToPtr` (incl.
    //    `*const -> *mut` refusal), and zero-offset-dead conservative UB class.
    let ptr_arith_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            // Body 0: `ptr.offset(count)` then `PtrAdd(1)` then read `*ptr`.
            Body {
                arg_count: 2,
                is_unsafe: true,
                identity: "test::ptr_offset_and_add".into(),
                local_tys: vec![U32_TY, const_u32_ptr.clone(), ISIZE_TY, const_u32_ptr.clone()],
                blocks: vec![
                    Block {
                        statements: vec![Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Binary {
                                op: BinOp::Offset,
                                left: Operand::Copy { local: 1, projection: Vec::new() },
                                right: Operand::Copy { local: 2, projection: Vec::new() },
                            },
                        }],
                        terminator: Terminator::CoreCall {
                            op: CoreCallOp::PtrAdd {
                                mutability: Mutability::Shared,
                                pointee: U32_TY,
                            },
                            args: vec![
                                Operand::Copy { local: 3, projection: Vec::new() },
                                Operand::Constant {
                                    ty: USIZE_TY,
                                    lit: ConstLit::Scalar { bits: 0 },
                                },
                            ],
                            dst: Place { local: 3, projection: Vec::new() },
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block {
                        statements: vec![Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 3,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        }],
                        terminator: Terminator::Ret,
                        cleanup: false,
                    },
                ],
            },
            // Body 1: `IntToPtr` + `*const -> *mut` refusal (`Unsupported`).
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::const_to_mut_cast".into(),
                local_tys: vec![mut_u32_ptr.clone(), USIZE_TY, const_u32_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Cast {
                                cast_kind: CastKind::IntToPtr,
                                operand: Operand::Copy { local: 1, projection: Vec::new() },
                                ty: const_u32_ptr.clone(),
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Cast {
                                cast_kind: CastKind::PtrToPtr,
                                operand: Operand::Copy { local: 2, projection: Vec::new() },
                                ty: mut_u32_ptr.clone(),
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 2: `PtrAdd(0)` on raw ptr (for zero-offset-dead contrast).
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::zero_offset".into(),
                local_tys: vec![const_u32_ptr.clone(), const_u32_ptr.clone()],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::CoreCall {
                            op: CoreCallOp::PtrAdd {
                                mutability: Mutability::Shared,
                                pointee: U32_TY,
                            },
                            args: vec![
                                Operand::Copy { local: 1, projection: Vec::new() },
                                Operand::Constant {
                                    ty: USIZE_TY,
                                    lit: ConstLit::Scalar { bits: 0 },
                                },
                            ],
                            dst: Place { local: 0, projection: Vec::new() },
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                ],
            },
        ],
    };
    let mut arr_bytes = encode_val(TargetEndian::Little, &U32_TY, &Val::u32(100), true).unwrap();
    arr_bytes.extend(encode_val(TargetEndian::Little, &U32_TY, &Val::u32(200), true).unwrap());
    let arr_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Shared,
            bytes: arr_bytes,
            live: true,
        }],
    };
    let p0 = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    assert_returned(
        &eval_body_with_caller_mem(
            &ptr_arith_prog,
            0,
            &[p0.clone(), Val::isize_val(1)],
            arr_cm.clone(),
            32,
            &cfg,
        ),
        Val::u32(200),
    );
    // Negative offset from element 1 back to element 0.
    let p1 = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 4, width: IntWidth::Isize });
    assert_returned(
        &eval_body_with_caller_mem(
            &ptr_arith_prog,
            0,
            &[p1, Val::isize_val(-1)],
            arr_cm.clone(),
            32,
            &cfg,
        ),
        Val::u32(100),
    );
    // Out-of-bounds offset (+3 elems in 2-elem alloc) -> ReplayableMiriUb.
    match &eval_body_with_caller_mem(&ptr_arith_prog, 0, &[p0, Val::isize_val(3)], arr_cm, 32, &cfg)
        .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::PtrOffsetOverflowOrOob));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected PtrOffsetOverflowOrOob, got {other:?}"),
    }
    // `*const -> *mut` PtrToPtr cast fails closed with Unsupported.
    assert_fault(
        &eval_body_with_config(&ptr_arith_prog, 1, &[Val::usize_val(0x1000)], 32, &cfg),
        FaultKind::Unsupported,
    );
    // Zero-offset `PtrAdd(0)`: provenance-free ptr succeeds (`ptrAddInMem`),
    // while a dead provenance-backed pointer faults conservative
    // `ModelOnlyUnreplayed` (`ZeroOffsetDeadOrOobPtr`).
    let dangling = Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 4, width: IntWidth::Isize });
    assert_returned(
        &eval_body_with_config(&ptr_arith_prog, 2, std::slice::from_ref(&dangling), 32, &cfg),
        dangling,
    );
    let dead_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Shared,
            bytes: vec![AllocByte::Init { byte: 0, prov: None }; 4],
            live: false,
        }],
    };
    let dead_ptr = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    match &eval_body_with_caller_mem(&ptr_arith_prog, 2, &[dead_ptr], dead_cm, 32, &cfg).outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::ZeroOffsetDeadOrOobPtr));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("expected ZeroOffsetDeadOrOobPtr, got {other:?}"),
    }

    // 5. `Ref` stack promotion + escaping stack reference (`StackRefEscaped`),
    //    `&mut` from `&` refusal (`Unsupported`), `OverlappingMutRefsReturned`,
    //    and `bodyMixesRefsAndRawPtrsV2` refusal (`Unsupported`).
    let stack_escape_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            // Body 0: returns `&local_u32` -> `Undefined(StackRefEscaped)`.
            Body {
                arg_count: 1,
                is_unsafe: false,
                identity: "test::stack_escape".into(),
                local_tys: vec![shared_u32_ref.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Ref {
                            mutability: Mutability::Shared,
                            place: Place { local: 1, projection: Vec::new() },
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 1: returns `(&mut *r, &mut *r)` ->
            // `Undefined(OverlappingMutRefsReturned)`.
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::overlapping_mut_ret".into(),
                local_tys: vec![
                    Ty::Tuple { fields: vec![mut_u32_ref.clone(), mut_u32_ref.clone()] },
                    mut_u32_ref.clone(),
                    mut_u32_ref.clone(),
                    mut_u32_ref.clone(),
                ],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Ref {
                                mutability: Mutability::Mut,
                                place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Ref {
                                mutability: Mutability::Mut,
                                place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::AggregateTuple {
                                fields: vec![
                                    Operand::Move { local: 2, projection: Vec::new() },
                                    Operand::Move { local: 3, projection: Vec::new() },
                                ],
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 2: mixes `Ty::Ref` and `Ty::RawPtr` -> fails
            // `bodyMixesRefsAndRawPtrsV2`.
            Body {
                arg_count: 0,
                is_unsafe: false,
                identity: "test::mixed_ref_raw".into(),
                local_tys: vec![Ty::Unit, shared_u32_ref, const_u32_ptr],
                blocks: vec![Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
        ],
    };
    match &eval_body_with_config(&stack_escape_prog, 0, &[Val::u32(7)], 32, &cfg).outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::StackRefEscaped));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected StackRefEscaped, got {other:?}"),
    }
    let cm_mut = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Mut,
            bytes: encode_val(TargetEndian::Little, &U32_TY, &Val::u32(9), true).unwrap(),
            live: true,
        }],
    };
    match &eval_body_with_caller_mem(
        &stack_escape_prog,
        1,
        &[Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize })],
        cm_mut,
        32,
        &cfg,
    )
    .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::OverlappingMutRefsReturned));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected OverlappingMutRefsReturned, got {other:?}"),
    }
    assert_fault(
        &eval_body_with_config(&stack_escape_prog, 2, &[], 32, &cfg),
        FaultKind::Unsupported,
    );
}

#[test]
fn real_zerocopy_06_byte_slice_into_byte_slice_evaluates_and_probes_cleanly() {
    // Captured verbatim from `zerocopy/proofs/06_byte_slice_into_byte_slice`
    // via `anneal-rustc-capture` (schema version 5, Profile v2).
    const CAPTURE_JSON: &str =
        include_str!("fixtures/zerocopy_06_byte_slice_into_byte_slice_capture.json");
    let input = CaptureInput::from_json_str(CAPTURE_JSON).unwrap();
    let CaptureInput::Manifest(manifest) = input else {
        panic!("expected schema-v5 capture manifest");
    };
    assert_eq!(manifest.schema_version, anneal_mir_eval::CAPTURE_SCHEMA_VERSION);
    assert_eq!(manifest.program.mir_profile_version, 2);
    assert_eq!(manifest.program.bodies.len(), 3);

    let endian = TargetEndian::from_manifest_str(&manifest.configuration.endian);
    let cfg = EvalConfig::for_program(&manifest.program, endian).unwrap();
    assert!(cfg.enable_profile_v2());

    for body_id in 0..manifest.program.bodies.len() {
        let report = probe_body(
            &manifest.program,
            body_id,
            &ProbeConfig { max_cases: 32, fuel: 128, seed: 1 },
            &cfg,
        );
        assert!(report.cases_run > 0, "body {body_id}: {report:?}");
        assert_eq!(report.returned_count, report.cases_run, "body {body_id}: {report:?}");
        assert_eq!(report.undefined_count, 0, "body {body_id}: {report:?}");
        assert_eq!(report.unsupported_count, 0, "body {body_id}: {report:?}");
        assert_eq!(report.out_of_fuel_count, 0, "body {body_id}: {report:?}");
    }
}

#[test]
fn real_zerocopy_08_byte_slice_split_at_unchecked_evaluates_and_probes() {
    // Captured verbatim from `zerocopy/proofs/08_byte_slice_split_at_unchecked`
    // (`<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked`, schema 5,
    // Profile v2).
    const CAPTURE_JSON: &str =
        include_str!("fixtures/zerocopy_08_byte_slice_split_at_unchecked_capture.json");
    let input = CaptureInput::from_json_str(CAPTURE_JSON).unwrap();
    let CaptureInput::Manifest(manifest) = input else {
        panic!("expected schema-v5 capture manifest");
    };
    assert_eq!(manifest.schema_version, anneal_mir_eval::CAPTURE_SCHEMA_VERSION);
    assert_eq!(manifest.program.mir_profile_version, 2);
    assert_eq!(manifest.program.bodies.len(), 1);
    assert_eq!(
        manifest.program.bodies[0].identity,
        "rust-path-v1::<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"
    );
    assert!(manifest.program.bodies[0].is_unsafe);

    let endian = TargetEndian::from_manifest_str(&manifest.configuration.endian);
    let cfg = EvalConfig::for_program(&manifest.program, endian).unwrap();
    assert!(cfg.enable_profile_v2());

    // Valid in-bounds splits: mid = 0, 2, 4 on a 4-byte slice.
    let cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 0,
            mutability: Mutability::Shared,
            bytes: vec![
                AllocByte::Init { byte: 10, prov: None },
                AllocByte::Init { byte: 20, prov: None },
                AllocByte::Init { byte: 30, prov: None },
                AllocByte::Init { byte: 40, prov: None },
            ],
            live: true,
        }],
    };
    let slice_4 = Val::SlicePtr {
        ptr: PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize },
        len: 4,
    };
    for mid in [0u64, 2, 4] {
        let trace = eval_body_with_caller_mem(
            &manifest.program,
            0,
            &[slice_4.clone(), Val::usize_val(mid)],
            cm.clone(),
            128,
            &cfg,
        );
        assert_returned(
            &trace,
            Val::Tuple(vec![
                Val::SlicePtr {
                    ptr: PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize },
                    len: mid,
                },
                Val::SlicePtr {
                    ptr: PtrVal { alloc_id: Some(2), offset_bytes: mid, width: IntWidth::Isize },
                    len: 4 - mid,
                },
            ]),
        );
    }

    // Valid dangling empty slice (`NonNull::dangling()`, `len = 0`, `mid = 0`).
    let dangling_empty = Val::SlicePtr {
        ptr: PtrVal { alloc_id: None, offset_bytes: 1, width: IntWidth::Isize },
        len: 0,
    };
    assert_returned(
        &eval_body_with_caller_mem(
            &manifest.program,
            0,
            &[dangling_empty.clone(), Val::usize_val(0)],
            CallerMemory::default(),
            128,
            &cfg,
        ),
        Val::Tuple(vec![dangling_empty.clone(), dangling_empty]),
    );

    // Out-of-bounds `mid = 5` on length-4 slice -> ReplayableMiriUb!
    let oob_trace = eval_body_with_caller_mem(
        &manifest.program,
        0,
        &[slice_4, Val::usize_val(5)],
        cm,
        128,
        &cfg,
    );
    match &oob_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::SliceGetUncheckedOutOfBounds));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected Undefined(SliceGetUncheckedOutOfBounds), got {other:?}"),
    }

    // Entry-invalid null `&[u8]` -> ModelOnlyUnreplayed (`EntryInvalidRefArg`).
    let null_slice = Val::SlicePtr {
        ptr: PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize },
        len: 0,
    };
    let null_trace = eval_body_with_caller_mem(
        &manifest.program,
        0,
        &[null_slice, Val::usize_val(0)],
        CallerMemory::default(),
        128,
        &cfg,
    );
    match &null_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::EntryInvalidRefArg));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("expected Undefined(EntryInvalidRefArg), got {other:?}"),
    }

    // Probing skips unsafe by default (`skip_unsafe = true`), and discovers
    // concrete `ReplayableMiriUb` OOB witnesses when `skip_unsafe = false`.
    let skipped = probe_body_with_policy(&manifest.program, 0, &ProbeConfig::default(), &cfg, true);
    assert!(skipped.skipped_unsafe);
    assert_eq!(skipped.cases_run, 0);
    assert_eq!(skipped.unsupported_count, 0);

    let probed =
        probe_body(&manifest.program, 0, &ProbeConfig { max_cases: 48, fuel: 128, seed: 1 }, &cfg);
    assert!(!probed.skipped_unsafe);
    assert_eq!(probed.unsupported_count, 0, "{probed:?}");
    assert!(probed.returned_count > 0, "{probed:?}");
    assert!(probed.replayable_ub_count > 0, "{probed:?}");
    assert_eq!(probed.model_only_unreplayed_ub_count, 0, "{probed:?}");
    let ce = probed.first_replayable_undefined.as_ref().expect("expected replayable UB witness");
    assert_eq!(ce.witness_class, Some(WitnessClass::ReplayableMiriUb));
}

#[test]
fn move_on_never_init_and_indirect_move_ret_field_classification() {
    let v1_cfg = EvalConfig::profile_v1();
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);

    // 1. `Operand::Move` on a never-initialized local classifies as
    //    `ReplayableMiriUb` (`UninitLocalRead`), NOT `MoveDeinitLocalRead`, in
    //    both Profile v1 and Profile v2.
    for (ver, cfg) in [(1u32, &v1_cfg), (2u32, &v2_cfg)] {
        let prog = Program {
            scope: Scope::Crate,
            entry_def_id: 0,
            pointer_width_bits: 64,
            mir_profile_version: ver,
            overflow_checks: false,
            bodies: vec![Body {
                arg_count: 0,
                is_unsafe: false,
                identity: "test::move_never_init".into(),
                local_tys: vec![U32_TY, U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            }],
        };
        match &eval_body_with_config(&prog, 0, &[], 16, cfg).outcome {
            Outcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "v{ver}: {f:?}");
                assert_eq!(f.ub_class, Some(UbClass::UninitLocalRead), "v{ver}: {f:?}");
                assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
            }
            other => panic!("v{ver}: expected UninitLocalRead, got {other:?}"),
        }

        // Indirect never-initialized local read via `Move` also classifies as
        // `ReplayableMiriUb` (never `MoveDeinitLocalRead`).
        let mut st = MachineState::init(&prog, 0, &[], cfg).unwrap();
        assert!(matches!(st.step(&prog, cfg), StepOutcome::Stepped { .. }));
        st.force_allocation(&prog, 1, cfg).unwrap();
        match st.step(&prog, cfg) {
            StepOutcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "v{ver} indirect: {f:?}");
                assert_eq!(f.ub_class, Some(UbClass::UninitMemoryRead), "v{ver} indirect: {f:?}");
                assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
            }
            other => panic!("v{ver} indirect: expected UninitMemoryRead, got {other:?}"),
        }
    }

    // 2. Moving an initialized indirect `_0` then executing `Ret` classifies as
    //    `MoveDeinitLocalRead` (`ModelOnlyUnreplayed`) in both v1 and v2; a
    //    never-initialized indirect `_0` still classifies as `UninitMemoryRead`
    //    (`ReplayableMiriUb`).
    for (ver, cfg) in [(1u32, &v1_cfg), (2u32, &v2_cfg)] {
        let prog = Program {
            scope: Scope::Crate,
            entry_def_id: 0,
            pointer_width_bits: 64,
            mir_profile_version: ver,
            overflow_checks: false,
            bodies: vec![
                Body {
                    arg_count: 1,
                    is_unsafe: false,
                    identity: "test::indirect_ret_after_move".into(),
                    local_tys: vec![U32_TY, U32_TY, U32_TY],
                    blocks: vec![Block {
                        statements: vec![
                            Statement::Assign {
                                local: 0,
                                projection: Vec::new(),
                                value: Rvalue::Use {
                                    operand: Operand::Copy { local: 1, projection: Vec::new() },
                                    with_retag: false,
                                },
                            },
                            Statement::Assign {
                                local: 2,
                                projection: Vec::new(),
                                value: Rvalue::Use {
                                    operand: Operand::Move { local: 0, projection: Vec::new() },
                                    with_retag: false,
                                },
                            },
                        ],
                        terminator: Terminator::Ret,
                        cleanup: false,
                    }],
                },
                Body {
                    arg_count: 0,
                    is_unsafe: false,
                    identity: "test::indirect_ret_never_init".into(),
                    local_tys: vec![U32_TY],
                    blocks: vec![Block {
                        statements: Vec::new(),
                        terminator: Terminator::Ret,
                        cleanup: false,
                    }],
                },
            ],
        };
        let mut st_moved = MachineState::init(&prog, 0, &[Val::u32(7)], cfg).unwrap();
        assert!(matches!(st_moved.step(&prog, cfg), StepOutcome::Stepped { .. }));
        st_moved.force_allocation(&prog, 0, cfg).unwrap();
        assert!(matches!(st_moved.step(&prog, cfg), StepOutcome::Stepped { .. }));
        match st_moved.step(&prog, cfg) {
            StepOutcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "v{ver}: {f:?}");
                assert_eq!(f.ub_class, Some(UbClass::MoveDeinitLocalRead), "v{ver}: {f:?}");
                assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
            }
            other => panic!("v{ver}: expected MoveDeinitLocalRead on indirect Ret, got {other:?}"),
        }

        let mut st_uninit = MachineState::init(&prog, 1, &[], cfg).unwrap();
        st_uninit.force_allocation(&prog, 0, cfg).unwrap();
        match st_uninit.step(&prog, cfg) {
            StepOutcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "v{ver}: {f:?}");
                assert_eq!(f.ub_class, Some(UbClass::UninitMemoryRead), "v{ver}: {f:?}");
                assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
            }
            other => panic!("v{ver}: expected UninitMemoryRead on indirect Ret, got {other:?}"),
        }
    }

    // 3. Profile v2 indirect overflow-pair field `Copy`: after `Move` ->
    //    `MoveDeinitLocalRead` (`ModelOnlyUnreplayed`); never initialized ->
    //    `UninitMemoryRead` (`ReplayableMiriUb`).
    let ovf_ty = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
    let field_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            Body {
                arg_count: 1,
                is_unsafe: false,
                identity: "test::indirect_field_after_move".into(),
                local_tys: vec![U32_TY, ovf_ty.clone(), ovf_ty.clone()],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy {
                                    local: 1,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            Body {
                arg_count: 0,
                is_unsafe: false,
                identity: "test::indirect_field_never_init".into(),
                local_tys: vec![U32_TY, ovf_ty],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy {
                                local: 1,
                                projection: vec![ProjectionElem::Field {
                                    field_idx: 0,
                                    ty: U32_TY,
                                }],
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
        ],
    };
    let pair = Val::overflow_pair(ScalarVal::new(IntWidth::I32, false, 5), false);
    let mut st_field_moved = MachineState::init(&field_prog, 0, &[pair], &v2_cfg).unwrap();
    st_field_moved.force_allocation(&field_prog, 1, &v2_cfg).unwrap();
    assert!(matches!(st_field_moved.step(&field_prog, &v2_cfg), StepOutcome::Stepped { .. }));
    match st_field_moved.step(&field_prog, &v2_cfg) {
        StepOutcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::MoveDeinitLocalRead));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("expected MoveDeinitLocalRead on indirect field copy, got {other:?}"),
    }

    let mut st_field_uninit = MachineState::init(&field_prog, 1, &[], &v2_cfg).unwrap();
    st_field_uninit.force_allocation(&field_prog, 1, &v2_cfg).unwrap();
    match st_field_uninit.step(&field_prog, &v2_cfg) {
        StepOutcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::UninitMemoryRead));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected UninitMemoryRead on indirect field copy, got {other:?}"),
    }

    // 4. Profile v2 dereference load `CopyPlace(*_p)` reading uninitialized
    //    pointee memory classifies as `UninitMemoryRead` (`ReplayableMiriUb`),
    //    never consulting `moved_locals` on the pointer local `_p`.
    let const_u32_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let deref_uninit_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "test::deref_uninit_pointee".into(),
            local_tys: vec![U32_TY, const_u32_ptr],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    let uninit_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Uninit; 4],
            live: true,
        }],
    };
    let p_uninit = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    match &eval_body_with_caller_mem(&deref_uninit_prog, 0, &[p_uninit], uninit_cm, 16, &v2_cfg)
        .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::UninitMemoryRead));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected UninitMemoryRead on deref of uninit pointee, got {other:?}"),
    }

    // 5. `G2-R2-01`: Profile v2 `CopyPlace(*_2)` reading bytes deinitialized by
    //    `Move(_1)` classifies as `MoveDeinitLocalRead` (`ModelOnlyUnreplayed`)
    //    whether `AddressOf` occurred before or after `Move(_1)`, while reading
    //    a never-initialized indirect local via `*_2` stays `UninitMemoryRead`
    //    (`ReplayableMiriUb`), full re-initialization clears move-deinit
    //    tracking, and partial re-initialization still tracks the remaining
    //    move-deinitialized bytes separately from never-initialized bytes.
    let const_u32_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let mut_u32_ptr = Ty::RawPtr { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let mut_u16_ptr = Ty::RawPtr { mutability: Mutability::Mut, pointee: Box::new(U16_TY) };
    let move_deref_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            // Body 0: `_2 = &raw const _1; _3 = Move(_1); _0 = Copy(*_2)`
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::addr_then_move_then_deref".into(),
                local_tys: vec![U32_TY, U32_TY, const_u32_ptr.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Shared,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 2,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 1: `_3 = Move(_1); _2 = &raw const _1; _0 = Copy(*_2)`
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::move_then_addr_then_deref".into(),
                local_tys: vec![U32_TY, U32_TY, const_u32_ptr.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Shared,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 2,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 2: never-initialized `_1`, `_2 = &raw const _1; _0 = *_2`
            Body {
                arg_count: 0,
                is_unsafe: true,
                identity: "test::never_init_addr_then_deref".into(),
                local_tys: vec![U32_TY, U32_TY, const_u32_ptr],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Shared,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 2,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 3: `_2 = &raw mut _1; _3 = Move(_1); *_2 = 77; _0 = *_2`
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::move_then_reinit_via_ptr".into(),
                local_tys: vec![U32_TY, U32_TY, mut_u32_ptr.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Mut,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                        Statement::AssignPlace {
                            place: Place { local: 2, projection: vec![ProjectionElem::Deref] },
                            value: Rvalue::Use {
                                operand: Operand::Constant {
                                    ty: U32_TY,
                                    lit: ConstLit::Scalar { bits: 77 },
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 2,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 4: move `_1: u32`, overwrite low 2 bytes via `*mut u16`,
            // then read `u32` (`*_2`) -> remaining high 2 bytes are still
            // move-deinitialized (`MoveDeinitLocalRead`).
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::move_then_partial_reinit_then_deref".into(),
                local_tys: vec![U32_TY, U32_TY, mut_u32_ptr.clone(), U32_TY, mut_u16_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Mut,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Move { local: 1, projection: Vec::new() },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 4,
                            projection: Vec::new(),
                            value: Rvalue::Cast {
                                cast_kind: CastKind::PtrToPtr,
                                operand: Operand::Copy { local: 2, projection: Vec::new() },
                                ty: mut_u16_ptr.clone(),
                            },
                        },
                        Statement::AssignPlace {
                            place: Place { local: 4, projection: vec![ProjectionElem::Deref] },
                            value: Rvalue::Use {
                                operand: Operand::Constant {
                                    ty: U16_TY,
                                    lit: ConstLit::Scalar { bits: 0x1234 },
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 2,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 5: never-init `_1: u32`, write low 2 bytes via `*mut u16`,
            // then read `u32` (`*_2`) -> high 2 bytes were never initialized
            // (`UninitMemoryRead`, `ReplayableMiriUb`).
            Body {
                arg_count: 0,
                is_unsafe: true,
                identity: "test::never_init_partial_write_then_deref".into(),
                local_tys: vec![U32_TY, U32_TY, mut_u32_ptr, mut_u16_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Mut,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Cast {
                                cast_kind: CastKind::PtrToPtr,
                                operand: Operand::Copy { local: 2, projection: Vec::new() },
                                ty: mut_u16_ptr,
                            },
                        },
                        Statement::AssignPlace {
                            place: Place { local: 3, projection: vec![ProjectionElem::Deref] },
                            value: Rvalue::Use {
                                operand: Operand::Constant {
                                    ty: U16_TY,
                                    lit: ConstLit::Scalar { bits: 0x1234 },
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::CopyPlace {
                                    place: Place {
                                        local: 2,
                                        projection: vec![ProjectionElem::Deref],
                                    },
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
        ],
    };

    for (body_id, label) in [
        (0usize, "addr_then_move"),
        (1usize, "move_then_addr"),
        (4usize, "move_then_partial_reinit"),
    ] {
        match &eval_body_with_config(&move_deref_prog, body_id, &[Val::u32(42)], 16, &v2_cfg)
            .outcome
        {
            Outcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "{label}: {f:?}");
                assert_eq!(f.ub_class, Some(UbClass::MoveDeinitLocalRead), "{label}: {f:?}");
                assert_eq!(
                    f.witness_class(),
                    Some(WitnessClass::ModelOnlyUnreplayed),
                    "{label}: {f:?}"
                );
            }
            other => panic!("{label}: expected MoveDeinitLocalRead, got {other:?}"),
        }
    }
    for (body_id, label) in
        [(2usize, "never_init_addr_then_deref"), (5usize, "never_init_partial_write")]
    {
        match &eval_body_with_config(&move_deref_prog, body_id, &[], 16, &v2_cfg).outcome {
            Outcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "{label}: {f:?}");
                assert_eq!(f.ub_class, Some(UbClass::UninitMemoryRead), "{label}: {f:?}");
                assert_eq!(
                    f.witness_class(),
                    Some(WitnessClass::ReplayableMiriUb),
                    "{label}: {f:?}"
                );
            }
            other => panic!("{label}: expected UninitMemoryRead, got {other:?}"),
        }
    }
    assert_returned(
        &eval_body_with_config(&move_deref_prog, 3, &[Val::u32(42)], 16, &v2_cfg),
        Val::u32(77),
    );
}

#[test]
fn caller_memory_u64_max_rejected_and_stack_alloc_id_overflow_fails_closed() {
    let max_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: u64::MAX,
            align_log2: 2,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Init { byte: 0, prov: None }; 4],
            live: true,
        }],
    };
    assert!(!memory::valid_caller_memory(&max_cm));
    assert_eq!(
        memory::MemoryState::entry_memory_with_caller(&max_cm).unwrap_err().kind,
        FaultKind::Unsupported
    );

    let v2_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            identity: "test::u64_max_cm".into(),
            local_tys: vec![Ty::Unit],
            blocks: vec![Block {
                statements: Vec::new(),
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    assert_eq!(
        MachineState::init_with_caller_mem(&v2_prog, 0, &[], max_cm, &v2_cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );

    let mut exhausted = memory::MemoryState { next_alloc_id: u64::MAX, allocations: Vec::new() };
    assert_eq!(
        exhausted.try_allocate_stack(LayoutData { size: 4, align_log2: 2 }).unwrap_err().kind,
        FaultKind::Unsupported
    );
}

#[test]
fn fail_closed_witness_classification_and_profile_v2_aggregate_unit_endian_parity() {
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);

    // 1. `refs_valid_in_mem` converting `Unsupported` to `Undefined` and
    //    `refs_valid_in_mem_list` arity mismatch fail closed to
    //    `ModelOnlyUnreplayed` (unclassified).
    let mem = memory::MemoryState::entry_memory();
    let bad_ref_err = memory::refs_valid_in_mem(
        &mem,
        TargetEndian::Little,
        &Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(Ty::Unsupported) },
        &Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 1, width: IntWidth::Isize }),
    )
    .unwrap_err();
    assert_eq!(bad_ref_err.kind, FaultKind::Undefined);
    assert_eq!(bad_ref_err.ub_class, None);
    assert_eq!(bad_ref_err.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));

    let arity_err =
        memory::refs_valid_in_mem_list(&mem, TargetEndian::Little, &[U32_TY], &[]).unwrap_err();
    assert_eq!(arity_err.kind, FaultKind::Undefined);
    assert_eq!(arity_err.ub_class, None);
    assert_eq!(arity_err.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));

    // 2. Symbolic allocation alignment (`alloc.align < access_align`) reports
    //    `SymbolicAllocAlignment` (`ModelOnlyUnreplayed`), whereas guaranteed
    //    offset misalignment reports `MisalignedMemoryAccess`
    //    (`ReplayableMiriUb`).
    let sym_mem = memory::MemoryState {
        next_alloc_id: 10,
        allocations: vec![
            Allocation {
                alloc_id: 2,
                align_log2: 0,
                mutability: Mutability::Mut,
                bytes: vec![AllocByte::Init { byte: 0, prov: None }; 8],
                live: true,
            },
            Allocation {
                alloc_id: 3,
                align_log2: 2,
                mutability: Mutability::Mut,
                bytes: vec![AllocByte::Init { byte: 0, prov: None }; 8],
                live: true,
            },
        ],
    };
    let sym_err =
        sym_mem.read_bytes(memory::MemPlace { alloc_id: 2, offset: 0 }, 4, 2).unwrap_err();
    assert_eq!(sym_err.ub_class, Some(UbClass::SymbolicAllocAlignment));
    assert_eq!(sym_err.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));

    let concrete_err =
        sym_mem.read_bytes(memory::MemPlace { alloc_id: 3, offset: 1 }, 4, 2).unwrap_err();
    assert_eq!(concrete_err.ub_class, Some(UbClass::MisalignedMemoryAccess));
    assert_eq!(concrete_err.witness_class(), Some(WitnessClass::ReplayableMiriUb));

    // 3. Synthetic MIR-unreachable guards and conservative `PtrMetadata` on
    //    `Ty::Ref` classify as `ModelOnlyUnreplayed`.
    let const_u32_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let mut_u32_ptr = Ty::RawPtr { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let shared_u32_ref = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let mut_u32_ref = Ty::Ref { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let slice_u8_ref = Ty::Ref {
        mutability: Mutability::Shared,
        pointee: Box::new(Ty::Slice { elem: Box::new(U8_TY) }),
    };
    let mut_slice_u8_ref = Ty::Ref {
        mutability: Mutability::Mut,
        pointee: Box::new(Ty::Slice { elem: Box::new(U8_TY) }),
    };
    let range_to_ty = Ty::RangeTo { elem: Box::new(USIZE_TY) };

    let synth_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![
            // Body 0: synthetic write through `*const u32`.
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::write_const_ptr".into(),
                local_tys: vec![Ty::Unit, const_u32_ptr.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::AssignPlace {
                        place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 1 },
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 1: synthetic `&mut *shared_ref`.
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::mut_reborrow_shared".into(),
                local_tys: vec![mut_u32_ref, shared_u32_ref.clone()],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Ref {
                            mutability: Mutability::Mut,
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 2: synthetic `&raw mut *const_ptr`.
            Body {
                arg_count: 1,
                is_unsafe: true,
                identity: "test::mut_raw_reborrow_const".into(),
                local_tys: vec![mut_u32_ptr, const_u32_ptr],
                blocks: vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::AddressOf {
                            mutability: Mutability::Mut,
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
            // Body 3: synthetic `SliceGetUncheckedRangeTo` producing
            // `&mut [u8]` from `&[u8]`.
            Body {
                arg_count: 2,
                is_unsafe: true,
                identity: "test::get_unchecked_mut_from_shared".into(),
                local_tys: vec![mut_slice_u8_ref, slice_u8_ref.clone(), range_to_ty],
                blocks: vec![
                    Block {
                        statements: Vec::new(),
                        terminator: Terminator::CoreCall {
                            op: CoreCallOp::SliceGetUncheckedRangeTo,
                            args: vec![
                                Operand::Copy { local: 1, projection: Vec::new() },
                                Operand::Copy { local: 2, projection: Vec::new() },
                            ],
                            dst: Place { local: 0, projection: Vec::new() },
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block { statements: Vec::new(), terminator: Terminator::Ret, cleanup: false },
                ],
            },
            // Body 4: `PtrMetadata` on a `&u32` whose target was freed mid-body
            // (conservative `refValidInMem` re-check -> `ModelOnlyUnreplayed`).
            Body {
                arg_count: 0,
                is_unsafe: true,
                identity: "test::ptr_metadata_dead_ref".into(),
                local_tys: vec![Ty::Unit, U32_TY, shared_u32_ref],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 1,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Constant {
                                    ty: U32_TY,
                                    lit: ConstLit::Scalar { bits: 9 },
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Ref {
                                mutability: Mutability::Shared,
                                place: Place { local: 1, projection: Vec::new() },
                            },
                        },
                        Statement::StorageDead { local: 1 },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Unary {
                                op: UnOp::PtrMetadata,
                                operand: Operand::Copy { local: 2, projection: Vec::new() },
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
            },
        ],
    };

    let valid_u32_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Shared,
            bytes: encode_val(TargetEndian::Little, &U32_TY, &Val::u32(7), true).unwrap(),
            live: true,
        }],
    };
    let p2 = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    for body_id in [0usize, 1, 2] {
        match &eval_body_with_caller_mem(
            &synth_prog,
            body_id,
            std::slice::from_ref(&p2),
            valid_u32_cm.clone(),
            32,
            &v2_cfg,
        )
        .outcome
        {
            Outcome::Fault(f) => {
                assert_eq!(f.kind, FaultKind::Undefined, "body {body_id}: {f:?}");
                assert_eq!(
                    f.witness_class(),
                    Some(WitnessClass::ModelOnlyUnreplayed),
                    "body {body_id}: {f:?}"
                );
            }
            other => panic!("body {body_id}: expected ModelOnlyUnreplayed, got {other:?}"),
        }
    }
    let slice_dangling = Val::SlicePtr {
        ptr: PtrVal { alloc_id: None, offset_bytes: 1, width: IntWidth::Isize },
        len: 0,
    };
    match &eval_body_with_caller_mem(
        &synth_prog,
        3,
        &[slice_dangling, Val::RangeTo(0)],
        CallerMemory::default(),
        32,
        &v2_cfg,
    )
    .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("body 3: expected ModelOnlyUnreplayed, got {other:?}"),
    }
    match &eval_body_with_config(&synth_prog, 4, &[], 32, &v2_cfg).outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("body 4: expected ModelOnlyUnreplayed, got {other:?}"),
    }

    // 4. Schema-5 `AggregateTuple { fields: [] }` into `Ty::Unit` fails closed
    //    `Unsupported` (matching `Step.lean:1586-1597`), and Profile v2 fails
    //    closed on `TargetEndian::Big`.
    let agg_unit_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            identity: "test::agg_tuple_into_unit".into(),
            local_tys: vec![Ty::Unit],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::AggregateTuple { fields: Vec::new() },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    assert_fault(
        &eval_body_with_config(&agg_unit_prog, 0, &[], 16, &v2_cfg),
        FaultKind::Unsupported,
    );

    assert_eq!(
        EvalConfig::for_program(&agg_unit_prog, Some(TargetEndian::Big)).unwrap_err().kind,
        FaultKind::Unsupported
    );
    let big_v2 = EvalConfig::profile_v2(TargetEndian::Big);
    assert_eq!(
        validate_program_config(&agg_unit_prog, &big_v2).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_fault(
        &eval_body_with_config(&agg_unit_prog, 0, &[], 16, &big_v2),
        FaultKind::Unsupported,
    );
}

/// Returns whether any statement or terminator of `body` satisfies `pred`.
fn body_has(
    body: &Body,
    mut pred: impl FnMut(Option<&Statement>, Option<&Terminator>) -> bool,
) -> bool {
    body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| pred(Some(stmt), None)) || pred(None, Some(&bb.terminator))
    })
}

fn assign_rvalue(stmt: Option<&Statement>) -> Option<&Rvalue> {
    stmt.and_then(Statement::as_assign).map(|(_, _, rvalue)| rvalue)
}

#[test]
fn real_capture_schema5_rvalue_drift_fixture_parses_and_evaluates() {
    // Captured by `anneal-rustc-capture` (schema version 5, Profile v2,
    // `--scope crate`) from this crate, with unselected census rows elided
    // and host paths normalized:
    //
    //   #[repr(u8)]
    //   pub enum Step { First = 1, Second = 2, Third = 3 }
    //   pub fn step_value(s: Step) -> i32 {
    //       match s { Step::First => 10, Step::Second => 20, Step::Third => 30 }
    //   }
    //   pub fn array_literal(a: u8, b: u8) -> [u8; 2] { [a, b] }
    //   pub fn array_repeat(a: u8) -> [u8; 4] { [a; 4] }
    //   pub fn array_first(arr: [u8; 4]) -> u8 { let [first, ..] = arr; first }
    //   pub fn unsize(arr: &[u8; 4]) -> &[u8] { arr }
    //   pub fn le_bytes(x: u32) -> [u8; 4] { x.to_le_bytes() }
    //   pub fn array_eq(a: [u8; 2], b: [u8; 2]) -> bool { a == b }
    //   pub fn rodata() -> &'static [u8] { b"abc" }
    //
    // Before the evaluator's IR followed the capture serializer, this
    // manifest failed to load (`missing field 'local'` for the place-wrapped
    // `discriminant` rvalue, and unknown variants for the rest).
    const CAPTURE_JSON: &str = include_str!("fixtures/capture_schema5_rvalue_drift_capture.json");
    let CaptureInput::Manifest(manifest) = CaptureInput::from_json_str(CAPTURE_JSON).unwrap()
    else {
        panic!("expected schema-v5 capture manifest");
    };
    let program = &manifest.program;
    let identities: Vec<&str> = program.bodies.iter().map(|b| b.identity.as_str()).collect();
    assert_eq!(
        identities,
        [
            "rust-path-v1::step_value",
            "rust-path-v1::array_literal",
            "rust-path-v1::array_repeat",
            "rust-path-v1::array_first",
            "rust-path-v1::unsize",
            "rust-path-v1::le_bytes",
            "rust-path-v1::array_eq",
            "rust-path-v1::rodata",
        ]
    );

    // Every newly mirrored capture shape is present in the parsed program.
    let bodies = &program.bodies;
    assert!(body_has(&bodies[0], |s, _| matches!(
        assign_rvalue(s),
        Some(Rvalue::Discriminant { place }) if place.projection.is_empty()
    )));
    assert!(body_has(&bodies[1], |s, _| matches!(
        assign_rvalue(s),
        Some(Rvalue::AggregateArray { elems, .. }) if elems.len() == 2
    )));
    assert!(body_has(&bodies[2], |s, _| matches!(
        assign_rvalue(s),
        Some(Rvalue::Repeat { count: 4, .. })
    )));
    assert!(body_has(&bodies[3], |s, _| {
        let Some(Rvalue::Use { operand, .. }) = assign_rvalue(s) else { return false };
        operand.as_place().is_some_and(|(_, proj, _)| {
            matches!(
                proj,
                [ProjectionElem::ConstantIndex { offset: 0, min_length: 4, from_end: false }]
            )
        })
    }));
    assert!(body_has(&bodies[4], |s, _| matches!(
        assign_rvalue(s),
        Some(Rvalue::Cast { cast_kind: CastKind::Unsize, .. })
    )));
    assert!(body_has(&bodies[5], |_, t| matches!(
        t,
        Some(Terminator::CoreCall { op: CoreCallOp::IntToLeBytes { .. }, .. })
    )));
    assert!(body_has(&bodies[6], |_, t| matches!(
        t,
        Some(Terminator::CoreCall { op: CoreCallOp::ArrayEq { len: 2, .. }, .. })
    )));
    assert!(body_has(&bodies[7], |s, _| {
        let Some(Rvalue::UseRetag { operand: Operand::Constant { lit, .. } }) = assign_rvalue(s)
        else {
            return false;
        };
        matches!(lit, ConstLit::RodataRef { bytes, slice_len: None, .. } if bytes.len() == 3)
    }));

    // The captured enum `match` evaluates end to end.
    let endian = TargetEndian::from_manifest_str(&manifest.configuration.endian);
    let cfg = EvalConfig::for_program(program, endian).unwrap();
    let Some(Ty::Enum(step_ty)) = bodies[0].local_tys.get(1) else {
        panic!("expected enum parameter");
    };
    for (variant, expected) in [(0usize, 10u128), (1, 20), (2, 30)] {
        let arg = Val::EnumVal { ty: step_ty.clone(), variant };
        let trace = eval_body_with_config(program, 0, &[arg], 64, &cfg);
        assert_returned(&trace, Val::Scalar(ScalarVal::new(IntWidth::I32, true, expected)));
    }

    // The other bodies have array or array-reference locals, which are
    // outside the Profile v2 local fragment, so they fail closed at entry
    // validation before any step runs; the new shapes in them are never
    // evaluated here. `unmodeled_schema5_shapes_fail_closed_during_evaluation`
    // reaches each new arm directly.
    for (body_id, body) in bodies.iter().enumerate().skip(1) {
        let err = validate_body_entry(body, &cfg).unwrap_err();
        assert_eq!(err.kind, FaultKind::Unsupported, "body {body_id}");
        assert_eq!(err.reason, "body contains unsupported local variable type", "body {body_id}");
    }
    let trace = eval_body_with_config(program, 2, &[Val::u8(7)], 64, &cfg);
    assert_eq!(trace.steps_executed, 0);
    assert_fault(&trace, FaultKind::Unsupported);
}

/// One-block body `fn(u8) -> ret_ty` (local 1 is the `u8` argument) running
/// `statements` and then `terminator`; `Terminator::Ret` is block 1.
fn unmodeled_shape_program(
    profile: u32,
    ret_ty: Ty,
    statements: Vec<Statement>,
    terminator: Terminator,
) -> Program {
    let mut program = single_unit_program(vec![Body {
        arg_count: 1,
        is_unsafe: false,
        local_tys: vec![ret_ty, U8_TY],
        blocks: vec![
            Block { statements, terminator, cleanup: false },
            Block { statements: Vec::new(), terminator: Terminator::Ret, cleanup: false },
        ],
        identity: "test::entry".into(),
    }]);
    program.mir_profile_version = profile;
    program
}

#[test]
fn unmodeled_schema5_shapes_fail_closed_during_evaluation() {
    // Every local is in the Profile v2 local fragment (and, except for the
    // `RodataRef` case's `&[u8]`, the v1 fragment), so entry validation
    // passes and each fault below comes from evaluating the shape, not from
    // `validate_body_entry`.
    const ENTRY_REASON: &str = "body contains unsupported local variable type";
    const V2_RVALUE: &str = "unmodeled Profile v2 MIR rvalue";
    const V1_RVALUE: &str = "unmodeled Profile v1 MIR rvalue";
    const PROJECTION: &str = "unsupported place projection element";
    const CORE_CALL: &str = "invalid CoreCallOp arguments or signature";
    const CONST_LIT: &str = "unsupported constant type/literal combination";
    const V1_PROJECTION: &str = "projected operand unsupported in Profile v1";
    const V1_TERMINATOR: &str = "unmodeled Profile v1 MIR terminator";

    let arg = || Operand::Copy { local: 1, projection: Vec::new() };
    let u8_slice_ref = Ty::Ref {
        mutability: Mutability::Shared,
        pointee: Box::new(Ty::Slice { elem: Box::new(U8_TY) }),
    };
    let rodata = vec![
        RodataByte::Init { byte: b'a' },
        RodataByte::Init { byte: b'b' },
        RodataByte::Init { byte: b'c' },
    ];
    let assign = |ret_ty: Ty, value: Rvalue| {
        (
            ret_ty,
            vec![Statement::Assign { local: 0, projection: Vec::new(), value }],
            Terminator::Goto { block: 1 },
        )
    };
    let core_call = |op: CoreCallOp| {
        (
            Ty::Bool,
            Vec::new(),
            Terminator::CoreCall {
                op,
                args: vec![arg()],
                dst: Place::local(0),
                target: Some(1),
                unwind: UnwindAction::Continue,
            },
        )
    };
    let use_const = |ret_ty: Ty, ty: Ty, lit: ConstLit| {
        assign(ret_ty, Rvalue::Use { operand: Operand::Constant { ty, lit }, with_retag: false })
    };

    let cases = vec![
        (
            "ProjectionElem::ConstantIndex",
            assign(
                U8_TY,
                Rvalue::Use {
                    operand: Operand::Copy {
                        local: 1,
                        projection: vec![ProjectionElem::ConstantIndex {
                            offset: 0,
                            min_length: 1,
                            from_end: false,
                        }],
                    },
                    with_retag: false,
                },
            ),
            PROJECTION,
            Some(V1_PROJECTION),
        ),
        (
            "CastKind::Unsize",
            assign(
                Ty::Unit,
                Rvalue::Cast {
                    cast_kind: CastKind::Unsize,
                    operand: arg(),
                    ty: u8_slice_ref.clone(),
                },
            ),
            V2_RVALUE,
            Some(V1_RVALUE),
        ),
        (
            "Rvalue::AggregateArray",
            assign(Ty::Unit, Rvalue::AggregateArray { elem_ty: U8_TY, elems: vec![arg()] }),
            V2_RVALUE,
            Some(V1_RVALUE),
        ),
        (
            "Rvalue::Repeat",
            assign(Ty::Unit, Rvalue::Repeat { operand: arg(), elem_ty: U8_TY, count: 4 }),
            V2_RVALUE,
            Some(V1_RVALUE),
        ),
        (
            "CoreCallOp::IntToLeBytes",
            core_call(CoreCallOp::IntToLeBytes {
                int_ty: IntTy { width: IntWidth::I8, signed: false },
            }),
            CORE_CALL,
            Some(V1_TERMINATOR),
        ),
        (
            "CoreCallOp::ArrayEq",
            core_call(CoreCallOp::ArrayEq { elem: U8_TY, len: 1 }),
            CORE_CALL,
            Some(V1_TERMINATOR),
        ),
        (
            "ConstLit::RodataBytes",
            use_const(
                Ty::Unit,
                Ty::Array { elem: Box::new(U8_TY), len: 3 },
                ConstLit::RodataBytes { bytes: rodata.clone() },
            ),
            CONST_LIT,
            Some(CONST_LIT),
        ),
        (
            "ConstLit::RodataRef",
            use_const(
                u8_slice_ref.clone(),
                u8_slice_ref.clone(),
                ConstLit::RodataRef {
                    bytes: rodata,
                    align_log2: 0,
                    offset_bytes: 0,
                    slice_len: Some(3),
                },
            ),
            CONST_LIT,
            None,
        ),
    ];

    for (name, (ret_ty, statements, terminator), v2_reason, v1_reason) in cases {
        let v2 = unmodeled_shape_program(2, ret_ty.clone(), statements.clone(), terminator.clone());
        let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
        assert_eq!(
            validate_body_entry(&v2.bodies[0], &v2_cfg).map_err(|e| e.reason),
            Ok(()),
            "{name}: v2 entry"
        );
        let trace = eval_body_with_config(&v2, 0, &[Val::u8(7)], 16, &v2_cfg);
        let Outcome::Fault(detail) = &trace.outcome else {
            panic!("{name}: expected a v2 fault, got {:?}", trace.outcome);
        };
        assert_eq!(detail.kind, FaultKind::Unsupported, "{name}: v2 {detail:?}");
        assert_ne!(detail.reason, ENTRY_REASON, "{name}: v2");
        assert_eq!(detail.reason, v2_reason, "{name}: v2");

        // Profile v1 rejects projected operands and core calls before
        // reaching these arms, and reference locals are outside its local
        // fragment, so `RodataRef` is v2-only.
        let Some(v1_reason) = v1_reason else { continue };
        let v1 = unmodeled_shape_program(1, ret_ty, statements, terminator);
        let v1_cfg = EvalConfig::for_program(&v1, Some(TargetEndian::Little)).unwrap();
        assert!(!v1_cfg.enable_profile_v2(), "{name}");
        assert_eq!(
            validate_body_entry(&v1.bodies[0], &v1_cfg).map_err(|e| e.reason),
            Ok(()),
            "{name}: v1 entry"
        );
        let trace = eval_body_with_config(&v1, 0, &[Val::u8(7)], 16, &v1_cfg);
        let Outcome::Fault(detail) = &trace.outcome else {
            panic!("{name}: expected a v1 fault, got {:?}", trace.outcome);
        };
        assert_eq!(detail.kind, FaultKind::Unsupported, "{name}: v1 {detail:?}");
        assert_ne!(detail.reason, ENTRY_REASON, "{name}: v1");
        assert_eq!(detail.reason, v1_reason, "{name}: v1");
    }
}

#[test]
fn capture_json_shapes_round_trip_and_legacy_discriminant_is_rejected() {
    let discr: Rvalue =
        serde_json::from_str(r#"{"kind":"discriminant","place":{"local":1,"projection":[]}}"#)
            .unwrap();
    assert_eq!(discr, Rvalue::Discriminant { place: Place::local(1) });
    // The pre-place flat shape is no longer emitted by the capture tool and
    // must not be accepted silently.
    assert!(serde_json::from_str::<Rvalue>(r#"{"kind":"discriminant","local":1}"#).is_err());

    for json in [
        r#"{"kind":"aggregate_array","elem_ty":{"kind":"bool"},"elems":[]}"#,
        r#"{"kind":"repeat","operand":{"kind":"copy","local":1},"elem_ty":{"kind":"bool"},"count":3}"#,
        r#"{"kind":"cast","cast_kind":"unsize","operand":{"kind":"copy","local":1},"ty":{"kind":"unit"}}"#,
    ] {
        let rvalue: Rvalue = serde_json::from_str(json).unwrap();
        let encoded = serde_json::to_string(&rvalue).unwrap();
        assert_eq!(serde_json::from_str::<Rvalue>(&encoded).unwrap(), rvalue);
    }
    for json in [
        r#"{"kind":"rodata_bytes","bytes":[{"kind":"init","byte":1},{"kind":"uninit"}]}"#,
        r#"{"kind":"rodata_ref","bytes":[],"align_log2":0,"offset_bytes":0,"slice_len":null}"#,
    ] {
        let lit: ConstLit = serde_json::from_str(json).unwrap();
        let encoded = serde_json::to_string(&lit).unwrap();
        assert_eq!(serde_json::from_str::<ConstLit>(&encoded).unwrap(), lit);
    }
    let lit: ConstLit = serde_json::from_str(
        r#"{"kind":"rodata_bytes","bytes":[{"kind":"init","byte":1},{"kind":"uninit"}]}"#,
    )
    .unwrap();
    assert_eq!(
        lit,
        ConstLit::RodataBytes { bytes: vec![RodataByte::Init { byte: 1 }, RodataByte::Uninit] }
    );
    for json in [
        r#"{"kind":"int_to_le_bytes","int_ty":{"width":"i32","signed":false}}"#,
        r#"{"kind":"array_eq","elem":{"kind":"bool"},"len":2}"#,
    ] {
        let op: CoreCallOp = serde_json::from_str(json).unwrap();
        let encoded = serde_json::to_string(&op).unwrap();
        assert_eq!(serde_json::from_str::<CoreCallOp>(&encoded).unwrap(), op);
    }
    let elem: ProjectionElem = serde_json::from_str(
        r#"{"kind":"constant_index","offset":1,"min_length":2,"from_end":true}"#,
    )
    .unwrap();
    assert_eq!(elem, ProjectionElem::ConstantIndex { offset: 1, min_length: 2, from_end: true });
}

#[test]
fn entry_alloc_id_freshness_assign_overlap_ub_and_slice_elem_size_parity() {
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);

    // 1. PM-1a: `entry_memory_with_caller` advances `next_alloc_id` past byte-level
    //    provenance ids (`prov: Some(7)` inside `alloc_id = 2` -> `next_alloc_id = 8`).
    let cm_prov = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 0,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Init { byte: 0, prov: Some(7) }],
            live: true,
        }],
    };
    let entry_prov = memory::MemoryState::entry_memory_with_caller(&cm_prov).unwrap();
    assert_eq!(entry_prov.next_alloc_id, 8);

    // 2. PM-1b: Dangling raw pointer `p = (Some(2), 0)` with empty `caller_mem`
    //    must fault `DanglingOrUnknownAllocAccess` even after callee promotes a
    //    stack local `_2: u8 = 42` via `&raw const _2`.
    let raw_u8_const = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U8_TY) };
    let dangling_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "test::dangling_raw_ptr_vs_stack_alloc".into(),
            local_tys: vec![U8_TY, raw_u8_const.clone(), U8_TY, raw_u8_const.clone()],
            blocks: vec![Block {
                statements: vec![
                    Statement::StorageLive { local: 2 },
                    Statement::Assign {
                        local: 2,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U8_TY,
                                lit: ConstLit::Scalar { bits: 42 },
                            },
                            with_retag: false,
                        },
                    },
                    Statement::StorageLive { local: 3 },
                    Statement::Assign {
                        local: 3,
                        projection: Vec::new(),
                        value: Rvalue::AddressOf {
                            mutability: Mutability::Shared,
                            place: Place { local: 2, projection: Vec::new() },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy {
                                local: 1,
                                projection: vec![ProjectionElem::Deref],
                            },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    let dangling_arg =
        Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    match &eval_body_with_caller_mem(
        &dangling_prog,
        0,
        &[dangling_arg],
        CallerMemory::default(),
        32,
        &v2_cfg,
    )
    .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::DanglingOrUnknownAllocAccess));
        }
        other => panic!("expected DanglingOrUnknownAllocAccess, got {other:?}"),
    }

    // 3. PM-3: Overlapping `Assign`:
    //    - `(u32, u32, u32)` (`BackendRepr::Memory`), alignment-inflated tuples
    //      such as `([u64; 0], u32, u32)` (`BackendRepr::Memory`), and in-memory
    //      `(u32, bool)` (`*p = *p`) fault `UbClass::OverlappingMemoryCopy`
    //      (`ReplayableMiriUb`),
    //    - immediate padded `(u32, bool)` local faults
    //      `UbClass::ConservativeOverlappingAssignCopy` (`ModelOnlyUnreplayed`),
    //    - unpadded `(u32, u32)` and `(u8, bool)` succeed,
    //    - clobbering `a = (a.1, a.0)` and deref-pointer clobbering in an
    //      `Aggregate` fail closed `Unsupported`.
    let tup3_ty = Ty::Tuple { fields: vec![U32_TY, U32_TY, U32_TY] };
    let tup2_ty = Ty::Tuple { fields: vec![U32_TY, U32_TY] };
    let padded_ovf_ty = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
    let unpadded_ovf_ty = Ty::OverflowPair(IntTy { width: IntWidth::I8, signed: false });

    let mk_self_assign_prog = |ty: Ty| Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            identity: "test::self_assign".into(),
            local_tys: vec![Ty::Unit, ty],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 1,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1, projection: Vec::new() },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };

    let v_u32_1 = Val::Scalar(ScalarVal::new(IntWidth::I32, false, 1));
    let v_u32_2 = Val::Scalar(ScalarVal::new(IntWidth::I32, false, 2));
    let v_u32_3 = Val::Scalar(ScalarVal::new(IntWidth::I32, false, 3));
    let v_u8_1 = Val::Scalar(ScalarVal::new(IntWidth::I8, false, 1));

    match &eval_body_with_config(
        &mk_self_assign_prog(tup3_ty),
        0,
        &[Val::Tuple(vec![v_u32_1.clone(), v_u32_2.clone(), v_u32_3])],
        16,
        &v2_cfg,
    )
    .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::OverlappingMemoryCopy));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected OverlappingMemoryCopy on (u32, u32, u32), got {other:?}"),
    }

    match &eval_body_with_config(
        &mk_self_assign_prog(padded_ovf_ty),
        0,
        &[Val::Tuple(vec![v_u32_1.clone(), Val::Bool(true)])],
        16,
        &v2_cfg,
    )
    .outcome
    {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::ConservativeOverlappingAssignCopy));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => {
            panic!(
                "expected ConservativeOverlappingAssignCopy on immediate (u32, bool), got {other:?}"
            )
        }
    }

    assert!(matches!(
        eval_body_with_config(
            &mk_self_assign_prog(tup2_ty.clone()),
            0,
            &[Val::Tuple(vec![v_u32_1.clone(), v_u32_2.clone()])],
            16,
            &v2_cfg,
        )
        .outcome,
        Outcome::Returned { .. }
    ));
    assert!(matches!(
        eval_body_with_config(
            &mk_self_assign_prog(unpadded_ovf_ty),
            0,
            &[Val::Tuple(vec![v_u8_1, Val::Bool(true)])],
            16,
            &v2_cfg,
        )
        .outcome,
        Outcome::Returned { .. }
    ));

    let swap_in_place_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            identity: "test::swap_in_place".into(),
            local_tys: vec![Ty::Unit, tup2_ty],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 1,
                    projection: Vec::new(),
                    value: Rvalue::AggregateTuple {
                        fields: vec![
                            Operand::Copy {
                                local: 1,
                                projection: vec![ProjectionElem::Field {
                                    field_idx: 1,
                                    ty: U32_TY,
                                }],
                            },
                            Operand::Copy {
                                local: 1,
                                projection: vec![ProjectionElem::Field {
                                    field_idx: 0,
                                    ty: U32_TY,
                                }],
                            },
                        ],
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    assert_fault(
        &eval_body_with_config(
            &swap_in_place_prog,
            0,
            &[Val::Tuple(vec![v_u32_1, v_u32_2])],
            16,
            &v2_cfg,
        ),
        FaultKind::Unsupported,
    );

    // 4. `slice_get_unchecked_check` scales `start_off` by `elem_size`.
    let mem4 = memory::MemoryState {
        next_alloc_id: 2,
        allocations: vec![Allocation {
            alloc_id: 1,
            align_log2: 2,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Init { byte: 0, prov: None }; 4],
            live: true,
        }],
    };
    let p1 = PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize };
    assert_eq!(
        memory::slice_get_unchecked_check(&mem4, p1, 2, 2, 2, 4).unwrap_err().ub_class,
        Some(UbClass::PtrOffsetOverflowOrOob)
    );
    assert_eq!(
        memory::slice_get_unchecked_check(&mem4, p1, 1, 1, 1, 4).unwrap(),
        Val::SlicePtr { ptr: PtrVal { offset_bytes: 4, ..p1 }, len: 0 }
    );
}

#[test]
fn profile_v2_fake_address_of_executes_metadata_only_and_rejects_misuse() {
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let slice_u8 = Ty::Slice { elem: Box::new(U8_TY) };
    let mut_slice_ref =
        Ty::Ref { mutability: Mutability::Mut, pointee: Box::new(slice_u8.clone()) };
    let const_slice_ptr =
        Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(slice_u8) };
    let const_u8_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U8_TY) };

    // Valid safe `&mut [u8]` body using `FakeAddressOf` + `PtrMetadata`.
    let valid_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            identity: "test::mut_slice_fake_meta_len".into(),
            local_tys: vec![USIZE_TY, mut_slice_ref.clone(), const_slice_ptr.clone()],
            blocks: vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        projection: Vec::new(),
                        value: Rvalue::FakeAddressOf {
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::Move { local: 2, projection: Vec::new() },
                        },
                    },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    let cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 1,
            align_log2: 0,
            mutability: Mutability::Mut,
            bytes: vec![
                AllocByte::Init { byte: 10, prov: None },
                AllocByte::Init { byte: 20, prov: None },
                AllocByte::Init { byte: 30, prov: None },
            ],
            live: true,
        }],
    };
    let slice_arg = Val::SlicePtr {
        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
        len: 3,
    };
    let trace = eval_body_with_caller_mem(
        &valid_prog,
        0,
        std::slice::from_ref(&slice_arg),
        cm.clone(),
        16,
        &v2_cfg,
    );
    assert_eq!(
        trace.outcome,
        Outcome::Returned(TerminalOut::Returned { ret: Val::usize_val(3), caller_mem: cm.clone() })
    );

    // Adding an unused real raw-pointer local alongside `&mut [u8]` still fails
    // `body_mixes_refs_and_raw_ptrs_v2` (`Unsupported`).
    let mut mixed_prog = valid_prog.clone();
    mixed_prog.bodies[0].local_tys.push(const_u8_ptr.clone());
    assert_fault(
        &eval_body_with_caller_mem(&mixed_prog, 0, &[slice_arg], cm, 16, &v2_cfg),
        FaultKind::Unsupported,
    );

    // Escaping a `FakeAddressOf` local in a raw-pointer-only body fails
    // `body_fake_address_of_valid_v2` (`Unsupported`).
    let raw_escape_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "test::raw_only_escaped_fake_meta".into(),
            local_tys: vec![const_u8_ptr.clone(), const_u8_ptr.clone(), const_u8_ptr],
            blocks: vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        projection: Vec::new(),
                        value: Rvalue::FakeAddressOf {
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        projection: Vec::new(),
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 2, projection: Vec::new() },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
    };
    let raw_ptr = Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 1, width: IntWidth::Isize });
    assert_fault(
        &eval_body_with_config(&raw_escape_prog, 0, std::slice::from_ref(&raw_ptr), 16, &v2_cfg),
        FaultKind::Unsupported,
    );

    // Passing a `FakeAddressOf` local to a `Terminator::CoreCall` must fail
    // `body_fake_address_of_valid_v2` (`Unsupported`).
    let const_u8_ptr_t = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U8_TY) };
    let term_escape_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "test::terminator_escape_fake_meta".into(),
            local_tys: vec![const_u8_ptr_t.clone(), const_u8_ptr_t.clone(), const_u8_ptr_t],
            blocks: vec![
                Block {
                    statements: vec![Statement::Assign {
                        local: 2,
                        projection: Vec::new(),
                        value: Rvalue::FakeAddressOf {
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                    }],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::PtrAdd { mutability: Mutability::Shared, pointee: U8_TY },
                        args: vec![
                            Operand::Copy { local: 2, projection: Vec::new() },
                            Operand::Constant { ty: USIZE_TY, lit: ConstLit::Scalar { bits: 0 } },
                        ],
                        dst: Place::local(0),
                        target: Some(1),
                        unwind: UnwindAction::Unreachable,
                    },
                    cleanup: false,
                },
                Block { statements: Vec::new(), terminator: Terminator::Ret, cleanup: false },
            ],
        }],
    };
    assert_fault(
        &eval_body_with_config(&term_escape_prog, 0, std::slice::from_ref(&raw_ptr), 16, &v2_cfg),
        FaultKind::Unsupported,
    );
}
