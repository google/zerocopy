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
    CallerMemory, CaptureInput, CastKind, ConstLit, EnumTagRepr, EnumTy, EvalConfig, FaultDetail,
    FaultKind, FrameState, IntTy, IntWidth, LocalSlot, MachineState, Mutability, Operand,
    OrderingVal, Outcome, ProbeConfig, Program, ProjectionElem, PtrVal, Rvalue, ScalarVal, Scope,
    Statement, StepOutcome, StepTrace, TargetEndian, TerminalOut, Terminator, Ty, UnOp,
    UnwindAction, Val, check_val, decode_val, eval_body, eval_body_auto, eval_body_by_identity,
    eval_body_with_config, layout_of_ty, load_indirect, memory, probe_body, probe_body_with_policy,
    store_indirect, validate_body_entry, validate_program_config,
};

const U8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
const I8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: true });
const U16_TY: Ty = Ty::Int(IntTy { width: IntWidth::I16, signed: false });
const U32_TY: Ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
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
                    value: Rvalue::Discriminant { local: 3, projection: Vec::new() },
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
                    value: Rvalue::Discriminant { local: 1, projection: Vec::new() },
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
                    value: Rvalue::Discriminant { local: 1, projection: Vec::new() },
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
                    value: Rvalue::Discriminant { local: 1, projection: Vec::new() },
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

    // Schema v4 manifest round-trip and rejection of unsupported schema_version.
    let h = "c".repeat(64);
    let manifest_json = format!(
        r#"{{
            "schema_version": 4,
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
                "overflow_checks": false,
                "mir_preserve_ub": true,
                "pointer_bits": 64,
                "endian": "little",
                "declared_source_files": ["src/lib.rs"]
            }},
            "source_files": [],
            "census": [],
            "selected": [],
            "unsupported": [],
            "program": {{
                "scope": {{ "kind": "crate" }},
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
    assert_eq!(parsed_manifest.manifest().unwrap().configuration.endian, "little");
    let manifest_prog = parsed_manifest.into_program();
    assert_eq!(manifest_prog.pointer_width_bits, 64);
    assert_returned(&eval_body(&manifest_prog, 0, &[], 16), Val::Unit);

    let bad_manifest_ver = manifest_json.replace("\"schema_version\": 4", "\"schema_version\": 5");
    assert!(CaptureInput::from_json_str(&bad_manifest_ver).is_err());
}

#[test]
fn profile_v2_aggregates_projections_assert_and_calls() {
    let mut roots = BTreeSet::new();
    roots.insert("test::caller".into());
    let prog = Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![
                    U32_TY,
                    U32_TY,
                    Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false }),
                ],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::Call {
                            callee: 1,
                            args: vec![
                                Operand::Copy { local: 1, projection: Vec::new() },
                                Operand::Constant { ty: U32_TY, lit: ConstLit::Scalar { bits: 1 } },
                            ],
                            dst_local: 2,
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
                                operand: Operand::Copy {
                                    local: 2,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy {
                                local: 2,
                                projection: vec![ProjectionElem::Field {
                                    field_idx: 1,
                                    ty: Ty::Bool,
                                }],
                            },
                            expected: false,
                            msg: AssertKind::Overflow { op: BinOp::Add },
                            target: 2,
                            unwind: UnwindAction::Continue,
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                ],
                identity: "test::caller".into(),
            },
            Body {
                arg_count: 2,
                is_unsafe: false,
                local_tys: vec![
                    Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false }),
                    U32_TY,
                    U32_TY,
                    U32_TY,
                    Ty::Bool,
                ],
                blocks: vec![Block {
                    statements: vec![
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Binary {
                                op: BinOp::AddWithOverflow,
                                left: Operand::Copy { local: 1, projection: Vec::new() },
                                right: Operand::Copy { local: 2, projection: Vec::new() },
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy {
                                    local: 0,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 0,
                                        ty: U32_TY,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 4,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Copy {
                                    local: 0,
                                    projection: vec![ProjectionElem::Field {
                                        field_idx: 1,
                                        ty: Ty::Bool,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 0,
                            projection: Vec::new(),
                            value: Rvalue::Aggregate {
                                aggregate_kind: AggregateKind::Tuple,
                                fields: vec![
                                    Operand::Copy { local: 3, projection: Vec::new() },
                                    Operand::Copy { local: 4, projection: Vec::new() },
                                ],
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::checked_inc".into(),
            },
        ],
    };

    let cfg_v2 = EvalConfig::profile_v2(TargetEndian::Little);
    assert_returned(&eval_body_with_config(&prog, 0, &[Val::u32(41)], 64, &cfg_v2), Val::u32(42));
    // Assert failure cleanly unwinds on `u32::MAX`
    match eval_body_with_config(&prog, 0, &[Val::u32(u32::MAX)], 64, &cfg_v2).outcome {
        Outcome::Returned(TerminalOut::Unwound { .. }) => {}
        other => panic!("expected Unwound on assert failure, got {other:?}"),
    }
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
    // Strict Profile v1 auto-selection (`eval_body_auto` / `for_program`)
    // also fails closed on `mir_profile_version == 2`, requiring explicit
    // opt-in via `EvalConfig::profile_v2`.
    assert!(EvalConfig::for_program(&bad_ver, None).is_err());
    assert_fault(&eval_body_auto(&bad_ver, 0, &[], 16), FaultKind::Unsupported);
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
                        local: 1,
                        projection: vec![ProjectionElem::Unsupported],
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
fn profile_v2_nested_call_respects_caller_unwind_action() {
    let callee_assert_continue = Body {
        arg_count: 0,
        is_unsafe: false,
        local_tys: vec![U32_TY],
        blocks: vec![
            Block {
                statements: vec![],
                terminator: Terminator::Assert {
                    cond: Operand::Constant { ty: Ty::Bool, lit: ConstLit::Scalar { bits: 0 } },
                    expected: true,
                    msg: AssertKind::BoundsCheck,
                    target: 1,
                    unwind: UnwindAction::Continue,
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
                            lit: ConstLit::Scalar { bits: 1 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            },
        ],
        identity: "test::callee_assert_continue".into(),
    };

    // 1. Caller Call with UnwindAction::Unreachable faults Undefined when callee unwinds.
    let mut roots = BTreeSet::new();
    roots.insert("test::caller_unreach".into());
    let prog_unreach = Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![U32_TY],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::Call {
                            callee: 1,
                            args: vec![],
                            dst_local: 0,
                            dst_projection: Vec::new(),
                            target: Some(1),
                            unwind: UnwindAction::Unreachable,
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                ],
                identity: "test::caller_unreach".into(),
            },
            callee_assert_continue.clone(),
        ],
    };
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    assert_fault(&eval_body_with_config(&prog_unreach, 0, &[], 32, &v2_cfg), FaultKind::Undefined);

    // 2. Caller Call with Cleanup runs cleanup block, then UnwindResume unwinds to root Unwound.
    let mut roots2 = BTreeSet::new();
    roots2.insert("test::caller_cleanup".into());
    let prog_cleanup = Program {
        scope: Scope::SelectedUnit { roots: roots2, instantiations: BTreeSet::new() },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![U32_TY],
                blocks: vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::Call {
                            callee: 1,
                            args: vec![],
                            dst_local: 0,
                            dst_projection: Vec::new(),
                            target: Some(1),
                            unwind: UnwindAction::Cleanup { block: 2 },
                        },
                        cleanup: false,
                    },
                    Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
                    Block {
                        statements: vec![],
                        terminator: Terminator::UnwindResume,
                        cleanup: true,
                    },
                ],
                identity: "test::caller_cleanup".into(),
            },
            callee_assert_continue,
        ],
    };
    let trace = eval_body_with_config(&prog_cleanup, 0, &[], 32, &v2_cfg);
    assert!(
        matches!(trace.outcome, Outcome::Returned(TerminalOut::Unwound { .. })),
        "expected Unwound, got {:?}",
        trace.outcome
    );
    assert!(
        trace.events.iter().any(|e| e.kind.contains("unwind_cleanup(->bb2)")),
        "expected caller cleanup block to execute: {:?}",
        trace.events
    );
    let report = probe_body(&prog_cleanup, 0, &ProbeConfig::default(), &v2_cfg);
    assert_eq!(report.returned_count, 0);
    assert_eq!(report.unwound_count, 1);
    assert!(report.first_unwound.is_some());
    assert!(
        trace.events.iter().any(|e| e.kind.contains("unwind_cleanup(->bb2)")),
        "expected caller cleanup block to execute: {:?}",
        trace.events
    );
}

#[test]
fn profile_v2_partial_tuple_move_preserves_sibling_fields() {
    let pair_ty = Ty::Tuple { fields: vec![U32_TY, Ty::Bool] };
    let nested_ty = Ty::Tuple { fields: vec![pair_ty.clone(), Ty::Bool] };
    let mut roots = BTreeSet::new();
    roots.insert("test::partial_move".into());
    roots.insert("test::moved_field_undef".into());
    let prog = Program {
        scope: Scope::SelectedUnit { roots, instantiations: BTreeSet::new() },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
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
            // Body 1: nested partial move + re-initialization + reading moved field UB.
            Body {
                arg_count: 1,
                is_unsafe: false,
                local_tys: vec![U32_TY, nested_ty.clone(), U32_TY],
                blocks: vec![Block {
                    statements: vec![
                        // Move `(_1.0).0`
                        Statement::Assign {
                            local: 2,
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
                        },
                        // Reading `(_1.0).0` again must fault Undefined!
                        Statement::Assign {
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
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::moved_field_undef".into(),
            },
        ],
    };
    let pair_val = Val::Tuple(vec![Val::u32(42), Val::Bool(true)]);
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    assert_returned(
        &eval_body_with_config(&prog, 0, std::slice::from_ref(&pair_val), 16, &v2_cfg),
        Val::Bool(true),
    );

    let nested_val = Val::Tuple(vec![pair_val, Val::Bool(false)]);
    assert_fault(
        &eval_body_with_config(&prog, 1, &[nested_val], 16, &v2_cfg),
        FaultKind::Undefined,
    );
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
fn partial_tuple_force_allocation_preserves_fields_and_avoids_leak_on_error() {
    let overflow_ty = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
    let prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["test::partial_overflow".into()].into_iter().collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit, overflow_ty.clone()],
            blocks: vec![Block {
                statements: vec![
                    Statement::StorageLive { local: 1 },
                    Statement::Assign {
                        local: 1,
                        projection: vec![ProjectionElem::Field { field_idx: 0, ty: U32_TY }],
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: U32_TY,
                                lit: ConstLit::Scalar { bits: 0x0102_0304 },
                            },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            identity: "test::partial_overflow".into(),
        }],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut state = MachineState::init(&prog, 0, &[], &cfg).unwrap();
    assert!(matches!(state.step(&prog, &cfg), StepOutcome::Stepped { .. }));
    assert!(matches!(state.step(&prog, &cfg), StepOutcome::Stepped { .. }));
    let place = state.force_allocation(&prog, 1, &cfg).unwrap();
    let bytes = state.mem.read_bytes(place, 8, 2).unwrap();
    assert_eq!(
        bytes,
        vec![
            AllocByte::Init { byte: 0x04, prov: None },
            AllocByte::Init { byte: 0x03, prov: None },
            AllocByte::Init { byte: 0x02, prov: None },
            AllocByte::Init { byte: 0x01, prov: None },
            AllocByte::Uninit,
            AllocByte::Uninit,
            AllocByte::Uninit,
            AllocByte::Uninit,
        ]
    );
    assert_eq!(decode_val(TargetEndian::Little, &overflow_ty, &bytes, true).unwrap(), None);

    // Failed force_allocation does not leak an allocation into `state.mem`.
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
    };
    let mut err_state = MachineState::init(&bad_prog, 0, &[], &cfg).unwrap();
    let base_allocs = err_state.mem.allocations.len();
    err_state.frames[0].locals[1] = LocalSlot::PartialTuple {
        fields: vec![
            LocalSlot::Immediate { val: Some(Val::Bool(true)) },
            LocalSlot::Immediate { val: None },
        ],
    };
    assert_eq!(
        err_state.force_allocation(&bad_prog, 1, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_eq!(err_state.mem.allocations.len(), base_allocs);

    err_state.frames[0].locals[1] = LocalSlot::Immediate { val: Some(Val::Bool(false)) };
    assert_eq!(
        err_state.force_allocation(&bad_prog, 1, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_eq!(err_state.mem.allocations.len(), base_allocs);

    err_state.frames[0].locals[2] = LocalSlot::PartialTuple {
        fields: vec![
            LocalSlot::Immediate { val: Some(Val::u32(1)) },
            LocalSlot::Immediate { val: Some(Val::u32(2)) },
        ],
    };
    assert_eq!(
        err_state.force_allocation(&bad_prog, 2, &cfg).unwrap_err().kind,
        FaultKind::Unsupported
    );
    assert_eq!(err_state.mem.allocations.len(), base_allocs);
}

#[test]
fn pointer_and_ref_types_have_no_layout_even_when_uninit() {
    let ref_ty = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let raw_ty = Ty::RawPtr { mutability: Mutability::Mut, pointee: Box::new(U32_TY) };
    let mut mem = anneal_mir_eval::MemoryState::default();
    let place = mem.allocate_stack(anneal_mir_eval::LayoutData { size: 8, align_log2: 3 });

    for ty in [&ref_ty, &raw_ty] {
        assert_eq!(layout_of_ty(ty, true), None);
        assert_eq!(
            decode_val(TargetEndian::Little, ty, &[AllocByte::Uninit; 8], true).unwrap_err().kind,
            FaultKind::Unsupported
        );
        assert_eq!(
            load_indirect(&mem, TargetEndian::Little, ty, place, true).unwrap_err().kind,
            FaultKind::Unsupported
        );
        assert_eq!(
            store_indirect(
                &mut mem,
                TargetEndian::Little,
                ty,
                place,
                &Val::Ptr(PtrVal {
                    alloc_id: Some(place.alloc_id),
                    offset_bytes: 0,
                    width: IntWidth::Isize,
                }),
                true,
            )
            .unwrap_err()
            .kind,
            FaultKind::Unsupported
        );
        assert_eq!(
            memory::deinit_indirect(&mut mem, ty, place, true).unwrap_err().kind,
            FaultKind::Unsupported
        );
    }

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
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut state = MachineState::init(&prog, 0, &[], &cfg).unwrap();
    assert_eq!(state.force_allocation(&prog, 1, &cfg).unwrap_err().kind, FaultKind::Unsupported);
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
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let mut state = MachineState::init(&prog, 0, &[], &cfg).unwrap();
    state.frames[0] = FrameState {
        def_id: 0,
        block_idx: 0,
        stmt_idx: 0,
        locals: vec![LocalSlot::Immediate { val: Some(Val::Unit) }],
        return_to: Some(CallReturnTarget {
            block_idx: 0,
            dst_local: 0,
            dst_projection: Vec::new(),
            unwind: UnwindAction::Continue,
        }),
    };
    match state.step(&prog, &cfg) {
        StepOutcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported),
        other => panic!("expected Fault(Unsupported), got {other:?}"),
    }
}

#[test]
fn zst_tuple_projection_from_uninit_local_reads_and_moves_zst_value() {
    let u32_unit = Ty::Tuple { fields: vec![U32_TY, Ty::Unit] };
    let unit_singleton = Ty::Tuple { fields: vec![Ty::Unit] };
    let u32_nested_zst = Ty::Tuple { fields: vec![U32_TY, unit_singleton.clone()] };
    let all_zst_pair = Ty::Tuple { fields: vec![Ty::Unit, Ty::Unit] };
    let prog = Program {
        scope: Scope::SelectedUnit {
            roots: [
                "test::copy_uninit_zst_field".into(),
                "test::move_uninit_zst_field".into(),
                "test::copy_uninit_zst_tuple_field".into(),
                "test::copy_uninit_all_zst_tuple".into(),
                "test::copy_uninit_non_zst_field".into(),
            ]
            .into_iter()
            .collect(),
            instantiations: BTreeSet::new(),
        },
        bodies: vec![
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit, u32_unit.clone()],
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
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![Ty::Unit, u32_unit.clone()],
                blocks: vec![Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 0,
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
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::move_uninit_zst_field".into(),
            },
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![unit_singleton.clone(), u32_nested_zst],
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
                                        ty: unit_singleton,
                                    }],
                                },
                                with_retag: false,
                            },
                        },
                    ],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                identity: "test::copy_uninit_zst_tuple_field".into(),
            },
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
            Body {
                arg_count: 0,
                is_unsafe: false,
                local_tys: vec![U32_TY, u32_unit],
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
                identity: "test::copy_uninit_non_zst_field".into(),
            },
        ],
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
    };

    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    assert_returned(&eval_body_with_config(&prog, 0, &[], 16, &cfg), Val::Unit);
    assert_returned(&eval_body_with_config(&prog, 1, &[], 16, &cfg), Val::Unit);
    assert_returned(&eval_body_with_config(&prog, 2, &[], 16, &cfg), Val::Tuple(vec![Val::Unit]));
    assert_returned(
        &eval_body_with_config(&prog, 3, &[], 16, &cfg),
        Val::Tuple(vec![Val::Unit, Val::Unit]),
    );
    assert_fault(&eval_body_with_config(&prog, 4, &[], 16, &cfg), FaultKind::Undefined);
}

#[test]
fn profile_v2_version_bounds_ptr_checks_and_terminate_aborts() {
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

    // `Ty::Ref` rejects null (`alloc_id: None`) and wrong pointer width;
    // `Ty::RawPtr` rejects wrong pointer width while permitting null `Isize`.
    let ref_ty = Ty::Ref { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let raw_ty = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let null_isize = Val::Ptr(PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize });
    let live_isize =
        Val::Ptr(PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize });
    let bad_i8 = Val::Ptr(PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::I8 });
    let bad_i64 = Val::Ptr(PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::I64 });

    assert!(!check_val(&null_isize, &ref_ty, true));
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
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            local_tys: vec![Ty::Unit, ref_ty],
            blocks: vec![Block { statements: vec![], terminator: Terminator::Ret, cleanup: false }],
            identity: "test::take_ref".into(),
        }],
    };
    assert_fault(
        &eval_body_with_config(&ref_prog, 0, &[null_isize], 16, &v2_cfg),
        FaultKind::Unsupported,
    );
    assert_fault(
        &eval_body_with_config(&ref_prog, 0, &[bad_i8], 16, &v2_cfg),
        FaultKind::Unsupported,
    );

    // `UnwindAction::Terminate` aborts execution (`Outcome::Aborted`), distinct
    // from `TerminalOut::Unwound`, and increments `aborted_count`.
    let term_prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["test::terminate".into()].into_iter().collect(),
            instantiations: BTreeSet::new(),
        },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![Body {
            arg_count: 0,
            is_unsafe: false,
            local_tys: vec![Ty::Unit],
            blocks: vec![Block {
                statements: vec![],
                terminator: Terminator::Assert {
                    cond: Operand::Constant { ty: Ty::Bool, lit: ConstLit::Scalar { bits: 0 } },
                    expected: true,
                    msg: AssertKind::BoundsCheck,
                    target: 0,
                    unwind: UnwindAction::Terminate,
                },
                cleanup: false,
            }],
            identity: "test::terminate".into(),
        }],
    };
    let term_trace = eval_body_with_config(&term_prog, 0, &[], 16, &v2_cfg);
    assert!(matches!(term_trace.outcome, Outcome::Aborted { .. }), "{:?}", term_trace.outcome);
    let report = probe_body(&term_prog, 0, &ProbeConfig::default(), &v2_cfg);
    assert_eq!(report.returned_count, 0);
    assert_eq!(report.aborted_count, 1);
    assert!(report.first_aborted.is_some());
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

    // 1-aligned zero-sized operations (`size == 0 && align_log2 == 0`) succeed
    // without looking up `alloc_id`, matching `Trusted.MirSemantics.Memory`
    // and `rustc`'s `get_place_alloc` / `get_place_alloc_mut`. Over-aligned
    // zero-sized operations (`align_log2 > 0`) still require a known
    // allocation and valid alignment.
    let missing = MemPlace { alloc_id: 99, offset: 0 };
    assert_eq!(mem.read_bytes(missing, 0, 0).unwrap(), Vec::<AllocByte>::new());
    mem.write_bytes(missing, 0, &[]).unwrap();
    mem.write_uninit(missing, 0, 0).unwrap();
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
    // `anneal-rustc-capture` (schema version 4, Profile v1) with unselected
    // census rows elided and host paths normalized.
    const CAPTURE_JSON: &str =
        include_str!("fixtures/zerocopy_01_usize_pointer_metadata_capture.json");
    let input = CaptureInput::from_json_str(CAPTURE_JSON).unwrap();
    let CaptureInput::Manifest(manifest) = input else {
        panic!("expected schema-v4 capture manifest");
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

    // 4. Tuple `(Never, RawPtr)` or param list `(Never, RawPtr)` must report
    //    `unsupported_param_shape` (not short-circuit to `uninhabited_params`).
    let raw_ptr_ty =
        Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(u32_ty.clone()) };
    let tuple_never_ptr = Body {
        arg_count: 1,
        is_unsafe: false,
        identity: "demo::tuple_never_ptr".into(),
        local_tys: vec![Ty::Unit, Ty::Tuple { fields: vec![Ty::Never, raw_ptr_ty.clone()] }],
        blocks: vec![ret_block],
    };
    let prog_tuple = Program {
        pointer_width_bits: 64,
        mir_profile_version: 2,
        bodies: vec![tuple_never_ptr],
        ..prog_32
    };
    let rtuple = probe_body(
        &prog_tuple,
        0,
        &ProbeConfig::default(),
        &EvalConfig::profile_v2(TargetEndian::Little),
    );
    assert!(rtuple.unsupported_param_shape);
    assert!(!rtuple.uninhabited_params);
}

#[test]
fn profile_v2_projected_cast_and_discriminant_validate_dst_ty_before_operand_read() {
    let u8_ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
    let u16_ty = Ty::Int(IntTy { width: IntWidth::I16, signed: false });
    let u32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
    let dst_tuple = Ty::Tuple { fields: vec![u32_ty.clone(), Ty::Bool] };
    let enum_u8 = canary_repr_u8_enum();

    // `(_0.0) = Cast(IntToInt, Copy(_1), u16)` with `_0: (u32, bool)` and
    // uninitialized `_1: u8` must fault `Unsupported` (not `Undefined`).
    let cast_body = Body {
        arg_count: 0,
        is_unsafe: false,
        identity: "demo::proj_cast_mismatch".into(),
        local_tys: vec![dst_tuple.clone(), u8_ty],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: vec![ProjectionElem::Field { field_idx: 0, ty: u32_ty.clone() }],
                value: Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1, projection: vec![] },
                    ty: u16_ty,
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
    };
    let discr_body = Body {
        arg_count: 0,
        is_unsafe: false,
        identity: "demo::proj_discr_mismatch".into(),
        local_tys: vec![dst_tuple, Ty::Enum(enum_u8)],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: vec![ProjectionElem::Field { field_idx: 0, ty: u32_ty }],
                value: Rvalue::Discriminant { local: 1, projection: vec![] },
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
        bodies: vec![cast_body, discr_body],
    };
    let cfg = EvalConfig::profile_v2(TargetEndian::Little);
    for id in [0usize, 1] {
        let trace = eval_body_with_config(&prog, id, &[], 32, &cfg);
        match trace.outcome {
            Outcome::Fault(f) => assert_eq!(f.kind, FaultKind::Unsupported, "body {id}: {f:?}"),
            other => panic!("body {id}: expected Unsupported, got {other:?}"),
        }
    }
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
