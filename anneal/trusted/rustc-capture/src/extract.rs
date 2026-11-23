// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Direct translation of the admitted pointer-free MIR syntax. Unsupported
//! variants remain errors; this adapter performs no control-flow or expression
//! simplification.

use rustc_abi::{Endian, ExternAbi, HasDataLayout, Integer, Primitive, Size, TagEncoding, Variants};
use rustc_ast::Mutability;
use rustc_hir::attrs::{InlineAttr, OptimizeAttr};
use rustc_middle::middle::codegen_fn_attrs::{
    CodegenFnAttrFlags, CodegenFnAttrs, SanitizerFnAttrs,
};
use rustc_middle::mir::interpret::{AllocRange, Allocation, GlobalAlloc, Provenance};
use rustc_middle::mir::{self, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, TyCtxt, TypingEnv};
use rustc_span::def_id::{DefId, LocalDefId};
use sha2::{Digest, Sha256};

use crate::ir::{self, ConstLit, IntTy, IntWidth};

pub type Result<T> = std::result::Result<T, String>;

/// Decode a `TyKind::Int` or `TyKind::Uint` into [`IntTy`], preserving pointer-
/// sized `isize`/`usize` (`bit_width() == None`) as [`IntWidth::Isize`] on the
/// separately checked 64-bit target and mapping 8..=128-bit integers 1-to-1.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ast_ir/src/lib.rs#L58-L67
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ast_ir/src/lib.rs#L134-L143
fn int_ty(t: ty::Ty<'_>) -> Result<IntTy> {
    let (bit_width, signed) = match *t.kind() {
        ty::Uint(u) => (u.bit_width(), false),
        ty::Int(i) => (i.bit_width(), true),
        _ => return Err(format!("expected integer type, got {t:?}")),
    };
    let width = match bit_width {
        None => IntWidth::Isize,
        Some(8) => IntWidth::I8,
        Some(16) => IntWidth::I16,
        Some(32) => IntWidth::I32,
        Some(64) => IntWidth::I64,
        Some(128) => IntWidth::I128,
        Some(bits) => {
            return Err(format!("unsupported integer width {bits}"));
        }
    };
    Ok(IntTy { width, signed })
}

/// Extract the in-memory tag representation of a fieldless enum from `rustc`'s
/// monomorphized `Variants` layout (`Empty`, `Single { index }`, `Multiple`
/// where "each variant comes with a *discriminant* ... encoded as a *tag* on
/// the machine").
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L1937-L1952
fn enum_tag_repr<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: ty::Ty<'tcx>,
    variant_count: usize,
) -> Result<ir::EnumTagRepr> {
    let layout = tcx
        .layout_of(TypingEnv::fully_monomorphized().as_query_input(t))
        .map_err(|err| format!("failed to compute enum layout for {t:?}: {err}"))?;
    match &layout.variants {
        Variants::Empty => Err(format!(
            "uninhabited zero-variant enums are unsupported: {t:?}"
        )),
        Variants::Single { index } => {
            if index.as_usize() == 0 && layout.size.bytes() == 0 && variant_count == 1 {
                Ok(ir::EnumTagRepr::ZeroSized)
            } else {
                Err(format!(
                    "non-zero-sized single-variant enum representations are unsupported: {t:?}"
                ))
            }
        }
        Variants::Multiple {
            tag,
            tag_encoding: TagEncoding::Direct,
            tag_field,
            ..
        } if tag_field.as_usize() == 0 => match tag.primitive() {
            Primitive::Int(integer, signed) => {
                let width = match integer {
                    Integer::I8 => IntWidth::I8,
                    Integer::I16 => IntWidth::I16,
                    Integer::I32 => IntWidth::I32,
                    Integer::I64 => IntWidth::I64,
                    Integer::I128 => IntWidth::I128,
                };
                Ok(ir::EnumTagRepr::Scalar(IntTy { width, signed }))
            }
            other => Err(format!("non-integer enum tag primitive {other:?}: {t:?}")),
        },
        other => Err(format!("unsupported enum variant layout {other:?}: {t:?}")),
    }
}

/// The type grammar is `TyKind` at the pinned compiler revision:
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs
///
/// Enum values in the owned syntax carry raw tag bits. The table below records
/// the compiler's `Discr` ("Bit representation of the discriminant (e.g.,
/// `-1i8` is `0xFF_u128`)") and layout tag representation separately because
/// MIR warns: "the value of the discriminant is not the same thing as the
/// variant index."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/util.rs#L35-L39
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1433-L1443
pub fn ty<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Result<ir::Ty> {
    // Every admitted value must fit the owned scalar representation. Rejecting
    // a type is deliberate: replacing a pointer, payload, or unmodeled
    // aggregate with a machine word would assign semantics the proof model does
    // not provide.
    match *t.kind() {
        ty::Bool => Ok(ir::Ty::Bool),
        ty::Char => Ok(ir::Ty::Char),
        ty::Never => Ok(ir::Ty::Never),
        ty::Tuple(elements) if elements.is_empty() => Ok(ir::Ty::Unit),
        // `BinOp::{Add,Sub,Mul}WithOverflow` "returns `(T, bool)` of both the
        // wrapped result and a bool indicating whether it overflowed", which is
        // the sole non-empty tuple type `Trusted.MirSemantics.isOverflowPairTy`
        // executes; every other non-empty tuple remains refused.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1626-L1642
        ty::Tuple(elements) if elements.len() == 2 => {
            if let (Ok(ir::Ty::Int(ity)), Ok(ir::Ty::Bool)) =
                (ty(tcx, elements[0]), ty(tcx, elements[1]))
            {
                Ok(ir::Ty::OverflowPair(ity))
            } else {
                Err(format!("unsupported type: {t:?}"))
            }
        }
        ty::Uint(_) | ty::Int(_) => Ok(ir::Ty::Int(int_ty(t)?)),
        // `core::cmp::Ordering` ("a lang item only so that `BinOp::Cmp` in MIR
        // can return it") maps to `Trusted.MirAst.MirTy.ordering` before the
        // crate-local fieldless enum arm (`capture.rs` separately refuses
        // crate-local language items).
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/cmp.rs#L400-L415
        ty::Adt(adt, args)
            if args.is_empty()
                && tcx.is_lang_item(adt.did(), rustc_hir::LangItem::OrderingEnum) =>
        {
            Ok(ir::Ty::Ordering)
        }
        // `Trusted.MirAst.EnumTy` keys nominal enum identity by the `u32` that
        // `enum_id` derives from the enum's semantic path, so the key does not
        // move when unrelated items shift compiler indices. Admission requires
        // non-generic (`args.is_empty()`) enums "defined in the crate currently
        // being compiled" (`is_local()`). Their paths are crate-relative,
        // phantom generic instantiations cannot share one key, and `capture.rs`
        // refuses any emitted key shared by two local enum definitions.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/def_id.rs#L291-L295
        ty::Adt(adt, args) if adt.did().is_local() && adt.is_enum() && args.is_empty() => {
            if adt.variants().is_empty() {
                return Err(format!(
                    "uninhabited zero-variant enums are unsupported: {t:?}"
                ));
            }
            // A fieldless enum has no "Fields of this variant" in any variant.
            // Payload values have no tag-only scalar representation.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/mod.rs#L1209-L1210
            if adt
                .variants()
                .iter()
                .any(|variant| !variant.fields.is_empty())
            {
                return Err(format!("enum payloads are unsupported: {t:?}"));
            }
            // `discriminant_ty` "Returns the type of the discriminant of this
            // type": the `repr` integer, or `isize` by default. That is the
            // "typeck type" of the discriminant; layout may store a smaller
            // tag, which `enum_tag_repr` records separately.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/sty.rs#L1682-L1685
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L198-L204
            let discr = int_ty(t.discriminant_ty(tcx))
                .map_err(|err| format!("unsupported enum discriminant type for {t:?}: {err}"))?;
            let tag_repr = enum_tag_repr(tcx, t, adt.variants().len())?;
            // `discriminants` computes explicit and implicit discriminants;
            // it is not safe to substitute the enumeration index here.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/adt.rs#L660-L679
            let discriminants = adt
                .discriminants(tcx)
                .map(|(_, entry)| {
                    if int_ty(entry.ty)? != discr {
                        return Err("enum discriminant type disagrees with discriminant_ty".into());
                    }
                    Ok(entry.val)
                })
                .collect::<Result<Vec<_>>>()?;
            let ety = ir::EnumTy::try_new(enum_id(tcx, adt.did()), discr, tag_repr, discriminants)
                .map_err(|reason| format!("{reason}: {t:?}"))?;
            Ok(ir::Ty::Enum(ety))
        }
        _ => Err(format!("unsupported type: {t:?}")),
    }
}

/// `Place` has a local plus projections. This fragment admits the empty
/// projection only, preserving the compiler local index without renumbering.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1182-L1188
fn local(place: &mir::Place<'_>) -> Result<u32> {
    if !place.projection.is_empty() {
        return Err(format!("place projections are unsupported: {place:?}"));
    }
    Ok(place.local.as_u32())
}

/// Copy and move are distinct constructors. The source says a move "may
/// additionally overwrite the place with `uninit` bytes"; the model owns that
/// operational choice rather than having the adapter erase the distinction.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1303-L1330
fn operand<'tcx>(tcx: TyCtxt<'tcx>, op: &mir::Operand<'tcx>) -> Result<ir::Operand> {
    match op {
        mir::Operand::Copy(place) => Ok(ir::Operand::Copy {
            local: local(place)?,
        }),
        mir::Operand::Move(place) => Ok(ir::Operand::Move {
            local: local(place)?,
        }),
        mir::Operand::Constant(constant) => {
            let t = ty(tcx, constant.const_.ty())?;
            let width = match &t {
                ir::Ty::Bool | ir::Ty::Ordering => 8,
                ir::Ty::Char => 32,
                ir::Ty::Unit => {
                    // `ZeroSized` is documented as "Only for ZSTs." The
                    // source type must independently be the empty tuple;
                    // other zero-sized types do not acquire unit semantics.
                    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/consts.rs#L38-L39
                    if matches!(
                        constant.const_,
                        mir::Const::Val(mir::ConstValue::ZeroSized, _)
                    ) {
                        return Ok(ir::Operand::Constant {
                            ty: t,
                            lit: ConstLit::ZeroSized,
                        });
                    }
                    return Err("unit constant lacks the compiler ZeroSized representation".into());
                }
                ir::Ty::Never => {
                    return Err("the never type has no scalar constants".into());
                }
                ir::Ty::OverflowPair(_) => {
                    return Err("overflow-pair tuple constants are unsupported".into());
                }
                ir::Ty::Int(ity) => ity.width.bits(),
                ir::Ty::Enum(ety) => match ety.tag_repr() {
                    ir::EnumTagRepr::ZeroSized => {
                        if matches!(
                            constant.const_,
                            mir::Const::Val(mir::ConstValue::ZeroSized, _)
                        ) {
                            return Ok(ir::Operand::Constant {
                                ty: t,
                                lit: ConstLit::ZeroSized,
                            });
                        }
                        return Err(
                            "zero-sized enum constant lacks the compiler ZeroSized representation"
                                .into(),
                        );
                    }
                    ir::EnumTagRepr::Scalar(tag) => tag.width.bits(),
                },
            };
            // Only already-valued integer scalars or read-only `.rodata`
            // `GlobalAlloc::Memory` scalars are admitted. In particular, do not
            // evaluate an `Unevaluated` constant and silently substitute its
            // result for an unrepresented constant obligation.
            // `Scalar::Int` denotes "The raw bytes of a simple value";
            // `try_to_scalar_int` excludes provenance-bearing pointers.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/consts.rs#L33-L71
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/value.rs
            let mir::Const::Val(value, _) = constant.const_ else {
                return Err(format!("unsupported constant: {:?}", constant.const_));
            };
            let bits = match value {
                mir::ConstValue::Scalar(scalar) => {
                    let scalar_int = scalar
                        .try_to_scalar_int()
                        .map_err(|_| "only integer scalar constants are modeled")?;
                    if scalar_int.size().bits() != u64::from(width) {
                        return Err("scalar constant width disagrees with its type".into());
                    }
                    scalar_int.to_bits_unchecked()
                }
                mir::ConstValue::Indirect { alloc_id, offset } => {
                    match tcx.global_alloc(alloc_id) {
                        GlobalAlloc::Memory(const_alloc) => {
                            read_rodata_scalar_from_alloc(&tcx, const_alloc.inner(), offset, width)?
                        }
                        GlobalAlloc::Static(_) => {
                            return Err(
                                "static global allocations are unsupported in constants".into(),
                            );
                        }
                        GlobalAlloc::Function { .. } => {
                            return Err(
                                "function global allocations are unsupported in constants".into(),
                            );
                        }
                        GlobalAlloc::VTable(..) => {
                            return Err(
                                "vtable global allocations are unsupported in constants".into(),
                            );
                        }
                        GlobalAlloc::TypeId { .. } => {
                            return Err(
                                "type-id global allocations are unsupported in constants".into(),
                            );
                        }
                    }
                }
                mir::ConstValue::ZeroSized | mir::ConstValue::Slice { .. } => {
                    return Err("only integer scalar constants are modeled".into());
                }
            };
            let lit = ConstLit::Scalar { bits };
            ir::validate_constant(&t, lit)?;
            Ok(ir::Operand::Constant { ty: t, lit })
        }
        other => Err(format!("unsupported operand: {other:?}")),
    }
}

/// Read an initialized, provenance-free little-endian scalar out of an immutable
/// (`.rodata`, `Mutability::Not`) `GlobalAlloc::Memory` allocation.
///
/// Fails closed on mutable allocations, non-little-endian targets, out-of-bounds
/// or overflowing ranges, uninitialized bytes (`InitMask`), and overlapping
/// pointer provenance (`ProvenanceMap`), matching `Allocation::read_scalar`
/// (`read_provenance = false`):
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/allocation.rs#L698-L737
fn read_rodata_scalar_from_alloc<Prov: Provenance>(
    cx: &impl HasDataLayout,
    alloc: &Allocation<Prov>,
    offset: Size,
    width: u32,
) -> Result<u128> {
    if cx.data_layout().endian != Endian::Little {
        return Err("non-little-endian global allocation constants are unsupported".into());
    }
    if width == 0 || !width.is_multiple_of(8) || width > 128 {
        return Err(format!(
            "unsupported scalar width {width} for global allocation constant"
        ));
    }
    if alloc.mutability != Mutability::Not {
        return Err("mutable global allocations are unsupported in constants".into());
    }
    let byte_len = u64::from(width / 8);
    let end = offset
        .bytes()
        .checked_add(byte_len)
        .ok_or("global allocation constant offset overflows")?;
    if end > alloc.size().bytes() {
        return Err(format!(
            "global allocation constant range [{}..{end}) exceeds allocation size {}",
            offset.bytes(),
            alloc.size().bytes()
        ));
    }
    let range = AllocRange {
        start: offset,
        size: Size::from_bytes(byte_len),
    };
    if !alloc.provenance().range_empty(range, cx) {
        return Err("provenance-bearing global allocation constants are unsupported".into());
    }
    let scalar = alloc
        .read_scalar(cx, range, false)
        .map_err(|err| format!("unreadable global allocation constant: {err:?}"))?;
    let mir::interpret::Scalar::Int(scalar_int) = scalar else {
        return Err("provenance-bearing global allocation constants are unsupported".into());
    };
    if scalar_int.size().bits() != u64::from(width) {
        return Err("global allocation constant width disagrees with its type".into());
    }
    Ok(scalar_int.to_bits_unchecked())
}

/// Extract MIR unary operators (`Not` and `Neg`), refusing `PtrMetadata`
/// ("Gets the metadata `M` from a `*const`/`*mut`/`&`/`&mut`").
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617
fn un_op(op: mir::UnOp) -> Result<ir::UnOp> {
    Ok(match op {
        mir::UnOp::Not => ir::UnOp::Not,
        mir::UnOp::Neg => ir::UnOp::Neg,
        mir::UnOp::PtrMetadata => return Err(format!("unsupported unary operator: {op:?}")),
    })
}

/// Extract MIR cast kinds, admitting only `CastKind::IntToInt` and refusing
/// pointer, float, transmute, and subtype casts exhaustively.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532
fn cast_kind(kind: mir::CastKind) -> Result<ir::CastKind> {
    match kind {
        mir::CastKind::IntToInt => Ok(ir::CastKind::IntToInt),
        mir::CastKind::PointerExposeProvenance
        | mir::CastKind::PointerWithExposedProvenance
        | mir::CastKind::PointerCoercion(..)
        | mir::CastKind::FloatToInt
        | mir::CastKind::FloatToFloat
        | mir::CastKind::IntToFloat
        | mir::CastKind::PtrToPtr
        | mir::CastKind::FnPtrToPtr
        | mir::CastKind::Transmute
        | mir::CastKind::Subtype => Err(format!("unsupported cast kind: {kind:?}")),
    }
}

/// Preserve the ordinary MIR operators. In particular, ordinary shifts use
/// "RHS.rem_euclid(LHS::BITS)"; the unchecked variants have a different UB
/// contract and are rejected. The model interprets these operators, including
/// signed comparisons, division/remainder UB, three-way comparison (`Cmp`), and
/// wrapping or `(T, bool)` overflowing arithmetic, rather than the adapter.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1708
fn bin_op(op: mir::BinOp) -> Result<ir::BinOp> {
    Ok(match op {
        mir::BinOp::BitAnd => ir::BinOp::BitAnd,
        mir::BinOp::BitOr => ir::BinOp::BitOr,
        mir::BinOp::BitXor => ir::BinOp::BitXor,
        mir::BinOp::Shl => ir::BinOp::Shl,
        mir::BinOp::Shr => ir::BinOp::Shr,
        mir::BinOp::Add => ir::BinOp::Add,
        mir::BinOp::Sub => ir::BinOp::Sub,
        mir::BinOp::Mul => ir::BinOp::Mul,
        mir::BinOp::Div => ir::BinOp::Div,
        mir::BinOp::Rem => ir::BinOp::Rem,
        mir::BinOp::AddWithOverflow => ir::BinOp::AddWithOverflow,
        mir::BinOp::SubWithOverflow => ir::BinOp::SubWithOverflow,
        mir::BinOp::MulWithOverflow => ir::BinOp::MulWithOverflow,
        mir::BinOp::Eq => ir::BinOp::Eq,
        mir::BinOp::Ne => ir::BinOp::Ne,
        mir::BinOp::Lt => ir::BinOp::Lt,
        mir::BinOp::Le => ir::BinOp::Le,
        mir::BinOp::Gt => ir::BinOp::Gt,
        mir::BinOp::Ge => ir::BinOp::Ge,
        mir::BinOp::Cmp => ir::BinOp::Cmp,
        other => return Err(format!("unsupported binary operator: {other:?}")),
    })
}

/// `Use` "yields the operand unchanged, except for a potential retag."
/// `rustc` lowers ordinary assignments to `Rvalue::Use(_, WithRetag::Yes)`,
/// which in Miri (`Miri/Interpreter/Rvalue.lean` + `ValidityVisitor.lean`)
/// invokes `retagSafePointer` only on safe-pointer types (`&T`, `&mut T`,
/// `Box<T>`). `ir::Body::try_new` admits `with_retag == true` only when
/// `dst_ty.is_retag_noop()`, so future pointer/reference extensions fail
/// closed until retagging is modeled. Binary operands may have different types
/// for shifts; no casts are inserted.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1365
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1403-L1443
fn rvalue<'tcx>(tcx: TyCtxt<'tcx>, value: &mir::Rvalue<'tcx>) -> Result<ir::Rvalue> {
    Ok(match value {
        mir::Rvalue::Use(op, with_retag) => ir::Rvalue::Use {
            operand: operand(tcx, op)?,
            with_retag: with_retag.yes(),
        },
        mir::Rvalue::BinaryOp(op, values) => ir::Rvalue::Binary {
            op: bin_op(*op)?,
            left: operand(tcx, &values.0)?,
            right: operand(tcx, &values.1)?,
        },
        mir::Rvalue::UnaryOp(op, value) => ir::Rvalue::Unary {
            op: un_op(*op)?,
            operand: operand(tcx, value)?,
        },
        mir::Rvalue::Cast(kind, value, target_ty) => ir::Rvalue::Cast {
            cast_kind: cast_kind(*kind)?,
            operand: operand(tcx, value)?,
            ty: ty(tcx, *target_ty)?,
        },
        mir::Rvalue::Discriminant(place) => ir::Rvalue::Discriminant {
            local: local(place)?,
        },
        // This also refuses `Aggregate(Tuple, ..)` and `Aggregate(Adt, ..)`.
        // `Trusted.MirSemantics` models unit constants via `Use` and overflow
        // pairs via `*WithOverflow`, and rejects tuple and ADT `Aggregate`
        // rvalues with `.unsupported`.
        other => return Err(format!("unsupported rvalue: {other:?}")),
    })
}

/// Storage markers survive capture (`"Using a local in any way (not only
/// reading/writing from it) while it is unallocated is UB."`).
/// `PlaceMention` survives capture because `-Zmir-preserve-ub` disables
/// `RemovePlaceMention`; mentions with projections fail closed because
/// `"When executed at runtime, this computes the given place, but then
/// discards it without doing a load."` can dereference pointers or project
/// fields, while unprojected `Sized` locals are recorded as
/// [`ir::Statement::PlaceMention`], validated as `Sized` in
/// [`ir::Body::try_new`], and lowered to `StatementKind.nop` matching Miri
/// (`eval_place` + `local_to_place` check only local bounds without `.access()`
/// or loading memory; see `Trusted/MirSemantics.lean` and
/// `Trusted/MirAst/Statements.lean`). `Nop` alone has no effect.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L364-L393
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L442-L443
fn statement<'tcx>(tcx: TyCtxt<'tcx>, stmt: &mir::StatementKind<'tcx>) -> Result<ir::Statement> {
    Ok(match stmt {
        mir::StatementKind::Assign(value) => ir::Statement::Assign {
            local: local(&value.0)?,
            value: rvalue(tcx, &value.1)?,
        },
        mir::StatementKind::StorageLive(local) => ir::Statement::StorageLive {
            local: local.as_u32(),
        },
        mir::StatementKind::StorageDead(local) => ir::Statement::StorageDead {
            local: local.as_u32(),
        },
        mir::StatementKind::PlaceMention(place) => {
            if !place.projection.is_empty() {
                return Err(format!(
                    "PlaceMention with projections is unsupported: {place:?}"
                ));
            }
            ir::Statement::PlaceMention {
                local: place.local.as_u32(),
            }
        }
        mir::StatementKind::Nop => ir::Statement::Nop,
        other => return Err(format!("unsupported statement: {other:?}")),
    })
}

/// Fail closed on `TerminatorKind::Call` with `CallSource::Use` before any
/// future `Call` lowering can run.
///
/// Under `#![feature(ergonomic_clones)]`, `rustc_codegen_ssa` runs
/// `optimize_use_clone` after `Runtime(PostCleanup)` capture (`"Replace
/// `clone` calls that come from `use` statements with direct copies if
/// possible."`), which can rewrite `CallSource::Use` calls on `&T` (`T: Copy`)
/// to bitwise copies even when `<T as Clone>::clone` is non-trivial, diverging
/// from captured MIR and Miri.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L217-L224
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L350-L407
fn check_call_source(call_source: mir::CallSource) -> Result<()> {
    match call_source {
        mir::CallSource::Use => Err(
            "CallSource::Use call terminators are unsupported: post-capture \
             optimize_use_clone may rewrite Clone::clone to a bitwise copy \
             for Copy types, diverging from captured MIR"
                .into(),
        ),
        mir::CallSource::Normal
        | mir::CallSource::OverloadedOperator
        | mir::CallSource::MatchCmp
        | mir::CallSource::Misc => Ok(()),
    }
}

/// `SwitchInt` evaluates its operand and selects an explicit or otherwise edge.
/// `Unreachable` is retained because "Executing this terminator is UB."
/// Diverging calls (`TerminatorKind::Call { target: None, .. }`, e.g.
/// `zx_process_exit -> !` or `_start -> !`) never return to a continuation
/// block (`target` is "Where to go after this call returns. If none, the
/// call necessarily diverges."); after checking [`check_call_source`], they
/// lower to `ir::Terminator::Unsupported`
/// (`Trusted.MirAst.TerminatorKind.unsupported`), which steps fail-closed to
/// `.fault .unsupported` in `Trusted.MirSemantics` if reachable while
/// permitting verified functions whose diverging guard branches are proved
/// unreachable.
/// Returning calls (`target: Some(_)`), `Drop`, unwind, assembly, and all
/// other terminators stay refused at capture time.
/// `TerminatorKind::Call` explicitly runs [`check_call_source`] first so
/// `CallSource::Use` fails closed even for diverging calls.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L692-L740
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L800-L821
fn terminator<'tcx>(tcx: TyCtxt<'tcx>, term: &mir::TerminatorKind<'tcx>) -> Result<ir::Terminator> {
    Ok(match term {
        mir::TerminatorKind::Goto { target } => ir::Terminator::Goto {
            block: target.as_u32(),
        },
        mir::TerminatorKind::SwitchInt { discr, targets } => ir::Terminator::SwitchInt {
            operand: operand(tcx, discr)?,
            targets: targets
                .iter()
                .map(|(value, block)| (value, block.as_u32()))
                .collect(),
            otherwise: targets.otherwise().as_u32(),
        },
        mir::TerminatorKind::Return => ir::Terminator::Ret,
        mir::TerminatorKind::Unreachable => ir::Terminator::Unreachable,
        mir::TerminatorKind::Call {
            call_source,
            target,
            ..
        } => {
            check_call_source(*call_source)?;
            if target.is_none() {
                ir::Terminator::Unsupported
            } else {
                return Err(format!("unsupported terminator: {term:?}"));
            }
        }
        other => return Err(format!("unsupported terminator: {other:?}")),
    })
}

/// Bind an item to an owned, versioned source identity for this compiler.
///
/// The pinned compiler calls `def_path_str` a string "suitable for user
/// output"; it is not a stable identifier contract. Anneal's v1 scheme fixes
/// that pinned semantic path printer with trimming and visible reexports
/// disabled. Thus a public alias cannot replace the defining path. In this
/// phase impl paths use their self/trait types rather than file positions.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L115-L124
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2191-L2210
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2266-L2306
///
/// Raw compiler indices cannot identify a contract across source edits. Even a
/// raw DefPath disambiguator has "some artificial ordering dependency", notably
/// for impl blocks, so v1 uses the pinned semantic owner/type path instead.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/definitions.rs#L103-L109
///
/// Identities are crate-relative and tied to this scheme and compiler pin.
/// Item renames and owner changes change the key. Toolchain changes require
/// reviewing the scheme and its specifications; this is an Anneal format, not
/// an assumption that Rust's diagnostic formatter remains stable forever.
///
/// Anonymous-owner components can still depend on source order. Such functions
/// are admitted only through selected scope today, whose reviewed roots already
/// expose selectors such as `outer::{closure#0}::inner`. This v1 key exposes
/// the same selector; persistent identity across anonymous-owner edits needs a
/// reviewed stable anchor or a separate binding protocol. It is not established
/// by prefixing a diagnostic path with a version number.
///
/// `ir::Program::try_new` separately refuses duplicate function identities
/// before publishing a subject, so a printer collision cannot share one
/// contract between distinct functions. `capture.rs` performs the
/// corresponding check for the enum keys that [`enum_id`] derives from this
/// identity.
fn item_identity(tcx: TyCtxt<'_>, def: DefId) -> String {
    let path = rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(tcx.def_path_str(def))
    );
    format!("rust-path-v1::{path}")
}

/// Key a crate-local enum for `Trusted.MirAst.EnumTy.id`.
///
/// Lean compares this key when deciding enum type equality, and a reviewed
/// specification may name it as a literal. A `DefIndex` would silently select
/// another type once unrelated items are inserted before the enum. The key is
/// instead the first four bytes, read big-endian, of the SHA-256 digest of
/// `anneal:enum:v1:` followed by the enum's `item_identity`. The key thus
/// follows that identity, including its anonymous-owner caveat: renaming or
/// moving the enum changes the key, while inserting or reordering unrelated
/// items does not.
///
/// Truncation to the `u32` width of `ir::EnumTy`'s key can collide, and
/// distinct definitions can print the same path (for example, same-named enums
/// in sibling blocks of one function or repeated anonymous `const _` blocks).
/// `capture.rs` therefore refuses any admitted or captured enum key that two
/// local enum definitions in the crate share, while ignoring collisions among
/// unreferenced enums outside the captured scope.
pub fn enum_id(tcx: TyCtxt<'_>, def: DefId) -> u32 {
    let digest = Sha256::digest(format!("anneal:enum:v1:{}", item_identity(tcx, def)));
    u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]])
}

/// The only codegen flags admitted: hints that change neither the captured
/// body nor its entry contract.
///
/// `#[cold]` "suggests that the attributed function is unlikely to be called
/// which may help the compiler produce better code."
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L91-L92
///
/// `#[track_caller]` "allows code within `f` to get a hint of the `Location`
/// of the "topmost" tracked call", which `core` observes through "the
/// `core::intrinsics::caller_location` intrinsic". `rustc` passes the
/// location "by appending an implicit parameter to the function ABI", outside
/// the MIR locals. Reading it takes a returning call (with `caller_location`
/// returning `&'static Location<'_>`), and the admitted fragment refuses every
/// returning call (`target: Some(_)`) and assertion terminator, so no captured
/// body can observe it.
/// The compiler also sets this flag when a trait method inherits the
/// attribute from its declaration.
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L763-L779
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L855-L856
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L355-L358
///
/// Every other flag at the pinned revision is refused; see [`codegen_attrs`].
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L156-L214
const ADMITTED_CODEGEN_FLAGS: CodegenFnAttrFlags =
    CodegenFnAttrFlags::COLD.union(CodegenFnAttrFlags::TRACK_CALLER);

/// Refuse code-generation attributes whose effect the model does not state.
///
/// `codegen_fn_attrs` combines an item's codegen attributes with the settings
/// that the compiler implies for it. Destructuring every field of
/// `CodegenFnAttrs` makes a compiler upgrade that adds a field fail to compile
/// here until the field is classified. Only settings that cannot change what
/// a call executes or what the body may assume are admitted: inlining hints,
/// `#[optimize]` goals, and [`ADMITTED_CODEGEN_FLAGS`]. Everything else is a
/// refusal, including attributes that are rare or impossible on an admitted
/// function, so an unclassified case cannot pass silently.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L60-L112
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L551-L577
fn codegen_attrs(tcx: TyCtxt<'_>, def: LocalDefId) -> Result<()> {
    let CodegenFnAttrs {
        flags,
        inline,
        optimize,
        symbol_name,
        foreign_item_symbol_aliases,
        link_ordinal,
        target_features,
        safe_target_features,
        linkage,
        import_linkage,
        link_section,
        sanitizers,
        instruction_set,
        alignment,
        patchable_function_entry,
        objc_class,
        objc_selector,
    } = tcx.codegen_fn_attrs(def);
    // Refuse `#[target_feature]` functions. `target_features` records "The
    // `#[target_feature(enable = "...")]` attribute and the enabled
    // features", and `safe_target_features` records "Whether the function was
    // declared safe, but has target features". A safe function with target
    // features has `HeaderSafety::SafeTargetFeatures`; the type system "treats
    // this function as an unsafe function", and `FnHeader::safety` maps it to
    // `Safety::Unsafe`. The signature safety read in [`body`] would therefore
    // report `Unsafe`, capture would emit `isUnsafe := true`, and verification
    // would assume `specs.safety` without modeling the hardware-feature entry
    // obligation.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L82-L87
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4668-L4673
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4708-L4713
    if !target_features.is_empty() || *safe_target_features {
        return Err("target-feature entry obligations are unsupported".into());
    }
    // `linkage` holds "The `#[linkage = "..."]` attribute on Rust-defined
    // items", whose values are LLVM linkage types. The LLVM that the pinned
    // compiler builds against (its `src/llvm-project` submodule) never emits
    // an `available_externally` definition: "From the linker's perspective,
    // an `available_externally` global is equivalent to an external
    // declaration." `linkonce` globals "are merged with other globals of the
    // same name when linkage occurs", so "the body may be overridden with a
    // more definitive definition later", and `weak` "has the same merging
    // semantics". As with the intrinsics refused in [`body`], calls need not
    // execute the captured body. `import_linkage` is the same attribute on a
    // foreign item, which has no body to capture; refuse it too.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L88-L91
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/attrs/data_structures.rs#L282-L298
    // https://github.com/rust-lang/llvm-project/blob/08c84e69a84d95936296dfcab0e38b34100725d5/llvm/docs/LangRef.rst?plain=1#L237-L264
    if let Some(linkage) = linkage.or(*import_linkage) {
        return Err(format!(
            "linkage attribute {linkage:?} is unsupported: calls need not execute the captured body"
        ));
    }
    // Symbol and section attributes impose link-time obligations that neither
    // the captured body nor `isUnsafe`, which [`body`] reads from the
    // signature alone, records. The Reference requires `unsafe` on each:
    // `export_name` because "a symbol with a custom name may collide with
    // another symbol with the same name (or with a well-known symbol),
    // leading to undefined behavior", `no_mangle` (the `NO_MANGLE` flag
    // below) for the same collision, and `link_section` because "it allows
    // users to place data and code into sections of memory not expecting
    // them". `symbol_name` is "The name this function will be
    // imported/exported under"; weak lang items also receive one.
    // `foreign_item_symbol_aliases` additionally exports this function under
    // the symbol of a foreign item that it should "satisfy", binding calls to
    // that item, whose contract the model does not state, to this body.
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/abi.md?plain=1#L114-L115
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/abi.md?plain=1#L145-L146
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/abi.md?plain=1#L172-L173
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L67-L76
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L92-L94
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L518-L523
    if let Some(name) = symbol_name {
        return Err(format!(
            "exported symbol name `{name}` is unsupported: symbol obligations are unmodeled"
        ));
    }
    if let Some(section) = link_section {
        return Err(format!(
            "link section `{section}` is unsupported: section obligations are unmodeled"
        ));
    }
    if !foreign_item_symbol_aliases.is_empty() {
        return Err("foreign-item symbol aliases are unsupported".into());
    }
    // Refuse every flag outside [`ADMITTED_CODEGEN_FLAGS`]. The others carry
    // obligations or behavior the model lacks: `NO_MANGLE`,
    // `RUSTC_STD_INTERNAL_SYMBOL` (a "weird symbol" with "slightly different
    // linkage, visibility, and reachability rules"), and
    // `EXTERNALLY_IMPLEMENTABLE_ITEM` bind symbols; `NEVER_UNWIND` asserts
    // that the "function will never unwind"; the allocator flags make claims
    // such as "the pointer returned from this function is never null";
    // `NAKED` omits the prologue; `OFFLOAD_KERNEL` adds "an extra ptr arg";
    // and `NO_BUILTINS` (set for every function of a `#![no_builtins]` crate)
    // is unreviewed. The rest apply to statics or foreign items.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L156-L214
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L348-L353
    let unmodeled = flags.difference(ADMITTED_CODEGEN_FLAGS);
    if !unmodeled.is_empty() {
        return Err(format!(
            "codegen attribute flags {unmodeled:?} are unsupported"
        ));
    }
    // The Reference documents three inlining modes and says: "In every form
    // the attribute is a hint. The compiler may ignore it." Forced inlining
    // (`#[rustc_force_inline]`) is an internal attribute outside those modes,
    // so it stays refused until reviewed. An `#[optimize]` goal (`none`,
    // `speed` or `size`) selects optimization effort, which must preserve the
    // captured MIR's meaning just as the optimization level must. Matching
    // every variant makes a new mode fail to compile here.
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L65-L73
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/attrs/data_structures.rs#L108-L150
    match inline {
        InlineAttr::None | InlineAttr::Hint | InlineAttr::Always | InlineAttr::Never => {}
        InlineAttr::Force { .. } => {
            return Err("forced inlining is unsupported".into());
        }
    }
    match optimize {
        OptimizeAttr::Default
        | OptimizeAttr::DoNotOptimize
        | OptimizeAttr::Speed
        | OptimizeAttr::Size => {}
    }
    // The remaining settings have no counterpart in the model: `#[sanitize]`
    // overrides, `#[instruction_set]`, function alignment (from
    // `#[rustc_align]` or `-Zmin-function-alignment`, which capture does not
    // pass), the "nops ... around the function entry" that
    // `#[patchable_function_entry]` reserves for patching, the foreign-only
    // `#[link_ordinal]`, and Objective-C class and selector names.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L77-L81
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L95-L111
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L305-L317
    if *sanitizers != SanitizerFnAttrs::default() {
        return Err(format!("sanitizer settings {sanitizers:?} are unsupported"));
    }
    if let Some(set) = instruction_set {
        return Err(format!("instruction set {set:?} is unsupported"));
    }
    if let Some(align) = alignment {
        return Err(format!("function alignment {align:?} is unsupported"));
    }
    if patchable_function_entry.is_some() {
        return Err("patchable function entries are unsupported".into());
    }
    if link_ordinal.is_some() || objc_class.is_some() || objc_selector.is_some() {
        return Err("link ordinals and Objective-C names are unsupported".into());
    }
    Ok(())
}

/// Translate the provider's exact body. `required_consts` is explicitly
/// "soundness-critical"; an unrepresented required constant is a refusal,
/// independent of runtime preconditions or whether any return is reachable.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L265-L271
pub fn body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &mir::Body<'tcx>) -> Result<ir::Body> {
    // Refuse intrinsics before reading the body: calls to an intrinsic need
    // not execute its fallback body. Once `#![feature(intrinsics)]` is
    // enabled, `intrinsic_raw` "Determines whether an item is an intrinsic"
    // from the `#[rustc_intrinsic]` attribute, even when the function has a
    // fallback body. Calls resolve to `ty::InstanceKind::Intrinsic(def_id)`,
    // and `LowerIntrinsics`, which runs before `Runtime(PostCleanup)`,
    // rewrites calls by intrinsic name in this crate and downstream: a call
    // to `unreachable` becomes `TerminatorKind::Unreachable` even when the
    // fallback body is a benign loop. A contract verified for the fallback
    // body therefore need not describe what callers execute.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/context.rs#L2667-L2673
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/util.rs#L1669-L1689
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ty_utils/src/instance.rs#L35-L37
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/lib.rs#L649-L663
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/lower_intrinsics.rs#L17-L25
    if let Some(intrinsic) = tcx.intrinsic(def) {
        return Err(format!(
            "intrinsic `{}` is unsupported: calls need not execute its fallback body",
            intrinsic.name
        ));
    }
    // Defense in depth: `-Zmir-preserve-ub` disables `RemovePlaceMention` and
    // trivial `SwitchInt` read erasure before `Runtime(PostCleanup)`.
    if !tcx.sess.opts.unstable_opts.mir_preserve_ub {
        return Err(
            "capture requires -Zmir-preserve-ub so PlaceMention and SwitchInt \
             UB checks survive Runtime(PostCleanup)"
                .into(),
        );
    }
    // Refuse crates enabling `#![feature(ergonomic_clones)]`: post-capture
    // `optimize_use_clone` in `rustc_codegen_ssa` ("Replace `clone` calls that
    // come from `use` statements with direct copies if possible", guarded by
    // `if tcx.features().ergonomic_clones()`) rewrites `CallSource::Use` calls
    // on `&T` (`T: Copy`) to bitwise copies after `Runtime(PostCleanup)`.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L217-L224
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L350-L407
    if tcx.features().ergonomic_clones() {
        return Err(
            "#![feature(ergonomic_clones)] is unsupported during capture: \
             post-capture optimize_use_clone can diverge from captured MIR"
                .into(),
        );
    }
    // The phase determines the meaning and allowed grammar of MIR. The
    // compiler's phase field records progress through "desugaring and
    // optimization". Refuse another phase instead of guessing how to normalize
    // it into the syntax modeled here.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L211-L216
    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        return Err(format!("unexpected MIR phase: {:?}", body.phase));
    }
    // For injected bodies, "Everything that comes before this `MirPhase`
    // should be skipped." The phase alone cannot establish ordinary lowering.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L302-L309
    if body.injection_phase.is_some() {
        return Err("compiler-injected MIR is unsupported".into());
    }
    // An error-tainted body is not compiler approval. Coroutine state and
    // rust-call tuple spreading need entry/continuation rules absent from this
    // IR. `spread_arg` passes "its individual components at the LLVM level";
    // treating that as ordinary flat arguments would change the call contract.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L227-L257
    if body.tainted_by_errors.is_some() || body.coroutine.is_some() || body.spread_arg.is_some() {
        return Err("tainted, coroutine or spread-argument body is unsupported".into());
    }
    // `None` means "the list has not been computed yet", not an empty set of
    // obligations. Even a valid scalar runtime body cannot waive a missing or
    // nonempty compile-time obligation inventory.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L265-L271
    if !matches!(body.required_consts.as_deref(), Some([])) {
        return Err("required constants are unavailable in the scalar model".into());
    }
    // One captured body has one concrete scalar argument/type interpretation.
    // Generic entry points would require quantified instantiation obligations;
    // compiler completion alone does not prove every future instantiation.
    // `Generics` describes "the formal type/lifetime parameters associated
    // with an item or method", optionally starting with `Self`, and `count`
    // is `self.parent_count + self.own_params.len()`. A method therefore also
    // counts its parent's parameters, including a trait's implicit `Self`.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/generics.rs#L112-L116
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/generics.rs#L153-L156
    if tcx.generics_of(def).count() != 0 {
        return Err("generic functions require quantified instantiation obligations".into());
    }
    // With generics refused, the identity instantiation is the only one.
    // `skip_binder` "is only valid when you are either extracting data that
    // does not reference any generic arguments": the ABI, C-variadic and
    // safety flags read below live in `fn_sig_kind`, separately from the
    // argument and return types that late-bound regions can reference.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/unnormalized.rs#L96-L100
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/binder.rs#L164-L170
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L899-L904
    let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
    // The model has ordinary Rust arguments and no foreign/variadic calling
    // convention or hardware-feature entry conditions. Do not infer those
    // missing preconditions merely because the body happens to use scalars.
    // `abi` returns the ABI "including the unwind flag", `c_variadic` answers
    // "Do the function arguments end with a C-style variadic argument?", and
    // `ExternAbi::Rust` is the native Rust ABI ("that's us!").
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L871-L890
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L929-L935
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/extern_abi.rs#L31-L32
    if signature.abi() != ExternAbi::Rust || signature.c_variadic() {
        return Err("only non-variadic Rust ABI functions are admitted".into());
    }
    // Codegen attributes can make calls execute another definition or add
    // entry and link-time obligations that the signature does not record.
    codegen_attrs(tcx, def)?;
    // A cleanup block "lies on an unwind path", and "Unwind blocks must only
    // branch to other unwind blocks." Such blocks need an unwinding
    // interpretation even when their ordinary edges are unreachable, and the
    // scalar fragment has none. Checking every block before translating
    // locals keeps this refusal reachable: holding a value with drop glue
    // across a call that may unwind produces a cleanup block and also a
    // non-scalar local, which local translation would otherwise report first.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L1337-L1341
    if let Some((id, _)) = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, block)| block.is_cleanup)
    {
        return Err(format!("cleanup block {id:?} is unsupported"));
    }
    // Preserve all compiler locals and blocks, including unused locals and
    // unreachable blocks. The compiler places arguments "Starting at local 1"
    // and block references index its basic-block vector. Filtering or
    // renumbering would change the subject and require a separate proof.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L207-L209
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L235-L251
    let local_tys = body
        .local_decls
        .iter()
        .map(|decl| ty(tcx, decl.ty))
        .collect::<Result<Vec<_>>>()?;
    let blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(id, block)| {
            let statements = block
                .statements
                .iter()
                .enumerate()
                .map(|(index, stmt)| {
                    statement(tcx, &stmt.kind)
                        .map_err(|error| format!("{id:?} statement {index}: {error}"))
                })
                .collect::<Result<Vec<_>>>()?;
            // The terminator "should generally ONLY be `None` during
            // construction"; a provided body without one is malformed.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L1327-L1335
            let term = block.terminator.as_ref().ok_or("missing terminator")?;
            let terminator = terminator(tcx, &term.kind)
                .map_err(|error| format!("{id:?} terminator: {error}"))?;
            Ok(ir::Block {
                statements,
                terminator,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    // fn_sig lowers ordinary declarations with "sig.header.safety()";
    // lower_fn_ty preserves it with ".set_safety(safety)". FnSig::safety
    // delegates to the getter documented as "Returns the safety mode."
    // hir::Safety::is_unsafe is "!self.is_safe()", with Unsafe/Safe mapped
    // to false/true by is_safe. Read declaration safety from that signature,
    // not from whether this scalar MIR happens to contain unsafe operations.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_analysis/src/collect.rs#L1066-L1084
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs#L3434-L3458
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L882-L885
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L925-L927
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4610-L4621
    //
    // The model uses this bit to decide whether reviewed caller requirements
    // apply. `codegen_attrs` above excludes target-feature entry points and
    // unsafe symbol and section attributes, whose obligations this bit does
    // not record; pointer-free syntax alone does not authorize treating an
    // unsafe declaration as an unrestricted safe entry point.
    ir::Body::try_new(
        body.arg_count,
        signature.safety().is_unsafe(),
        local_tys,
        blocks,
        item_identity(tcx, def.to_def_id()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn use_retag_is_admitted_only_for_retag_noop_types() {
        let u64_ty = ir::Ty::Int(IntTy {
            width: IntWidth::I64,
            signed: false,
        });
        assert!(ir::check_use_retag(&u64_ty, false).is_ok());
        assert!(ir::check_use_retag(&u64_ty, true).is_ok());
        assert!(ir::check_use_retag(&ir::Ty::Bool, true).is_ok());
        assert!(ir::check_use_retag(&ir::Ty::Unit, true).is_ok());
        let ety = ir::EnumTy::try_new(
            1,
            IntTy {
                width: IntWidth::Isize,
                signed: true,
            },
            ir::EnumTagRepr::Scalar(IntTy {
                width: IntWidth::I8,
                signed: false,
            }),
            vec![0, 1],
        )
        .unwrap();
        assert!(ir::check_use_retag(&ir::Ty::Enum(ety), true).is_ok());
    }

    #[test]
    fn enum_ty_constructor_enforces_discriminant_and_tag_invariants() {
        let isize_discr = IntTy {
            width: IntWidth::Isize,
            signed: true,
        };
        assert!(ir::EnumTy::try_new(1, isize_discr, ir::EnumTagRepr::ZeroSized, vec![0]).is_ok());
        assert!(ir::EnumTy::try_new(1, isize_discr, ir::EnumTagRepr::ZeroSized, vec![]).is_err());
        assert!(
            ir::EnumTy::try_new(1, isize_discr, ir::EnumTagRepr::ZeroSized, vec![0, 1]).is_err()
        );
        let i8_signed = ir::EnumTagRepr::Scalar(IntTy {
            width: IntWidth::I8,
            signed: true,
        });
        let u8_unsigned = ir::EnumTagRepr::Scalar(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        assert!(
            ir::EnumTy::try_new(2, isize_discr, i8_signed, vec![u128::from(u64::MAX), 0, 1])
                .is_ok()
        );
        assert!(ir::EnumTy::try_new(2, isize_discr, i8_signed, vec![7, 7]).is_err());
        assert!(
            ir::EnumTy::try_new(
                2,
                isize_discr,
                u8_unsigned,
                vec![u128::from(u64::MAX), 0, 1]
            )
            .is_err()
        );
        assert!(
            ir::EnumTy::try_new(
                3,
                IntTy {
                    width: IntWidth::I8,
                    signed: false,
                },
                u8_unsigned,
                vec![256]
            )
            .is_err()
        );
    }

    #[test]
    fn body_and_program_constructors_enforce_static_admission_and_unique_identities() {
        let block = ir::Block {
            statements: vec![],
            terminator: ir::Terminator::Ret,
        };
        assert!(
            ir::Body::try_new(
                0,
                false,
                vec![ir::Ty::Unit],
                vec![],
                "rust-path-v1::empty".into(),
            )
            .is_err()
        );
        assert!(
            ir::Body::try_new(
                1,
                false,
                vec![ir::Ty::Unit],
                vec![block.clone()],
                "rust-path-v1::bad_args".into(),
            )
            .is_err()
        );
        assert!(
            ir::Body::try_new(
                0,
                false,
                vec![ir::Ty::Unit],
                vec![ir::Block {
                    statements: vec![ir::Statement::StorageLive { local: 3 }],
                    terminator: ir::Terminator::Ret,
                }],
                "rust-path-v1::oob_storage".into(),
            )
            .is_err()
        );

        let valid = ir::Body::try_new(
            0,
            false,
            vec![ir::Ty::Unit],
            vec![block],
            "rust-path-v1::entry".into(),
        )
        .unwrap();
        assert!(ir::Program::try_new(ir::Scope::Crate, vec![]).is_err());
        assert!(
            ir::Program::try_new(
                ir::Scope::SelectedUnit {
                    roots: std::collections::BTreeSet::new(),
                },
                vec![valid.clone()],
            )
            .is_err()
        );
        let duplicate =
            ir::Program::try_new(ir::Scope::Crate, vec![valid.clone(), valid]).unwrap_err();
        assert!(duplicate.contains("ambiguous captured function identity"));
    }

    #[test]
    fn body_constructor_rejects_storage_dead_return_place_and_invalid_constants() {
        let u8_ty = ir::Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let storage_dead_ret = ir::Body::try_new(
            0,
            false,
            vec![u8_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::StorageDead { local: 0 }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::dead_ret".into(),
        )
        .unwrap_err();
        assert!(storage_dead_ret.contains("StorageDead on return place _0"));

        let u8_overflow = ir::Body::try_new(
            0,
            false,
            vec![u8_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    local: 0,
                    value: ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: u8_ty.clone(),
                            lit: ConstLit::Scalar { bits: 300 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::u8_overflow".into(),
        )
        .unwrap_err();
        assert!(u8_overflow.contains("exceeds 8-bit width"));

        let signed_enum = ir::EnumTy::try_new(
            7,
            IntTy {
                width: IntWidth::Isize,
                signed: true,
            },
            ir::EnumTagRepr::Scalar(IntTy {
                width: IntWidth::I8,
                signed: true,
            }),
            vec![u128::from(u64::MAX), 0, 1],
        )
        .unwrap();
        let enum_ty = ir::Ty::Enum(signed_enum);
        let enum_tag_overflow = ir::Body::try_new(
            0,
            false,
            vec![enum_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    local: 0,
                    value: ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: enum_ty.clone(),
                            lit: ConstLit::Scalar { bits: 256 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::enum_overflow".into(),
        )
        .unwrap_err();
        assert!(enum_tag_overflow.contains("exceeds 8-bit tag width"));

        let enum_bad_variant = ir::Body::try_new(
            0,
            false,
            vec![enum_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    local: 0,
                    value: ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: enum_ty.clone(),
                            lit: ConstLit::Scalar { bits: 5 },
                        },
                        with_retag: false,
                    },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::enum_bad_variant".into(),
        )
        .unwrap_err();
        assert!(enum_bad_variant.contains("does not match any declared variant"));

        let valid_neg = ir::Body::try_new(
            0,
            false,
            vec![enum_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    local: 0,
                    value: ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: enum_ty,
                            lit: ConstLit::Scalar { bits: 0xff },
                        },
                        with_retag: false,
                    },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::enum_neg_tag".into(),
        )
        .unwrap();
        let zst_enum = ir::Ty::Enum(
            ir::EnumTy::try_new(
                8,
                IntTy {
                    width: IntWidth::Isize,
                    signed: true,
                },
                ir::EnumTagRepr::ZeroSized,
                vec![42],
            )
            .unwrap(),
        );
        let valid_zst = ir::Body::try_new(
            0,
            false,
            vec![zst_enum.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    local: 0,
                    value: ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: zst_enum,
                            lit: ConstLit::ZeroSized,
                        },
                        with_retag: false,
                    },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::enum_zst".into(),
        )
        .unwrap();
        let prog = ir::Program::try_new(
            ir::Scope::SelectedUnit {
                roots: std::collections::BTreeSet::from(["enum_neg_tag".into(), "enum_zst".into()]),
            },
            vec![valid_neg, valid_zst],
        )
        .unwrap();
        let rendered = crate::lean::render(&prog);
        assert!(
            rendered.contains("ConstLit.scalar (BitVec.ofNat 128 255)"),
            "{rendered}"
        );
        assert!(rendered.contains("ConstLit.zeroSized"), "{rendered}");

        let non_enum_discr = ir::Body::try_new(
            1,
            false,
            vec![u8_ty.clone(), u8_ty],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    local: 0,
                    value: ir::Rvalue::Discriminant { local: 1 },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::non_enum_discr".into(),
        )
        .unwrap_err();
        assert!(non_enum_discr.contains("requires a fieldless enum or Ordering local"));
    }

    #[test]
    fn operator_and_cast_extractors_admit_modeled_variants_and_refuse_others() {
        assert_eq!(un_op(mir::UnOp::Not).unwrap(), ir::UnOp::Not);
        assert_eq!(un_op(mir::UnOp::Neg).unwrap(), ir::UnOp::Neg);
        assert!(
            un_op(mir::UnOp::PtrMetadata)
                .unwrap_err()
                .contains("unsupported unary operator")
        );

        assert_eq!(
            cast_kind(mir::CastKind::IntToInt).unwrap(),
            ir::CastKind::IntToInt
        );
        for refused_cast in [
            mir::CastKind::PointerExposeProvenance,
            mir::CastKind::PointerWithExposedProvenance,
            mir::CastKind::FloatToInt,
            mir::CastKind::FloatToFloat,
            mir::CastKind::IntToFloat,
            mir::CastKind::PtrToPtr,
            mir::CastKind::FnPtrToPtr,
            mir::CastKind::Transmute,
            mir::CastKind::Subtype,
        ] {
            let err = cast_kind(refused_cast).unwrap_err();
            assert!(err.contains("unsupported cast kind"), "{err}");
        }

        for (mir_op, expected) in [
            (mir::BinOp::Div, ir::BinOp::Div),
            (mir::BinOp::Rem, ir::BinOp::Rem),
            (mir::BinOp::AddWithOverflow, ir::BinOp::AddWithOverflow),
            (mir::BinOp::SubWithOverflow, ir::BinOp::SubWithOverflow),
            (mir::BinOp::MulWithOverflow, ir::BinOp::MulWithOverflow),
            (mir::BinOp::Cmp, ir::BinOp::Cmp),
        ] {
            assert_eq!(bin_op(mir_op).unwrap(), expected);
        }
        for refused_bin in [
            mir::BinOp::AddUnchecked,
            mir::BinOp::SubUnchecked,
            mir::BinOp::MulUnchecked,
            mir::BinOp::ShlUnchecked,
            mir::BinOp::ShrUnchecked,
            mir::BinOp::Offset,
        ] {
            let err = bin_op(refused_bin).unwrap_err();
            assert!(err.contains("unsupported binary operator"), "{err}");
        }
    }

    #[test]
    fn call_source_use_fails_closed_while_other_call_sources_pass_guard() {
        let err = check_call_source(mir::CallSource::Use).unwrap_err();
        assert!(err.contains("CallSource::Use"), "{err}");
        assert!(err.contains("optimize_use_clone"), "{err}");

        for other in [
            mir::CallSource::Normal,
            mir::CallSource::OverloadedOperator,
            mir::CallSource::MatchCmp,
            mir::CallSource::Misc,
        ] {
            assert!(check_call_source(other).is_ok(), "{other:?}");
        }
    }

    #[test]
    fn rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance() {
        use rustc_abi::{AddressSpace, Align, TargetDataLayout};
        use rustc_middle::mir::interpret::{AllocId, CtfeProvenance, Pointer, Scalar};
        use std::num::NonZero;

        let le_dl = TargetDataLayout::parse_from_llvm_datalayout_string(
            "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
            AddressSpace::ZERO,
        )
        .ok()
        .expect("valid little-endian data layout");
        let be_dl = TargetDataLayout::parse_from_llvm_datalayout_string(
            "E-m:e-p:64:64-i64:64-i128:128-n32:64-S128",
            AddressSpace::ZERO,
        )
        .ok()
        .expect("valid big-endian data layout");

        // 1. Valid immutable `.rodata` scalar at non-zero offset (little-endian).
        let bytes = [
            0xaa, 0xbb, 0x01, 0x00, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        ];
        let ro_alloc: Allocation<CtfeProvenance> =
            Allocation::from_bytes(bytes.as_slice(), Align::EIGHT, Mutability::Not, ());
        assert_eq!(
            read_rodata_scalar_from_alloc(&le_dl, &ro_alloc, Size::from_bytes(3), 64).unwrap(),
            0x0807_0605_0403_0200
        );
        assert_eq!(
            read_rodata_scalar_from_alloc(&le_dl, &ro_alloc, Size::from_bytes(2), 8).unwrap(),
            1
        );

        // 2. Reject big-endian layouts, mutable allocations, and out-of-bounds ranges.
        let be_err =
            read_rodata_scalar_from_alloc(&be_dl, &ro_alloc, Size::ZERO, 8).unwrap_err();
        assert!(be_err.contains("non-little-endian"), "{be_err}");

        let mut_alloc: Allocation<CtfeProvenance> =
            Allocation::from_bytes(bytes.as_slice(), Align::EIGHT, Mutability::Mut, ());
        let mut_err =
            read_rodata_scalar_from_alloc(&le_dl, &mut_alloc, Size::ZERO, 64).unwrap_err();
        assert!(mut_err.contains("mutable global allocations"), "{mut_err}");

        let oob_err =
            read_rodata_scalar_from_alloc(&le_dl, &ro_alloc, Size::from_bytes(8), 64).unwrap_err();
        assert!(oob_err.contains("exceeds allocation size"), "{oob_err}");

        // 3. Reject uninitialized bytes inside range.
        let mut uninit_alloc: Allocation<CtfeProvenance> = Allocation::from_bytes(
            [1u8, 2, 3, 4, 5, 6, 7, 8].as_slice(),
            Align::EIGHT,
            Mutability::Mut,
            (),
        );
        uninit_alloc.write_uninit(
            &le_dl,
            AllocRange {
                start: Size::from_bytes(2),
                size: Size::from_bytes(1),
            },
        );
        uninit_alloc.mutability = Mutability::Not;
        let uninit_err =
            read_rodata_scalar_from_alloc(&le_dl, &uninit_alloc, Size::ZERO, 64).unwrap_err();
        assert!(uninit_err.contains("unreadable global allocation"), "{uninit_err}");

        // 4. Reject pointer provenance inside the read range.
        let mut prov_alloc: Allocation<CtfeProvenance> =
            Allocation::from_bytes([0u8; 8].as_slice(), Align::EIGHT, Mutability::Mut, ());
        let ptr = Pointer::new(
            CtfeProvenance::from(AllocId(NonZero::new(7).unwrap())),
            Size::from_bytes(16),
        );
        prov_alloc
            .write_scalar(
                &le_dl,
                AllocRange {
                    start: Size::ZERO,
                    size: Size::from_bytes(8),
                },
                Scalar::from_pointer(ptr, &le_dl),
            )
            .unwrap();
        prov_alloc.mutability = Mutability::Not;
        let prov_err =
            read_rodata_scalar_from_alloc(&le_dl, &prov_alloc, Size::ZERO, 64).unwrap_err();
        assert!(prov_err.contains("provenance-bearing"), "{prov_err}");
    }
}
