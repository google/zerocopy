// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Direct translation of the admitted MIR syntax: the Profile v1 scalar
//! fragment plus the Profile v2 borrowed-slice and raw-pointer fragment
//! (single-level references and raw pointers, `Deref`/`Field` place
//! projections, and the closed [`ir::CoreCallOp`] call table). Unsupported
//! variants remain errors; this adapter performs no control-flow or expression
//! simplification.

use std::collections::{BTreeMap, BTreeSet};
use rustc_abi::{
    BackendRepr, Endian, ExternAbi, FieldIdx, HasDataLayout, Integer, Primitive, Scalar, Size,
    TagEncoding, VariantIdx, Variants,
};
use rustc_ast::Mutability;
use rustc_hir::attrs::{InlineAttr, OptimizeAttr};
use rustc_middle::middle::codegen_fn_attrs::{
    CodegenFnAttrFlags, CodegenFnAttrs, SanitizerFnAttrs,
};
use rustc_middle::mir::interpret::{AllocRange, Allocation, GlobalAlloc, Provenance};
use rustc_middle::mir::{self, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt, TypingEnv};
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
///
/// The tag representation alone fixes the layout that
/// `Trusted.MirSemantics.layoutOfTy` assigns the enum: `ZeroSized` is size 0
/// with alignment 1, and `Scalar(w)` is `intLayout w`, whose size and
/// alignment both equal `w`'s byte width. `#[repr(align(N))]` can raise the
/// enum's own `LayoutData` size and alignment above its tag's ("pub align:
/// AbiAlign, pub size: Size,"), which would change pointer stride and access
/// alignment under Profile v2. So the computed `layout.size` and
/// `layout.align.abi` must equal those values exactly; any other layout is
/// refused rather than modeled with the tag's layout.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L2133-L2134
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
            if index.as_usize() == 0
                && layout.size.bytes() == 0
                && layout.align.abi.bytes() == 1
                && variant_count == 1
            {
                Ok(ir::EnumTagRepr::ZeroSized)
            } else {
                Err(format!(
                    "non-zero-sized or over-aligned single-variant enum \
                     representations are unsupported (size {}, align {}): {t:?}",
                    layout.size.bytes(),
                    layout.align.abi.bytes(),
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
                let tag_bytes = integer.size().bytes();
                if layout.size.bytes() != tag_bytes || layout.align.abi.bytes() != tag_bytes {
                    return Err(format!(
                        "enum layout (size {}, align {}) differs from its {tag_bytes}-byte \
                         tag; over-aligned enum representations are unsupported: {t:?}",
                        layout.size.bytes(),
                        layout.align.abi.bytes(),
                    ));
                }
                Ok(ir::EnumTagRepr::Scalar(IntTy { width, signed }))
            }
            other => Err(format!("non-integer enum tag primitive {other:?}: {t:?}")),
        },
        other => Err(format!("unsupported enum variant layout {other:?}: {t:?}")),
    }
}

/// Cross-check `rustc`'s monomorphized layout for an addressable Profile v2
/// `core::option::Option<T>` (where both `elem.is_sized_no_ref()` and
/// `elem.is_option_payload_supported_v2()` hold) against the exact size,
/// alignment, tag encoding, tag offset, payload offset, and variant
/// discriminants assumed by `Trusted.MirSemantics.{Layout,Bytes}`.
fn verify_addressable_option_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: ty::Ty<'tcx>,
    adt: ty::AdtDef<'tcx>,
    elem: &ir::Ty,
) -> Result<()> {
    let opt_ty = ir::Ty::Option {
        elem: Box::new(elem.clone()),
    };
    let Some((expected_size, expected_align_log2)) = opt_ty.v2_layout() else {
        return Err(format!("addressable Option lacks a Profile v2 layout: {t:?}"));
    };
    let expected_align = 1u64
        .checked_shl(expected_align_log2)
        .ok_or_else(|| format!("Option alignment shift overflow for {t:?}"))?;
    let layout = tcx
        .layout_of(TypingEnv::fully_monomorphized().as_query_input(t))
        .map_err(|err| format!("failed to compute Option layout for {t:?}: {err}"))?;
    if layout.size.bytes() != expected_size as u64 || layout.align.abi.bytes() != expected_align {
        return Err(format!(
            "Option layout (size {}, align {}) disagrees with modeled Profile v2 layout \
             (size {expected_size}, align {expected_align}): {t:?}",
            layout.size.bytes(),
            layout.align.abi.bytes(),
        ));
    }
    let discrs: Vec<(usize, u128)> = adt
        .discriminants(tcx)
        .map(|(v, d)| (v.as_usize(), d.val))
        .collect();
    if discrs != [(0, 0), (1, 1)] {
        return Err(format!(
            "Option discriminants {discrs:?} disagree with modeled (None=0, Some=1): {t:?}"
        ));
    }
    let Variants::Multiple {
        tag,
        tag_encoding,
        tag_field,
        variants,
        ..
    } = &layout.variants
    else {
        return Err(format!(
            "Option layout is not Variants::Multiple ({:?}): {t:?}",
            layout.variants
        ));
    };
    if tag_field.as_usize() != 0 || layout.fields.offset(0).bytes() != 0 {
        return Err(format!(
            "Option tag is not at field 0 offset 0 (tag_field={}, offset={}): {t:?}",
            tag_field.as_usize(),
            layout.fields.offset(0).bytes(),
        ));
    }
    let dl = tcx.data_layout();
    let tag_bytes = tag.size(dl).bytes();
    let some_variant = variants
        .get(VariantIdx::from_usize(1))
        .ok_or_else(|| format!("Option layout missing Some variant 1: {t:?}"))?;
    match elem {
        ir::Ty::Bool => {
            let TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            } = tag_encoding
            else {
                return Err(format!(
                    "Option<bool> layout is not niche-encoded ({tag_encoding:?}): {t:?}"
                ));
            };
            if untagged_variant.as_usize() != 1
                || niche_variants.start.as_usize() != 0
                || niche_variants.last.as_usize() != 0
                || *niche_start != 2
                || tag_bytes != 1
                || some_variant
                    .field_offsets
                    .get(FieldIdx::from_usize(0))
                    .copied()
                    .map(Size::bytes)
                    != Some(0)
            {
                return Err(format!(
                    "Option<bool> niche layout disagrees with modeled (None=2, Some=0/1): {t:?}"
                ));
            }
        }
        ir::Ty::Unit => {
            if !matches!(tag_encoding, TagEncoding::Direct) || tag_bytes != 1 {
                return Err(format!(
                    "Option<()> layout disagrees with modeled 1-byte direct tag: {t:?}"
                ));
            }
        }
        ir::Ty::Int(_) => {
            let (inner_size, _) = elem
                .v2_layout()
                .ok_or_else(|| format!("Option payload lacks Profile v2 layout: {t:?}"))?;
            if !matches!(tag_encoding, TagEncoding::Direct)
                || tag_bytes != expected_align
                || some_variant
                    .field_offsets
                    .get(FieldIdx::from_usize(0))
                    .copied()
                    .map(Size::bytes)
                    != Some(expected_align)
                || layout.size.bytes() != expected_align + inner_size as u64
            {
                return Err(format!(
                    "Option<int> direct layout disagrees with modeled \
                     (tag_size={expected_align}, payload_offset={expected_align}): {t:?}"
                ));
            }
        }
        other => {
            return Err(format!(
                "unexpected addressable Option payload {other:?} in {t:?}"
            ));
        }
    }
    Ok(())
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
        ty::Str => Ok(ir::Ty::Str),
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
                let mut fields = Vec::with_capacity(elements.len());
                for elem in elements {
                    let ft = ty(tcx, elem)?;
                    if !ft.is_sized() {
                        return Err(format!("unsized tuple element in {t:?} is unsupported"));
                    }
                    fields.push(ft);
                }
                Ok(ir::Ty::Tuple { fields })
            }
        }
        ty::Tuple(elements) => {
            let mut fields = Vec::with_capacity(elements.len());
            for elem in elements {
                let ft = ty(tcx, elem)?;
                if !ft.is_sized() {
                    return Err(format!("unsized tuple element in {t:?} is unsupported"));
                }
                fields.push(ft);
            }
            Ok(ir::Ty::Tuple { fields })
        }
        ty::Ref(_region, pointee, mutability) => {
            let mutability = match mutability {
                rustc_ast::Mutability::Not => ir::Mutability::Shared,
                rustc_ast::Mutability::Mut => ir::Mutability::Mut,
            };
            Ok(ir::Ty::Ref {
                mutability,
                pointee: Box::new(ty(tcx, pointee)?),
            })
        }
        ty::RawPtr(pointee, mutability) => {
            let mutability = match mutability {
                rustc_ast::Mutability::Not => ir::Mutability::Shared,
                rustc_ast::Mutability::Mut => ir::Mutability::Mut,
            };
            Ok(ir::Ty::RawPtr {
                mutability,
                pointee: Box::new(ty(tcx, pointee)?),
            })
        }
        ty::Slice(elem) => {
            let elem_ty = ty(tcx, elem)?;
            if !elem_ty.is_sized() {
                return Err(format!("unsized slice element in {t:?} is unsupported"));
            }
            Ok(ir::Ty::Slice {
                elem: Box::new(elem_ty),
            })
        }
        ty::Array(elem, len) => {
            let elem_ty = ty(tcx, elem)?;
            if !elem_ty.is_sized() {
                return Err(format!("unsized array element in {t:?} is unsupported"));
            }
            let len_u64 = len
                .try_to_target_usize(tcx)
                .ok_or_else(|| format!("unevaluated or non-usize array length in {t:?}"))?;
            let len_usize = usize::try_from(len_u64)
                .map_err(|_| format!("array length {len_u64} overflows usize in {t:?}"))?;
            Ok(ir::Ty::Array {
                elem: Box::new(elem_ty),
                len: len_usize,
            })
        }
        ty::Uint(_) | ty::Int(_) => Ok(ir::Ty::Int(int_ty(t)?)),
        // `core::cmp::Ordering` ("a lang item only so that `BinOp::Cmp` in MIR
        // can return it") maps to `Trusted.MirAst.MirTy.ordering` before the
        // crate-local fieldless enum arm (`capture.rs` refuses crate-local
        // language items except under `--stdlib-crate`, where
        // `check_local_ordering` validates a local `Ordering`'s shape; any
        // new language-item-keyed arm needs a matching check in
        // `check_stdlib_capability`).
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/cmp.rs#L400-L415
        // `Box<T, A>` is the `owned_box` lang item, a pointer plus an allocator
        // (`library/alloc/src/boxed.rs:227-237`, `rust-lang/rust`
        // `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
        //
        // > #[lang = "owned_box"]
        // > ...
        // > pub struct Box<
        // >     T: ?Sized,
        // >     #[unstable(...)] A: Allocator = Global,
        // > >(Unique<T>, A);
        //
        // (with the `#[unstable]` attribute's arguments elided here).
        // Only `A = Global` is modeled (`Trusted.MirSemantics.AllocContracts`).
        // The lang item alone does not pin the type: under `--stdlib-crate` a
        // crate-local `#[lang = "owned_box"]` item is possible, so the path
        // must also be the sysroot `alloc::boxed::Box`.
        ty::Adt(adt, args)
            if tcx.is_lang_item(adt.did(), rustc_hir::LangItem::OwnedBox)
                && core_or_alloc_def_path(tcx, adt.did()).as_deref() == Some("alloc::boxed::Box")
                && matches!(args.len(), 1 | 2)
                && args.get(1).is_none_or(|a| {
                    a.as_type().is_some_and(|alloc_ty| is_global_allocator(tcx, alloc_ty))
                }) =>
        {
            let Some(pointee_ty) = args[0].as_type() else {
                return Err(format!("unsupported Box type argument: {t:?}"));
            };
            Ok(ir::Ty::Box {
                pointee: Box::new(ty(tcx, pointee_ty)?),
            })
        }
        // `alloc::vec::Vec<T, A>` (`library/alloc/src/vec/mod.rs:438-441`, at
        // `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
        //
        // > pub struct Vec<T, #[unstable(...)] A: Allocator = Global> {
        // >     buf: RawVec<T, A>,
        // >     len: usize,
        // > }
        //
        // (with the `#[unstable]` attribute's arguments elided here).
        // Only `A = Global` and sized `T` are modeled. The field order is not a
        // layout guarantee ("The order of these fields is completely
        // unspecified", `:312-314`), which is why raw pointers to a `Vec` are
        // not admitted (`ir::Ty::is_supported_v2_local`).
        ty::Adt(adt, args)
            if core_or_alloc_def_path(tcx, adt.did()).as_deref() == Some("alloc::vec::Vec")
                && matches!(args.len(), 1 | 2)
                && args.get(1).is_none_or(|a| {
                    a.as_type().is_some_and(|alloc_ty| is_global_allocator(tcx, alloc_ty))
                }) =>
        {
            let Some(elem_ty) = args[0].as_type() else {
                return Err(format!("unsupported Vec element type: {t:?}"));
            };
            let elem = ty(tcx, elem_ty)?;
            if !elem.is_sized() {
                return Err(format!("unsized Vec element in {t:?} is unsupported"));
            }
            Ok(ir::Ty::Vec {
                elem: Box::new(elem),
            })
        }
        ty::Adt(adt, args)
            if args.is_empty()
                && tcx.is_lang_item(adt.did(), rustc_hir::LangItem::OrderingEnum) =>
        {
            Ok(ir::Ty::Ordering)
        }
        // `core::ops::range::RangeTo<Idx>` (`#[lang = "RangeTo"]`, one field
        // `pub end: Idx`), `RangeFrom<Idx>` (`#[lang = "RangeFrom"]`, one
        // field `pub start: Idx`), and `Range<Idx>` (`#[lang = "Range"]`, two
        // fields `pub start: Idx, pub end: Idx`) map to
        // `MirTy.{rangeTo,rangeFrom,range}` only for `Idx = usize`. They are
        // identified by lang item within the authenticated sysroot `core`
        // crate ([`core_range`]), never by printed path, so a look-alike local
        // struct or enum cannot acquire these range types.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ops/range.rs#L77-L89
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ops/range.rs#L192-L201
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ops/range.rs#L276-L285
        ty::Adt(adt, args) if args.len() == 1 && adt.is_struct() && core_range(tcx, adt.did()).is_some() => {
            let range = core_range(tcx, adt.did()).expect("checked above");
            let Some(arg_ty) = args[0].as_type() else {
                return Err(format!("unsupported core ADT argument: {t:?}"));
            };
            let elem = ty(tcx, arg_ty)?;
            if elem
                != ir::Ty::Int(IntTy {
                    width: IntWidth::Isize,
                    signed: false,
                })
            {
                return Err(format!("unsupported range index type in {t:?}"));
            }
            match range {
                CoreRange::To => Ok(ir::Ty::RangeTo {
                    elem: Box::new(elem),
                }),
                CoreRange::From => Ok(ir::Ty::RangeFrom {
                    elem: Box::new(elem),
                }),
                CoreRange::Range => Ok(ir::Ty::Range {
                    elem: Box::new(elem),
                }),
            }
        }
        // `core::option::Option<T>` (`#[lang = "Option"]`, variants `None` = 0
        // and `Some(T)` = 1) maps to `MirTy.option` when `T` is sized, pinned
        // to the authenticated sysroot `core` crate ([`is_core_option`]).
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/option.rs#L594-L606
        ty::Adt(adt, args)
            if args.len() == 1 && adt.is_enum() && is_core_option(tcx, adt.did()) =>
        {
            let Some(arg_ty) = args[0].as_type() else {
                return Err(format!("unsupported core ADT argument: {t:?}"));
            };
            let elem = ty(tcx, arg_ty)?;
            if !elem.is_sized() {
                return Err(format!("unsized Option payload in {t:?} is unsupported"));
            }
            if elem.is_sized_no_ref() && elem.is_option_payload_supported_v2() {
                verify_addressable_option_layout(tcx, t, adt, &elem)?;
            }
            Ok(ir::Ty::Option {
                elem: Box::new(elem),
            })
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

/// `Place` has a local plus projections. This adapter preserves the compiler
/// local index without renumbering and translates `Deref` and `Field`
/// projections 1:1, refusing every other `ProjectionElem`. Which projection
/// sequences are admitted where (at most one leading `Deref`, `Field` only
/// on tuples, overflow pairs, and ranges) is checked by `ir::Body::try_new`.
/// `Field(FieldIdx, T)` records "A field (e.g., `f` in `_1.f`)" with its
/// type `T`, which `ir::Body::try_new` checks against the projected type.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1182-L1201
fn place<'tcx>(tcx: TyCtxt<'tcx>, place: &mir::Place<'tcx>) -> Result<ir::Place> {
    let mut projection = Vec::with_capacity(place.projection.len());
    for elem in place.projection.iter() {
        match elem {
            mir::ProjectionElem::Deref => projection.push(ir::PlaceElem::Deref),
            mir::ProjectionElem::Field(idx, field_ty) => projection.push(ir::PlaceElem::Field {
                index: idx.as_usize(),
                ty: ty(tcx, field_ty)?,
            }),
            mir::ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                let offset_usize = usize::try_from(offset).map_err(|_| {
                    format!("ConstantIndex offset {offset} overflows usize in `{place:?}`")
                })?;
                let min_len_usize = usize::try_from(min_length).map_err(|_| {
                    format!(
                        "ConstantIndex min_length {min_length} overflows usize in `{place:?}`"
                    )
                })?;
                projection.push(ir::PlaceElem::ConstantIndex {
                    offset: offset_usize,
                    min_length: min_len_usize,
                    from_end,
                });
            }
            mir::ProjectionElem::Downcast(_, variant) => {
                projection.push(ir::PlaceElem::Downcast {
                    variant_idx: variant.as_usize(),
                });
            }
            other => {
                return Err(format!(
                    "unsupported place projection `{other:?}` in `{place:?}`"
                ));
            }
        }
    }
    Ok(ir::Place {
        local: place.local.as_u32(),
        projection,
    })
}

fn local(place: &mir::Place<'_>) -> Result<u32> {
    if !place.projection.is_empty() {
        return Err(format!("place projections are unsupported: {place:?}"));
    }
    Ok(place.local.as_u32())
}

// RUSTC-WORKAROUND(#4369): `Const::eval` ICEs on non-value `Const::Ty`.
/// Evaluate an operand or `required_consts` constant under `typing_env`.
///
/// Upstream `Const::eval` resolves `Const::Unevaluated` via
/// `const_eval_resolve`, lowers `ConstKind::Value(cv)` via
/// `valtree_to_const_val`, triggers `bug!("Normalization of
/// \`ty::ConstKind::Expr\` is unimplemented")` on `ConstKind::Expr`, and calls
/// `delayed_bug("Unevaluated \`ty::Const\` in MIR body")` on any other
/// `Const::Ty`; guard `Const::Ty` before calling `eval`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/consts.rs#L268-L341
fn eval_mir_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    constant: mir::Const<'tcx>,
    span: rustc_span::Span,
) -> Result<mir::ConstValue> {
    if constant.has_non_region_param()
        || constant.has_non_region_infer()
        || constant.references_error()
    {
        return Err(format!("uninstantiated or erroneous constant: {constant:?}"));
    }
    match constant {
        mir::Const::Val(value, _) => Ok(value),
        mir::Const::Unevaluated(..) => constant
            .eval(tcx, typing_env, span)
            .map_err(|err| format!("unevaluated constant failed CTFE: {err:?}")),
        mir::Const::Ty(_, ct) if matches!(ct.kind(), ty::ConstKind::Value(_)) => constant
            .eval(tcx, typing_env, span)
            .map_err(|err| format!("type-level constant failed evaluation: {err:?}")),
        mir::Const::Ty(..) => Err(format!(
            "unsupported non-value type-level constant: {constant:?}"
        )),
    }
}

/// Evaluate every `required_consts` entry on a body under `typing_env` so
/// dead-branch or generic post-monomorphization constant errors fail closed.
///
/// Upstream `Body::required_consts` documents: "We hold in this field all the
/// constants we are not able to evaluate yet. `None` indicates that the list
/// has not been computed yet. This is soundness-critical, we make a guarantee
/// that all consts syntactically mentioned in a function have successfully
/// evaluated if the function ever gets executed at runtime."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L266-L271
fn eval_required_consts<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
) -> Result<()> {
    let Some(required_consts) = body.required_consts.as_deref() else {
        return Err("required constants are unavailable in the scalar model".into());
    };
    for const_op in required_consts {
        eval_mir_const(tcx, typing_env, const_op.const_, const_op.span)?;
    }
    Ok(())
}

/// Decode a concrete scalar `ConstValue` (`Scalar::Int` or `Indirect` static
/// constant allocation without pointer provenance) to raw bits.
///
/// Upstream `Scalar` is "Information about one scalar component of a Rust
/// type", and `Allocation::read_scalar` with `read_provenance = false` states
/// "If we can just ignore provenance or there is none, that's easy" (checking
/// `Prov::OFFSET_IS_ADDR || self.provenance.range_empty(range, cx)`), so we
/// independently assert `alloc.provenance().range_empty(range, &tcx)` before
/// reading raw bits.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L1539-L1544
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/allocation.rs#L712-L737
fn decode_scalar_bits<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    value: mir::ConstValue,
    raw_ty: ty::Ty<'tcx>,
    width: u32,
) -> Result<u128> {
    if let Some(scalar) = value.try_to_scalar_int() {
        if scalar.size().bits() != u64::from(width) {
            return Err("scalar constant width disagrees with its type".into());
        }
        return Ok(scalar.to_bits_unchecked());
    }
    let mir::ConstValue::Indirect { alloc_id, offset } = value else {
        return Err("only integer and indirect scalar constants are modeled".into());
    };
    let layout = tcx
        .layout_of(typing_env.as_query_input(raw_ty))
        .map_err(|err| format!("failed to compute layout for indirect constant {raw_ty:?}: {err}"))?;
    if layout.is_unsized() || layout.size.bits() != u64::from(width) {
        return Err("indirect scalar constant size disagrees with its type".into());
    }
    if !matches!(
        layout.backend_repr,
        BackendRepr::Scalar(Scalar::Initialized { .. })
    ) {
        return Err(format!(
            "indirect constant lacks initialized scalar representation: {:?}",
            layout.backend_repr
        ));
    }
    match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(const_alloc) => {
            read_rodata_scalar_from_alloc(&tcx, const_alloc.inner(), offset, width)
        }
        GlobalAlloc::Static(_) => {
            Err("static global allocations are unsupported in constants".into())
        }
        GlobalAlloc::Function { .. } => {
            Err("function global allocations are unsupported in constants".into())
        }
        GlobalAlloc::VTable(..) => {
            Err("vtable global allocations are unsupported in constants".into())
        }
        GlobalAlloc::TypeId { .. } => {
            Err("type-id global allocations are unsupported in constants".into())
        }
    }
}

/// Copy and move are distinct constructors. The source says a move "may
/// additionally overwrite the place with `uninit` bytes"; the model owns that
/// operational choice rather than having the adapter erase the distinction.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1303-L1330
fn operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    op: &mir::Operand<'tcx>,
) -> Result<ir::Operand> {
    match op {
        mir::Operand::Copy(p) => {
            let p = place(tcx, p)?;
            if p.projection.is_empty() {
                Ok(ir::Operand::Copy { local: p.local })
            } else {
                Ok(ir::Operand::CopyPlace { place: p })
            }
        }
        mir::Operand::Move(p) => {
            let p = place(tcx, p)?;
            if p.projection.is_empty() {
                Ok(ir::Operand::Move { local: p.local })
            } else {
                Ok(ir::Operand::MovePlace { place: p })
            }
        }
        mir::Operand::Constant(constant) => {
            let raw_ty = constant.const_.ty();
            let t = ty(tcx, raw_ty)?;
            let const_val = eval_mir_const(tcx, typing_env, constant.const_, constant.span)?;
            let width = match &t {
                ir::Ty::Bool | ir::Ty::Ordering => 8,
                ir::Ty::Char => 32,
                ir::Ty::Unit => {
                    // `ZeroSized` is documented as "Only for ZSTs." The
                    // source type must independently be the empty tuple;
                    // other zero-sized types do not acquire unit semantics.
                    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/consts.rs#L38-L39
                    if matches!(const_val, mir::ConstValue::ZeroSized) {
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
                ir::Ty::Array { .. } => {
                    let lit = decode_rodata_array_lit(tcx, typing_env, const_val, raw_ty, &t)?;
                    ir::validate_constant(&t, &lit)?;
                    return Ok(ir::Operand::Constant { ty: t, lit });
                }
                ir::Ty::Ref { mutability, .. } | ir::Ty::RawPtr { mutability, .. } => {
                    if *mutability != ir::Mutability::Shared {
                        return Err(format!(
                            "mutable constant references/pointers of type {t:?} are unsupported"
                        ));
                    }
                    let lit = decode_rodata_ref_lit(tcx, const_val, &t)?;
                    ir::validate_constant(&t, &lit)?;
                    return Ok(ir::Operand::Constant { ty: t, lit });
                }
                ir::Ty::OverflowPair(_)
                | ir::Ty::Tuple { .. }
                | ir::Ty::Slice { .. }
                | ir::Ty::Str
                | ir::Ty::Vec { .. }
                | ir::Ty::Box { .. }
                | ir::Ty::RangeTo { .. }
                | ir::Ty::RangeFrom { .. }
                | ir::Ty::Range { .. }
                | ir::Ty::Option { .. } => {
                    return Err(format!("constants of compound/pointer type {t:?} are unsupported"));
                }
                ir::Ty::Int(ity) => ity.width.bits(),
                ir::Ty::Enum(ety) => match ety.tag_repr() {
                    ir::EnumTagRepr::ZeroSized => {
                        if matches!(const_val, mir::ConstValue::ZeroSized) {
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
            let bits = decode_scalar_bits(tcx, typing_env, const_val, raw_ty, width)?;
            let lit = ConstLit::Scalar { bits };
            ir::validate_constant(&t, &lit)?;
            Ok(ir::Operand::Constant { ty: t, lit })
        }
        other => Err(format!("unsupported operand: {other:?}")),
    }
}

/// Extract a slice of [`ir::RodataByte`] out of an immutable, provenance-free
/// `GlobalAlloc::Memory` allocation (`Mutability::Not`), preserving initialized
/// vs. uninitialized bytes via `InitMask`.
fn read_rodata_bytes_from_alloc<Prov: Provenance>(
    cx: &impl HasDataLayout,
    alloc: &Allocation<Prov>,
    offset: Size,
    len: usize,
) -> Result<(Vec<ir::RodataByte>, u32)> {
    if cx.data_layout().endian != Endian::Little {
        return Err("non-little-endian global allocation constants are unsupported".into());
    }
    if alloc.mutability != Mutability::Not {
        return Err("mutable global allocations are unsupported in constants".into());
    }
    let start = usize::try_from(offset.bytes())
        .map_err(|_| "rodata constant offset overflows usize")?;
    let end = start
        .checked_add(len)
        .ok_or("rodata constant range overflows usize")?;
    if end > alloc.len() {
        return Err(format!(
            "rodata constant range [{start}..{end}) exceeds allocation size {}",
            alloc.len()
        ));
    }
    let range = AllocRange {
        start: offset,
        size: Size::from_bytes(len),
    };
    if !alloc.provenance().range_empty(range, cx) {
        return Err("provenance-bearing global allocation constants are unsupported".into());
    }
    let raw = alloc.inspect_with_uninit_and_ptr_outside_interpreter(start..end);
    let init_mask = alloc.init_mask();
    let mut bytes = Vec::with_capacity(len);
    for (idx, &b) in raw.iter().enumerate() {
        let pos = Size::from_bytes(start + idx);
        if init_mask.get(pos) {
            bytes.push(ir::RodataByte::Init { byte: b });
        } else {
            bytes.push(ir::RodataByte::Uninit);
        }
    }
    let align_log2 = alloc.align.bytes().trailing_zeros();
    Ok((bytes, align_log2))
}

fn decode_rodata_array_lit<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    value: mir::ConstValue,
    raw_ty: ty::Ty<'tcx>,
    ty_ir: &ir::Ty,
) -> Result<ConstLit> {
    let Some((expected_size, _)) = ty_ir.v2_layout() else {
        return Err(format!("array constant type {ty_ir:?} lacks layout"));
    };
    let layout = tcx
        .layout_of(typing_env.as_query_input(raw_ty))
        .map_err(|err| format!("failed to compute layout for array constant {raw_ty:?}: {err}"))?;
    if layout.is_unsized() || layout.size.bytes() as usize != expected_size {
        return Err("array constant size disagrees with its layout".into());
    }
    match value {
        mir::ConstValue::ZeroSized if expected_size == 0 => Ok(ConstLit::RodataBytes {
            bytes: Vec::new(),
        }),
        mir::ConstValue::Scalar(mir::interpret::Scalar::Int(si)) => {
            if tcx.data_layout().endian != Endian::Little {
                return Err("non-little-endian array constants are unsupported".into());
            }
            if si.size().bytes() as usize != expected_size {
                return Err("scalar array constant width disagrees with its type".into());
            }
            let le = si.to_bits_unchecked().to_le_bytes();
            let bytes = le[..expected_size]
                .iter()
                .map(|&byte| ir::RodataByte::Init { byte })
                .collect();
            Ok(ConstLit::RodataBytes { bytes })
        }
        mir::ConstValue::Indirect { alloc_id, offset } => {
            let GlobalAlloc::Memory(const_alloc) = tcx.global_alloc(alloc_id) else {
                return Err("non-memory global allocations are unsupported in array constants".into());
            };
            let (bytes, _) =
                read_rodata_bytes_from_alloc(&tcx, const_alloc.inner(), offset, expected_size)?;
            Ok(ConstLit::RodataBytes { bytes })
        }
        other => Err(format!("unsupported array constant representation: {other:?}")),
    }
}

fn decode_rodata_ref_lit<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: mir::ConstValue,
    ty_ir: &ir::Ty,
) -> Result<ConstLit> {
    match value {
        mir::ConstValue::Slice { alloc_id, meta } => {
            let slice_len = usize::try_from(meta)
                .map_err(|_| format!("rodata slice length {meta} overflows usize"))?;
            let GlobalAlloc::Memory(const_alloc) = tcx.global_alloc(alloc_id) else {
                return Err("non-memory global allocations are unsupported in slice constants".into());
            };
            let inner = const_alloc.inner();
            let (bytes, align_log2) = read_rodata_bytes_from_alloc(&tcx, inner, Size::ZERO, inner.len())?;
            // `ConstValue::Slice::alloc_id` in
            // `compiler/rustc_middle/src/mir/consts.rs` (`rust-lang/rust`
            // `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
            // > "The allocation storing the slice contents.
            // > This always points to the beginning of the allocation."
            Ok(ConstLit::RodataRef {
                bytes,
                align_log2,
                offset_bytes: 0,
                slice_len: Some(slice_len),
            })
        }
        mir::ConstValue::Scalar(mir::interpret::Scalar::Ptr(ptr, _)) => {
            let (prov, offset) = ptr.prov_and_relative_offset();
            let alloc_id = prov.alloc_id();
            let offset_bytes = usize::try_from(offset.bytes())
                .map_err(|_| "rodata pointer offset overflows usize")?;
            let GlobalAlloc::Memory(const_alloc) = tcx.global_alloc(alloc_id) else {
                return Err("non-memory global allocations are unsupported in ref constants".into());
            };
            let inner = const_alloc.inner();
            let (bytes, align_log2) = read_rodata_bytes_from_alloc(&tcx, inner, Size::ZERO, inner.len())?;
            Ok(ConstLit::RodataRef {
                bytes,
                align_log2,
                offset_bytes,
                slice_len: None,
            })
        }
        mir::ConstValue::Scalar(mir::interpret::Scalar::Int(si)) => {
            if si.size().bytes() != 8 {
                return Err(format!(
                    "unexpected scalar width {} for rodata ref constant {ty_ir:?}",
                    si.size().bytes()
                ));
            }
            let (pt_size, pt_align) = match ty_ir {
                ir::Ty::Ref { pointee, .. } | ir::Ty::RawPtr { pointee, .. } => match &**pointee {
                    ir::Ty::Slice { elem } => elem.v2_layout().map(|(_, a)| (0, a)),
                    ir::Ty::Str => Some((0, 0)),
                    pt => pt.v2_layout(),
                },
                _ => None,
            }
            .ok_or_else(|| format!("rodata ref type {ty_ir:?} lacks layout"))?;
            let addr = si.to_bits_unchecked();
            let align_bytes = 1u128.checked_shl(pt_align).unwrap_or(u128::MAX);
            if pt_size == 0 && addr != 0 && addr % align_bytes == 0 {
                let slice_len = match ty_ir {
                    ir::Ty::Ref { pointee, .. } | ir::Ty::RawPtr { pointee, .. }
                        if matches!(&**pointee, ir::Ty::Slice { .. } | ir::Ty::Str) =>
                    {
                        Some(0)
                    }
                    _ => None,
                };
                Ok(ConstLit::RodataRef {
                    bytes: Vec::new(),
                    align_log2: pt_align,
                    offset_bytes: 0,
                    slice_len,
                })
            } else {
                Err(format!(
                    "non-ZST or invalid dangling integer pointer in constant {ty_ir:?}"
                ))
            }
        }
        other => Err(format!("unsupported constant reference representation: {other:?}")),
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

/// Extract MIR unary operators (`Not`, `Neg`, and `PtrMetadata`, which "Gets
/// the metadata `M` from a `*const`/`*mut`/`&`/`&mut`"; Profile v2 executes it
/// on single-level references and raw pointers).
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617
fn un_op(op: mir::UnOp) -> Result<ir::UnOp> {
    Ok(match op {
        mir::UnOp::Not => ir::UnOp::Not,
        mir::UnOp::Neg => ir::UnOp::Neg,
        mir::UnOp::PtrMetadata => ir::UnOp::PtrMetadata,
    })
}

/// Extract MIR cast kinds: `IntToInt`, `PtrToPtr` (raw-to-raw pointer casts;
/// `ir::Body::try_new` refuses reference sources),
/// `PointerWithExposedProvenance` ("An address-to-pointer cast that picks up
/// an exposed provenance", rendered as `ir::CastKind::IntToPtr`), and
/// `PointerCoercion::Unsize` (rendered as `ir::CastKind::Unsize`;
/// `ir::Body::try_new` admits only array-to-slice pointer/reference unsizing).
/// Pointer-expose, float, transmute, and subtype casts stay refused
/// exhaustively.
///
/// Every other `PointerCoercion` is refused outright rather than normalized.
/// Upstream says `ArrayToPointer` and `MutToConstPointer` "are allowed in
/// [`AnalysisPhase::Initial`] as they're needed for borrowck, but after that
/// are forbidden (including in all phases of runtime MIR)", because
/// `CleanupPostBorrowck` rewrites both: "just make them ordinary pointer casts
/// instead" (`*cast_kind = CastKind::PtrToPtr;`). Neither can therefore reach
/// `Runtime(PostCleanup)`, and the remaining coercions (`ReifyFnPointer`,
/// `UnsafeFnPointer`, and `ClosureFnPointer`) are unmodeled. Upstream also
/// notes that "reference-to-raw-ptr casts are translated into
/// `&raw mut/const *r`, i.e., they are not actually casts."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs#L44-L60
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/adjustment.rs#L10-L40
fn cast_kind(kind: mir::CastKind) -> Result<ir::CastKind> {
    match kind {
        mir::CastKind::IntToInt => Ok(ir::CastKind::IntToInt),
        mir::CastKind::PtrToPtr => Ok(ir::CastKind::PtrToPtr),
        mir::CastKind::PointerWithExposedProvenance => Ok(ir::CastKind::IntToPtr),
        mir::CastKind::PointerCoercion(
            rustc_middle::ty::adjustment::PointerCoercion::Unsize,
            _,
        ) => Ok(ir::CastKind::Unsize),
        mir::CastKind::PointerExposeProvenance
        | mir::CastKind::PointerCoercion(..)
        | mir::CastKind::FloatToInt
        | mir::CastKind::FloatToFloat
        | mir::CastKind::IntToFloat
        | mir::CastKind::FnPtrToPtr
        | mir::CastKind::Transmute
        | mir::CastKind::Subtype => Err(format!("unsupported cast kind: {kind:?}")),
    }
}

/// Preserve the ordinary MIR operators. In particular, ordinary shifts use
/// "RHS.rem_euclid(LHS::BITS)"; the unchecked shift variants have a different
/// UB contract and remain rejected, while `AddUnchecked`/`SubUnchecked`/
/// `MulUnchecked` match Lean's `BinOp` UB guards directly. The model interprets
/// these operators, including signed comparisons, division/remainder UB,
/// three-way comparison (`Cmp`), unchecked arithmetic, and wrapping or
/// `(T, bool)` overflowing arithmetic, rather than the adapter.
/// `Offset` ("The `ptr.offset` operator") "has the same semantics as
/// [`offset`](pointer::offset), except that the second parameter may be a
/// `usize` as well"; `ir::Body::try_new` admits only a sized raw-pointer
/// left operand with an `isize` right operand and matching destination.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1708
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1410-L1411
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
        mir::BinOp::AddUnchecked => ir::BinOp::AddUnchecked,
        mir::BinOp::SubUnchecked => ir::BinOp::SubUnchecked,
        mir::BinOp::MulUnchecked => ir::BinOp::MulUnchecked,
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
        mir::BinOp::Offset => ir::BinOp::Offset,
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
fn rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    local_decls: &mir::LocalDecls<'tcx>,
    value: &mir::Rvalue<'tcx>,
) -> Result<ir::Rvalue> {
    Ok(match value {
        mir::Rvalue::Use(op, with_retag) => {
            let op_ty = ty(tcx, op.ty(local_decls, tcx))?;
            let operand_ir = operand(tcx, typing_env, op)?;
            if with_retag.yes() && !op_ty.is_retag_noop() {
                ir::Rvalue::UseRetag {
                    operand: operand_ir,
                }
            } else {
                ir::Rvalue::Use {
                    operand: operand_ir,
                    with_retag: with_retag.yes(),
                }
            }
        }
        mir::Rvalue::BinaryOp(op, values) => ir::Rvalue::Binary {
            op: bin_op(*op)?,
            left: operand(tcx, typing_env, &values.0)?,
            right: operand(tcx, typing_env, &values.1)?,
        },
        mir::Rvalue::UnaryOp(op, value) => ir::Rvalue::Unary {
            op: un_op(*op)?,
            operand: operand(tcx, typing_env, value)?,
        },
        mir::Rvalue::Cast(mir::CastKind::Transmute, value, target_ty) => {
            if let Some(opnd) = try_peel_box_raw_ptr_transmute(
                tcx,
                typing_env,
                local_decls,
                value,
                *target_ty,
            )? {
                ir::Rvalue::Cast {
                    cast_kind: ir::CastKind::BoxAsRawPtr,
                    operand: opnd,
                    ty: ty(tcx, *target_ty)?,
                }
            } else {
                ir::Rvalue::Cast {
                    cast_kind: cast_kind(mir::CastKind::Transmute)?,
                    operand: operand(tcx, typing_env, value)?,
                    ty: ty(tcx, *target_ty)?,
                }
            }
        }
        mir::Rvalue::Cast(kind, value, target_ty) => ir::Rvalue::Cast {
            cast_kind: cast_kind(*kind)?,
            operand: operand(tcx, typing_env, value)?,
            ty: ty(tcx, *target_ty)?,
        },
        mir::Rvalue::Discriminant(p) => ir::Rvalue::Discriminant {
            place: place(tcx, p)?,
        },
        // `Ref` "Creates a reference of the indicated kind to the place";
        // its semantics "are essentially entirely a part of the aliasing
        // model." Profile v2 has no aliasing model, so `ir::Body::try_new`
        // admits only unprojected or `(*ref)` reborrow places, and
        // `ir::validate_local_tys_with_exemptions` refuses every body that
        // mixes reference and non-fake raw-pointer locals. `BorrowKind::Shared`
        // ("Data must be immutable and is aliasable") and `Mut` ("Data is
        // mutable and not aliasable") map to `ir::Mutability`; `Fake` borrows,
        // which `CleanupPostBorrowck` turns into `Nop`s, stay refused.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1372-L1379
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L149-L176
        mir::Rvalue::Ref(_region, borrow_kind, p) => {
            let mutability = match borrow_kind {
                mir::BorrowKind::Shared => ir::Mutability::Shared,
                mir::BorrowKind::Mut { .. } => ir::Mutability::Mut,
                mir::BorrowKind::Fake(_) => {
                    return Err(format!("unsupported fake borrow: {borrow_kind:?}"));
                }
            };
            ir::Rvalue::Ref {
                mutability,
                place: place(tcx, p)?,
            }
        }
        // `RawPtr` "Creates a raw pointer with the indicated mutability to the
        // place" and "is generated by pointer casts like `&v as *const _` or
        // raw borrow expressions like `&raw const v`." `RawPtrKind::Const` and
        // `RawPtrKind::Mut` map to `ir::Mutability`. `FakeForPtrMetadata`
        // ("Creates a raw pointer to a place that will only be used to access
        // its metadata, not the data behind the pointer. Note that this
        // limitation is *not* enforced by the validator."; "In terms of the
        // operational semantics (i.e., Miri), this is equivalent to
        // `RawPtrKind::Mut`, but will never incur a retag.") lowers to
        // `ir::Rvalue::FakeAddressOf`, and `ir::Body::try_new` enforces the
        // single-purpose `PtrMetadata` discipline (`isFakePtrMetadataLocalV2`).
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1394-L1401
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L180-L192
        mir::Rvalue::RawPtr(raw_kind, p) => match raw_kind {
            mir::RawPtrKind::Const => ir::Rvalue::AddressOf {
                mutability: ir::Mutability::Shared,
                place: place(tcx, p)?,
            },
            mir::RawPtrKind::Mut => ir::Rvalue::AddressOf {
                mutability: ir::Mutability::Mut,
                place: place(tcx, p)?,
            },
            mir::RawPtrKind::FakeForPtrMetadata => ir::Rvalue::FakeAddressOf {
                place: place(tcx, p)?,
            },
        },
        mir::Rvalue::Repeat(op, count) => {
            let op_ir = operand(tcx, typing_env, op)?;
            let elem_ty = ty(tcx, op.ty(local_decls, tcx))?;
            let count_u64 = count
                .try_to_target_usize(tcx)
                .ok_or_else(|| format!("unevaluated repeat count in {value:?}"))?;
            let count_usize = usize::try_from(count_u64)
                .map_err(|_| format!("repeat count {count_u64} overflows usize in {value:?}"))?;
            ir::Rvalue::Repeat {
                operand: op_ir,
                elem_ty,
                count: count_usize,
            }
        }
        // `Aggregate` "Creates an aggregate value, like a tuple or struct."
        // Arrays lower to `ir::Rvalue::AggregateArray`, and non-empty tuples
        // lower to `ir::Rvalue::AggregateTuple`; the empty tuple stays refused
        // because unit values are `ZeroSized` constants. For
        // `AggregateKind::Adt(def, variant, ..)`, "The second field is the
        // variant index. It's equal to 0 for struct and union expressions."
        // Only the sysroot `core::ops::range::{RangeTo, RangeFrom}` lang-item
        // structs are admitted (see [`core_range`]), requiring
        // `VariantIdx::ZERO` and exactly one operand (their single
        // `end`/`start` field); the active-field slot is for unions and must
        // be `None`.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1445-L1453
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1546-L1556
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ops/range.rs#L192-L201
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ops/range.rs#L276-L285
        mir::Rvalue::Aggregate(agg_kind, ops) => match &**agg_kind {
            mir::AggregateKind::Array(elem_ty) => {
                let elem_ir = ty(tcx, *elem_ty)?;
                let mut elems = Vec::with_capacity(ops.len());
                for op in ops.iter() {
                    elems.push(operand(tcx, typing_env, op)?);
                }
                ir::Rvalue::AggregateArray {
                    elem_ty: elem_ir,
                    elems,
                }
            }
            mir::AggregateKind::Tuple if !ops.is_empty() => {
                let mut fields = Vec::with_capacity(ops.len());
                for op in ops.iter() {
                    fields.push(operand(tcx, typing_env, op)?);
                }
                ir::Rvalue::AggregateTuple { fields }
            }
            mir::AggregateKind::Adt(adt_did, variant, substs, _, None) if substs.len() == 1 => {
                let Some(arg_ty) = substs[0].as_type() else {
                    return Err(format!("unsupported ADT aggregate: {value:?}"));
                };
                let elem_ty = ty(tcx, arg_ty)?;
                if let Some(range) = core_range(tcx, *adt_did) {
                    if *variant != rustc_abi::VariantIdx::ZERO {
                        return Err(format!("unsupported ADT aggregate: {value:?}"));
                    }
                    match (range, ops.len()) {
                        (CoreRange::To, 1) => {
                            let op =
                                operand(tcx, typing_env, &ops[rustc_abi::FieldIdx::from_u32(0)])?;
                            ir::Rvalue::AggregateRangeTo { elem_ty, end: op }
                        }
                        (CoreRange::From, 1) => {
                            let op =
                                operand(tcx, typing_env, &ops[rustc_abi::FieldIdx::from_u32(0)])?;
                            ir::Rvalue::AggregateRangeFrom { elem_ty, start: op }
                        }
                        (CoreRange::Range, 2) => {
                            let start =
                                operand(tcx, typing_env, &ops[rustc_abi::FieldIdx::from_u32(0)])?;
                            let end =
                                operand(tcx, typing_env, &ops[rustc_abi::FieldIdx::from_u32(1)])?;
                            ir::Rvalue::AggregateRange {
                                elem_ty,
                                start,
                                end,
                            }
                        }
                        _ => return Err(format!("unsupported ADT aggregate: {value:?}")),
                    }
                } else if is_core_option(tcx, *adt_did) {
                    match (variant.as_usize(), ops.len()) {
                        (0, 0) => ir::Rvalue::AggregateOption {
                            variant_idx: 0,
                            inner_ty: elem_ty,
                            payload: None,
                        },
                        (1, 1) => {
                            let op =
                                operand(tcx, typing_env, &ops[rustc_abi::FieldIdx::from_u32(0)])?;
                            ir::Rvalue::AggregateOption {
                                variant_idx: 1,
                                inner_ty: elem_ty,
                                payload: Some(Box::new(op)),
                            }
                        }
                        _ => return Err(format!("unsupported ADT aggregate: {value:?}")),
                    }
                } else {
                    return Err(format!("unsupported non-core ADT aggregate: {value:?}"));
                }
            }
            _ => return Err(format!("unsupported rvalue aggregate: {value:?}")),
        },
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
fn statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    local_decls: &mir::LocalDecls<'tcx>,
    stmt: &mir::StatementKind<'tcx>,
) -> Result<ir::Statement> {
    Ok(match stmt {
        mir::StatementKind::Assign(value) => {
            let p = place(tcx, &value.0)?;
            let rv = rvalue(tcx, typing_env, local_decls, &value.1)?;
            if p.projection.is_empty() {
                ir::Statement::Assign {
                    local: p.local,
                    value: rv,
                }
            } else {
                ir::Statement::AssignPlace { place: p, value: rv }
            }
        }
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

// RUSTC-WORKAROUND(#4364): codegen rewrites `Use` calls after capture.
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

/// The crate that defines the `Sized` lang item, when that crate is the
/// sysroot `core`.
///
/// `Sized` is a `core` lang item (`LangItem::Sized`, `sym::sized`, a
/// `Target::Trait`) that every crate linking `core` resolves. The crate
/// defining it must be external (`!is_local()`) and named `core`:
/// `capture.rs` refuses crate-local lang items before extraction (`"Defined
/// lang items can come from the current crate or its dependencies"`), and
/// `verify_sysroot_only_crates` admits only external crates whose artifacts
/// match the authenticated target sysroot by `(st_dev, st_ino)`, with no
/// `--extern` flags or search paths. The returned crate is therefore the
/// authenticated sysroot `core`, and a `#![no_core]` crate (which must define
/// `Sized` itself) yields `None`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L155
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L20-L29
fn sysroot_core_crate(tcx: TyCtxt<'_>) -> Option<rustc_span::def_id::CrateNum> {
    let sized = tcx.lang_items().get(rustc_hir::LangItem::Sized)?;
    if sized.is_local() || tcx.crate_name(sized.krate) != rustc_span::sym::core {
        return None;
    }
    Some(sized.krate)
}

/// The semantic path of `def` if, and only if, `def` belongs to the
/// authenticated sysroot `core` crate.
///
/// Capture identifies the closed [`ir::CoreCallOp`] table by printed path,
/// so the path is trusted only after `def` is pinned to sysroot `core`.
/// Matching on `tcx.crate_name(def.krate) == "core"` alone is unsound: a
/// target crate compiled with `--crate-name=core` is itself named `core`,
/// and `def_path_str` prints crate-local paths without a crate prefix (see
/// [`item_identity`]), so a local `mod core { mod ops { .. } }` would print
/// as `core::ops::..`. This function therefore requires:
///
/// - `!def.is_local()`: `is_local` "Returns whether the item is defined in
///   the crate currently being compiled", which is exactly the spoofing case;
/// - `def.krate == sysroot_core_crate(tcx)`: the crate defining the `Sized`
///   lang item, which [`sysroot_core_crate`] pins to an external,
///   sysroot-authenticated crate named `core`.
///
/// The printed path uses the same trimming- and reexport-free printer as
/// [`item_identity`], so a public reexport cannot stand in for the defining
/// path.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/def_id.rs#L291-L295
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2191-L2210
fn core_def_path(tcx: TyCtxt<'_>, def: DefId) -> Option<String> {
    if def.is_local() || Some(def.krate) != sysroot_core_crate(tcx) {
        return None;
    }
    Some(rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(tcx.def_path_str(def))
    ))
}

/// The semantic path of `def` if, and only if, `def` belongs to the sysroot
/// `alloc` crate or, via [`core_def_path`], to the authenticated sysroot
/// `core` crate.
///
/// Modeled library items (`Vec`, `Box`, `Global`, and the `Vec`/`Box`
/// methods in `core_call_op`) are matched by these paths. A local item is
/// never accepted, even when the local crate is itself named `core` or
/// `alloc`, because `def_path_str` prints crate-local paths without a crate
/// prefix (see [`core_def_path`]). `verify_sysroot_only_crates` admits only
/// external crates whose artifacts match the authenticated target sysroot,
/// so the external crate named `alloc` is the sysroot `alloc`.
fn core_or_alloc_def_path(tcx: TyCtxt<'_>, def: DefId) -> Option<String> {
    if def.is_local() {
        return None;
    }
    if tcx.crate_name(def.krate).as_str() != "alloc" {
        return core_def_path(tcx, def);
    }
    Some(rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(tcx.def_path_str(def))
    ))
}

fn is_global_allocator(tcx: TyCtxt<'_>, alloc_ty: ty::Ty<'_>) -> bool {
    match *alloc_ty.kind() {
        ty::Adt(adt, args) if args.is_empty() => {
            core_or_alloc_def_path(tcx, adt.did()).as_deref() == Some("alloc::alloc::Global")
        }
        _ => false,
    }
}

// RUSTC-WORKAROUND(#4367): match the private `Box`/`Unique`/`NonNull` fields
// that the rustc 1.98 `ElaborateBoxDerefs` transmute reaches through.
fn is_unique_ptr_ty(tcx: TyCtxt<'_>, t: ty::Ty<'_>) -> bool {
    match *t.kind() {
        ty::Adt(adt, _) => matches!(
            core_or_alloc_def_path(tcx, adt.did()).as_deref(),
            Some("core::ptr::Unique" | "core::ptr::unique::Unique")
        ),
        _ => false,
    }
}

fn is_nonnull_ptr_ty(tcx: TyCtxt<'_>, t: ty::Ty<'_>) -> bool {
    match *t.kind() {
        ty::Adt(adt, _) => matches!(
            core_or_alloc_def_path(tcx, adt.did()).as_deref(),
            Some("core::ptr::NonNull" | "core::ptr::non_null::NonNull")
        ),
        _ => false,
    }
}

/// Recognize the pointer temporary that `rustc`'s `ElaborateBoxDerefs` pass
/// introduces for each `*b` dereference of a `Box<P>` and lower it to
/// `CastKind::BoxAsRawPtr` of the box itself. The pass builds a `*const P`
/// temporary from a transmute of the box's `Unique<P>`/`NonNull<P>` pointer
/// field (`compiler/rustc_mir_transform/src/elaborate_box_derefs.rs`, lines
/// 23, 29-34, and 68-83, `rust-lang/rust`
/// `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
///
/// > let ptr_ty = Ty::new_imm_ptr(tcx, pointee);
///
/// > [PlaceElem::Field(FieldIdx::ZERO, unique_ty),
/// > PlaceElem::Field(FieldIdx::ZERO, nonnull_ty)]
///
/// (one line upstream)
///
/// > Rvalue::Cast(
/// >     CastKind::Transmute,
/// >     Operand::Copy(
/// >         Place::from(place.local)
/// >             .project_deeper(&build_projection(unique_ty, nonnull_ty),
/// > tcx),
/// >     ),
/// >     ptr_ty,
/// > ),
///
/// (the `project_deeper` line is wrapped here), so this matches exactly a
/// transmute of `<place>.0.0` (with `Unique` and
/// `NonNull` field types) of a `Box<P, Global>` place to a raw pointer to `P`.
/// `promote_box_as_ref` turns admitted uses into `CastKind::BoxAsRef`, and
/// `ir::check_cast_types` refuses the rest. Any other transmute is left to the
/// caller, which refuses it.
// RUSTC-WORKAROUND(#4367): peel rustc 1.98's `ElaborateBoxDerefs` transmute
// of `<box>.0.0`; rustc 1.99 lowers `*b` with `BoxDerefTransmute` instead.
fn try_peel_box_raw_ptr_transmute<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    local_decls: &mir::LocalDecls<'tcx>,
    value: &mir::Operand<'tcx>,
    target_ty: ty::Ty<'tcx>,
) -> Result<Option<ir::Operand>> {
    let ty::RawPtr(target_pointee, _) = *target_ty.kind() else {
        return Ok(None);
    };
    let (is_move, src_place) = match value {
        mir::Operand::Copy(p) => (false, p),
        mir::Operand::Move(p) => (true, p),
        mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => return Ok(None),
    };
    let proj = src_place.projection;
    if proj.len() < 2 {
        return Ok(None);
    }
    let prefix = &proj[..proj.len() - 2];
    let mir::ProjectionElem::Field(f0, uniq_ty) = proj[proj.len() - 2] else {
        return Ok(None);
    };
    let mir::ProjectionElem::Field(f1, nn_ty) = proj[proj.len() - 1] else {
        return Ok(None);
    };
    if f0.as_usize() != 0
        || f1.as_usize() != 0
        || !is_unique_ptr_ty(tcx, uniq_ty)
        || !is_nonnull_ptr_ty(tcx, nn_ty)
    {
        return Ok(None);
    }
    let mut place_ty = mir::PlaceTy::from_ty(local_decls[src_place.local].ty);
    for elem in prefix {
        place_ty = place_ty.projection_ty(tcx, *elem);
    }
    let ty::Adt(adt, args) = *place_ty.ty.kind() else {
        return Ok(None);
    };
    if !tcx.is_lang_item(adt.did(), rustc_hir::LangItem::OwnedBox)
        || core_or_alloc_def_path(tcx, adt.did()).as_deref() != Some("alloc::boxed::Box")
        || !matches!(args.len(), 1 | 2)
        || !args.get(1).is_none_or(|a| {
            a.as_type().is_some_and(|alloc_ty| is_global_allocator(tcx, alloc_ty))
        })
    {
        return Ok(None);
    }
    if args[0].as_type() != Some(target_pointee) {
        return Ok(None);
    }
    let _ = typing_env;
    let mut peeled_proj = Vec::with_capacity(prefix.len());
    for elem in prefix {
        match *elem {
            mir::ProjectionElem::Deref => peeled_proj.push(ir::PlaceElem::Deref),
            mir::ProjectionElem::Field(idx, field_ty) => peeled_proj.push(ir::PlaceElem::Field {
                index: idx.as_usize(),
                ty: ty(tcx, field_ty)?,
            }),
            other => {
                return Err(format!(
                    "unsupported Box projection `{other:?}` in `{src_place:?}`"
                ));
            }
        }
    }
    let peeled_ir = ir::Place {
        local: src_place.local.as_u32(),
        projection: peeled_proj,
    };
    Ok(Some(match (is_move, peeled_ir.projection.is_empty()) {
        (false, true) => ir::Operand::Copy {
            local: peeled_ir.local,
        },
        (false, false) => ir::Operand::CopyPlace { place: peeled_ir },
        (true, true) => ir::Operand::Move {
            local: peeled_ir.local,
        },
        (true, false) => ir::Operand::MovePlace { place: peeled_ir },
    }))
}

/// Promote non-argument locals `_raw : *const P` (never `_0`, arguments, or
/// `*mut P`) whose only assignments are `try_peel_box_raw_ptr_transmute`
/// (`CastKind::BoxAsRawPtr` with matching pointee `P`) and whose only uses are
/// shared `Deref` projection reads, `UnOp::PtrMetadata`, or storage/mention
/// markers (`StorageLive`, `StorageDead`, `PlaceMention`) to `&P`
/// (`MirTy::Ref { Mutability::Shared, .. }`) via `CastKind::BoxAsRef`.
///
/// Locals escaped to calls, returned, stored in aggregates, cast/offset,
/// copied/retagged by value, or `&mut`/`&raw`-borrowed remain `.rawPtr` with
/// `CastKind::BoxAsRawPtr`. Such a body mixes the `Box` (which counts as a
/// reference, `ir::Ty::has_ref_v2`) with a raw-pointer local, so capture
/// refuses it.
///
/// The promoted temporary is the one `ElaborateBoxDerefs` substitutes for the
/// box in a `*b` place (`elaborate_box_derefs.rs:83`, `rust-lang/rust`
/// `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`: `place.local = ptr_local;`),
/// so it denotes the same shared access to the boxed value as `&*b` in the
/// source program. `Trusted.MirSemantics.evalCastKindV2` checks the reference
/// validity of the boxed value when it evaluates the `BoxAsRef` cast.
// RUSTC-WORKAROUND(#4367): recover `&*b` from the raw-pointer temporary that
// rustc 1.98's `ElaborateBoxDerefs` introduces.
fn promote_box_as_ref(
    arg_count: usize,
    local_tys: &mut [ir::Ty],
    blocks: &mut [(Vec<ir::Statement>, RawTerminator)],
) {
    fn operand_mentions_local(op: &ir::Operand, lid: u32) -> bool {
        match op {
            ir::Operand::Copy { local } | ir::Operand::Move { local } => *local == lid,
            ir::Operand::CopyPlace { place } | ir::Operand::MovePlace { place } => {
                place.local == lid
            }
            ir::Operand::Constant { .. } => false,
        }
    }

    fn operand_only_shared_deref_reads(op: &ir::Operand, lid: u32) -> bool {
        match op {
            ir::Operand::Copy { local } | ir::Operand::Move { local } => *local != lid,
            ir::Operand::CopyPlace { place } => {
                place.local != lid || matches!(place.projection.as_slice(), [ir::PlaceElem::Deref])
            }
            ir::Operand::MovePlace { place } => place.local != lid,
            ir::Operand::Constant { .. } => true,
        }
    }

    fn rvalue_uses_safe_for_ref_promo(rv: &ir::Rvalue, lid: u32) -> bool {
        match rv {
            ir::Rvalue::Unary {
                op: ir::UnOp::PtrMetadata,
                operand,
            } => {
                matches!(
                    operand,
                    ir::Operand::Copy { local } | ir::Operand::Move { local } if *local == lid
                ) || operand_only_shared_deref_reads(operand, lid)
            }
            ir::Rvalue::Ref { mutability, place } => {
                place.local != lid
                    || (*mutability == ir::Mutability::Shared
                        && matches!(place.projection.as_slice(), [ir::PlaceElem::Deref]))
            }
            ir::Rvalue::AddressOf { place, .. } | ir::Rvalue::FakeAddressOf { place } => {
                place.local != lid
            }
            ir::Rvalue::Discriminant { place } => place.local != lid,
            ir::Rvalue::Use { operand, .. }
            | ir::Rvalue::UseRetag { operand }
            | ir::Rvalue::Unary { operand, .. }
            | ir::Rvalue::Cast { operand, .. }
            | ir::Rvalue::AggregateRangeTo { end: operand, .. }
            | ir::Rvalue::AggregateRangeFrom { start: operand, .. } => {
                operand_only_shared_deref_reads(operand, lid)
            }
            ir::Rvalue::Binary { left, right, .. } => {
                operand_only_shared_deref_reads(left, lid)
                    && operand_only_shared_deref_reads(right, lid)
            }
            ir::Rvalue::AggregateTuple { fields }
            | ir::Rvalue::AggregateArray { elems: fields, .. } => {
                fields.iter().all(|f| operand_only_shared_deref_reads(f, lid))
            }
            ir::Rvalue::Repeat { operand, .. } => operand_only_shared_deref_reads(operand, lid),
            ir::Rvalue::AggregateRange { start, end, .. } => {
                operand_only_shared_deref_reads(start, lid)
                    && operand_only_shared_deref_reads(end, lid)
            }
            ir::Rvalue::AggregateOption { payload, .. } => {
                payload.as_deref().is_none_or(|p| operand_only_shared_deref_reads(p, lid))
            }
        }
    }

    if arg_count >= local_tys.len() {
        return;
    }
    for (lid_usize, local_ty) in local_tys.iter_mut().enumerate().skip(arg_count + 1) {
        let raw_ty = local_ty.clone();
        let ir::Ty::RawPtr {
            mutability: ir::Mutability::Shared,
            pointee,
        } = local_ty
        else {
            continue;
        };
        let lid = lid_usize as u32;
        let mut saw_box_cast = false;
        let mut eligible = true;

        'scan: for (statements, terminator) in blocks.iter() {
            for stmt in statements {
                match stmt {
                    ir::Statement::Assign { local, value } if *local == lid => match value {
                        ir::Rvalue::Cast {
                            cast_kind: ir::CastKind::BoxAsRawPtr,
                            operand,
                            ty,
                        } if *ty == raw_ty && !operand_mentions_local(operand, lid) => {
                            saw_box_cast = true;
                        }
                        _ => {
                            eligible = false;
                            break 'scan;
                        }
                    },
                    ir::Statement::Assign { value, .. } => {
                        if !rvalue_uses_safe_for_ref_promo(value, lid) {
                            eligible = false;
                            break 'scan;
                        }
                    }
                    ir::Statement::AssignPlace { place, value } => {
                        if place.local == lid || !rvalue_uses_safe_for_ref_promo(value, lid) {
                            eligible = false;
                            break 'scan;
                        }
                    }
                    ir::Statement::StorageLive { .. }
                    | ir::Statement::StorageDead { .. }
                    | ir::Statement::PlaceMention { .. }
                    | ir::Statement::Nop => {}
                }
            }
            let term_ok = match terminator {
                RawTerminator::LocalCall { args, dst, .. } => {
                    *dst != lid && args.iter().all(|a| operand_only_shared_deref_reads(a, lid))
                }
                RawTerminator::Resolved(terminator) => match terminator {
                    ir::Terminator::SwitchInt { operand, .. } => {
                        operand_only_shared_deref_reads(operand, lid)
                    }
                    ir::Terminator::Assert { cond, .. } => {
                        operand_only_shared_deref_reads(cond, lid)
                    }
                    ir::Terminator::CoreCall { args, dst, .. } => {
                        dst.local != lid
                            && args.iter().all(|a| operand_only_shared_deref_reads(a, lid))
                    }
                    ir::Terminator::Call { args, dst, .. }
                    | ir::Terminator::SysrootCall { args, dst, .. } => {
                        *dst != lid && args.iter().all(|a| operand_only_shared_deref_reads(a, lid))
                    }
                    ir::Terminator::Goto { .. }
                    | ir::Terminator::Ret
                    | ir::Terminator::Unreachable
                    | ir::Terminator::Unsupported => true,
                },
            };
            if !term_ok {
                eligible = false;
                break 'scan;
            }
        }

        if saw_box_cast && eligible {
            let ref_ty = ir::Ty::Ref {
                mutability: ir::Mutability::Shared,
                pointee: pointee.clone(),
            };
            *local_ty = ref_ty.clone();
            for (statements, _) in blocks.iter_mut() {
                for stmt in statements {
                    if let ir::Statement::Assign { local, value } = stmt
                        && *local == lid
                        && let ir::Rvalue::Cast { cast_kind, ty, .. } = value
                    {
                        *cast_kind = ir::CastKind::BoxAsRef;
                        *ty = ref_ty.clone();
                    }
                }
            }
        }
    }
}

/// The admitted `core::ops::range` structs.
#[derive(Clone, Copy)]
enum CoreRange {
    To,
    From,
    Range,
}

/// Classify `def` as sysroot `core::ops::range::{RangeTo, RangeFrom, Range}`
/// by lang item (`LangItem::{RangeTo, RangeFrom, Range}`, each a
/// `Target::Struct`), after pinning `def` to the authenticated sysroot `core`
/// as in [`core_def_path`]. The newer `core::range::{RangeFrom, Range}`
/// (`RangeFromCopy`, `RangeCopy`) are distinct lang items and stay refused.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L406-L421
fn core_range(tcx: TyCtxt<'_>, def: DefId) -> Option<CoreRange> {
    if def.is_local() || Some(def.krate) != sysroot_core_crate(tcx) {
        return None;
    }
    if tcx.is_lang_item(def, rustc_hir::LangItem::RangeTo) {
        Some(CoreRange::To)
    } else if tcx.is_lang_item(def, rustc_hir::LangItem::RangeFrom) {
        Some(CoreRange::From)
    } else if tcx.is_lang_item(def, rustc_hir::LangItem::Range) {
        Some(CoreRange::Range)
    } else {
        None
    }
}

/// Return `true` when `def` is sysroot `core::option::Option`
/// (`LangItem::Option`, `Target::Enum`), pinned to the authenticated sysroot
/// `core` crate as in [`core_def_path`].
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L390-L392
fn is_core_option(tcx: TyCtxt<'_>, def: DefId) -> bool {
    !def.is_local()
        && Some(def.krate) == sysroot_core_crate(tcx)
        && tcx.is_lang_item(def, rustc_hir::LangItem::Option)
}

fn parse_core_num_impl_method(path: &str) -> Option<(IntTy, &str)> {
    let rest = path.strip_prefix("core::num::<impl ")?;
    let (ty_name, method) = rest.split_once(">::")?;
    let ity = match ty_name {
        "u8" => IntTy {
            width: IntWidth::I8,
            signed: false,
        },
        "u16" => IntTy {
            width: IntWidth::I16,
            signed: false,
        },
        "u32" => IntTy {
            width: IntWidth::I32,
            signed: false,
        },
        "u64" => IntTy {
            width: IntWidth::I64,
            signed: false,
        },
        "u128" => IntTy {
            width: IntWidth::I128,
            signed: false,
        },
        "usize" => IntTy {
            width: IntWidth::Isize,
            signed: false,
        },
        "i8" => IntTy {
            width: IntWidth::I8,
            signed: true,
        },
        "i16" => IntTy {
            width: IntWidth::I16,
            signed: true,
        },
        "i32" => IntTy {
            width: IntWidth::I32,
            signed: true,
        },
        "i64" => IntTy {
            width: IntWidth::I64,
            signed: true,
        },
        "i128" => IntTy {
            width: IntWidth::I128,
            signed: true,
        },
        "isize" => IntTy {
            width: IntWidth::Isize,
            signed: true,
        },
        _ => return None,
    };
    Some((ity, method))
}

/// Map a returning call to a sysroot `core` or `alloc` function onto the
/// closed [`ir::CoreCallOp`] table, refusing every other callee.
///
/// The callee is identified by [`core_or_alloc_def_path`] (pinned to the
/// sysroot `alloc` or the authenticated sysroot `core`), after resolving a
/// `core`/`alloc` trait method to its impl, and the generic arguments select
/// the operand types. Each entry corresponds to one pinned `library/core`
/// definition; `ir::Body::try_new` checks argument and destination types,
/// and `Trusted.MirSemantics` states the operational semantics:
///
/// - `<[T]>::{len, is_empty, split_at, split_at_mut}` and
///   `core::ops::index::{Index::index, IndexMut::index_mut}` on `[T]` for
///   `Range<usize>` and `RangeFrom<usize>`;
/// - `<[T]>::get_unchecked::<I>`
///   (`get_unchecked<I>(&self, index: I) -> &I::Output`), admitted for
///   `I = Range<usize>`, `RangeTo<usize>`, `RangeFrom<usize>` (over integer
///   slices `[Int]`), or `usize` (over sized ref-free elements,
///   `SliceIndex<[T]>` in `library/core/src/slice/index.rs`);
///   `get_unchecked_mut` is not captured;
/// - `<*const T>::add` and `<*mut T>::add`: `pub const unsafe fn add(self,
///   count: usize) -> Self where T: Sized`;
/// - `core::num` inherent integer methods `unchecked_sub` (`usize` only),
///   `is_multiple_of` / `next_multiple_of` / `div_ceil` / `next_power_of_two`
///   (unsigned), `checked_{add, mul, sub, shl}`, `saturating_add`,
///   `wrapping_{shl, shr}`, `leading_zeros`, `count_ones`, `trailing_zeros`,
///   `overflowing_{add, sub, mul}`, `to_le_bytes`, and `from_le_bytes`;
/// - `core::cmp::{min, max}` on integers, `core::mem::replace`,
///   `core::mem::size_of` (types with a modeled Profile v2 layout),
///   `core::option::Option::<T>::{is_some, is_none, take, unwrap}`, and
///   structural `<[T; N] as core::cmp::PartialEq>::eq`.
///
/// It also maps the `Vec<T, Global>` and `Box<T, Global>` methods matched
/// below, whose contracts are stated in `Trusted.MirSemantics.AllocContracts`.
///
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/slice/mod.rs#L101-L138
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/slice/mod.rs#L639-L660
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/slice/mod.rs#L1953-L1992
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/slice/index.rs#L237-L616
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ops/index.rs#L73-L179
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ptr/const_ptr.rs#L811-L832
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/ptr/mut_ptr.rs#L909-L930
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/num/uint_macros.rs#L84-L4085
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/num/int_macros.rs#L76-L3887
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/cmp.rs#L1034-L1078
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/mem/mod.rs#L373-L932
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/option.rs#L632-L1903
fn core_call_op<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    fn_args: ty::GenericArgsRef<'tcx>,
) -> Result<ir::CoreCallOp> {
    // `Index`/`IndexMut` on slices and `PartialEq` on arrays are classified
    // below by their trait method and generic arguments. Resolving them would
    // yield `core` impl paths that the closed table does not list.
    let trait_level = matches!(
        core_or_alloc_def_path(tcx, def_id).as_deref(),
        Some(
            "core::ops::index::Index::index"
                | "core::ops::index::IndexMut::index_mut"
                | "core::cmp::PartialEq::eq"
        )
    ) && fn_args
        .first()
        .and_then(|a| a.as_type())
        .is_some_and(|t| matches!(t.kind(), ty::Slice(_) | ty::Array(..)));
    let (def_id, fn_args) = if !trait_level
        && tcx.trait_of_assoc(def_id).is_some()
        && core_or_alloc_def_path(tcx, def_id).is_some()
    {
        if let Ok(Some(inst)) = ty::Instance::try_resolve(tcx, typing_env, def_id, fn_args) {
            (inst.def_id(), inst.args)
        } else {
            (def_id, fn_args)
        }
    } else {
        (def_id, fn_args)
    };
    let Some(path) = core_or_alloc_def_path(tcx, def_id) else {
        return Err(format!(
            "external call to non-core/non-alloc def `{}` is unsupported",
            tcx.def_path_str(def_id)
        ));
    };
    let usize_int = IntTy {
        width: IntWidth::Isize,
        signed: false,
    };
    let usize_ty = ir::Ty::Int(usize_int);
    if let Some((ity, method)) = parse_core_num_impl_method(path.as_str()) {
        return match method {
            "is_multiple_of" if !ity.signed => Ok(ir::CoreCallOp::NumIsMultipleOf(ity)),
            "next_multiple_of" if !ity.signed => Ok(ir::CoreCallOp::NumNextMultipleOf(ity)),
            "div_ceil" if !ity.signed => Ok(ir::CoreCallOp::NumDivCeil(ity)),
            "checked_add" => Ok(ir::CoreCallOp::NumCheckedAdd(ity)),
            "checked_mul" => Ok(ir::CoreCallOp::NumCheckedMul(ity)),
            "checked_sub" => Ok(ir::CoreCallOp::NumCheckedSub(ity)),
            "checked_shl" => Ok(ir::CoreCallOp::NumCheckedShl(ity)),
            "saturating_add" => Ok(ir::CoreCallOp::NumSaturatingAdd(ity)),
            "wrapping_shl" => Ok(ir::CoreCallOp::NumWrappingShl(ity)),
            "wrapping_shr" => Ok(ir::CoreCallOp::NumWrappingShr(ity)),
            "leading_zeros" => Ok(ir::CoreCallOp::NumLeadingZeros(ity)),
            "count_ones" => Ok(ir::CoreCallOp::NumCountOnes(ity)),
            "trailing_zeros" => Ok(ir::CoreCallOp::NumTrailingZeros(ity)),
            "next_power_of_two" if !ity.signed => Ok(ir::CoreCallOp::NumNextPowerOfTwo(ity)),
            "overflowing_add" => Ok(ir::CoreCallOp::NumOverflowingAdd(ity)),
            "overflowing_sub" => Ok(ir::CoreCallOp::NumOverflowingSub(ity)),
            "overflowing_mul" => Ok(ir::CoreCallOp::NumOverflowingMul(ity)),
            "unchecked_sub" if ity == usize_int => Ok(ir::CoreCallOp::UsizeUncheckedSub),
            "to_le_bytes" => Ok(ir::CoreCallOp::IntToLeBytes { int_ty: ity }),
            "from_le_bytes" => Ok(ir::CoreCallOp::IntFromLeBytes { int_ty: ity }),
            _ => Err(format!("unsupported core call `{path}`")),
        };
    }
    match path.as_str() {
        "core::slice::<impl [T]>::len" => Ok(ir::CoreCallOp::SliceLen),
        "core::slice::<impl [T]>::get_unchecked" => {
            let idx_ty = fn_args
                .get(1)
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing index type argument in {path}"))?;
            match ty(tcx, idx_ty)? {
                ir::Ty::RangeTo { elem: e } if *e == usize_ty => {
                    Ok(ir::CoreCallOp::SliceGetUncheckedRangeTo)
                }
                ir::Ty::RangeFrom { elem: e } if *e == usize_ty => {
                    Ok(ir::CoreCallOp::SliceGetUncheckedRangeFrom)
                }
                ir::Ty::Range { elem: e } if *e == usize_ty => {
                    Ok(ir::CoreCallOp::SliceGetUncheckedRange)
                }
                ir::Ty::Int(ity) if ity == usize_int => {
                    Ok(ir::CoreCallOp::SliceGetUncheckedIndex)
                }
                other => Err(format!(
                    "unsupported get_unchecked index type {other:?}"
                )),
            }
        }
        "core::slice::<impl [T]>::is_empty" => {
            let elem_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing slice element type in {path}"))?;
            Ok(ir::CoreCallOp::SliceIsEmpty {
                elem: ty(tcx, elem_ty)?,
            })
        }
        "core::slice::<impl [T]>::split_at" => {
            let elem_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing slice element type in {path}"))?;
            Ok(ir::CoreCallOp::SliceSplitAt {
                mutability: ir::Mutability::Shared,
                elem: ty(tcx, elem_ty)?,
            })
        }
        "core::slice::<impl [T]>::split_at_mut" => {
            let elem_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing slice element type in {path}"))?;
            Ok(ir::CoreCallOp::SliceSplitAt {
                mutability: ir::Mutability::Mut,
                elem: ty(tcx, elem_ty)?,
            })
        }
        "core::ops::index::Index::index" | "core::ops::index::IndexMut::index_mut" => {
            let mutability = if path == "core::ops::index::IndexMut::index_mut" {
                ir::Mutability::Mut
            } else {
                ir::Mutability::Shared
            };
            let self_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Self type argument in {path}"))?;
            let idx_ty = fn_args
                .get(1)
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Idx type argument in {path}"))?;
            match (ty(tcx, self_ty)?, ty(tcx, idx_ty)?) {
                (ir::Ty::Slice { elem }, ir::Ty::Range { elem: idx_e }) if *idx_e == usize_ty => {
                    Ok(ir::CoreCallOp::SliceIndexRange {
                        mutability,
                        elem: *elem,
                    })
                }
                (ir::Ty::Slice { elem }, ir::Ty::RangeFrom { elem: idx_e })
                    if *idx_e == usize_ty =>
                {
                    Ok(ir::CoreCallOp::SliceIndexRangeFrom {
                        mutability,
                        elem: *elem,
                    })
                }
                (s_ty, i_ty) => Err(format!(
                    "unsupported {path} receiver/index types ({s_ty:?}, {i_ty:?})"
                )),
            }
        }
        "core::cmp::min" | "core::cmp::max" => {
            let arg_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing type argument in {path}"))?;
            match ty(tcx, arg_ty)? {
                ir::Ty::Int(ity) => Ok(if path == "core::cmp::min" {
                    ir::CoreCallOp::CmpMin(ity)
                } else {
                    ir::CoreCallOp::CmpMax(ity)
                }),
                other => Err(format!("unsupported {path} integer type {other:?}")),
            }
        }
        "core::mem::replace" => {
            let arg_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing type argument in {path}"))?;
            Ok(ir::CoreCallOp::MemReplace {
                ty: ty(tcx, arg_ty)?,
            })
        }
        "core::mem::size_of" => {
            let arg_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing type argument in {path}"))?;
            let ty_ir = ty(tcx, arg_ty)?;
            if !ty_ir.is_sized() || !ty_ir.is_supported_v2_local() {
                return Err(format!("unsupported {path} type {ty_ir:?}"));
            }
            let Some((expected_size, _)) = ty_ir.v2_layout() else {
                return Err(format!(
                    "unsupported {path} type {ty_ir:?} lacks v2 layout"
                ));
            };
            let layout = tcx
                .layout_of(typing_env.as_query_input(arg_ty))
                .map_err(|err| format!("failed to compute layout for {arg_ty:?}: {err}"))?;
            if layout.is_unsized() || layout.size.bytes() as usize != expected_size {
                return Err(format!(
                    "{path} layout (unsized={}, size={}) disagrees with \
                     modeled size {expected_size} for {ty_ir:?}",
                    layout.is_unsized(),
                    layout.size.bytes(),
                ));
            }
            Ok(ir::CoreCallOp::MemSizeOf { ty: ty_ir })
        }
        "core::option::Option::<T>::is_some" => {
            let inner_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Option inner type in {path}"))?;
            Ok(ir::CoreCallOp::OptionIsSome {
                inner: ty(tcx, inner_ty)?,
            })
        }
        "core::option::Option::<T>::is_none" => {
            let inner_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Option inner type in {path}"))?;
            Ok(ir::CoreCallOp::OptionIsNone {
                inner: ty(tcx, inner_ty)?,
            })
        }
        "core::option::Option::<T>::take" => {
            let inner_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Option inner type in {path}"))?;
            Ok(ir::CoreCallOp::OptionTake {
                inner: ty(tcx, inner_ty)?,
            })
        }
        "core::option::Option::<T>::unwrap" => {
            let inner_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Option inner type in {path}"))?;
            Ok(ir::CoreCallOp::OptionUnwrap {
                inner: ty(tcx, inner_ty)?,
            })
        }
        "core::ptr::const_ptr::<impl *const T>::add" => {
            let pt = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing pointee type in {path}"))?;
            Ok(ir::CoreCallOp::PtrAdd {
                mutability: ir::Mutability::Shared,
                pointee: ty(tcx, pt)?,
            })
        }
        "core::ptr::mut_ptr::<impl *mut T>::add" => {
            let pt = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing pointee type in {path}"))?;
            Ok(ir::CoreCallOp::PtrAdd {
                mutability: ir::Mutability::Mut,
                pointee: ty(tcx, pt)?,
            })
        }
        "core::cmp::PartialEq::eq" => {
            if fn_args.len() != 2 {
                return Err(format!(
                    "unexpected type argument count {} in {path}",
                    fn_args.len()
                ));
            }
            let self_raw = fn_args[0]
                .as_type()
                .ok_or_else(|| format!("missing Self type argument in {path}"))?;
            let rhs_raw = fn_args[1]
                .as_type()
                .ok_or_else(|| format!("missing Rhs type argument in {path}"))?;
            let self_ty = ty(tcx, self_raw)?;
            let rhs_ty = ty(tcx, rhs_raw)?;
            match (self_ty, rhs_ty) {
                (
                    ir::Ty::Array { elem: e1, len: n1 },
                    ir::Ty::Array { elem: e2, len: n2 },
                ) if e1 == e2 && n1 == n2 && e1.is_array_eq_elem_supported() => {
                    Ok(ir::CoreCallOp::ArrayEq {
                        elem: *e1,
                        len: n1,
                    })
                }
                (s, r) => Err(format!(
                    "unsupported PartialEq::eq types ({s:?}, {r:?})"
                )),
            }
        }
        "alloc::vec::Vec::<T>::new" => {
            let elem_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Vec element type in {path}"))?;
            Ok(ir::CoreCallOp::VecNew {
                elem: ty(tcx, elem_ty)?,
            })
        }
        "alloc::vec::Vec::<T>::with_capacity" => {
            let elem_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Vec element type in {path}"))?;
            Ok(ir::CoreCallOp::VecWithCapacity {
                elem: ty(tcx, elem_ty)?,
            })
        }
        "alloc::vec::Vec::<T, A>::len" | "alloc::vec::Vec::<T>::len" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::VecLen)
        }
        "alloc::vec::Vec::<T, A>::push" | "alloc::vec::Vec::<T>::push" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::VecPush)
        }
        "alloc::vec::Vec::<T, A>::resize" | "alloc::vec::Vec::<T>::resize" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            check_trivial_clone_arg(tcx, fn_args, &path)?;
            Ok(ir::CoreCallOp::VecResize)
        }
        "alloc::vec::Vec::<T, A>::extend_from_slice"
        | "alloc::vec::Vec::<T>::extend_from_slice" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            check_trivial_clone_arg(tcx, fn_args, &path)?;
            Ok(ir::CoreCallOp::VecExtendFromSlice)
        }
        "alloc::vec::Vec::<T, A>::reserve" | "alloc::vec::Vec::<T>::reserve" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::VecReserve)
        }
        "<alloc::vec::Vec<T, A> as core::ops::index::Index<I>>::index"
        | "<alloc::vec::Vec<T, A> as core::ops::Index<I>>::index" => {
            check_vec_index_usize_arg(fn_args, &path)?;
            check_alloc_global_arg(tcx, fn_args, 2, &path)?;
            Ok(ir::CoreCallOp::VecIndex)
        }
        "<alloc::vec::Vec<T, A> as core::ops::index::IndexMut<I>>::index_mut"
        | "<alloc::vec::Vec<T, A> as core::ops::IndexMut<I>>::index_mut" => {
            check_vec_index_usize_arg(fn_args, &path)?;
            check_alloc_global_arg(tcx, fn_args, 2, &path)?;
            Ok(ir::CoreCallOp::VecIndexMut)
        }
        "<alloc::vec::Vec<T, A> as core::ops::deref::Deref>::deref"
        | "<alloc::vec::Vec<T, A> as core::ops::Deref>::deref" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::VecDeref)
        }
        "<alloc::vec::Vec<T, A> as core::ops::deref::DerefMut>::deref_mut"
        | "<alloc::vec::Vec<T, A> as core::ops::DerefMut>::deref_mut" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::VecDerefMut)
        }
        "<alloc::boxed::Box<[T], A> as core::convert::From<alloc::vec::Vec<T, A>>>::from"
        | concat!(
            "alloc::vec::<impl core::convert::From<alloc::vec::Vec<T, A>> ",
            "for alloc::boxed::Box<[T], A>>::from"
        ) => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::BoxFromVec)
        }
        "<alloc::boxed::Box<T, A> as core::ops::deref::Deref>::deref"
        | "<alloc::boxed::Box<T, A> as core::ops::Deref>::deref" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::BoxDeref)
        }
        "<alloc::boxed::Box<T, A> as core::ops::deref::DerefMut>::deref_mut"
        | "<alloc::boxed::Box<T, A> as core::ops::DerefMut>::deref_mut" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            Ok(ir::CoreCallOp::BoxDerefMut)
        }
        "<alloc::boxed::Box<T, A> as core::clone::Clone>::clone"
        | "<alloc::boxed::Box<[T], A> as core::clone::Clone>::clone" => {
            check_alloc_global_arg(tcx, fn_args, 1, &path)?;
            check_trivial_clone_arg(tcx, fn_args, &path)?;
            Ok(ir::CoreCallOp::BoxClone)
        }
        "alloc::boxed::Box::<T>::new" => {
            let pt_ty = fn_args
                .first()
                .and_then(|a| a.as_type())
                .ok_or_else(|| format!("missing Box pointee type in {path}"))?;
            Ok(ir::CoreCallOp::BoxNew {
                pointee: ty(tcx, pt_ty)?,
            })
        }
        _ => Err(format!("unsupported core/alloc call `{path}`")),
    }
}

/// Translate a non-cleanup `UnwindAction` 1:1 into [`ir::UnwindAction`].
///
/// Upstream: `Continue` is "No action is to be taken. Continue unwinding.",
/// `Unreachable` "Triggers undefined behavior if unwind happens.",
/// `Terminate(UnwindTerminateReason)` "Terminates the execution if unwind
/// happens.", and `Cleanup(BasicBlock)` names "Cleanups to be done."
/// `-Cpanic=abort` bodies carry `Unreachable`, and bodies that cannot unwind
/// through their ABI carry `Terminate(Abi)`. Each is preserved rather than
/// normalized to `Continue`. The `UnwindTerminateReason` (`Abi` or
/// `InCleanup`, "The reason we are terminating the process during
/// unwinding") is dropped because `Trusted.MirAst.UnwindAction.terminate`
/// has no reason field; both reasons terminate execution. `Cleanup` stays
/// refused: cleanup blocks are refused separately and have no Profile v2
/// interpretation.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1027-L1055
fn unwind_action(unwind: mir::UnwindAction, what: &str) -> Result<ir::UnwindAction> {
    match unwind {
        mir::UnwindAction::Continue => Ok(ir::UnwindAction::Continue),
        mir::UnwindAction::Unreachable => Ok(ir::UnwindAction::Unreachable),
        mir::UnwindAction::Terminate(_reason) => Ok(ir::UnwindAction::Terminate),
        mir::UnwindAction::Cleanup(_) => Err(format!("cleanup unwinds on {what} are unsupported")),
    }
}

fn mir_place_mentions_local(place: &mir::Place<'_>, lid: usize) -> bool {
    place.local.as_usize() == lid
        || place.projection.iter().any(|elem| match elem {
            mir::ProjectionElem::Index(v) => v.as_usize() == lid,
            _ => false,
        })
}

fn mir_operand_mentions_local(op: &mir::Operand<'_>, lid: usize) -> bool {
    match op {
        mir::Operand::Copy(p) | mir::Operand::Move(p) => mir_place_mentions_local(p, lid),
        mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => false,
    }
}

fn mir_rvalue_mentions_local(rv: &mir::Rvalue<'_>, lid: usize) -> bool {
    match rv {
        mir::Rvalue::Use(op, _)
        | mir::Rvalue::Repeat(op, _)
        | mir::Rvalue::Cast(_, op, _)
        | mir::Rvalue::UnaryOp(_, op)
        | mir::Rvalue::WrapUnsafeBinder(op, _) => mir_operand_mentions_local(op, lid),
        mir::Rvalue::BinaryOp(_, ops) => {
            mir_operand_mentions_local(&ops.0, lid) || mir_operand_mentions_local(&ops.1, lid)
        }
        mir::Rvalue::Ref(_, _, p)
        | mir::Rvalue::RawPtr(_, p)
        | mir::Rvalue::Discriminant(p)
        | mir::Rvalue::CopyForDeref(p)
        | mir::Rvalue::Reborrow(_, _, p) => mir_place_mentions_local(p, lid),
        mir::Rvalue::Aggregate(_, ops) => ops.iter().any(|op| mir_operand_mentions_local(op, lid)),
        mir::Rvalue::ThreadLocalRef(_) => false,
    }
}

fn mir_terminator_mentions_local(term: &mir::TerminatorKind<'_>, lid: usize) -> bool {
    match term {
        mir::TerminatorKind::Goto { .. }
        | mir::TerminatorKind::Return
        | mir::TerminatorKind::Unreachable
        | mir::TerminatorKind::UnwindResume
        | mir::TerminatorKind::UnwindTerminate(_)
        | mir::TerminatorKind::CoroutineDrop => false,
        mir::TerminatorKind::SwitchInt { discr, .. } => mir_operand_mentions_local(discr, lid),
        mir::TerminatorKind::Assert { cond, .. } => mir_operand_mentions_local(cond, lid),
        mir::TerminatorKind::Drop { place, .. } => mir_place_mentions_local(place, lid),
        mir::TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            mir_operand_mentions_local(func, lid)
                || args.iter().any(|a| mir_operand_mentions_local(&a.node, lid))
                || mir_place_mentions_local(destination, lid)
        }
        mir::TerminatorKind::TailCall { func, args, .. } => {
            mir_operand_mentions_local(func, lid)
                || args.iter().any(|a| mir_operand_mentions_local(&a.node, lid))
        }
        mir::TerminatorKind::Yield {
            value, resume_arg, ..
        } => mir_operand_mentions_local(value, lid) || mir_place_mentions_local(resume_arg, lid),
        mir::TerminatorKind::InlineAsm { operands, .. } => operands.iter().any(|op| match op {
            mir::InlineAsmOperand::In { value, .. } => mir_operand_mentions_local(value, lid),
            mir::InlineAsmOperand::Out { place, .. } => {
                place.as_ref().is_some_and(|p| mir_place_mentions_local(p, lid))
            }
            mir::InlineAsmOperand::InOut {
                in_value,
                out_place,
                ..
            } => {
                mir_operand_mentions_local(in_value, lid)
                    || out_place
                        .as_ref()
                        .is_some_and(|p| mir_place_mentions_local(p, lid))
            }
            mir::InlineAsmOperand::Const { .. }
            | mir::InlineAsmOperand::SymFn { .. }
            | mir::InlineAsmOperand::SymStatic { .. }
            | mir::InlineAsmOperand::Label { .. } => false,
        }),
        mir::TerminatorKind::FalseEdge { .. } | mir::TerminatorKind::FalseUnwind { .. } => true,
    }
}

/// Pre-lowering scan of `mir::Body` identifying `*const` temporaries written
/// exclusively by `Rvalue::RawPtr(RawPtrKind::FakeForPtrMetadata, (*base))`
/// and read exclusively by `UnOp::PtrMetadata`, mirroring
/// `Trusted.MirSemantics.isFakePtrMetadataLocalV2`. `ir::Body::try_new`
/// independently re-checks the lowered `ir::Block`s.
fn collect_mir_fake_ptr_metadata_locals(
    body: &mir::Body<'_>,
    local_tys: &[ir::Ty],
) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for (lid, lty) in local_tys.iter().enumerate() {
        if lid <= body.arg_count
            || !matches!(
                lty,
                ir::Ty::RawPtr {
                    mutability: ir::Mutability::Shared,
                    ..
                }
            )
        {
            continue;
        }
        let mut saw_fake_assign = false;
        let mut valid = true;
        'blocks: for block in body.basic_blocks.iter() {
            for stmt in &block.statements {
                match &stmt.kind {
                    mir::StatementKind::Assign(assign) => {
                        let (dst, rv) = &**assign;
                        if mir_place_mentions_local(dst, lid) {
                            let ok = dst.local.as_usize() == lid
                                && dst.projection.is_empty()
                                && match rv {
                                    mir::Rvalue::RawPtr(
                                        mir::RawPtrKind::FakeForPtrMetadata,
                                        src,
                                    ) => {
                                        let base_idx = src.local.as_usize();
                                        base_idx != lid
                                            && src.projection.as_ref()
                                                == [mir::ProjectionElem::Deref]
                                            && match local_tys.get(base_idx) {
                                                Some(
                                                    ir::Ty::Ref { pointee: pt, .. }
                                                    | ir::Ty::RawPtr { pointee: pt, .. },
                                                ) => {
                                                    !matches!(&**pt, ir::Ty::OverflowPair(_))
                                                        && *lty
                                                            == ir::Ty::RawPtr {
                                                                mutability: ir::Mutability::Shared,
                                                                pointee: pt.clone(),
                                                            }
                                                }
                                                _ => false,
                                            }
                                    }
                                    _ => false,
                                };
                            if !ok {
                                valid = false;
                                break 'blocks;
                            }
                            saw_fake_assign = true;
                        } else if mir_rvalue_mentions_local(rv, lid) {
                            let ok = match rv {
                                mir::Rvalue::UnaryOp(
                                    mir::UnOp::PtrMetadata,
                                    mir::Operand::Copy(p) | mir::Operand::Move(p),
                                ) => p.local.as_usize() == lid && p.projection.is_empty(),
                                _ => false,
                            };
                            if !ok {
                                valid = false;
                                break 'blocks;
                            }
                        }
                    }
                    mir::StatementKind::StorageLive(_)
                    | mir::StatementKind::StorageDead(_)
                    | mir::StatementKind::Nop
                    | mir::StatementKind::ConstEvalCounter
                    | mir::StatementKind::Coverage(_) => {}
                    mir::StatementKind::PlaceMention(p) => {
                        if mir_place_mentions_local(p, lid) {
                            valid = false;
                            break 'blocks;
                        }
                    }
                    _ => {
                        valid = false;
                        break 'blocks;
                    }
                }
            }
            if let Some(term) = &block.terminator
                && mir_terminator_mentions_local(&term.kind, lid)
            {
                valid = false;
                break 'blocks;
            }
        }
        if saw_fake_assign && valid {
            out.insert(lid);
        }
    }
    out
}

#[derive(Clone, Debug)]
pub(crate) enum RawTerminator {
    Resolved(ir::Terminator),
    LocalCall {
        callee: LocalDefId,
        args: Vec<ir::Operand>,
        dst: u32,
        target: Option<u32>,
        unwind: ir::UnwindAction,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct ExtractedBody {
    arg_count: usize,
    is_unsafe: bool,
    local_tys: Vec<ir::Ty>,
    blocks: Vec<(Vec<ir::Statement>, RawTerminator)>,
    identity: String,
    local_callees: Vec<LocalDefId>,
    callees: BTreeSet<String>,
}

impl ExtractedBody {
    pub(crate) fn local_callees(&self) -> &[LocalDefId] {
        &self.local_callees
    }

    pub(crate) fn resolve(self, body_indices: &BTreeMap<u32, usize>) -> Result<ir::Body> {
        let blocks = self
            .blocks
            .into_iter()
            .map(|(statements, terminator)| {
                let terminator = match terminator {
                    RawTerminator::Resolved(term) => term,
                    RawTerminator::LocalCall {
                        callee,
                        args,
                        dst,
                        target,
                        unwind,
                    } => {
                        let key = callee.local_def_index.as_u32();
                        let body_index = *body_indices.get(&key).ok_or_else(|| {
                            format!("resolved body index missing for local callee {callee:?}")
                        })?;
                        ir::Terminator::Call {
                            callee: body_index,
                            args,
                            dst,
                            target,
                            unwind,
                        }
                    }
                };
                Ok(ir::Block {
                    statements,
                    terminator,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        ir::Body::try_new_with_callees(
            self.arg_count,
            self.is_unsafe,
            self.local_tys,
            blocks,
            self.identity,
            self.callees,
        )
    }
}

/// Map a printed `core::num` method path to its operand type and
/// [`ir::SysrootNumKind`]. The kind alone selects the Lean semantics, so
/// [`verify_sysroot_num_call`] checks the callee's MIR against the operator
/// that [`sysroot_kind_mir_op`] derives from this kind, not against a second
/// entry in this table.
fn parse_sysroot_num_path(path: &str) -> Option<(IntTy, ir::SysrootNumKind)> {
    let rest = path.strip_prefix("core::num::<impl ")?;
    let (ty_name, method) = rest.split_once(">::")?;
    let ity = match ty_name {
        "i8" => IntTy { width: IntWidth::I8, signed: true },
        "i16" => IntTy { width: IntWidth::I16, signed: true },
        "i32" => IntTy { width: IntWidth::I32, signed: true },
        "i64" => IntTy { width: IntWidth::I64, signed: true },
        "i128" => IntTy { width: IntWidth::I128, signed: true },
        "isize" => IntTy { width: IntWidth::Isize, signed: true },
        "u8" => IntTy { width: IntWidth::I8, signed: false },
        "u16" => IntTy { width: IntWidth::I16, signed: false },
        "u32" => IntTy { width: IntWidth::I32, signed: false },
        "u64" => IntTy { width: IntWidth::I64, signed: false },
        "u128" => IntTy { width: IntWidth::I128, signed: false },
        "usize" => IntTy { width: IntWidth::Isize, signed: false },
        _ => return None,
    };
    let kind = match method {
        "unchecked_add" => ir::SysrootNumKind::UncheckedAdd,
        "unchecked_sub" => ir::SysrootNumKind::UncheckedSub,
        "unchecked_mul" => ir::SysrootNumKind::UncheckedMul,
        "wrapping_add" => ir::SysrootNumKind::WrappingAdd,
        "wrapping_sub" => ir::SysrootNumKind::WrappingSub,
        "wrapping_mul" => ir::SysrootNumKind::WrappingMul,
        _ => return None,
    };
    Some((ity, kind))
}

/// The MIR operator that the pinned `core` body of `kind` applies to its two
/// arguments, mirroring `Trusted.MirSemantics.sysrootNumBinOp`. Deriving the
/// expected operator from the emitted kind means a wrong method-to-kind entry
/// in [`parse_sysroot_num_path`] fails the callee shape check instead of
/// silently selecting another operation's semantics.
fn sysroot_kind_mir_op(kind: ir::SysrootNumKind) -> mir::BinOp {
    match kind {
        ir::SysrootNumKind::UncheckedAdd => mir::BinOp::AddUnchecked,
        ir::SysrootNumKind::UncheckedSub => mir::BinOp::SubUnchecked,
        ir::SysrootNumKind::UncheckedMul => mir::BinOp::MulUnchecked,
        ir::SysrootNumKind::WrappingAdd => mir::BinOp::Add,
        ir::SysrootNumKind::WrappingSub => mir::BinOp::Sub,
        ir::SysrootNumKind::WrappingMul => mir::BinOp::Mul,
    }
}

fn is_sysroot_pure_noop_stmt(stmt: &mir::StatementKind<'_>) -> bool {
    match stmt {
        mir::StatementKind::Nop => true,
        mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
            local.as_u32() > 2
        }
        _ => false,
    }
}

fn is_arg_local_operand(op: &mir::Operand<'_>, expected_local: u32) -> bool {
    match op {
        mir::Operand::Copy(place) | mir::Operand::Move(place) => {
            place.projection.is_empty() && place.local.as_u32() == expected_local
        }
        mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => false,
    }
}

fn is_binop_assign_on_args(stmt: &mir::StatementKind<'_>, expected_op: mir::BinOp) -> bool {
    let mir::StatementKind::Assign(assign) = stmt else {
        return false;
    };
    let (place, rvalue) = &**assign;
    if !place.projection.is_empty() || place.local.as_u32() != 0 {
        return false;
    }
    let mir::Rvalue::BinaryOp(op, operands) = rvalue else {
        return false;
    };
    *op == expected_op
        && is_arg_local_operand(&operands.0, 1)
        && is_arg_local_operand(&operands.1, 2)
}

fn verify_sysroot_arith_block<'tcx>(
    block: &mir::BasicBlockData<'tcx>,
    expected_op: mir::BinOp,
    context: &str,
) -> Result<()> {
    if block.is_cleanup {
        return Err(format!("{context}: unexpected cleanup block in sysroot MIR"));
    }
    let mut saw_assign = false;
    for stmt in &block.statements {
        if is_binop_assign_on_args(&stmt.kind, expected_op) {
            if saw_assign {
                return Err(format!("{context}: multiple binary assignments in sysroot MIR"));
            }
            saw_assign = true;
        } else if !is_sysroot_pure_noop_stmt(&stmt.kind) {
            return Err(format!(
                "{context}: unexpected statement {:?} in sysroot MIR",
                stmt.kind
            ));
        }
    }
    if !saw_assign {
        return Err(format!(
            "{context}: missing expected binary assignment {expected_op:?} in sysroot MIR"
        ));
    }
    let Some(term) = block.terminator.as_ref() else {
        return Err(format!("{context}: missing terminator in sysroot MIR"));
    };
    if !matches!(term.kind, mir::TerminatorKind::Return) {
        return Err(format!(
            "{context}: expected Return terminator in sysroot MIR, got {:?}",
            term.kind
        ));
    }
    Ok(())
}

/// Admits a call to one of the six pinned `core::num` methods
/// (`unchecked_{add,sub,mul}`, `wrapping_{add,sub,mul}`) only if the callee's
/// `instance_mir` has exactly the shape that `Trusted.MirSemantics`
/// `sysrootNumBody` models: `_0 = op(copy _1, copy _2); return`.
///
/// `wrapping_*` must be a single block. Its source, in
/// `library/core/src/num/uint_macros.rs` (`rust-lang/rust`
/// `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), is:
///
/// > pub const fn wrapping_add(self, rhs: Self) -> Self {
/// >     intrinsics::wrapping_add(self, rhs)
/// > }
///
/// `unchecked_*` opens with `assert_unsafe_precondition!(check_language_ub,
/// ...)`. In `library/core/src/ub_checks.rs`, that macro expands to:
///
/// > if ::core::ub_checks::$kind() {
/// >     precondition_check($($arg,)*);
/// > }
///
/// and `check_language_ub` ends in `&& intrinsics::ub_checks()`, which lowers
/// to `Operand::RuntimeChecks(RuntimeChecks::UbChecks)`. Per
/// `compiler/rustc_middle/src/mir/syntax.rs`:
///
/// > /// Returns whether we should perform some UB-checking at runtime.
/// > /// See the `ub_checks` intrinsic docs for details.
/// > UbChecks,
///
/// and `RuntimeChecks::value` evaluates it as `sess.ub_checks()`. So the
/// entry block must be `SwitchInt(UbChecks)` with a `0` edge to the
/// arithmetic block and an `otherwise` edge to the `precondition_check` call,
/// and capture requires `ub_checks`, `overflow_checks` and `debug_assertions`
/// to be off. The checked block is then dead in the compiled program, and the
/// model reduces the body to the unchecked binary operation.
fn verify_sysroot_num_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_did: DefId,
    path: &str,
) -> Result<ir::SysrootNumOp> {
    let Some((ity, kind)) = parse_sysroot_num_path(path) else {
        return Err(format!("calls to external function `{path}` are unsupported"));
    };
    let mir_op = sysroot_kind_mir_op(kind);
    if tcx.intrinsic(callee_did).is_some() {
        return Err(format!(
            "sysroot numeric function `{path}` unexpectedly marked intrinsic"
        ));
    }
    if tcx.generics_of(callee_did).count() != 0 {
        return Err(format!(
            "sysroot numeric function `{path}` unexpectedly generic"
        ));
    }
    let is_unchecked = matches!(
        kind,
        ir::SysrootNumKind::UncheckedAdd
            | ir::SysrootNumKind::UncheckedSub
            | ir::SysrootNumKind::UncheckedMul
    );
    if is_unchecked
        && (tcx.sess.ub_checks()
            || tcx.sess.overflow_checks()
            || tcx.sess.opts.debug_assertions)
    {
        return Err(format!(
            "unchecked sysroot call `{path}` requires -Cdebug-assertions=no -Coverflow-checks=no"
        ));
    }
    codegen_attrs_for_def(tcx, callee_did, is_unchecked)?;
    let sig = tcx.fn_sig(callee_did).instantiate_identity().skip_binder();
    if sig.abi() != ExternAbi::Rust
        || sig.c_variadic()
        || sig.inputs().len() != 2
        || int_ty(sig.inputs()[0]) != Ok(ity)
        || int_ty(sig.inputs()[1]) != Ok(ity)
        || int_ty(sig.output()) != Ok(ity)
    {
        return Err(format!(
            "sysroot numeric function `{path}` signature disagrees with ({ity:?}, {ity:?}) -> {ity:?}"
        ));
    }
    let body = tcx.instance_mir(ty::InstanceKind::Item(callee_did));
    if body.arg_count != 2
        || body.tainted_by_errors.is_some()
        || body.coroutine.is_some()
        || body.spread_arg.is_some()
        || body.local_decls.len() < 3
    {
        return Err(format!(
            "sysroot numeric function `{path}` MIR shape does not match binary scalar operation"
        ));
    }
    for local_idx in 0..=2 {
        let local_ty = body.local_decls[mir::Local::from_usize(local_idx)].ty;
        if int_ty(local_ty) != Ok(ity) {
            return Err(format!(
                "sysroot numeric function `{path}` local _{local_idx} type disagrees with {ity:?}"
            ));
        }
    }
    let entry_bb = &body.basic_blocks[mir::START_BLOCK];
    if entry_bb.is_cleanup {
        return Err(format!(
            "sysroot numeric function `{path}` entry block is unexpectedly cleanup"
        ));
    }
    if is_unchecked {
        if !entry_bb
            .statements
            .iter()
            .all(|stmt| is_sysroot_pure_noop_stmt(&stmt.kind))
        {
            return Err(format!(
                "sysroot numeric function `{path}` entry block contains unexpected statements: {:?}",
                entry_bb.statements
            ));
        }
        let Some(entry_term) = entry_bb.terminator.as_ref() else {
            return Err(format!("sysroot numeric function `{path}` missing entry terminator"));
        };
        let mir::TerminatorKind::SwitchInt {
            discr: mir::Operand::RuntimeChecks(mir::RuntimeChecks::UbChecks),
            targets,
        } = &entry_term.kind
        else {
            return Err(format!(
                "sysroot numeric function `{path}` expected SwitchInt(UbChecks), got {:?}",
                entry_term.kind
            ));
        };
        let target_pairs: Vec<(u128, mir::BasicBlock)> = targets.iter().collect();
        let arith_bb = match target_pairs.as_slice() {
            [(0, arith_bb)] => *arith_bb,
            _ => {
                return Err(format!(
                    "sysroot numeric function `{path}` unexpected UbChecks switch targets: {target_pairs:?}"
                ));
            }
        };
        let check_bb = targets.otherwise();
        if arith_bb == mir::START_BLOCK || check_bb == mir::START_BLOCK || arith_bb == check_bb {
            return Err(format!(
                "sysroot numeric function `{path}` unexpected UbChecks block topology"
            ));
        }
        verify_sysroot_arith_block(
            &body.basic_blocks[arith_bb],
            mir_op,
            path,
        )?;
        // Also ensure the untaken precondition_check block cannot corrupt state
        // if inspected.
        if body.basic_blocks.len() > 3 {
            return Err(format!(
                "sysroot numeric function `{path}` has unexpected extra blocks ({})",
                body.basic_blocks.len()
            ));
        }
    } else {
        if body.basic_blocks.len() != 1 {
            return Err(format!(
                "sysroot wrapping function `{path}` expected single-block MIR, got {} blocks",
                body.basic_blocks.len()
            ));
        }
        verify_sysroot_arith_block(entry_bb, mir_op, path)?;
    }
    Ok(ir::SysrootNumOp { kind, ty: ity })
}

/// Whether capture should lower admitted diverging `core::panicking::*` calls
/// (`panic` and `panic_nounwind` with a shared `&str` operand) into Profile v2
/// [`ir::CoreCallOp::PanicAbort`] terminators. Enabled only under
/// `-Cpanic=abort` without a crate-local `#[panic_handler]`; otherwise
/// `evalCorePanicAbort` would always fault `.unsupported`, so keeping
/// `Terminator::Unsupported` avoids forcing Profile v2 on Profile v1 programs
/// (including those with intra-crate calls).
fn admit_core_panicking_abort(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.panic_strategy() == rustc_target::spec::PanicStrategy::Abort
        && !tcx.lang_items().iter().any(|(lang_item, def)| {
            def.is_local() && matches!(lang_item, rustc_hir::LangItem::PanicImpl)
        })
}

/// Extract a direct zero-sized sysroot `core` `FnDef` callee and its generic
/// args from a MIR `Call` `func` operand.
fn direct_core_call_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &mir::Operand<'tcx>,
) -> Option<(DefId, ty::GenericArgsRef<'tcx>, String)> {
    let mir::Operand::Constant(const_op) = func else {
        return None;
    };
    if !matches!(
        const_op.const_,
        mir::Const::Val(mir::ConstValue::ZeroSized, _)
    ) {
        return None;
    }
    let ty::FnDef(callee_did, generic_args) = *const_op.const_.ty().kind() else {
        return None;
    };
    let path = core_def_path(tcx, callee_did)?;
    Some((callee_did, generic_args, path))
}

/// `<Vec<T, A> as Index<I>>` is generic over every `I: SliceIndex<[T]>`
/// (`impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A>`), but
/// `CoreCallOp::VecIndex`/`VecIndexMut` model only `I = usize`, which returns
/// a single element. Ranges and other `SliceIndex` types are refused here
/// rather than relying on the later IR type check.
fn check_vec_index_usize_arg(fn_args: ty::GenericArgsRef<'_>, path: &str) -> Result<()> {
    match fn_args.get(1).and_then(|a| a.as_type()).map(|t| t.kind()) {
        Some(ty::Uint(ty::UintTy::Usize)) => Ok(()),
        _ => Err(format!("non-`usize` index type in `{path}` is unsupported")),
    }
}

/// `Vec::extend_from_slice`, `Vec::resize`, and `Box::clone` are modeled as
/// bitwise copies of the element (`CoreCallOp::VecExtendFromSlice`,
/// `VecResize`, and `BoxClone`), but they call `T::clone` unless `T` is
/// `TrivialClone`. Only then does the library copy bytes, and only then is
/// `T::clone` guaranteed to equal a copy. `resize` clones `n - 1` times
/// (`ptr::write(ptr, value.clone())`), while `extend_from_slice` (through
/// `append_elements`) and `Box::clone` (through `ConvertVec` and `CopySpec`)
/// copy bytes only in their `TrivialClone` specializations. `TrivialClone` is
/// unsafe and documented as: "`Clone::clone` must be equivalent to copying
/// the value, otherwise calling functions such as `slice::clone_from_slice`
/// can have undefined behaviour." It is "automatically implemented when using
/// `#[derive(Clone, Copy)]`" and by every primitive the element fragment
/// admits, so a hand-written `Clone` (which may, say, return a different enum
/// variant) is refused here. The trait is resolved as the `trivial_clone`
/// lang item, never by path.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/clone.rs#L253-L283
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/alloc/src/vec/spec_extend.rs#L40-L58
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/alloc/src/vec/mod.rs#L3655-L3670
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/alloc/src/slice.rs#L408-L460
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/clone/uninit.rs#L12-L82
fn check_trivial_clone_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_args: ty::GenericArgsRef<'tcx>,
    path: &str,
) -> Result<()> {
    use rustc_trait_selection::infer::{InferCtxtExt as _, TyCtxtInferExt as _};
    let elem = fn_args
        .first()
        .and_then(|a| a.as_type())
        .ok_or_else(|| format!("missing element type in `{path}`"))?;
    let Some(trivial_clone) = tcx.lang_items().get(rustc_hir::LangItem::TrivialClone) else {
        return Err(format!("missing `TrivialClone` lang item for `{path}`"));
    };
    let (infcx, param_env) =
        tcx.infer_ctxt().build_with_typing_env(TypingEnv::fully_monomorphized());
    if !infcx
        .type_implements_trait(trivial_clone, [elem], param_env)
        .must_apply_modulo_regions()
    {
        return Err(format!(
            "`{path}` on element type {elem:?}, which is not `TrivialClone`, \
             is unsupported"
        ));
    }
    Ok(())
}

fn check_alloc_global_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_args: ty::GenericArgsRef<'tcx>,
    alloc_idx: usize,
    path: &str,
) -> Result<()> {
    if let Some(alloc_ty) = fn_args.get(alloc_idx).and_then(|a| a.as_type())
        && !is_global_allocator(tcx, alloc_ty)
    {
        return Err(format!("non-Global allocator in `{path}` is unsupported"));
    }
    Ok(())
}

/// `SwitchInt` evaluates its operand and selects an explicit or otherwise edge.
/// `Assert` "Evaluates the operand, which must have type `bool`. If it is not
/// equal to `expected`, initiates a panic." Its condition, expected value,
/// message kind, target, and [`unwind_action`] are preserved without
/// normalization.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L853-L870
/// `Unreachable` is retained because "Executing this terminator is UB."
/// Diverging calls (`TerminatorKind::Call { target: None, .. }`, e.g.
/// `zx_process_exit -> !` or `_start -> !`) never return to a continuation
/// block (`target` is "Where to go after this call returns. If none, the
/// call necessarily diverges."). Under `-Cpanic=abort` without a crate-local
/// `#[panic_handler]`, calls to `core::panicking::{panic, panic_nounwind}`
/// carrying a shared `&str` operand lower 1:1 to `ir::Terminator::CoreCall`
/// (`CoreCallOp::PanicAbort`) with that operand; every other diverging call
/// (after [`check_call_source`], including `core::panicking::panic_fmt`)
/// lowers to `ir::Terminator::Unsupported`
/// (`Trusted.MirAst.TerminatorKind.unsupported`), which steps fail-closed to
/// `.fault .unsupported` in `Trusted.MirSemantics` if reachable while
/// permitting verified functions whose diverging guard branches are proved
/// unreachable.
/// Returning calls (`target: Some(_)`) without cleanup unwinds admit three
/// callee classes: intra-crate direct calls ([`RawTerminator::LocalCall`],
/// Profile v1), the closed [`ir::CoreCallOp`] table (Profile v2), and audited
/// `core::num` sysroot calls ([`verify_sysroot_num_call`], Profile v1). A
/// sysroot `core` callee in the `CoreCallOp` table always lowers to
/// `CoreCall`. Indirect calls, other generic or external callees, `Drop`,
/// unwinds, assembly, and other terminators stay refused at capture time.
/// `TerminatorKind::Call` runs [`check_call_source`] first so
/// `CallSource::Use` fails closed even for diverging calls.
///
/// Profile v2-only `Assert`s and all `CoreCall`s (both returning ops and
/// diverging `PanicAbort`) select Profile v2; `capture::collect` refuses both
/// Profile v2 and `Assert`-bearing Profile v1 bodies under `--stdlib-crate`,
/// where language items such as the `panic_*` family would otherwise shape
/// captured behavior. Admitting `Drop` or other returning calls also widens
/// what `capture.rs` must check under `--stdlib-crate` and what metadata-only
/// emission must evaluate (callee `required_consts`); update
/// `check_stdlib_capability` and the emission note in `capture::run` first.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L692-L740
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L800-L821
fn terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
    term: &mir::TerminatorKind<'tcx>,
) -> Result<RawTerminator> {
    Ok(match term {
        mir::TerminatorKind::Goto { target } => RawTerminator::Resolved(ir::Terminator::Goto {
            block: target.as_u32(),
        }),
        mir::TerminatorKind::SwitchInt { discr, targets } => {
            RawTerminator::Resolved(ir::Terminator::SwitchInt {
                operand: operand(tcx, typing_env, discr)?,
                targets: targets
                    .iter()
                    .map(|(value, block)| (value, block.as_u32()))
                    .collect(),
                otherwise: targets.otherwise().as_u32(),
            })
        }
        mir::TerminatorKind::Assert {
            cond,
            expected,
            msg,
            target,
            unwind,
        } => {
            let unwind = unwind_action(*unwind, "assert")?;
            let msg_ir = match &**msg {
                mir::AssertMessage::Overflow(op, ..) => ir::AssertKind::Overflow {
                    op: bin_op(*op)?,
                },
                mir::AssertMessage::OverflowNeg(..) => ir::AssertKind::OverflowNeg,
                mir::AssertMessage::DivisionByZero(..) => ir::AssertKind::DivByZero,
                mir::AssertMessage::RemainderByZero(..) => ir::AssertKind::RemByZero,
                mir::AssertMessage::BoundsCheck { .. } => ir::AssertKind::BoundsCheck,
                mir::AssertMessage::MisalignedPointerDereference { .. } => {
                    ir::AssertKind::MisalignedPtrDeref
                }
                mir::AssertMessage::NullPointerDereference => ir::AssertKind::NullPtrDeref,
                other => return Err(format!("unsupported assert message: {other:?}")),
            };
            RawTerminator::Resolved(ir::Terminator::Assert {
                cond: operand(tcx, typing_env, cond)?,
                expected: *expected,
                msg: msg_ir,
                target: target.as_u32(),
                unwind,
            })
        }
        mir::TerminatorKind::Return => RawTerminator::Resolved(ir::Terminator::Ret),
        mir::TerminatorKind::Unreachable => RawTerminator::Resolved(ir::Terminator::Unreachable),
        mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            call_source,
            fn_span: _,
        } => {
            check_call_source(*call_source)?;
            let Some(target_bb) = target else {
                if admit_core_panicking_abort(tcx)
                    && destination.projection.is_empty()
                    && body.local_decls[destination.local].ty.is_never()
                    && args.len() == 1
                    && let Ok(uw) = unwind_action(*unwind, "call")
                    && let Some((_, generic_args, path)) = direct_core_call_callee(tcx, func)
                    && generic_args.is_empty()
                    && matches!(
                        path.as_str(),
                        "core::panicking::panic" | "core::panicking::panic_nounwind"
                    )
                    && matches!(
                        ty(tcx, args[0].node.ty(body, tcx)),
                        Ok(ir::Ty::Ref {
                            mutability: ir::Mutability::Shared,
                            pointee,
                        }) if *pointee == ir::Ty::Str
                    )
                    && let Ok(msg_arg) = operand(tcx, typing_env, &args[0].node)
                {
                    return Ok(RawTerminator::Resolved(ir::Terminator::CoreCall {
                        op: ir::CoreCallOp::PanicAbort,
                        args: vec![msg_arg],
                        dst: place(tcx, destination)?,
                        target: None,
                        unwind: uw,
                    }));
                }
                return Ok(RawTerminator::Resolved(ir::Terminator::Unsupported));
            };
            let mir::Operand::Constant(const_op) = func else {
                return Err(format!("indirect calls are unsupported: {func:?}"));
            };
            if !matches!(
                const_op.const_,
                mir::Const::Val(mir::ConstValue::ZeroSized, _)
            ) {
                return Err(format!("non-zero-sized call callee is unsupported: {func:?}"));
            }
            let ty::FnDef(callee_did, generic_args) = *const_op.const_.ty().kind() else {
                return Err(format!(
                    "calls through non-FnDef values are unsupported: {:?}",
                    const_op.const_.ty()
                ));
            };
            let args = args
                .iter()
                .map(|spanned| operand(tcx, typing_env, &spanned.node))
                .collect::<Result<Vec<_>>>()?;
            if let Some(path) = core_or_alloc_def_path(tcx, callee_did) {
                // `core_or_alloc_def_path` pins the callee to the authenticated
                // sysroot `core` or `alloc`, so neither a crate-local
                // `mod core` nor a local crate built with `--crate-name core`
                // reaches this branch. The closed Profile v2 `CoreCallOp`
                // table takes precedence;
                // remaining `core::num` arithmetic goes through the Profile v1
                // sysroot path, where `verify_sysroot_num_call` re-checks the
                // callee's `instance_mir` shape.
                match core_call_op(tcx, typing_env, callee_did, generic_args) {
                    Ok(op) => {
                        let unwind = unwind_action(*unwind, "call")?;
                        RawTerminator::Resolved(ir::Terminator::CoreCall {
                            op,
                            args,
                            dst: place(tcx, destination)?,
                            target: Some(target_bb.as_u32()),
                            unwind,
                        })
                    }
                    Err(core_err) => {
                        if parse_sysroot_num_path(&path).is_none() {
                            return Err(core_err);
                        }
                        if !generic_args.is_empty() {
                            return Err(format!(
                                "sysroot numeric function `{path}` unexpectedly instantiated"
                            ));
                        }
                        let op = verify_sysroot_num_call(tcx, callee_did, &path)?;
                        RawTerminator::Resolved(ir::Terminator::SysrootCall {
                            op,
                            args,
                            dst: local(destination)?,
                            target: Some(target_bb.as_u32()),
                            unwind: unwind_action(*unwind, "call")?,
                        })
                    }
                }
            } else {
                let path = rustc_middle::ty::print::with_no_trimmed_paths!(
                    rustc_middle::ty::print::with_no_visible_paths!(tcx.def_path_str(callee_did))
                );
                let Some(local_callee) = callee_did.as_local() else {
                    return Err(format!("calls to external function `{path}` are unsupported"));
                };
                if !generic_args.is_empty() || tcx.generics_of(callee_did).count() != 0 {
                    return Err(format!(
                        "calls to generic or monomorphized functions (`{path}`) are unsupported"
                    ));
                }
                if tcx
                    .codegen_fn_attrs(callee_did)
                    .flags
                    .contains(CodegenFnAttrFlags::TRACK_CALLER)
                {
                    return Err(format!(
                        "intra-crate calls to #[track_caller] function `{path}` are unsupported"
                    ));
                }
                RawTerminator::LocalCall {
                    callee: local_callee,
                    args,
                    dst: local(destination)?,
                    target: Some(target_bb.as_u32()),
                    unwind: unwind_action(*unwind, "call")?,
                }
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

pub(crate) fn instance_path<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> String {
    rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(
            tcx.def_path_str_with_args(instance.def_id(), instance.args)
        )
    )
}

fn instance_identity<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> String {
    format!("rust-path-v1::{}", instance_path(tcx, instance))
}

/// Collect intra-crate static callable identities from a `ty::FnDef` operand
/// type for Tarjan SCC condensation. External (`!is_local()`) or non-`FnDef`
/// types insert nothing.
///
/// Matches the pinned `rustc` representation:
/// - `TyKind::FnDef(I::FunctionId, I::GenericArgs)` holds "the anonymous type
///   of a function declaration/definition" where "each function has a unique
///   type" paired with its generic arguments:
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L156-L168
/// - `Instance::try_resolve` "resolves a `(def_id, args)` pair to an
///   (optional) instance" ("returns `Ok(None)` if we cannot resolve `Instance`
///   to a specific instance"):
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/instance.rs#L471-L502
/// - The resolved `Instance` pairs `def: InstanceKind<'tcx>` and
///   `args: GenericArgsRef<'tcx>`, with `Instance::def_id` delegating to
///   `InstanceKind::def_id`:
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/instance.rs#L33-L36
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/instance.rs#L239-L262
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/instance.rs#L466-L469
/// - Monomorphized callee identities use `tcx.def_path_str_with_args` with
///   trimming and visible-path shortcuts disabled, matching
///   `instance_path`/`item_identity`:
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2195-L2209
fn collect_local_callee_identities<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    raw_ty: ty::Ty<'tcx>,
    out: &mut BTreeSet<String>,
) {
    let ty::FnDef(def_id, args) = *raw_ty.kind() else {
        return;
    };
    if !args.has_non_region_param()
        && !args.has_non_region_infer()
        && !args.references_error()
        && let Ok(Some(inst)) = ty::Instance::try_resolve(tcx, typing_env, def_id, args)
    {
        if !inst.def_id().is_local() {
            return;
        }
        let lifetime_only = inst
            .args
            .iter()
            .all(|arg| matches!(arg.kind(), ty::GenericArgKind::Lifetime(_)));
        if lifetime_only {
            // Uninstantiated capture (`body_inner` with `instance: None`)
            // admits local defs whose generics are purely lifetimes under
            // `item_identity` (named `'a`), whereas explicit `--instantiate`
            // captures record `instance_identity` (erased `'_`). Emit the
            // item identity unconditionally and also the instance identity
            // when lifetime args are present so either form matches.
            out.insert(item_identity(tcx, inst.def_id()));
            if !inst.args.is_empty() {
                out.insert(instance_identity(tcx, inst));
            }
        } else {
            out.insert(instance_identity(tcx, inst));
        }
        return;
    }
    if def_id.is_local()
        && args.iter().all(|arg| matches!(arg.kind(), ty::GenericArgKind::Lifetime(_)))
    {
        out.insert(item_identity(tcx, def_id));
    }
}

fn collect_operand_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
    op: &mir::Operand<'tcx>,
    out: &mut BTreeSet<String>,
) {
    collect_local_callee_identities(tcx, typing_env, op.ty(body, tcx), out);
}

/// Sharded captures permute `Captured.program.bodies` into canonical
/// callee-first Tarjan-SCC order while keeping `Program.entryDefId = 0`, so
/// sharded crates must identify verified items by `Body.identity`.
///
/// Exhaustive MIR call-site matching follows pinned `rust-lang/rust`
/// (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
/// - `StatementKind::Assign`: "Assign statements roughly correspond to an
///   assignment in Rust proper (`x = ...`)":
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L305-L335
/// - `Rvalue::{Use, Repeat, Cast, BinaryOp, UnaryOp, Aggregate,
///   WrapUnsafeBinder}` cover operand-bearing right-hand sides;
///   reference/discriminant/layout rvalues hold `Place`/`DefId` values rather
///   than `Operand` function items:
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488
/// - `TerminatorKind::Call { func, args, .. }`: "evaluates the `func` operand
///   and the arguments, and starts execution of the referred to function";
///   `SwitchInt { discr, .. }`, `TailCall { func, args, .. }`,
///   `Assert { cond, .. }`, and `Yield { value, .. }` carry direct operands,
///   while `Drop`, `InlineAsm` (rejected by `extract::terminator`; any
///   `InlineAsmOperand::SymFn` symbol is not a direct MIR `Call` edge), and
///   control-flow-only terminators are skipped:
///   https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L692-L981
///
/// Callee edges are purely SCC-partitioning and topological-ordering hints;
/// indirect `fn()` calls or unmodeled aggregates cannot alter
/// `ProgramVerified` theorem meaning because every captured body is verified.
fn collect_block_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
    block: &mir::BasicBlockData<'tcx>,
    out: &mut BTreeSet<String>,
) {
    for stmt in &block.statements {
        if let mir::StatementKind::Assign(assign) = &stmt.kind {
            match &assign.1 {
                mir::Rvalue::Use(op, _)
                | mir::Rvalue::Repeat(op, _)
                | mir::Rvalue::UnaryOp(_, op)
                | mir::Rvalue::Cast(_, op, _)
                | mir::Rvalue::WrapUnsafeBinder(op, _) => {
                    collect_operand_callee(tcx, typing_env, body, op, out);
                }
                mir::Rvalue::BinaryOp(_, pair) => {
                    collect_operand_callee(tcx, typing_env, body, &pair.0, out);
                    collect_operand_callee(tcx, typing_env, body, &pair.1, out);
                }
                mir::Rvalue::Aggregate(_, ops) => {
                    for op in ops {
                        collect_operand_callee(tcx, typing_env, body, op, out);
                    }
                }
                mir::Rvalue::Ref(..)
                | mir::Rvalue::ThreadLocalRef(..)
                | mir::Rvalue::RawPtr(..)
                | mir::Rvalue::Discriminant(..)
                | mir::Rvalue::CopyForDeref(..)
                | mir::Rvalue::Reborrow(..) => {}
            }
        }
    }
    if let Some(term) = &block.terminator {
        match &term.kind {
            mir::TerminatorKind::Call { func, args, .. }
            | mir::TerminatorKind::TailCall { func, args, .. } => {
                collect_operand_callee(tcx, typing_env, body, func, out);
                for arg in args {
                    collect_operand_callee(tcx, typing_env, body, &arg.node, out);
                }
            }
            mir::TerminatorKind::SwitchInt { discr, .. } => {
                collect_operand_callee(tcx, typing_env, body, discr, out);
            }
            mir::TerminatorKind::Assert { cond, .. } => {
                collect_operand_callee(tcx, typing_env, body, cond, out);
            }
            mir::TerminatorKind::Yield { value, .. } => {
                collect_operand_callee(tcx, typing_env, body, value, out);
            }
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(..)
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Drop { .. }
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. }
            | mir::TerminatorKind::InlineAsm { .. } => {}
        }
    }
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
/// the MIR locals. Reading it takes a returning call to `caller_location`
/// (returning `&'static Location<'_>`), which is outside the closed
/// [`ir::CoreCallOp`] table and the audited `core::num` sysroot table, so no
/// captured body can observe it. Passing it on to a `#[track_caller]` callee
/// is refused for intra-crate callees and skipped on `UbChecks == 0` sysroot
/// paths. Otherwise the location only reaches panic payloads (of a failed
/// `Assert` or of the `#[track_caller]` `core` functions in the `CoreCallOp`
/// table), never a captured local.
/// The compiler also sets this flag when a trait method inherits the
/// attribute from its declaration.
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L763-L779
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L855-L856
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L355-L358
///
/// Every other flag at the pinned revision is refused; see
/// [`codegen_attrs_for_def`].
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L156-L214
const ADMITTED_CODEGEN_FLAGS: CodegenFnAttrFlags = CodegenFnAttrFlags::COLD;

/// Refuse code-generation attributes whose effect the model does not state.
///
/// `codegen_fn_attrs` combines an item's codegen attributes with the settings
/// that the compiler implies for it. Destructuring every field of
/// `CodegenFnAttrs` makes a compiler upgrade that adds a field fail to compile
/// here until the field is classified. Only settings that cannot change what
/// a call executes or what the body may assume are admitted: inlining hints,
/// `#[optimize]` goals, and [`ADMITTED_CODEGEN_FLAGS`] (plus `TRACK_CALLER`
/// when `allow_track_caller` holds). Everything else is a refusal, including
/// attributes that are rare or impossible on an admitted function, so an
/// unclassified case cannot pass silently.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L60-L112
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L551-L577
pub(crate) fn codegen_attrs(tcx: TyCtxt<'_>, def: LocalDefId) -> Result<()> {
    codegen_attrs_for_def(tcx, def.to_def_id(), true)
}

fn codegen_attrs_for_def(tcx: TyCtxt<'_>, def: DefId, allow_track_caller: bool) -> Result<()> {
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
    let allowed_flags = if allow_track_caller {
        ADMITTED_CODEGEN_FLAGS.union(CodegenFnAttrFlags::TRACK_CALLER)
    } else {
        ADMITTED_CODEGEN_FLAGS
    };
    let unmodeled = flags.difference(allowed_flags);
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

/// Translate the provider's exact body, evaluating all `required_consts`
/// compile-time obligations before admitting the body.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L265-L271
pub(crate) fn extract_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    body: &mir::Body<'tcx>,
    features: crate::capture::FeaturePolicy<'_>,
) -> Result<ExtractedBody> {
    body_inner(tcx, def, None, body, TypingEnv::fully_monomorphized(), features)
}

/// Translate an explicitly monomorphized body validated by [`crate::mono`].
pub(crate) fn extract_instantiated_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    resolved: &crate::mono::ResolvedMonoBody<'tcx>,
    features: crate::capture::FeaturePolicy<'_>,
) -> Result<ExtractedBody> {
    body_inner(
        tcx,
        resolved.resolved_local,
        Some(resolved.instance),
        &resolved.body,
        resolved.typing_env,
        features,
    )
}

fn body_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    instance: Option<ty::Instance<'tcx>>,
    body: &mir::Body<'tcx>,
    typing_env: TypingEnv<'tcx>,
    features: crate::capture::FeaturePolicy<'_>,
) -> Result<ExtractedBody> {
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
    // RUSTC-WORKAROUND(#4365): MIR UB checks survive only under this flag.
    // Defense in depth: `-Zmir-preserve-ub` disables `RemovePlaceMention` and
    // trivial `SwitchInt` read erasure before `Runtime(PostCleanup)`.
    if !tcx.sess.opts.unstable_opts.mir_preserve_ub {
        return Err(
            "capture requires -Zmir-preserve-ub so PlaceMention and SwitchInt \
             UB checks survive Runtime(PostCleanup)"
                .into(),
        );
    }
    // RUSTC-WORKAROUND(#4364): codegen rewrites `Use` calls after capture.
    // Defense in depth: re-enforce the closed positive `#![feature(...)]`
    // allowlist and explicitly refuse `#![feature(ergonomic_clones)]` before
    // per-body translation. Post-capture `optimize_use_clone` in
    // `rustc_codegen_ssa` ("Replace `clone` calls that come from `use`
    // statements with direct copies if possible", guarded by
    // `if tcx.features().ergonomic_clones()`) rewrites `CallSource::Use` calls
    // on `&T` (`T: Copy`) to bitwise copies after `Runtime(PostCleanup)`.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L217-L224
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L350-L407
    crate::capture::check_allowed_features(tcx, features)?;
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
    eval_required_consts(tcx, typing_env, body)?;
    // Unrequested generic entry points would require quantified instantiation
    // obligations; compiler completion alone does not prove every future
    // instantiation. Explicit concrete instantiations are admitted only after
    // `mono::instantiate_body` resolves and validates concrete args and trait
    // obligations.
    // `Generics` describes "the formal type/lifetime parameters associated
    // with an item or method", optionally starting with `Self`, and `count`
    // is `self.parent_count + self.own_params.len()`. A method therefore also
    // counts its parent's parameters, including a trait's implicit `Self`.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/generics.rs#L112-L116
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/generics.rs#L153-L156
    let (signature, identity) = match instance {
        None => {
            // Admit uninstantiated bodies whose own and parent generics are
            // all `GenericParamDefKind::Lifetime` (of `Lifetime`, `Type`, and
            // `Const`) and carry no predicates (`predicates_of` returns "the
            // (elaborated) *predicates* of the definition ... that must be
            // proven true at usage sites"). Walking `parent` covers impl and
            // trait parameters, including a trait's implicit `Self` (a
            // `Type` parameter). Lifetime parameters select no runtime value
            // or layout: [`ty`] ignores the region of `ty::Ref`, so every
            // instantiation of such a body captures to the same IR. Bounds
            // (including `'a: 'b`) are refused because they would be
            // unrecorded entry assumptions.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/generics.rs#L12-L17
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/generics.rs#L112-L121
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/queries.rs#L416-L423
            let mut cur_gen = Some(def.to_def_id());
            while let Some(did) = cur_gen {
                let gens = tcx.generics_of(did);
                for param in &gens.own_params {
                    if !matches!(param.kind, ty::GenericParamDefKind::Lifetime) {
                        return Err(
                            "generic functions require quantified instantiation obligations".into(),
                        );
                    }
                }
                if !tcx.predicates_of(did).predicates.is_empty() {
                    return Err("functions with generic or lifetime bounds are unsupported".into());
                }
                cur_gen = gens.parent;
            }
            // With non-lifetime generics and bounds refused, the identity
            // instantiation is the only one. `skip_binder` "is only valid when
            // you are either extracting data that does not reference any
            // generic arguments": the ABI, C-variadic, and safety flags read
            // below live in `fn_sig_kind`, separately from the argument and
            // return types that late-bound regions can reference.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/unnormalized.rs#L96-L100
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/binder.rs#L164-L170
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L899-L904
            (
                tcx.fn_sig(def).instantiate_identity().skip_binder(),
                item_identity(tcx, def.to_def_id()),
            )
        }
        Some(inst) => {
            let bound_sig = tcx.fn_sig(def).instantiate(tcx, inst.args);
            let normalized_sig = tcx
                .try_normalize_erasing_regions(typing_env, bound_sig)
                .map_err(|_| "failed to normalize instantiated function signature".to_owned())?;
            let sig = normalized_sig.skip_binder();
            if sig.has_non_region_param() || sig.has_non_region_infer() || sig.references_error() {
                return Err("instantiated function signature remains generic or erroneous".into());
            }
            (sig, instance_identity(tcx, inst))
        }
    };
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
    codegen_attrs_for_def(tcx, def.to_def_id(), true)?;
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
    let mut local_tys = body
        .local_decls
        .iter()
        .map(|decl| ty(tcx, decl.ty))
        .collect::<Result<Vec<_>>>()?;
    // Enforce the Profile v2 local type fragment before lowering statements so
    // disallowed local types (e.g. `&&T` or `*const &T`) report the type
    // boundary error rather than secondary statement errors inside the body.
    // The full mixed ref/raw-pointer check runs after promoting single-purpose
    // shared `Box<P>` deref temps to `BoxAsRef`. Only non-argument `*const P`
    // locals can be promoted, so if the other locals already mix, the body is
    // refused here, before secondary statement or call errors.
    // `FakeForPtrMetadata` temporaries are pre-classified here, exempted from
    // the mixing check, and independently re-validated on the lowered
    // `ir::Body` in `ir::Body::try_new_with_callees`.
    let fake_meta_locals = collect_mir_fake_ptr_metadata_locals(body, &local_tys);
    ir::validate_local_ty_fragment(&local_tys)?;
    let mut local_callees = Vec::new();
    let mut seen_callees = BTreeSet::new();
    let mut callees = BTreeSet::new();
    // RUSTC-WORKAROUND(#4367): `Box` deref temporaries are promoted after
    // lowering, so only the unpromotable locals are checked here.
    let unpromotable_tys: Vec<ir::Ty> = local_tys
        .iter()
        .enumerate()
        .map(|(i, t)| match t {
            ir::Ty::RawPtr {
                mutability: ir::Mutability::Shared,
                ..
            } if i > body.arg_count => ir::Ty::Unit,
            _ => t.clone(),
        })
        .collect();
    ir::validate_local_tys_with_exemptions(&unpromotable_tys, &fake_meta_locals)?;
    let mut blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(id, block)| {
            collect_block_callees(tcx, typing_env, body, block, &mut callees);
            let statements = block
                .statements
                .iter()
                .enumerate()
                .map(|(index, stmt)| {
                    statement(tcx, typing_env, &body.local_decls, &stmt.kind)
                        .map_err(|error| format!("{id:?} statement {index}: {error}"))
                })
                .collect::<Result<Vec<_>>>()?;
            // The terminator "should generally ONLY be `None` during
            // construction"; a provided body without one is malformed.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L1327-L1335
            let term = block.terminator.as_ref().ok_or("missing terminator")?;
            let terminator = terminator(tcx, typing_env, body, &term.kind)
                .map_err(|error| format!("{id:?} terminator: {error}"))?;
            if let RawTerminator::LocalCall { callee, .. } = &terminator
                && seen_callees.insert(callee.local_def_index.as_u32())
            {
                local_callees.push(*callee);
            }
            Ok((statements, terminator))
        })
        .collect::<Result<Vec<_>>>()?;
    promote_box_as_ref(body.arg_count, &mut local_tys, &mut blocks);
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
    // apply. `codegen_attrs_for_def` above excludes target-feature entry points
    // and unsafe symbol and section attributes, whose obligations this bit does
    // not record; pointer-free syntax alone does not authorize treating an
    // unsafe declaration as an unrestricted safe entry point.
    let extracted = ExtractedBody {
        arg_count: body.arg_count,
        is_unsafe: signature.safety().is_unsafe(),
        local_tys,
        blocks,
        identity,
        local_callees,
        callees,
    };
    // Run single-body structural and type validation immediately so an
    // unsupported body reports its diagnostic even before cross-body
    // resolution.
    let mut dummy_indices = BTreeMap::new();
    for callee in &extracted.local_callees {
        dummy_indices.insert(callee.local_def_index.as_u32(), 0);
    }
    let _ = extracted.clone().resolve(&dummy_indices)?;
    Ok(extracted)
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
                    instantiations: std::collections::BTreeSet::new(),
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
                instantiations: std::collections::BTreeSet::new(),
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
                    value: ir::Rvalue::Discriminant {
                        place: ir::Place {
                            local: 1,
                            projection: vec![],
                        },
                    },
                }],
                terminator: ir::Terminator::Ret,
            }],
            "rust-path-v1::non_enum_discr".into(),
        )
        .unwrap_err();
        assert!(non_enum_discr.contains("requires a fieldless enum, Ordering, or Option place"));
    }

    #[test]
    fn operator_and_cast_extractors_admit_modeled_variants_and_refuse_others() {
        assert_eq!(un_op(mir::UnOp::Not).unwrap(), ir::UnOp::Not);
        assert_eq!(un_op(mir::UnOp::Neg).unwrap(), ir::UnOp::Neg);
        assert_eq!(un_op(mir::UnOp::PtrMetadata).unwrap(), ir::UnOp::PtrMetadata);

        assert_eq!(
            cast_kind(mir::CastKind::IntToInt).unwrap(),
            ir::CastKind::IntToInt
        );
        assert_eq!(
            cast_kind(mir::CastKind::PtrToPtr).unwrap(),
            ir::CastKind::PtrToPtr
        );
        assert_eq!(
            cast_kind(mir::CastKind::PointerWithExposedProvenance).unwrap(),
            ir::CastKind::IntToPtr
        );
        for refused_cast in [
            mir::CastKind::PointerExposeProvenance,
            mir::CastKind::FloatToInt,
            mir::CastKind::FloatToFloat,
            mir::CastKind::IntToFloat,
            mir::CastKind::FnPtrToPtr,
            mir::CastKind::Transmute,
            mir::CastKind::Subtype,
        ] {
            let err = cast_kind(refused_cast).unwrap_err();
            assert!(err.contains("unsupported cast kind"), "{err}");
        }
        // `CleanupPostBorrowck` rewrites `MutToConstPointer` and
        // `ArrayToPointer` to `PtrToPtr` before `Runtime(PostCleanup)`, so
        // capture refuses every `PointerCoercion` except `Unsize`.
        use rustc_middle::ty::adjustment::PointerCoercion;
        assert_eq!(
            cast_kind(mir::CastKind::PointerCoercion(
                PointerCoercion::Unsize,
                mir::CoercionSource::Implicit,
            ))
            .unwrap(),
            ir::CastKind::Unsize
        );
        for coercion in [
            PointerCoercion::MutToConstPointer,
            PointerCoercion::ArrayToPointer,
            PointerCoercion::UnsafeFnPointer,
        ] {
            let err = cast_kind(mir::CastKind::PointerCoercion(
                coercion,
                mir::CoercionSource::Implicit,
            ))
            .unwrap_err();
            assert!(err.contains("unsupported cast kind"), "{err}");
        }

        assert_eq!(
            unwind_action(mir::UnwindAction::Continue, "call").unwrap(),
            ir::UnwindAction::Continue
        );
        assert_eq!(
            unwind_action(mir::UnwindAction::Unreachable, "call").unwrap(),
            ir::UnwindAction::Unreachable
        );
        for reason in [
            mir::UnwindTerminateReason::Abi,
            mir::UnwindTerminateReason::InCleanup,
        ] {
            assert_eq!(
                unwind_action(mir::UnwindAction::Terminate(reason), "assert").unwrap(),
                ir::UnwindAction::Terminate
            );
        }
        let err = unwind_action(mir::UnwindAction::Cleanup(mir::START_BLOCK), "assert")
            .unwrap_err();
        assert!(err.contains("cleanup unwinds on assert are unsupported"), "{err}");

        for (mir_op, expected) in [
            (mir::BinOp::AddUnchecked, ir::BinOp::AddUnchecked),
            (mir::BinOp::SubUnchecked, ir::BinOp::SubUnchecked),
            (mir::BinOp::MulUnchecked, ir::BinOp::MulUnchecked),
            (mir::BinOp::Div, ir::BinOp::Div),
            (mir::BinOp::Rem, ir::BinOp::Rem),
            (mir::BinOp::AddWithOverflow, ir::BinOp::AddWithOverflow),
            (mir::BinOp::SubWithOverflow, ir::BinOp::SubWithOverflow),
            (mir::BinOp::MulWithOverflow, ir::BinOp::MulWithOverflow),
            (mir::BinOp::Cmp, ir::BinOp::Cmp),
            (mir::BinOp::Offset, ir::BinOp::Offset),
        ] {
            assert_eq!(bin_op(mir_op).unwrap(), expected);
        }
        // Pin every method-to-kind entry and the operator each kind's pinned
        // body must apply (`Trusted.MirSemantics.sysrootNumBinOp`).
        for (method, kind, op) in [
            ("unchecked_add", ir::SysrootNumKind::UncheckedAdd, mir::BinOp::AddUnchecked),
            ("unchecked_sub", ir::SysrootNumKind::UncheckedSub, mir::BinOp::SubUnchecked),
            ("unchecked_mul", ir::SysrootNumKind::UncheckedMul, mir::BinOp::MulUnchecked),
            ("wrapping_add", ir::SysrootNumKind::WrappingAdd, mir::BinOp::Add),
            ("wrapping_sub", ir::SysrootNumKind::WrappingSub, mir::BinOp::Sub),
            ("wrapping_mul", ir::SysrootNumKind::WrappingMul, mir::BinOp::Mul),
        ] {
            let path = format!("core::num::<impl u16>::{method}");
            let (ity, parsed) = parse_sysroot_num_path(&path).unwrap();
            assert_eq!(parsed, kind, "{method}");
            assert_eq!(ity, IntTy { width: IntWidth::I16, signed: false });
            assert_eq!(sysroot_kind_mir_op(kind), op, "{method}");
        }
        assert!(parse_sysroot_num_path("core::num::<impl u16>::saturating_add").is_none());
        assert!(parse_sysroot_num_path("core::num::<impl f32>::unchecked_add").is_none());
        for refused_bin in [
            mir::BinOp::ShlUnchecked,
            mir::BinOp::ShrUnchecked,
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
