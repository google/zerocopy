// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::BTreeSet;

use rustc_abi::{FieldIdx, Primitive, Size, TagEncoding, VariantIdx, Variants};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::interpret::{
    AllocId, ErrorHandled, GlobalAlloc, Pointer, Provenance, Scalar, alloc_range,
};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    Body, Const, ConstOperand, ConstValue, Location, Rvalue, StatementKind,
    UnevaluatedConst,
};
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{self, EarlyBinder, GenericArgs, Ty, TyCtxt, TyKind, ValTree};
use rustc_span::DUMMY_SP;

#[cfg(rustc_1_98)]
fn bind_early<'tcx, T>(_tcx: TyCtxt<'tcx>, val: T) -> EarlyBinder<'tcx, T> {
    EarlyBinder::bind(val)
}

#[cfg(rustc_1_101)]
fn bind_early<'tcx, T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    val: T,
) -> EarlyBinder<'tcx, T> {
    EarlyBinder::bind(tcx, val)
}

#[cfg(rustc_1_98)]
fn eval_for_typeck<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    uv: UnevaluatedConst<'tcx>,
) -> String {
    if uv.promoted.is_some() {
        return "N/A(promoted_cannot_shrink)".to_string();
    }
    match tcx.const_eval_resolve_for_typeck(typing_env, uv.shrink(), DUMMY_SP) {
        Ok(Ok(vt)) => format!("Ok(ValTree({}))", format_valtree(tcx, vt)),
        Ok(Err(ty)) => format!("Ok(Err(NonSupportedType({ty})))"),
        Err(ErrorHandled::Reported(info, _)) => {
            format!(
                "Err(Reported(allowed_in_infallible={}))",
                info.is_allowed_in_infallible()
            )
        }
        Err(ErrorHandled::TooGeneric(_)) => "Err(TooGeneric)".to_string(),
    }
}

#[cfg(rustc_1_101)]
fn eval_for_typeck<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    uv: UnevaluatedConst<'tcx>,
) -> String {
    if uv.promoted.is_some() {
        return "N/A(promoted_cannot_shrink)".to_string();
    }
    match tcx.const_eval_resolve_for_typeck(typing_env, uv.shrink(tcx), DUMMY_SP) {
        Ok(Ok(vt)) => format!("Ok(ValTree({}))", format_valtree(tcx, vt)),
        Ok(Err(ty)) => format!("Ok(Err(NonSupportedType({ty})))"),
        Err(ErrorHandled::Reported(info, _)) => {
            format!(
                "Err(Reported(allowed_in_infallible={}))",
                info.is_allowed_in_infallible()
            )
        }
        Err(ErrorHandled::TooGeneric(_)) => "Err(TooGeneric)".to_string(),
    }
}

fn format_valtree<'tcx>(_tcx: TyCtxt<'tcx>, vt: ValTree<'tcx>) -> String {
    if let Some(leaf) = vt.try_to_leaf() {
        format!("Leaf({leaf:?})")
    } else {
        let branches = vt.to_branch();
        let inner: Vec<String> = branches
            .iter()
            .map(|c| format_valtree(_tcx, c.to_value().valtree))
            .collect();
        format!("Branch([{}])", inner.join(", "))
    }
}

#[cfg(rustc_1_98)]
fn scalar_ptr_parts<Prov: Provenance>(s: Scalar<Prov>) -> Option<(Pointer<Prov>, u8)> {
    match s {
        Scalar::Ptr(ptr, sz) => Some((ptr, sz)),
        Scalar::Int(_) => None,
    }
}

#[cfg(rustc_1_101)]
fn scalar_ptr_parts<Prov: Provenance>(s: Scalar<Prov>) -> Option<(Pointer<Prov>, u8)> {
    match s {
        Scalar::Ptr(ptr, sz) => Some((ptr, sz.get())),
        Scalar::Int(_) => None,
    }
}

/// Pure algebraic representation of a decoded constant (no raw `AllocId` numbers,
/// no host/target byte endianness, no uninitialized padding bytes).
fn decode_const_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    cv: ConstValue,
    ty: Ty<'tcx>,
    visited: &mut BTreeSet<(AllocId, u64, String)>,
) -> String {
    let layout_cx = LayoutCx::new(tcx, typing_env);
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return format!("{{\"error\": \"LayoutError({ty})\"}}");
    };

    match cv {
        ConstValue::ZeroSized => decode_zero_sized(tcx, ty),
        ConstValue::Scalar(scalar) => {
            decode_from_scalar(tcx, typing_env, &layout_cx, scalar, layout, visited)
        }
        ConstValue::Slice { alloc_id, meta } => {
            decode_slice_from_alloc(tcx, typing_env, alloc_id, Size::ZERO, meta, ty, visited)
        }
        ConstValue::Indirect { alloc_id, offset } => {
            decode_from_memory(tcx, typing_env, &layout_cx, alloc_id, offset, layout, visited)
        }
    }
}

fn decode_zero_sized<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> String {
    match ty.kind() {
        TyKind::Tuple(fields) if fields.is_empty() => "{\"kind\": \"Unit\"}".to_string(),
        TyKind::Array(elem_ty, _) => {
            format!("{{\"kind\": \"Array\", \"elem_ty\": \"{elem_ty}\", \"elems\": []}}")
        }
        TyKind::Adt(adt_def, _) => {
            let name = tcx.item_name(adt_def.did());
            format!("{{\"kind\": \"ZeroSizedAdt\", \"name\": \"{name}\"}}")
        }
        TyKind::FnDef(def_id, _args) => {
            let path = tcx.def_path_str(*def_id);
            format!("{{\"kind\": \"FnDef\", \"path\": \"{path}\"}}")
        }
        _ => format!("{{\"kind\": \"ZeroSized\", \"ty\": \"{ty}\"}}"),
    }
}

fn decode_primitive_int<'tcx>(ty: Ty<'tcx>, bits: u128, size: Size) -> String {
    match ty.kind() {
        TyKind::Bool => format!("{{\"kind\": \"Bool\", \"val\": {}}}", bits != 0),
        TyKind::Char => {
            let c = char::from_u32(bits as u32).unwrap_or('\u{fffd}');
            format!("{{\"kind\": \"Char\", \"val\": {:?}}}", c)
        }
        TyKind::Uint(_) => format!("{{\"kind\": \"Uint\", \"ty\": \"{ty}\", \"val\": \"{bits}\"}}"),
        TyKind::Int(_) => {
            let shift = 128 - size.bits();
            let signed = ((bits << shift) as i128) >> shift;
            format!("{{\"kind\": \"Int\", \"ty\": \"{ty}\", \"val\": \"{signed}\"}}")
        }
        TyKind::Float(fty) => {
            format!("{{\"kind\": \"Float\", \"ty\": \"{fty:?}\", \"bits\": \"0x{bits:x}\"}}")
        }
        _ => format!("{{\"kind\": \"ScalarBits\", \"ty\": \"{ty}\", \"bits\": \"0x{bits:x}\"}}"),
    }
}

fn decode_from_scalar<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    layout_cx: &LayoutCx<'tcx>,
    scalar: Scalar,
    layout: rustc_middle::ty::layout::TyAndLayout<'tcx>,
    visited: &mut BTreeSet<(AllocId, u64, String)>,
) -> String {
    let ty = layout.ty;
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Uint(_) | TyKind::Int(_) | TyKind::Float(_) => {
            let sint = scalar.try_to_scalar_int().expect("primitive scalar must be int");
            let bits = sint.to_bits(layout.size);
            decode_primitive_int(ty, bits, layout.size)
        }
        TyKind::Pat(base_ty, _) => {
            let base_layout = tcx.layout_of(typing_env.as_query_input(*base_ty)).unwrap();
            let inner = decode_from_scalar(tcx, typing_env, layout_cx, scalar, base_layout, visited);
            format!("{{\"kind\": \"Pat\", \"ty\": \"{ty}\", \"base\": {inner}}}")
        }
        TyKind::RawPtr(pointee_ty, mutbl) => {
            if let Some((ptr, _sz)) = scalar_ptr_parts(scalar) {
                let (prov, offset) = ptr.into_raw_parts();
                let target = decode_provenance_target(
                    tcx,
                    typing_env,
                    prov.alloc_id(),
                    offset,
                    *pointee_ty,
                    visited,
                );
                format!(
                    "{{\"kind\": \"RawPtr\", \"mutability\": \"{mutbl:?}\", \"address_mode\": \"Provenance\", \"offset_bytes\": {}, \"target\": {target}}}",
                    offset.bytes()
                )
            } else {
                let sint = scalar.try_to_scalar_int().unwrap();
                let addr = sint.to_bits(layout.size);
                format!(
                    "{{\"kind\": \"RawPtr\", \"mutability\": \"{mutbl:?}\", \"address_mode\": \"ConcreteAddr\", \"addr\": \"0x{addr:x}\"}}"
                )
            }
        }
        TyKind::Ref(_, pointee_ty, mutbl) => {
            let (ptr, _sz) = scalar_ptr_parts(scalar).expect("thin reference must have provenance");
            let (prov, offset) = ptr.into_raw_parts();
            let target = decode_provenance_target(
                tcx,
                typing_env,
                prov.alloc_id(),
                offset,
                *pointee_ty,
                visited,
            );
            format!(
                "{{\"kind\": \"Ref\", \"mutability\": \"{mutbl:?}\", \"pointee\": {target}}}"
            )
        }
        TyKind::FnPtr(..) => {
            if let Some((ptr, _sz)) = scalar_ptr_parts(scalar) {
                let (prov, offset) = ptr.into_raw_parts();
                match tcx.global_alloc(prov.alloc_id()) {
                    GlobalAlloc::Function { instance, .. } => {
                        let fn_name = tcx.def_path_str_with_args(instance.def_id(), instance.args);
                        format!(
                            "{{\"kind\": \"FnPtr\", \"instance\": \"{fn_name}\", \"offset\": {}}}",
                            offset.bytes()
                        )
                    }
                    other => format!("{{\"kind\": \"FnPtrOther\", \"alloc\": \"{other:?}\"}}"),
                }
            } else {
                "{\"kind\": \"FnPtrInt\"}".to_string()
            }
        }
        TyKind::Tuple(_) => {
            let mut fields = Vec::new();
            for i in 0..layout.fields.count() {
                let f_layout = layout.field(layout_cx, i);
                if f_layout.is_zst() {
                    fields.push(decode_zero_sized(tcx, f_layout.ty));
                } else {
                    fields.push(decode_from_scalar(
                        tcx, typing_env, layout_cx, scalar, f_layout, visited,
                    ));
                }
            }
            format!("{{\"kind\": \"Tuple\", \"fields\": [{}]}}", fields.join(", "))
        }
        TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
            let name = tcx.item_name(adt_def.did());
            let variant = adt_def.non_enum_variant();
            let mut fields = Vec::new();
            for i in 0..layout.fields.count() {
                let fname = variant.fields[FieldIdx::from_usize(i)].name;
                let f_layout = layout.field(layout_cx, i);
                let val_str = if f_layout.is_zst() {
                    decode_zero_sized(tcx, f_layout.ty)
                } else {
                    decode_from_scalar(tcx, typing_env, layout_cx, scalar, f_layout, visited)
                };
                fields.push(format!("{{\"name\": \"{fname}\", \"val\": {val_str}}}"));
            }
            format!(
                "{{\"kind\": \"Struct\", \"name\": \"{name}\", \"repr\": \"Scalar\", \"fields\": [{}]}}",
                fields.join(", ")
            )
        }
        TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
            let name = tcx.item_name(adt_def.did());
            let variant_idx = resolve_enum_variant_from_scalar(tcx, typing_env, layout, scalar);
            let variant_def = &adt_def.variant(variant_idx);
            let vname = variant_def.name;
            let vlayout = layout.for_variant(layout_cx, variant_idx);
            let mut fields = Vec::new();
            for i in 0..vlayout.fields.count() {
                let fname = variant_def.fields[FieldIdx::from_usize(i)].name;
                let f_layout = vlayout.field(layout_cx, i);
                let val_str = if f_layout.is_zst() {
                    decode_zero_sized(tcx, f_layout.ty)
                } else {
                    decode_from_scalar(tcx, typing_env, layout_cx, scalar, f_layout, visited)
                };
                fields.push(format!("{{\"name\": \"{fname}\", \"val\": {val_str}}}"));
            }
            format!(
                "{{\"kind\": \"Enum\", \"name\": \"{name}\", \"variant\": \"{vname}\", \"repr\": \"Scalar\", \"fields\": [{}]}}",
                fields.join(", ")
            )
        }
        _ => format!("{{\"kind\": \"UnhandledScalar\", \"ty\": \"{ty}\"}}"),
    }
}

fn resolve_enum_variant_from_scalar<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    layout: rustc_middle::ty::layout::TyAndLayout<'tcx>,
    scalar: Scalar,
) -> VariantIdx {
    let adt_def = layout.ty.ty_adt_def().expect("enum must be ADT");
    match &layout.variants {
        Variants::Empty => panic!("uninhabited enum"),
        Variants::Single { index } => *index,
        Variants::Multiple { tag, tag_encoding, .. } => {
            let tag_size = tag.size(&tcx);
            match tag_encoding {
                TagEncoding::Direct => {
                    let sint = scalar.try_to_scalar_int().expect("Direct tag must be int");
                    let raw_bits = sint.to_bits(tag_size);
                    let discr_ty = layout.ty.discriminant_ty(tcx);
                    let discr_size = tcx
                        .layout_of(typing_env.as_query_input(discr_ty))
                        .unwrap()
                        .size;
                    let discr_bits = if matches!(tag.primitive(), Primitive::Int(_, true)) {
                        let shift = 128 - tag_size.bits();
                        let signed = ((raw_bits << shift) as i128) >> shift;
                        discr_size.truncate(signed as u128)
                    } else {
                        raw_bits
                    };
                    adt_def
                        .discriminants(tcx)
                        .find(|(_, d)| d.val == discr_bits)
                        .expect("matching discriminant")
                        .0
                }
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                } => {
                    if scalar_ptr_parts(scalar).is_some() {
                        *untagged_variant
                    } else {
                        let sint = scalar.try_to_scalar_int().unwrap();
                        let tag_bits = sint.to_bits(tag_size);
                        let relative = tag_size.truncate(tag_bits.wrapping_sub(*niche_start));
                        let start = niche_variants.start.as_u32();
                        let end = niche_variants.last.as_u32();
                        if relative <= u128::from(end - start) {
                            VariantIdx::from_u32(start + relative as u32)
                        } else {
                            *untagged_variant
                        }
                    }
                }
            }
        }
    }
}

fn decode_provenance_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    alloc_id: AllocId,
    offset: Size,
    pointee_ty: Ty<'tcx>,
    visited: &mut BTreeSet<(AllocId, u64, String)>,
) -> String {
    match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Static(def_id) => {
            let path = tcx.def_path_str(def_id);
            format!(
                "{{\"global_kind\": \"Static\", \"def_path\": \"{path}\", \"offset_bytes\": {}}}",
                offset.bytes()
            )
        }
        GlobalAlloc::Function { instance, .. } => {
            let path = tcx.def_path_str_with_args(instance.def_id(), instance.args);
            format!(
                "{{\"global_kind\": \"Function\", \"instance\": \"{path}\", \"offset_bytes\": {}}}",
                offset.bytes()
            )
        }
        GlobalAlloc::VTable(ty, dyn_ty) => {
            format!(
                "{{\"global_kind\": \"VTable\", \"ty\": \"{ty}\", \"dyn_ty\": \"{dyn_ty:?}\"}}"
            )
        }
        GlobalAlloc::TypeId { ty } => {
            format!("{{\"global_kind\": \"TypeId\", \"ty\": \"{ty}\"}}")
        }
        GlobalAlloc::Memory(_alloc) => {
            let key = (alloc_id, offset.bytes(), pointee_ty.to_string());
            if !visited.insert(key.clone()) {
                return "{\"global_kind\": \"CycleDetected\"}".to_string();
            }
            let layout_cx = LayoutCx::new(tcx, typing_env);
            let res = if let Ok(layout) = tcx.layout_of(typing_env.as_query_input(pointee_ty))
                && layout.is_sized()
            {
                decode_from_memory(
                    tcx,
                    typing_env,
                    &layout_cx,
                    alloc_id,
                    offset,
                    layout,
                    visited,
                )
            } else {
                format!("{{\"global_kind\": \"UnsizedPointee\", \"ty\": \"{pointee_ty}\"}}")
            };
            visited.remove(&key);
            res
        }
    }
}

fn decode_slice_from_alloc<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    alloc_id: AllocId,
    offset: Size,
    len_meta: u64,
    ref_ty: Ty<'tcx>,
    visited: &mut BTreeSet<(AllocId, u64, String)>,
) -> String {
    let pointee_ty = ref_ty.builtin_deref(true).expect("slice ref must deref");
    let alloc = tcx.global_alloc(alloc_id).unwrap_memory().inner();
    match pointee_ty.kind() {
        TyKind::Str => {
            let start = offset.bytes_usize();
            let end = start + (len_meta as usize);
            let bytes = alloc.inspect_with_uninit_and_ptr_outside_interpreter(start..end);
            let s = std::str::from_utf8(bytes).unwrap_or("<invalid-utf8>");
            format!("{{\"kind\": \"Str\", \"len\": {len_meta}, \"val\": {s:?}}}")
        }
        TyKind::Slice(elem_ty) => {
            let layout_cx = LayoutCx::new(tcx, typing_env);
            let elem_layout = tcx.layout_of(typing_env.as_query_input(*elem_ty)).unwrap();
            let mut elems = Vec::new();
            for i in 0..len_meta {
                let elem_off = offset + Size::from_bytes(i * elem_layout.size.bytes());
                elems.push(decode_from_memory(
                    tcx,
                    typing_env,
                    &layout_cx,
                    alloc_id,
                    elem_off,
                    elem_layout,
                    visited,
                ));
            }
            format!(
                "{{\"kind\": \"Slice\", \"elem_ty\": \"{elem_ty}\", \"len\": {len_meta}, \"elems\": [{}]}}",
                elems.join(", ")
            )
        }
        _ => format!("{{\"kind\": \"CustomUnsizedSlice\", \"ty\": \"{ref_ty}\", \"meta\": {len_meta}}}"),
    }
}

fn decode_from_memory<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    layout_cx: &LayoutCx<'tcx>,
    alloc_id: AllocId,
    offset: Size,
    layout: rustc_middle::ty::layout::TyAndLayout<'tcx>,
    visited: &mut BTreeSet<(AllocId, u64, String)>,
) -> String {
    if layout.is_zst() {
        return decode_zero_sized(tcx, layout.ty);
    }

    let alloc = tcx.global_alloc(alloc_id).unwrap_memory().inner();
    let ptr_size = tcx.data_layout.pointer_size();

    let range = alloc_range(offset, layout.size);
    let fully_init = alloc.init_mask().is_range_initialized(range).is_ok();
    let num_ptrs = alloc.provenance().ptrs().len();

    let ty = layout.ty;
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Uint(_) | TyKind::Int(_) | TyKind::Float(_) | TyKind::Pat(..) => {
            let scalar = alloc
                .read_scalar(&tcx, range, false)
                .expect("primitive in memory must be initialized");
            decode_from_scalar(tcx, typing_env, layout_cx, scalar, layout, visited)
        }
        TyKind::RawPtr(..) | TyKind::FnPtr(..) => {
            let scalar = alloc
                .read_scalar(&tcx, range, range.size == ptr_size)
                .expect("ptr in memory must be initialized");
            decode_from_scalar(tcx, typing_env, layout_cx, scalar, visited_layout_clone(layout), visited)
        }
        TyKind::Ref(_, pointee_ty, mutbl) => {
            if layout.size == ptr_size {
                let scalar = alloc
                    .read_scalar(&tcx, range, true)
                    .expect("thin ref in memory must be initialized");
                decode_from_scalar(tcx, typing_env, layout_cx, scalar, layout, visited)
            } else {
                let ptr_scalar = alloc
                    .read_scalar(&tcx, alloc_range(offset, ptr_size), true)
                    .expect("wide ref data ptr");
                let meta_scalar = alloc
                    .read_scalar(&tcx, alloc_range(offset + ptr_size, ptr_size), false)
                    .expect("wide ref metadata");
                let meta = meta_scalar.try_to_scalar_int().unwrap().to_bits(ptr_size) as u64;
                let (ptr, _) = scalar_ptr_parts(ptr_scalar).expect("wide ref ptr provenance");
                let (prov, inner_off) = ptr.into_raw_parts();
                let inner_decoded = decode_slice_from_alloc(
                    tcx,
                    typing_env,
                    prov.alloc_id(),
                    inner_off,
                    meta,
                    ty,
                    visited,
                );
                format!(
                    "{{\"kind\": \"WideRefInMemory\", \"mutability\": \"{mutbl:?}\", \"pointee_ty\": \"{pointee_ty}\", \"target\": {inner_decoded}}}"
                )
            }
        }
        TyKind::Array(elem_ty, len_const) => {
            let count = len_const.try_to_target_usize(tcx).unwrap_or(0);
            let elem_layout = layout.field(layout_cx, 0);
            let mut elems = Vec::new();
            for i in 0..count {
                let elem_off = offset + Size::from_bytes(i * elem_layout.size.bytes());
                elems.push(decode_from_memory(
                    tcx,
                    typing_env,
                    layout_cx,
                    alloc_id,
                    elem_off,
                    elem_layout,
                    visited,
                ));
            }
            format!(
                "{{\"kind\": \"Array\", \"elem_ty\": \"{elem_ty}\", \"len\": {count}, \"elems\": [{}]}}",
                elems.join(", ")
            )
        }
        TyKind::Tuple(_) => {
            let mut fields = Vec::new();
            for i in 0..layout.fields.count() {
                let f_off = offset + layout.fields.offset(i);
                let f_layout = layout.field(layout_cx, i);
                fields.push(decode_from_memory(
                    tcx, typing_env, layout_cx, alloc_id, f_off, f_layout, visited,
                ));
            }
            format!(
                "{{\"kind\": \"Tuple\", \"size_bytes\": {}, \"fully_init\": {fully_init}, \"fields\": [{}]}}",
                layout.size.bytes(),
                fields.join(", ")
            )
        }
        TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
            let name = tcx.item_name(adt_def.did());
            let variant = adt_def.non_enum_variant();
            let mut fields = Vec::new();
            for i in 0..layout.fields.count() {
                let fname = variant.fields[FieldIdx::from_usize(i)].name;
                let f_off = offset + layout.fields.offset(i);
                let f_layout = layout.field(layout_cx, i);
                let val_str = decode_from_memory(
                    tcx, typing_env, layout_cx, alloc_id, f_off, f_layout, visited,
                );
                fields.push(format!(
                    "{{\"name\": \"{fname}\", \"offset_bytes\": {}, \"val\": {val_str}}}",
                    layout.fields.offset(i).bytes()
                ));
            }
            format!(
                "{{\"kind\": \"Struct\", \"name\": \"{name}\", \"size_bytes\": {}, \"fully_init\": {fully_init}, \"provenance_ptrs_in_alloc\": {num_ptrs}, \"fields\": [{}]}}",
                layout.size.bytes(),
                fields.join(", ")
            )
        }
        TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
            let name = tcx.item_name(adt_def.did());
            let variant_idx = match &layout.variants {
                Variants::Empty => panic!("uninhabited enum in memory"),
                Variants::Single { index } => *index,
                Variants::Multiple { tag, tag_field, .. } => {
                    let tag_off = offset + layout.fields.offset(tag_field.as_usize());
                    let tag_size = tag.size(&tcx);
                    let tag_scalar = alloc
                        .read_scalar(&tcx, alloc_range(tag_off, tag_size), tag_size == ptr_size)
                        .expect("enum tag in memory must be initialized");
                    resolve_enum_variant_from_scalar(tcx, typing_env, layout, tag_scalar)
                }
            };
            let variant_def = &adt_def.variant(variant_idx);
            let vname = variant_def.name;
            let vlayout = layout.for_variant(layout_cx, variant_idx);
            let mut fields = Vec::new();
            for i in 0..vlayout.fields.count() {
                let fname = variant_def.fields[FieldIdx::from_usize(i)].name;
                let f_off = offset + vlayout.fields.offset(i);
                let f_layout = vlayout.field(layout_cx, i);
                let val_str = decode_from_memory(
                    tcx, typing_env, layout_cx, alloc_id, f_off, f_layout, visited,
                );
                fields.push(format!(
                    "{{\"name\": \"{fname}\", \"offset_bytes\": {}, \"val\": {val_str}}}",
                    vlayout.fields.offset(i).bytes()
                ));
            }
            format!(
                "{{\"kind\": \"Enum\", \"name\": \"{name}\", \"variant\": \"{vname}\", \"size_bytes\": {}, \"fully_init\": {fully_init}, \"fields\": [{}]}}",
                layout.size.bytes(),
                fields.join(", ")
            )
        }
        _ => format!("{{\"kind\": \"UnhandledMemory\", \"ty\": \"{ty}\"}}"),
    }
}

fn visited_layout_clone<'tcx>(
    l: rustc_middle::ty::layout::TyAndLayout<'tcx>,
) -> rustc_middle::ty::layout::TyAndLayout<'tcx> {
    l
}

struct BodyConstCollector<'tcx> {
    consts: Vec<(Location, ConstOperand<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> for BodyConstCollector<'tcx> {
    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        self.consts.push((location, *constant));
    }
}

fn describe_const_kind<'tcx>(tcx: TyCtxt<'tcx>, c: Const<'tcx>) -> String {
    match c {
        Const::Val(cv, ty) => format!("Const::Val({cv:?}, {ty})"),
        Const::Ty(ty, ct) => format!("Const::Ty({ty}, {ct:?})"),
        Const::Unevaluated(uv, ty) => {
            let path = tcx.def_path_str(uv.def);
            let def_kind = tcx.def_kind(uv.def);
            format!(
                "Const::Unevaluated(def={path}, def_kind={def_kind:?}, args={:?}, promoted={:?}, ty={ty})",
                uv.args, uv.promoted
            )
        }
    }
}

fn describe_eval_result<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    res: Result<ConstValue, ErrorHandled>,
    ty: Ty<'tcx>,
) -> String {
    match res {
        Ok(cv) => {
            let variant_name = match cv {
                ConstValue::Scalar(Scalar::Int(_)) => "Scalar(Int)",
                ConstValue::Scalar(Scalar::Ptr(..)) => "Scalar(Ptr)",
                ConstValue::ZeroSized => "ZeroSized",
                ConstValue::Slice { .. } => "Slice",
                ConstValue::Indirect { .. } => "Indirect",
            };
            let mut visited = BTreeSet::new();
            let decoded = decode_const_value(tcx, typing_env, cv, ty, &mut visited);
            format!(
                "{{\"status\": \"Ok\", \"cv_variant\": \"{variant_name}\", \"decoded\": {decoded}}}"
            )
        }
        Err(ErrorHandled::Reported(info, span)) => {
            format!(
                "{{\"status\": \"Err(Reported)\", \"allowed_in_infallible\": {}, \"span_is_dummy\": {}}}",
                info.is_allowed_in_infallible(),
                span.is_dummy()
            )
        }
        Err(ErrorHandled::TooGeneric(span)) => {
            format!(
                "{{\"status\": \"Err(TooGeneric)\", \"span_is_dummy\": {}}}",
                span.is_dummy()
            )
        }
    }
}

struct ProbeCallbacks;

impl Callbacks for ProbeCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let errors_before = tcx.dcx().has_errors().is_some();

        println!("{{");
        println!("  \"errors_before_mir_queries\": {errors_before},");

        // 1. Inspect Part 1 functions (required_consts, Const::Unevaluated, ErrorHandled)
        let part1_fns = [
            "part1_unreachable_if_false_panic",
            "part1_unreachable_if_false_div_zero",
            "part1_match_false_deleted_bb_div_zero",
            "part1_promoted_if_false_div_zero",
            "part1_post_return_div_zero",
            "part1_concrete_size_check_u32_ok",
            "part1_concrete_size_check_u64_err",
            "part1_reachable_inline_div_zero",
            "part1_generic_mention_uncond_fail",
            "part1_generic_mention_size_check",
            "part1_generic_mention_trait_const",
        ];

        println!("  \"part1_functions\": [");
        let mut first_fn = true;
        for fn_name in part1_fns {
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if tcx.def_path_str(def_id).ends_with(fn_name) {
                    if !first_fn {
                        println!("    ,");
                    }
                    first_fn = false;

                    let errs_pre = tcx.dcx().err_count();
                    let body = tcx.mir_drops_elaborated_and_const_checked(local_def_id).borrow();
                    let errs_post_mir = tcx.dcx().err_count();

                    let mut bb_collector = BodyConstCollector { consts: Vec::new() };
                    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                        bb_collector.visit_basic_block_data(bb, bb_data);
                    }
                    let req_consts = body.required_consts();
                    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);

                    let bb_consts_desc: Vec<String> = bb_collector
                        .consts
                        .iter()
                        .map(|(loc, c)| format!("{:?}: {}", loc, describe_const_kind(tcx, c.const_)))
                        .collect();

                    let mut req_evals = Vec::new();
                    for rc in req_consts {
                        let desc = describe_const_kind(tcx, rc.const_);
                        let poly_res = rc.const_.eval(tcx, typing_env, rc.span);
                        let poly_json =
                            describe_eval_result(tcx, typing_env, poly_res, rc.const_.ty());

                        let generics = tcx.generics_of(def_id);
                        let mut mono_u32_json = "null".to_string();
                        let mut mono_u64_json = "null".to_string();
                        if generics.own_params.len() == 1
                            && matches!(
                                generics.own_params[0].kind,
                                ty::GenericParamDefKind::Type { .. }
                            )
                            && fn_name != "part1_generic_mention_trait_const"
                        {
                            let mono_env = ty::TypingEnv::fully_monomorphized();
                            let args_u32 = tcx.mk_args(&[tcx.types.u32.into()]);
                            let c_u32 = bind_early(tcx, rc.const_).instantiate(tcx, args_u32).skip_norm_wip();
                            let res_u32 = c_u32.eval(tcx, mono_env, rc.span);
                            mono_u32_json =
                                describe_eval_result(tcx, mono_env, res_u32, c_u32.ty());

                            let args_u64 = tcx.mk_args(&[tcx.types.u64.into()]);
                            let c_u64 = bind_early(tcx, rc.const_).instantiate(tcx, args_u64).skip_norm_wip();
                            let res_u64 = c_u64.eval(tcx, mono_env, rc.span);
                            mono_u64_json =
                                describe_eval_result(tcx, mono_env, res_u64, c_u64.ty());
                        }

                        req_evals.push(format!(
                            "{{\"const\": {desc:?}, \"eval_post_analysis\": {poly_json}, \"eval_mono_u32\": {mono_u32_json}, \"eval_mono_u64\": {mono_u64_json}}}"
                        ));
                    }
                    let errs_post_eval = tcx.dcx().err_count();

                    println!(
                        "    {{\"fn\": \"{fn_name}\", \"phase\": \"{:?}\", \"err_count_before_mir\": {errs_pre}, \"err_count_after_mir\": {errs_post_mir}, \"err_count_after_eval\": {errs_post_eval}, \"bb_const_count\": {}, \"bb_consts\": {:?}, \"required_consts_count\": {}, \"required_consts\": [{}]}}",
                        body.phase,
                        bb_consts_desc.len(),
                        bb_consts_desc,
                        req_consts.len(),
                        req_evals.join(", ")
                    );
                }
            }
        }
        println!("  ],");

        // 2. Part 2: 20 representative constant shapes (ConstValue vs ValTree vs Layout Decoder)
        println!("  \"part2_constants\": [");
        let mut first_const = true;
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let path = tcx.def_path_str(def_id);
            if path.starts_with("C_") {
                if !first_const {
                    println!("    ,");
                }
                first_const = false;

                let typing_env = ty::TypingEnv::fully_monomorphized();
                let args = GenericArgs::identity_for_item(tcx, def_id);
                let uv = UnevaluatedConst::new(def_id, args);
                let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
                let layout = tcx.layout_of(typing_env.as_query_input(ty)).unwrap();

                let is_trivial = tcx.is_trivial_const(local_def_id);
                let cv_res = tcx.const_eval_resolve(typing_env, uv, DUMMY_SP);
                let poly_res = tcx.const_eval_poly(def_id);
                assert_eq!(
                    cv_res, poly_res,
                    "const_eval_resolve and const_eval_poly must agree on mono const"
                );

                let vt_str = eval_for_typeck(tcx, typing_env, uv);
                let eval_json = describe_eval_result(tcx, typing_env, cv_res, ty);
                let repr_str = format!("{:?}", layout.backend_repr);
                let fields_str = format!("{:?}", layout.fields);
                let variants_str = format!("{:?}", layout.variants);

                println!(
                    "    {{\"name\": \"{path}\", \"ty\": \"{ty}\", \"size_bytes\": {}, \"align_bytes\": {}, \"is_trivial_const\": {is_trivial}, \"backend_repr\": {repr_str:?}, \"fields_shape\": {fields_str:?}, \"variants_shape\": {variants_str:?}, \"valtree_result\": {vt_str:?}, \"const_eval_resolve\": {eval_json}}}",
                    layout.size.bytes(),
                    layout.align.abi.bytes()
                );
            }
        }
        println!("  ],");

        // 3. Part 3: Constant Promotion (promoted[N] bodies, accepted vs rejected, generic promoted)
        let part3_items = [
            "promo_accepted_candidates",
            "promo_assert_eq",
            "promo_rejected_candidates",
            "PROMO_IN_CONST_CALL",
            "PROMO_IN_STATIC_CALL",
            "PROMO_IN_CONST_DEAD_BRANCH",
            "promo_generic_independent",
            "promo_generic_array_dependent",
            "promo_generic_size_of_dependent",
        ];

        println!("  \"part3_promotions\": [");
        let mut first_promo = true;
        for item_name in part3_items {
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if tcx.def_path_str(def_id).ends_with(item_name) {
                    if !first_promo {
                        println!("    ,");
                    }
                    first_promo = false;

                    let is_const_ctx = tcx.hir_body_const_context(local_def_id).is_some();
                    let body_ref;
                    let ctfe_body;
                    let body: &Body<'tcx> = if is_const_ctx {
                        ctfe_body = tcx.mir_for_ctfe(local_def_id);
                        ctfe_body
                    } else {
                        body_ref = tcx.mir_drops_elaborated_and_const_checked(local_def_id).borrow();
                        &body_ref
                    };
                    let promoteds = tcx.promoted_mir(local_def_id);
                    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
                    let args = GenericArgs::identity_for_item(tcx, def_id);

                    let mut promo_entries = Vec::new();
                    for (p_idx, p_body) in promoteds.iter_enumerated() {
                        let p_ty = p_body.return_ty();
                        let uv = UnevaluatedConst {
                            def: def_id,
                            args,
                            promoted: Some(p_idx),
                        };
                        let eval_res = tcx.const_eval_resolve(typing_env, uv, DUMMY_SP);
                        let eval_json = describe_eval_result(tcx, typing_env, eval_res, p_ty);

                        let generics = tcx.generics_of(def_id);
                        let mut mono_eval_json = "null".to_string();
                        if generics.own_params.len() == 1 {
                            let mono_env = ty::TypingEnv::fully_monomorphized();
                            let concrete_args = match generics.own_params[0].kind {
                                ty::GenericParamDefKind::Type { .. } => {
                                    tcx.mk_args(&[tcx.types.u64.into()])
                                }
                                ty::GenericParamDefKind::Const { .. } => {
                                    let c4 = ty::Const::from_target_usize(tcx, 4);
                                    tcx.mk_args(&[c4.into()])
                                }
                                _ => args,
                            };
                            let uv_mono = bind_early(tcx, uv).instantiate(tcx, concrete_args).skip_norm_wip();
                            let p_ty_mono = bind_early(tcx, p_ty).instantiate(tcx, concrete_args).skip_norm_wip();
                            let mono_res = tcx.const_eval_resolve(mono_env, uv_mono, DUMMY_SP);
                            mono_eval_json =
                                describe_eval_result(tcx, mono_env, mono_res, p_ty_mono);
                        }

                        let mut stmts = Vec::new();
                        for (bb, bb_data) in p_body.basic_blocks.iter_enumerated() {
                            for stmt in &bb_data.statements {
                                if !matches!(
                                    stmt.kind,
                                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_)
                                ) {
                                    stmts.push(format!("{bb:?}: {:?}", stmt.kind));
                                }
                            }
                            stmts.push(format!("{bb:?} term: {:?}", bb_data.terminator().kind));
                        }

                        promo_entries.push(format!(
                            "{{\"index\": \"{p_idx:?}\", \"phase\": \"{:?}\", \"return_ty\": \"{p_ty}\", \"required_consts_count\": {}, \"stmts\": {stmts:?}, \"eval_post_analysis\": {eval_json}, \"eval_monomorphized\": {mono_eval_json}}}",
                            p_body.phase,
                            p_body.required_consts().len()
                        ));
                    }

                    let mut unpromoted_borrows = Vec::new();
                    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                        for stmt in &bb_data.statements {
                            if let StatementKind::Assign(assign_box) = &stmt.kind
                                && let (lhs, Rvalue::Ref(_, bkind, place)) = &**assign_box
                            {
                                unpromoted_borrows.push(format!(
                                    "{bb:?}: {lhs:?} = &({bkind:?}) {place:?}"
                                ));
                            }
                        }
                    }

                    println!(
                        "    {{\"item\": \"{item_name}\", \"promoted_count\": {}, \"unpromoted_borrows\": {unpromoted_borrows:?}, \"promoteds\": [{}]}}",
                        promoteds.len(),
                        promo_entries.join(", ")
                    );
                }
            }
        }
        println!("  ]");
        println!("}}");

        Compilation::Stop
    }
}

#[cfg(rustc_1_98)]
fn invoke_compiler(args: &[String]) {
    let _ = rustc_driver::run_compiler(args, &mut ProbeCallbacks);
}

#[cfg(rustc_1_101)]
fn invoke_compiler(args: &[String]) {
    rustc_driver::compiler_entrypoint(args, &mut ProbeCallbacks);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let _ = rustc_driver::catch_fatal_errors(|| {
        invoke_compiler(&args);
    });
}
