// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Reference validity, access spans, and escape checks, aligned with
//! `Trusted.MirSemantics.{refValidInMem, refsValidInMem, refAccessSpans,
//! spansPairwiseDisjoint, hasEscapingRodataPtr, refsStayInCallerMem}`.

use alloc::vec::Vec;

use super::{
    CallerMemory, MemoryState, TargetEndian, checks::slice_from_raw_parts_check, codec::decode_val,
    int_layout, layout_of_ty, offset_is_aligned,
};
use crate::{
    ir::{Mutability, Ty},
    value::{FaultDetail, FaultKind, UbClass, Val},
};

/// Validate Rust language validity invariants for a `&T`, `&mut T`, `&[uN]`,
/// `&mut [uN]`, or `&str` value in `mem` (`Trusted.MirSemantics.refValidInMem`).
pub fn ref_valid_in_mem(
    mem: &MemoryState,
    endian: TargetEndian,
    req_mut: Mutability,
    pointee: &Ty,
    val: &Val,
) -> Result<(), FaultDetail> {
    match (pointee, val) {
        (Ty::Str, Val::SlicePtr { ptr, len }) => {
            if req_mut == Mutability::Mut {
                return Err(FaultDetail::unsupported("`&mut str` is unsupported in Profile v2"));
            }
            slice_from_raw_parts_check(mem, false, 1, 0, *ptr, *len)?;
            Ok(())
        }
        (Ty::Str, _) => {
            Err(FaultDetail::unsupported("`&str` reference requires a SlicePtr runtime value"))
        }
        (Ty::Slice { elem }, Val::SlicePtr { ptr, len }) => {
            let Ty::Int(ity) = elem.as_ref() else {
                return Err(FaultDetail::unsupported(
                    "only integer slice references are supported in Profile v2",
                ));
            };
            let lay = int_layout(ity.width);
            slice_from_raw_parts_check(
                mem,
                req_mut == Mutability::Mut,
                lay.size,
                lay.align_log2,
                *ptr,
                *len,
            )?;
            Ok(())
        }
        (Ty::Slice { .. }, _) => {
            Err(FaultDetail::unsupported("slice reference requires a SlicePtr runtime value"))
        }
        (pt, Val::Ptr(p)) => {
            let Some(lay) = layout_of_ty(pt, true) else {
                return Err(FaultDetail::unsupported("reference pointee has no Profile v2 layout"));
            };
            match p.alloc_id {
                None => {
                    if p.offset_bytes == 0 || lay.size > 0 {
                        return Err(FaultDetail::undefined_classified(
                            UbClass::InvalidReferenceProduced,
                            "null or non-ZST provenance-free reference",
                        ));
                    }
                    if !offset_is_aligned(p.offset_bytes, lay.align_log2) {
                        return Err(FaultDetail::undefined_classified(
                            UbClass::InvalidReferenceProduced,
                            "misaligned provenance-free ZST reference",
                        ));
                    }
                    match decode_val(endian, pt, &[], true) {
                        Ok(Some(_)) => Ok(()),
                        Ok(None) => Err(FaultDetail::undefined_classified(
                            UbClass::RefPointeeUninitOrInvalid,
                            "reference points to uninhabited or invalid ZST pointee",
                        )),
                        Err(err) if err.kind == FaultKind::Undefined => {
                            Err(FaultDetail::undefined_classified(
                                UbClass::RefPointeeUninitOrInvalid,
                                err.reason,
                            ))
                        }
                        Err(err) => Err(err),
                    }
                }
                Some(aid) => {
                    let Some(alloc) = mem.find(aid) else {
                        let class = if lay.size == 0 {
                            UbClass::ZstProvenanceDeadOrOob
                        } else {
                            UbClass::InvalidReferenceProduced
                        };
                        return Err(FaultDetail::undefined_classified(
                            class,
                            "reference points to unknown allocation",
                        ));
                    };
                    if !alloc.live || !MemoryState::is_in_bounds(alloc, p.offset_bytes, lay.size) {
                        let class = if lay.size == 0 {
                            UbClass::ZstProvenanceDeadOrOob
                        } else {
                            UbClass::InvalidReferenceProduced
                        };
                        return Err(FaultDetail::undefined_classified(
                            class,
                            "reference is dangling or out of bounds",
                        ));
                    }
                    if !MemoryState::is_aligned(alloc, p.offset_bytes, lay.align_log2) {
                        let class = if lay.align_log2 > alloc.align_log2 {
                            UbClass::SymbolicAllocAlignment
                        } else {
                            UbClass::InvalidReferenceProduced
                        };
                        return Err(FaultDetail::undefined_classified(
                            class,
                            "reference is misaligned",
                        ));
                    }
                    if req_mut == Mutability::Mut && alloc.mutability != Mutability::Mut {
                        let class = if lay.size == 0 {
                            UbClass::ZstMutRefImmutableAlloc
                        } else {
                            UbClass::InvalidReferenceProduced
                        };
                        return Err(FaultDetail::undefined_classified(
                            class,
                            "mutable reference points to immutable allocation",
                        ));
                    }
                    let start =
                        usize::try_from(p.offset_bytes).expect("in-bounds offset fits usize");
                    let len = usize::try_from(lay.size).expect("in-bounds size fits usize");
                    match decode_val(endian, pt, &alloc.bytes[start..start + len], true) {
                        Ok(Some(_)) => Ok(()),
                        Ok(None) => Err(FaultDetail::undefined_classified(
                            UbClass::RefPointeeUninitOrInvalid,
                            "reference points to uninitialized or uninhabited memory",
                        )),
                        Err(err) if err.kind == FaultKind::Undefined => {
                            Err(FaultDetail::undefined_classified(
                                UbClass::RefPointeeUninitOrInvalid,
                                err.reason,
                            ))
                        }
                        Err(err) => Err(err),
                    }
                }
            }
        }
        _ => Err(FaultDetail::unsupported("reference type requires a pointer runtime value")),
    }
}

/// Validate all references inside `(ty, val)` against `mem`, matching
/// `Trusted.MirSemantics.refsValidInMem`.
///
/// Always returns `FaultKind::Undefined` on failure (mirroring `refsValidInMem`
/// returning `false` whenever `refValidInMem` returns any error).
pub fn refs_valid_in_mem(
    mem: &MemoryState,
    endian: TargetEndian,
    ty: &Ty,
    val: &Val,
) -> Result<(), FaultDetail> {
    match (ty, val) {
        (Ty::Ref { mutability, pointee }, v) => {
            ref_valid_in_mem(mem, endian, *mutability, pointee, v).map_err(|err| {
                if err.kind == FaultKind::Undefined {
                    err
                } else {
                    FaultDetail::undefined(err.reason)
                }
            })
        }
        (Ty::Tuple { fields }, Val::Tuple(vals)) => {
            refs_valid_in_mem_list(mem, endian, fields, vals)
        }
        (Ty::Option { elem }, Val::OptionVal(Some(inner))) => {
            refs_valid_in_mem(mem, endian, elem, inner)
        }
        _ => Ok(()),
    }
}

/// Validate pairwise references across `(tys, vals)` against `mem`, matching
/// `Trusted.MirSemantics.refsValidInMemList`.
pub fn refs_valid_in_mem_list(
    mem: &MemoryState,
    endian: TargetEndian,
    tys: &[Ty],
    vals: &[Val],
) -> Result<(), FaultDetail> {
    if tys.len() != vals.len() {
        return Err(FaultDetail::undefined(
            "tuple or argument arity mismatch during reference validation",
        ));
    }
    for (ty, val) in tys.iter().zip(vals.iter()) {
        refs_valid_in_mem(mem, endian, ty, val)?;
    }
    Ok(())
}

/// Provenance-backed byte access span of a reference (`(isMut, allocId,
/// offset, byteSize)` in `Trusted.MirSemantics.refAccessSpans`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RefAccessSpan {
    pub is_mut: bool,
    pub alloc_id: u64,
    pub offset: u64,
    pub size: u128,
}

/// Extract provenance-backed access spans for every reference in `(ty, val)`.
pub fn ref_access_spans(ty: &Ty, val: &Val) -> Vec<RefAccessSpan> {
    let mut out = Vec::new();
    collect_ref_access_spans(ty, val, &mut out);
    out
}

/// Extract provenance-backed access spans across `(tys, vals)`.
pub fn ref_access_spans_list(tys: &[Ty], vals: &[Val]) -> Vec<RefAccessSpan> {
    let mut out = Vec::new();
    for (ty, val) in tys.iter().zip(vals.iter()) {
        collect_ref_access_spans(ty, val, &mut out);
    }
    out
}

fn collect_ref_access_spans(ty: &Ty, val: &Val, out: &mut Vec<RefAccessSpan>) {
    match (ty, val) {
        (Ty::Ref { mutability, pointee }, Val::SlicePtr { ptr, len }) if **pointee == Ty::Str => {
            if let Some(alloc_id) = ptr.alloc_id {
                out.push(RefAccessSpan {
                    is_mut: *mutability == Mutability::Mut,
                    alloc_id,
                    offset: ptr.offset_bytes,
                    size: u128::from(*len),
                });
            }
        }
        (Ty::Ref { mutability, pointee }, Val::SlicePtr { ptr, len }) => {
            if let Ty::Slice { elem } = pointee.as_ref()
                && let Ty::Int(ity) = elem.as_ref()
                && let Some(alloc_id) = ptr.alloc_id
            {
                let lay = int_layout(ity.width);
                out.push(RefAccessSpan {
                    is_mut: *mutability == Mutability::Mut,
                    alloc_id,
                    offset: ptr.offset_bytes,
                    size: u128::from(*len) * u128::from(lay.size),
                });
            }
        }
        (Ty::Ref { mutability, pointee }, Val::Ptr(p)) => {
            if let (Some(lay), Some(alloc_id)) = (layout_of_ty(pointee, true), p.alloc_id) {
                out.push(RefAccessSpan {
                    is_mut: *mutability == Mutability::Mut,
                    alloc_id,
                    offset: p.offset_bytes,
                    size: u128::from(lay.size),
                });
            }
        }
        (Ty::Tuple { fields }, Val::Tuple(vals)) => {
            for (t, v) in fields.iter().zip(vals.iter()) {
                collect_ref_access_spans(t, v, out);
            }
        }
        (Ty::Option { elem }, Val::OptionVal(Some(inner))) => {
            collect_ref_access_spans(elem, inner, out);
        }
        _ => {}
    }
}

fn spans_disjoint(a: RefAccessSpan, b: RefAccessSpan) -> bool {
    if !(a.is_mut || b.is_mut) || a.size == 0 || b.size == 0 || a.alloc_id != b.alloc_id {
        return true;
    }
    let a_start = u128::from(a.offset);
    let b_start = u128::from(b.offset);
    a_start + a.size <= b_start || b_start + b.size <= a_start
}

/// Check pairwise disjointness across active mutable borrow spans, matching
/// `Trusted.MirSemantics.spansPairwiseDisjoint`.
pub fn spans_pairwise_disjoint(spans: &[RefAccessSpan]) -> bool {
    for (idx, &a) in spans.iter().enumerate() {
        for &b in &spans[idx + 1..] {
            if !spans_disjoint(a, b) {
                return false;
            }
        }
    }
    true
}

/// Whether `ty` is shared `&str`, the only `str` pointer Profile v2 encodes
/// and decodes (`Trusted.MirSemantics.{encodeValV2, decodeValV2}`).
pub(super) fn is_shared_str_ref(ty: &Ty) -> bool {
    matches!(ty, Ty::Ref { mutability: Mutability::Shared, pointee } if **pointee == Ty::Str)
}

/// Collect the allocation ids of every reference or raw pointer inside
/// `(ty, val)`, matching `Trusted.MirSemantics.ptrOrRefAllocIds`.
fn collect_ptr_or_ref_alloc_ids(ty: &Ty, val: &Val, out: &mut Vec<u64>) {
    match (ty, val) {
        (Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. }, Val::SlicePtr { ptr, .. })
            if matches!(pointee.as_ref(), Ty::Slice { .. })
                || matches!(ty, Ty::Ref { .. }) && **pointee == Ty::Str =>
        {
            out.extend(ptr.alloc_id);
        }
        (Ty::Ref { .. } | Ty::RawPtr { .. }, Val::Ptr(p)) => out.extend(p.alloc_id),
        (Ty::Tuple { fields }, Val::Tuple(vals)) if fields.len() == vals.len() => {
            for (t, v) in fields.iter().zip(vals.iter()) {
                collect_ptr_or_ref_alloc_ids(t, v, out);
            }
        }
        (Ty::Option { elem }, Val::OptionVal(Some(inner))) => {
            collect_ptr_or_ref_alloc_ids(elem, inner, out);
        }
        _ => {}
    }
}

/// Whether any reference or raw pointer inside `(ty, val)` points into a
/// callee-allocated read-only `.rodata` allocation (in `mem` with shared
/// mutability, absent from `cm`), matching
/// `Trusted.MirSemantics.hasEscapingRodataPtr`.
pub fn has_escaping_rodata_ptr(cm: &CallerMemory, mem: &MemoryState, ty: &Ty, val: &Val) -> bool {
    let mut ids = Vec::new();
    collect_ptr_or_ref_alloc_ids(ty, val, &mut ids);
    ids.into_iter().any(|aid| {
        !cm.allocations.iter().any(|a| a.alloc_id == aid)
            && mem.find(aid).is_some_and(|a| a.mutability == Mutability::Shared)
    })
}

/// Check that every reference provenance `alloc_id` inside `(ty, val)` belongs
/// to `cm`, matching `Trusted.MirSemantics.refsStayInCallerMem`.
///
/// Distinguishes non-ZST escaping stack references (`StackRefEscaped`) from
/// zero-sized escaping stack references (`ZstStackRefEscape`, conservative).
pub fn refs_stay_in_caller_mem(cm: &CallerMemory, ty: &Ty, val: &Val) -> Result<(), UbClass> {
    match (ty, val) {
        (Ty::Ref { pointee, .. }, Val::SlicePtr { ptr, len }) => {
            if let Some(aid) = ptr.alloc_id
                && !cm.allocations.iter().any(|a| a.alloc_id == aid)
            {
                let elem_zero = matches!(pointee.as_ref(), Ty::Slice { elem } if layout_of_ty(elem, true).is_some_and(|l| l.size == 0));
                if *len == 0 || elem_zero {
                    return Err(UbClass::ZstStackRefEscape);
                }
                return Err(UbClass::StackRefEscaped);
            }
            Ok(())
        }
        (Ty::Ref { pointee, .. }, Val::Ptr(p)) => {
            if let Some(aid) = p.alloc_id
                && !cm.allocations.iter().any(|a| a.alloc_id == aid)
            {
                if layout_of_ty(pointee, true).is_some_and(|l| l.size == 0) {
                    return Err(UbClass::ZstStackRefEscape);
                }
                return Err(UbClass::StackRefEscaped);
            }
            Ok(())
        }
        (Ty::Tuple { fields }, Val::Tuple(vals)) => {
            for (t, v) in fields.iter().zip(vals.iter()) {
                refs_stay_in_caller_mem(cm, t, v)?;
            }
            Ok(())
        }
        (Ty::Option { elem }, Val::OptionVal(Some(inner))) => {
            refs_stay_in_caller_mem(cm, elem, inner)
        }
        _ => Ok(()),
    }
}
