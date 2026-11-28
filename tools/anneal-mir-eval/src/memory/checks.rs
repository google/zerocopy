// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pointer arithmetic and slice-reference checks over `MemoryState`, aligned
//! with `Trusted.MirSemantics.{ptrAddInMem, strSliceUtf8InMem,
//! sliceFromRawPartsCheck, sliceGetUncheckedCheck}`.

use alloc::vec::Vec;

use super::{ISIZE_MAX_BYTES, MemoryState, offset_is_aligned};
use crate::{
    ir::Mutability,
    value::{AllocByte, FaultDetail, PtrVal, UbClass, Val},
};

/// Whether every byte in `bytes` is initialized (`AllocByte::Init`).
pub fn is_slice_all_init(bytes: &[AllocByte]) -> bool {
    bytes.iter().all(|b| matches!(b, AllocByte::Init { .. }))
}

/// Checked Rust `pointer::add` in `mem`, matching
/// `Trusted.MirSemantics.ptrAddInMem`.
pub fn ptr_add_in_mem(
    mem: &MemoryState,
    elem_size: u64,
    ptr: PtrVal,
    count: u64,
) -> Result<PtrVal, FaultDetail> {
    let delta = u128::from(count) * u128::from(elem_size);
    if delta >= u128::from(ISIZE_MAX_BYTES) {
        return Err(FaultDetail::undefined_classified(
            UbClass::PtrOffsetOverflowOrOob,
            "pointer offset delta exceeds isize::MAX",
        ));
    }
    let delta_u64 = delta as u64;
    match ptr.alloc_id {
        None => {
            if delta_u64 == 0 {
                Ok(ptr)
            } else {
                Err(FaultDetail::undefined_classified(
                    UbClass::PtrOffsetOverflowOrOob,
                    "non-zero pointer offset on provenance-free pointer",
                ))
            }
        }
        Some(aid) => {
            let Some(alloc) = mem.find(aid) else {
                let class = if delta_u64 == 0 {
                    UbClass::ZeroOffsetDeadOrOobPtr
                } else {
                    UbClass::PtrOffsetOverflowOrOob
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "pointer offset into unknown allocation",
                ));
            };
            let end = u128::from(ptr.offset_bytes) + delta;
            if !alloc.live || end > alloc.bytes.len() as u128 {
                let class = if delta_u64 == 0 {
                    UbClass::ZeroOffsetDeadOrOobPtr
                } else {
                    UbClass::PtrOffsetOverflowOrOob
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "pointer offset out of bounds or on dead allocation",
                ));
            }
            Ok(PtrVal { offset_bytes: ptr.offset_bytes.wrapping_add(delta_u64), ..ptr })
        }
    }
}

/// Whether the already-validated `&str` slice `(ptr, len)` in `mem` holds
/// valid UTF-8, matching `Trusted.MirSemantics.strSliceUtf8InMem`.
///
/// This checks the bytes with `core::str::from_utf8`, so it also cross-checks
/// the Lean `validUtf8Bytes` state machine against the real `core` validator.
pub fn str_slice_utf8_in_mem(mem: &MemoryState, ptr: PtrVal, len: u64) -> bool {
    if len == 0 {
        return true;
    }
    let Some(aid) = ptr.alloc_id else {
        return false;
    };
    let Some(alloc) = mem.find(aid) else {
        return false;
    };
    let (Ok(start), Ok(n)) = (usize::try_from(ptr.offset_bytes), usize::try_from(len)) else {
        return false;
    };
    let Some(end) = start.checked_add(n) else {
        return false;
    };
    let Some(slice) = alloc.bytes.get(start..end) else {
        return false;
    };
    let mut raw = Vec::with_capacity(n);
    for b in slice {
        match b {
            AllocByte::Init { byte, .. } => raw.push(*byte),
            AllocByte::Uninit => return false,
        }
    }
    core::str::from_utf8(&raw).is_ok()
}

/// Validate slice-reference invariants for `&[uN]` / `&mut [uN]` in `mem`,
/// matching `Trusted.MirSemantics.sliceFromRawPartsCheck`.
pub fn slice_from_raw_parts_check(
    mem: &MemoryState,
    is_mut: bool,
    elem_size: u64,
    elem_align_log2: u32,
    ptr: PtrVal,
    len: u64,
) -> Result<Val, FaultDetail> {
    let total_bytes = u128::from(len) * u128::from(elem_size);
    if total_bytes >= u128::from(ISIZE_MAX_BYTES) {
        return Err(FaultDetail::undefined_classified(
            UbClass::InvalidReferenceProduced,
            "slice byte length exceeds isize::MAX",
        ));
    }
    let total_u64 = total_bytes as u64;
    match ptr.alloc_id {
        None => {
            if ptr.offset_bytes == 0 || total_u64 > 0 {
                return Err(FaultDetail::undefined_classified(
                    UbClass::InvalidReferenceProduced,
                    "null or non-empty provenance-free slice reference",
                ));
            }
            if !offset_is_aligned(ptr.offset_bytes, elem_align_log2) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::InvalidReferenceProduced,
                    "misaligned provenance-free empty slice reference",
                ));
            }
            Ok(Val::SlicePtr { ptr, len })
        }
        Some(aid) => {
            let Some(alloc) = mem.find(aid) else {
                let class = if total_u64 == 0 {
                    UbClass::ZstProvenanceDeadOrOob
                } else {
                    UbClass::InvalidReferenceProduced
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "slice reference points to unknown allocation",
                ));
            };
            if !alloc.live || !MemoryState::is_in_bounds(alloc, ptr.offset_bytes, total_u64) {
                let class = if total_u64 == 0 {
                    UbClass::ZstProvenanceDeadOrOob
                } else {
                    UbClass::InvalidReferenceProduced
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "slice reference is dangling or out of bounds",
                ));
            }
            if !MemoryState::is_aligned(alloc, ptr.offset_bytes, elem_align_log2) {
                let class = if elem_align_log2 > alloc.align_log2 {
                    UbClass::SymbolicAllocAlignment
                } else {
                    UbClass::InvalidReferenceProduced
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "slice reference is misaligned",
                ));
            }
            if is_mut && alloc.mutability != Mutability::Mut {
                let class = if total_u64 == 0 {
                    UbClass::ZstMutRefImmutableAlloc
                } else {
                    UbClass::InvalidReferenceProduced
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "mutable slice reference points to immutable allocation",
                ));
            }
            let start = usize::try_from(ptr.offset_bytes).expect("in-bounds offset fits usize");
            let byte_len = usize::try_from(total_u64).expect("in-bounds length fits usize");
            if !is_slice_all_init(&alloc.bytes[start..start + byte_len]) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::RefPointeeUninitOrInvalid,
                    "slice reference points to uninitialized bytes",
                ));
            }
            Ok(Val::SlicePtr { ptr, len })
        }
    }
}

/// Checked `slice::get_unchecked` subslice (`[start_off..end_off]` of
/// `(ptr, len)` with element byte size `elem_size`), matching
/// `Trusted.MirSemantics.sliceGetUncheckedCheck`.
pub fn slice_get_unchecked_check(
    mem: &MemoryState,
    ptr: PtrVal,
    len: u64,
    start_off: u64,
    end_off: u64,
    elem_size: u64,
) -> Result<Val, FaultDetail> {
    if start_off > end_off || end_off > len {
        return Err(FaultDetail::undefined_classified(
            UbClass::SliceGetUncheckedOutOfBounds,
            "slice::get_unchecked range exceeds slice bounds",
        ));
    }
    let advanced = ptr_add_in_mem(mem, elem_size, ptr, start_off)?;
    Ok(Val::SlicePtr { ptr: advanced, len: end_off - start_off })
}
