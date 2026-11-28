// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Target layout, byte-level stack/caller memory, typed value byte codecs, and
//! Profile v2 pointer/reference/slice checks aligned 1:1 with
//! `Trusted.MirSemantics.{Layout,Memory,Bytes}`.

use alloc::{collections::BTreeSet, vec, vec::Vec};

use serde::{Deserialize, Serialize};

use crate::{
    ir::{ConstLit, EnumTagRepr, IntWidth, Mutability, Ty},
    value::{
        AllocByte, FaultDetail, FaultKind, OrderingVal, PtrVal, ScalarVal, UbClass, Val, check_val,
        enum_admitted, find_discr_variant, is_unicode_scalar, is_zst_enum_ty,
        tag_bits_to_discr_bits,
    },
};

/// Upper bound `isize::MAX + 1` on a 64-bit target (`2^63` bytes), matching
/// `Trusted.MirSemantics.isizeMaxBytes`.
pub const ISIZE_MAX_BYTES: u64 = 1u64 << 63;

/// Multi-byte integer byte order matching `Trusted.MirSemantics.TargetEndian`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TargetEndian {
    Little,
    Big,
}

impl TargetEndian {
    /// Parse a manifest configuration endian string (`"little"` or `"big"`).
    pub fn from_manifest_str(s: &str) -> Option<Self> {
        match s {
            "little" => Some(Self::Little),
            "big" => Some(Self::Big),
            _ => None,
        }
    }
}

/// Size (bytes) and log2 ABI alignment of a sized type (`LayoutData`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LayoutData {
    pub size: u64,
    pub align_log2: u32,
}

/// Natural integer layout matching `Trusted.MirSemantics.intLayout`.
pub const fn int_layout(w: IntWidth) -> LayoutData {
    match w {
        IntWidth::I8 => LayoutData { size: 1, align_log2: 0 },
        IntWidth::I16 => LayoutData { size: 2, align_log2: 1 },
        IntWidth::I32 => LayoutData { size: 4, align_log2: 2 },
        IntWidth::I64 | IntWidth::Isize => LayoutData { size: 8, align_log2: 3 },
        IntWidth::I128 => LayoutData { size: 16, align_log2: 4 },
    }
}

/// Layout of `(T, bool)` overflow pairs matching `overflowPairLayout`.
pub const fn overflow_pair_layout(w: IntWidth) -> LayoutData {
    let base = int_layout(w);
    LayoutData { size: 2 * base.size, align_log2: base.align_log2 }
}

/// Compute type layout matching `Trusted.MirSemantics.layoutOfTy` (Profile v1)
/// and `Trusted.MirSemantics.layoutOfTyV2` (Profile v2).
pub fn layout_of_ty(ty: &Ty, enable_profile_v2: bool) -> Option<LayoutData> {
    if let Some(ity) = ty.as_overflow_pair() {
        return Some(overflow_pair_layout(ity.width));
    }
    let v1 = match ty {
        Ty::Bool | Ty::Ordering => Some(LayoutData { size: 1, align_log2: 0 }),
        Ty::Int(ity) => Some(int_layout(ity.width)),
        Ty::Char => Some(LayoutData { size: 4, align_log2: 2 }),
        Ty::Unit | Ty::Never => Some(LayoutData { size: 0, align_log2: 0 }),
        Ty::Enum(ety) => {
            if !enum_admitted(ety) {
                None
            } else {
                match ety.tag_repr {
                    EnumTagRepr::ZeroSized => Some(LayoutData { size: 0, align_log2: 0 }),
                    EnumTagRepr::Scalar(tag) => Some(int_layout(tag.width)),
                }
            }
        }
        _ => None,
    };
    if v1.is_some() || !enable_profile_v2 {
        return v1;
    }
    match ty {
        Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. } => {
            if pointee.is_unsized() {
                Some(LayoutData { size: 16, align_log2: 3 })
            } else {
                Some(LayoutData { size: 8, align_log2: 3 })
            }
        }
        Ty::RangeTo { elem } | Ty::RangeFrom { elem } if elem.is_usize() => {
            Some(LayoutData { size: 8, align_log2: 3 })
        }
        _ => None,
    }
}

/// Check whether `offset` is divisible by `2^align_log2`.
pub const fn offset_is_aligned(offset: u64, align_log2: u32) -> bool {
    if align_log2 >= u64::BITS { offset == 0 } else { offset.is_multiple_of(1u64 << align_log2) }
}

/// Byte place inside a memory allocation (`MemPlace`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MemPlace {
    pub alloc_id: u64,
    pub offset: u64,
}

/// Single stack or caller allocation (`Allocation`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Allocation {
    pub alloc_id: u64,
    pub align_log2: u32,
    pub mutability: Mutability,
    pub bytes: Vec<AllocByte>,
    pub live: bool,
}

/// Snapshot of caller-visible allocations (`CallerMemory`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallerMemory {
    pub allocations: Vec<Allocation>,
}

impl CallerMemory {
    /// Whether `self` contains zero caller allocations.
    pub fn is_empty(&self) -> bool {
        self.allocations.is_empty()
    }
}

/// Structural validity of caller-provided memory for Profile v2, matching
/// `Trusted.MirSemantics.validCallerMemory`: non-zero, `< u64::MAX`,
/// pairwise-distinct `alloc_id`s, each allocation `< isize::MAX + 1` bytes and
/// alignment `<= 2^29` (`Align::MAX`).
pub fn valid_caller_memory(cm: &CallerMemory) -> bool {
    let mut seen = BTreeSet::new();
    for alloc in &cm.allocations {
        if alloc.alloc_id == 0
            || alloc.alloc_id == u64::MAX
            || !seen.insert(alloc.alloc_id)
            || (alloc.bytes.len() as u64) >= ISIZE_MAX_BYTES
            || alloc.align_log2 > 29
        {
            return false;
        }
    }
    true
}

/// Byte-level stack and caller memory (`MemoryState`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryState {
    pub next_alloc_id: u64,
    pub allocations: Vec<Allocation>,
}

impl Default for MemoryState {
    fn default() -> Self {
        Self::entry_memory()
    }
}

fn max_val_ptr_alloc_id(v: &Val) -> u64 {
    match v {
        Val::Ptr(p) | Val::SlicePtr { ptr: p, .. } => p.alloc_id.unwrap_or(0),
        Val::Tuple(vs) => vs.iter().map(max_val_ptr_alloc_id).max().unwrap_or(0),
        Val::OptionVal(Some(inner)) => max_val_ptr_alloc_id(inner),
        Val::OptionVal(None) => 0,
        Val::Bytes(bs) => bs
            .iter()
            .filter_map(|b| match b {
                AllocByte::Init { prov: Some(pid), .. } => Some(*pid),
                AllocByte::Init { prov: None, .. } | AllocByte::Uninit => None,
            })
            .max()
            .unwrap_or(0),
        Val::Scalar(_)
        | Val::Bool(_)
        | Val::Char(_)
        | Val::Ordering(_)
        | Val::Unit
        | Val::EnumVal { .. }
        | Val::RangeTo(_)
        | Val::RangeFrom(_) => 0,
    }
}

impl MemoryState {
    /// Empty memory starting with allocation id `1`.
    pub const fn empty() -> Self {
        Self { next_alloc_id: 1, allocations: Vec::new() }
    }

    /// Entry memory reserving allocation id `1` for the caller return place.
    pub const fn entry_memory() -> Self {
        Self { next_alloc_id: 2, allocations: Vec::new() }
    }

    /// Profile v2 entry memory pre-populated with caller allocations,
    /// matching `Trusted.MirSemantics.entryMemoryWithCaller` (advancing
    /// `next_alloc_id` past both caller allocation ids and provenance ids
    /// stored inside caller bytes), failing closed if an id would overflow
    /// `next_alloc_id`.
    pub fn entry_memory_with_caller(cm: &CallerMemory) -> Result<Self, FaultDetail> {
        let max_alloc_id = cm.allocations.iter().map(|a| a.alloc_id).max().unwrap_or(0);
        let max_prov_id = cm
            .allocations
            .iter()
            .flat_map(|a| a.bytes.iter())
            .filter_map(|b| match b {
                AllocByte::Init { prov: Some(pid), .. } => Some(*pid),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        let max_id = max_alloc_id.max(max_prov_id);
        let next_from_caller = max_id.checked_add(1).ok_or_else(|| {
            FaultDetail::unsupported(
                "caller allocation or provenance id u64::MAX overflows next_alloc_id",
            )
        })?;
        let next_alloc_id = Self::entry_memory().next_alloc_id.max(next_from_caller);
        Ok(Self { next_alloc_id, allocations: cm.allocations.clone() })
    }

    /// Profile v2 entry memory for `(param_tys, args)`, matching
    /// `Trusted.MirSemantics.entryMemoryForArgsV2` by additionally advancing
    /// `next_alloc_id` past provenance ids carried in raw-pointer parameters.
    pub fn entry_memory_for_args_v2(
        cm: &CallerMemory,
        param_tys: &[Ty],
        args: &[Val],
    ) -> Result<Self, FaultDetail> {
        let mut base = Self::entry_memory_with_caller(cm)?;
        if param_tys.iter().any(Ty::has_raw_ptr_v2) {
            let max_arg_ptr = args.iter().map(max_val_ptr_alloc_id).max().unwrap_or(0);
            let next_from_args = max_arg_ptr.checked_add(1).ok_or_else(|| {
                FaultDetail::unsupported(
                    "raw pointer argument alloc_id u64::MAX overflows next_alloc_id",
                )
            })?;
            base.next_alloc_id = base.next_alloc_id.max(next_from_args);
        }
        Ok(base)
    }

    /// Snapshot caller-visible allocations in the original order of `orig`,
    /// matching `Trusted.MirSemantics.extractCallerMemory`.
    pub fn extract_caller_memory(&self, orig: &CallerMemory) -> CallerMemory {
        let allocations = orig
            .allocations
            .iter()
            .map(|a| self.find(a.alloc_id).cloned().unwrap_or_else(|| a.clone()))
            .collect();
        CallerMemory { allocations }
    }

    fn reserve_alloc_id(&mut self) -> Result<u64, FaultDetail> {
        let id = self.next_alloc_id;
        let next = self
            .next_alloc_id
            .checked_add(1)
            .ok_or_else(|| FaultDetail::unsupported("stack allocation id space exhausted"))?;
        self.next_alloc_id = next;
        Ok(id)
    }

    /// Look up an allocation by id (live or deallocated).
    pub fn find(&self, alloc_id: u64) -> Option<&Allocation> {
        self.allocations.iter().find(|a| a.alloc_id == alloc_id)
    }

    fn find_mut(&mut self, alloc_id: u64) -> Option<&mut Allocation> {
        self.allocations.iter_mut().find(|a| a.alloc_id == alloc_id)
    }

    /// Allocate a fresh live read-only allocation holding `bytes`, matching
    /// `Trusted.MirSemantics.allocRodataMemory`.
    pub fn try_allocate_rodata(
        &mut self,
        bytes: Vec<AllocByte>,
        align_log2: u32,
    ) -> Result<u64, FaultDetail> {
        let alloc_id = self.reserve_alloc_id()?;
        self.allocations.push(Allocation {
            alloc_id,
            align_log2,
            mutability: Mutability::Shared,
            bytes,
            live: true,
        });
        Ok(alloc_id)
    }

    /// Allocate a fresh mutable uninitialized stack object of `layout`,
    /// failing closed with [`FaultKind::Unsupported`] if the allocation id
    /// space is exhausted.
    pub fn try_allocate_stack(&mut self, layout: LayoutData) -> Result<MemPlace, FaultDetail> {
        let alloc_id = self.reserve_alloc_id()?;
        let size = usize::try_from(layout.size).map_err(|_| {
            FaultDetail::unsupported("stack layout size exceeds host address space")
        })?;
        self.allocations.push(Allocation {
            alloc_id,
            align_log2: layout.align_log2,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Uninit; size],
            live: true,
        });
        Ok(MemPlace { alloc_id, offset: 0 })
    }

    /// Allocate a fresh mutable uninitialized stack object of `layout`.
    pub fn allocate_stack(&mut self, layout: LayoutData) -> MemPlace {
        self.try_allocate_stack(layout).expect("stack allocation id and size fit host limits")
    }

    /// Deallocate the stack allocation beginning at `place`.
    pub fn deallocate_stack(&mut self, place: MemPlace) -> Result<(), FaultDetail> {
        if place.offset != 0 {
            return Err(FaultDetail::undefined_classified(
                UbClass::DanglingOrUnknownAllocAccess,
                "deallocating non-zero offset within allocation",
            ));
        }
        let Some(alloc) = self.find_mut(place.alloc_id) else {
            return Err(FaultDetail::undefined_classified(
                UbClass::DanglingOrUnknownAllocAccess,
                "deallocating missing allocation",
            ));
        };
        if !alloc.live {
            return Err(FaultDetail::undefined_classified(
                UbClass::DanglingOrUnknownAllocAccess,
                "double free / use-after-free on stack allocation",
            ));
        }
        if alloc.mutability != Mutability::Mut {
            return Err(FaultDetail::undefined_classified(
                UbClass::WriteToReadOnlyMemory,
                "deallocating immutable allocation",
            ));
        }
        alloc.live = false;
        Ok(())
    }

    /// Whether `[offset, offset + size)` lies within `alloc`.
    pub fn is_in_bounds(alloc: &Allocation, offset: u64, size: u64) -> bool {
        offset.checked_add(size).is_some_and(|end| end <= alloc.bytes.len() as u64)
    }

    /// Whether `offset` with alignment `2^align_log2` is aligned in `alloc`.
    pub fn is_aligned(alloc: &Allocation, offset: u64, align_log2: u32) -> bool {
        if align_log2 > alloc.align_log2 {
            return false;
        }
        offset_is_aligned(offset, align_log2)
    }

    /// Read `size` bytes from `place`, matching
    /// `Trusted.MirSemantics.readBytes`.
    ///
    /// Resolves `place.alloc_id` first (faulting with `Undefined` if unknown),
    /// then checks alignment even when `size == 0` (skipping liveness and
    /// bounds at `size == 0`).
    pub fn read_bytes(
        &self,
        place: MemPlace,
        size: u64,
        align_log2: u32,
    ) -> Result<Vec<AllocByte>, FaultDetail> {
        let Some(alloc) = self.find(place.alloc_id) else {
            let class = if size == 0 {
                UbClass::ZstProvenanceDeadOrOob
            } else {
                UbClass::DanglingOrUnknownAllocAccess
            };
            return Err(FaultDetail::undefined_classified(
                class,
                "memory read from unknown allocation",
            ));
        };
        if size == 0 {
            if !Self::is_aligned(alloc, place.offset, align_log2) {
                let class = if align_log2 > alloc.align_log2 {
                    UbClass::SymbolicAllocAlignment
                } else {
                    UbClass::MisalignedMemoryAccess
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "misaligned zero-sized memory read",
                ));
            }
            return Ok(Vec::new());
        }
        if !alloc.live {
            return Err(FaultDetail::undefined_classified(
                UbClass::DanglingOrUnknownAllocAccess,
                "use-after-free memory read",
            ));
        }
        if !Self::is_in_bounds(alloc, place.offset, size) {
            return Err(FaultDetail::undefined_classified(
                UbClass::OutOfBoundsMemoryAccess,
                "out-of-bounds memory read",
            ));
        }
        if !Self::is_aligned(alloc, place.offset, align_log2) {
            let class = if align_log2 > alloc.align_log2 {
                UbClass::SymbolicAllocAlignment
            } else {
                UbClass::MisalignedMemoryAccess
            };
            return Err(FaultDetail::undefined_classified(class, "misaligned memory read"));
        }
        let start = usize::try_from(place.offset).expect("in-bounds offset fits usize");
        let len = usize::try_from(size).expect("in-bounds size fits usize");
        Ok(alloc.bytes[start..start + len].to_vec())
    }

    /// Overwrite `bytes` at `place`, matching
    /// `Trusted.MirSemantics.writeBytes`.
    ///
    /// Resolves `place.alloc_id` first (faulting with `Undefined` if unknown),
    /// then checks alignment even when `bytes.is_empty()` (skipping liveness,
    /// bounds, and mutability at size 0).
    pub fn write_bytes(
        &mut self,
        place: MemPlace,
        align_log2: u32,
        bytes: &[AllocByte],
    ) -> Result<(), FaultDetail> {
        let Some(alloc) = self.find_mut(place.alloc_id) else {
            let class = if bytes.is_empty() {
                UbClass::ZstProvenanceDeadOrOob
            } else {
                UbClass::DanglingOrUnknownAllocAccess
            };
            return Err(FaultDetail::undefined_classified(
                class,
                "memory write to unknown allocation",
            ));
        };
        if bytes.is_empty() {
            if !Self::is_aligned(alloc, place.offset, align_log2) {
                let class = if align_log2 > alloc.align_log2 {
                    UbClass::SymbolicAllocAlignment
                } else {
                    UbClass::MisalignedMemoryAccess
                };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "misaligned zero-sized memory write",
                ));
            }
            return Ok(());
        }
        if !alloc.live {
            return Err(FaultDetail::undefined_classified(
                UbClass::DanglingOrUnknownAllocAccess,
                "use-after-free memory write",
            ));
        }
        if !Self::is_in_bounds(alloc, place.offset, bytes.len() as u64) {
            return Err(FaultDetail::undefined_classified(
                UbClass::OutOfBoundsMemoryAccess,
                "out-of-bounds memory write",
            ));
        }
        if !Self::is_aligned(alloc, place.offset, align_log2) {
            let class = if align_log2 > alloc.align_log2 {
                UbClass::SymbolicAllocAlignment
            } else {
                UbClass::MisalignedMemoryAccess
            };
            return Err(FaultDetail::undefined_classified(class, "misaligned memory write"));
        }
        if alloc.mutability != Mutability::Mut {
            return Err(FaultDetail::undefined_classified(
                UbClass::WriteToReadOnlyMemory,
                "write to immutable allocation",
            ));
        }
        let start = usize::try_from(place.offset).expect("in-bounds offset fits usize");
        alloc.bytes[start..start + bytes.len()].copy_from_slice(bytes);
        Ok(())
    }

    /// Mark `size` bytes at `place` uninitialized, matching
    /// `Trusted.MirSemantics.writeUninit`.
    pub fn write_uninit(
        &mut self,
        place: MemPlace,
        size: u64,
        align_log2: u32,
    ) -> Result<(), FaultDetail> {
        let len = usize::try_from(size).expect("size fits host address space");
        let uninit = vec![AllocByte::Uninit; len];
        self.write_bytes(place, align_log2, &uninit)
    }
}

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

/// Decode a typed constant literal matching `Trusted.MirSemantics.evalConstLit`.
pub fn eval_const_lit(ty: &Ty, lit: &ConstLit) -> Result<Val, FaultDetail> {
    eval_const_lit_with_class(ty, lit, UbClass::SyntheticInvalidConstOrSwitch)
}

fn eval_const_lit_with_class(
    ty: &Ty,
    lit: &ConstLit,
    invalid_val_class: UbClass,
) -> Result<Val, FaultDetail> {
    match (ty, lit) {
        (Ty::Int(ity), ConstLit::Scalar { bits }) => {
            if (*bits & ity.width.mask()) != *bits {
                Err(FaultDetail::unsupported("scalar constant exceeds declared width"))
            } else {
                Ok(Val::Scalar(ScalarVal::new(ity.width, ity.signed, *bits)))
            }
        }
        (Ty::Bool, ConstLit::Scalar { bits }) => {
            if (*bits & 0xff) != *bits {
                Err(FaultDetail::unsupported("bool constant exceeds 8-bit scalar"))
            } else if *bits == 0 {
                Ok(Val::Bool(false))
            } else if *bits == 1 {
                Ok(Val::Bool(true))
            } else {
                Err(FaultDetail::undefined_classified(
                    invalid_val_class,
                    "invalid boolean bit pattern",
                ))
            }
        }
        (Ty::Unit, ConstLit::ZeroSized) => Ok(Val::Unit),
        (Ty::Char, ConstLit::Scalar { bits }) => {
            if (*bits & 0xffff_ffff) != *bits {
                Err(FaultDetail::unsupported("char constant exceeds 32 bits"))
            } else if is_unicode_scalar(*bits) {
                let c = char::from_u32(*bits as u32).ok_or_else(|| {
                    FaultDetail::undefined_classified(invalid_val_class, "invalid char scalar")
                })?;
                Ok(Val::Char(c))
            } else {
                Err(FaultDetail::undefined_classified(
                    invalid_val_class,
                    "surrogate or out-of-range char scalar",
                ))
            }
        }
        (Ty::Ordering, ConstLit::Scalar { bits }) => {
            if (*bits & 0xff) != *bits {
                Err(FaultDetail::unsupported("Ordering constant exceeds 8 bits"))
            } else {
                OrderingVal::from_tag_bits(*bits).map(Val::Ordering).ok_or_else(|| {
                    FaultDetail::undefined_classified(
                        invalid_val_class,
                        "invalid Ordering discriminant tag",
                    )
                })
            }
        }
        (Ty::Enum(ety), ConstLit::ZeroSized) => {
            if is_zst_enum_ty(ety) {
                Ok(Val::EnumVal { ty: ety.clone(), variant: 0 })
            } else {
                Err(FaultDetail::unsupported("ZeroSized constant on non-ZST or unadmitted enum"))
            }
        }
        (Ty::Enum(ety), ConstLit::Scalar { bits }) => match ety.tag_repr {
            EnumTagRepr::ZeroSized => {
                Err(FaultDetail::unsupported("scalar constant for zero-sized enum"))
            }
            EnumTagRepr::Scalar(tag) => {
                if !enum_admitted(ety) || (*bits & tag.width.mask()) != *bits {
                    return Err(FaultDetail::unsupported(
                        "unadmitted enum or constant exceeding tag width",
                    ));
                }
                let discr_bits = tag_bits_to_discr_bits(tag, ety.discr_width, *bits);
                find_discr_variant(discr_bits, &ety.discriminants)
                    .map(|variant| Val::EnumVal { ty: ety.clone(), variant })
                    .ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            invalid_val_class,
                            "invalid fieldless enum tag",
                        )
                    })
            }
        },
        _ => Err(FaultDetail::unsupported("unsupported constant type/literal combination")),
    }
}

/// Encode the low `n` bytes (`<= 16`) of `value` in byte order `endian`.
pub fn encode_uint(endian: TargetEndian, n: usize, value: u128) -> Vec<u8> {
    let le = value.to_le_bytes();
    let mut out: Vec<u8> = (0..n).map(|i| *le.get(i).unwrap_or(&0)).collect();
    if endian == TargetEndian::Big {
        out.reverse();
    }
    out
}

/// Decode up to 16 bytes in byte order `endian` into an unsigned `u128`.
pub fn decode_uint(endian: TargetEndian, bytes: &[u8]) -> u128 {
    let mut acc = 0u128;
    match endian {
        TargetEndian::Little => {
            for (idx, &b) in bytes.iter().enumerate() {
                if idx < 16 {
                    acc |= u128::from(b) << (idx * 8);
                }
            }
        }
        TargetEndian::Big => {
            for &b in bytes {
                acc = (acc << 8) | u128::from(b);
            }
        }
    }
    acc
}

fn init_bytes(bytes: &[AllocByte]) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(bytes.len());
    for byte in bytes {
        match byte {
            AllocByte::Uninit => return None,
            AllocByte::Init { byte, .. } => out.push(*byte),
        }
    }
    Some(out)
}

fn init_alloc_bytes(raw: Vec<u8>, prov: Option<u64>) -> Vec<AllocByte> {
    raw.into_iter().map(|byte| AllocByte::Init { byte, prov }).collect()
}

/// Check initialization and extract uniform provenance across `bytes`,
/// matching `Trusted.MirSemantics.readPtrProv?`.
pub fn read_ptr_prov(bytes: &[AllocByte]) -> Option<Option<u64>> {
    let (first, rest) = bytes.split_first()?;
    let AllocByte::Init { prov: mut cur, .. } = *first else {
        return None;
    };
    for byte in rest {
        let AllocByte::Init { prov, .. } = *byte else {
            return None;
        };
        cur = match (cur, prov) {
            (Some(a), Some(b)) if a == b => Some(a),
            _ => None,
        };
    }
    Some(cur)
}

/// Encode runtime value `val` of type `ty` into bytes matching
/// `Trusted.MirSemantics`'s `encodeVal` (v1) and `encodeValV2` (v2).
pub fn encode_val(
    endian: TargetEndian,
    ty: &Ty,
    val: &Val,
    enable_profile_v2: bool,
) -> Result<Vec<AllocByte>, FaultDetail> {
    if !check_val(val, ty, enable_profile_v2) {
        return Err(FaultDetail::unsupported("value does not match declared storage type"));
    }
    if enable_profile_v2 {
        match (ty, val) {
            (Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. }, Val::Ptr(p)) => {
                if pointee.is_unsized() {
                    return Err(FaultDetail::unsupported(
                        "cannot encode thin pointer for unsized pointee",
                    ));
                }
                return Ok(init_alloc_bytes(
                    encode_uint(endian, 8, u128::from(p.offset_bytes)),
                    p.alloc_id,
                ));
            }
            (Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. }, Val::SlicePtr { ptr, len })
                if matches!(pointee.as_ref(), Ty::Slice { .. }) || is_shared_str_ref(ty) =>
            {
                let mut out = init_alloc_bytes(
                    encode_uint(endian, 8, u128::from(ptr.offset_bytes)),
                    ptr.alloc_id,
                );
                out.extend(init_alloc_bytes(encode_uint(endian, 8, u128::from(*len)), None));
                return Ok(out);
            }
            (Ty::RangeTo { elem }, Val::RangeTo(bound))
            | (Ty::RangeFrom { elem }, Val::RangeFrom(bound))
                if elem.is_usize() =>
            {
                return Ok(init_alloc_bytes(encode_uint(endian, 8, u128::from(*bound)), None));
            }
            _ => {}
        }
    }
    if let (Some(ity), Val::Tuple(fields)) = (ty.as_overflow_pair(), val)
        && fields.len() == 2
        && let (Val::Scalar(sv), Val::Bool(overflowed)) = (&fields[0], &fields[1])
    {
        let width_bytes = ity.width.byte_size();
        let mut out = init_alloc_bytes(encode_uint(endian, width_bytes, sv.bits), None);
        out.push(AllocByte::Init { byte: u8::from(*overflowed), prov: None });
        out.resize(out.len() + width_bytes - 1, AllocByte::Uninit);
        return Ok(out);
    }
    match (ty, val) {
        (Ty::Int(ity), Val::Scalar(sv)) => {
            Ok(init_alloc_bytes(encode_uint(endian, ity.width.byte_size(), sv.bits), None))
        }
        (Ty::Bool, Val::Bool(b)) => Ok(vec![AllocByte::Init { byte: u8::from(*b), prov: None }]),
        (Ty::Char, Val::Char(c)) => {
            Ok(init_alloc_bytes(encode_uint(endian, 4, u128::from(u32::from(*c))), None))
        }
        (Ty::Ordering, Val::Ordering(ord)) => {
            Ok(init_alloc_bytes(encode_uint(endian, 1, ord.tag_bits()), None))
        }
        (Ty::Unit, Val::Unit) => Ok(Vec::new()),
        (Ty::Enum(ety), Val::EnumVal { variant, .. }) => match ety.tag_repr {
            EnumTagRepr::ZeroSized => Ok(Vec::new()),
            EnumTagRepr::Scalar(tag) => {
                let Some(&disc) = ety.discriminants.get(*variant) else {
                    return Err(FaultDetail::unsupported("enum variant index out of bounds"));
                };
                Ok(init_alloc_bytes(encode_uint(endian, tag.width.byte_size(), disc), None))
            }
        },
        _ => Err(FaultDetail::unsupported("cannot encode unsupported (ty, val) pair to bytes")),
    }
}

/// Decode `bytes` of type `ty` matching `Trusted.MirSemantics.decodeVal`
/// (Profile v1) and `decodeValV2` (Profile v2).
pub fn decode_val(
    endian: TargetEndian,
    ty: &Ty,
    bytes: &[AllocByte],
    enable_profile_v2: bool,
) -> Result<Option<Val>, FaultDetail> {
    if enable_profile_v2 {
        match ty {
            Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. } => {
                if pointee.is_unsized() {
                    if !matches!(pointee.as_ref(), Ty::Slice { .. }) && !is_shared_str_ref(ty) {
                        return Err(FaultDetail::unsupported(
                            "unsupported unsized pointer pointee",
                        ));
                    }
                    if bytes.len() != 16 {
                        return Err(FaultDetail::unsupported(
                            "wide slice pointer byte length mismatch",
                        ));
                    }
                    let (p_bytes, l_bytes) = bytes.split_at(8);
                    return match (init_bytes(p_bytes), read_ptr_prov(p_bytes), init_bytes(l_bytes))
                    {
                        (Some(p_raw), Some(prov), Some(l_raw)) => {
                            let ptr = PtrVal {
                                alloc_id: prov,
                                offset_bytes: decode_uint(endian, &p_raw) as u64,
                                width: IntWidth::Isize,
                            };
                            let len = decode_uint(endian, &l_raw) as u64;
                            Ok(Some(Val::SlicePtr { ptr, len }))
                        }
                        _ => Ok(None),
                    };
                }
                if bytes.len() != 8 {
                    return Err(FaultDetail::unsupported("thin pointer byte length mismatch"));
                }
                return match (init_bytes(bytes), read_ptr_prov(bytes)) {
                    (Some(p_raw), Some(prov)) => Ok(Some(Val::Ptr(PtrVal {
                        alloc_id: prov,
                        offset_bytes: decode_uint(endian, &p_raw) as u64,
                        width: IntWidth::Isize,
                    }))),
                    _ => Ok(None),
                };
            }
            Ty::RangeTo { elem } if elem.is_usize() => {
                if bytes.len() != 8 {
                    return Err(FaultDetail::unsupported("RangeTo byte length mismatch"));
                }
                return Ok(
                    init_bytes(bytes).map(|raw| Val::RangeTo(decode_uint(endian, &raw) as u64))
                );
            }
            Ty::RangeFrom { elem } if elem.is_usize() => {
                if bytes.len() != 8 {
                    return Err(FaultDetail::unsupported("RangeFrom byte length mismatch"));
                }
                return Ok(
                    init_bytes(bytes).map(|raw| Val::RangeFrom(decode_uint(endian, &raw) as u64))
                );
            }
            _ => {}
        }
    }
    if matches!(ty, Ty::Never) {
        return Ok(None);
    }
    if let Some(ity) = ty.as_overflow_pair() {
        let pair_layout = overflow_pair_layout(ity.width);
        if (bytes.len() as u64) != pair_layout.size {
            return Err(FaultDetail::unsupported("overflow pair byte length mismatch"));
        }
        let width_bytes = ity.width.byte_size();
        let (Some(int_raw), Some(bool_raw)) =
            (init_bytes(&bytes[..width_bytes]), init_bytes(&bytes[width_bytes..width_bytes + 1]))
        else {
            return Ok(None);
        };
        let int_val = eval_const_lit_with_class(
            &Ty::Int(ity),
            &ConstLit::Scalar { bits: decode_uint(endian, &int_raw) },
            UbClass::InvalidMemoryValue,
        )?;
        let bool_val = eval_const_lit_with_class(
            &Ty::Bool,
            &ConstLit::Scalar { bits: decode_uint(endian, &bool_raw) },
            UbClass::InvalidMemoryValue,
        )?;
        return Ok(Some(Val::Tuple(vec![int_val, bool_val])));
    }
    let Some(layout) = layout_of_ty(ty, false) else {
        return Err(FaultDetail::unsupported("type has no layout"));
    };
    if (bytes.len() as u64) != layout.size {
        return Err(FaultDetail::unsupported("byte length differs from type layout"));
    }
    if layout.size == 0 {
        let val = eval_const_lit_with_class(ty, &ConstLit::ZeroSized, UbClass::InvalidMemoryValue)?;
        return Ok(Some(val));
    }
    let Some(raw) = init_bytes(bytes) else {
        return Ok(None);
    };
    let val = eval_const_lit_with_class(
        ty,
        &ConstLit::Scalar { bits: decode_uint(endian, &raw) },
        UbClass::InvalidMemoryValue,
    )?;
    Ok(Some(val))
}

/// Load an indirect value from memory matching
/// `Trusted.MirSemantics.loadIndirect` (Profile v1) and `loadIndirectV2`
/// (Profile v2).
pub fn load_indirect(
    mem: &MemoryState,
    endian: TargetEndian,
    ty: &Ty,
    place: MemPlace,
    enable_profile_v2: bool,
) -> Result<Option<Val>, FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("cannot load indirect local without layout"));
    };
    let bytes = mem.read_bytes(place, layout.size, layout.align_log2)?;
    decode_val(endian, ty, &bytes, enable_profile_v2)
}

/// Store `val` of type `ty` into an indirect memory place matching
/// `Trusted.MirSemantics.storeIndirect` / `storeIndirectV2`.
pub fn store_indirect(
    mem: &mut MemoryState,
    endian: TargetEndian,
    ty: &Ty,
    place: MemPlace,
    val: &Val,
    enable_profile_v2: bool,
) -> Result<(), FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("cannot store indirect local without layout"));
    };
    let bytes = encode_val(endian, ty, val, enable_profile_v2)?;
    mem.write_bytes(place, layout.align_log2, &bytes)
}

/// Mark bytes of `ty` at `place` uninitialized (`deinitIndirect` /
/// `deinitIndirectV2`).
pub fn deinit_indirect(
    mem: &mut MemoryState,
    ty: &Ty,
    place: MemPlace,
    enable_profile_v2: bool,
) -> Result<(), FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("cannot deinitialize indirect local without layout"));
    };
    mem.write_uninit(place, layout.size, layout.align_log2)
}

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
fn is_shared_str_ref(ty: &Ty) -> bool {
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
