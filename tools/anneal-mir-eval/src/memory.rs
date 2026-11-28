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

mod checks;
mod codec;
mod refs;

use alloc::{collections::BTreeSet, vec, vec::Vec};

use serde::{Deserialize, Serialize};

pub use self::{
    checks::{
        is_slice_all_init, ptr_add_in_mem, slice_from_raw_parts_check, slice_get_unchecked_check,
        str_slice_utf8_in_mem,
    },
    codec::{
        decode_uint, decode_val, deinit_indirect, encode_uint, encode_val, eval_const_lit,
        load_indirect, read_ptr_prov, store_indirect,
    },
    refs::{
        RefAccessSpan, has_escaping_rodata_ptr, ref_access_spans, ref_access_spans_list,
        ref_valid_in_mem, refs_stay_in_caller_mem, refs_valid_in_mem, refs_valid_in_mem_list,
        spans_pairwise_disjoint,
    },
};
use crate::{
    ir::{EnumTagRepr, IntWidth, Mutability, Ty},
    value::{AllocByte, FaultDetail, UbClass, Val, enum_admitted},
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
