// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Target layout, byte-level stack memory, and typed value byte codecs
//! aligned with `Trusted.MirSemantics.{Layout,Memory,Bytes}`.
//!
//! 1-aligned zero-sized memory accesses (`size == 0 && align_log2 == 0`,
//! covering all Profile v1 ZSTs) succeed without allocation lookup, matching
//! both `Trusted.MirSemantics.Memory` and `rustc`'s `get_place_alloc` /
//! `get_place_alloc_mut`. Over-aligned zero-sized accesses (`size == 0 &&
//! align_log2 > 0`) require a known allocation and valid alignment (using
//! `alloc.align_log2` even when `!alloc.live`).

use alloc::{vec, vec::Vec};

use serde::{Deserialize, Serialize};

use crate::{
    ir::{ConstLit, EnumTagRepr, IntWidth, Mutability, Ty},
    value::{
        AllocByte, FaultDetail, OrderingVal, ScalarVal, Val, check_val, enum_admitted,
        find_discr_variant, is_unicode_scalar, is_zst_enum_ty, tag_bits_to_discr_bits,
    },
};

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

/// Compute type layout matching `Trusted.MirSemantics.layoutOfTy`.
pub fn layout_of_ty(ty: &Ty, _enable_profile_v2: bool) -> Option<LayoutData> {
    if let Some(ity) = ty.as_overflow_pair() {
        return Some(overflow_pair_layout(ity.width));
    }
    match ty {
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
    }
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

/// Byte-level stack memory (`MemoryState`).
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

impl MemoryState {
    /// Empty memory starting with allocation id `1`.
    pub const fn empty() -> Self {
        Self { next_alloc_id: 1, allocations: Vec::new() }
    }

    /// Entry memory reserving allocation id `1` for the caller return place.
    pub const fn entry_memory() -> Self {
        Self { next_alloc_id: 2, allocations: Vec::new() }
    }

    fn reserve_alloc_id(&mut self) -> u64 {
        let id = self.next_alloc_id;
        self.next_alloc_id = self.next_alloc_id.saturating_add(1);
        id
    }

    fn find(&self, alloc_id: u64) -> Option<&Allocation> {
        self.allocations.iter().find(|a| a.alloc_id == alloc_id)
    }

    fn find_mut(&mut self, alloc_id: u64) -> Option<&mut Allocation> {
        self.allocations.iter_mut().find(|a| a.alloc_id == alloc_id)
    }

    /// Allocate a fresh mutable uninitialized stack object of `layout`.
    pub fn allocate_stack(&mut self, layout: LayoutData) -> MemPlace {
        let alloc_id = self.reserve_alloc_id();
        let size = usize::try_from(layout.size).expect("stack layout size fits host address space");
        self.allocations.push(Allocation {
            alloc_id,
            align_log2: layout.align_log2,
            mutability: Mutability::Mut,
            bytes: vec![AllocByte::Uninit; size],
            live: true,
        });
        MemPlace { alloc_id, offset: 0 }
    }

    /// Deallocate the stack allocation beginning at `place`.
    pub fn deallocate_stack(&mut self, place: MemPlace) -> Result<(), FaultDetail> {
        if place.offset != 0 {
            return Err(FaultDetail::undefined("deallocating non-zero offset within allocation"));
        }
        let Some(alloc) = self.find_mut(place.alloc_id) else {
            return Err(FaultDetail::undefined("deallocating missing allocation"));
        };
        if !alloc.live {
            return Err(FaultDetail::undefined("double free / use-after-free on stack allocation"));
        }
        if alloc.mutability != Mutability::Mut {
            return Err(FaultDetail::undefined("deallocating immutable allocation"));
        }
        alloc.live = false;
        Ok(())
    }

    fn is_in_bounds(alloc: &Allocation, offset: u64, size: u64) -> bool {
        offset.checked_add(size).is_some_and(|end| end <= alloc.bytes.len() as u64)
    }

    fn is_aligned(alloc: &Allocation, offset: u64, align_log2: u32) -> bool {
        if align_log2 > alloc.align_log2 {
            return false;
        }
        if align_log2 >= u64::BITS {
            return offset == 0;
        }
        let align = 1u64 << align_log2;
        offset.is_multiple_of(align)
    }

    /// Read `size` bytes from `place`.
    ///
    /// Matches `Trusted.MirSemantics.Memory` and `rustc`'s `get_place_alloc`:
    /// 1-aligned zero-sized reads (`size == 0 && align_log2 == 0`) succeed
    /// without looking up `place.alloc_id`; over-aligned zero-sized reads
    /// (`size == 0 && align_log2 > 0`) check allocation existence and alignment
    /// (using `alloc.align_log2` even when `!alloc.live`) without requiring
    /// liveness or bounds.
    pub fn read_bytes(
        &self,
        place: MemPlace,
        size: u64,
        align_log2: u32,
    ) -> Result<Vec<AllocByte>, FaultDetail> {
        if size == 0 && align_log2 == 0 {
            return Ok(Vec::new());
        }
        let Some(alloc) = self.find(place.alloc_id) else {
            return Err(FaultDetail::undefined("memory read from unknown allocation"));
        };
        if !Self::is_aligned(alloc, place.offset, align_log2) {
            return Err(FaultDetail::undefined("misaligned memory read"));
        }
        if size == 0 {
            return Ok(Vec::new());
        }
        if !alloc.live {
            return Err(FaultDetail::undefined("use-after-free memory read"));
        }
        if !Self::is_in_bounds(alloc, place.offset, size) {
            return Err(FaultDetail::undefined("out-of-bounds memory read"));
        }
        let start = usize::try_from(place.offset).expect("in-bounds offset fits usize");
        let len = usize::try_from(size).expect("in-bounds size fits usize");
        Ok(alloc.bytes[start..start + len].to_vec())
    }

    /// Overwrite `bytes` at `place`.
    ///
    /// Matches `Trusted.MirSemantics.Memory` and `rustc`'s
    /// `get_place_alloc_mut`: 1-aligned zero-sized writes (`bytes.is_empty()
    /// && align_log2 == 0`) succeed without looking up `place.alloc_id`;
    /// over-aligned zero-sized writes (`bytes.is_empty() && align_log2 > 0`)
    /// check allocation existence and alignment (using `alloc.align_log2` even
    /// when `!alloc.live`) without requiring liveness, bounds, or mutability.
    pub fn write_bytes(
        &mut self,
        place: MemPlace,
        align_log2: u32,
        bytes: &[AllocByte],
    ) -> Result<(), FaultDetail> {
        if bytes.is_empty() && align_log2 == 0 {
            return Ok(());
        }
        let Some(alloc) = self.find_mut(place.alloc_id) else {
            return Err(FaultDetail::undefined("memory write to unknown allocation"));
        };
        if !Self::is_aligned(alloc, place.offset, align_log2) {
            return Err(FaultDetail::undefined("misaligned memory write"));
        }
        if bytes.is_empty() {
            return Ok(());
        }
        if !alloc.live {
            return Err(FaultDetail::undefined("use-after-free memory write"));
        }
        if !Self::is_in_bounds(alloc, place.offset, bytes.len() as u64) {
            return Err(FaultDetail::undefined("out-of-bounds memory write"));
        }
        if alloc.mutability != Mutability::Mut {
            return Err(FaultDetail::undefined("write to immutable allocation"));
        }
        let start = usize::try_from(place.offset).expect("in-bounds offset fits usize");
        alloc.bytes[start..start + bytes.len()].copy_from_slice(bytes);
        Ok(())
    }

    /// Mark `size` bytes at `place` uninitialized (`size == 0` follows the same
    /// zero-sized lookup and alignment rule as `write_bytes`).
    pub fn write_uninit(
        &mut self,
        place: MemPlace,
        size: u64,
        align_log2: u32,
    ) -> Result<(), FaultDetail> {
        if size == 0 && align_log2 == 0 {
            return Ok(());
        }
        let Some(alloc) = self.find_mut(place.alloc_id) else {
            return Err(FaultDetail::undefined("memory write to unknown allocation"));
        };
        if !Self::is_aligned(alloc, place.offset, align_log2) {
            return Err(FaultDetail::undefined("misaligned memory write"));
        }
        if size == 0 {
            return Ok(());
        }
        if !alloc.live {
            return Err(FaultDetail::undefined("use-after-free memory write"));
        }
        if !Self::is_in_bounds(alloc, place.offset, size) {
            return Err(FaultDetail::undefined("out-of-bounds memory write"));
        }
        if alloc.mutability != Mutability::Mut {
            return Err(FaultDetail::undefined("write to immutable allocation"));
        }
        let start = usize::try_from(place.offset).expect("in-bounds offset fits usize");
        let len = usize::try_from(size).expect("in-bounds size fits usize");
        alloc.bytes[start..start + len].fill(AllocByte::Uninit);
        Ok(())
    }
}

/// Decode a typed constant literal matching `Trusted.MirSemantics.evalConstLit`.
pub fn eval_const_lit(ty: &Ty, lit: &ConstLit) -> Result<Val, FaultDetail> {
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
                Err(FaultDetail::undefined("invalid boolean bit pattern"))
            }
        }
        (Ty::Unit, ConstLit::ZeroSized) => Ok(Val::Unit),
        (Ty::Char, ConstLit::Scalar { bits }) => {
            if (*bits & 0xffff_ffff) != *bits {
                Err(FaultDetail::unsupported("char constant exceeds 32 bits"))
            } else if is_unicode_scalar(*bits) {
                let c = char::from_u32(*bits as u32)
                    .ok_or_else(|| FaultDetail::undefined("invalid char scalar"))?;
                Ok(Val::Char(c))
            } else {
                Err(FaultDetail::undefined("surrogate or out-of-range char scalar"))
            }
        }
        (Ty::Ordering, ConstLit::Scalar { bits }) => {
            if (*bits & 0xff) != *bits {
                Err(FaultDetail::unsupported("Ordering constant exceeds 8 bits"))
            } else {
                OrderingVal::from_tag_bits(*bits)
                    .map(Val::Ordering)
                    .ok_or_else(|| FaultDetail::undefined("invalid Ordering discriminant tag"))
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
                    .ok_or_else(|| FaultDetail::undefined("invalid fieldless enum tag"))
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

fn init_alloc_bytes(raw: Vec<u8>) -> Vec<AllocByte> {
    raw.into_iter().map(|byte| AllocByte::Init { byte, prov: None }).collect()
}

/// Encode runtime value `val` of type `ty` into bytes matching
/// `Trusted.MirSemantics.encodeVal`.
pub fn encode_val(
    endian: TargetEndian,
    ty: &Ty,
    val: &Val,
    enable_profile_v2: bool,
) -> Result<Vec<AllocByte>, FaultDetail> {
    if !check_val(val, ty, enable_profile_v2) {
        return Err(FaultDetail::unsupported("value does not match declared storage type"));
    }
    if let (Some(ity), Val::Tuple(fields)) = (ty.as_overflow_pair(), val)
        && fields.len() == 2
        && let (Val::Scalar(sv), Val::Bool(overflowed)) = (&fields[0], &fields[1])
    {
        let width_bytes = ity.width.byte_size();
        let mut out = init_alloc_bytes(encode_uint(endian, width_bytes, sv.bits));
        out.push(AllocByte::Init { byte: u8::from(*overflowed), prov: None });
        out.resize(out.len() + width_bytes - 1, AllocByte::Uninit);
        return Ok(out);
    }
    match (ty, val) {
        (Ty::Int(ity), Val::Scalar(sv)) => {
            Ok(init_alloc_bytes(encode_uint(endian, ity.width.byte_size(), sv.bits)))
        }
        (Ty::Bool, Val::Bool(b)) => Ok(vec![AllocByte::Init { byte: u8::from(*b), prov: None }]),
        (Ty::Char, Val::Char(c)) => {
            Ok(init_alloc_bytes(encode_uint(endian, 4, u128::from(u32::from(*c)))))
        }
        (Ty::Ordering, Val::Ordering(ord)) => {
            Ok(init_alloc_bytes(encode_uint(endian, 1, ord.tag_bits())))
        }
        (Ty::Unit, Val::Unit) => Ok(Vec::new()),
        (Ty::Enum(ety), Val::EnumVal { variant, .. }) => match ety.tag_repr {
            EnumTagRepr::ZeroSized => Ok(Vec::new()),
            EnumTagRepr::Scalar(tag) => {
                let Some(&disc) = ety.discriminants.get(*variant) else {
                    return Err(FaultDetail::unsupported("enum variant index out of bounds"));
                };
                Ok(init_alloc_bytes(encode_uint(endian, tag.width.byte_size(), disc)))
            }
        },
        _ => Err(FaultDetail::unsupported("cannot encode unsupported (ty, val) pair to bytes")),
    }
}

/// Decode `bytes` of type `ty` matching `Trusted.MirSemantics.decodeVal`.
pub fn decode_val(
    endian: TargetEndian,
    ty: &Ty,
    bytes: &[AllocByte],
    enable_profile_v2: bool,
) -> Result<Option<Val>, FaultDetail> {
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
        let int_val = eval_const_lit(
            &Ty::Int(ity),
            &ConstLit::Scalar { bits: decode_uint(endian, &int_raw) },
        )?;
        let bool_val =
            eval_const_lit(&Ty::Bool, &ConstLit::Scalar { bits: decode_uint(endian, &bool_raw) })?;
        return Ok(Some(Val::Tuple(vec![int_val, bool_val])));
    }
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("type has no layout"));
    };
    if (bytes.len() as u64) != layout.size {
        return Err(FaultDetail::unsupported("byte length differs from type layout"));
    }
    if layout.size == 0 {
        let val = eval_const_lit(ty, &ConstLit::ZeroSized)?;
        return Ok(Some(val));
    }
    let Some(raw) = init_bytes(bytes) else {
        return Ok(None);
    };
    let val = eval_const_lit(ty, &ConstLit::Scalar { bits: decode_uint(endian, &raw) })?;
    Ok(Some(val))
}

/// Load an indirect value from memory matching `Trusted.MirSemantics.loadIndirect`.
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
/// `Trusted.MirSemantics.storeIndirect`.
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

/// Mark bytes of `ty` at `place` uninitialized (`Trusted.MirSemantics.deinitIndirect`).
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
