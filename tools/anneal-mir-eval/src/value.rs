// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Concrete runtime values, fault classifications, and MIR type predicates
//! matching `Trusted.MirModel` and `Trusted.MirSemantics.Enum`.

use alloc::{collections::BTreeSet, string::String, vec, vec::Vec};
use core::fmt;

use serde::{Deserialize, Serialize};

use crate::ir::{EnumTagRepr, EnumTy, IntTy, IntWidth, Ty};

/// Operational fault classification matching `Trusted.MirSemantics.FaultKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FaultKind {
    /// Modeled Rust Undefined Behavior.
    Undefined,
    /// Unmodeled MIR construct, type, invariant violation, or Profile v1 boundary.
    Unsupported,
}

impl fmt::Display for FaultKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undefined => f.write_str("undefined"),
            Self::Unsupported => f.write_str("unsupported"),
        }
    }
}

/// Fault outcome enriched with diagnostic explanation while keeping
/// [`FaultKind`] primary for semantic comparisons.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaultDetail {
    pub kind: FaultKind,
    pub reason: String,
}

impl FaultDetail {
    pub fn undefined(reason: impl Into<String>) -> Self {
        Self { kind: FaultKind::Undefined, reason: reason.into() }
    }

    pub fn unsupported(reason: impl Into<String>) -> Self {
        Self { kind: FaultKind::Unsupported, reason: reason.into() }
    }
}

impl fmt::Display for FaultDetail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.reason)
    }
}

/// Canonical scalar value with explicit width, signedness, and 128-bit payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ScalarVal {
    pub width: IntWidth,
    pub signed: bool,
    #[serde(
        serialize_with = "crate::ir::serialize_u128_decimal",
        deserialize_with = "crate::ir::deserialize_u128_decimal"
    )]
    pub bits: u128,
}

impl ScalarVal {
    /// Construct a scalar value truncating `bits` to `width`.
    pub const fn new(width: IntWidth, signed: bool, bits: u128) -> Self {
        Self { width, signed, bits: bits & width.mask() }
    }

    /// Construct a scalar value from raw bits without truncating (useful for
    /// negative `wf()` validation tests).
    pub const fn from_raw_untruncated(width: IntWidth, signed: bool, bits: u128) -> Self {
        Self { width, signed, bits }
    }

    /// Whether `bits` fits inside `width` bits (`ScalarVal.wf`).
    pub const fn wf(self) -> bool {
        (self.bits & self.width.mask()) == self.bits
    }

    /// Mask raw bits to `self.width`.
    pub const fn truncated_bits(self) -> u128 {
        self.bits & self.width.mask()
    }

    /// Sign-extended `i128` interpretation when `self.signed == true`.
    pub const fn to_signed_i128(self) -> i128 {
        let masked = self.truncated_bits();
        let shift = 128 - self.width.bits();
        ((masked << shift) as i128) >> shift
    }
}

/// Canonical pointer/reference value (`alloc_id` provenance + byte offset).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PtrVal {
    pub alloc_id: Option<u64>,
    pub offset_bytes: u64,
    pub width: IntWidth,
}

/// Abstract memory byte: uninitialized or initialized byte with optional
/// provenance allocation id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AllocByte {
    Uninit,
    Init { byte: u8, prov: Option<u64> },
}

/// Runtime value of `core::cmp::Ordering` matching `OrderingVal`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OrderingVal {
    Less,
    Equal,
    Greater,
}

impl OrderingVal {
    /// Canonical `#[repr(i8)]` tag bit pattern (`255`, `0`, `1`).
    pub const fn tag_bits(self) -> u128 {
        match self {
            Self::Less => 255,
            Self::Equal => 0,
            Self::Greater => 1,
        }
    }

    /// Decode an 8-bit `Ordering` tag pattern, or `None` on invalid tags.
    pub const fn from_tag_bits(bits: u128) -> Option<Self> {
        match bits {
            255 => Some(Self::Less),
            0 => Some(Self::Equal),
            1 => Some(Self::Greater),
            _ => None,
        }
    }
}

/// Canonical boundary and runtime value matching `Trusted.MirModel.Val`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum Val {
    Scalar(ScalarVal),
    Ptr(PtrVal),
    Bool(bool),
    Char(char),
    Ordering(OrderingVal),
    Unit,
    EnumVal { ty: EnumTy, variant: usize },
    Tuple(Vec<Val>),
    Bytes(Vec<AllocByte>),
}

impl Val {
    pub const fn u8(v: u8) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I8, false, v as u128))
    }

    pub const fn u16(v: u16) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I16, false, v as u128))
    }

    pub const fn u32(v: u32) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I32, false, v as u128))
    }

    pub const fn u64(v: u64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I64, false, v as u128))
    }

    pub const fn u128(v: u128) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I128, false, v))
    }

    pub const fn usize_val(v: u64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::Isize, false, v as u128))
    }

    pub const fn i8(v: i8) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I8, true, (v as i128) as u128))
    }

    pub const fn i16(v: i16) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I16, true, (v as i128) as u128))
    }

    pub const fn i32(v: i32) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I32, true, (v as i128) as u128))
    }

    pub const fn i64(v: i64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I64, true, (v as i128) as u128))
    }

    pub const fn i128(v: i128) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I128, true, v as u128))
    }

    pub const fn isize_val(v: i64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::Isize, true, (v as i128) as u128))
    }

    /// Construct an `(T, bool)` overflow pair runtime tuple.
    pub fn overflow_pair(sv: ScalarVal, overflowed: bool) -> Self {
        Self::Tuple(vec![Self::Scalar(sv), Self::Bool(overflowed)])
    }
}

/// Recover discriminant bits from raw tag bits following `rustc`'s
/// `TagEncoding::Direct` sign/zero-extension rule.
pub const fn tag_bits_to_discr_bits(tag: IntTy, discr_width: IntWidth, raw_tag: u128) -> u128 {
    let masked_tag = raw_tag & tag.width.mask();
    let extended = if tag.signed {
        let shift = 128 - tag.width.bits();
        (((masked_tag << shift) as i128) >> shift) as u128
    } else {
        masked_tag
    };
    extended & discr_width.mask()
}

/// Check `Trusted.MirSemantics.enumAdmitted` invariants on a fieldless enum
/// descriptor.
pub fn enum_admitted(ety: &EnumTy) -> bool {
    if ety.discriminants.is_empty() {
        return false;
    }
    if u64::try_from(ety.discriminants.len()).unwrap_or(u64::MAX) >= (1u64 << 32) {
        return false;
    }
    let discr_mask = ety.discr_width.mask();
    let mut seen = BTreeSet::new();
    for &d in &ety.discriminants {
        if d > discr_mask || !seen.insert(d) {
            return false;
        }
    }
    match ety.tag_repr {
        EnumTagRepr::ZeroSized => ety.discriminants.len() == 1,
        EnumTagRepr::Scalar(tag) => ety
            .discriminants
            .iter()
            .all(|&d| tag_bits_to_discr_bits(tag, ety.discr_width, d & tag.width.mask()) == d),
    }
}

/// Whether `ety` is an admitted 1-variant 0-byte ZST enum.
pub fn is_zst_enum_ty(ety: &EnumTy) -> bool {
    matches!(ety.tag_repr, EnumTagRepr::ZeroSized) && enum_admitted(ety)
}

/// Resolve a discriminant bit pattern to its 0-based declaration variant index.
pub fn find_discr_variant(discr_bits: u128, discriminants: &[u128]) -> Option<usize> {
    discriminants.iter().position(|&d| d == discr_bits)
}

/// Whether `bits` is a valid Unicode scalar value (`0x0000..=0xD7FF` or
/// `0xE000..=0x10FFFF`).
pub const fn is_unicode_scalar(bits: u128) -> bool {
    bits <= 0x10_FFFF && !(0xD800 <= bits && bits <= 0xDFFF)
}

/// Intrinsic well-formed Profile v1 type of a runtime [`Val`] (`Val.ty?`).
pub fn val_ty(val: &Val) -> Option<Ty> {
    match val {
        Val::Scalar(sv) => sv.wf().then_some(Ty::Int(IntTy { width: sv.width, signed: sv.signed })),
        Val::Bool(_) => Some(Ty::Bool),
        Val::Char(_) => Some(Ty::Char),
        Val::Ordering(_) => Some(Ty::Ordering),
        Val::Unit => Some(Ty::Unit),
        Val::EnumVal { ty, variant } => {
            (enum_admitted(ty) && *variant < ty.discriminants.len()).then(|| Ty::Enum(ty.clone()))
        }
        Val::Tuple(fields) if fields.len() == 2 => match (&fields[0], &fields[1]) {
            (Val::Scalar(sv), Val::Bool(_)) if sv.wf() => {
                Some(Ty::OverflowPair(IntTy { width: sv.width, signed: sv.signed }))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Check that runtime value `val` is a well-formed instance of `ty`.
pub fn check_val(val: &Val, ty: &Ty, enable_profile_v2: bool) -> bool {
    if let Some(inferred) = val_ty(val) {
        return inferred.structural_eq(ty);
    }
    if enable_profile_v2 {
        match (val, ty) {
            (Val::Tuple(vals), Ty::Tuple { fields }) if vals.len() == fields.len() => {
                vals.iter().zip(fields.iter()).all(|(v, elem_ty)| check_val(v, elem_ty, true))
            }
            (Val::Ptr(p), Ty::Ref { .. }) => p.width == IntWidth::Isize && p.alloc_id.is_some(),
            (Val::Ptr(p), Ty::RawPtr { .. }) => p.width == IntWidth::Isize,
            _ => false,
        }
    } else {
        false
    }
}

/// Check whether `args` matches `param_tys` pairwise under [`check_val`].
pub fn check_args_match(args: &[Val], param_tys: &[Ty], enable_profile_v2: bool) -> bool {
    args.len() == param_tys.len()
        && args.iter().zip(param_tys.iter()).all(|(v, ty)| check_val(v, ty, enable_profile_v2))
}

/// Whether `ty` is executable in locals under the selected profile.
pub fn is_supported_local_ty(ty: &Ty, enable_profile_v2: bool) -> bool {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Char | Ty::Ordering | Ty::Unit | Ty::Never => true,
        Ty::Enum(ety) => enum_admitted(ety),
        Ty::OverflowPair(_) => true,
        Ty::Tuple { fields } if ty.as_overflow_pair().is_some() => fields.len() == 2,
        Ty::Tuple { fields } if enable_profile_v2 => {
            fields.iter().all(|f| is_supported_local_ty(f, true))
        }
        Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } if enable_profile_v2 => {
            is_supported_local_ty(pointee, true)
        }
        _ => false,
    }
}

/// Whether `ty` is primitive-readable (`bool`, `int`, `char`, overflow pair).
/// Notice `Enum` and `Ordering` are NOT primitive-readable.
pub fn is_primitive_readable_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int(_) | Ty::Char) || ty.as_overflow_pair().is_some()
}

/// Whether `ty` is an integer-like source for `CastKind::IntToInt`.
pub fn is_int_like_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int(_) | Ty::Char)
}
