// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture JSON IR schema types and decoders mirroring
//! `anneal-rustc-capture` schema version 5 (Profile v1 and Profile v2).

use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    format,
    string::{String, ToString},
    vec::Vec,
};
use core::fmt;

use serde::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{self, MapAccess, SeqAccess, Visitor},
    ser::{SerializeMap, SerializeSeq},
};

/// Capture JSON schema version produced by `anneal-rustc-capture`.
pub const CAPTURE_SCHEMA_VERSION: u32 = 5;

const fn default_pointer_width_bits() -> u64 {
    64
}

const fn default_has_local_panic_handler() -> bool {
    true
}

const fn default_mir_profile_version() -> u32 {
    1
}

/// Deserialize a `u128` encoded either as a canonical base-10 string or as a
/// JSON unsigned integer literal.
pub(crate) fn deserialize_u128_decimal<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<u128, D::Error> {
    struct U128Visitor;

    impl<'de> Visitor<'de> for U128Visitor {
        type Value = u128;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a base-10 integer string or unsigned integer fitting in u128")
        }

        fn visit_u64<E: de::Error>(self, value: u64) -> Result<u128, E> {
            Ok(u128::from(value))
        }

        fn visit_u128<E: de::Error>(self, value: u128) -> Result<u128, E> {
            Ok(value)
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<u128, E> {
            value.parse::<u128>().map_err(|_| E::custom("invalid base-10 u128 string"))
        }
    }

    deserializer.deserialize_any(U128Visitor)
}

fn serialize_u128_slice_decimal<S: Serializer>(
    vals: &[u128],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut seq = serializer.serialize_seq(Some(vals.len()))?;
    for val in vals {
        seq.serialize_element(&val.to_string())?;
    }
    seq.end()
}

fn deserialize_u128_vec_decimal<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<u128>, D::Error> {
    struct U128VecVisitor;

    impl<'de> Visitor<'de> for U128VecVisitor {
        type Value = Vec<u128>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a sequence of base-10 u128 strings or unsigned integers")
        }

        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Vec<u128>, A::Error> {
            #[derive(Deserialize)]
            struct DecimalU128(#[serde(deserialize_with = "deserialize_u128_decimal")] u128);

            let mut out = Vec::with_capacity(seq.size_hint().unwrap_or(0));
            while let Some(elem) = seq.next_element::<DecimalU128>()? {
                out.push(elem.0);
            }
            Ok(out)
        }
    }

    deserializer.deserialize_seq(U128VecVisitor)
}

pub(crate) fn serialize_u128_decimal<S: Serializer>(
    val: &u128,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&val.to_string())
}

fn serialize_switch_targets_decimal<S: Serializer>(
    targets: &[(u128, u32)],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut seq = serializer.serialize_seq(Some(targets.len()))?;
    for (val, block) in targets {
        seq.serialize_element(&(val.to_string(), *block))?;
    }
    seq.end()
}

fn deserialize_switch_targets_decimal<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<(u128, u32)>, D::Error> {
    struct SwitchTargetsVisitor;

    impl<'de> Visitor<'de> for SwitchTargetsVisitor {
        type Value = Vec<(u128, u32)>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a sequence of (decimal u128, block id) pairs")
        }

        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Vec<(u128, u32)>, A::Error> {
            #[derive(Deserialize)]
            struct Pair(#[serde(deserialize_with = "deserialize_u128_decimal")] u128, u32);

            let mut out = Vec::with_capacity(seq.size_hint().unwrap_or(0));
            while let Some(Pair(val, block)) = seq.next_element()? {
                out.push((val, block));
            }
            Ok(out)
        }
    }

    deserializer.deserialize_seq(SwitchTargetsVisitor)
}

/// Admitted integer widths matching `Trusted.MirAst.IntWidth`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum IntWidth {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

impl IntWidth {
    /// Width in bytes (`1`, `2`, `4`, `8`, or `16`).
    pub const fn byte_size(self) -> usize {
        match self {
            Self::I8 => 1,
            Self::I16 => 2,
            Self::I32 => 4,
            Self::I64 | Self::Isize => 8,
            Self::I128 => 16,
        }
    }

    /// Width in bits (`8`, `16`, `32`, `64`, or `128`).
    pub const fn bits(self) -> u32 {
        (self.byte_size() as u32) * 8
    }

    /// Low `self.bits()` mask inside `u128`.
    pub const fn mask(self) -> u128 {
        let bits = self.bits();
        if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 }
    }

    /// Canonical Rust integer type name.
    pub const fn rust_name(self, signed: bool) -> &'static str {
        match (self, signed) {
            (Self::I8, true) => "i8",
            (Self::I8, false) => "u8",
            (Self::I16, true) => "i16",
            (Self::I16, false) => "u16",
            (Self::I32, true) => "i32",
            (Self::I32, false) => "u32",
            (Self::I64, true) => "i64",
            (Self::I64, false) => "u64",
            (Self::I128, true) => "i128",
            (Self::I128, false) => "u128",
            (Self::Isize, true) => "isize",
            (Self::Isize, false) => "usize",
        }
    }
}

/// Integer type descriptor `(width, signed)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct IntTy {
    pub width: IntWidth,
    pub signed: bool,
}

/// Mutability qualifier for references, raw pointers, and memory allocations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Mutability {
    #[serde(alias = "not")]
    Shared,
    Mut,
}

/// In-memory tag representation of a fieldless Rust enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EnumTagRepr {
    ZeroSized,
    Scalar(IntTy),
}

/// Fieldless enum descriptor mirroring `Trusted.MirAst.EnumTy`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnumTy {
    pub id: u32,
    pub discr_width: IntWidth,
    pub discr_signed: bool,
    pub tag_repr: EnumTagRepr,
    #[serde(
        serialize_with = "serialize_u128_slice_decimal",
        deserialize_with = "deserialize_u128_vec_decimal"
    )]
    pub discriminants: Vec<u128>,
}

impl EnumTy {
    /// Discriminant integer type.
    pub const fn discr(&self) -> IntTy {
        IntTy { width: self.discr_width, signed: self.discr_signed }
    }
}

/// MIR local and constant types matching schema v5 (Profile v1 and v2).
/// `Str` is `str`, the unsized pointee of shared `&str`
/// (`Trusted.MirAst.MirTy.str`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Ty {
    Bool,
    Char,
    Ordering,
    Unit,
    Never,
    Int(IntTy),
    Enum(EnumTy),
    OverflowPair(IntTy),
    Tuple {
        fields: Vec<Ty>,
    },
    Ref {
        mutability: Mutability,
        pointee: Box<Ty>,
    },
    RawPtr {
        mutability: Mutability,
        pointee: Box<Ty>,
    },
    Slice {
        elem: Box<Ty>,
    },
    Str,
    RangeTo {
        elem: Box<Ty>,
    },
    RangeFrom {
        elem: Box<Ty>,
    },
    /// `core::ops::Range<T>`; captured, but not yet evaluated.
    Range {
        elem: Box<Ty>,
    },
    /// `core::option::Option<T>` (`Trusted.MirAst.MirTy.option`).
    Option {
        elem: Box<Ty>,
    },
    Array {
        elem: Box<Ty>,
        len: u64,
    },
    Unsupported,
}

impl Ty {
    /// Returns the inner integer type when `self` represents an `(T, bool)`
    /// overflow pair (either `OverflowPair(ity)` or normalized
    /// `Tuple { fields: [Int(ity), Bool] }`).
    pub fn as_overflow_pair(&self) -> Option<IntTy> {
        match self {
            Self::OverflowPair(ity) => Some(*ity),
            Self::Tuple { fields } if fields.len() == 2 && fields[1] == Self::Bool => {
                match fields[0] {
                    Self::Int(ity) => Some(ity),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Whether `self` is the target `usize` integer type.
    pub const fn is_usize(&self) -> bool {
        matches!(self, Self::Int(IntTy { width: IntWidth::Isize, signed: false }))
    }

    /// Whether `self` is an unsized dynamically-sized type (`[T]` or `str`),
    /// matching `Trusted.MirAst.isUnsizedTy`.
    pub const fn is_unsized(&self) -> bool {
        matches!(self, Self::Slice { .. } | Self::Str)
    }

    /// Structural equality normalizing `OverflowPair(ity)` and
    /// `Tuple { fields: [Int(ity), Bool] }`.
    pub fn structural_eq(&self, other: &Self) -> bool {
        if let (Some(a), Some(b)) = (self.as_overflow_pair(), other.as_overflow_pair()) {
            return a == b;
        }
        match (self, other) {
            (Self::Tuple { fields: fs_a }, Self::Tuple { fields: fs_b }) => {
                fs_a.len() == fs_b.len()
                    && fs_a.iter().zip(fs_b.iter()).all(|(a, b)| a.structural_eq(b))
            }
            (
                Self::Ref { mutability: m_a, pointee: p_a },
                Self::Ref { mutability: m_b, pointee: p_b },
            )
            | (
                Self::RawPtr { mutability: m_a, pointee: p_a },
                Self::RawPtr { mutability: m_b, pointee: p_b },
            ) => m_a == m_b && p_a.structural_eq(p_b),
            (Self::Slice { elem: e_a }, Self::Slice { elem: e_b })
            | (Self::RangeTo { elem: e_a }, Self::RangeTo { elem: e_b })
            | (Self::RangeFrom { elem: e_a }, Self::RangeFrom { elem: e_b })
            | (Self::Range { elem: e_a }, Self::Range { elem: e_b })
            | (Self::Option { elem: e_a }, Self::Option { elem: e_b }) => e_a.structural_eq(e_b),
            (Self::Array { elem: e_a, len: l_a }, Self::Array { elem: e_b, len: l_b }) => {
                l_a == l_b && e_a.structural_eq(e_b)
            }
            _ => self == other,
        }
    }

    /// Whether `WithRetag::Yes` on `Rvalue::Use` is an operational no-op.
    pub fn is_retag_noop(&self) -> bool {
        match self {
            Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Int(_)
            | Self::Enum(_)
            | Self::OverflowPair(_)
            | Self::RawPtr { .. }
            | Self::Slice { .. }
            | Self::Str
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. } => true,
            Self::Ref { .. } | Self::Unsupported => false,
            Self::Tuple { fields } => fields.iter().all(Self::is_retag_noop),
            Self::Option { elem } => elem.is_retag_noop(),
            Self::Array { elem, .. } => elem.is_retag_noop(),
        }
    }

    /// Whether locals of `self` are statically `Sized`.
    pub fn is_sized(&self) -> bool {
        match self {
            Self::Slice { .. } | Self::Str | Self::Unsupported => false,
            Self::Tuple { fields } => fields.iter().all(Self::is_sized),
            Self::Array { elem, .. } => elem.is_sized(),
            Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Int(_)
            | Self::Enum(_)
            | Self::OverflowPair(_)
            | Self::Ref { .. }
            | Self::RawPtr { .. }
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Option { .. } => true,
        }
    }

    /// Whether `self` is a reference or a tuple/array containing one, matching
    /// `Trusted.MirSemantics.tyHasRefV2`.
    pub fn has_ref_v2(&self) -> bool {
        match self {
            Self::Ref { .. } => true,
            Self::Array { elem, .. } | Self::Option { elem } => elem.has_ref_v2(),
            Self::Tuple { fields } => fields.iter().any(Self::has_ref_v2),
            Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Int(_)
            | Self::Enum(_)
            | Self::OverflowPair(_)
            | Self::RawPtr { .. }
            | Self::Slice { .. }
            | Self::Str
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Unsupported => false,
        }
    }

    /// Whether `self` is a raw pointer or a tuple/array containing one,
    /// matching `Trusted.MirSemantics.tyHasRawPtrV2`.
    pub fn has_raw_ptr_v2(&self) -> bool {
        match self {
            Self::RawPtr { .. } => true,
            Self::Array { elem, .. } | Self::Option { elem } => elem.has_raw_ptr_v2(),
            Self::Tuple { fields } => fields.iter().any(Self::has_raw_ptr_v2),
            Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Int(_)
            | Self::Enum(_)
            | Self::OverflowPair(_)
            | Self::Ref { .. }
            | Self::Slice { .. }
            | Self::Str
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Unsupported => false,
        }
    }

    /// Whether `self` is a `*const T` raw pointer type, matching
    /// `Trusted.MirSemantics.isConstRawPtrTy`.
    pub const fn is_const_raw_ptr(&self) -> bool {
        matches!(self, Self::RawPtr { mutability: Mutability::Shared, .. })
    }
}

/// Place projection element matching `Trusted.MirAst.ProjectionElem`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ProjectionElem {
    Deref,
    Field {
        #[serde(rename = "index", alias = "field_idx")]
        field_idx: u32,
        ty: Ty,
    },
    /// `ProjectionElem::ConstantIndex`; captured, but not yet evaluated.
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    /// `ProjectionElem::Downcast`; Profile v2 evaluates only the `Option`
    /// payload path `.downcast 1` followed by `.field 0`.
    Downcast {
        variant_idx: u64,
    },
    Unsupported,
}

/// MIR place `(local, projection)` matching `Trusted.MirAst.Place` and
/// schema v5 JSON.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Place {
    pub local: u32,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub projection: Vec<ProjectionElem>,
}

impl Place {
    /// Construct an unprojected local place.
    pub const fn local(local: u32) -> Self {
        Self { local, projection: Vec::new() }
    }
}

/// One byte of a read-only data constant, matching `Trusted.MirAst.RodataByte`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RodataByte {
    Uninit,
    Init { byte: u8 },
}

/// Constant literal payload matching `Trusted.MirAst.ConstLit`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ConstLit {
    ZeroSized,
    Scalar {
        #[serde(
            serialize_with = "serialize_u128_decimal",
            deserialize_with = "deserialize_u128_decimal"
        )]
        bits: u128,
    },
    /// By-value read-only data constant; captured, but not yet evaluated.
    RodataBytes {
        bytes: Vec<RodataByte>,
    },
    /// Reference to read-only data; captured, but not yet evaluated.
    RodataRef {
        bytes: Vec<RodataByte>,
        align_log2: u32,
        offset_bytes: u64,
        slice_len: Option<u64>,
    },
}

/// Operand in MIR rvalues and terminators.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Operand {
    Copy {
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
    },
    Move {
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
    },
    CopyPlace {
        place: Place,
    },
    MovePlace {
        place: Place,
    },
    Constant {
        ty: Ty,
        lit: ConstLit,
    },
}

impl Operand {
    /// View a place operand (`Copy`, `Move`, `CopyPlace`, or `MovePlace`) as
    /// `(local, projection, is_move)`.
    pub fn as_place(&self) -> Option<(u32, &[ProjectionElem], bool)> {
        match self {
            Self::Copy { local, projection } => Some((*local, projection.as_slice(), false)),
            Self::Move { local, projection } => Some((*local, projection.as_slice(), true)),
            Self::CopyPlace { place } => Some((place.local, place.projection.as_slice(), false)),
            Self::MovePlace { place } => Some((place.local, place.projection.as_slice(), true)),
            Self::Constant { .. } => None,
        }
    }
}

/// Unary MIR operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Cast kind in `Rvalue::Cast`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CastKind {
    IntToInt,
    PtrToPtr,
    IntToPtr,
    /// `PointerCoercion::Unsize`; captured, but not yet evaluated.
    Unsize,
    Unsupported,
}

/// Binary MIR operator matching `Trusted.MirAst.BinOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinOp {
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    ShlUnchecked,
    Shr,
    ShrUnchecked,
    Add,
    AddUnchecked,
    AddWithOverflow,
    Sub,
    SubUnchecked,
    SubWithOverflow,
    Mul,
    MulUnchecked,
    MulWithOverflow,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Cmp,
    Offset,
}

impl BinOp {
    pub const fn is_shift(self) -> bool {
        matches!(self, Self::Shl | Self::ShlUnchecked | Self::Shr | Self::ShrUnchecked)
    }

    pub const fn is_unchecked(self) -> bool {
        matches!(
            self,
            Self::AddUnchecked
                | Self::SubUnchecked
                | Self::MulUnchecked
                | Self::ShlUnchecked
                | Self::ShrUnchecked
        )
    }

    pub const fn is_overflowing(self) -> bool {
        matches!(self, Self::AddWithOverflow | Self::SubWithOverflow | Self::MulWithOverflow)
    }
}

/// Aggregate construction kind for Profile v2 extensibility.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AggregateKind {
    Tuple,
    Array { elem: Ty },
    Unsupported,
}

/// MIR right-hand-side expression.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Rvalue {
    Use {
        operand: Operand,
        #[serde(default)]
        with_retag: bool,
    },
    UseRetag {
        operand: Operand,
    },
    Binary {
        op: BinOp,
        left: Operand,
        right: Operand,
    },
    Unary {
        op: UnOp,
        operand: Operand,
    },
    Cast {
        cast_kind: CastKind,
        operand: Operand,
        ty: Ty,
    },
    Discriminant {
        place: Place,
    },
    AggregateTuple {
        fields: Vec<Operand>,
    },
    /// `AggregateKind::Array`; captured, but not yet evaluated.
    AggregateArray {
        elem_ty: Ty,
        elems: Vec<Operand>,
    },
    /// `Rvalue::Repeat`; captured, but not yet evaluated.
    Repeat {
        operand: Operand,
        elem_ty: Ty,
        count: u64,
    },
    AggregateRangeTo {
        elem_ty: Ty,
        end: Operand,
    },
    AggregateRangeFrom {
        elem_ty: Ty,
        start: Operand,
    },
    /// `AggregateKind::Adt` for `core::ops::Range`; captured, but not yet
    /// evaluated.
    AggregateRange {
        elem_ty: Ty,
        start: Operand,
        end: Operand,
    },
    /// `AggregateKind::Adt` for `core::option::Option` (`None` is variant 0
    /// without a payload, `Some` is variant 1 with one).
    AggregateOption {
        variant_idx: u64,
        inner_ty: Ty,
        #[serde(default)]
        payload: Option<Box<Operand>>,
    },
    Aggregate {
        aggregate_kind: AggregateKind,
        fields: Vec<Operand>,
    },
    Ref {
        mutability: Mutability,
        place: Place,
    },
    AddressOf {
        mutability: Mutability,
        place: Place,
    },
    FakeAddressOf {
        place: Place,
    },
    Unsupported,
}

/// MIR basic-block statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Statement {
    Assign {
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
        value: Rvalue,
    },
    AssignPlace {
        place: Place,
        value: Rvalue,
    },
    StorageLive {
        local: u32,
    },
    StorageDead {
        local: u32,
    },
    PlaceMention {
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
    },
    Nop,
    Unsupported,
}

impl Statement {
    /// If `self` is an assignment (`Assign` or `AssignPlace`), returns
    /// `(local, projection, value)`.
    pub fn as_assign(&self) -> Option<(u32, &[ProjectionElem], &Rvalue)> {
        match self {
            Self::Assign { local, projection, value } => {
                Some((*local, projection.as_slice(), value))
            }
            Self::AssignPlace { place, value } => {
                Some((place.local, place.projection.as_slice(), value))
            }
            _ => None,
        }
    }
}

/// Unwind action on panicking or calling terminators.
///
/// Schema v5 encodes non-cleanup actions as bare snake_case strings
/// (`"continue"`, `"unreachable"`, `"terminate"`). Deserialization also
/// accepts tagged object encodings (`{"kind": "..."}`) including
/// `{"kind": "cleanup", "block": n}` for fail-closed refusal testing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnwindAction {
    Continue,
    Unreachable,
    Terminate,
    Cleanup { block: u32 },
}

impl Serialize for UnwindAction {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Continue => serializer.serialize_str("continue"),
            Self::Unreachable => serializer.serialize_str("unreachable"),
            Self::Terminate => serializer.serialize_str("terminate"),
            Self::Cleanup { block } => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("kind", "cleanup")?;
                map.serialize_entry("block", block)?;
                map.end()
            }
        }
    }
}

impl<'de> Deserialize<'de> for UnwindAction {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct UnwindActionVisitor;

        impl<'de> Visitor<'de> for UnwindActionVisitor {
            type Value = UnwindAction;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str(
                    "an unwind action string (\"continue\", \"unreachable\", \"terminate\") \
                     or tagged object {\"kind\": ...}",
                )
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<UnwindAction, E> {
                match value {
                    "continue" => Ok(UnwindAction::Continue),
                    "unreachable" => Ok(UnwindAction::Unreachable),
                    "terminate" => Ok(UnwindAction::Terminate),
                    other => {
                        Err(E::unknown_variant(other, &["continue", "unreachable", "terminate"]))
                    }
                }
            }

            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<UnwindAction, A::Error> {
                let mut kind: Option<String> = None;
                let mut block: Option<u32> = None;
                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "kind" => {
                            if kind.is_some() {
                                return Err(de::Error::duplicate_field("kind"));
                            }
                            kind = Some(map.next_value()?);
                        }
                        "block" => {
                            if block.is_some() {
                                return Err(de::Error::duplicate_field("block"));
                            }
                            block = Some(map.next_value()?);
                        }
                        other => {
                            return Err(de::Error::unknown_field(other, &["kind", "block"]));
                        }
                    }
                }
                let kind = kind.ok_or_else(|| de::Error::missing_field("kind"))?;
                match kind.as_str() {
                    "continue" => {
                        if block.is_some() {
                            return Err(de::Error::custom(
                                "unexpected field \"block\" for continue unwind action",
                            ));
                        }
                        Ok(UnwindAction::Continue)
                    }
                    "unreachable" => {
                        if block.is_some() {
                            return Err(de::Error::custom(
                                "unexpected field \"block\" for unreachable unwind action",
                            ));
                        }
                        Ok(UnwindAction::Unreachable)
                    }
                    "terminate" => {
                        if block.is_some() {
                            return Err(de::Error::custom(
                                "unexpected field \"block\" for terminate unwind action",
                            ));
                        }
                        Ok(UnwindAction::Terminate)
                    }
                    "cleanup" => {
                        let block = block.ok_or_else(|| de::Error::missing_field("block"))?;
                        Ok(UnwindAction::Cleanup { block })
                    }
                    other => Err(de::Error::unknown_variant(
                        other,
                        &["continue", "unreachable", "terminate", "cleanup"],
                    )),
                }
            }
        }

        deserializer.deserialize_any(UnwindActionVisitor)
    }
}

/// Assertion failure kind for Profile v2 `Terminator::Assert`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AssertKind {
    Overflow { op: BinOp },
    OverflowNeg,
    DivByZero,
    RemByZero,
    BoundsCheck,
    MisalignedPtrDeref,
    NullPtrDeref,
    Unsupported,
}

/// Closed table of `core` primitive calls executed in Profile v2,
/// matching `Trusted.MirAst.CoreCallOp`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CoreCallOp {
    SliceLen,
    SliceGetUncheckedRangeTo,
    SliceGetUncheckedRangeFrom,
    /// `<[T]>::index(Range)`; captured, but not yet evaluated.
    SliceIndexRange {
        mutability: Mutability,
        elem: Ty,
    },
    /// `<[T]>::index(RangeFrom)`; captured, but not yet evaluated.
    SliceIndexRangeFrom {
        mutability: Mutability,
        elem: Ty,
    },
    /// `<[T]>::is_empty`; captured, but not yet evaluated.
    SliceIsEmpty {
        elem: Ty,
    },
    /// `<[T]>::split_at{,_mut}`; captured, but not yet evaluated.
    SliceSplitAt {
        mutability: Mutability,
        elem: Ty,
    },
    /// `{integer}::is_multiple_of`; captured, but not yet evaluated.
    NumIsMultipleOf(IntTy),
    NumCheckedAdd(IntTy),
    NumCheckedMul(IntTy),
    NumCheckedSub(IntTy),
    /// `{integer}::saturating_add`; captured, but not yet evaluated.
    NumSaturatingAdd(IntTy),
    /// `{integer}::wrapping_shl`; captured, but not yet evaluated.
    NumWrappingShl(IntTy),
    /// `{integer}::wrapping_shr`; captured, but not yet evaluated.
    NumWrappingShr(IntTy),
    /// `{integer}::leading_zeros`; captured, but not yet evaluated.
    NumLeadingZeros(IntTy),
    /// `{integer}::overflowing_add`; captured, but not yet evaluated.
    NumOverflowingAdd(IntTy),
    /// `{integer}::overflowing_sub`; captured, but not yet evaluated.
    NumOverflowingSub(IntTy),
    /// `core::cmp::min`; captured, but not yet evaluated.
    CmpMin(IntTy),
    /// `core::cmp::max`; captured, but not yet evaluated.
    CmpMax(IntTy),
    /// `core::mem::replace`; captured, but not yet evaluated.
    MemReplace {
        ty: Ty,
    },
    /// `Option::is_some` through `&Option<T>`; captured, but not yet
    /// evaluated (`Option` values are immediate-only in this evaluator).
    OptionIsSome {
        inner: Ty,
    },
    /// `Option::is_none` through `&Option<T>`; captured, but not yet
    /// evaluated.
    OptionIsNone {
        inner: Ty,
    },
    /// `Option::take` through `&mut Option<T>`; captured, but not yet
    /// evaluated.
    OptionTake {
        inner: Ty,
    },
    OptionUnwrap {
        inner: Ty,
    },
    PtrAdd {
        mutability: Mutability,
        pointee: Ty,
    },
    UsizeUncheckedSub,
    /// `{integer}::to_le_bytes`; captured, but not yet evaluated.
    IntToLeBytes {
        int_ty: IntTy,
    },
    /// `<[T; N] as PartialEq>::eq`; captured, but not yet evaluated.
    ArrayEq {
        elem: Ty,
        len: u64,
    },
    /// Diverging `core::panicking::{panic, panic_nounwind}` taking a shared
    /// `&str` message (`target = None`).
    PanicAbort,
}

/// Pinned `core::num` arithmetic operation executed in Profile v1,
/// matching `Trusted.MirAst.SysrootNumKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SysrootNumKind {
    UncheckedAdd,
    UncheckedSub,
    UncheckedMul,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
}

/// Pinned `core::num` sysroot call descriptor matching
/// `Trusted.MirAst.SysrootNumOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SysrootNumOp {
    pub kind: SysrootNumKind,
    pub ty: IntTy,
}

/// MIR basic-block terminator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Terminator {
    Goto {
        block: u32,
    },
    SwitchInt {
        operand: Operand,
        #[serde(
            serialize_with = "serialize_switch_targets_decimal",
            deserialize_with = "deserialize_switch_targets_decimal"
        )]
        targets: Vec<(u128, u32)>,
        otherwise: u32,
    },
    Ret,
    Unreachable,
    UnwindResume,
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertKind,
        target: u32,
        unwind: UnwindAction,
    },
    CoreCall {
        op: CoreCallOp,
        args: Vec<Operand>,
        dst: Place,
        #[serde(default)]
        target: Option<u32>,
        unwind: UnwindAction,
    },
    Call {
        callee: u32,
        args: Vec<Operand>,
        #[serde(rename = "dst", alias = "dst_local")]
        dst_local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        dst_projection: Vec<ProjectionElem>,
        target: Option<u32>,
        unwind: UnwindAction,
    },
    SysrootCall {
        op: SysrootNumOp,
        args: Vec<Operand>,
        #[serde(rename = "dst", alias = "dst_local")]
        dst_local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        dst_projection: Vec<ProjectionElem>,
        target: Option<u32>,
        unwind: UnwindAction,
    },
    Unsupported,
}

/// Basic block containing sequential statements and one terminator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
    #[serde(default)]
    pub cleanup: bool,
}

/// Captured MIR function body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Body {
    pub arg_count: usize,
    #[serde(default)]
    pub is_unsafe: bool,
    pub local_tys: Vec<Ty>,
    pub blocks: Vec<Block>,
    #[serde(default)]
    pub identity: String,
}

impl Body {
    /// Returns parameter types `local_tys[1..=arg_count]` when in bounds.
    pub fn param_tys(&self) -> Option<&[Ty]> {
        let end = self.arg_count.checked_add(1)?;
        self.local_tys.get(1..end)
    }

    /// Returns return place type `_0` when non-empty.
    pub fn return_ty(&self) -> Option<&Ty> {
        self.local_tys.first()
    }
}

/// Generic monomorphized item selector entry.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct Instantiation {
    pub path: String,
    pub args: Vec<String>,
}

/// Capture verification scope (`SelectedUnit` or whole `Crate`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Scope {
    SelectedUnit {
        roots: BTreeSet<String>,
        #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
        instantiations: BTreeSet<Instantiation>,
    },
    Crate,
}

/// Complete MIR program unit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Program {
    pub scope: Scope,
    pub bodies: Vec<Body>,
    #[serde(default)]
    pub entry_def_id: u32,
    #[serde(default = "default_pointer_width_bits")]
    pub pointer_width_bits: u64,
    #[serde(default)]
    pub overflow_checks: bool,
    /// Captured `-Cpanic` strategy (`Trusted.MirAst.Program.panicStrategy`).
    #[serde(default)]
    pub panic: PanicStrategy,
    /// Whether the crate defines its own `#[panic_handler]`
    /// (`Trusted.MirAst.Program.hasLocalPanicHandler`, defaulting to `true` so
    /// a manifest without the field never aborts).
    #[serde(default = "default_has_local_panic_handler")]
    pub has_local_panic_handler: bool,
    #[serde(default = "default_mir_profile_version")]
    pub mir_profile_version: u32,
}

/// Crate compilation type recorded in capture manifests.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CrateType {
    #[default]
    Lib,
    Bin,
}

/// Panic strategy recorded in capture manifests.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PanicStrategy {
    #[default]
    Unwind,
    Abort,
}

/// Compiler linkage mode recorded in capture manifests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DriverLinkage {
    DynamicDso,
    StaticExe,
}

/// Compiler driver identity metadata.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DriverIdentity {
    pub linkage: DriverLinkage,
    pub driver_sha256: String,
    pub dso_digests: BTreeMap<String, String>,
}

/// Compiler metadata in a schema v5 capture manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Compiler {
    pub commit: String,
    pub version: String,
    pub sysroot: String,
    pub rustc_sha256: String,
    pub driver: DriverIdentity,
}

/// Standard-library crate capability recorded in capture manifests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StdlibCrate {
    Core,
}

/// Compilation configuration recorded in a schema v5 capture manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Configuration {
    pub crate_root: String,
    pub crate_name: String,
    pub crate_type: CrateType,
    pub panic: PanicStrategy,
    pub edition: String,
    pub target: String,
    pub cfg: Vec<String>,
    pub env: BTreeMap<String, String>,
    pub opt_level: u8,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub mir_preserve_ub: bool,
    pub pointer_bits: u64,
    pub endian: String,
    pub declared_source_files: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stdlib_crate: Option<StdlibCrate>,
}

/// Captured source file digest metadata.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceFile {
    pub path: String,
    pub sha256: String,
    pub read_kind: String,
}

/// Compiler item census record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CensusItem {
    pub def_id: u32,
    pub path: String,
    pub kind: String,
    pub has_body: bool,
    pub selected: bool,
    pub required: bool,
}

/// Mapping from selected compiler item to `program.bodies` index.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SelectedBody {
    pub def_id: u32,
    pub path: String,
    pub body_index: usize,
}

/// Item rejected during capture translation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnsupportedItem {
    pub def_id: u32,
    pub path: String,
    pub reason: String,
}

/// Full capture manifest written by `anneal-rustc-capture`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Manifest {
    pub schema_version: u32,
    pub compiler: Compiler,
    pub configuration: Configuration,
    pub source_files: Vec<SourceFile>,
    pub census: Vec<CensusItem>,
    pub selected: Vec<SelectedBody>,
    pub unsupported: Vec<UnsupportedItem>,
    pub program: Program,
}

impl Manifest {
    /// Extract an evaluation-ready `Program` carrying the manifest's configured
    /// target `pointer_bits`, `overflow_checks`, and `panic` strategy.
    pub fn into_program(mut self) -> Program {
        self.program.pointer_width_bits = self.configuration.pointer_bits;
        self.program.overflow_checks = self.configuration.overflow_checks;
        self.program.panic = self.configuration.panic;
        self.program
    }

    /// Borrow a cloned evaluation-ready `Program` with `pointer_width_bits`,
    /// `overflow_checks`, and `panic` synchronized from `configuration`.
    pub fn to_program(&self) -> Program {
        let mut program = self.program.clone();
        program.pointer_width_bits = self.configuration.pointer_bits;
        program.overflow_checks = self.configuration.overflow_checks;
        program.panic = self.configuration.panic;
        program
    }
}

/// Decoded capture payload, either a full schema v5 [`Manifest`] or a
/// standalone [`Program`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaptureInput {
    Manifest(Box<Manifest>),
    Program(Program),
}

impl CaptureInput {
    /// Parse a JSON document as either a capture [`Manifest`] (validating
    /// `schema_version == 5`) or a standalone [`Program`].
    pub fn from_json_str(json: &str) -> Result<Self, String> {
        let raw: serde_json::Value =
            serde_json::from_str(json).map_err(|err| format!("invalid JSON: {err}"))?;
        let Some(obj) = raw.as_object() else {
            return Err("expected top-level JSON object".into());
        };
        if let Some(version_val) = obj.get("schema_version") {
            let Some(version) = version_val.as_u64() else {
                return Err("schema_version must be an unsigned integer".into());
            };
            if version != u64::from(CAPTURE_SCHEMA_VERSION) {
                return Err(format!(
                    "unsupported capture schema_version {version} (expected {CAPTURE_SCHEMA_VERSION})"
                ));
            }
            let explicit_prog_ptr_bits = raw
                .get("program")
                .and_then(|p| p.get("pointer_width_bits"))
                .and_then(serde_json::Value::as_u64);
            let explicit_prog_overflow_checks = raw
                .get("program")
                .and_then(|p| p.get("overflow_checks"))
                .and_then(serde_json::Value::as_bool);
            let explicit_prog_panic = raw.get("program").and_then(|p| p.get("panic")).cloned();
            let mut manifest: Manifest = serde_json::from_value(raw)
                .map_err(|err| format!("invalid capture manifest: {err}"))?;
            if let Some(explicit) = explicit_prog_ptr_bits
                && explicit != manifest.configuration.pointer_bits
            {
                return Err(format!(
                    "manifest pointer width mismatch: configuration.pointer_bits={} != program.pointer_width_bits={explicit}",
                    manifest.configuration.pointer_bits
                ));
            }
            if let Some(explicit) = explicit_prog_overflow_checks
                && explicit != manifest.configuration.overflow_checks
            {
                return Err(format!(
                    "manifest overflow_checks mismatch: configuration.overflow_checks={} != program.overflow_checks={explicit}",
                    manifest.configuration.overflow_checks
                ));
            }
            if let Some(explicit) = explicit_prog_panic {
                let explicit: PanicStrategy = serde_json::from_value(explicit)
                    .map_err(|err| format!("invalid program.panic: {err}"))?;
                if explicit != manifest.configuration.panic {
                    return Err(format!(
                        "manifest panic strategy mismatch: configuration.panic={:?} != program.panic={explicit:?}",
                        manifest.configuration.panic
                    ));
                }
            }
            manifest.program.pointer_width_bits = manifest.configuration.pointer_bits;
            manifest.program.overflow_checks = manifest.configuration.overflow_checks;
            manifest.program.panic = manifest.configuration.panic;
            Ok(Self::Manifest(Box::new(manifest)))
        } else {
            if !obj.contains_key("pointer_width_bits") || !obj.contains_key("mir_profile_version") {
                return Err(
                    "standalone MIR program JSON must specify pointer_width_bits and mir_profile_version"
                        .into(),
                );
            }
            let program: Program = serde_json::from_value(raw)
                .map_err(|err| format!("invalid MIR program JSON: {err}"))?;
            Ok(Self::Program(program))
        }
    }

    /// Return the evaluation-ready [`Program`] (propagating manifest
    /// `configuration.pointer_bits` and `configuration.overflow_checks` when
    /// loaded from a manifest).
    pub fn into_program(self) -> Program {
        match self {
            Self::Manifest(m) => m.into_program(),
            Self::Program(p) => p,
        }
    }

    /// Optional manifest metadata when parsed from a capture manifest.
    pub fn manifest(&self) -> Option<&Manifest> {
        match self {
            Self::Manifest(m) => Some(m),
            Self::Program(_) => None,
        }
    }
}
