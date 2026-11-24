// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture JSON IR schema types and decoders mirroring
//! `anneal-rustc-capture` schema version 4 (Profile v1) with explicit
//! extensibility for Profile v2 constructs.

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
    de::{self, SeqAccess, Visitor},
    ser::SerializeSeq,
};

/// Capture JSON schema version produced by `anneal-rustc-capture`.
pub const CAPTURE_SCHEMA_VERSION: u32 = 4;

const fn default_pointer_width_bits() -> u64 {
    64
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

/// MIR local and constant types matching schema v4 plus Profile v2 extensions.
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
    Tuple { fields: Vec<Ty> },
    Ref { mutability: Mutability, pointee: Box<Ty> },
    RawPtr { mutability: Mutability, pointee: Box<Ty> },
    Array { elem: Box<Ty>, len: u64 },
    Unsupported,
}

impl Ty {
    /// Returns the inner integer type when `self` represents an `(T, bool)`
    /// overflow pair (either schema v4 `OverflowPair(ity)` or normalized
    /// Profile v2 `Tuple { fields: [Int(ity), Bool] }`).
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
            (Self::Array { elem: e_a, len: l_a }, Self::Array { elem: e_b, len: l_b }) => {
                l_a == l_b && e_a.structural_eq(e_b)
            }
            _ => self == other,
        }
    }

    /// Whether `WithRetag::Yes` on `Rvalue::Use` is an operational no-op.
    pub fn is_retag_noop(&self) -> bool {
        self.as_overflow_pair().is_some()
            || matches!(
                self,
                Self::Bool
                    | Self::Char
                    | Self::Ordering
                    | Self::Unit
                    | Self::Never
                    | Self::Int(_)
                    | Self::Enum(_)
                    | Self::OverflowPair(_)
            )
    }

    /// Whether locals of `self` are statically `Sized`.
    pub const fn is_sized(&self) -> bool {
        matches!(
            self,
            Self::Bool
                | Self::Char
                | Self::Ordering
                | Self::Unit
                | Self::Never
                | Self::Int(_)
                | Self::Enum(_)
                | Self::OverflowPair(_)
                | Self::Tuple { .. }
                | Self::Ref { .. }
                | Self::RawPtr { .. }
                | Self::Array { .. }
        )
    }
}

/// Place projection element (Profile v1 rejects non-empty projections;
/// opt-in preview Profile v2 executes `.field`, while `.deref` fails closed
/// as `Unsupported`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ProjectionElem {
    Deref,
    Field { field_idx: u32, ty: Ty },
    Unsupported,
}

/// Constant literal payload matching `Trusted.MirAst.ConstLit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
    Constant {
        ty: Ty,
        lit: ConstLit,
    },
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
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
    },
    AggregateTuple {
        fields: Vec<Operand>,
    },
    Aggregate {
        aggregate_kind: AggregateKind,
        fields: Vec<Operand>,
    },
    Ref {
        mutability: Mutability,
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
    },
    AddressOf {
        mutability: Mutability,
        local: u32,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        projection: Vec<ProjectionElem>,
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

/// Unwind action on panicking terminators.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum UnwindAction {
    Continue,
    Unreachable,
    Terminate,
    Cleanup { block: u32 },
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
    Call {
        callee: u32,
        args: Vec<Operand>,
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

/// Compiler metadata in a schema v4 capture manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Compiler {
    pub commit: String,
    pub version: String,
    pub sysroot: String,
    pub rustc_sha256: String,
    pub driver: DriverIdentity,
}

/// Compilation configuration recorded in a schema v4 capture manifest.
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
    /// target `pointer_bits`.
    pub fn into_program(mut self) -> Program {
        self.program.pointer_width_bits = self.configuration.pointer_bits;
        self.program
    }

    /// Borrow a cloned evaluation-ready `Program` with `pointer_width_bits`
    /// synchronized from `configuration.pointer_bits`.
    pub fn to_program(&self) -> Program {
        let mut program = self.program.clone();
        program.pointer_width_bits = self.configuration.pointer_bits;
        program
    }
}

/// Decoded capture payload, either a full schema v4 [`Manifest`] or a standalone
/// [`Program`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaptureInput {
    Manifest(Box<Manifest>),
    Program(Program),
}

impl CaptureInput {
    /// Parse a JSON document as either a capture [`Manifest`] (validating
    /// `schema_version == 4`) or a standalone [`Program`].
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
            manifest.program.pointer_width_bits = manifest.configuration.pointer_bits;
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
    /// `configuration.pointer_bits` when loaded from a manifest).
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
