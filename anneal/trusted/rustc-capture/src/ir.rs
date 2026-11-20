// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Owned capture data. Metadata and semantic constructors stay separate so that
//! Rust names and paths never become executable Lean source.

use std::collections::BTreeSet;
use std::path::PathBuf;

use serde::{Serialize, Serializer};

// Version 4 extends the typed IR JSON schema for Tier 1 MIR: `IntWidth::I128`,
// non-empty `Ty::Tuple`, `Place` with `ProjectionElem::Field`, `UnOp`, full
// scalar `BinOp` (`Div`, `Rem`, `*Unchecked`, `*WithOverflow`),
// `CastKind::IntToInt`, `Rvalue::{Unary, Cast, AggregateTuple}`,
// `Block.cleanup`, `UnwindAction`, operand-free `AssertKind`, audited
// `CoreBuiltin`, `Terminator::{Assert, UnwindResume, Call, CallBuiltin}`,
// decimal-string serialization for 128-bit payloads, and configurable
// `overflow_checks`.
pub const SCHEMA_VERSION: u32 = 4;
pub const COMPILER_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";
pub const COMPILER_VERSION: &str = "1.98.0-nightly (f8a08b688 2026-05-30)";

/// Serialize a 128-bit unsigned payload as a decimal string so `serde_json`
/// consumers without `arbitrary_precision` preserve all 128 bits losslessly.
fn serialize_u128<S: Serializer>(value: &u128, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&value.to_string())
}

fn serialize_u128_vec<S: Serializer>(values: &[u128], serializer: S) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeSeq;
    let mut seq = serializer.serialize_seq(Some(values.len()))?;
    for value in values {
        seq.serialize_element(&value.to_string())?;
    }
    seq.end()
}

/// Admitted integer widths in the 64-bit little-endian capture profile,
/// corresponding 1-to-1 to `Trusted.MirAst.IntWidth`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
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
    pub const fn bits(self) -> u32 {
        match self {
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 | Self::Isize => 64,
            Self::I128 => 128,
        }
    }

    pub const fn mask(self) -> u128 {
        match self {
            Self::I128 => u128::MAX,
            _ => (1u128 << self.bits()) - 1,
        }
    }

    pub const fn lean_name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
            Self::Isize => "isize",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct IntTy {
    pub width: IntWidth,
    pub signed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EnumTagRepr {
    ZeroSized,
    Scalar(IntTy),
}

/// Recover discriminant bits from raw tag bits as `rustc` does for
/// `TagEncoding::Direct`. The tag is read at the integer type of its layout
/// primitive and then cast to the discriminant type ("Cast bits from tag
/// layout to discriminant layout."). That integer cast first makes sure the
/// value "is sign-extended *if* it has a signed type" and then truncates it to
/// the target size.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/discriminant.rs#L95-L96
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/discriminant.rs#L119-L123
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/cast.rs#L266-L286
fn tag_bits_to_discr_bits(tag: IntTy, discr_width: IntWidth, raw_tag: u128) -> u128 {
    let masked_tag = raw_tag & tag.width.mask();
    let extended = if tag.signed {
        let shift = 128 - tag.width.bits();
        (((masked_tag << shift) as i128) >> shift) as u128
    } else {
        masked_tag
    };
    extended & discr_width.mask()
}

/// Validated fieldless enum descriptor matching `Trusted.MirAst.EnumTy` and
/// `Trusted.MirSemantics.enumAdmitted`.
///
/// Private fields guarantee that every `EnumTy` instance is inhabited, has
/// fewer than `2^32` variants, carries pairwise-distinct discriminants within
/// `discr_width`, and round-trips losslessly through `tag_repr`.
///
/// `id` is the nominal key that Lean compares in enum type equality. Capture
/// derives it with `extract::enum_id` from the enum's semantic path rather
/// than from a compiler index, and refuses crates in which two local enums
/// share a key. This constructor does not check how the key was derived.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnumTy {
    id: u32,
    discr_width: IntWidth,
    discr_signed: bool,
    tag_repr: EnumTagRepr,
    #[serde(serialize_with = "serialize_u128_vec")]
    discriminants: Vec<u128>,
}

impl EnumTy {
    pub fn try_new(
        id: u32,
        discr: IntTy,
        tag_repr: EnumTagRepr,
        discriminants: Vec<u128>,
    ) -> Result<Self, String> {
        if discriminants.is_empty() {
            return Err("uninhabited zero-variant enums are unsupported".into());
        }
        if u64::try_from(discriminants.len()).unwrap_or(u64::MAX) >= (1u64 << 32) {
            return Err("enum variant count is at or above 2^32".into());
        }
        let discr_mask = discr.width.mask();
        for &d in &discriminants {
            if d > discr_mask {
                return Err("enum discriminant exceeds its discriminant width".into());
            }
        }
        let unique: BTreeSet<u128> = discriminants.iter().copied().collect();
        if unique.len() != discriminants.len() {
            return Err("duplicate enum discriminants are unsupported".into());
        }
        match tag_repr {
            EnumTagRepr::ZeroSized => {
                if discriminants.len() != 1 {
                    return Err("zero-sized enum tag requires a single variant".into());
                }
            }
            EnumTagRepr::Scalar(tag) => {
                let tag_mask = tag.width.mask();
                for &d in &discriminants {
                    let recovered = tag_bits_to_discr_bits(tag, discr.width, d & tag_mask);
                    if recovered != d {
                        return Err(
                            "enum discriminant does not round-trip through its tag representation"
                                .into(),
                        );
                    }
                }
            }
        }
        Ok(Self {
            id,
            discr_width: discr.width,
            discr_signed: discr.signed,
            tag_repr,
            discriminants,
        })
    }

    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn discr(&self) -> IntTy {
        IntTy {
            width: self.discr_width,
            signed: self.discr_signed,
        }
    }

    pub fn tag_repr(&self) -> EnumTagRepr {
        self.tag_repr
    }

    pub fn discriminants(&self) -> &[u128] {
        &self.discriminants
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Ty {
    Bool,
    Unit,
    Never,
    Int(IntTy),
    Enum(EnumTy),
    Tuple { fields: Vec<Ty> },
}

impl Ty {
    /// Whether `rustc`'s `WithRetag::Yes` (`pub enum WithRetag { Yes, No }`,
    /// where `Rvalue::Use` "yields the operand unchanged, except for a
    /// potential retag") is an operational no-op for values of this type.
    /// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L497-L511
    /// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1365
    ///
    /// In Miri (`Miri/Interpreter/Rvalue.lean` and `ValidityVisitor.lean`),
    /// `WithRetag::Yes` sets `RetagMode::Default` during `copyOp`, which calls
    /// `retagSafePointer` only inside `ValidityVisitor::checkSafe` on safe
    /// pointers (`&T`, `&mut T`, `Box<T>`). For reference-free scalar, unit,
    /// never, fieldless-enum, and tuple-of-retag-noop types, `WithRetag::Yes`
    /// and `WithRetag::No` have identical semantics. Any future `Ty` variant
    /// capable of carrying references or `Box` must return `false` so capture
    /// fails closed rather than erasing active retags.
    pub fn is_retag_noop(&self) -> bool {
        match self {
            Self::Bool | Self::Unit | Self::Never | Self::Int(_) | Self::Enum(_) => true,
            Self::Tuple { fields } => fields.iter().all(Self::is_retag_noop),
        }
    }
}

/// Validate structural type invariants (`Ty::Tuple` must be non-empty; `()`
/// uses `Ty::Unit`).
pub fn validate_ty(ty: &Ty) -> Result<(), String> {
    match ty {
        Ty::Bool | Ty::Unit | Ty::Never | Ty::Int(_) | Ty::Enum(_) => Ok(()),
        Ty::Tuple { fields } => {
            if fields.is_empty() {
                return Err("empty tuple type must use Ty::Unit".into());
            }
            for field in fields {
                validate_ty(field)?;
            }
            Ok(())
        }
    }
}

/// Constant literal payload matching `Trusted.MirAst.ConstLit` 1-to-1.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ConstLit {
    ZeroSized,
    Scalar {
        #[serde(serialize_with = "serialize_u128")]
        bits: u128,
    },
}

/// Validate that `with_retag` is admitted for destination type `dst_ty`.
///
/// `lean.rs` renders `Rvalue::Use` without its retag flag, so the flag may be
/// erased only when [`Ty::is_retag_noop`] holds for the destination type.
/// Every admitted [`Ty`] variant is retag-noop today, so this check cannot
/// fail for any current type. `admit_retag` holds the refusal itself, which
/// stays unit-tested until a reference-bearing variant makes it reachable.
pub fn check_use_retag(dst_ty: &Ty, with_retag: bool) -> Result<(), String> {
    admit_retag(dst_ty.is_retag_noop(), with_retag)
}

/// Refuse erasing a `WithRetag::Yes` that could change the assigned value.
fn admit_retag(retag_noop: bool, with_retag: bool) -> Result<(), String> {
    if with_retag && !retag_noop {
        return Err("retagging Use rvalues on reference-bearing types are unsupported".into());
    }
    Ok(())
}

/// Validate a typed constant literal against `evalConstLit` invariants.
pub fn validate_constant(ty: &Ty, lit: ConstLit) -> Result<(), String> {
    validate_ty(ty)?;
    match (ty, lit) {
        (Ty::Unit, ConstLit::ZeroSized) => Ok(()),
        (Ty::Unit, ConstLit::Scalar { .. }) => {
            Err("zero-sized constant must use ZeroSized literal".into())
        }
        (Ty::Never, ConstLit::ZeroSized) => {
            Err("ZeroSized constant requires unit or zero-sized enum type".into())
        }
        (Ty::Never, ConstLit::Scalar { .. }) => {
            Err("the never type has no scalar constants".into())
        }
        (Ty::Bool, ConstLit::ZeroSized) => {
            Err("ZeroSized constant requires unit or zero-sized enum type".into())
        }
        (Ty::Bool, ConstLit::Scalar { bits }) => {
            // `Scalar::to_bool` maps `0` and `1` to `false` and `true` and
            // raises `InvalidBool` for every other byte.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/value.rs#L344-L351
            if bits <= 1 {
                Ok(())
            } else {
                Err("invalid Boolean constant".into())
            }
        }
        (Ty::Int(_), ConstLit::ZeroSized) => {
            Err("ZeroSized constant requires unit or zero-sized enum type".into())
        }
        (Ty::Int(ity), ConstLit::Scalar { bits }) => {
            if bits > ity.width.mask() {
                return Err(format!(
                    "scalar constant {bits:#x} exceeds {}-bit width",
                    ity.width.bits()
                ));
            }
            Ok(())
        }
        (Ty::Tuple { .. }, _) => Err("tuple constants are unsupported".into()),
        (Ty::Enum(ety), lit) => match (ety.tag_repr, lit) {
            (EnumTagRepr::ZeroSized, ConstLit::ZeroSized) => Ok(()),
            (EnumTagRepr::ZeroSized, ConstLit::Scalar { .. }) => {
                Err("zero-sized constant must use ZeroSized literal".into())
            }
            (EnumTagRepr::Scalar(_), ConstLit::ZeroSized) => {
                Err("ZeroSized constant requires unit or zero-sized enum type".into())
            }
            (EnumTagRepr::Scalar(tag), ConstLit::Scalar { bits }) => {
                if bits > tag.width.mask() {
                    return Err(format!(
                        "enum tag constant {bits:#x} exceeds {}-bit tag width",
                        tag.width.bits()
                    ));
                }
                let discr = tag_bits_to_discr_bits(tag, ety.discr().width, bits);
                if !ety.discriminants.contains(&discr) {
                    return Err(format!(
                        "enum tag constant {bits:#x} does not match any declared variant"
                    ));
                }
                Ok(())
            }
        },
    }
}

/// Admitted MIR place projection elements matching
/// `Trusted.MirAst.ProjectionElem`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ProjectionElem {
    Field { index: u32, ty: Ty },
}

/// MIR place (`local` plus left-to-right `projection` elements) matching
/// `Trusted.MirAst.Place`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Place {
    pub local: u32,
    pub projection: Vec<ProjectionElem>,
}

#[cfg(test)]
impl Place {
    pub fn local(local: u32) -> Self {
        Self {
            local,
            projection: Vec::new(),
        }
    }
}

/// Resolve and validate `place` against `local_tys`, mirroring
/// `Trusted.MirSemantics.projectTy?`.
pub fn project_place_ty<'a>(
    local_tys: &'a [Ty],
    place: &Place,
    role: &str,
) -> Result<&'a Ty, String> {
    let mut current = local_tys
        .get(place.local as usize)
        .ok_or_else(|| format!("{role} local {} out of bounds", place.local))?;
    for elem in &place.projection {
        match elem {
            ProjectionElem::Field { index, ty: stated } => {
                validate_ty(stated)?;
                let Ty::Tuple { fields } = current else {
                    return Err(format!(
                        "{role} field projection requires tuple place, got {current:?}"
                    ));
                };
                let field_ty = fields.get(*index as usize).ok_or_else(|| {
                    format!(
                        "{role} field projection index {index} out of bounds for {} fields",
                        fields.len()
                    )
                })?;
                if field_ty != stated {
                    return Err(format!(
                        "{role} field projection type {stated:?} disagrees with tuple field {field_ty:?}"
                    ));
                }
                current = field_ty;
            }
        }
    }
    Ok(current)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Operand {
    Copy { place: Place },
    Move { place: Place },
    Constant { ty: Ty, lit: ConstLit },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
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
}

impl BinOp {
    pub const fn is_with_overflow(self) -> bool {
        matches!(
            self,
            Self::AddWithOverflow | Self::SubWithOverflow | Self::MulWithOverflow
        )
    }

    pub const fn is_admitted_assert_overflow_op(self) -> bool {
        matches!(
            self,
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Rem | Self::Shl | Self::Shr
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CastKind {
    IntToInt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Rvalue {
    Unit,
    Use {
        operand: Operand,
        with_retag: bool,
    },
    Unary {
        op: UnOp,
        operand: Operand,
    },
    Binary {
        op: BinOp,
        left: Operand,
        right: Operand,
    },
    Cast {
        cast_kind: CastKind,
        operand: Operand,
        ty: Ty,
    },
    AggregateTuple {
        operands: Vec<Operand>,
    },
    Discriminant {
        place: Place,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Statement {
    Assign { place: Place, value: Rvalue },
    StorageLive { local: u32 },
    StorageDead { local: u32 },
    Nop,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum UnwindAction {
    Continue,
    Unreachable,
    Terminate,
    Cleanup { block: u32 },
}

/// Admitted operand-free `AssertKind` variants matching
/// `Trusted.MirSemantics.isOperandFreeAssertKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AssertKind {
    Overflow { op: BinOp },
    OverflowNeg,
    DivisionByZero,
    RemainderByZero,
    NullPointerDereference,
}

/// Audited `core::num` and `core::cmp` scalar/tuple builtins matching
/// `Trusted.MirAst.CoreBuiltin` 1-to-1.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CoreBuiltin {
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    WrappingShl,
    WrappingShr,
    OverflowingAdd,
    OverflowingSub,
    OverflowingMul,
    SaturatingAdd,
    SaturatingSub,
    LeadingZeros,
    TrailingZeros,
    IsMultipleOf,
    CmpMin,
    CmpMax,
}

impl CoreBuiltin {
    pub const fn lean_name(self) -> &'static str {
        match self {
            Self::WrappingAdd => "wrappingAdd",
            Self::WrappingSub => "wrappingSub",
            Self::WrappingMul => "wrappingMul",
            Self::WrappingShl => "wrappingShl",
            Self::WrappingShr => "wrappingShr",
            Self::OverflowingAdd => "overflowingAdd",
            Self::OverflowingSub => "overflowingSub",
            Self::OverflowingMul => "overflowingMul",
            Self::SaturatingAdd => "saturatingAdd",
            Self::SaturatingSub => "saturatingSub",
            Self::LeadingZeros => "leadingZeros",
            Self::TrailingZeros => "trailingZeros",
            Self::IsMultipleOf => "isMultipleOf",
            Self::CmpMin => "cmpMin",
            Self::CmpMax => "cmpMax",
        }
    }
}

/// Validate `CoreBuiltin` argument and destination types against
/// `Trusted.MirSemantics.evalCoreBuiltin`.
pub fn validate_core_builtin_signature(
    builtin: CoreBuiltin,
    arg_tys: &[&Ty],
    dst_ty: &Ty,
) -> Result<(), String> {
    let u32_ty = Ty::Int(IntTy {
        width: IntWidth::I32,
        signed: false,
    });
    match builtin {
        CoreBuiltin::WrappingAdd
        | CoreBuiltin::WrappingSub
        | CoreBuiltin::WrappingMul
        | CoreBuiltin::SaturatingAdd
        | CoreBuiltin::SaturatingSub
        | CoreBuiltin::CmpMin
        | CoreBuiltin::CmpMax => {
            let [Ty::Int(lhs), Ty::Int(rhs)] = arg_tys else {
                return Err(format!(
                    "builtin {builtin:?} requires two integer arguments"
                ));
            };
            if lhs != rhs || *dst_ty != Ty::Int(*lhs) {
                return Err(format!(
                    "builtin {builtin:?} requires matching integer arguments and destination"
                ));
            }
            Ok(())
        }
        CoreBuiltin::WrappingShl | CoreBuiltin::WrappingShr => {
            let [Ty::Int(lhs), rhs] = arg_tys else {
                return Err(format!("builtin {builtin:?} requires (int, u32) arguments"));
            };
            if **rhs != u32_ty || *dst_ty != Ty::Int(*lhs) {
                return Err(format!(
                    "builtin {builtin:?} requires u32 shift amount and matching destination"
                ));
            }
            Ok(())
        }
        CoreBuiltin::OverflowingAdd | CoreBuiltin::OverflowingSub | CoreBuiltin::OverflowingMul => {
            let [Ty::Int(lhs), Ty::Int(rhs)] = arg_tys else {
                return Err(format!(
                    "builtin {builtin:?} requires two integer arguments"
                ));
            };
            let expected_dst = Ty::Tuple {
                fields: vec![Ty::Int(*lhs), Ty::Bool],
            };
            if lhs != rhs || *dst_ty != expected_dst {
                return Err(format!(
                    "builtin {builtin:?} requires matching integer arguments and (T, bool) destination"
                ));
            }
            Ok(())
        }
        CoreBuiltin::LeadingZeros | CoreBuiltin::TrailingZeros => {
            let [Ty::Int(_)] = arg_tys else {
                return Err(format!("builtin {builtin:?} requires one integer argument"));
            };
            if *dst_ty != u32_ty {
                return Err(format!("builtin {builtin:?} requires u32 destination"));
            }
            Ok(())
        }
        CoreBuiltin::IsMultipleOf => {
            let [Ty::Int(lhs), Ty::Int(rhs)] = arg_tys else {
                return Err("builtin IsMultipleOf requires two unsigned integer arguments".into());
            };
            if lhs.signed || lhs != rhs || *dst_ty != Ty::Bool {
                return Err(
                    "builtin IsMultipleOf requires matching unsigned integer arguments and bool destination"
                        .into(),
                );
            }
            Ok(())
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct SwitchTarget {
    #[serde(serialize_with = "serialize_u128")]
    pub value: u128,
    pub block: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Terminator {
    Goto {
        block: u32,
    },
    SwitchInt {
        operand: Operand,
        targets: Vec<SwitchTarget>,
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
        destination: Place,
        target: Option<u32>,
        unwind: UnwindAction,
    },
    CallBuiltin {
        builtin: CoreBuiltin,
        args: Vec<Operand>,
        destination: Place,
        target: Option<u32>,
        unwind: UnwindAction,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
    pub cleanup: bool,
}

/// Validated MIR function body enforcing
/// `Trusted.MirSemantics.BodyStaticAdmitted`, constant/retag/storage
/// invariants, and in-bounds local/block references by construction.
///
/// Most checks in [`Body::try_new`] (static `BodyStaticAdmitted` conditions,
/// constant/index/storage bounds, place projections, cast/tuple/assert/builtin
/// typing, and direct destination-type agreement) mirror `BodyStaticAdmitted`
/// and `WellFormed` in `Trusted.MirSemantics` for fail-fast defense in depth;
/// full runtime operand and terminator typing is enforced by `WellFormed`. By
/// contrast, [`check_use_retag`] is the sole soundness guard for erasing
/// `WithRetag::Yes` in `lean.rs`, because `Trusted.MirAst.Rvalue.use` carries
/// no retag field (vacuous today while every admitted [`Ty`] variant is
/// retag-noop, but load-bearing for any future reference-bearing [`Ty`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Body {
    arg_count: usize,
    is_unsafe: bool,
    local_tys: Vec<Ty>,
    blocks: Vec<Block>,
    /// Source contract key, attached to the same body produced for its DefId.
    /// Inventory indices remain navigation metadata; this value enters the
    /// theorem subject and selects the reviewed unsafe caller requirements.
    identity: String,
}

fn check_operand<'a>(local_tys: &'a [Ty], op: &'a Operand) -> Result<&'a Ty, String> {
    match op {
        Operand::Copy { place } | Operand::Move { place } => {
            project_place_ty(local_tys, place, "operand")
        }
        Operand::Constant { ty, lit } => {
            validate_constant(ty, *lit)?;
            Ok(ty)
        }
    }
}

impl Body {
    pub fn try_new(
        arg_count: usize,
        is_unsafe: bool,
        local_tys: Vec<Ty>,
        blocks: Vec<Block>,
        identity: String,
    ) -> Result<Self, String> {
        if identity.is_empty() {
            return Err("captured function identity must not be empty".into());
        }
        if blocks.is_empty() {
            return Err("MIR body contains no basic blocks".into());
        }
        if arg_count >= local_tys.len() {
            return Err(format!(
                "argument count {arg_count} out of bounds for {} locals",
                local_tys.len()
            ));
        }
        for local_ty in &local_tys {
            validate_ty(local_ty)?;
        }
        fn check_local<'a>(local_tys: &'a [Ty], local: u32, role: &str) -> Result<&'a Ty, String> {
            local_tys
                .get(local as usize)
                .ok_or_else(|| format!("{role} local {local} out of bounds"))
        }
        let num_blocks = blocks.len();
        let check_block = |target: u32| -> Result<(), String> {
            if (target as usize) >= num_blocks {
                return Err(format!(
                    "target basic block {target} out of bounds for {num_blocks} blocks"
                ));
            }
            Ok(())
        };
        let check_unwind = |unwind: UnwindAction| -> Result<(), String> {
            if let UnwindAction::Cleanup { block } = unwind {
                check_block(block)?;
            }
            Ok(())
        };
        for block in &blocks {
            for stmt in &block.statements {
                match stmt {
                    Statement::Assign { place, value } => {
                        let dst_ty = project_place_ty(&local_tys, place, "assignment")?;
                        match value {
                            Rvalue::Unit => {
                                if *dst_ty != Ty::Unit {
                                    return Err(
                                        "unit aggregate requires unit destination place".into()
                                    );
                                }
                            }
                            Rvalue::Use {
                                operand,
                                with_retag,
                            } => {
                                check_use_retag(dst_ty, *with_retag)?;
                                let op_ty = check_operand(&local_tys, operand)?;
                                if op_ty != dst_ty {
                                    return Err(
                                        "use rvalue operand type disagrees with destination place"
                                            .into(),
                                    );
                                }
                            }
                            Rvalue::Unary { op, operand } => {
                                let op_ty = check_operand(&local_tys, operand)?;
                                match op {
                                    UnOp::Not => {
                                        if !matches!(op_ty, Ty::Bool | Ty::Int(_)) {
                                            return Err(
                                                "unary Not requires bool or integer operand".into(),
                                            );
                                        }
                                    }
                                    UnOp::Neg => {
                                        if !matches!(op_ty, Ty::Int(IntTy { signed: true, .. })) {
                                            return Err(
                                                "unary Neg requires signed integer operand".into(),
                                            );
                                        }
                                    }
                                }
                                if op_ty != dst_ty {
                                    return Err(
                                        "unary rvalue operand type disagrees with destination place"
                                            .into(),
                                    );
                                }
                            }
                            Rvalue::Binary { op, left, right } => {
                                let lhs_ty = check_operand(&local_tys, left)?;
                                let rhs_ty = check_operand(&local_tys, right)?;
                                if op.is_with_overflow() {
                                    let (Ty::Int(l), Ty::Int(r)) = (lhs_ty, rhs_ty) else {
                                        return Err(
                                            "overflowing binary op requires integer operands"
                                                .into(),
                                        );
                                    };
                                    let expected_dst = Ty::Tuple {
                                        fields: vec![Ty::Int(*l), Ty::Bool],
                                    };
                                    if l != r || *dst_ty != expected_dst {
                                        return Err(
                                            "overflowing binary op destination must be (T, bool)"
                                                .into(),
                                        );
                                    }
                                }
                            }
                            Rvalue::Cast {
                                cast_kind: CastKind::IntToInt,
                                operand,
                                ty,
                            } => {
                                validate_ty(ty)?;
                                let src_ty = check_operand(&local_tys, operand)?;
                                if !matches!(src_ty, Ty::Int(_) | Ty::Bool) {
                                    return Err(
                                        "IntToInt cast requires integer or bool source operand"
                                            .into(),
                                    );
                                }
                                if !matches!(ty, Ty::Int(_)) {
                                    return Err("IntToInt cast requires integer target type".into());
                                }
                                if ty != dst_ty {
                                    return Err(
                                        "cast target type disagrees with destination place".into(),
                                    );
                                }
                            }
                            Rvalue::AggregateTuple { operands } => {
                                if operands.is_empty() {
                                    return Err(
                                        "empty tuple aggregate must use Rvalue::Unit".into()
                                    );
                                }
                                let Ty::Tuple { fields } = dst_ty else {
                                    return Err(
                                        "tuple aggregate requires tuple destination place".into()
                                    );
                                };
                                if operands.len() != fields.len() {
                                    return Err(
                                        "tuple aggregate operand count disagrees with destination"
                                            .into(),
                                    );
                                }
                                for (op, field_ty) in operands.iter().zip(fields.iter()) {
                                    let op_ty = check_operand(&local_tys, op)?;
                                    if op_ty != field_ty {
                                        return Err(
                                            "tuple aggregate operand type disagrees with field"
                                                .into(),
                                        );
                                    }
                                }
                            }
                            Rvalue::Discriminant { place: src } => {
                                if !src.projection.is_empty() {
                                    return Err(
                                        "projected discriminant place is unsupported".into()
                                    );
                                }
                                let Ty::Enum(ety) =
                                    project_place_ty(&local_tys, src, "discriminant")?
                                else {
                                    return Err(
                                        "discriminant rvalue requires a fieldless enum place"
                                            .into(),
                                    );
                                };
                                if *dst_ty != Ty::Int(ety.discr()) {
                                    return Err(
                                        "discriminant rvalue destination type disagrees with enum discriminant"
                                            .into(),
                                    );
                                }
                            }
                        }
                    }
                    Statement::StorageLive { local } => {
                        check_local(&local_tys, *local, "storage annotation")?;
                    }
                    Statement::StorageDead { local } => {
                        // `rustc_const_eval`'s `storage_dead` asserts
                        // `local != mir::RETURN_PLACE` ("Cannot make return
                        // place dead"), and `Trusted.MirSemantics` faults with
                        // `.unsupported` on `StorageDead(0)` in
                        // `evalStatement`.
                        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/stack.rs#L582-L590
                        if *local == 0 {
                            return Err("StorageDead on return place _0 is unsupported".into());
                        }
                        check_local(&local_tys, *local, "storage annotation")?;
                    }
                    Statement::Nop => {}
                }
            }
            match &block.terminator {
                Terminator::Goto { block } => check_block(*block)?,
                Terminator::SwitchInt {
                    operand,
                    targets,
                    otherwise,
                } => {
                    check_operand(&local_tys, operand)?;
                    for target in targets {
                        check_block(target.block)?;
                    }
                    check_block(*otherwise)?;
                }
                Terminator::Ret | Terminator::Unreachable | Terminator::UnwindResume => {}
                Terminator::Assert {
                    cond,
                    msg,
                    target,
                    unwind,
                    ..
                } => {
                    let cond_ty = check_operand(&local_tys, cond)?;
                    if *cond_ty != Ty::Bool {
                        return Err("assert condition operand must have bool type".into());
                    }
                    if let AssertKind::Overflow { op } = msg
                        && !op.is_admitted_assert_overflow_op()
                    {
                        return Err(format!("unsupported assert overflow operator: {op:?}"));
                    }
                    check_block(*target)?;
                    check_unwind(*unwind)?;
                }
                Terminator::Call {
                    args,
                    destination,
                    target,
                    unwind,
                    ..
                } => {
                    for arg in args {
                        check_operand(&local_tys, arg)?;
                    }
                    project_place_ty(&local_tys, destination, "call destination")?;
                    if let Some(next) = target {
                        check_block(*next)?;
                    }
                    check_unwind(*unwind)?;
                }
                Terminator::CallBuiltin {
                    builtin,
                    args,
                    destination,
                    target,
                    unwind,
                } => {
                    let arg_tys = args
                        .iter()
                        .map(|arg| check_operand(&local_tys, arg))
                        .collect::<Result<Vec<_>, _>>()?;
                    let dst_ty = project_place_ty(&local_tys, destination, "builtin destination")?;
                    validate_core_builtin_signature(*builtin, &arg_tys, dst_ty)?;
                    let Some(next) = target else {
                        return Err("diverging core builtin call is unsupported".into());
                    };
                    check_block(*next)?;
                    check_unwind(*unwind)?;
                }
            }
        }
        Ok(Self {
            arg_count,
            is_unsafe,
            local_tys,
            blocks,
            identity,
        })
    }

    pub fn arg_count(&self) -> usize {
        self.arg_count
    }

    pub fn is_unsafe(&self) -> bool {
        self.is_unsafe
    }

    pub fn local_tys(&self) -> &[Ty] {
        &self.local_tys
    }

    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }
}

/// Single authoritative capture scope recorded on [`Program`] and matching
/// the `scope` schema of `cargo-anneal verify`.
///
/// `lean::render` inspects only the enum variant (`SelectedUnit` vs `Crate`)
/// when emitting `Trusted.MirAst.VerificationScope`, so raw selector strings
/// never enter the emitted Lean subject while remaining available in
/// `capture.json` for receipt authentication.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Scope {
    SelectedUnit { roots: BTreeSet<String> },
    Crate,
}

/// Validated captured program enforcing non-empty selected-unit roots,
/// non-empty bodies, pairwise-distinct function identities
/// (`Trusted.MirSemantics.bodiesHaveUniqueIdentities`), and valid direct-call
/// targets/signatures across `bodies`.
#[derive(Debug, Serialize)]
pub struct Program {
    scope: Scope,
    bodies: Vec<Body>,
}

impl Program {
    pub fn try_new(scope: Scope, bodies: Vec<Body>) -> Result<Self, String> {
        if let Scope::SelectedUnit { roots } = &scope
            && roots.is_empty()
        {
            return Err("selected-unit scope must contain at least one root".into());
        }
        if bodies.is_empty() {
            return Err("captured program contains no executable bodies".into());
        }
        let mut identities = BTreeSet::new();
        for body in &bodies {
            if !identities.insert(body.identity.as_str()) {
                return Err(format!(
                    "ambiguous captured function identity: {}",
                    body.identity
                ));
            }
        }
        for body in &bodies {
            for block in &body.blocks {
                if let Terminator::Call {
                    callee,
                    args,
                    destination,
                    ..
                } = &block.terminator
                {
                    let callee_body = bodies.get(*callee as usize).ok_or_else(|| {
                        format!(
                            "call callee index {callee} out of bounds for {} bodies",
                            bodies.len()
                        )
                    })?;
                    if args.len() != callee_body.arg_count() {
                        return Err(format!(
                            "call argument count {} disagrees with callee {} arity {}",
                            args.len(),
                            callee_body.identity(),
                            callee_body.arg_count()
                        ));
                    }
                    let dst_ty =
                        project_place_ty(&body.local_tys, destination, "call destination")?;
                    if *dst_ty != callee_body.local_tys()[0] {
                        return Err(format!(
                            "call destination type disagrees with callee {} return type",
                            callee_body.identity()
                        ));
                    }
                    for (index, arg) in args.iter().enumerate() {
                        let arg_ty = check_operand(&body.local_tys, arg)?;
                        if *arg_ty != callee_body.local_tys()[1 + index] {
                            return Err(format!(
                                "call argument {index} type disagrees with callee {} parameter",
                                callee_body.identity()
                            ));
                        }
                    }
                }
            }
        }
        Ok(Self { scope, bodies })
    }

    pub fn scope(&self) -> &Scope {
        &self.scope
    }

    pub fn bodies(&self) -> &[Body] {
        &self.bodies
    }
}

#[derive(Debug, Serialize)]
pub struct Compiler {
    pub commit: &'static str,
    pub version: &'static str,
    pub sysroot: PathBuf,
}

#[derive(Debug, Serialize)]
pub struct Configuration {
    pub crate_root: PathBuf,
    pub crate_name: String,
    pub edition: String,
    pub target: String,
    pub cfg: Vec<String>,
    pub opt_level: u8,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub panic: &'static str,
    pub pointer_bits: u64,
    pub endian: &'static str,
    pub declared_source_files: Vec<PathBuf>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SourceFile {
    pub path: PathBuf,
    pub sha256: String,
    pub read_kind: &'static str,
}

/// Inventory every compiler definition independently of successful translation.
/// Separate required/selected flags expose unsupported unselected items without
/// implying that a selected-unit proof covers them.
#[derive(Debug, Serialize)]
pub struct CensusItem {
    pub def_id: u32,
    pub path: String,
    pub kind: String,
    pub has_body: bool,
    pub selected: bool,
    pub required: bool,
}

#[derive(Debug, Serialize)]
pub struct SelectedBody {
    pub def_id: u32,
    pub path: String,
    pub body_index: usize,
}

#[derive(Debug, Serialize)]
pub struct Unsupported {
    pub def_id: u32,
    pub path: String,
    pub reason: String,
}

/// Bind the proof subject to the compilation and observed input evidence.
/// JSON metadata supports host authentication and coverage checks, with
/// `program.scope` serving as the single authoritative scope for both receipt
/// authentication and `lean::render`; only the owned `program` constructors
/// are rendered into the Lean subject.
#[derive(Debug, Serialize)]
pub struct Manifest {
    pub schema_version: u32,
    pub compiler: Compiler,
    pub configuration: Configuration,
    pub source_files: Vec<SourceFile>,
    pub census: Vec<CensusItem>,
    pub selected: Vec<SelectedBody>,
    pub unsupported: Vec<Unsupported>,
    pub program: Program,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn body_try_new_rejects_mismatched_use_and_discriminant_destination_types() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let unit_into_u8 = Body::try_new(
            0,
            false,
            vec![u8_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    place: Place::local(0),
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: Ty::Unit,
                            lit: ConstLit::ZeroSized,
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::unit_into_u8".into(),
        )
        .unwrap_err();
        assert!(unit_into_u8.contains("disagrees with destination place"));

        let copy_mismatch = Body::try_new(
            1,
            false,
            vec![Ty::Unit, u8_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    place: Place::local(0),
                    value: Rvalue::Use {
                        operand: Operand::Copy {
                            place: Place::local(1),
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::copy_mismatch".into(),
        )
        .unwrap_err();
        assert!(copy_mismatch.contains("disagrees with destination place"));

        assert!(
            Body::try_new(
                0,
                false,
                vec![Ty::Unit],
                vec![Block {
                    statements: vec![Statement::Assign {
                        place: Place::local(0),
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Unit,
                                lit: ConstLit::ZeroSized,
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                "rust-path-v1::unit_into_unit".into(),
            )
            .is_ok()
        );

        let ety = EnumTy::try_new(
            1,
            IntTy {
                width: IntWidth::Isize,
                signed: true,
            },
            EnumTagRepr::ZeroSized,
            vec![42],
        )
        .unwrap();
        let discr_mismatch = Body::try_new(
            1,
            false,
            vec![u8_ty, Ty::Enum(ety.clone())],
            vec![Block {
                statements: vec![Statement::Assign {
                    place: Place::local(0),
                    value: Rvalue::Discriminant {
                        place: Place::local(1),
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::discr_mismatch".into(),
        )
        .unwrap_err();
        assert!(discr_mismatch.contains("disagrees with enum discriminant"));

        assert!(
            Body::try_new(
                0,
                false,
                vec![Ty::Enum(ety.clone())],
                vec![Block {
                    statements: vec![Statement::Assign {
                        place: Place::local(0),
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Enum(ety),
                                lit: ConstLit::ZeroSized,
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                    cleanup: false,
                }],
                "rust-path-v1::zst_enum_ok".into(),
            )
            .is_ok()
        );
    }

    #[test]
    fn validate_constant_checks_all_ty_and_lit_combinations() {
        let zst_enum = Ty::Enum(
            EnumTy::try_new(
                1,
                IntTy {
                    width: IntWidth::Isize,
                    signed: true,
                },
                EnumTagRepr::ZeroSized,
                vec![0],
            )
            .unwrap(),
        );
        let scalar_enum = Ty::Enum(
            EnumTy::try_new(
                2,
                IntTy {
                    width: IntWidth::Isize,
                    signed: true,
                },
                EnumTagRepr::Scalar(IntTy {
                    width: IntWidth::I8,
                    signed: true,
                }),
                vec![u128::from(u64::MAX), 1],
            )
            .unwrap(),
        );
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let u128_ty = Ty::Int(IntTy {
            width: IntWidth::I128,
            signed: false,
        });

        assert!(validate_constant(&Ty::Unit, ConstLit::ZeroSized).is_ok());
        assert!(validate_constant(&Ty::Unit, ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&Ty::Never, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Never, ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&Ty::Bool, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Bool, ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Bool, ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&Ty::Bool, ConstLit::Scalar { bits: 2 }).is_err());
        assert!(validate_constant(&u8_ty, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&u8_ty, ConstLit::Scalar { bits: 255 }).is_ok());
        assert!(validate_constant(&u8_ty, ConstLit::Scalar { bits: 256 }).is_err());
        assert!(validate_constant(&u128_ty, ConstLit::Scalar { bits: u128::MAX }).is_ok());
        assert!(validate_constant(&zst_enum, ConstLit::ZeroSized).is_ok());
        assert!(validate_constant(&zst_enum, ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&scalar_enum, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&scalar_enum, ConstLit::Scalar { bits: 0xff }).is_ok());
        assert!(validate_constant(&scalar_enum, ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&scalar_enum, ConstLit::Scalar { bits: 2 }).is_err());
        assert!(
            validate_constant(
                &Ty::Tuple {
                    fields: vec![u8_ty]
                },
                ConstLit::ZeroSized
            )
            .is_err()
        );
    }

    #[test]
    fn rvalue_unit_validates_destination_and_serializes_distinct_kind() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let err = Body::try_new(
            0,
            false,
            vec![u8_ty],
            vec![Block {
                statements: vec![Statement::Assign {
                    place: Place::local(0),
                    value: Rvalue::Unit,
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::unit_mismatch".into(),
        )
        .unwrap_err();
        assert!(err.contains("unit aggregate requires unit destination place"));

        let ok = Body::try_new(
            0,
            false,
            vec![Ty::Unit],
            vec![Block {
                statements: vec![Statement::Assign {
                    place: Place::local(0),
                    value: Rvalue::Unit,
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::unit_ok".into(),
        )
        .unwrap();
        let json = serde_json::to_value(&ok).unwrap();
        assert_eq!(
            json["blocks"][0]["statements"][0]["value"],
            serde_json::json!({"kind": "unit"})
        );
    }

    #[test]
    fn retag_guard_refuses_erasing_an_effective_retag() {
        // No admitted `Ty` can carry a reference, so exercise the refusal
        // through the decision that `check_use_retag` delegates to.
        let refusal = admit_retag(false, true).unwrap_err();
        assert!(
            refusal.contains("retagging Use rvalues on reference-bearing types are unsupported"),
            "{refusal}"
        );
        assert!(admit_retag(false, false).is_ok());
        assert!(admit_retag(true, true).is_ok());
        assert!(admit_retag(true, false).is_ok());
        for ty in [
            Ty::Bool,
            Ty::Unit,
            Ty::Never,
            Ty::Int(IntTy {
                width: IntWidth::Isize,
                signed: true,
            }),
            Ty::Tuple {
                fields: vec![Ty::Bool, Ty::Unit],
            },
        ] {
            assert!(ty.is_retag_noop(), "{ty:?}");
            assert!(check_use_retag(&ty, true).is_ok(), "{ty:?}");
        }
    }
}
