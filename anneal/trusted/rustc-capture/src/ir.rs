// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Owned capture data. Metadata and semantic constructors stay separate so that
//! Rust names and paths never become executable Lean source.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use serde::ser::SerializeSeq;
use serde::{Serialize, Serializer};

// Version 4 widens integer widths to include `i128` (`IntWidth::I128`), encodes
// 128-bit bit-pattern fields (`ConstLit::Scalar.bits`, `EnumTy.discriminants`,
// and `Terminator::SwitchInt.targets`) as canonical base-10 strings so JSON
// consumers without arbitrary-precision numbers round-trip `0..=u128::MAX`
// losslessly, adds `Ty::{Char, Ordering, OverflowPair}`, `UnOp::{Not, Neg}`,
// `CastKind::IntToInt`, `BinOp::{Div, Rem, AddWithOverflow, SubWithOverflow,
// MulWithOverflow, Cmp}`, and `Rvalue::{Unary, Cast}`, and enforces static
// operand and destination typing across binary, unary, cast, discriminant, and
// switch operations.
pub const SCHEMA_VERSION: u32 = 4;
pub const COMPILER_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";
pub const COMPILER_VERSION: &str = "1.98.0-nightly (f8a08b688 2026-05-30)";

fn serialize_u128_decimal<S: Serializer>(val: &u128, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&val.to_string())
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
        let bits = self.bits();
        if bits == 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
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
/// than from a compiler index, and refuses any emitted key shared by two local
/// enum definitions in the crate. This constructor does not check how the key
/// was derived.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnumTy {
    id: u32,
    discr_width: IntWidth,
    discr_signed: bool,
    tag_repr: EnumTagRepr,
    #[serde(serialize_with = "serialize_u128_slice_decimal")]
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

/// Whether `bits` is a Unicode scalar value (`0x0000..=0xD7FF` or
/// `0xE000..=0x10FFFF`), matching the Rust Reference ("A value of type `char`
/// is represented as a 32-bit unsigned word in the 0x0000 to 0xD7FF or 0xE000
/// to 0x10FFFF range. It is immediate [undefined behavior] to create a `char`
/// that falls outside this range.") and `Scalar::to_char`.
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/types/char.md?plain=1#L17-L21
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/value.rs#L353-L359
pub const fn is_unicode_scalar(bits: u128) -> bool {
    bits <= 0x10_FFFF && !(0xD800 <= bits && bits <= 0xDFFF)
}

/// Mutability qualifier matching `Trusted.MirAst.Mutability`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Mutability {
    Shared,
    Mut,
}

impl Mutability {
    pub const fn lean_name(self) -> &'static str {
        match self {
            Self::Shared => "shared",
            Self::Mut => "mut",
        }
    }
}

fn serialize_boxed_ty<S: Serializer>(val: &Ty, serializer: S) -> Result<S::Ok, S::Error> {
    let v = serde_json::to_value(val).map_err(serde::ser::Error::custom)?;
    v.serialize(serializer)
}

fn serialize_ty_slice<S: Serializer>(vals: &[Ty], serializer: S) -> Result<S::Ok, S::Error> {
    let mut seq = serializer.serialize_seq(Some(vals.len()))?;
    for val in vals {
        let v = serde_json::to_value(val).map_err(serde::ser::Error::custom)?;
        seq.serialize_element(&v)?;
    }
    seq.end()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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
        #[serde(serialize_with = "serialize_ty_slice")]
        fields: Vec<Ty>,
    },
    Ref {
        mutability: Mutability,
        #[serde(serialize_with = "serialize_boxed_ty")]
        pointee: Box<Ty>,
    },
    RawPtr {
        mutability: Mutability,
        #[serde(serialize_with = "serialize_boxed_ty")]
        pointee: Box<Ty>,
    },
    Slice {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
    },
    RangeTo {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
    },
    RangeFrom {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
    },
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
    /// pointers (`&T`, `&mut T`, `Box<T>`). For reference-free scalar, `char`,
    /// `Ordering`, unit, never, fieldless-enum, raw-pointer, range, and `(int,
    /// bool)` overflow-pair types, `WithRetag::Yes` and `WithRetag::No` have
    /// identical semantics. Any reference-bearing type returns `false` so
    /// capture never erases active retags (`Rvalue::UseRetag` instead).
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
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. } => true,
            Self::Ref { .. } => false,
            Self::Tuple { fields } => fields.iter().all(Self::is_retag_noop),
        }
    }

    /// Whether values of this type are always statically `Sized`.
    ///
    /// In `rustc_const_eval`'s `eval_statement` (`"PlaceMention(place) => {
    /// let _ = self.eval_place(**place)?; }"`) and `local_to_place` (`"let
    /// layout = self.layout_of_local(frame, local, None)?; let place = if
    /// layout.is_sized() { Place::Local { local, offset: None, locals_addr:
    /// frame.locals_addr() } } else { match frame.locals[local].access()? {
    /// Operand::Immediate(_) => bug!(), Operand::Indirect(mplace) =>
    /// Place::Ptr(*mplace), } };"`, where `layout_of_local` indexes
    /// `&frame.locals[local]` without calling `.access()`), and in
    /// `lean-miri`'s `Miri.Interpreter.localToPlace`, evaluating an unprojected
    /// `PlaceMention` of a `Sized` local returns `Place::Local` without reading
    /// memory or checking liveness (an exact operational no-op), whereas an
    /// unsized local accesses its local operand and checks liveness. Unsized
    /// [`Ty`] variants (such as [`Self::Slice`]) return `false` so capture
    /// fails closed rather than rendering `Statement::PlaceMention` as
    /// `StatementKind.nop`.
    /// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/step.rs#L117-L119
    /// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/place.rs#L519-L536
    /// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/stack.rs#L610-L631
    pub fn is_sized(&self) -> bool {
        match self {
            Self::Slice { .. } => false,
            Self::Tuple { fields } => fields.iter().all(Self::is_sized),
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
            | Self::RangeFrom { .. } => true,
        }
    }

    /// Whether this type belongs to the Profile v1 scalar/unit/enum/pair
    /// fragment.
    pub fn is_supported_scalar_or_unit(&self) -> bool {
        matches!(
            self,
            Self::Bool
                | Self::Int(_)
                | Self::Char
                | Self::Ordering
                | Self::Unit
                | Self::Never
                | Self::Enum(_)
                | Self::OverflowPair(_)
        )
    }

    /// Whether this type is admitted as a Profile v2 local type (matching
    /// `Trusted.MirSemantics.isSupportedV2LocalTy`). Forbids nested
    /// references/pointers inside pointees (`&&T`, `*mut &T`, `&[&T]`).
    ///
    /// Also forbids overflow-pair pointees (`&(T, bool)`, `*const (T, bool)`).
    /// The Reference says "Tuples are laid out according to the [`Rust`
    /// representation][`Rust`]." Beyond field alignment and non-overlap,
    /// "There are no other guarantees of data layout made by this
    /// representation." Yet `Trusted.MirSemantics.overflowPairLayout` fixes
    /// one field order and size without a `layout_of` check. So overflow
    /// pairs stay non-addressable locals that hold checked-operator results,
    /// and no pointer can reach their bytes.
    /// https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/type-layout.md#L94
    /// https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/type-layout.md#L184
    pub fn is_supported_v2_local(&self) -> bool {
        match self {
            Self::Bool
            | Self::Int(_)
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Enum(_)
            | Self::OverflowPair(_) => true,
            Self::Tuple { fields } => fields.iter().all(Self::is_supported_v2_local),
            Self::Ref { pointee, .. } | Self::RawPtr { pointee, .. } => match &**pointee {
                Self::Slice { elem } => matches!(&**elem, Self::Int(_)),
                Self::OverflowPair(_) => false,
                other => other.is_supported_scalar_or_unit(),
            },
            Self::RangeTo { elem } | Self::RangeFrom { elem } => {
                **elem
                    == Self::Int(IntTy {
                        width: IntWidth::Isize,
                        signed: false,
                    })
            }
            Self::Slice { .. } => false,
        }
    }

    /// Whether this type is a reference or a tuple containing one, mirroring
    /// `Trusted.MirSemantics.tyHasRefV2`.
    pub fn has_ref_v2(&self) -> bool {
        match self {
            Self::Ref { .. } => true,
            Self::Tuple { fields } => fields.iter().any(Self::has_ref_v2),
            _ => false,
        }
    }

    /// Whether this type is a raw pointer or a tuple containing one, mirroring
    /// `Trusted.MirSemantics.tyHasRawPtrV2`.
    pub fn has_raw_ptr_v2(&self) -> bool {
        match self {
            Self::RawPtr { .. } => true,
            Self::Tuple { fields } => fields.iter().any(Self::has_raw_ptr_v2),
            _ => false,
        }
    }

    /// Whether this type uses Profile v2 extensions.
    pub fn is_profile_v2(&self) -> bool {
        match self {
            Self::Tuple { .. }
            | Self::Ref { .. }
            | Self::RawPtr { .. }
            | Self::Slice { .. }
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. } => true,
            Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Int(_)
            | Self::Enum(_)
            | Self::OverflowPair(_) => false,
        }
    }

    /// Record every nominal [`EnumTy::id`] embedded in this type.
    ///
    /// Keep the match exhaustive so any future compound type variant must
    /// recurse into its constituent types rather than hiding an enum key from
    /// collision checks.
    pub fn collect_enum_ids(&self, out: &mut BTreeSet<u32>) {
        match self {
            Self::Enum(ety) => {
                out.insert(ety.id());
            }
            Self::Tuple { fields } => {
                for f in fields {
                    f.collect_enum_ids(out);
                }
            }
            Self::Ref { pointee, .. } | Self::RawPtr { pointee, .. } => {
                pointee.collect_enum_ids(out);
            }
            Self::Slice { elem } | Self::RangeTo { elem } | Self::RangeFrom { elem } => {
                elem.collect_enum_ids(out);
            }
            Self::Bool
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Int(_)
            | Self::OverflowPair(_) => {}
        }
    }
}

/// Constant literal payload matching `Trusted.MirAst.ConstLit` 1-to-1.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ConstLit {
    ZeroSized,
    Scalar {
        #[serde(serialize_with = "serialize_u128_decimal")]
        bits: u128,
    },
}

/// Validate that `with_retag` is admitted for destination type `dst_ty`.
///
/// `lean.rs` renders `Rvalue::Use` without its retag flag, so the flag may be
/// erased only when [`Ty::is_retag_noop`] holds for the destination type
/// (retagging `Use` on reference-bearing types uses [`Rvalue::UseRetag`]).
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

/// Validate that an unprojected `PlaceMention` is an operational no-op for
/// `local_ty`.
///
/// `lean.rs` renders an unprojected [`Statement::PlaceMention`] as
/// `Trusted.MirAst.StatementKind.nop`, which is sound only when the place has
/// no projections (enforced in `extract.rs`) and its local type is `Sized`
/// (`local_to_place` neither loads memory nor checks liveness; unsized
/// [`Ty::Slice`] returns `false` from [`Ty::is_sized`]).
pub fn check_place_mention(local_ty: &Ty) -> Result<(), String> {
    admit_place_mention(local_ty.is_sized())
}

/// Refuse rendering a `PlaceMention` of an unsized local as a no-op.
fn admit_place_mention(is_sized: bool) -> Result<(), String> {
    if !is_sized {
        return Err("PlaceMention on unsized locals is unsupported".into());
    }
    Ok(())
}

/// Validate a typed constant literal against `evalConstLit` invariants.
pub fn validate_constant(ty: &Ty, lit: ConstLit) -> Result<(), String> {
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
        (Ty::OverflowPair(_), _) => Err("overflow-pair tuple constants are unsupported".into()),
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
        (Ty::Char, ConstLit::ZeroSized) => {
            Err("ZeroSized constant requires unit or zero-sized enum type".into())
        }
        (Ty::Char, ConstLit::Scalar { bits }) => {
            if is_unicode_scalar(bits) {
                Ok(())
            } else {
                Err(format!(
                    "invalid char constant {bits:#x}: outside Unicode scalar range"
                ))
            }
        }
        (Ty::Ordering, ConstLit::ZeroSized) => {
            Err("ZeroSized constant requires unit or zero-sized enum type".into())
        }
        (Ty::Ordering, ConstLit::Scalar { bits }) => {
            // `core::cmp::Ordering` is `#[repr(i8)]` whose "three variants
            // `Less`/`Equal`/`Greater` remain `-1_i8`/`0_i8`/`+1_i8`
            // respectively" (`0xff`, `0`, `1` as 8-bit unsigned tags).
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/cmp.rs#L400-L415
            if matches!(bits, 0 | 1 | 0xff) {
                Ok(())
            } else {
                Err(format!("invalid Ordering tag constant {bits:#x}"))
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
        (
            Ty::Tuple { .. }
            | Ty::Ref { .. }
            | Ty::RawPtr { .. }
            | Ty::Slice { .. }
            | Ty::RangeTo { .. }
            | Ty::RangeFrom { .. },
            _,
        ) => Err(format!("constants of compound/pointer type {ty:?} are unsupported")),
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PlaceElem {
    Deref,
    Field { index: usize, ty: Ty },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Place {
    pub local: u32,
    pub projection: Vec<PlaceElem>,
}

impl Place {
    pub fn collect_enum_ids(&self, out: &mut BTreeSet<u32>) {
        for elem in &self.projection {
            if let PlaceElem::Field { ty, .. } = elem {
                ty.collect_enum_ids(out);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Operand {
    Copy { local: u32 },
    Move { local: u32 },
    CopyPlace { place: Place },
    MovePlace { place: Place },
    Constant { ty: Ty, lit: ConstLit },
}

impl Operand {
    fn collect_enum_ids(&self, out: &mut BTreeSet<u32>) {
        match self {
            Self::Copy { .. } | Self::Move { .. } => {}
            Self::CopyPlace { place } | Self::MovePlace { place } => place.collect_enum_ids(out),
            Self::Constant { ty, .. } => ty.collect_enum_ids(out),
        }
    }

    pub fn is_profile_v2(&self) -> bool {
        match self {
            Self::CopyPlace { .. } | Self::MovePlace { .. } => true,
            Self::Copy { .. } | Self::Move { .. } => false,
            Self::Constant { ty, .. } => ty.is_profile_v2(),
        }
    }
}

/// Admitted MIR unary operators (`rustc_middle::mir::UnOp`): "The `!`
/// operator for logical inversion", "The `-` operator for negation", and
/// `PtrMetadata`, which "Gets the metadata `M` from a
/// `*const`/`*mut`/`&`/`&mut` to `impl Pointee<Metadata = M>`" ("a `()`
/// from `*const i32`, a `usize` from `&mut [u8]`"), matching
/// `Trusted.MirAst.UnOp`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum UnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Admitted MIR cast kinds (`rustc_middle::mir::CastKind::{IntToInt,
/// PtrToPtr}` and `PointerWithExposedProvenance`, "An address-to-pointer cast
/// that picks up an exposed provenance", as `IntToPtr`), matching
/// `Trusted.MirAst.CastKind`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CastKind {
    IntToInt,
    PtrToPtr,
    IntToPtr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BinOp {
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    AddWithOverflow,
    SubWithOverflow,
    MulWithOverflow,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Cmp,
    Offset,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Rvalue {
    Use {
        operand: Operand,
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
        local: u32,
    },
    Ref {
        mutability: Mutability,
        place: Place,
    },
    AddressOf {
        mutability: Mutability,
        place: Place,
    },
    AggregateTuple {
        fields: Vec<Operand>,
    },
    AggregateRangeTo {
        elem_ty: Ty,
        end: Operand,
    },
    AggregateRangeFrom {
        elem_ty: Ty,
        start: Operand,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Statement {
    Assign { local: u32, value: Rvalue },
    AssignPlace { place: Place, value: Rvalue },
    StorageLive { local: u32 },
    StorageDead { local: u32 },
    PlaceMention { local: u32 },
    Nop,
}

/// Compilation crate type explicitly authorized for capture.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CrateType {
    #[default]
    Lib,
    Bin,
}

impl CrateType {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Lib => "lib",
            Self::Bin => "bin",
        }
    }
}

/// Panic unwinding strategy explicitly configured for capture.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PanicStrategy {
    #[default]
    Unwind,
    Abort,
}

impl PanicStrategy {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unwind => "unwind",
            Self::Abort => "abort",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AssertKind {
    Overflow { op: BinOp },
    OverflowNeg,
    DivByZero,
    RemByZero,
    BoundsCheck,
    MisalignedPtrDeref,
    NullPtrDeref,
}

/// Unwind action of a captured `Assert` or returning call, matching the
/// non-cleanup constructors of `Trusted.MirAst.UnwindAction` 1:1.
///
/// Upstream `UnwindAction::Continue` is "No action is to be taken. Continue
/// unwinding.", `Unreachable` "Triggers undefined behavior if unwind
/// happens.", and `Terminate(UnwindTerminateReason)` "Terminates the
/// execution if unwind happens." The terminate reason is not recorded
/// because the Lean AST has no reason field. `Cleanup(BasicBlock)` is refused
/// at capture time and has no variant here.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1027-L1055
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum UnwindAction {
    Continue,
    Unreachable,
    Terminate,
}

impl UnwindAction {
    /// The `Trusted.MirAst.UnwindAction` constructor name.
    pub const fn lean_name(self) -> &'static str {
        match self {
            Self::Continue => "continue_",
            Self::Unreachable => "unreachable",
            Self::Terminate => "terminate",
        }
    }
}

/// The closed table of sysroot `core` calls that Profile v2 executes,
/// matching `Trusted.MirAst.CoreCallOp` 1:1. `extract::core_call_op` maps
/// each entry from one pinned `library/core` definition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CoreCallOp {
    SliceLen,
    SliceGetUncheckedRangeTo,
    SliceGetUncheckedRangeFrom,
    PtrAdd {
        mutability: Mutability,
        pointee: Ty,
    },
    UsizeUncheckedSub,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Terminator {
    Goto {
        block: u32,
    },
    SwitchInt {
        operand: Operand,
        #[serde(serialize_with = "serialize_switch_targets_decimal")]
        targets: Vec<(u128, u32)>,
        otherwise: u32,
    },
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
        target: u32,
        unwind: UnwindAction,
    },
    Ret,
    Unreachable,
    Unsupported,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

/// Check static operand and destination typing for [`Rvalue::Binary`], matching
/// `Trusted.MirSemantics.evalBinOp` and `writePlace`.
fn check_binary_types(op: BinOp, l_ty: &Ty, r_ty: &Ty, dst_ty: &Ty) -> Result<(), String> {
    match op {
        BinOp::Shl | BinOp::Shr => match (l_ty, r_ty) {
            (Ty::Int(l_ity), Ty::Int(_)) if *dst_ty == Ty::Int(*l_ity) => Ok(()),
            _ => Err(format!(
                "invalid shift operand or destination types: ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
            )),
        },
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => match (l_ty, r_ty) {
            (Ty::Int(l_ity), Ty::Int(r_ity)) if l_ity == r_ity && *dst_ty == Ty::Int(*l_ity) => {
                Ok(())
            }
            _ => Err(format!(
                "invalid arithmetic operand or destination types for {op:?}: \
                 ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
            )),
        },
        BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow => {
            match (l_ty, r_ty) {
                (Ty::Int(l_ity), Ty::Int(r_ity))
                    if l_ity == r_ity && *dst_ty == Ty::OverflowPair(*l_ity) =>
                {
                    Ok(())
                }
                _ => Err(format!(
                    "invalid overflowing arithmetic types for {op:?}: \
                     ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
                )),
            }
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => match (l_ty, r_ty) {
            (Ty::Int(l_ity), Ty::Int(r_ity)) if l_ity == r_ity && *dst_ty == Ty::Int(*l_ity) => {
                Ok(())
            }
            (Ty::Bool, Ty::Bool) if *dst_ty == Ty::Bool => Ok(()),
            _ => Err(format!(
                "invalid bitwise operand or destination types for {op:?}: \
                 ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
            )),
        },
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            if l_ty == r_ty
                && matches!(l_ty, Ty::Int(_) | Ty::Bool | Ty::Char)
                && *dst_ty == Ty::Bool
            {
                Ok(())
            } else {
                Err(format!(
                    "invalid comparison operand or destination types for {op:?}: \
                     ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
                ))
            }
        }
        // `BinOp::Cmp` "is supported only on the integer types and `char`,
        // always returning [`rustc_hir::LangItem::OrderingEnum`]".
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1697-L1706
        BinOp::Cmp => {
            if l_ty == r_ty && matches!(l_ty, Ty::Int(_) | Ty::Char) && *dst_ty == Ty::Ordering {
                Ok(())
            } else {
                Err(format!(
                    "invalid three-way comparison types: ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
                ))
            }
        }
        BinOp::Offset => match (l_ty, r_ty) {
            (Ty::RawPtr { pointee, .. }, Ty::Int(IntTy { width: IntWidth::Isize, signed: true }))
                if pointee.is_sized() && dst_ty == l_ty =>
            {
                Ok(())
            }
            _ => Err(format!(
                "invalid pointer offset types: ({l_ty:?}, {r_ty:?}) -> {dst_ty:?}"
            )),
        },
    }
}

/// Check static operand and destination typing for [`Rvalue::Unary`], matching
/// `Trusted.MirSemantics.evalUnOp` and `UnOp.ptrMetadata`.
fn check_unary_types(op: UnOp, op_ty: &Ty, dst_ty: &Ty) -> Result<(), String> {
    if op == UnOp::PtrMetadata {
        return match op_ty {
            Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } => match &**pointee {
                Ty::Slice { .. }
                    if *dst_ty
                        == Ty::Int(IntTy {
                            width: IntWidth::Isize,
                            signed: false,
                        }) =>
                {
                    Ok(())
                }
                pt if pt.is_sized() && *dst_ty == Ty::Unit => Ok(()),
                _ => Err(format!(
                    "invalid PtrMetadata destination {dst_ty:?} for {op_ty:?}"
                )),
            },
            _ => Err(format!("invalid PtrMetadata operand type {op_ty:?}")),
        };
    }
    if op_ty != dst_ty {
        return Err("unary rvalue operand type disagrees with destination local".into());
    }
    match (op, op_ty) {
        (UnOp::Not, Ty::Bool | Ty::Int(_)) => Ok(()),
        (UnOp::Neg, Ty::Int(IntTy { signed: true, .. })) => Ok(()),
        _ => Err(format!("invalid unary operator {op:?} for type {op_ty:?}")),
    }
}

/// Refuse a pointer to an overflow pair `(T, bool)`, which must stay a
/// non-addressable local (see [`Ty::is_supported_v2_local`]).
/// [`validate_local_tys`] already refuses every local typed as such a
/// pointer; this check names the cause at the rvalue or cast.
fn refuse_overflow_pair_pointee(pointee: &Ty, what: &str) -> Result<(), String> {
    if matches!(pointee, Ty::OverflowPair(_)) {
        return Err(format!(
            "{what} to an overflow pair `(T, bool)` is unsupported: its \
             `#[repr(Rust)]` tuple layout is unchecked, so overflow pairs are not addressable"
        ));
    }
    Ok(())
}

/// Check static source, target, and destination typing for [`Rvalue::Cast`].
///
/// `IntToInt` matches `cast_from_int_like` ("can take 'int-like' input type
/// (basically everything with a scalar layout) to int/float/char types",
/// where `ty::Char` executes `u8::try_from(v).unwrap().into()`) and
/// `Trusted.MirSemantics.castTypesValid` / `evalIntToIntCast`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/cast.rs#L258-L312
///
/// `PtrToPtr` matches `ptr_to_ptr` ("Thin or wide pointer that just has the
/// ptr kind of target type changed"), admitting only raw-pointer sources
/// with both pointees sized or both the same slice, and never a `*const T`
/// to `*mut T` cast, mirroring `Trusted.MirSemantics.evalPtrToPtrCastV2`:
/// Profile v2 models no aliasing rules, and that cast is how a body could
/// write to an immutable binding. Reference sources stay
/// refused: upstream says "reference-to-raw-ptr casts are translated into
/// `&raw mut/const *r`, i.e., they are not actually casts", and such a body
/// would mix reference and raw-pointer locals, which [`validate_local_tys`]
/// refuses. `IntToPtr` (`PointerWithExposedProvenance`) admits only a
/// `usize` source and a sized raw-pointer target, matching
/// `pointer_with_exposed_provenance_cast` ("First cast to usize.").
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/cast.rs#L189-L218
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_const_eval/src/interpret/cast.rs#L240-L256
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1499-L1500
fn check_cast_types(kind: CastKind, src_ty: &Ty, cast_ty: &Ty, dst_ty: &Ty) -> Result<(), String> {
    if cast_ty != dst_ty {
        return Err("cast target type disagrees with destination local".into());
    }
    match (kind, src_ty, cast_ty) {
        (CastKind::IntToInt, Ty::Int(_) | Ty::Bool | Ty::Char, Ty::Int(_)) => Ok(()),
        (
            CastKind::IntToInt,
            Ty::Int(IntTy {
                width: IntWidth::I8,
                signed: false,
            }),
            Ty::Char,
        ) => Ok(()),
        (CastKind::PtrToPtr, Ty::Ref { .. }, _) => Err(format!(
            "PtrToPtr cast from reference {src_ty:?} is unsupported: runtime MIR \
             expresses reference-to-raw-pointer conversion as `&raw (*r)`, \
             and Profile v2 refuses bodies mixing references and raw pointers"
        )),
        (
            CastKind::PtrToPtr,
            Ty::RawPtr {
                mutability: Mutability::Shared,
                ..
            },
            Ty::RawPtr {
                mutability: Mutability::Mut,
                ..
            },
        ) => Err(format!(
            "PtrToPtr cast from {src_ty:?} to {cast_ty:?} is unsupported: \
             Profile v2 models no aliasing rules, so it refuses `*const T` to \
             `*mut T` casts, which could write to an immutable binding"
        )),
        (
            CastKind::PtrToPtr,
            Ty::RawPtr { pointee: src_pt, .. },
            Ty::RawPtr { pointee: dst_pt, .. },
        ) => match (&**src_pt, &**dst_pt) {
            (pt @ Ty::OverflowPair(_), _) | (_, pt @ Ty::OverflowPair(_)) => {
                refuse_overflow_pair_pointee(pt, "PtrToPtr cast")
            }
            (Ty::Slice { elem: e1 }, Ty::Slice { elem: e2 }) if e1 == e2 => Ok(()),
            (s, d) if s.is_sized() && d.is_sized() => Ok(()),
            _ => Err(format!(
                "unsupported PtrToPtr cast from {src_ty:?} to {cast_ty:?}"
            )),
        },
        (
            CastKind::IntToPtr,
            Ty::Int(IntTy {
                width: IntWidth::Isize,
                signed: false,
            }),
            Ty::RawPtr { pointee, .. },
        ) if pointee.is_sized() => Ok(()),
        _ => Err(format!(
            "unsupported cast {kind:?} from {src_ty:?} to {cast_ty:?}"
        )),
    }
}

/// Check static operand and case-value typing for [`Terminator::SwitchInt`],
/// matching `Trusted.MirSemantics.evalTerminator`.
fn check_switch_targets(discr_ty: &Ty, targets: &[(u128, u32)]) -> Result<(), String> {
    match discr_ty {
        Ty::Int(ity) => {
            let mask = ity.width.mask();
            for &(val, _) in targets {
                if val > mask {
                    return Err(format!(
                        "SwitchInt case {val:#x} exceeds {}-bit operand width",
                        ity.width.bits()
                    ));
                }
            }
            Ok(())
        }
        Ty::Bool => {
            for &(val, _) in targets {
                if val > 1 {
                    return Err(format!("invalid Boolean SwitchInt case {val:#x}"));
                }
            }
            Ok(())
        }
        Ty::Char => {
            for &(val, _) in targets {
                if !is_unicode_scalar(val) {
                    return Err(format!(
                        "invalid char SwitchInt case {val:#x}: outside Unicode scalar range"
                    ));
                }
            }
            Ok(())
        }
        Ty::OverflowPair(_) => {
            if targets.is_empty() {
                Ok(())
            } else {
                Err("non-empty SwitchInt branches on overflow-pair tuple are unsupported".into())
            }
        }
        Ty::Unit
        | Ty::Never
        | Ty::Ordering
        | Ty::Enum(_)
        | Ty::Tuple { .. }
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::Slice { .. }
        | Ty::RangeTo { .. }
        | Ty::RangeFrom { .. } => Err(format!(
            "SwitchInt operand type {discr_ty:?} is not primitive-switchable"
        )),
    }
}

/// Validates that every local in a MIR body is `Sized` and belongs to the
/// Profile v2 local type fragment
/// (`Trusted.MirSemantics.isSupportedV2LocalTy`).
pub(crate) fn validate_local_tys(local_tys: &[Ty]) -> Result<(), String> {
    for (idx, lty) in local_tys.iter().enumerate() {
        if !lty.is_sized() {
            return Err(format!("unsized local _{idx} of type {lty:?} is unsupported"));
        }
        if !lty.is_supported_v2_local() {
            return Err(format!(
                "local _{idx} of type {lty:?} is outside the Profile v2 type fragment"
            ));
        }
    }
    // Mirrors `Trusted.MirSemantics.bodyMixesRefsAndRawPtrsV2`: Profile v2 has
    // no aliasing model, so it admits no body that could derive references
    // from raw pointers or access referenced memory through them.
    if local_tys.iter().any(Ty::has_ref_v2) && local_tys.iter().any(Ty::has_raw_ptr_v2) {
        return Err("body mixes reference and raw-pointer locals, which Profile v2 \
             refuses because it does not model Rust's pointer aliasing rules"
            .to_string());
    }
    Ok(())
}

/// Validated MIR function body enforcing
/// `Trusted.MirSemantics.BodyStaticAdmitted`, constant/retag/storage
/// invariants, static rvalue/terminator typing, and in-bounds local/block
/// references by construction.
///
/// Most checks in [`Body::try_new`] (static `BodyStaticAdmitted` conditions,
/// constant/index/storage bounds, and operand/destination typing for
/// `Rvalue` and `Terminator::SwitchInt`) mirror `BodyStaticAdmitted` and
/// `WellFormed` in `Trusted.MirSemantics` for fail-fast defense in depth; full
/// runtime safety (such as division-by-zero and initialized-local checks) is
/// enforced by `WellFormed`. By contrast, [`check_use_retag`] is the sole
/// soundness guard for erasing `WithRetag::Yes` in `lean.rs`, because
/// `Trusted.MirAst.Rvalue.use` carries no retag field (load-bearing for
/// reference-bearing types such as [`Ty::Ref`], whose retagging `Use`
/// rvalues are captured as [`Rvalue::UseRetag`] instead).
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
        validate_local_tys(&local_tys)?;
        fn check_local<'a>(local_tys: &'a [Ty], local: u32, role: &str) -> Result<&'a Ty, String> {
            local_tys
                .get(local as usize)
                .ok_or_else(|| format!("{role} local {local} out of bounds"))
        }
        fn check_place(
            local_tys: &[Ty],
            place: &Place,
            role: &str,
            allow_unsized_deref: bool,
            require_mut_deref: bool,
        ) -> Result<Ty, String> {
            let base = check_local(local_tys, place.local, role)?;
            let mut cur = base.clone();
            let mut saw_deref = false;
            for (step, elem) in place.projection.iter().enumerate() {
                match elem {
                    PlaceElem::Deref => {
                        if saw_deref || step != 0 {
                            return Err("nested or post-field deref projections are unsupported".into());
                        }
                        saw_deref = true;
                        match &cur {
                            Ty::Ref { mutability, pointee } | Ty::RawPtr { mutability, pointee } => {
                                if require_mut_deref && *mutability != Mutability::Mut {
                                    return Err("cannot write through shared pointer/reference".into());
                                }
                                if !allow_unsized_deref && !pointee.is_sized() {
                                    return Err(format!(
                                        "unsized deref of {pointee:?} is unsupported here"
                                    ));
                                }
                                cur = (**pointee).clone();
                            }
                            _ => return Err(format!("cannot deref non-pointer local type {cur:?}")),
                        }
                    }
                    PlaceElem::Field { index, ty } => {
                        if saw_deref {
                            return Err("field projection after deref is unsupported".into());
                        }
                        let usize_ty = Ty::Int(IntTy {
                            width: IntWidth::Isize,
                            signed: false,
                        });
                        let expected_field = match &cur {
                            Ty::Tuple { fields } => fields.get(*index).cloned(),
                            Ty::OverflowPair(ity) if *index == 0 => Some(Ty::Int(*ity)),
                            Ty::OverflowPair(_) if *index == 1 => Some(Ty::Bool),
                            Ty::RangeTo { elem: e } | Ty::RangeFrom { elem: e }
                                if *index == 0 && **e == usize_ty =>
                            {
                                Some(usize_ty)
                            }
                            _ => None,
                        };
                        let Some(expected) = expected_field else {
                            return Err(format!("unsupported field {index} projection on {cur:?}"));
                        };
                        if expected != *ty {
                            return Err(format!(
                                "field {index} projection type {ty:?} disagrees with {expected:?}"
                            ));
                        }
                        cur = expected;
                    }
                }
            }
            Ok(cur)
        }
        fn check_operand<'a>(local_tys: &'a [Ty], op: &'a Operand) -> Result<Ty, String> {
            match op {
                Operand::Copy { local } | Operand::Move { local } => {
                    Ok(check_local(local_tys, *local, "operand")?.clone())
                }
                Operand::CopyPlace { place } => check_place(local_tys, place, "operand", false, false),
                // `Trusted.MirSemantics.readPlaceV2` models a move out of one
                // field of a tuple local (`move (_t.1)`, which rustc emits for
                // overflow checks) by deinitializing just that field. The
                // local is not caller memory, so a verified body, which never
                // reads the moved field again, behaves the same whether or
                // not MIR deinitializes it. Every other projected move
                // (`move (*p)`, nested fields, ranges) stays `.unsupported`:
                // moving out of `*p` may deinitialize caller memory, which
                // MIR leaves unspecified. Refuse those here so capture fails
                // instead of emitting an obligation no execution can
                // discharge.
                Operand::MovePlace { place }
                    if matches!(place.projection.as_slice(), [PlaceElem::Field { .. }])
                        && matches!(
                            local_tys.get(place.local as usize),
                            Some(Ty::Tuple { .. } | Ty::OverflowPair(_))
                        ) =>
                {
                    check_place(local_tys, place, "operand", false, false)
                }
                Operand::MovePlace { .. } => Err(
                    "projected move operands other than a field of a tuple local \
                     (`move (*p)`, nested fields) are unsupported: Profile v2 models \
                     partial deinitialization by a move only for tuple locals"
                        .into(),
                ),
                Operand::Constant { ty, lit } => {
                    validate_constant(ty, *lit)?;
                    Ok(ty.clone())
                }
            }
        }
        fn check_rvalue(local_tys: &[Ty], dst_ty: &Ty, value: &Rvalue) -> Result<(), String> {
            let usize_ty = Ty::Int(IntTy {
                width: IntWidth::Isize,
                signed: false,
            });
            match value {
                Rvalue::Use {
                    operand,
                    with_retag,
                } => {
                    check_use_retag(dst_ty, *with_retag)?;
                    let op_ty = check_operand(local_tys, operand)?;
                    if &op_ty != dst_ty {
                        return Err(
                            "use rvalue operand type disagrees with destination local".into()
                        );
                    }
                }
                Rvalue::UseRetag { operand } => {
                    if dst_ty.is_retag_noop() {
                        return Err("UseRetag requires a reference-bearing destination type".into());
                    }
                    let op_ty = check_operand(local_tys, operand)?;
                    if &op_ty != dst_ty {
                        return Err(
                            "retag use operand type disagrees with destination local".into()
                        );
                    }
                }
                Rvalue::Binary { op, left, right } => {
                    let l_ty = check_operand(local_tys, left)?;
                    let r_ty = check_operand(local_tys, right)?;
                    check_binary_types(*op, &l_ty, &r_ty, dst_ty)?;
                }
                Rvalue::Unary { op, operand } => {
                    let op_ty = check_operand(local_tys, operand)?;
                    check_unary_types(*op, &op_ty, dst_ty)?;
                }
                Rvalue::Cast {
                    cast_kind,
                    operand,
                    ty,
                } => {
                    let src_ty = check_operand(local_tys, operand)?;
                    check_cast_types(*cast_kind, &src_ty, ty, dst_ty)?;
                }
                Rvalue::Discriminant { local: src } => {
                    let expected_discr = match check_local(local_tys, *src, "discriminant")? {
                        Ty::Enum(ety) => ety.discr(),
                        Ty::Ordering => IntTy {
                            width: IntWidth::I8,
                            signed: true,
                        },
                        _ => {
                            return Err(
                                "discriminant rvalue requires a fieldless enum or Ordering local"
                                    .into(),
                            );
                        }
                    };
                    if *dst_ty != Ty::Int(expected_discr) {
                        return Err(
                            "discriminant rvalue destination type disagrees with enum discriminant"
                                .into(),
                        );
                    }
                }
                Rvalue::Ref { mutability, place } => {
                    if place.projection.len() > 1
                        || (place.projection.len() == 1
                            && !matches!(place.projection[0], PlaceElem::Deref))
                    {
                        return Err("unsupported projection in Rvalue::Ref".into());
                    }
                    if place.projection.len() == 1 {
                        let base = check_local(local_tys, place.local, "ref")?;
                        // `&(*p)` for a raw pointer `p` would derive a
                        // reference from a raw pointer, which needs the
                        // aliasing model that Profile v2 lacks. Such a body
                        // mixes reference and raw-pointer locals and is
                        // already refused by `validate_local_tys`; refuse it
                        // here too rather than keep an unreachable rule.
                        if matches!(base, Ty::RawPtr { .. }) {
                            return Err(
                                "Rvalue::Ref through a raw pointer is unsupported: \
                                 Profile v2 does not derive references from raw pointers"
                                    .into(),
                            );
                        }
                        if *mutability == Mutability::Mut
                            && matches!(
                                base,
                                Ty::Ref {
                                    mutability: Mutability::Shared,
                                    ..
                                }
                            )
                        {
                            return Err("cannot reborrow &mut from shared & reference".into());
                        }
                    }
                    let pointee = check_place(local_tys, place, "ref", true, false)?;
                    refuse_overflow_pair_pointee(&pointee, "Rvalue::Ref")?;
                    let expected = Ty::Ref {
                        mutability: *mutability,
                        pointee: Box::new(pointee),
                    };
                    if *dst_ty != expected {
                        return Err(format!(
                            "Rvalue::Ref type {expected:?} disagrees with destination {dst_ty:?}"
                        ));
                    }
                }
                Rvalue::AddressOf { mutability, place } => {
                    if place.projection.len() > 1
                        || (place.projection.len() == 1
                            && !matches!(place.projection[0], PlaceElem::Deref))
                    {
                        return Err("unsupported projection in Rvalue::AddressOf".into());
                    }
                    if place.projection.len() == 1 {
                        let base = check_local(local_tys, place.local, "addressOf")?;
                        // `&raw (*r)` for a reference `r` is how runtime MIR
                        // converts a reference to a raw pointer. Such a body
                        // mixes reference and raw-pointer locals and is
                        // already refused by `validate_local_tys`; refuse it
                        // here too rather than keep an unreachable rule.
                        if matches!(base, Ty::Ref { .. }) {
                            return Err(
                                "Rvalue::AddressOf through a reference is unsupported: \
                                 Profile v2 does not derive raw pointers from references"
                                    .into(),
                            );
                        }
                        // `&raw mut *p` through a `*const T` is a borrow-check
                        // error, so this is unreachable. Refusing it keeps a
                        // `*const T` from yielding a `*mut T`, matching the
                        // `PtrToPtr` refusal in [`check_cast_types`].
                        if *mutability == Mutability::Mut
                            && matches!(
                                base,
                                Ty::RawPtr {
                                    mutability: Mutability::Shared,
                                    ..
                                }
                            )
                        {
                            return Err(
                                "cannot take `&raw mut` through a `*const` raw pointer".into()
                            );
                        }
                    }
                    let pointee = check_place(local_tys, place, "addressOf", true, false)?;
                    refuse_overflow_pair_pointee(&pointee, "Rvalue::AddressOf")?;
                    let expected = Ty::RawPtr {
                        mutability: *mutability,
                        pointee: Box::new(pointee),
                    };
                    if *dst_ty != expected {
                        return Err(format!(
                            "Rvalue::AddressOf type {expected:?} disagrees with destination {dst_ty:?}"
                        ));
                    }
                }
                Rvalue::AggregateTuple { fields } => {
                    let overflow_fields;
                    let dst_fields: &[Ty] = match dst_ty {
                        Ty::Tuple { fields } => fields.as_slice(),
                        Ty::OverflowPair(ity) => {
                            overflow_fields = [Ty::Int(*ity), Ty::Bool];
                            &overflow_fields
                        }
                        _ => {
                            return Err(format!(
                                "AggregateTuple requires Tuple destination type, got {dst_ty:?}"
                            ));
                        }
                    };
                    if fields.len() != dst_fields.len() {
                        return Err("AggregateTuple arity disagrees with destination tuple".into());
                    }
                    for (field_op, expected_ty) in fields.iter().zip(dst_fields.iter()) {
                        let got = check_operand(local_tys, field_op)?;
                        if &got != expected_ty {
                            return Err(format!(
                                "AggregateTuple field type {got:?} disagrees with {expected_ty:?}"
                            ));
                        }
                    }
                }
                Rvalue::AggregateRangeTo { elem_ty, end } => {
                    if *elem_ty != usize_ty
                        || *dst_ty
                            != (Ty::RangeTo {
                                elem: Box::new(usize_ty.clone()),
                            })
                    {
                        return Err("AggregateRangeTo requires RangeTo<usize>".into());
                    }
                    let got = check_operand(local_tys, end)?;
                    if got != usize_ty {
                        return Err("AggregateRangeTo end operand must be usize".into());
                    }
                }
                Rvalue::AggregateRangeFrom { elem_ty, start } => {
                    if *elem_ty != usize_ty
                        || *dst_ty
                            != (Ty::RangeFrom {
                                elem: Box::new(usize_ty.clone()),
                            })
                    {
                        return Err("AggregateRangeFrom requires RangeFrom<usize>".into());
                    }
                    let got = check_operand(local_tys, start)?;
                    if got != usize_ty {
                        return Err("AggregateRangeFrom start operand must be usize".into());
                    }
                }
            }
            Ok(())
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
        for block in &blocks {
            for stmt in &block.statements {
                match stmt {
                    Statement::Assign { local, value } => {
                        let dst_ty = check_local(&local_tys, *local, "assignment")?.clone();
                        check_rvalue(&local_tys, &dst_ty, value)?;
                    }
                    Statement::AssignPlace { place, value } => {
                        if place.projection != vec![PlaceElem::Deref] && !place.projection.is_empty()
                        {
                            return Err("AssignPlace supports only empty or single [Deref] projection".into());
                        }
                        let dst_ty = check_place(
                            &local_tys,
                            place,
                            "assignment",
                            false,
                            !place.projection.is_empty(),
                        )?;
                        check_rvalue(&local_tys, &dst_ty, value)?;
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
                    Statement::PlaceMention { local } => {
                        let local_ty = check_local(&local_tys, *local, "place mention")?;
                        check_place_mention(local_ty)?;
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
                    let discr_ty = check_operand(&local_tys, operand)?;
                    check_switch_targets(&discr_ty, targets)?;
                    for &(_, target) in targets {
                        check_block(target)?;
                    }
                    check_block(*otherwise)?;
                }
                Terminator::Assert {
                    cond,
                    target,
                    ..
                } => {
                    let cond_ty = check_operand(&local_tys, cond)?;
                    if cond_ty != Ty::Bool {
                        return Err(format!("Assert condition must be bool, got {cond_ty:?}"));
                    }
                    check_block(*target)?;
                }
                Terminator::CoreCall {
                    op,
                    args,
                    dst,
                    target,
                    unwind: _,
                } => {
                    if !dst.projection.is_empty() {
                        return Err("CoreCall destination must be an unprojected local".into());
                    }
                    let dst_ty = check_local(&local_tys, dst.local, "core call destination")?.clone();
                    let arg_tys = args
                        .iter()
                        .map(|op| check_operand(&local_tys, op))
                        .collect::<Result<Vec<_>, _>>()?;
                    let usize_ty = Ty::Int(IntTy {
                        width: IntWidth::Isize,
                        signed: false,
                    });
                    // `get_unchecked(&self, index: I) -> &I::Output` takes and
                    // returns shared slices, so the `get_unchecked` arms admit
                    // only `&[u8] -> &[u8]`; a `&mut [u8]` receiver reaches the
                    // call through a shared reborrow.
                    match (op, arg_tys.as_slice()) {
                        (
                            CoreCallOp::SliceLen,
                            [Ty::Ref { pointee, .. }],
                        ) if matches!(&**pointee, Ty::Slice { elem: e } if matches!(&**e, Ty::Int(_)))
                            && dst_ty == usize_ty => {}
                        (
                            CoreCallOp::SliceGetUncheckedRangeTo,
                            [Ty::Ref {
                                mutability: in_mut,
                                pointee,
                            }, Ty::RangeTo { elem: idx_ty }],
                        ) if **idx_ty == usize_ty
                            && matches!(&**pointee, Ty::Slice { elem: e } if **e == Ty::Int(IntTy { width: IntWidth::I8, signed: false }))
                            && *in_mut == Mutability::Shared
                            && matches!(&dst_ty, Ty::Ref { mutability: Mutability::Shared, pointee: dst_pt } if dst_pt == pointee) => {}
                        (
                            CoreCallOp::SliceGetUncheckedRangeFrom,
                            [Ty::Ref {
                                mutability: in_mut,
                                pointee,
                            }, Ty::RangeFrom { elem: idx_ty }],
                        ) if **idx_ty == usize_ty
                            && matches!(&**pointee, Ty::Slice { elem: e } if **e == Ty::Int(IntTy { width: IntWidth::I8, signed: false }))
                            && *in_mut == Mutability::Shared
                            && matches!(&dst_ty, Ty::Ref { mutability: Mutability::Shared, pointee: dst_pt } if dst_pt == pointee) => {}
                        (
                            CoreCallOp::PtrAdd {
                                mutability,
                                pointee,
                            },
                            [Ty::RawPtr {
                                mutability: arg_mut,
                                pointee: arg_pt,
                            }, count_ty],
                        ) if arg_mut == mutability
                            && **arg_pt == *pointee
                            && pointee.is_sized()
                            && *count_ty == usize_ty
                            && dst_ty
                                == Ty::RawPtr {
                                    mutability: *mutability,
                                    pointee: Box::new(pointee.clone()),
                                } => {}
                        (CoreCallOp::UsizeUncheckedSub, [l_ty, r_ty])
                            if *l_ty == usize_ty && *r_ty == usize_ty && dst_ty == usize_ty => {}
                        _ => {
                            return Err(format!(
                                "invalid CoreCall {op:?} arguments {arg_tys:?} -> {dst_ty:?}"
                            ));
                        }
                    }
                    check_block(*target)?;
                }
                Terminator::Ret | Terminator::Unreachable | Terminator::Unsupported => {}
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

    /// Whether this body requires Profile v2 execution rules
    /// (`mir_profile_version = 2`).
    pub fn uses_profile_v2(&self) -> bool {
        if self.local_tys.iter().any(Ty::is_profile_v2) {
            return true;
        }
        for block in &self.blocks {
            for stmt in &block.statements {
                match stmt {
                    Statement::AssignPlace { .. } => return true,
                    Statement::Assign { value, .. } => match value {
                        Rvalue::Use { operand, .. } => {
                            if operand.is_profile_v2() {
                                return true;
                            }
                        }
                        Rvalue::Binary { op, left, right } => {
                            if *op == BinOp::Offset || left.is_profile_v2() || right.is_profile_v2()
                            {
                                return true;
                            }
                        }
                        Rvalue::Unary { op, operand } => {
                            if *op == UnOp::PtrMetadata || operand.is_profile_v2() {
                                return true;
                            }
                        }
                        Rvalue::Cast {
                            cast_kind,
                            operand,
                            ty,
                        } => {
                            if *cast_kind != CastKind::IntToInt
                                || operand.is_profile_v2()
                                || ty.is_profile_v2()
                            {
                                return true;
                            }
                        }
                        Rvalue::Discriminant { .. } => {}
                        Rvalue::UseRetag { .. }
                        | Rvalue::Ref { .. }
                        | Rvalue::AddressOf { .. }
                        | Rvalue::AggregateTuple { .. }
                        | Rvalue::AggregateRangeTo { .. }
                        | Rvalue::AggregateRangeFrom { .. } => return true,
                    },
                    Statement::StorageLive { .. }
                    | Statement::StorageDead { .. }
                    | Statement::PlaceMention { .. }
                    | Statement::Nop => {}
                }
            }
            match &block.terminator {
                Terminator::SwitchInt { operand, .. } => {
                    if operand.is_profile_v2() {
                        return true;
                    }
                }
                Terminator::Assert { .. } | Terminator::CoreCall { .. } => return true,
                Terminator::Goto { .. }
                | Terminator::Ret
                | Terminator::Unreachable
                | Terminator::Unsupported => {}
            }
        }
        false
    }

    /// Record every nominal [`EnumTy::id`] referenced anywhere in this body.
    ///
    /// Exhaustive matching guarantees that any future statement, rvalue,
    /// operand, or terminator variant carrying a [`Ty`] must update this
    /// traversal so emitted enum keys cannot bypass collision checks.
    pub fn collect_enum_ids(&self, out: &mut BTreeSet<u32>) {
        for ty in &self.local_tys {
            ty.collect_enum_ids(out);
        }
        for block in &self.blocks {
            for stmt in &block.statements {
                let (place_opt, value_opt) = match stmt {
                    Statement::Assign { value, .. } => (None, Some(value)),
                    Statement::AssignPlace { place, value } => (Some(place), Some(value)),
                    Statement::StorageLive { .. }
                    | Statement::StorageDead { .. }
                    | Statement::PlaceMention { .. }
                    | Statement::Nop => (None, None),
                };
                if let Some(p) = place_opt {
                    p.collect_enum_ids(out);
                }
                if let Some(value) = value_opt {
                    match value {
                        Rvalue::Use { operand, .. }
                        | Rvalue::UseRetag { operand }
                        | Rvalue::Unary { operand, .. } => {
                            operand.collect_enum_ids(out);
                        }
                        Rvalue::Binary { left, right, .. } => {
                            left.collect_enum_ids(out);
                            right.collect_enum_ids(out);
                        }
                        Rvalue::Cast { operand, ty, .. } => {
                            operand.collect_enum_ids(out);
                            ty.collect_enum_ids(out);
                        }
                        Rvalue::Ref { place, .. } | Rvalue::AddressOf { place, .. } => {
                            place.collect_enum_ids(out);
                        }
                        Rvalue::AggregateTuple { fields } => {
                            for f in fields {
                                f.collect_enum_ids(out);
                            }
                        }
                        Rvalue::AggregateRangeTo { elem_ty, end } => {
                            elem_ty.collect_enum_ids(out);
                            end.collect_enum_ids(out);
                        }
                        Rvalue::AggregateRangeFrom { elem_ty, start } => {
                            elem_ty.collect_enum_ids(out);
                            start.collect_enum_ids(out);
                        }
                        Rvalue::Discriminant { .. } => {}
                    }
                }
            }
            match &block.terminator {
                Terminator::SwitchInt { operand, .. } => operand.collect_enum_ids(out),
                Terminator::Assert { cond, .. } => cond.collect_enum_ids(out),
                Terminator::CoreCall { op, args, dst, .. } => {
                    if let CoreCallOp::PtrAdd { pointee, .. } = op {
                        pointee.collect_enum_ids(out);
                    }
                    for a in args {
                        a.collect_enum_ids(out);
                    }
                    dst.collect_enum_ids(out);
                }
                Terminator::Goto { .. }
                | Terminator::Ret
                | Terminator::Unreachable
                | Terminator::Unsupported => {}
            }
        }
    }
}

/// Single authoritative capture scope recorded on [`Program`] and matching
/// the `scope` schema of `cargo-anneal verify`.
///
/// `lean::render` inspects only the enum variant (`SelectedUnit` vs `Crate`)
/// when emitting `Trusted.MirAst.VerificationScope`, so raw selector strings
/// never enter the emitted Lean subject while remaining available in
/// `capture.json` for receipt authentication.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, serde::Deserialize, serde::Serialize)]
#[serde(deny_unknown_fields)]
pub struct Instantiation {
    pub path: String,
    pub args: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Scope {
    SelectedUnit {
        roots: BTreeSet<String>,
        #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
        instantiations: BTreeSet<Instantiation>,
    },
    Crate,
}

/// Validated captured program enforcing non-empty selected-unit targets,
/// non-empty bodies, and pairwise-distinct function identities
/// (`Trusted.MirSemantics.bodiesHaveUniqueIdentities`).
#[derive(Debug, Serialize)]
pub struct Program {
    scope: Scope,
    overflow_checks: bool,
    mir_profile_version: u32,
    bodies: Vec<Body>,
}

impl Program {
    #[cfg(test)]
    pub fn try_new(scope: Scope, bodies: Vec<Body>) -> Result<Self, String> {
        Self::try_new_with_overflow_checks(scope, false, bodies)
    }

    pub fn try_new_with_overflow_checks(
        scope: Scope,
        overflow_checks: bool,
        bodies: Vec<Body>,
    ) -> Result<Self, String> {
        if let Scope::SelectedUnit { roots, instantiations } = &scope
            && roots.is_empty()
            && instantiations.is_empty()
        {
            return Err("selected-unit scope must contain at least one root or instantiation".into());
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
        let mir_profile_version = if bodies.iter().any(Body::uses_profile_v2) {
            2
        } else {
            1
        };
        Ok(Self {
            scope,
            overflow_checks,
            mir_profile_version,
            bodies,
        })
    }

    pub fn scope(&self) -> &Scope {
        &self.scope
    }

    pub fn overflow_checks(&self) -> bool {
        self.overflow_checks
    }

    pub fn mir_profile_version(&self) -> u32 {
        self.mir_profile_version
    }

    pub fn bodies(&self) -> &[Body] {
        &self.bodies
    }
}

/// Linkage mode observed for `rustc_driver::run_compiler` in the live process.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DriverLinkage {
    /// `rustc_driver::run_compiler` lives in a dynamically loaded
    /// `librustc_driver-*.so` verified against the sysroot.
    DynamicDso,
    /// `rustc_driver::run_compiler` is statically linked into the capture
    /// executable itself (zero `librustc_driver-*.so` mapped).
    StaticExe,
}

/// Authenticated compiler driver identity returned by Linux residency checks
/// and recorded in the capture manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DriverIdentity {
    pub linkage: DriverLinkage,
    pub driver_sha256: String,
    pub dso_digests: BTreeMap<String, String>,
}

#[derive(Debug, Serialize)]
pub struct Compiler {
    pub commit: &'static str,
    pub version: &'static str,
    pub sysroot: PathBuf,
    pub rustc_sha256: String,
    pub driver: DriverIdentity,
}

/// Standard-library crate admitted by the explicit `--stdlib-crate`
/// capability. Only `core` is modeled: it links no other crate, so all of its
/// language items are its own definitions. `alloc` and `std` additionally
/// need hashed `--extern` admission and are not representable here yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum StdlibCrate {
    Core,
}

impl StdlibCrate {
    pub const fn crate_name(self) -> &'static str {
        match self {
            Self::Core => "core",
        }
    }
}

#[derive(Debug, Serialize)]
pub struct Configuration {
    pub crate_root: PathBuf,
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
    pub endian: &'static str,
    pub declared_source_files: Vec<PathBuf>,
    /// Present only under the explicit `--stdlib-crate` capability, which
    /// admits crate-local language items and selection-only metadata
    /// emission (see `capture::check_stdlib_capability`). Omitted otherwise
    /// so default captures keep their exact manifest bytes, and so a receipt
    /// that embeds this configuration discloses every relaxation in effect.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdlib_crate: Option<StdlibCrate>,
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
    fn validate_local_tys_rejects_mixed_refs_and_raw_ptrs() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let shared_ref = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(u8_ty.clone()),
        };
        let raw_ptr = Ty::RawPtr {
            mutability: Mutability::Mut,
            pointee: Box::new(u8_ty.clone()),
        };
        assert!(validate_local_tys(&[Ty::Unit, shared_ref.clone()]).is_ok());
        assert!(validate_local_tys(&[Ty::Unit, raw_ptr.clone()]).is_ok());
        let mixed = validate_local_tys(&[Ty::Unit, shared_ref.clone(), raw_ptr.clone()]);
        assert!(mixed.unwrap_err().contains("body mixes reference and raw-pointer locals"));
        let nested = validate_local_tys(&[
            Ty::Tuple {
                fields: vec![shared_ref, u8_ty],
            },
            raw_ptr,
        ]);
        assert!(nested.unwrap_err().contains("body mixes reference and raw-pointer locals"));
    }

    #[test]
    fn ptr_to_ptr_casts_admit_raw_sources_and_refuse_reference_and_const_to_mut() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let raw = |mutability, pointee: &Ty| Ty::RawPtr {
            mutability,
            pointee: Box::new(pointee.clone()),
        };
        let const_u8 = raw(Mutability::Shared, &u8_ty);
        let mut_u8 = raw(Mutability::Mut, &u8_ty);
        check_cast_types(CastKind::PtrToPtr, &mut_u8, &const_u8, &const_u8).unwrap();
        check_cast_types(CastKind::PtrToPtr, &mut_u8, &mut_u8, &mut_u8).unwrap();
        check_cast_types(CastKind::PtrToPtr, &const_u8, &const_u8, &const_u8).unwrap();
        let err = check_cast_types(CastKind::PtrToPtr, &const_u8, &mut_u8, &mut_u8).unwrap_err();
        assert!(err.contains("`*const T` to `*mut T`"), "{err}");
        let u8_slice = Ty::Slice {
            elem: Box::new(u8_ty.clone()),
        };
        let slice = |mutability| raw(mutability, &u8_slice);
        for (src, dst) in [
            (Mutability::Mut, Mutability::Shared),
            (Mutability::Mut, Mutability::Mut),
            (Mutability::Shared, Mutability::Shared),
        ] {
            check_cast_types(CastKind::PtrToPtr, &slice(src), &slice(dst), &slice(dst)).unwrap();
        }
        let err = check_cast_types(
            CastKind::PtrToPtr,
            &slice(Mutability::Shared),
            &slice(Mutability::Mut),
            &slice(Mutability::Mut),
        )
        .unwrap_err();
        assert!(err.contains("`*const T` to `*mut T`"), "{err}");
        for mutability in [Mutability::Shared, Mutability::Mut] {
            let reference = Ty::Ref {
                mutability,
                pointee: Box::new(u8_ty.clone()),
            };
            let err =
                check_cast_types(CastKind::PtrToPtr, &reference, &const_u8, &const_u8).unwrap_err();
            assert!(err.contains("PtrToPtr cast from reference"), "{err}");
        }
    }

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
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::Constant {
                            ty: Ty::Unit,
                            lit: ConstLit::ZeroSized,
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::unit_into_u8".into(),
        )
        .unwrap_err();
        assert!(unit_into_u8.contains("disagrees with destination local"));

        let copy_mismatch = Body::try_new(
            1,
            false,
            vec![Ty::Unit, u8_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1 },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::copy_mismatch".into(),
        )
        .unwrap_err();
        assert!(copy_mismatch.contains("disagrees with destination local"));

        assert!(
            Body::try_new(
                0,
                false,
                vec![Ty::Unit],
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Unit,
                                lit: ConstLit::ZeroSized,
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
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
                    local: 0,
                    value: Rvalue::Discriminant { local: 1 },
                }],
                terminator: Terminator::Ret,
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
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Enum(ety),
                                lit: ConstLit::ZeroSized,
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::zst_enum_ok".into(),
            )
            .is_ok()
        );
    }

    #[test]
    fn body_try_new_refuses_raw_borrow_mut_through_const_pointer() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let raw = |mutability| Ty::RawPtr {
            mutability,
            pointee: Box::new(u8_ty.clone()),
        };
        let body = |mutability: Mutability, dst: Ty| {
            Body::try_new(
                1,
                true,
                vec![dst, raw(Mutability::Shared)],
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::AddressOf {
                            mutability,
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::raw_borrow_through_const".into(),
            )
        };
        let err = body(Mutability::Mut, raw(Mutability::Mut)).unwrap_err();
        assert!(err.contains("`&raw mut` through a `*const`"), "{err}");
        body(Mutability::Shared, raw(Mutability::Shared)).unwrap();
    }

    #[test]
    fn body_try_new_admits_only_tuple_local_field_moves() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let range_from = Ty::RangeFrom {
            elem: Box::new(usize_ty.clone()),
        };
        let body = |locals: Vec<Ty>, operand: Operand| {
            Body::try_new(
                1,
                true,
                locals,
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand,
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::projected_move".into(),
            )
        };
        // `move (_1.0)` out of a `(RangeFrom<usize>, usize)` tuple local is
        // admitted: Profile v2 deinitializes just that field.
        let tuple_locals = vec![
            range_from.clone(),
            Ty::Tuple {
                fields: vec![range_from.clone(), usize_ty.clone()],
            },
        ];
        let field = Place {
            local: 1,
            projection: vec![PlaceElem::Field {
                index: 0,
                ty: range_from.clone(),
            }],
        };
        body(tuple_locals.clone(), Operand::MovePlace { place: field.clone() }).unwrap();
        // Refused: `move (*_1)` through a `*const u8`, a nested field move
        // `move ((_1.0).0)`, and a field move out of a non-tuple
        // `RangeFrom<usize>` local.
        let ptr_locals = vec![
            u8_ty.clone(),
            Ty::RawPtr {
                mutability: Mutability::Shared,
                pointee: Box::new(u8_ty.clone()),
            },
        ];
        let deref = Place {
            local: 1,
            projection: vec![PlaceElem::Deref],
        };
        let inner = Ty::Tuple {
            fields: vec![usize_ty.clone(), usize_ty.clone()],
        };
        let nested_locals = vec![
            usize_ty.clone(),
            Ty::Tuple {
                fields: vec![inner.clone(), usize_ty.clone()],
            },
        ];
        let nested = Place {
            local: 1,
            projection: vec![
                PlaceElem::Field {
                    index: 0,
                    ty: inner,
                },
                PlaceElem::Field {
                    index: 0,
                    ty: usize_ty.clone(),
                },
            ],
        };
        let range_locals = vec![usize_ty.clone(), range_from.clone()];
        let range_field = Place {
            local: 1,
            projection: vec![PlaceElem::Field {
                index: 0,
                ty: usize_ty.clone(),
            }],
        };
        let cases = [
            (ptr_locals.clone(), deref.clone()),
            (nested_locals.clone(), nested.clone()),
            (range_locals.clone(), range_field.clone()),
        ];
        for (locals, place) in cases {
            let err = body(locals, Operand::MovePlace { place }).unwrap_err();
            assert!(err.contains("projected move operands"), "{err}");
        }
        // Copying the same places stays admitted.
        body(tuple_locals, Operand::CopyPlace { place: field }).unwrap();
        body(ptr_locals, Operand::CopyPlace { place: deref }).unwrap();
        body(nested_locals, Operand::CopyPlace { place: nested }).unwrap();
        body(range_locals, Operand::CopyPlace { place: range_field }).unwrap();
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
        let ovf_u8 = Ty::OverflowPair(IntTy {
            width: IntWidth::I8,
            signed: false,
        });

        assert_eq!(IntWidth::I128.bits(), 128);
        assert_eq!(IntWidth::I128.mask(), u128::MAX);
        assert_eq!(IntWidth::I128.lean_name(), "i128");

        assert!(validate_constant(&Ty::Unit, ConstLit::ZeroSized).is_ok());
        assert!(validate_constant(&Ty::Unit, ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&Ty::Never, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Never, ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&ovf_u8, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&ovf_u8, ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&Ty::Bool, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Bool, ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Bool, ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&Ty::Bool, ConstLit::Scalar { bits: 2 }).is_err());
        assert!(validate_constant(&Ty::Char, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0xD7FF }).is_ok());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0xD800 }).is_err());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0xDFFF }).is_err());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0xE000 }).is_ok());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0x10_FFFF }).is_ok());
        assert!(validate_constant(&Ty::Char, ConstLit::Scalar { bits: 0x11_0000 }).is_err());
        assert!(validate_constant(&Ty::Ordering, ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Ordering, ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Ordering, ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&Ty::Ordering, ConstLit::Scalar { bits: 0xff }).is_ok());
        assert!(validate_constant(&Ty::Ordering, ConstLit::Scalar { bits: 2 }).is_err());
        assert!(validate_constant(&Ty::Ordering, ConstLit::Scalar { bits: 0x1ff }).is_err());
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
            Ty::Char,
            Ty::Ordering,
            Ty::Unit,
            Ty::Never,
            Ty::Int(IntTy {
                width: IntWidth::Isize,
                signed: true,
            }),
            Ty::Int(IntTy {
                width: IntWidth::I128,
                signed: false,
            }),
            Ty::OverflowPair(IntTy {
                width: IntWidth::I64,
                signed: false,
            }),
        ] {
            assert!(ty.is_retag_noop(), "{ty:?}");
            assert!(check_use_retag(&ty, true).is_ok(), "{ty:?}");
        }
    }

    #[test]
    fn body_try_new_enforces_operator_cast_discriminant_and_switch_typing() {
        let u8_ity = IntTy {
            width: IntWidth::I8,
            signed: false,
        };
        let i8_ity = IntTy {
            width: IntWidth::I8,
            signed: true,
        };
        let u32_ity = IntTy {
            width: IntWidth::I32,
            signed: false,
        };
        let i128_ity = IntTy {
            width: IntWidth::I128,
            signed: true,
        };
        let u8_ty = Ty::Int(u8_ity);
        let i8_ty = Ty::Int(i8_ity);
        let u32_ty = Ty::Int(u32_ity);
        let i128_ty = Ty::Int(i128_ity);
        let ovf_u32 = Ty::OverflowPair(u32_ity);

        let one_stmt_body = |locals: Vec<Ty>, value: Rvalue| {
            Body::try_new(
                locals.len() - 1,
                false,
                locals,
                vec![Block {
                    statements: vec![Statement::Assign { local: 0, value }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::stmt_check".into(),
            )
        };

        // Overflowing arithmetic requires matching `Int` operands and
        // `OverflowPair(ity)` destination.
        assert!(
            one_stmt_body(
                vec![ovf_u32.clone(), u32_ty.clone(), u32_ty.clone()],
                Rvalue::Binary {
                    op: BinOp::AddWithOverflow,
                    left: Operand::Copy { local: 1 },
                    right: Operand::Copy { local: 2 },
                },
            )
            .is_ok()
        );
        assert!(
            one_stmt_body(
                vec![u32_ty.clone(), u32_ty.clone(), u32_ty.clone()],
                Rvalue::Binary {
                    op: BinOp::AddWithOverflow,
                    left: Operand::Copy { local: 1 },
                    right: Operand::Copy { local: 2 },
                },
            )
            .is_err()
        );

        // `Cmp` admits `Int` and `Char` -> `Ordering`, rejecting `Bool` and
        // `Ordering`; relational ops admit `Char` and reject `Ordering`.
        assert!(
            one_stmt_body(
                vec![Ty::Ordering, Ty::Char, Ty::Char],
                Rvalue::Binary {
                    op: BinOp::Cmp,
                    left: Operand::Copy { local: 1 },
                    right: Operand::Copy { local: 2 },
                },
            )
            .is_ok()
        );
        assert!(
            one_stmt_body(
                vec![Ty::Ordering, Ty::Bool, Ty::Bool],
                Rvalue::Binary {
                    op: BinOp::Cmp,
                    left: Operand::Copy { local: 1 },
                    right: Operand::Copy { local: 2 },
                },
            )
            .is_err()
        );
        assert!(
            one_stmt_body(
                vec![Ty::Bool, Ty::Char, Ty::Char],
                Rvalue::Binary {
                    op: BinOp::Lt,
                    left: Operand::Copy { local: 1 },
                    right: Operand::Copy { local: 2 },
                },
            )
            .is_ok()
        );
        assert!(
            one_stmt_body(
                vec![Ty::Bool, Ty::Ordering, Ty::Ordering],
                Rvalue::Binary {
                    op: BinOp::Eq,
                    left: Operand::Copy { local: 1 },
                    right: Operand::Copy { local: 2 },
                },
            )
            .is_err()
        );

        // `Unary`: `Not` admits `Bool` and `Int` (rejects `Char`), `Neg` admits
        // signed `Int` (rejects unsigned `Int` and `Bool`).
        assert!(
            one_stmt_body(
                vec![i128_ty.clone(), i128_ty.clone()],
                Rvalue::Unary {
                    op: UnOp::Neg,
                    operand: Operand::Copy { local: 1 },
                },
            )
            .is_ok()
        );
        assert!(
            one_stmt_body(
                vec![u32_ty.clone(), u32_ty.clone()],
                Rvalue::Unary {
                    op: UnOp::Neg,
                    operand: Operand::Copy { local: 1 },
                },
            )
            .is_err()
        );
        assert!(
            one_stmt_body(
                vec![Ty::Char, Ty::Char],
                Rvalue::Unary {
                    op: UnOp::Not,
                    operand: Operand::Copy { local: 1 },
                },
            )
            .is_err()
        );

        // `Cast(IntToInt)`: `{int, bool, char} -> int` and `u8 -> char` only,
        // with `cast_ty == dst_ty`.
        assert!(
            one_stmt_body(
                vec![Ty::Char, u8_ty.clone()],
                Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1 },
                    ty: Ty::Char,
                },
            )
            .is_ok()
        );
        for bad_src in [i8_ty.clone(), u32_ty.clone(), Ty::Bool, Ty::Char] {
            assert!(
                one_stmt_body(
                    vec![Ty::Char, bad_src],
                    Rvalue::Cast {
                        cast_kind: CastKind::IntToInt,
                        operand: Operand::Copy { local: 1 },
                        ty: Ty::Char,
                    },
                )
                .is_err()
            );
        }
        assert!(
            one_stmt_body(
                vec![u32_ty.clone(), Ty::Char],
                Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1 },
                    ty: u8_ty.clone(),
                },
            )
            .is_err()
        );
        assert!(
            one_stmt_body(
                vec![Ty::Bool, u8_ty.clone()],
                Rvalue::Cast {
                    cast_kind: CastKind::IntToInt,
                    operand: Operand::Copy { local: 1 },
                    ty: Ty::Bool,
                },
            )
            .is_err()
        );

        // `Discriminant` on `Ordering` requires `i8` destination.
        assert!(
            one_stmt_body(
                vec![i8_ty.clone(), Ty::Ordering],
                Rvalue::Discriminant { local: 1 },
            )
            .is_ok()
        );
        assert!(
            one_stmt_body(
                vec![u8_ty.clone(), Ty::Ordering],
                Rvalue::Discriminant { local: 1 },
            )
            .is_err()
        );

        // `SwitchInt` checks operand switchability and case bounds.
        let switch_body = |discr_ty: Ty, targets: Vec<(u128, u32)>| {
            Body::try_new(
                1,
                false,
                vec![Ty::Unit, discr_ty],
                vec![Block {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        operand: Operand::Copy { local: 1 },
                        targets,
                        otherwise: 0,
                    },
                }],
                "rust-path-v1::switch_check".into(),
            )
        };
        assert!(switch_body(i128_ty, vec![(u128::MAX, 0)]).is_ok());
        assert!(switch_body(u8_ty, vec![(256, 0)]).is_err());
        assert!(switch_body(Ty::Bool, vec![(0, 0), (1, 0)]).is_ok());
        assert!(switch_body(Ty::Bool, vec![(2, 0)]).is_err());
        assert!(switch_body(Ty::Char, vec![(0x1F600, 0)]).is_ok());
        assert!(switch_body(Ty::Char, vec![(0xD800, 0)]).is_err());
        assert!(switch_body(ovf_u32.clone(), vec![]).is_ok());
        assert!(switch_body(ovf_u32, vec![(0, 0)]).is_err());
        assert!(switch_body(Ty::Ordering, vec![]).is_err());

        // Decimal string serialization for 128-bit values round-trips via
        // standard `serde_json::Value` without `arbitrary_precision`.
        let i128_enum = EnumTy::try_new(
            9,
            i128_ity,
            EnumTagRepr::Scalar(i128_ity),
            vec![u128::MAX, 0, 1],
        )
        .unwrap();
        let json_val = serde_json::to_value(&i128_enum).unwrap();
        assert_eq!(
            json_val["discriminants"],
            serde_json::json!(["340282366920938463463374607431768211455", "0", "1"])
        );
    }

    #[test]
    fn place_mention_guard_checks_local_bounds_and_sizedness() {
        assert!(admit_place_mention(true).is_ok());
        assert!(
            admit_place_mention(false)
                .unwrap_err()
                .contains("PlaceMention on unsized locals is unsupported")
        );

        let u64_ty = Ty::Int(IntTy {
            width: IntWidth::I64,
            signed: false,
        });
        assert!(check_place_mention(&u64_ty).is_ok());
        assert!(check_place_mention(&Ty::Unit).is_ok());

        let valid = Body::try_new(
            1,
            false,
            vec![Ty::Unit, u64_ty.clone()],
            vec![Block {
                statements: vec![Statement::PlaceMention { local: 1 }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::place_mention_ok".into(),
        )
        .unwrap();
        let json = serde_json::to_value(&valid).unwrap();
        assert_eq!(
            json["blocks"][0]["statements"][0],
            serde_json::json!({ "kind": "place_mention", "local": 1 })
        );

        let oob = Body::try_new(
            1,
            false,
            vec![Ty::Unit, u64_ty],
            vec![Block {
                statements: vec![Statement::PlaceMention { local: 9 }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::place_mention_oob".into(),
        )
        .unwrap_err();
        assert!(oob.contains("place mention local 9 out of bounds"), "{oob}");
    }

    #[test]
    fn body_collect_enum_ids_visits_locals_and_constant_operands() {
        let isize_discr = IntTy {
            width: IntWidth::Isize,
            signed: true,
        };
        let enum_a = EnumTy::try_new(101, isize_discr, EnumTagRepr::ZeroSized, vec![0]).unwrap();
        let enum_b = EnumTy::try_new(
            202,
            isize_discr,
            EnumTagRepr::Scalar(IntTy {
                width: IntWidth::I8,
                signed: false,
            }),
            vec![0, 1],
        )
        .unwrap();
        let body = Body::try_new(
            0,
            false,
            vec![Ty::Enum(enum_a.clone()), Ty::Enum(enum_b.clone())],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Enum(enum_a),
                                lit: ConstLit::ZeroSized,
                            },
                            with_retag: false,
                        },
                    },
                    Statement::Assign {
                        local: 1,
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Enum(enum_b),
                                lit: ConstLit::Scalar { bits: 1 },
                            },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::enum_ids_body".into(),
        )
        .unwrap();
        let mut ids = BTreeSet::new();
        body.collect_enum_ids(&mut ids);
        assert_eq!(ids, BTreeSet::from([101, 202]));

        let unsupported_term = Body::try_new(
            0,
            false,
            vec![Ty::Never],
            vec![Block {
                statements: vec![],
                terminator: Terminator::Unsupported,
            }],
            "rust-path-v1::diverging_call".into(),
        )
        .unwrap();
        let term_json = serde_json::to_value(&unsupported_term).unwrap();
        assert_eq!(
            term_json["blocks"][0]["terminator"],
            serde_json::json!({ "kind": "unsupported" })
        );
    }
}
