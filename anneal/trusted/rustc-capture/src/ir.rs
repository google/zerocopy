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
// switch operations. Version 5 adds `Terminator::{Call, SysrootCall}` with
// their `SysrootNumOp` (`SysrootNumKind`) payloads, and
// `BinOp::{AddUnchecked, SubUnchecked, MulUnchecked}`.
pub const SCHEMA_VERSION: u32 = 5;
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
    Array {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
        len: usize,
    },
    RangeTo {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
    },
    RangeFrom {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
    },
    Range {
        #[serde(serialize_with = "serialize_boxed_ty")]
        elem: Box<Ty>,
    },
    Option {
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
            | Self::RangeFrom { .. }
            | Self::Range { .. } => true,
            Self::Option { elem } => elem.is_retag_noop(),
            Self::Ref { .. } => false,
            Self::Array { elem, .. } => elem.is_retag_noop(),
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
            Self::Array { elem, .. } => elem.is_sized(),
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
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Option { .. } => true,
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

    /// Whether this type belongs to the Profile v2 fixed-size data fragment
    /// (`Trusted.MirSemantics.isSupportedV2DataTy`): scalars, units, enums,
    /// and fixed arrays `[T; N]` without embedded refs, ptrs, or overflow
    /// pairs.
    pub fn is_supported_v2_data(&self) -> bool {
        match self {
            Self::Array { elem, .. } => elem.is_supported_v2_data(),
            Self::OverflowPair(_) => false,
            _ => self.is_supported_scalar_or_unit(),
        }
    }

    /// Whether this type belongs to the Profile v2 structural `PartialEq`
    /// fragment (`Trusted.MirSemantics.isArrayEqElemSupported`): primitives,
    /// `Ordering`, `()`, and nested fixed-size arrays thereof, excluding enums
    /// whose `PartialEq` impl may be non-structural.
    pub fn is_array_eq_elem_supported(&self) -> bool {
        match self {
            Self::Bool | Self::Int(_) | Self::Char | Self::Ordering | Self::Unit => true,
            Self::Array { elem, .. } => elem.is_array_eq_elem_supported(),
            Self::Never
            | Self::Enum(_)
            | Self::OverflowPair(_)
            | Self::Tuple { .. }
            | Self::Ref { .. }
            | Self::RawPtr { .. }
            | Self::Slice { .. }
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Option { .. } => false,
        }
    }

    /// Layout `(size_bytes, align_log2)` matching
    /// `Trusted.MirSemantics.layoutOfTyV2`.
    pub fn v2_layout(&self) -> Option<(usize, u32)> {
        match self {
            Self::Bool | Self::Ordering => Some((1, 0)),
            Self::Int(ity) => Some(match ity.width {
                IntWidth::I8 => (1, 0),
                IntWidth::I16 => (2, 1),
                IntWidth::I32 => (4, 2),
                IntWidth::I64 | IntWidth::Isize => (8, 3),
                IntWidth::I128 => (16, 4),
            }),
            Self::Char => Some((4, 2)),
            Self::Unit | Self::Never => Some((0, 0)),
            Self::Enum(ety) => match ety.tag_repr() {
                EnumTagRepr::ZeroSized => Some((0, 0)),
                EnumTagRepr::Scalar(tag) => Self::Int(tag).v2_layout(),
            },
            Self::OverflowPair(ity) => {
                let (w_bytes, align_log2) = Self::Int(*ity).v2_layout()?;
                Some((2 * w_bytes, align_log2))
            }
            Self::Array { elem, len } => {
                let (elem_size, align_log2) = elem.v2_layout()?;
                let size = len.checked_mul(elem_size)?;
                Some((size, align_log2))
            }
            Self::Ref { pointee, .. } | Self::RawPtr { pointee, .. } => {
                Some(if matches!(&**pointee, Self::Slice { .. }) {
                    (16, 3)
                } else {
                    (8, 3)
                })
            }
            Self::RangeTo { elem } | Self::RangeFrom { elem }
                if matches!(
                    &**elem,
                    Self::Int(IntTy {
                        width: IntWidth::Isize,
                        signed: false
                    })
                ) =>
            {
                Some((8, 3))
            }
            Self::Option { elem } => {
                if !elem.is_sized_no_ref() || !elem.is_option_payload_supported_v2() {
                    return None;
                }
                match &**elem {
                    Self::Bool | Self::Unit => Some((1, 0)),
                    inner => {
                        let (size, align_log2) = inner.v2_layout()?;
                        let tag_bytes = 1usize.checked_shl(align_log2)?;
                        Some((tag_bytes.checked_add(size)?, align_log2))
                    }
                }
            }
            Self::Tuple { .. }
            | Self::Slice { .. }
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. } => None,
        }
    }

    /// Whether this type is a sized Profile v2 pointee or slice-element type
    /// containing no nested references or raw pointers and having a fixed,
    /// guaranteed ABI layout (matching
    /// `Trusted.MirSemantics.isSizedNoRefV2Ty`).
    ///
    /// Tuples (`OverflowPair` and `Tuple`) and `Range`/`RangeTo`/`RangeFrom`
    /// are `#[repr(Rust)]` and subject to `rustc_abi`'s `univariant` field
    /// reordering (`compiler/rustc_abi/src/layout.rs:1111` at
    /// `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), so they remain local-only
    /// (`is_supported_v2_local`) and are refused behind references, pointers,
    /// and slices. `Option<T>` additionally requires
    /// `is_option_payload_supported_v2` so `&Option<Option<u8>>` fails closed.
    pub fn is_sized_no_ref(&self) -> bool {
        match self {
            Self::Bool
            | Self::Int(_)
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Enum(_) => true,
            Self::Option { elem } => {
                elem.is_sized_no_ref() && elem.is_option_payload_supported_v2()
            }
            Self::OverflowPair(_)
            | Self::Tuple { .. }
            | Self::Array { .. }
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Ref { .. }
            | Self::RawPtr { .. }
            | Self::Slice { .. } => false,
        }
    }

    /// Whether `self` is an admitted Profile v2 thin pointee (matching
    /// `Trusted.MirSemantics.isSupportedV2PointeeTy`): the union of
    /// [`Self::is_sized_no_ref`] and [`Self::is_supported_v2_data`].
    pub fn is_supported_v2_pointee(&self) -> bool {
        self.is_sized_no_ref() || self.is_supported_v2_data()
    }

    /// Whether `self` uses `rustc` `TagEncoding::Direct` with fixed layout
    /// inside `Option<self>` (scalars and raw pointers; matching
    /// `Trusted.MirSemantics.isNicheFreeOptionPayloadV2`). Tuples,
    /// `OverflowPair`, and `Range*` are refused due to `#[repr(Rust)]`
    /// field reordering and padding-tag optimizations.
    pub fn is_niche_free_option_payload(&self) -> bool {
        matches!(self, Self::Int(_) | Self::RawPtr { .. })
    }

    /// Whether `self` has a modeled `Option<self>` layout in Profile v2
    /// (matching `Trusted.MirSemantics.isOptionPayloadSupportedV2`).
    pub fn is_option_payload_supported_v2(&self) -> bool {
        matches!(self, Self::Unit | Self::Bool | Self::Ref { .. })
            || self.is_niche_free_option_payload()
    }

    /// Whether this type is admitted as a Profile v2 local type (matching
    /// `Trusted.MirSemantics.isSupportedV2LocalTy`). Forbids nested
    /// references/pointers inside pointees (`&&T`, `*mut &T`, `&[&T]`,
    /// `[&T; N]`) and unmodeled niche-packed `Option` payloads.
    ///
    /// Also forbids tuple, overflow-pair, and range pointees and overflow-pair
    /// array elements (`&(T, bool)`, `*const (T, bool)`, `&Range<usize>`,
    /// `[(T, bool); N]`). The Reference says "Tuples are
    /// laid out according to the [`Rust` representation][`Rust`]." Beyond
    /// field alignment and non-overlap, "There are no other guarantees of
    /// data layout made by this representation." Yet
    /// `Trusted.MirSemantics.overflowPairLayout` fixes one field order and
    /// size without a `layout_of` check. So overflow pairs stay
    /// non-addressable locals that hold checked-operator results, and no
    /// pointer can reach their bytes (see [`Self::is_sized_no_ref`]).
    /// https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/type-layout.md#L94
    /// https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/type-layout.md#L184
    pub fn is_supported_v2_local(&self) -> bool {
        let usize_ty = Self::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        match self {
            Self::Bool
            | Self::Int(_)
            | Self::Char
            | Self::Ordering
            | Self::Unit
            | Self::Never
            | Self::Enum(_)
            | Self::OverflowPair(_) => true,
            Self::Array { elem, .. } => elem.is_supported_v2_data(),
            Self::Tuple { fields } => fields.iter().all(Self::is_supported_v2_local),
            Self::Ref { pointee, .. } | Self::RawPtr { pointee, .. } => match &**pointee {
                Self::Slice { elem } => elem.is_sized_no_ref(),
                other => other.is_supported_v2_pointee(),
            },
            Self::RangeTo { elem } | Self::RangeFrom { elem } | Self::Range { elem } => {
                **elem == usize_ty
            }
            Self::Option { elem } => {
                elem.is_supported_v2_local() && elem.is_option_payload_supported_v2()
            }
            Self::Slice { .. } => false,
        }
    }

    /// Whether this type is a reference or an `Option`, range, or tuple/array
    /// containing one, mirroring `Trusted.MirSemantics.tyHasRefV2`.
    pub fn has_ref_v2(&self) -> bool {
        match self {
            Self::Ref { .. } => true,
            Self::Array { elem, .. } => elem.has_ref_v2(),
            Self::Option { elem }
            | Self::RangeTo { elem }
            | Self::RangeFrom { elem }
            | Self::Range { elem } => elem.has_ref_v2(),
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
            | Self::Slice { .. } => false,
        }
    }

    /// Whether this type is a raw pointer or an `Option`, range, or tuple/array
    /// containing one, mirroring `Trusted.MirSemantics.tyHasRawPtrV2`.
    pub fn has_raw_ptr_v2(&self) -> bool {
        match self {
            Self::RawPtr { .. } => true,
            Self::Array { elem, .. } => elem.has_raw_ptr_v2(),
            Self::Option { elem }
            | Self::RangeTo { elem }
            | Self::RangeFrom { elem }
            | Self::Range { elem } => elem.has_raw_ptr_v2(),
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
            | Self::Slice { .. } => false,
        }
    }

    /// Whether this type uses Profile v2 extensions.
    pub fn is_profile_v2(&self) -> bool {
        match self {
            Self::Tuple { .. }
            | Self::Ref { .. }
            | Self::RawPtr { .. }
            | Self::Slice { .. }
            | Self::Array { .. }
            | Self::RangeTo { .. }
            | Self::RangeFrom { .. }
            | Self::Range { .. }
            | Self::Option { .. } => true,
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
            Self::Slice { elem }
            | Self::Array { elem, .. }
            | Self::RangeTo { elem }
            | Self::RangeFrom { elem }
            | Self::Range { elem }
            | Self::Option { elem } => {
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

    pub fn ast_nodes(&self) -> usize {
        match self {
            Self::Bool | Self::Char | Self::Ordering | Self::Unit | Self::Never | Self::Int(_) => 1,
            Self::OverflowPair(_) => 3,
            Self::Enum(ety) => 1 + ety.discriminants.len(),
            Self::Tuple { fields } => 1 + fields.iter().map(Self::ast_nodes).sum::<usize>(),
            Self::Ref { pointee, .. } | Self::RawPtr { pointee, .. } => 1 + pointee.ast_nodes(),
            Self::Slice { elem }
            | Self::Array { elem, .. }
            | Self::RangeTo { elem }
            | Self::RangeFrom { elem }
            | Self::Range { elem }
            | Self::Option { elem } => 1 + elem.ast_nodes(),
        }
    }
}

/// Byte entry in immutable `.rodata` constant memory
/// (`Trusted.MirAst.RodataByte`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RodataByte {
    Uninit,
    Init { byte: u8 },
}

/// Constant literal payload matching `Trusted.MirAst.ConstLit` 1-to-1.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ConstLit {
    ZeroSized,
    Scalar {
        #[serde(serialize_with = "serialize_u128_decimal")]
        bits: u128,
    },
    RodataBytes {
        bytes: Vec<RodataByte>,
    },
    RodataRef {
        bytes: Vec<RodataByte>,
        align_log2: u32,
        offset_bytes: usize,
        slice_len: Option<usize>,
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

/// Validate a typed constant literal against `evalConstLit` / Profile v2
/// `.rodata` invariants.
pub fn validate_constant(ty: &Ty, lit: &ConstLit) -> Result<(), String> {
    match (ty, lit) {
        (Ty::Unit, ConstLit::ZeroSized) => Ok(()),
        (Ty::Unit, ConstLit::Scalar { .. } | ConstLit::RodataBytes { .. } | ConstLit::RodataRef { .. }) => {
            Err("zero-sized constant must use ZeroSized literal".into())
        }
        (Ty::Never, ConstLit::ZeroSized) => {
            Err("ZeroSized constant requires unit or zero-sized enum type".into())
        }
        (Ty::Never, _) => Err("the never type has no constants".into()),
        (Ty::OverflowPair(_), _) => Err("overflow-pair tuple constants are unsupported".into()),
        (Ty::Bool, ConstLit::Scalar { bits }) => {
            // `Scalar::to_bool` maps `0` and `1` to `false` and `true` and
            // raises `InvalidBool` for every other byte.
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/value.rs#L344-L351
            if *bits <= 1 {
                Ok(())
            } else {
                Err("invalid Boolean constant".into())
            }
        }
        (Ty::Bool, _) => Err("boolean constant must use Scalar literal".into()),
        (Ty::Char, ConstLit::Scalar { bits }) => {
            if is_unicode_scalar(*bits) {
                Ok(())
            } else {
                Err(format!(
                    "invalid char constant {bits:#x}: outside Unicode scalar range"
                ))
            }
        }
        (Ty::Char, _) => Err("char constant must use Scalar literal".into()),
        (Ty::Ordering, ConstLit::Scalar { bits }) => {
            // `core::cmp::Ordering` is `#[repr(i8)]` whose "three variants
            // `Less`/`Equal`/`Greater` remain `-1_i8`/`0_i8`/`+1_i8`
            // respectively" (`0xff`, `0`, `1` as 8-bit unsigned tags).
            // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/core/src/cmp.rs#L400-L415
            if matches!(*bits, 0 | 1 | 0xff) {
                Ok(())
            } else {
                Err(format!("invalid Ordering tag constant {bits:#x}"))
            }
        }
        (Ty::Ordering, _) => Err("Ordering constant must use Scalar literal".into()),
        (Ty::Int(ity), ConstLit::Scalar { bits }) => {
            if *bits > ity.width.mask() {
                return Err(format!(
                    "scalar constant {bits:#x} exceeds {}-bit width",
                    ity.width.bits()
                ));
            }
            Ok(())
        }
        (Ty::Int(_), _) => Err("integer constant must use Scalar literal".into()),
        (Ty::Array { elem, .. }, ConstLit::RodataBytes { bytes }) => {
            if !elem.is_supported_v2_data() {
                return Err(format!(
                    "unsupported element type {elem:?} in array constant"
                ));
            }
            let Some((expected_size, _)) = ty.v2_layout() else {
                return Err(format!("array constant type {ty:?} lacks layout"));
            };
            if bytes.len() != expected_size {
                return Err(format!(
                    "array constant byte length {} disagrees with layout size {expected_size}",
                    bytes.len()
                ));
            }
            Ok(())
        }
        (
            Ty::Ref {
                mutability: Mutability::Shared,
                pointee,
            }
            | Ty::RawPtr {
                mutability: Mutability::Shared,
                pointee,
            },
            ConstLit::RodataRef {
                bytes,
                align_log2,
                offset_bytes,
                slice_len,
            },
        ) => match (&**pointee, slice_len) {
            (Ty::Slice { elem }, Some(len)) if matches!(&**elem, Ty::Int(_)) => {
                let Some((elem_size, elem_align_log2)) = elem.v2_layout() else {
                    return Err(format!("slice element type {elem:?} lacks layout"));
                };
                let slice_bytes = len
                    .checked_mul(elem_size)
                    .ok_or_else(|| "rodata slice byte size overflow".to_string())?;
                let end = offset_bytes
                    .checked_add(slice_bytes)
                    .ok_or_else(|| "rodata slice offset overflow".to_string())?;
                if end > bytes.len() {
                    return Err(format!(
                        "rodata slice range [{offset_bytes}..{end}) exceeds rodata size {}",
                        bytes.len()
                    ));
                }
                let align_bytes = 1usize.checked_shl(elem_align_log2).unwrap_or(usize::MAX);
                if *align_log2 < elem_align_log2 || *offset_bytes % align_bytes != 0 {
                    return Err("rodata slice reference is misaligned".into());
                }
                Ok(())
            }
            (pt, None) if pt.is_supported_v2_data() => {
                let Some((pt_size, pt_align_log2)) = pt.v2_layout() else {
                    return Err(format!("rodata pointee type {pt:?} lacks layout"));
                };
                let end = offset_bytes
                    .checked_add(pt_size)
                    .ok_or_else(|| "rodata pointer offset overflow".to_string())?;
                if end > bytes.len() {
                    return Err(format!(
                        "rodata pointer range [{offset_bytes}..{end}) exceeds rodata size {}",
                        bytes.len()
                    ));
                }
                let align_bytes = 1usize.checked_shl(pt_align_log2).unwrap_or(usize::MAX);
                if *align_log2 < pt_align_log2 || *offset_bytes % align_bytes != 0 {
                    return Err("rodata pointer is misaligned".into());
                }
                Ok(())
            }
            _ => Err(format!(
                "unsupported rodata reference pointee {pointee:?} / slice_len {slice_len:?}"
            )),
        },
        (
            Ty::Array { .. }
            | Ty::Tuple { .. }
            | Ty::Ref { .. }
            | Ty::RawPtr { .. }
            | Ty::Slice { .. }
            | Ty::RangeTo { .. }
            | Ty::RangeFrom { .. }
            | Ty::Range { .. }
            | Ty::Option { .. },
            _,
        ) => Err(format!("constants of compound/pointer type {ty:?} are unsupported")),
        (Ty::Enum(ety), lit) => match (ety.tag_repr, lit) {
            (EnumTagRepr::ZeroSized, ConstLit::ZeroSized) => Ok(()),
            (EnumTagRepr::ZeroSized, _) => {
                Err("zero-sized constant must use ZeroSized literal".into())
            }
            (EnumTagRepr::Scalar(_), ConstLit::ZeroSized) => {
                Err("ZeroSized constant requires unit or zero-sized enum type".into())
            }
            (EnumTagRepr::Scalar(tag), ConstLit::Scalar { bits }) => {
                if *bits > tag.width.mask() {
                    return Err(format!(
                        "enum tag constant {bits:#x} exceeds {}-bit tag width",
                        tag.width.bits()
                    ));
                }
                let discr = tag_bits_to_discr_bits(tag, ety.discr().width, *bits);
                if !ety.discriminants.contains(&discr) {
                    return Err(format!(
                        "enum tag constant {bits:#x} does not match any declared variant"
                    ));
                }
                Ok(())
            }
            (EnumTagRepr::Scalar(_), _) => Err("scalar enum constant must use Scalar literal".into()),
        },
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PlaceElem {
    Deref,
    Field {
        index: usize,
        ty: Ty,
    },
    ConstantIndex {
        offset: usize,
        min_length: usize,
        from_end: bool,
    },
    Downcast { variant_idx: usize },
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

    fn ast_nodes(&self) -> usize {
        1 + self
            .projection
            .iter()
            .map(|elem| match elem {
                PlaceElem::Deref
                | PlaceElem::ConstantIndex { .. }
                | PlaceElem::Downcast { .. } => 1,
                PlaceElem::Field { ty, .. } => 1 + ty.ast_nodes(),
            })
            .sum::<usize>()
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
            Self::Constant { ty, lit } => {
                ty.is_profile_v2() || !matches!(lit, ConstLit::ZeroSized | ConstLit::Scalar { .. })
            }
        }
    }

    fn ast_nodes(&self) -> usize {
        match self {
            Self::Copy { .. } | Self::Move { .. } => 1,
            Self::CopyPlace { place } | Self::MovePlace { place } => 1 + place.ast_nodes(),
            Self::Constant { ty, .. } => 1 + ty.ast_nodes(),
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
    Unsize,
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
    AddUnchecked,
    SubUnchecked,
    MulUnchecked,
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
        place: Place,
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
    AggregateTuple {
        fields: Vec<Operand>,
    },
    AggregateArray {
        elem_ty: Ty,
        elems: Vec<Operand>,
    },
    Repeat {
        operand: Operand,
        elem_ty: Ty,
        count: usize,
    },
    AggregateRangeTo {
        elem_ty: Ty,
        end: Operand,
    },
    AggregateRangeFrom {
        elem_ty: Ty,
        start: Operand,
    },
    AggregateRange {
        elem_ty: Ty,
        start: Operand,
        end: Operand,
    },
    AggregateOption {
        variant_idx: usize,
        inner_ty: Ty,
        payload: Option<Box<Operand>>,
    },
}

impl Rvalue {
    fn ast_nodes(&self) -> usize {
        match self {
            Self::Use { operand, .. }
            | Self::UseRetag { operand }
            | Self::Unary { operand, .. } => 1 + operand.ast_nodes(),
            Self::Binary { left, right, .. } => 1 + left.ast_nodes() + right.ast_nodes(),
            Self::Cast { operand, ty, .. } => 1 + operand.ast_nodes() + ty.ast_nodes(),
            Self::Discriminant { place } => 1 + place.ast_nodes(),
            Self::Ref { place, .. }
            | Self::AddressOf { place, .. }
            | Self::FakeAddressOf { place } => 1 + place.ast_nodes(),
            Self::AggregateTuple { fields } => {
                1 + fields.iter().map(Operand::ast_nodes).sum::<usize>()
            }
            Self::AggregateArray { elem_ty, elems } => {
                1 + elem_ty.ast_nodes() + elems.iter().map(Operand::ast_nodes).sum::<usize>()
            }
            Self::Repeat { elem_ty, operand, .. } => 1 + elem_ty.ast_nodes() + operand.ast_nodes(),
            Self::AggregateRangeTo { elem_ty, end } => 1 + elem_ty.ast_nodes() + end.ast_nodes(),
            Self::AggregateRangeFrom { elem_ty, start } => {
                1 + elem_ty.ast_nodes() + start.ast_nodes()
            }
            Self::AggregateRange { elem_ty, start, end } => {
                1 + elem_ty.ast_nodes() + start.ast_nodes() + end.ast_nodes()
            }
            Self::AggregateOption { inner_ty, payload, .. } => {
                1 + inner_ty.ast_nodes() + payload.as_ref().map_or(0, |op| op.ast_nodes())
            }
        }
    }
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

impl Statement {
    fn ast_nodes(&self) -> usize {
        match self {
            Self::Assign { value, .. } => 1 + value.ast_nodes(),
            Self::AssignPlace { place, value } => 1 + place.ast_nodes() + value.ast_nodes(),
            Self::StorageLive { .. }
            | Self::StorageDead { .. }
            | Self::PlaceMention { .. }
            | Self::Nop => 1,
        }
    }
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
    SliceIndexRange {
        mutability: Mutability,
        elem: Ty,
    },
    SliceIndexRangeFrom {
        mutability: Mutability,
        elem: Ty,
    },
    SliceIsEmpty {
        elem: Ty,
    },
    SliceSplitAt {
        mutability: Mutability,
        elem: Ty,
    },
    NumIsMultipleOf(IntTy),
    NumCheckedAdd(IntTy),
    NumCheckedMul(IntTy),
    NumCheckedSub(IntTy),
    NumSaturatingAdd(IntTy),
    NumWrappingShl(IntTy),
    NumWrappingShr(IntTy),
    NumLeadingZeros(IntTy),
    NumOverflowingAdd(IntTy),
    NumOverflowingSub(IntTy),
    CmpMin(IntTy),
    CmpMax(IntTy),
    MemReplace {
        ty: Ty,
    },
    OptionIsSome {
        inner: Ty,
    },
    OptionIsNone {
        inner: Ty,
    },
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
    IntToLeBytes {
        int_ty: IntTy,
    },
    ArrayEq {
        elem: Ty,
        len: usize,
    },
}

/// A `core::num` arithmetic method that Profile v1 calls through its pinned
/// sysroot body (`Trusted.MirAst.SysrootNumKind`). Profile v2 instead models
/// its `core` calls atomically through [`CoreCallOp`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SysrootNumKind {
    UncheckedAdd,
    UncheckedSub,
    UncheckedMul,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct SysrootNumOp {
    pub kind: SysrootNumKind,
    pub ty: IntTy,
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
    Call {
        callee: usize,
        args: Vec<Operand>,
        dst: u32,
        target: Option<u32>,
        unwind: UnwindAction,
    },
    SysrootCall {
        op: SysrootNumOp,
        args: Vec<Operand>,
        dst: u32,
        target: Option<u32>,
        unwind: UnwindAction,
    },
    Ret,
    Unreachable,
    Unsupported,
}

/// Pairwise local-disjointness of `.move` call operands and `dst`, matching
/// `Trusted.MirSemantics.moveDefinitelyDisjoint`.
fn check_move_disjoint(args: &[Operand], dst: u32) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    for arg in args {
        match arg {
            Operand::Move { local } if !seen.insert(*local) => {
                return Err(format!("duplicate Move operand local _{local} in call"));
            }
            Operand::CopyPlace { .. } | Operand::MovePlace { .. } => {
                return Err("call operands must be unprojected locals or constants".into());
            }
            _ => {}
        }
    }
    if !seen.insert(dst) {
        return Err(format!("call destination _{dst} aliases a Move operand"));
    }
    Ok(())
}

impl Terminator {
    fn ast_nodes(&self) -> usize {
        match self {
            Self::Goto { .. } | Self::Ret | Self::Unreachable | Self::Unsupported => 1,
            Self::SwitchInt { operand, targets, .. } => 2 + operand.ast_nodes() + targets.len(),
            Self::Assert { cond, .. } => 2 + cond.ast_nodes(),
            Self::CoreCall { op, args, dst, .. } => {
                let op_nodes = match op {
                    CoreCallOp::PtrAdd { pointee, .. } => 1 + pointee.ast_nodes(),
                    CoreCallOp::SliceIndexRange { elem, .. }
                    | CoreCallOp::SliceIndexRangeFrom { elem, .. }
                    | CoreCallOp::SliceIsEmpty { elem }
                    | CoreCallOp::SliceSplitAt { elem, .. }
                    | CoreCallOp::ArrayEq { elem, .. } => 1 + elem.ast_nodes(),
                    CoreCallOp::MemReplace { ty } => 1 + ty.ast_nodes(),
                    CoreCallOp::OptionIsSome { inner }
                    | CoreCallOp::OptionIsNone { inner }
                    | CoreCallOp::OptionTake { inner }
                    | CoreCallOp::OptionUnwrap { inner } => 1 + inner.ast_nodes(),
                    CoreCallOp::SliceLen
                    | CoreCallOp::SliceGetUncheckedRangeTo
                    | CoreCallOp::SliceGetUncheckedRangeFrom
                    | CoreCallOp::NumIsMultipleOf(_)
                    | CoreCallOp::NumCheckedAdd(_)
                    | CoreCallOp::NumCheckedMul(_)
                    | CoreCallOp::NumCheckedSub(_)
                    | CoreCallOp::NumSaturatingAdd(_)
                    | CoreCallOp::NumWrappingShl(_)
                    | CoreCallOp::NumWrappingShr(_)
                    | CoreCallOp::NumLeadingZeros(_)
                    | CoreCallOp::NumOverflowingAdd(_)
                    | CoreCallOp::NumOverflowingSub(_)
                    | CoreCallOp::CmpMin(_)
                    | CoreCallOp::CmpMax(_)
                    | CoreCallOp::UsizeUncheckedSub
                    | CoreCallOp::IntToLeBytes { .. } => 1,
                };
                1 + op_nodes + args.iter().map(Operand::ast_nodes).sum::<usize>() + dst.ast_nodes()
            }
            Self::Call { args, .. } | Self::SysrootCall { args, .. } => {
                2 + args.iter().map(Operand::ast_nodes).sum::<usize>()
            }
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

impl Block {
    fn ast_nodes(&self) -> usize {
        1 + self.statements.iter().map(Statement::ast_nodes).sum::<usize>()
            + self.terminator.ast_nodes()
    }
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
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::AddUnchecked
        | BinOp::SubUnchecked
        | BinOp::MulUnchecked
        | BinOp::Div
        | BinOp::Rem => match (l_ty, r_ty) {
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
/// would mix reference and non-fake raw-pointer locals, which
/// [`validate_local_tys_with_exemptions`] refuses. `IntToPtr`
/// (`PointerWithExposedProvenance`) admits only a `usize` source and a sized
/// raw-pointer target, matching `pointer_with_exposed_provenance_cast`
/// ("First cast to usize.").
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
        (CastKind::Unsize, src_ptr, dst_ptr) => match (src_ptr, dst_ptr) {
            (
                Ty::Ref {
                    mutability: src_mut,
                    pointee: src_pt,
                },
                Ty::Ref {
                    mutability: dst_mut,
                    pointee: dst_pt,
                },
            )
            | (
                Ty::RawPtr {
                    mutability: src_mut,
                    pointee: src_pt,
                },
                Ty::RawPtr {
                    mutability: dst_mut,
                    pointee: dst_pt,
                },
            ) => match (&**src_pt, &**dst_pt) {
                (Ty::Array { elem: e1, .. }, Ty::Slice { elem: e2 })
                    if e1 == e2
                        && e1.is_sized()
                        && !(*src_mut == Mutability::Shared && *dst_mut == Mutability::Mut) =>
                {
                    Ok(())
                }
                _ => Err(format!(
                    "unsupported Unsize cast from {src_ty:?} to {cast_ty:?}"
                )),
            },
            _ => Err(format!(
                "unsupported Unsize cast from {src_ty:?} to {cast_ty:?}"
            )),
        },
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
        | Ty::Array { .. }
        | Ty::Tuple { .. }
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::Slice { .. }
        | Ty::RangeTo { .. }
        | Ty::RangeFrom { .. }
        | Ty::Range { .. }
        | Ty::Option { .. } => Err(format!(
            "SwitchInt operand type {discr_ty:?} is not primitive-switchable"
        )),
    }
}

fn place_mentions_local_v2(place: &Place, lid: u32) -> bool {
    place.local == lid
}

fn operand_mentions_local_v2(op: &Operand, lid: u32) -> bool {
    match op {
        Operand::Copy { local } | Operand::Move { local } => *local == lid,
        Operand::CopyPlace { place } | Operand::MovePlace { place } => {
            place_mentions_local_v2(place, lid)
        }
        Operand::Constant { .. } => false,
    }
}

fn rvalue_mentions_local_v2(rv: &Rvalue, lid: u32) -> bool {
    match rv {
        Rvalue::Use { operand, .. }
        | Rvalue::UseRetag { operand }
        | Rvalue::Unary { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. }
        | Rvalue::AggregateRangeTo { end: operand, .. }
        | Rvalue::AggregateRangeFrom { start: operand, .. } => {
            operand_mentions_local_v2(operand, lid)
        }
        Rvalue::Binary { left, right, .. }
        | Rvalue::AggregateRange { start: left, end: right, .. } => {
            operand_mentions_local_v2(left, lid) || operand_mentions_local_v2(right, lid)
        }
        Rvalue::AggregateOption { payload, .. } => {
            payload.as_deref().is_some_and(|op| operand_mentions_local_v2(op, lid))
        }
        Rvalue::Discriminant { place }
        | Rvalue::Ref { place, .. }
        | Rvalue::AddressOf { place, .. }
        | Rvalue::FakeAddressOf { place } => place_mentions_local_v2(place, lid),
        Rvalue::AggregateTuple { fields: ops } | Rvalue::AggregateArray { elems: ops, .. } => {
            ops.iter().any(|op| operand_mentions_local_v2(op, lid))
        }
    }
}

fn terminator_mentions_local_v2(term: &Terminator, lid: u32) -> bool {
    match term {
        Terminator::Goto { .. }
        | Terminator::Ret
        | Terminator::Unreachable
        | Terminator::Unsupported => false,
        Terminator::SwitchInt { operand, .. } => operand_mentions_local_v2(operand, lid),
        Terminator::Assert { cond, .. } => operand_mentions_local_v2(cond, lid),
        Terminator::CoreCall { args, dst, .. } => {
            args.iter().any(|op| operand_mentions_local_v2(op, lid))
                || place_mentions_local_v2(dst, lid)
        }
        Terminator::Call { args, dst, .. } | Terminator::SysrootCall { args, dst, .. } => {
            args.iter().any(|op| operand_mentions_local_v2(op, lid)) || *dst == lid
        }
    }
}

fn fake_address_of_types_match_v2(local_tys: &[Ty], dst_id: u32, src: &Place) -> bool {
    if src.local == dst_id || src.projection.as_slice() != [PlaceElem::Deref] {
        return false;
    }
    let (Some(base_ty), Some(dst_ty)) = (
        local_tys.get(src.local as usize),
        local_tys.get(dst_id as usize),
    ) else {
        return false;
    };
    let (Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. }) = base_ty else {
        return false;
    };
    !matches!(&**pointee, Ty::OverflowPair(_))
        && *dst_ty
            == Ty::RawPtr {
                mutability: Mutability::Shared,
                pointee: pointee.clone(),
            }
}

/// Mirror `Trusted.MirSemantics.isFakePtrMetadataLocalV2`: `lid > arg_count`,
/// `local_tys[lid]` is a top-level `*const` raw pointer, at least one
/// unprojected `FakeAddressOf` writes to `lid`, and every statement/terminator
/// in `blocks` uses `lid` strictly as an unprojected `FakeAddressOf (*base)`
/// destination (`base != lid`) or an unprojected `UnOp::PtrMetadata` operand.
fn is_fake_ptr_metadata_local_v2(
    arg_count: usize,
    local_tys: &[Ty],
    blocks: &[Block],
    lid: usize,
) -> bool {
    if lid <= arg_count {
        return false;
    }
    let Ok(lid_u32) = u32::try_from(lid) else {
        return false;
    };
    if !matches!(
        local_tys.get(lid),
        Some(Ty::RawPtr {
            mutability: Mutability::Shared,
            ..
        })
    ) {
        return false;
    }
    let mut saw_fake_assign = false;
    for bb in blocks {
        for stmt in &bb.statements {
            match stmt {
                Statement::Assign { local, value } => {
                    if *local == lid_u32 {
                        let Rvalue::FakeAddressOf { place } = value else {
                            return false;
                        };
                        if !fake_address_of_types_match_v2(local_tys, lid_u32, place) {
                            return false;
                        }
                        saw_fake_assign = true;
                    } else if rvalue_mentions_local_v2(value, lid_u32) {
                        let ok = match value {
                            Rvalue::Unary {
                                op: UnOp::PtrMetadata,
                                operand,
                            } => match operand {
                                Operand::Copy { local } | Operand::Move { local } => {
                                    *local == lid_u32
                                }
                                Operand::CopyPlace { place } | Operand::MovePlace { place } => {
                                    place.local == lid_u32 && place.projection.is_empty()
                                }
                                Operand::Constant { .. } => false,
                            },
                            _ => false,
                        };
                        if !ok {
                            return false;
                        }
                    }
                }
                Statement::AssignPlace { place, value } => {
                    if place_mentions_local_v2(place, lid_u32) {
                        return false;
                    }
                    if rvalue_mentions_local_v2(value, lid_u32) {
                        let ok = match value {
                            Rvalue::Unary {
                                op: UnOp::PtrMetadata,
                                operand,
                            } => match operand {
                                Operand::Copy { local } | Operand::Move { local } => {
                                    *local == lid_u32
                                }
                                Operand::CopyPlace { place } | Operand::MovePlace { place } => {
                                    place.local == lid_u32 && place.projection.is_empty()
                                }
                                Operand::Constant { .. } => false,
                            },
                            _ => false,
                        };
                        if !ok {
                            return false;
                        }
                    }
                }
                Statement::StorageLive { .. } | Statement::StorageDead { .. } | Statement::Nop => {
                }
                // Intentionally stricter (fail-closed) than Lean/eval, which
                // lower `PlaceMention` to `.nop` (`lean.rs`): rustc does not
                // emit `PlaceMention` on synthetic `FakeForPtrMetadata` temps.
                Statement::PlaceMention { local } => {
                    if *local == lid_u32 {
                        return false;
                    }
                }
            }
        }
        if terminator_mentions_local_v2(&bb.terminator, lid_u32) {
            return false;
        }
    }
    saw_fake_assign
}

fn collect_fake_ptr_metadata_locals_v2(
    arg_count: usize,
    local_tys: &[Ty],
    blocks: &[Block],
) -> BTreeSet<usize> {
    (0..local_tys.len())
        .filter(|&idx| is_fake_ptr_metadata_local_v2(arg_count, local_tys, blocks, idx))
        .collect()
}

/// Validates that every local in a MIR body is `Sized` and belongs to the
/// Profile v2 local type fragment
/// (`Trusted.MirSemantics.isSupportedV2LocalTy`), exempting `fake_meta_locals`
/// from the reference / raw-pointer mixing check
/// (`Trusted.MirSemantics.bodyMixesRefsAndRawPtrsV2`).
pub(crate) fn validate_local_tys_with_exemptions(
    local_tys: &[Ty],
    fake_meta_locals: &BTreeSet<usize>,
) -> Result<(), String> {
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
    // from raw pointers or access referenced memory through them; metadata-only
    // `FakeForPtrMetadata` temporaries (`isFakePtrMetadataLocalV2`) never incur
    // a retag and are read solely by `UnOp::PtrMetadata`.
    let has_non_fake_raw_ptr = local_tys
        .iter()
        .enumerate()
        .any(|(idx, ty)| ty.has_raw_ptr_v2() && !fake_meta_locals.contains(&idx));
    if local_tys.iter().any(Ty::has_ref_v2) && has_non_fake_raw_ptr {
        return Err("body mixes reference and raw-pointer locals, which Profile v2 \
             refuses because it does not model Rust's pointer aliasing rules"
            .to_string());
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn validate_local_tys(local_tys: &[Ty]) -> Result<(), String> {
    validate_local_tys_with_exemptions(local_tys, &BTreeSet::new())
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
    /// Intra-crate static `ty::FnDef` callee identities extracted from MIR
    /// assign-rvalue operands and call/branch/assert terminators for Tarjan SCC
    /// `.olean` sharding. Omitted from `capture.json` and projected into
    /// `capture_shards.json`.
    #[serde(skip)]
    callees: BTreeSet<String>,
}

impl Body {
    #[cfg(test)]
    pub fn try_new(
        arg_count: usize,
        is_unsafe: bool,
        local_tys: Vec<Ty>,
        blocks: Vec<Block>,
        identity: String,
    ) -> Result<Self, String> {
        Self::try_new_with_callees(
            arg_count,
            is_unsafe,
            local_tys,
            blocks,
            identity,
            BTreeSet::new(),
        )
    }

    pub fn try_new_with_callees(
        arg_count: usize,
        is_unsafe: bool,
        local_tys: Vec<Ty>,
        blocks: Vec<Block>,
        identity: String,
        callees: BTreeSet<String>,
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
        let fake_meta_locals =
            collect_fake_ptr_metadata_locals_v2(arg_count, &local_tys, &blocks);
        validate_local_tys_with_exemptions(&local_tys, &fake_meta_locals)?;
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
            let mut downcast_variant: Option<usize> = None;
            for (step, elem) in place.projection.iter().enumerate() {
                match elem {
                    PlaceElem::Deref => {
                        if saw_deref || step != 0 || downcast_variant.is_some() {
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
                    PlaceElem::Downcast { variant_idx } => {
                        if saw_deref || downcast_variant.is_some() {
                            return Err("nested or post-deref downcast projections are unsupported".into());
                        }
                        if !matches!(cur, Ty::Option { .. }) || *variant_idx != 1 {
                            return Err(format!("unsupported downcast variant {variant_idx} on {cur:?}"));
                        }
                        downcast_variant = Some(*variant_idx);
                    }
                    PlaceElem::Field { index, ty } => {
                        let usize_ty = Ty::Int(IntTy {
                            width: IntWidth::Isize,
                            signed: false,
                        });
                        if let Some(variant) = downcast_variant.take() {
                            if variant != 1 || *index != 0 {
                                return Err(format!("unsupported downcast field {index} for variant {variant}"));
                            }
                            let Ty::Option { elem: inner } = &cur else {
                                return Err("downcast field requires Option".into());
                            };
                            if *ty != **inner {
                                return Err(format!(
                                    "Option downcast field type {ty:?} disagrees with {inner:?}"
                                ));
                            }
                            cur = (**inner).clone();
                            continue;
                        }
                        let expected_field = match &cur {
                            Ty::Tuple { fields } => fields.get(*index).cloned(),
                            Ty::OverflowPair(ity) if *index == 0 => Some(Ty::Int(*ity)),
                            Ty::OverflowPair(_) if *index == 1 => Some(Ty::Bool),
                            Ty::RangeTo { elem: e } | Ty::RangeFrom { elem: e }
                                if *index == 0 && **e == usize_ty =>
                            {
                                Some(usize_ty)
                            }
                            Ty::Range { elem: e }
                                if (*index == 0 || *index == 1) && **e == usize_ty =>
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
                    PlaceElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    } => {
                        let Ty::Array { elem, len } = &cur else {
                            return Err(format!(
                                "ConstantIndex projection requires fixed-size array type, got {cur:?}"
                            ));
                        };
                        // Match `Trusted.MirSemantics.constantIndexOffset`:
                        // `from_end` is a 1-based offset from `len`
                        // (`1 <= offset <= len`), otherwise 0-based
                        // (`offset < len`), with `len >= min_length`.
                        let out_of_bounds = if *from_end {
                            *offset == 0 || *offset > *len
                        } else {
                            *offset >= *len
                        };
                        if *len < *min_length || out_of_bounds {
                            return Err(format!(
                                "ConstantIndex [{offset} of min {min_length}, from_end={from_end}] out of bounds for array length {len}"
                            ));
                        }
                        cur = (**elem).clone();
                    }
                }
            }
            if downcast_variant.is_some() {
                return Err("downcast projection must be followed by field projection".into());
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
                    validate_constant(ty, lit)?;
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
                Rvalue::Discriminant { place } => {
                    let src_ty = check_place(local_tys, place, "discriminant", false, false)?;
                    let expected_discr = match &src_ty {
                        Ty::Enum(ety) => ety.discr(),
                        Ty::Ordering => IntTy {
                            width: IntWidth::I8,
                            signed: true,
                        },
                        Ty::Option { .. } => IntTy {
                            width: IntWidth::Isize,
                            signed: true,
                        },
                        _ => {
                            return Err(
                                "discriminant rvalue requires a fieldless enum, Ordering, or Option place"
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
                        // mixes reference and non-fake raw-pointer locals and
                        // is already refused by
                        // `validate_local_tys_with_exemptions`; refuse it here
                        // too rather than keep an unreachable rule.
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
                        // mixes reference and non-fake raw-pointer locals and
                        // is already refused by
                        // `validate_local_tys_with_exemptions`; refuse it here
                        // too rather than keep an unreachable rule.
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
                Rvalue::FakeAddressOf { place } => {
                    if place.projection.as_slice() != [PlaceElem::Deref] {
                        return Err(
                            "Rvalue::FakeAddressOf requires a single Deref projection".into(),
                        );
                    }
                    let base = check_local(local_tys, place.local, "fakeAddressOf")?;
                    if !matches!(base, Ty::Ref { .. } | Ty::RawPtr { .. }) {
                        return Err(
                            "Rvalue::FakeAddressOf base local must be a reference or raw pointer"
                                .into(),
                        );
                    }
                    let pointee = check_place(local_tys, place, "fakeAddressOf", true, false)?;
                    refuse_overflow_pair_pointee(&pointee, "Rvalue::FakeAddressOf")?;
                    let expected = Ty::RawPtr {
                        mutability: Mutability::Shared,
                        pointee: Box::new(pointee),
                    };
                    if *dst_ty != expected {
                        return Err(format!(
                            "Rvalue::FakeAddressOf type {expected:?} disagrees with destination {dst_ty:?}"
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
                Rvalue::AggregateArray { elem_ty, elems } => {
                    let Ty::Array {
                        elem: dst_elem,
                        len: dst_len,
                    } = dst_ty
                    else {
                        return Err(format!(
                            "AggregateArray requires Array destination type, got {dst_ty:?}"
                        ));
                    };
                    if elem_ty != &**dst_elem || elems.len() != *dst_len || !elem_ty.is_sized() {
                        return Err("AggregateArray element type or length disagrees with destination array".into());
                    }
                    for op in elems {
                        let got = check_operand(local_tys, op)?;
                        if &got != elem_ty {
                            return Err(format!(
                                "AggregateArray element operand type {got:?} disagrees with {elem_ty:?}"
                            ));
                        }
                    }
                }
                Rvalue::Repeat {
                    operand,
                    elem_ty,
                    count,
                } => {
                    let Ty::Array {
                        elem: dst_elem,
                        len: dst_len,
                    } = dst_ty
                    else {
                        return Err(format!(
                            "Repeat requires Array destination type, got {dst_ty:?}"
                        ));
                    };
                    if elem_ty != &**dst_elem || *count != *dst_len || !elem_ty.is_sized() {
                        return Err("Repeat element type or length disagrees with destination array".into());
                    }
                    let got = check_operand(local_tys, operand)?;
                    if &got != elem_ty {
                        return Err(format!(
                            "Repeat operand type {got:?} disagrees with {elem_ty:?}"
                        ));
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
                Rvalue::AggregateRange { elem_ty, start, end } => {
                    if *elem_ty != usize_ty
                        || *dst_ty
                            != (Ty::Range {
                                elem: Box::new(usize_ty.clone()),
                            })
                    {
                        return Err("AggregateRange requires Range<usize>".into());
                    }
                    let got_start = check_operand(local_tys, start)?;
                    let got_end = check_operand(local_tys, end)?;
                    if got_start != usize_ty || got_end != usize_ty {
                        return Err("AggregateRange bounds must be usize".into());
                    }
                }
                Rvalue::AggregateOption {
                    variant_idx,
                    inner_ty,
                    payload,
                } => {
                    if *dst_ty
                        != (Ty::Option {
                            elem: Box::new(inner_ty.clone()),
                        })
                    {
                        return Err("AggregateOption requires Option<inner_ty> destination".into());
                    }
                    match (variant_idx, payload) {
                        (0, None) => {}
                        (1, Some(op)) => {
                            let got = check_operand(local_tys, op)?;
                            if got != *inner_ty {
                                return Err("AggregateOption Some payload type mismatch".into());
                            }
                        }
                        _ => return Err("invalid AggregateOption variant/payload".into()),
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
                        if matches!(value, Rvalue::FakeAddressOf { .. })
                            && !fake_meta_locals.contains(&(*local as usize))
                        {
                            return Err(format!(
                                "Rvalue::FakeAddressOf destination _{local} must be a non-argument \
                                 *const temporary read exclusively by UnOp::PtrMetadata"
                            ));
                        }
                    }
                    Statement::AssignPlace { place, value } => {
                        if matches!(value, Rvalue::FakeAddressOf { .. }) {
                            return Err(
                                "Rvalue::FakeAddressOf destination must be an unprojected local"
                                    .into(),
                            );
                        }
                        let require_mut_deref =
                            matches!(place.projection.first(), Some(PlaceElem::Deref));
                        let dst_ty = check_place(
                            &local_tys,
                            place,
                            "assignment",
                            false,
                            require_mut_deref,
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
                        (CoreCallOp::IntToLeBytes { int_ty }, [arg_ty])
                            if *arg_ty == Ty::Int(*int_ty)
                                && dst_ty
                                    == Ty::Array {
                                        elem: Box::new(Ty::Int(IntTy {
                                            width: IntWidth::I8,
                                            signed: false,
                                        })),
                                        len: (int_ty.width.bits() / 8) as usize,
                                    } => {}
                        (
                            CoreCallOp::ArrayEq { elem, len },
                            [
                                Ty::Ref {
                                    pointee: pt1,
                                    ..
                                },
                                Ty::Ref {
                                    pointee: pt2,
                                    ..
                                },
                            ],
                        ) if elem.is_array_eq_elem_supported()
                            && **pt1
                                == (Ty::Array {
                                    elem: Box::new(elem.clone()),
                                    len: *len,
                                })
                            && **pt2
                                == (Ty::Array {
                                    elem: Box::new(elem.clone()),
                                    len: *len,
                                })
                            && dst_ty == Ty::Bool => {}
                        (
                            CoreCallOp::SliceIndexRange { mutability, elem },
                            [Ty::Ref {
                                mutability: in_mut,
                                pointee,
                            }, Ty::Range { elem: idx_ty }],
                        ) if **idx_ty == usize_ty
                            && elem.is_sized_no_ref()
                            && matches!(&**pointee, Ty::Slice { elem: e } if **e == *elem)
                            && *in_mut == *mutability
                            && dst_ty
                                == Ty::Ref {
                                    mutability: *mutability,
                                    pointee: Box::new(Ty::Slice {
                                        elem: Box::new(elem.clone()),
                                    }),
                                } => {}
                        (
                            CoreCallOp::SliceIndexRangeFrom { mutability, elem },
                            [Ty::Ref {
                                mutability: in_mut,
                                pointee,
                            }, Ty::RangeFrom { elem: idx_ty }],
                        ) if **idx_ty == usize_ty
                            && elem.is_sized_no_ref()
                            && matches!(&**pointee, Ty::Slice { elem: e } if **e == *elem)
                            && *in_mut == *mutability
                            && dst_ty
                                == Ty::Ref {
                                    mutability: *mutability,
                                    pointee: Box::new(Ty::Slice {
                                        elem: Box::new(elem.clone()),
                                    }),
                                } => {}
                        (
                            CoreCallOp::SliceIsEmpty { elem },
                            [Ty::Ref { pointee, .. }],
                        ) if elem.is_sized_no_ref()
                            && matches!(&**pointee, Ty::Slice { elem: e } if **e == *elem)
                            && dst_ty == Ty::Bool => {}
                        (
                            CoreCallOp::SliceSplitAt { mutability, elem },
                            [Ty::Ref {
                                mutability: in_mut,
                                pointee,
                            }, mid_ty],
                        ) if *mid_ty == usize_ty
                            && elem.is_sized_no_ref()
                            && matches!(&**pointee, Ty::Slice { elem: e } if **e == *elem)
                            && *in_mut == *mutability
                            && dst_ty
                                == Ty::Tuple {
                                    fields: vec![
                                        Ty::Ref {
                                            mutability: *mutability,
                                            pointee: Box::new(Ty::Slice {
                                                elem: Box::new(elem.clone()),
                                            }),
                                        },
                                        Ty::Ref {
                                            mutability: *mutability,
                                            pointee: Box::new(Ty::Slice {
                                                elem: Box::new(elem.clone()),
                                            }),
                                        },
                                    ],
                                } => {}
                        (CoreCallOp::NumIsMultipleOf(ity), [l_ty, r_ty])
                            if !ity.signed
                                && *l_ty == Ty::Int(*ity)
                                && *r_ty == Ty::Int(*ity)
                                && dst_ty == Ty::Bool => {}
                        (
                            CoreCallOp::NumCheckedAdd(ity)
                            | CoreCallOp::NumCheckedMul(ity)
                            | CoreCallOp::NumCheckedSub(ity),
                            [l_ty, r_ty],
                        ) if *l_ty == Ty::Int(*ity)
                            && *r_ty == Ty::Int(*ity)
                            && dst_ty
                                == Ty::Option {
                                    elem: Box::new(Ty::Int(*ity)),
                                } => {}
                        (CoreCallOp::NumSaturatingAdd(ity), [l_ty, r_ty])
                            if *l_ty == Ty::Int(*ity)
                            && *r_ty == Ty::Int(*ity)
                            && dst_ty == Ty::Int(*ity) => {}
                        (
                            CoreCallOp::NumWrappingShl(ity) | CoreCallOp::NumWrappingShr(ity),
                            [l_ty, r_ty],
                        ) if *l_ty == Ty::Int(*ity)
                            && *r_ty
                                == Ty::Int(IntTy {
                                    width: IntWidth::I32,
                                    signed: false,
                                })
                            && dst_ty == Ty::Int(*ity) => {}
                        (CoreCallOp::NumLeadingZeros(ity), [l_ty])
                            if *l_ty == Ty::Int(*ity)
                                && dst_ty
                                    == Ty::Int(IntTy {
                                        width: IntWidth::I32,
                                        signed: false,
                                    }) => {}
                        (
                            CoreCallOp::NumOverflowingAdd(ity) | CoreCallOp::NumOverflowingSub(ity),
                            [l_ty, r_ty],
                        ) if *l_ty == Ty::Int(*ity)
                            && *r_ty == Ty::Int(*ity)
                            && dst_ty == Ty::OverflowPair(*ity) => {}
                        (
                            CoreCallOp::CmpMin(ity) | CoreCallOp::CmpMax(ity),
                            [l_ty, r_ty],
                        ) if *l_ty == Ty::Int(*ity)
                            && *r_ty == Ty::Int(*ity)
                            && dst_ty == Ty::Int(*ity) => {}
                        (
                            CoreCallOp::MemReplace { ty },
                            [Ty::Ref {
                                mutability: Mutability::Mut,
                                pointee,
                            }, src_ty],
                        ) if ty.is_sized_no_ref()
                            && **pointee == *ty
                            && *src_ty == *ty
                            && dst_ty == *ty => {}
                        (
                            CoreCallOp::OptionIsSome { inner } | CoreCallOp::OptionIsNone { inner },
                            [Ty::Ref { pointee, .. }],
                        ) if inner.is_sized_no_ref()
                            && inner.is_option_payload_supported_v2()
                            && matches!(&**pointee, Ty::Option { elem } if **elem == *inner)
                            && dst_ty == Ty::Bool => {}
                        (
                            CoreCallOp::OptionTake { inner },
                            [Ty::Ref {
                                mutability: Mutability::Mut,
                                pointee,
                            }],
                        ) if inner.is_sized_no_ref()
                            && inner.is_option_payload_supported_v2()
                            && matches!(&**pointee, Ty::Option { elem } if **elem == *inner)
                            && dst_ty
                                == Ty::Option {
                                    elem: Box::new(inner.clone()),
                                } => {}
                        (CoreCallOp::OptionUnwrap { inner }, [opt_ty])
                            if *opt_ty
                                == Ty::Option {
                                    elem: Box::new(inner.clone()),
                                }
                                && dst_ty == *inner => {}
                        _ => {
                            return Err(format!(
                                "invalid CoreCall {op:?} arguments {arg_tys:?} -> {dst_ty:?}"
                            ));
                        }
                    }
                    check_block(*target)?;
                }
                Terminator::Call {
                    args, dst, target, ..
                } => {
                    for arg in args {
                        check_operand(&local_tys, arg)?;
                    }
                    check_local(&local_tys, *dst, "call destination")?;
                    check_move_disjoint(args, *dst)?;
                    if let Some(target_block) = target {
                        check_block(*target_block)?;
                    }
                }
                Terminator::SysrootCall {
                    op,
                    args,
                    dst,
                    target,
                    ..
                } => {
                    if args.len() != 2 {
                        return Err(format!(
                            "sysroot numeric call expects 2 arguments, got {}",
                            args.len()
                        ));
                    }
                    let expected_ty = Ty::Int(op.ty);
                    for (idx, arg) in args.iter().enumerate() {
                        let arg_ty = check_operand(&local_tys, arg)?;
                        if arg_ty != expected_ty {
                            return Err(format!(
                                "sysroot numeric call argument {idx} type {arg_ty:?} \
                                 disagrees with {expected_ty:?}"
                            ));
                        }
                    }
                    let dst_ty = check_local(&local_tys, *dst, "sysroot call destination")?;
                    if *dst_ty != expected_ty {
                        return Err(format!(
                            "sysroot numeric call destination type {dst_ty:?} \
                             disagrees with {expected_ty:?}"
                        ));
                    }
                    check_move_disjoint(args, *dst)?;
                    if let Some(target_block) = target {
                        check_block(*target_block)?;
                    }
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
            callees,
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
                        Rvalue::Discriminant { place } => {
                            if !place.projection.is_empty() {
                                return true;
                            }
                        }
                        Rvalue::UseRetag { .. }
                        | Rvalue::Ref { .. }
                        | Rvalue::AddressOf { .. }
                        | Rvalue::FakeAddressOf { .. }
                        | Rvalue::AggregateTuple { .. }
                        | Rvalue::AggregateArray { .. }
                        | Rvalue::Repeat { .. }
                        | Rvalue::AggregateRangeTo { .. }
                        | Rvalue::AggregateRangeFrom { .. }
                        | Rvalue::AggregateRange { .. }
                        | Rvalue::AggregateOption { .. } => return true,
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
                // Intra-crate and `core::num` sysroot calls are Profile v1
                // terminators; `Program::try_new` refuses them in a Profile v2
                // program.
                Terminator::Call { .. }
                | Terminator::SysrootCall { .. }
                | Terminator::Goto { .. }
                | Terminator::Ret
                | Terminator::Unreachable
                | Terminator::Unsupported => {}
            }
        }
        false
    }

    pub fn callees(&self) -> &BTreeSet<String> {
        &self.callees
    }

    /// Deterministic AST-node weight used for sharding budgets, counting local
    /// types, basic blocks, and exact `_root_.String.ofList` and
    /// `_root_.Char.ofNat` identity chunk nodes matching `lean.rs`.
    pub fn ast_nodes(&self) -> usize {
        self.identity_ast_nodes()
            + self.local_tys.iter().map(Ty::ast_nodes).sum::<usize>()
            + self.blocks.iter().map(Block::ast_nodes).sum::<usize>()
    }

    fn identity_ast_nodes(&self) -> usize {
        let id_chars = self.identity.chars().count();
        if id_chars == 0 {
            return 1;
        }
        // Matches `lean::identity_at`: 16-char `_root_.String.ofList` chunks
        // joined by `Trusted.MirAst.stringAppend`, with one
        // `(_root_.Char.ofNat n)` term per Unicode scalar character.
        let chunks = id_chars.div_ceil(16);
        1 + (2 * chunks - 1) + 2 * id_chars
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
                        Rvalue::Ref { place, .. }
                        | Rvalue::AddressOf { place, .. }
                        | Rvalue::FakeAddressOf { place } => {
                            place.collect_enum_ids(out);
                        }
                        Rvalue::AggregateTuple { fields } => {
                            for f in fields {
                                f.collect_enum_ids(out);
                            }
                        }
                        Rvalue::AggregateArray { elem_ty, elems } => {
                            elem_ty.collect_enum_ids(out);
                            for e in elems {
                                e.collect_enum_ids(out);
                            }
                        }
                        Rvalue::Repeat {
                            operand, elem_ty, ..
                        } => {
                            operand.collect_enum_ids(out);
                            elem_ty.collect_enum_ids(out);
                        }
                        Rvalue::AggregateRangeTo { elem_ty, end } => {
                            elem_ty.collect_enum_ids(out);
                            end.collect_enum_ids(out);
                        }
                        Rvalue::AggregateRangeFrom { elem_ty, start } => {
                            elem_ty.collect_enum_ids(out);
                            start.collect_enum_ids(out);
                        }
                        Rvalue::AggregateRange { elem_ty, start, end } => {
                            elem_ty.collect_enum_ids(out);
                            start.collect_enum_ids(out);
                            end.collect_enum_ids(out);
                        }
                        Rvalue::AggregateOption {
                            inner_ty, payload, ..
                        } => {
                            inner_ty.collect_enum_ids(out);
                            if let Some(op) = payload {
                                op.collect_enum_ids(out);
                            }
                        }
                        Rvalue::Discriminant { place } => place.collect_enum_ids(out),
                    }
                }
            }
            match &block.terminator {
                Terminator::SwitchInt { operand, .. } => operand.collect_enum_ids(out),
                Terminator::Assert { cond, .. } => cond.collect_enum_ids(out),
                Terminator::CoreCall { op, args, dst, .. } => {
                    match op {
                        CoreCallOp::PtrAdd { pointee, .. } | CoreCallOp::MemReplace { ty: pointee } => {
                            pointee.collect_enum_ids(out);
                        }
                        CoreCallOp::ArrayEq { elem, .. }
                        | CoreCallOp::SliceIndexRange { elem, .. }
                        | CoreCallOp::SliceIndexRangeFrom { elem, .. }
                        | CoreCallOp::SliceIsEmpty { elem }
                        | CoreCallOp::SliceSplitAt { elem, .. }
                        | CoreCallOp::OptionIsSome { inner: elem }
                        | CoreCallOp::OptionIsNone { inner: elem }
                        | CoreCallOp::OptionTake { inner: elem }
                        | CoreCallOp::OptionUnwrap { inner: elem } => {
                            elem.collect_enum_ids(out);
                        }
                        _ => {}
                    }
                    for a in args {
                        a.collect_enum_ids(out);
                    }
                    dst.collect_enum_ids(out);
                }
                Terminator::Call { args, .. } | Terminator::SysrootCall { args, .. } => {
                    for arg in args {
                        arg.collect_enum_ids(out);
                    }
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
    panic: PanicStrategy,
    has_local_panic_handler: bool,
    mir_profile_version: u32,
    bodies: Vec<Body>,
}

impl Program {
    #[cfg(test)]
    pub fn try_new(scope: Scope, bodies: Vec<Body>) -> Result<Self, String> {
        Self::try_new_with_options(scope, false, PanicStrategy::Unwind, false, bodies)
    }

    pub fn try_new_with_options(
        scope: Scope,
        overflow_checks: bool,
        panic: PanicStrategy,
        has_local_panic_handler: bool,
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
        for body in &bodies {
            for block in &body.blocks {
                if let Terminator::Call {
                    callee, args, dst, ..
                } = &block.terminator
                {
                    let callee_body = bodies.get(*callee).ok_or_else(|| {
                        format!(
                            "call target body index {callee} out of bounds for {} bodies",
                            bodies.len()
                        )
                    })?;
                    if args.len() != callee_body.arg_count {
                        return Err(format!(
                            "call argument count {} disagrees with callee {} arity {}",
                            args.len(),
                            callee_body.identity,
                            callee_body.arg_count
                        ));
                    }
                    let dst_ty = &body.local_tys[*dst as usize];
                    if *dst_ty != callee_body.local_tys[0] {
                        return Err(format!(
                            "call destination type {dst_ty:?} disagrees with callee {} return type {:?}",
                            callee_body.identity,
                            callee_body.local_tys[0]
                        ));
                    }
                    for (idx, arg) in args.iter().enumerate() {
                        let arg_ty = match arg {
                            Operand::Copy { local } | Operand::Move { local } => {
                                &body.local_tys[*local as usize]
                            }
                            Operand::Constant { ty, .. } => ty,
                            Operand::CopyPlace { .. } | Operand::MovePlace { .. } => {
                                return Err(format!(
                                    "call argument {idx} must be an unprojected local or constant"
                                ));
                            }
                        };
                        let param_ty = &callee_body.local_tys[1 + idx];
                        if arg_ty != param_ty {
                            return Err(format!(
                                "call argument {idx} type {arg_ty:?} disagrees with callee {} parameter type {param_ty:?}",
                                callee_body.identity
                            ));
                        }
                    }
                }
            }
        }
        let mir_profile_version = if bodies.iter().any(Body::uses_profile_v2) {
            2
        } else {
            1
        };
        // `Trusted.MirSemantics.evalStepV2` executes a single frame and faults
        // on `.call` and `.sysrootCall`, so refuse them here rather than emit
        // a program whose calls can only fault.
        if mir_profile_version == 2
            && let Some(body) = bodies.iter().find(|body| {
                body.blocks.iter().any(|block| {
                    matches!(
                        block.terminator,
                        Terminator::Call { .. } | Terminator::SysrootCall { .. }
                    )
                })
            })
        {
            return Err(format!(
                "{} makes a Profile v1 call in a Profile v2 program",
                body.identity
            ));
        }
        Ok(Self {
            scope,
            overflow_checks,
            panic,
            has_local_panic_handler,
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

    pub fn panic(&self) -> PanicStrategy {
        self.panic
    }

    pub fn has_local_panic_handler(&self) -> bool {
        self.has_local_panic_handler
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
    /// Unstable features the operator admitted on a normal crate with
    /// `--allow-unstable-feature` (sorted). This and the following feature
    /// lists are omitted when empty, so default captures keep their exact
    /// manifest bytes.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub allowed_unstable_features: Vec<String>,
    /// Unstable features that `tcx.features()` reports the crate enabled
    /// (sorted), each a member of `allowed_unstable_features`.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub observed_unstable_features: Vec<String>,
    /// The subset of `observed_unstable_features` that `rustc` marks
    /// incomplete (sorted).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub incomplete_observed_unstable_features: Vec<String>,
    /// Language features the crate enables with `#![feature(...)]` that the
    /// pinned compiler has already stabilized (sorted). They activate no
    /// unstable behavior and do not taint.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub stabilized_features_present: Vec<String>,
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

impl Manifest {
    /// Permute `program.bodies` into canonical callee-first shard order
    /// (`new_bodies[new_idx] = old_bodies[permutation[new_idx]]`) while
    /// remapping every `selected[i].body_index` to its new `DefId`.
    pub fn reorder_bodies(&mut self, permutation: &[usize]) -> Result<(), String> {
        let n = self.program.bodies.len();
        if permutation.len() != n {
            return Err(format!(
                "body permutation length {} disagrees with body count {n}",
                permutation.len()
            ));
        }
        let mut old_to_new = vec![None; n];
        for (new_idx, &old_idx) in permutation.iter().enumerate() {
            let Some(slot) = old_to_new.get_mut(old_idx) else {
                return Err(format!("body permutation index {old_idx} out of bounds for {n}"));
            };
            if slot.is_some() {
                return Err(format!("duplicate body index {old_idx} in permutation"));
            }
            *slot = Some(new_idx);
        }
        let mut old_opts: Vec<Option<Body>> =
            std::mem::take(&mut self.program.bodies).into_iter().map(Some).collect();
        let mut new_bodies = Vec::with_capacity(n);
        for &old_idx in permutation {
            let mut body = old_opts[old_idx]
                .take()
                .ok_or_else(|| format!("missing body at {old_idx}"))?;
            // Remap intra-crate `Terminator::Call` callee body indices into
            // the new canonical callee-first body numbering so call targets
            // stay bound to the exact same `Body` after sharding.
            for block in &mut body.blocks {
                if let Terminator::Call { callee, .. } = &mut block.terminator {
                    *callee = old_to_new
                        .get(*callee)
                        .and_then(|opt| *opt)
                        .ok_or_else(|| format!("call callee index {} out of bounds", *callee))?;
                }
            }
            new_bodies.push(body);
        }
        self.program = Program::try_new_with_options(
            self.program.scope.clone(),
            self.program.overflow_checks,
            self.program.panic,
            self.program.has_local_panic_handler,
            new_bodies,
        )?;
        for sel in &mut self.selected {
            sel.body_index = old_to_new
                .get(sel.body_index)
                .and_then(|opt| *opt)
                .ok_or_else(|| format!("selected body_index {} out of bounds", sel.body_index))?;
        }
        Ok(())
    }
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
        let nested_array_ref = Ty::Array {
            elem: Box::new(shared_ref.clone()),
            len: 2,
        };
        let nested_array_raw = Ty::Array {
            elem: Box::new(raw_ptr.clone()),
            len: 2,
        };
        assert!(nested_array_ref.has_ref_v2());
        assert!(!nested_array_ref.has_raw_ptr_v2());
        assert!(nested_array_raw.has_raw_ptr_v2());
        assert!(!nested_array_raw.has_ref_v2());
        let nested = validate_local_tys(&[
            Ty::Tuple {
                fields: vec![shared_ref.clone(), u8_ty],
            },
            raw_ptr.clone(),
        ]);
        assert!(nested.unwrap_err().contains("body mixes reference and raw-pointer locals"));
        let opt_raw = validate_local_tys(&[
            shared_ref.clone(),
            Ty::Option {
                elem: Box::new(raw_ptr.clone()),
            },
        ]);
        assert!(opt_raw.unwrap_err().contains("body mixes reference and raw-pointer locals"));
        let opt_ref = validate_local_tys(&[
            Ty::Option {
                elem: Box::new(shared_ref),
            },
            raw_ptr,
        ]);
        assert!(opt_ref.unwrap_err().contains("body mixes reference and raw-pointer locals"));
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
                    value: Rvalue::Discriminant {
                        place: Place {
                            local: 1,
                            projection: vec![],
                        },
                    },
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

        assert!(validate_constant(&Ty::Unit, &ConstLit::ZeroSized).is_ok());
        assert!(validate_constant(&Ty::Unit, &ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&Ty::Never, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Never, &ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&ovf_u8, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&ovf_u8, &ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&Ty::Bool, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Bool, &ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Bool, &ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&Ty::Bool, &ConstLit::Scalar { bits: 2 }).is_err());
        assert!(validate_constant(&Ty::Char, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0xD7FF }).is_ok());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0xD800 }).is_err());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0xDFFF }).is_err());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0xE000 }).is_ok());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0x10_FFFF }).is_ok());
        assert!(validate_constant(&Ty::Char, &ConstLit::Scalar { bits: 0x11_0000 }).is_err());
        assert!(validate_constant(&Ty::Ordering, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&Ty::Ordering, &ConstLit::Scalar { bits: 0 }).is_ok());
        assert!(validate_constant(&Ty::Ordering, &ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&Ty::Ordering, &ConstLit::Scalar { bits: 0xff }).is_ok());
        assert!(validate_constant(&Ty::Ordering, &ConstLit::Scalar { bits: 2 }).is_err());
        assert!(validate_constant(&Ty::Ordering, &ConstLit::Scalar { bits: 0x1ff }).is_err());
        assert!(validate_constant(&u8_ty, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&u8_ty, &ConstLit::Scalar { bits: 255 }).is_ok());
        assert!(validate_constant(&u8_ty, &ConstLit::Scalar { bits: 256 }).is_err());
        assert!(validate_constant(&u128_ty, &ConstLit::Scalar { bits: u128::MAX }).is_ok());
        assert!(validate_constant(&zst_enum, &ConstLit::ZeroSized).is_ok());
        assert!(validate_constant(&zst_enum, &ConstLit::Scalar { bits: 0 }).is_err());
        assert!(validate_constant(&scalar_enum, &ConstLit::ZeroSized).is_err());
        assert!(validate_constant(&scalar_enum, &ConstLit::Scalar { bits: 0xff }).is_ok());
        assert!(validate_constant(&scalar_enum, &ConstLit::Scalar { bits: 1 }).is_ok());
        assert!(validate_constant(&scalar_enum, &ConstLit::Scalar { bits: 2 }).is_err());
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
                Rvalue::Discriminant {
                    place: Place {
                        local: 1,
                        projection: vec![],
                    },
                },
            )
            .is_ok()
        );
        assert!(
            one_stmt_body(
                vec![u8_ty.clone(), Ty::Ordering],
                Rvalue::Discriminant {
                    place: Place {
                        local: 1,
                        projection: vec![],
                    },
                },
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

    #[test]
    fn call_sysroot_call_and_unchecked_arith_validation() {
        let u16_ty = Ty::Int(IntTy {
            width: IntWidth::I16,
            signed: false,
        });
        let u32_ty = Ty::Int(IntTy {
            width: IntWidth::I32,
            signed: false,
        });
        let isize_discr = IntTy {
            width: IntWidth::Isize,
            signed: true,
        };
        let enum_a = EnumTy::try_new(303, isize_discr, EnumTagRepr::ZeroSized, vec![0]).unwrap();
        let enum_ty = Ty::Enum(enum_a);

        // Unchecked integer arithmetic admits matching IntTy
        // operands/destination.
        for op in [
            BinOp::AddUnchecked,
            BinOp::SubUnchecked,
            BinOp::MulUnchecked,
        ] {
            assert!(Body::try_new(
                2,
                false,
                vec![u16_ty.clone(), u16_ty.clone(), u16_ty.clone()],
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::Binary {
                            op,
                            left: Operand::Copy { local: 1 },
                            right: Operand::Copy { local: 2 },
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                format!("rust-path-v1::unchecked_{op:?}"),
            )
            .is_ok());
        }

        // Duplicate Move operand or Move aliasing dst fails closed.
        let dup_move = Body::try_new(
            1,
            false,
            vec![u16_ty.clone(), u16_ty.clone()],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::SysrootCall {
                        op: SysrootNumOp {
                            kind: SysrootNumKind::UncheckedAdd,
                            ty: IntTy {
                                width: IntWidth::I16,
                                signed: false,
                            },
                        },
                        args: vec![Operand::Move { local: 1 }, Operand::Move { local: 1 }],
                        dst: 0,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::dup_move".into(),
        )
        .unwrap_err();
        assert!(dup_move.contains("duplicate Move operand"), "{dup_move}");

        let alias_dst = Body::try_new(
            1,
            false,
            vec![u16_ty.clone(), u16_ty.clone()],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::Call {
                        callee: 0,
                        args: vec![Operand::Move { local: 0 }],
                        dst: 0,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::alias_dst".into(),
        )
        .unwrap_err();
        assert!(alias_dst.contains("aliases a Move operand"), "{alias_dst}");

        // Cross-body Program::try_new rejects oob callee, arity mismatch, and
        // argument/return type mismatch, while admitting matching signatures.
        let callee_body = Body::try_new(
            1,
            false,
            vec![enum_ty.clone(), enum_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::Move { local: 1 },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::callee_enum".into(),
        )
        .unwrap();
        let caller_ok = Body::try_new(
            1,
            false,
            vec![enum_ty.clone(), enum_ty.clone()],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::Call {
                        callee: 1,
                        args: vec![Operand::Copy { local: 1 }],
                        dst: 0,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::caller_ok".into(),
        )
        .unwrap();
        let prog_ok = Program::try_new(Scope::Crate, vec![caller_ok, callee_body.clone()]).unwrap();
        let mut ids = BTreeSet::new();
        prog_ok.bodies()[0].collect_enum_ids(&mut ids);
        assert!(ids.contains(&303));

        let caller_bad_type = Body::try_new(
            1,
            false,
            vec![u32_ty.clone(), u32_ty],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::Call {
                        callee: 1,
                        args: vec![Operand::Copy { local: 1 }],
                        dst: 0,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::caller_bad_type".into(),
        )
        .unwrap();
        let mismatch = Program::try_new(Scope::Crate, vec![caller_bad_type, callee_body])
            .unwrap_err();
        assert!(mismatch.contains("disagrees with callee"), "{mismatch}");
    }

    #[test]
    fn array_eq_rejects_enum_elements() {
        let enum_ty = EnumTy::try_new(
            303,
            IntTy {
                width: IntWidth::I8,
                signed: false,
            },
            EnumTagRepr::Scalar(IntTy {
                width: IntWidth::I8,
                signed: false,
            }),
            vec![0, 1],
        )
        .unwrap();
        let arr_ty = Ty::Array {
            elem: Box::new(Ty::Enum(enum_ty.clone())),
            len: 2,
        };
        let ref_arr_ty = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(arr_ty),
        };
        let err = Body::try_new(
            2,
            false,
            vec![Ty::Bool, ref_arr_ty.clone(), ref_arr_ty],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::ArrayEq {
                            elem: Ty::Enum(enum_ty),
                            len: 2,
                        },
                        args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                        dst: Place {
                            local: 0,
                            projection: vec![],
                        },
                        target: 1,
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::enum_array_eq".into(),
        )
        .unwrap_err();
        assert!(err.contains("invalid CoreCall ArrayEq"), "{err}");
    }

    #[test]
    fn constant_index_honors_from_end_matching_lean_semantics() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        for len in 0..=4usize {
            let arr_ty = Ty::Array {
                elem: Box::new(u8_ty.clone()),
                len,
            };
            for min_length in 0..=5usize {
                for offset in 0..=5usize {
                    for from_end in [false, true] {
                        let expected_ok = len >= min_length
                            && if from_end {
                                offset >= 1 && offset <= len
                            } else {
                                offset < len
                            };
                        let res = Body::try_new(
                            1,
                            false,
                            vec![u8_ty.clone(), arr_ty.clone()],
                            vec![Block {
                                statements: vec![Statement::Assign {
                                    local: 0,
                                    value: Rvalue::Use {
                                        operand: Operand::CopyPlace {
                                            place: Place {
                                                local: 1,
                                                projection: vec![PlaceElem::ConstantIndex {
                                                    offset,
                                                    min_length,
                                                    from_end,
                                                }],
                                            },
                                        },
                                        with_retag: false,
                                    },
                                }],
                                terminator: Terminator::Ret,
                            }],
                            "rust-path-v1::const_idx_bounds".into(),
                        );
                        assert_eq!(
                            res.is_ok(),
                            expected_ok,
                            "len={len} min_length={min_length} offset={offset} from_end={from_end}: {res:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn fake_address_of_enforces_metadata_only_temporary_invariants() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let slice_u8 = Ty::Slice {
            elem: Box::new(u8_ty.clone()),
        };
        let mut_slice_ref = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(slice_u8.clone()),
        };
        let const_slice_ptr = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(slice_u8.clone()),
        };
        let mut_slice_ptr = Ty::RawPtr {
            mutability: Mutability::Mut,
            pointee: Box::new(slice_u8),
        };
        let const_u8_ptr = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(u8_ty.clone()),
        };
        let mut_u8_ref = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(u8_ty.clone()),
        };

        // 1. Valid metadata-only temporary on `&mut [u8]` succeeds and selects
        //    Profile v2.
        let valid = Body::try_new(
            1,
            false,
            vec![
                usize_ty.clone(),
                mut_slice_ref.clone(),
                const_slice_ptr.clone(),
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::Move { local: 2 },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::valid_fake_ptr_metadata".into(),
        )
        .expect("valid FakeAddressOf + PtrMetadata body must pass");
        assert!(valid.uses_profile_v2());

        // 2. Adding an unrelated real `*const u8` local alongside `&mut [u8]`
        //    is still rejected by `validate_local_tys_with_exemptions`.
        let mixed_err = Body::try_new(
            1,
            false,
            vec![
                usize_ty.clone(),
                mut_slice_ref.clone(),
                const_slice_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::Move { local: 2 },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::mixed_fake_and_real_raw".into(),
        )
        .unwrap_err();
        assert!(
            mixed_err.contains("body mixes reference and raw-pointer locals"),
            "{mixed_err}"
        );

        // 3. Parameter local (`lid <= arg_count`) cannot be exempted as a fake
        //    metadata temporary.
        let arg_err = Body::try_new(
            2,
            false,
            vec![
                usize_ty.clone(),
                mut_slice_ref.clone(),
                const_slice_ptr.clone(),
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::Move { local: 2 },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::fake_meta_param".into(),
        )
        .unwrap_err();
        assert!(
            arg_err.contains("body mixes reference and raw-pointer locals"),
            "{arg_err}"
        );

        // Return place (`_0`, `lid < arg_count`) cannot be exempted either
        // (kills `lid <= arg_count -> lid == arg_count`).
        let ret_err = Body::try_new(
            1,
            false,
            vec![const_slice_ptr.clone(), mut_slice_ref.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::FakeAddressOf {
                        place: Place {
                            local: 1,
                            projection: vec![PlaceElem::Deref],
                        },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::fake_meta_return_place".into(),
        )
        .unwrap_err();
        assert!(
            ret_err.contains("body mixes reference and raw-pointer locals"),
            "{ret_err}"
        );

        // 4. `*mut [u8]` destination is rejected.
        let mut_dst_err = Body::try_new(
            1,
            false,
            vec![usize_ty, mut_slice_ref, mut_slice_ptr],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::fake_meta_mut_dst".into(),
        )
        .unwrap_err();
        assert!(
            mut_dst_err.contains("body mixes reference and raw-pointer locals"),
            "{mut_dst_err}"
        );

        // 5. Dereferencing the fake temporary (`*_2`) in a ref body fails the
        //    mixed-locals guard, and copying `_2` in a raw-pointer-only body
        //    fails the unconditional `FakeAddressOf` discipline check.
        let deref_err = Body::try_new(
            1,
            false,
            vec![u8_ty, mut_u8_ref, const_u8_ptr.clone()],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::CopyPlace {
                                place: Place {
                                    local: 2,
                                    projection: vec![PlaceElem::Deref],
                                },
                            },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::deref_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            deref_err.contains("body mixes reference and raw-pointer locals"),
            "{deref_err}"
        );

        let raw_escape_err = Body::try_new(
            1,
            true,
            vec![
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 2 },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::raw_only_escape_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            raw_escape_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{raw_escape_err}"
        );

        // 6. Passing a fake-metadata local as a `Terminator::CoreCall` argument
        //    (without mentioning it in `dst`) or overwriting it as a `CoreCall`
        //    destination (without mentioning it in `args`) must both fail
        //    closed (kills `|| -> &&` in `terminator_mentions_local_v2`).
        let core_call_arg_escape_err = Body::try_new(
            1,
            true,
            vec![
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![
                Block {
                    statements: vec![Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    }],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::PtrAdd {
                            mutability: Mutability::Shared,
                            pointee: Ty::Int(IntTy {
                                width: IntWidth::I8,
                                signed: false,
                            }),
                        },
                        args: vec![
                            Operand::Copy { local: 2 },
                            Operand::Constant {
                                ty: Ty::Int(IntTy {
                                    width: IntWidth::Isize,
                                    signed: false,
                                }),
                                lit: ConstLit::Scalar { bits: 0 },
                            },
                        ],
                        dst: Place {
                            local: 0,
                            projection: vec![],
                        },
                        target: 1,
                        unwind: UnwindAction::Unreachable,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::core_call_arg_escape_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            core_call_arg_escape_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{core_call_arg_escape_err}"
        );

        let core_call_dst_escape_err = Body::try_new(
            1,
            true,
            vec![
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![
                Block {
                    statements: vec![Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    }],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::PtrAdd {
                            mutability: Mutability::Shared,
                            pointee: Ty::Int(IntTy {
                                width: IntWidth::I8,
                                signed: false,
                            }),
                        },
                        args: vec![
                            Operand::Copy { local: 1 },
                            Operand::Constant {
                                ty: Ty::Int(IntTy {
                                    width: IntWidth::Isize,
                                    signed: false,
                                }),
                                lit: ConstLit::Scalar { bits: 0 },
                            },
                        ],
                        dst: Place {
                            local: 2,
                            projection: vec![],
                        },
                        target: 1,
                        unwind: UnwindAction::Unreachable,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::core_call_dst_escape_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            core_call_dst_escape_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{core_call_dst_escape_err}"
        );

        // 7. Self-referential `_2 = FakeAddressOf(*_2)` must fail closed
        //    (kills `fake_address_of_types_match_v2 -> true`).
        let self_assign_err = Body::try_new(
            1,
            true,
            vec![
                Ty::Unit,
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 2,
                    value: Rvalue::FakeAddressOf {
                        place: Place {
                            local: 2,
                            projection: vec![PlaceElem::Deref],
                        },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::self_assign_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            self_assign_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{self_assign_err}"
        );

        // 8. `Statement::AssignPlace` reading `PtrMetadata(move _3)` into a
        //    projected destination (`*_2`) is admitted, while copying `_3` into
        //    a projected destination is rejected.
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let mut_usize_ref = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(usize_ty.clone()),
        };
        let mut_slice_ref = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(Ty::Slice {
                elem: Box::new(Ty::Int(IntTy {
                    width: IntWidth::I8,
                    signed: false,
                })),
            }),
        };
        let assign_place_ok = Body::try_new(
            2,
            false,
            vec![
                Ty::Unit,
                mut_slice_ref.clone(),
                mut_usize_ref.clone(),
                const_slice_ptr.clone(),
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 3,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::AssignPlace {
                        place: Place {
                            local: 2,
                            projection: vec![PlaceElem::Deref],
                        },
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::Move { local: 3 },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::assign_place_ptr_metadata_ok".into(),
        )
        .expect("AssignPlace reading PtrMetadata of fake temp must pass");
        assert!(assign_place_ok.uses_profile_v2());

        let assign_place_bad_err = Body::try_new(
            2,
            false,
            vec![
                Ty::Unit,
                mut_slice_ref,
                mut_usize_ref,
                const_slice_ptr,
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 3,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::AssignPlace {
                        place: Place {
                            local: 2,
                            projection: vec![PlaceElem::Deref],
                        },
                        value: Rvalue::Use {
                            operand: Operand::Copy { local: 3 },
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::assign_place_copy_fake_meta_bad".into(),
        )
        .unwrap_err();
        assert!(
            assign_place_bad_err.contains("body mixes reference and raw-pointer locals"),
            "{assign_place_bad_err}"
        );

        // 9. Escaping a fake-metadata temporary through `Rvalue::Binary`
        //    (`BinOp::Offset`) in a raw-pointer-only body must fail closed
        //    (kills `|| -> &&` in `rvalue_mentions_local_v2`).
        let isize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: true,
        });
        let binary_offset_escape_err = Body::try_new(
            1,
            true,
            vec![
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Binary {
                            op: BinOp::Offset,
                            left: Operand::Move { local: 2 },
                            right: Operand::Constant {
                                ty: isize_ty.clone(),
                                lit: ConstLit::Scalar { bits: 0 },
                            },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::binary_offset_escape_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            binary_offset_escape_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{binary_offset_escape_err}"
        );

        // 10. Passing a fake-metadata local as a `Terminator::Call` argument
        //     or overwriting it as a `Terminator::Call` destination must both
        //     fail closed (kills `|| -> &&` and each disjunct in
        //     `terminator_mentions_local_v2` for `Terminator::Call`).
        let call_arg_escape_err = Body::try_new(
            1,
            true,
            vec![
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![
                Block {
                    statements: vec![Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    }],
                    terminator: Terminator::Call {
                        callee: 0,
                        args: vec![Operand::Copy { local: 2 }],
                        dst: 0,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::call_arg_escape_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            call_arg_escape_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{call_arg_escape_err}"
        );

        let call_dst_escape_err = Body::try_new(
            1,
            true,
            vec![
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
                const_u8_ptr.clone(),
            ],
            vec![
                Block {
                    statements: vec![Statement::Assign {
                        local: 2,
                        value: Rvalue::FakeAddressOf {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    }],
                    terminator: Terminator::Call {
                        callee: 0,
                        args: vec![Operand::Copy { local: 1 }],
                        dst: 2,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::call_dst_escape_fake_meta".into(),
        )
        .unwrap_err();
        assert!(
            call_dst_escape_err.contains("read exclusively by UnOp::PtrMetadata"),
            "{call_dst_escape_err}"
        );

        // 11. Other well-typed escapes (`Cast`, `AggregateTuple`, `AddressOf`,
        //     distinct-dst `FakeAddressOf`, non-`FakeAddressOf` second
        //     assignment, and `PlaceMention`) must all fail closed. (`Repeat`
        //     and `AggregateArray` cannot hold raw-pointer elements in the
        //     Profile v2 type fragment and are covered directly in
        //     `fake_ptr_metadata_predicates_cover_every_arm`.)
        let fake_assign_2 = Statement::Assign {
            local: 2,
            value: Rvalue::FakeAddressOf {
                place: Place {
                    local: 1,
                    projection: vec![PlaceElem::Deref],
                },
            },
        };
        let ptr_pair_ty = Ty::Tuple {
            fields: vec![const_u8_ptr.clone(), const_u8_ptr.clone()],
        };
        let escape_cases: Vec<(&str, Vec<Ty>, Statement)> = vec![
            (
                "cast_escape",
                vec![
                    const_u8_ptr.clone(),
                    const_u8_ptr.clone(),
                    const_u8_ptr.clone(),
                ],
                Statement::Assign {
                    local: 0,
                    value: Rvalue::Cast {
                        cast_kind: CastKind::PtrToPtr,
                        operand: Operand::Move { local: 2 },
                        ty: const_u8_ptr.clone(),
                    },
                },
            ),
            (
                "tuple_escape",
                vec![ptr_pair_ty, const_u8_ptr.clone(), const_u8_ptr.clone()],
                Statement::Assign {
                    local: 0,
                    value: Rvalue::AggregateTuple {
                        fields: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                    },
                },
            ),
            (
                "address_of_escape",
                vec![
                    const_u8_ptr.clone(),
                    const_u8_ptr.clone(),
                    const_u8_ptr.clone(),
                ],
                Statement::Assign {
                    local: 0,
                    value: Rvalue::AddressOf {
                        mutability: Mutability::Shared,
                        place: Place {
                            local: 2,
                            projection: vec![PlaceElem::Deref],
                        },
                    },
                },
            ),
            (
                "chained_fake_address_of_escape",
                vec![
                    Ty::Unit,
                    const_u8_ptr.clone(),
                    const_u8_ptr.clone(),
                    const_u8_ptr.clone(),
                ],
                Statement::Assign {
                    local: 3,
                    value: Rvalue::FakeAddressOf {
                        place: Place {
                            local: 2,
                            projection: vec![PlaceElem::Deref],
                        },
                    },
                },
            ),
            (
                "second_non_fake_assign",
                vec![Ty::Unit, const_u8_ptr.clone(), const_u8_ptr.clone()],
                Statement::Assign {
                    local: 2,
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1 },
                        with_retag: false,
                    },
                },
            ),
            (
                "place_mention_escape",
                vec![Ty::Unit, const_u8_ptr.clone(), const_u8_ptr.clone()],
                Statement::PlaceMention { local: 2 },
            ),
        ];
        for (name, locals, stmt) in escape_cases {
            let err = Body::try_new(
                1,
                true,
                locals,
                vec![Block {
                    statements: vec![fake_assign_2.clone(), stmt],
                    terminator: Terminator::Ret,
                }],
                format!("rust-path-v1::{name}"),
            )
            .unwrap_err();
            assert!(
                err.contains("read exclusively by UnOp::PtrMetadata"),
                "{name}: {err}"
            );
        }

        // 12. Unprojected `CopyPlace` read by `UnOp::PtrMetadata` is admitted.
        let slice_u8 = Ty::Slice {
            elem: Box::new(Ty::Int(IntTy {
                width: IntWidth::I8,
                signed: false,
            })),
        };
        let mut_slice_ref = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(slice_u8.clone()),
        };
        let const_slice_ptr = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(slice_u8),
        };
        let ok = Body::try_new(
            1,
            false,
            vec![usize_ty, mut_slice_ref, const_slice_ptr],
            vec![Block {
                statements: vec![
                    fake_assign_2,
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::CopyPlace {
                                place: Place {
                                    local: 2,
                                    projection: vec![],
                                },
                            },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::ptr_metadata_unprojected_copy_place_ok".into(),
        )
        .expect("unprojected CopyPlace PtrMetadata must pass");
        assert!(ok.uses_profile_v2());
    }

    #[test]
    fn fake_ptr_metadata_predicates_cover_every_arm() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let const_u8_ptr = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(u8_ty.clone()),
        };
        let mut_u8_ptr = Ty::RawPtr {
            mutability: Mutability::Mut,
            pointee: Box::new(u8_ty.clone()),
        };
        let const_usize_ptr = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(usize_ty.clone()),
        };
        let overflow_ref = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::OverflowPair(IntTy {
                width: IntWidth::I8,
                signed: false,
            })),
        };
        let overflow_ptr = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::OverflowPair(IntTy {
                width: IntWidth::I8,
                signed: false,
            })),
        };
        let p2 = Place {
            local: 2,
            projection: vec![],
        };
        let p2_deref = Place {
            local: 2,
            projection: vec![PlaceElem::Deref],
        };
        let p1 = Place {
            local: 1,
            projection: vec![],
        };
        let c0 = Operand::Constant {
            ty: usize_ty.clone(),
            lit: ConstLit::Scalar { bits: 0 },
        };

        // `operand_mentions_local_v2`
        assert!(operand_mentions_local_v2(&Operand::Copy { local: 2 }, 2));
        assert!(!operand_mentions_local_v2(&Operand::Copy { local: 1 }, 2));
        assert!(operand_mentions_local_v2(&Operand::Move { local: 2 }, 2));
        assert!(!operand_mentions_local_v2(&Operand::Move { local: 1 }, 2));
        assert!(operand_mentions_local_v2(
            &Operand::CopyPlace { place: p2.clone() },
            2
        ));
        assert!(!operand_mentions_local_v2(
            &Operand::CopyPlace { place: p1.clone() },
            2
        ));
        assert!(operand_mentions_local_v2(
            &Operand::MovePlace { place: p2.clone() },
            2
        ));
        assert!(!operand_mentions_local_v2(
            &Operand::MovePlace { place: p1.clone() },
            2
        ));
        assert!(!operand_mentions_local_v2(&c0, 2));

        // `rvalue_mentions_local_v2` across every Rvalue arm (including both
        // sides of Binary).
        let rv_true = [
            Rvalue::Use {
                operand: Operand::Copy { local: 2 },
                with_retag: false,
            },
            Rvalue::UseRetag {
                operand: Operand::Move { local: 2 },
            },
            Rvalue::Unary {
                op: UnOp::PtrMetadata,
                operand: Operand::Copy { local: 2 },
            },
            Rvalue::Cast {
                cast_kind: CastKind::PtrToPtr,
                operand: Operand::Copy { local: 2 },
                ty: const_u8_ptr.clone(),
            },
            Rvalue::Repeat {
                operand: Operand::Copy { local: 2 },
                elem_ty: const_u8_ptr.clone(),
                count: 2,
            },
            Rvalue::AggregateRangeTo {
                elem_ty: usize_ty.clone(),
                end: Operand::Copy { local: 2 },
            },
            Rvalue::AggregateRangeFrom {
                elem_ty: usize_ty.clone(),
                start: Operand::Copy { local: 2 },
            },
            Rvalue::Binary {
                op: BinOp::Offset,
                left: Operand::Copy { local: 2 },
                right: c0.clone(),
            },
            Rvalue::Binary {
                op: BinOp::Add,
                left: c0.clone(),
                right: Operand::Copy { local: 2 },
            },
            Rvalue::Discriminant { place: p2.clone() },
            Rvalue::Ref {
                mutability: Mutability::Shared,
                place: p2.clone(),
            },
            Rvalue::AddressOf {
                mutability: Mutability::Shared,
                place: p2_deref.clone(),
            },
            Rvalue::FakeAddressOf {
                place: p2_deref.clone(),
            },
            Rvalue::AggregateTuple {
                fields: vec![c0.clone(), Operand::Copy { local: 2 }],
            },
            Rvalue::AggregateArray {
                elem_ty: const_u8_ptr.clone(),
                elems: vec![c0.clone(), Operand::Copy { local: 2 }],
            },
        ];
        for rv in &rv_true {
            assert!(rvalue_mentions_local_v2(rv, 2), "expected mention: {rv:?}");
            assert!(
                !rvalue_mentions_local_v2(rv, 3),
                "unexpected mention of 3: {rv:?}"
            );
        }

        // `terminator_mentions_local_v2` across every Terminator arm
        let sys_op = SysrootNumOp {
            kind: SysrootNumKind::WrappingAdd,
            ty: IntTy {
                width: IntWidth::Isize,
                signed: false,
            },
        };
        let term_false = [
            Terminator::Goto { block: 0 },
            Terminator::Ret,
            Terminator::Unreachable,
            Terminator::Unsupported,
            Terminator::SwitchInt {
                operand: Operand::Copy { local: 1 },
                targets: vec![],
                otherwise: 0,
            },
            Terminator::Assert {
                cond: Operand::Copy { local: 1 },
                expected: true,
                msg: AssertKind::BoundsCheck,
                target: 0,
                unwind: UnwindAction::Continue,
            },
            Terminator::SysrootCall {
                op: sys_op,
                args: vec![Operand::Copy { local: 1 }, c0.clone()],
                dst: 0,
                target: Some(0),
                unwind: UnwindAction::Continue,
            },
        ];
        for term in &term_false {
            assert!(
                !terminator_mentions_local_v2(term, 2),
                "unexpected mention: {term:?}"
            );
        }
        let term_true = [
            Terminator::SwitchInt {
                operand: Operand::Copy { local: 2 },
                targets: vec![],
                otherwise: 0,
            },
            Terminator::Assert {
                cond: Operand::Copy { local: 2 },
                expected: true,
                msg: AssertKind::BoundsCheck,
                target: 0,
                unwind: UnwindAction::Continue,
            },
            Terminator::CoreCall {
                op: CoreCallOp::SliceLen,
                args: vec![Operand::Copy { local: 2 }],
                dst: Place {
                    local: 0,
                    projection: vec![],
                },
                target: 0,
                unwind: UnwindAction::Continue,
            },
            Terminator::CoreCall {
                op: CoreCallOp::SliceLen,
                args: vec![Operand::Copy { local: 1 }],
                dst: p2.clone(),
                target: 0,
                unwind: UnwindAction::Continue,
            },
            Terminator::Call {
                callee: 0,
                args: vec![Operand::Copy { local: 2 }],
                dst: 0,
                target: Some(0),
                unwind: UnwindAction::Continue,
            },
            Terminator::Call {
                callee: 0,
                args: vec![Operand::Copy { local: 1 }],
                dst: 2,
                target: Some(0),
                unwind: UnwindAction::Continue,
            },
            Terminator::SysrootCall {
                op: sys_op,
                args: vec![Operand::Copy { local: 2 }, c0.clone()],
                dst: 0,
                target: Some(0),
                unwind: UnwindAction::Continue,
            },
            Terminator::SysrootCall {
                op: sys_op,
                args: vec![Operand::Copy { local: 1 }, c0.clone()],
                dst: 2,
                target: Some(0),
                unwind: UnwindAction::Continue,
            },
        ];
        for term in &term_true {
            assert!(
                terminator_mentions_local_v2(term, 2),
                "expected mention: {term:?}"
            );
        }

        // `fake_address_of_types_match_v2` rejection branches
        let base_locals = vec![Ty::Unit, const_u8_ptr.clone(), const_u8_ptr.clone()];
        assert!(fake_address_of_types_match_v2(
            &base_locals,
            2,
            &Place {
                local: 1,
                projection: vec![PlaceElem::Deref],
            }
        ));
        assert!(!fake_address_of_types_match_v2(&base_locals, 2, &p2_deref));
        assert!(!fake_address_of_types_match_v2(&base_locals, 2, &p1));
        assert!(!fake_address_of_types_match_v2(
            &base_locals,
            2,
            &Place {
                local: 1,
                projection: vec![PlaceElem::Deref, PlaceElem::Deref],
            }
        ));
        assert!(!fake_address_of_types_match_v2(
            &[Ty::Unit, u8_ty.clone(), const_u8_ptr.clone()],
            2,
            &Place {
                local: 1,
                projection: vec![PlaceElem::Deref],
            }
        ));
        assert!(!fake_address_of_types_match_v2(
            &[Ty::Unit, overflow_ref, overflow_ptr],
            2,
            &Place {
                local: 1,
                projection: vec![PlaceElem::Deref],
            }
        ));
        assert!(!fake_address_of_types_match_v2(
            &[Ty::Unit, const_u8_ptr.clone(), mut_u8_ptr],
            2,
            &Place {
                local: 1,
                projection: vec![PlaceElem::Deref],
            }
        ));
        assert!(!fake_address_of_types_match_v2(
            &[Ty::Unit, const_u8_ptr.clone(), const_usize_ptr],
            2,
            &Place {
                local: 1,
                projection: vec![PlaceElem::Deref],
            }
        ));

        // `is_fake_ptr_metadata_local_v2` structural rejections unreachable via
        // MIR typing rules alone (projected `PtrMetadata` operand,
        // `AssignPlace` writing through `*_2`, and `SysrootCall` mention).
        let fake_assign = Statement::Assign {
            local: 2,
            value: Rvalue::FakeAddressOf {
                place: Place {
                    local: 1,
                    projection: vec![PlaceElem::Deref],
                },
            },
        };
        let proj_ptr_meta = Rvalue::Unary {
            op: UnOp::PtrMetadata,
            operand: Operand::CopyPlace {
                place: p2_deref.clone(),
            },
        };
        assert!(is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::MovePlace { place: p2.clone() },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::AssignPlace {
                        place: Place {
                            local: 0,
                            projection: vec![PlaceElem::Deref],
                        },
                        value: Rvalue::Unary {
                            op: UnOp::PtrMetadata,
                            operand: Operand::MovePlace { place: p2 },
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(!is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::Assign {
                        local: 0,
                        value: proj_ptr_meta.clone(),
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(!is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::AssignPlace {
                        place: Place {
                            local: 0,
                            projection: vec![PlaceElem::Deref],
                        },
                        value: proj_ptr_meta,
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(!is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::AssignPlace {
                        place: p2_deref,
                        value: Rvalue::Use {
                            operand: c0.clone(),
                            with_retag: false,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(!is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Repeat {
                            operand: Operand::Copy { local: 2 },
                            elem_ty: const_u8_ptr.clone(),
                            count: 2,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(!is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![
                    fake_assign.clone(),
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::AggregateArray {
                            elem_ty: const_u8_ptr,
                            elems: vec![c0.clone(), Operand::Copy { local: 2 }],
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            2,
        ));
        assert!(!is_fake_ptr_metadata_local_v2(
            1,
            &base_locals,
            &[Block {
                statements: vec![fake_assign],
                terminator: Terminator::SysrootCall {
                    op: sys_op,
                    args: vec![Operand::Copy { local: 2 }, c0],
                    dst: 0,
                    target: Some(0),
                    unwind: UnwindAction::Continue,
                },
            }],
            2,
        ));
    }

    #[test]
    fn profile_v2_option_range_and_core_call_type_guards() {
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let u64_ty = Ty::Int(IntTy {
            width: IntWidth::I64,
            signed: false,
        });
        let range_ty = Ty::Range {
            elem: Box::new(usize_ty.clone()),
        };
        let opt_u64 = Ty::Option {
            elem: Box::new(u64_ty.clone()),
        };
        let opt_ref = Ty::Option {
            elem: Box::new(Ty::Ref {
                mutability: Mutability::Shared,
                pointee: Box::new(u64_ty.clone()),
            }),
        };
        let opt_opt = Ty::Option {
            elem: Box::new(opt_u64.clone()),
        };
        assert!(range_ty.is_supported_v2_local());
        assert!(opt_u64.is_supported_v2_local());
        assert!(opt_u64.is_retag_noop());
        assert!(opt_ref.is_supported_v2_local());
        assert!(!opt_ref.is_retag_noop());
        assert!(!opt_opt.is_supported_v2_local());

        // Local tuples and `Range*` are supported, whereas pointee/slice
        // elements and `Option` payloads reject `#[repr(Rust)]` tuples (and
        // `OverflowPair`), `Range*`, and nested `Option<Option<_>>`.
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let u32_ty = Ty::Int(IntTy {
            width: IntWidth::I32,
            signed: false,
        });
        let reordered_tuple = Ty::Tuple {
            fields: vec![u8_ty.clone(), u32_ty.clone(), u8_ty.clone()],
        };
        let overflow_pair = Ty::OverflowPair(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        assert!(reordered_tuple.is_supported_v2_local());
        assert!(overflow_pair.is_supported_v2_local());
        assert!(!reordered_tuple.is_sized_no_ref());
        assert!(!overflow_pair.is_sized_no_ref());
        assert!(!range_ty.is_sized_no_ref());

        let mut_opt_u64 = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(opt_u64.clone()),
        };
        assert!(mut_opt_u64.is_supported_v2_local());
        assert!(!Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(reordered_tuple.clone()),
        }
        .is_supported_v2_local());
        assert!(!Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(overflow_pair.clone()),
        }
        .is_supported_v2_local());
        assert!(!Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Slice {
                elem: Box::new(Ty::Tuple {
                    fields: vec![u8_ty.clone(), u32_ty],
                }),
            }),
        }
        .is_supported_v2_local());
        assert!(!Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(range_ty.clone()),
        }
        .is_supported_v2_local());
        assert!(!Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Option {
                elem: Box::new(Ty::Option {
                    elem: Box::new(u8_ty),
                }),
            }),
        }
        .is_supported_v2_local());
        assert!(!Ty::Option {
            elem: Box::new(reordered_tuple),
        }
        .is_supported_v2_local());
        assert!(!Ty::Option {
            elem: Box::new(overflow_pair),
        }
        .is_supported_v2_local());
        assert!(!Ty::Option {
            elem: Box::new(range_ty),
        }
        .is_supported_v2_local());
        assert!(!Ty::Option {
            elem: Box::new(Ty::RangeFrom {
                elem: Box::new(usize_ty.clone()),
            }),
        }
        .is_supported_v2_local());
        assert!(!Ty::Option {
            elem: Box::new(Ty::RangeTo {
                elem: Box::new(usize_ty),
            }),
        }
        .is_supported_v2_local());

        // Downcast on Option must be variant 1 -> field 0 of inner type.
        let ok_body = Body::try_new(
            1,
            false,
            vec![u64_ty.clone(), opt_u64.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![
                                    PlaceElem::Downcast { variant_idx: 1 },
                                    PlaceElem::Field {
                                        index: 0,
                                        ty: u64_ty.clone(),
                                    },
                                ],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::option_downcast".into(),
        );
        assert!(ok_body.is_ok(), "{ok_body:?}");

        let dangling_downcast = Body::try_new(
            1,
            false,
            vec![opt_u64.clone(), opt_u64],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Downcast { variant_idx: 1 }],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::dangling_downcast".into(),
        )
        .unwrap_err();
        assert!(dangling_downcast.contains("must be followed by field projection"));
    }

    #[test]
    fn is_sized_and_place_projection_guards_cover_unsized_downcast_and_range() {
        let u8_ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
        let u32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
        let u64_ty = Ty::Int(IntTy { width: IntWidth::I64, signed: false });
        let usize_ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
        let slice_u8 = Ty::Slice { elem: Box::new(u8_ty.clone()) };
        let ref_slice_u8 = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(slice_u8.clone()),
        };
        let ptr_slice_u8 = Ty::RawPtr {
            mutability: Mutability::Shared,
            pointee: Box::new(slice_u8.clone()),
        };
        let opt_u64 = Ty::Option { elem: Box::new(u64_ty.clone()) };
        let range_usize = Ty::Range { elem: Box::new(usize_ty.clone()) };
        let range_u32 = Ty::Range { elem: Box::new(u32_ty.clone()) };

        // Ty::is_sized must return false on unsized slices and unsized
        // composite tuples, and true on sized references/pointers.
        assert!(!slice_u8.is_sized());
        assert!(!Ty::Tuple { fields: vec![u8_ty.clone(), slice_u8.clone()] }.is_sized());
        assert!(u8_ty.is_sized());
        assert!(ref_slice_u8.is_sized());
        assert!(ptr_slice_u8.is_sized());
        assert!(opt_u64.is_sized());
        assert!(range_usize.is_sized());

        // Unsized deref in a non-PtrMetadata place must fail closed via
        // is_sized.
        let unsized_deref = Body::try_new(
            1,
            false,
            vec![u8_ty.clone(), ref_slice_u8.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place { local: 1, projection: vec![PlaceElem::Deref] },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::unsized_deref".into(),
        )
        .unwrap_err();
        assert!(unsized_deref.contains("unsized deref"), "{unsized_deref}");

        // PtrAdd on an unsized slice pointee must fail closed via is_sized.
        let unsized_ptr_add = Body::try_new(
            2,
            false,
            vec![ptr_slice_u8.clone(), ptr_slice_u8.clone(), usize_ty.clone()],
            vec![Block {
                statements: vec![],
                terminator: Terminator::CoreCall {
                    op: CoreCallOp::PtrAdd {
                        mutability: Mutability::Shared,
                        pointee: slice_u8.clone(),
                    },
                    args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                    dst: Place { local: 0, projection: vec![] },
                    target: 1,
                    unwind: UnwindAction::Continue,
                },
            },
            Block {
                statements: vec![],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::unsized_ptr_add".into(),
        )
        .unwrap_err();
        assert!(unsized_ptr_add.contains("invalid CoreCall PtrAdd"), "{unsized_ptr_add}");

        // Downcast(1) on a non-Option type must fail closed.
        let non_opt_downcast = Body::try_new(
            1,
            false,
            vec![u64_ty.clone(), u64_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![
                                    PlaceElem::Downcast { variant_idx: 1 },
                                    PlaceElem::Field { index: 0, ty: u64_ty.clone() },
                                ],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::non_opt_downcast".into(),
        )
        .unwrap_err();
        assert!(non_opt_downcast.contains("unsupported downcast variant"), "{non_opt_downcast}");

        // Downcast(0) (None) on Option must fail closed.
        let none_downcast = Body::try_new(
            1,
            false,
            vec![u64_ty.clone(), opt_u64.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![
                                    PlaceElem::Downcast { variant_idx: 0 },
                                    PlaceElem::Field { index: 0, ty: u64_ty.clone() },
                                ],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::none_downcast".into(),
        )
        .unwrap_err();
        assert!(none_downcast.contains("unsupported downcast variant"), "{none_downcast}");

        // [Downcast(1), Field(1)] on Option must fail closed.
        let bad_downcast_field = Body::try_new(
            1,
            false,
            vec![u64_ty.clone(), opt_u64.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![
                                    PlaceElem::Downcast { variant_idx: 1 },
                                    PlaceElem::Field { index: 1, ty: u64_ty.clone() },
                                ],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::bad_downcast_field".into(),
        )
        .unwrap_err();
        assert!(bad_downcast_field.contains("unsupported downcast field"), "{bad_downcast_field}");

        // Positive Range<usize> .start (0) and .end (1) projections.
        for field_idx in [0usize, 1usize] {
            let ok_range = Body::try_new(
                1,
                false,
                vec![usize_ty.clone(), range_usize.clone()],
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::CopyPlace {
                                place: Place {
                                    local: 1,
                                    projection: vec![PlaceElem::Field {
                                        index: field_idx,
                                        ty: usize_ty.clone(),
                                    }],
                                },
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                format!("rust-path-v1::range_field_{field_idx}"),
            );
            assert!(ok_range.is_ok(), "field {field_idx}: {ok_range:?}");
        }

        // Out-of-bounds field 2 on Range<usize> must fail closed.
        let bad_range_idx = Body::try_new(
            1,
            false,
            vec![usize_ty.clone(), range_usize],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Field {
                                    index: 2,
                                    ty: usize_ty.clone(),
                                }],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::bad_range_idx".into(),
        )
        .unwrap_err();
        assert!(bad_range_idx.contains("unsupported field 2"), "{bad_range_idx}");

        // Field 0 on non-usize Range<u32> must fail closed.
        let bad_range_elem = Body::try_new(
            1,
            false,
            vec![u32_ty.clone(), range_u32],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place {
                                local: 1,
                                projection: vec![PlaceElem::Field {
                                    index: 0,
                                    ty: u32_ty.clone(),
                                }],
                            },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::bad_range_elem".into(),
        )
        .unwrap_err();
        assert!(
            bad_range_elem.contains("outside the Profile v2 type fragment"),
            "{bad_range_elem}"
        );
    }

    #[test]
    fn v2_layout_covers_all_variants_and_rejects_non_zst_as_zero() {
        let u8_ty = Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let u16_ty = Ty::Int(IntTy {
            width: IntWidth::I16,
            signed: false,
        });
        let u32_ty = Ty::Int(IntTy {
            width: IntWidth::I32,
            signed: false,
        });
        let u64_ty = Ty::Int(IntTy {
            width: IntWidth::I64,
            signed: false,
        });
        let u128_ty = Ty::Int(IntTy {
            width: IntWidth::I128,
            signed: false,
        });
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let isize_ty = IntTy {
            width: IntWidth::Isize,
            signed: true,
        };
        let zst_enum = Ty::Enum(
            EnumTy::try_new(11, isize_ty, EnumTagRepr::ZeroSized, vec![0]).unwrap(),
        );
        let u16_enum = Ty::Enum(
            EnumTy::try_new(
                12,
                isize_ty,
                EnumTagRepr::Scalar(IntTy {
                    width: IntWidth::I16,
                    signed: false,
                }),
                vec![0, 1],
            )
            .unwrap(),
        );

        assert_eq!(Ty::Bool.v2_layout(), Some((1, 0)));
        assert_eq!(Ty::Ordering.v2_layout(), Some((1, 0)));
        assert_eq!(u8_ty.v2_layout(), Some((1, 0)));
        assert_eq!(u16_ty.v2_layout(), Some((2, 1)));
        assert_eq!(u32_ty.v2_layout(), Some((4, 2)));
        assert_eq!(u64_ty.v2_layout(), Some((8, 3)));
        assert_eq!(usize_ty.v2_layout(), Some((8, 3)));
        assert_eq!(u128_ty.v2_layout(), Some((16, 4)));
        assert_eq!(Ty::Char.v2_layout(), Some((4, 2)));
        assert_eq!(Ty::Unit.v2_layout(), Some((0, 0)));
        assert_eq!(Ty::Never.v2_layout(), Some((0, 0)));
        assert_eq!(zst_enum.v2_layout(), Some((0, 0)));
        assert_eq!(u16_enum.v2_layout(), Some((2, 1)));
        assert_eq!(
            Ty::OverflowPair(IntTy {
                width: IntWidth::I32,
                signed: false
            })
            .v2_layout(),
            Some((8, 2))
        );
        assert_eq!(
            Ty::Array {
                elem: Box::new(u32_ty.clone()),
                len: 3
            }
            .v2_layout(),
            Some((12, 2))
        );
        assert_eq!(
            Ty::Ref {
                mutability: Mutability::Shared,
                pointee: Box::new(u64_ty.clone())
            }
            .v2_layout(),
            Some((8, 3))
        );
        assert_eq!(
            Ty::Ref {
                mutability: Mutability::Mut,
                pointee: Box::new(Ty::Slice {
                    elem: Box::new(u8_ty.clone())
                })
            }
            .v2_layout(),
            Some((16, 3))
        );
        assert_eq!(
            Ty::RawPtr {
                mutability: Mutability::Shared,
                pointee: Box::new(u64_ty.clone())
            }
            .v2_layout(),
            Some((8, 3))
        );
        assert_eq!(
            Ty::RawPtr {
                mutability: Mutability::Mut,
                pointee: Box::new(Ty::Slice {
                    elem: Box::new(u8_ty.clone())
                })
            }
            .v2_layout(),
            Some((16, 3))
        );
        assert_eq!(
            Ty::RangeTo {
                elem: Box::new(usize_ty.clone())
            }
            .v2_layout(),
            Some((8, 3))
        );
        assert_eq!(
            Ty::RangeFrom {
                elem: Box::new(usize_ty.clone())
            }
            .v2_layout(),
            Some((8, 3))
        );
        assert_eq!(
            Ty::Range {
                elem: Box::new(usize_ty)
            }
            .v2_layout(),
            None
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(Ty::Bool)
            }
            .v2_layout(),
            Some((1, 0))
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(Ty::Unit)
            }
            .v2_layout(),
            Some((1, 0))
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(u64_ty.clone())
            }
            .v2_layout(),
            Some((16, 3))
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(Ty::Ref {
                    mutability: Mutability::Shared,
                    pointee: Box::new(u8_ty.clone())
                })
            }
            .v2_layout(),
            None
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(Ty::Ref {
                    mutability: Mutability::Shared,
                    pointee: Box::new(Ty::Slice {
                        elem: Box::new(u8_ty.clone())
                    })
                })
            }
            .v2_layout(),
            None
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(Ty::RawPtr {
                    mutability: Mutability::Shared,
                    pointee: Box::new(u8_ty.clone())
                })
            }
            .v2_layout(),
            None
        );
        assert_eq!(
            Ty::Option {
                elem: Box::new(Ty::Option {
                    elem: Box::new(u8_ty.clone())
                })
            }
            .v2_layout(),
            None
        );
        assert_eq!(
            Ty::Tuple {
                fields: vec![u8_ty.clone(), u64_ty]
            }
            .v2_layout(),
            None
        );
        assert_eq!(
            Ty::Slice {
                elem: Box::new(u8_ty)
            }
            .v2_layout(),
            None
        );
    }

    #[test]
    fn profile_v2_validators_and_gating_reject_malformed_ir() {
        let u8_ity = IntTy {
            width: IntWidth::I8,
            signed: false,
        };
        let u64_ity = IntTy {
            width: IntWidth::I64,
            signed: false,
        };
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let isize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: true,
        });
        let u8_ty = Ty::Int(u8_ity);
        let u64_ty = Ty::Int(u64_ity);
        let range_usize = Ty::Range {
            elem: Box::new(usize_ty.clone()),
        };
        let opt_u64 = Ty::Option {
            elem: Box::new(u64_ty.clone()),
        };
        let mut_ref_u64 = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(u64_ty.clone()),
        };
        let enum_ty = Ty::Enum(
            EnumTy::try_new(
                404,
                IntTy {
                    width: IntWidth::Isize,
                    signed: true,
                },
                EnumTagRepr::ZeroSized,
                vec![0],
            )
            .unwrap(),
        );

        // Positive and negative is_array_eq_elem_supported coverage.
        assert!(u8_ty.is_array_eq_elem_supported());
        assert!(Ty::Bool.is_array_eq_elem_supported());
        assert!(Ty::Char.is_array_eq_elem_supported());
        assert!(Ty::Ordering.is_array_eq_elem_supported());
        assert!(Ty::Unit.is_array_eq_elem_supported());
        assert!(Ty::Array {
            elem: Box::new(u8_ty.clone()),
            len: 2,
        }
        .is_array_eq_elem_supported());
        assert!(!Ty::Never.is_array_eq_elem_supported());
        assert!(!enum_ty.is_array_eq_elem_supported());
        assert!(!opt_u64.is_array_eq_elem_supported());
        assert!(!range_usize.is_array_eq_elem_supported());
        assert!(!mut_ref_u64.is_array_eq_elem_supported());

        // Ty::is_profile_v2 gates Range and Option.
        assert!(range_usize.is_profile_v2());
        assert!(opt_u64.is_profile_v2());
        assert!(!u64_ty.is_profile_v2());

        // AggregateRange: positive, wrong dst_ty, and half-ill-typed bounds.
        let agg_range_ok = Body::try_new(
            2,
            false,
            vec![range_usize.clone(), usize_ty.clone(), usize_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::AggregateRange {
                        elem_ty: usize_ty.clone(),
                        start: Operand::Copy { local: 1 },
                        end: Operand::Copy { local: 2 },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::agg_range_ok".into(),
        )
        .unwrap();
        assert!(agg_range_ok.uses_profile_v2());

        let agg_range_bad_dst = Body::try_new(
            2,
            false,
            vec![usize_ty.clone(), usize_ty.clone(), usize_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::AggregateRange {
                        elem_ty: usize_ty.clone(),
                        start: Operand::Copy { local: 1 },
                        end: Operand::Copy { local: 2 },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::agg_range_bad_dst".into(),
        )
        .unwrap_err();
        assert!(
            agg_range_bad_dst.contains("AggregateRange"),
            "{agg_range_bad_dst}"
        );

        let agg_range_bad_end = Body::try_new(
            2,
            false,
            vec![range_usize.clone(), usize_ty.clone(), u8_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::AggregateRange {
                        elem_ty: usize_ty.clone(),
                        start: Operand::Copy { local: 1 },
                        end: Operand::Copy { local: 2 },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::agg_range_bad_end".into(),
        )
        .unwrap_err();
        assert!(
            agg_range_bad_end.contains("AggregateRange"),
            "{agg_range_bad_end}"
        );

        let agg_range_bad_start = Body::try_new(
            2,
            false,
            vec![range_usize.clone(), u8_ty.clone(), usize_ty.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::AggregateRange {
                        elem_ty: usize_ty.clone(),
                        start: Operand::Copy { local: 1 },
                        end: Operand::Copy { local: 2 },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::agg_range_bad_start".into(),
        )
        .unwrap_err();
        assert!(
            agg_range_bad_start.contains("AggregateRange"),
            "{agg_range_bad_start}"
        );

        // Option Discriminant: positive isize dst, negative non-isize dst.
        let opt_discr_ok = Body::try_new(
            1,
            false,
            vec![isize_ty.clone(), opt_u64.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Discriminant {
                        place: Place {
                            local: 1,
                            projection: vec![],
                        },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::opt_discr_ok".into(),
        )
        .unwrap();
        assert!(opt_discr_ok.uses_profile_v2());

        let opt_discr_bad = Body::try_new(
            1,
            false,
            vec![u8_ty.clone(), opt_u64.clone()],
            vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Discriminant {
                        place: Place {
                            local: 1,
                            projection: vec![],
                        },
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::opt_discr_bad".into(),
        )
        .unwrap_err();
        assert!(opt_discr_bad.contains("discriminant"), "{opt_discr_bad}");

        // NumOverflowingAdd/Sub: positive + negative r_ty/dst_ty/l_ty checks.
        for op in [
            CoreCallOp::NumOverflowingAdd(u64_ity),
            CoreCallOp::NumOverflowingSub(u64_ity),
        ] {
            let ovf_ok = Body::try_new(
                2,
                false,
                vec![Ty::OverflowPair(u64_ity), u64_ty.clone(), u64_ty.clone()],
                vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::CoreCall {
                            op: op.clone(),
                            args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                            dst: Place {
                                local: 0,
                                projection: vec![],
                            },
                            target: 1,
                            unwind: UnwindAction::Unreachable,
                        },
                    },
                    Block {
                        statements: vec![],
                        terminator: Terminator::Ret,
                    },
                ],
                "rust-path-v1::ovf_ok".into(),
            )
            .unwrap();
            assert!(ovf_ok.uses_profile_v2());

            // Valid l_ty + mismatched r_ty must still fail closed.
            let ovf_bad_rhs = Body::try_new(
                2,
                false,
                vec![Ty::OverflowPair(u64_ity), u64_ty.clone(), u8_ty.clone()],
                vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::CoreCall {
                            op: op.clone(),
                            args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                            dst: Place {
                                local: 0,
                                projection: vec![],
                            },
                            target: 1,
                            unwind: UnwindAction::Unreachable,
                        },
                    },
                    Block {
                        statements: vec![],
                        terminator: Terminator::Ret,
                    },
                ],
                "rust-path-v1::ovf_bad_rhs".into(),
            )
            .unwrap_err();
            assert!(ovf_bad_rhs.contains("invalid CoreCall"), "{ovf_bad_rhs}");

            // Valid l_ty + valid r_ty + wrong dst_ty must still fail closed.
            let ovf_bad_dst = Body::try_new(
                2,
                false,
                vec![u64_ty.clone(), u64_ty.clone(), u64_ty.clone()],
                vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::CoreCall {
                            op,
                            args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                            dst: Place {
                                local: 0,
                                projection: vec![],
                            },
                            target: 1,
                            unwind: UnwindAction::Unreachable,
                        },
                    },
                    Block {
                        statements: vec![],
                        terminator: Terminator::Ret,
                    },
                ],
                "rust-path-v1::ovf_bad_dst".into(),
            )
            .unwrap_err();
            assert!(ovf_bad_dst.contains("invalid CoreCall"), "{ovf_bad_dst}");
        }

        // CoreCallOp::MemReplace: positive and mismatched src_ty rejection.
        let mem_replace_ok = Body::try_new(
            2,
            false,
            vec![u64_ty.clone(), mut_ref_u64.clone(), u64_ty.clone()],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::MemReplace { ty: u64_ty.clone() },
                        args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                        dst: Place {
                            local: 0,
                            projection: vec![],
                        },
                        target: 1,
                        unwind: UnwindAction::Unreachable,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::mem_replace_ok".into(),
        )
        .unwrap();
        assert!(mem_replace_ok.uses_profile_v2());

        let mem_replace_bad_src = Body::try_new(
            2,
            false,
            vec![u64_ty.clone(), mut_ref_u64, u8_ty.clone()],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::MemReplace { ty: u64_ty.clone() },
                        args: vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                        dst: Place {
                            local: 0,
                            projection: vec![],
                        },
                        target: 1,
                        unwind: UnwindAction::Unreachable,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::mem_replace_bad_src".into(),
        )
        .unwrap_err();
        assert!(
            mem_replace_bad_src.contains("invalid CoreCall"),
            "{mem_replace_bad_src}"
        );

        // Program::try_new enforces Profile v2 vs Profile v1 Call exclusivity.
        let v1_callee = Body::try_new(
            1,
            false,
            vec![u64_ty.clone(), u64_ty.clone()],
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
            "rust-path-v1::v1_callee".into(),
        )
        .unwrap();
        let v1_caller = Body::try_new(
            1,
            false,
            vec![u64_ty.clone(), u64_ty.clone()],
            vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::Call {
                        callee: 0,
                        args: vec![Operand::Copy { local: 1 }],
                        dst: 0,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                },
                Block {
                    statements: vec![],
                    terminator: Terminator::Ret,
                },
            ],
            "rust-path-v1::v1_caller".into(),
        )
        .unwrap();
        let mixed_err =
            Program::try_new(Scope::Crate, vec![v1_callee, v1_caller, agg_range_ok]).unwrap_err();
        assert!(mixed_err.contains("Profile v2"), "{mixed_err}");

        // `Rvalue::AggregateOption` validation: valid None/Some, bad dst,
        // mismatched Some payload, and invalid variant/payload combinations.
        let opt_u64_ty = Ty::Option {
            elem: Box::new(u64_ty.clone()),
        };
        let opt_u8_ty = Ty::Option {
            elem: Box::new(u8_ty.clone()),
        };
        let u32_ity = IntTy {
            width: IntWidth::I32,
            signed: false,
        };
        let u32_ty = Ty::Int(u32_ity);
        let i32_ty = Ty::Int(IntTy {
            width: IntWidth::I32,
            signed: true,
        });
        let i64_ty = Ty::Int(IntTy {
            width: IntWidth::I64,
            signed: true,
        });
        let check_agg_opt = |locals: Vec<Ty>, arg_count: usize, value: Rvalue| {
            Body::try_new(
                arg_count,
                false,
                locals,
                vec![Block {
                    statements: vec![Statement::Assign { local: 0, value }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::agg_opt_check".into(),
            )
        };
        assert!(
            check_agg_opt(
                vec![opt_u64_ty.clone()],
                0,
                Rvalue::AggregateOption {
                    variant_idx: 0,
                    inner_ty: u64_ty.clone(),
                    payload: None,
                },
            )
            .is_ok()
        );
        assert!(
            check_agg_opt(
                vec![opt_u64_ty.clone(), u64_ty.clone()],
                1,
                Rvalue::AggregateOption {
                    variant_idx: 1,
                    inner_ty: u64_ty.clone(),
                    payload: Some(Box::new(Operand::Copy { local: 1 })),
                },
            )
            .is_ok()
        );
        let agg_opt_bad_dst = check_agg_opt(
            vec![opt_u8_ty],
            0,
            Rvalue::AggregateOption {
                variant_idx: 0,
                inner_ty: u64_ty.clone(),
                payload: None,
            },
        )
        .unwrap_err();
        assert!(
            agg_opt_bad_dst.contains("AggregateOption requires Option<inner_ty> destination"),
            "{agg_opt_bad_dst}"
        );
        let agg_opt_bad_some_ty = check_agg_opt(
            vec![opt_u64_ty.clone(), u8_ty.clone()],
            1,
            Rvalue::AggregateOption {
                variant_idx: 1,
                inner_ty: u64_ty.clone(),
                payload: Some(Box::new(Operand::Copy { local: 1 })),
            },
        )
        .unwrap_err();
        assert!(
            agg_opt_bad_some_ty.contains("AggregateOption Some payload type mismatch"),
            "{agg_opt_bad_some_ty}"
        );
        for (variant_idx, payload) in [
            (0, Some(Box::new(Operand::Copy { local: 1 }))),
            (1, None),
            (2, None),
        ] {
            let err = check_agg_opt(
                vec![opt_u64_ty.clone(), u64_ty.clone()],
                1,
                Rvalue::AggregateOption {
                    variant_idx,
                    inner_ty: u64_ty.clone(),
                    payload,
                },
            )
            .unwrap_err();
            assert!(
                err.contains("invalid AggregateOption variant/payload"),
                "variant={variant_idx}: {err}"
            );
        }

        // `NumWrappingShl`, `NumWrappingShr`, and `NumLeadingZeros` operand and
        // destination type guards (positive + every individual mismatch).
        let check_core_call = |locals: Vec<Ty>, arg_count: usize, op: CoreCallOp, args: Vec<Operand>| {
            Body::try_new(
                arg_count,
                false,
                locals,
                vec![
                    Block {
                        statements: vec![],
                        terminator: Terminator::CoreCall {
                            op,
                            args,
                            dst: Place {
                                local: 0,
                                projection: vec![],
                            },
                            target: 1,
                            unwind: UnwindAction::Unreachable,
                        },
                    },
                    Block {
                        statements: vec![],
                        terminator: Terminator::Ret,
                    },
                ],
                "rust-path-v1::core_call_check".into(),
            )
        };
        for op in [
            CoreCallOp::NumWrappingShl(u64_ity),
            CoreCallOp::NumWrappingShr(u64_ity),
        ] {
            assert!(
                check_core_call(
                    vec![u64_ty.clone(), u64_ty.clone(), u32_ty.clone()],
                    2,
                    op.clone(),
                    vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                )
                .is_ok()
            );
            for (label, locals) in [
                ("bad_l_ty", vec![u64_ty.clone(), u8_ty.clone(), u32_ty.clone()]),
                ("bad_r_ty_width", vec![u64_ty.clone(), u64_ty.clone(), u64_ty.clone()]),
                ("bad_r_ty_sign", vec![u64_ty.clone(), u64_ty.clone(), i32_ty.clone()]),
                ("bad_dst_width", vec![u32_ty.clone(), u64_ty.clone(), u32_ty.clone()]),
                ("bad_dst_sign", vec![i64_ty.clone(), u64_ty.clone(), u32_ty.clone()]),
            ] {
                let err = check_core_call(
                    locals,
                    2,
                    op.clone(),
                    vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                )
                .unwrap_err();
                assert!(err.contains("invalid CoreCall"), "{label}: {err}");
            }
        }
        assert!(
            check_core_call(
                vec![u32_ty.clone(), u64_ty.clone()],
                1,
                CoreCallOp::NumLeadingZeros(u64_ity),
                vec![Operand::Copy { local: 1 }],
            )
            .is_ok()
        );
        for (label, locals) in [
            ("lz_bad_l_ty", vec![u32_ty.clone(), u8_ty.clone()]),
            ("lz_bad_dst_width", vec![u64_ty.clone(), u64_ty.clone()]),
            ("lz_bad_dst_sign", vec![i32_ty, u64_ty.clone()]),
        ] {
            let err = check_core_call(
                locals,
                1,
                CoreCallOp::NumLeadingZeros(u64_ity),
                vec![Operand::Copy { local: 1 }],
            )
            .unwrap_err();
            assert!(err.contains("invalid CoreCall"), "{label}: {err}");
        }

        // `CoreCallOp::{SliceSplitAt, NumIsMultipleOf, OptionIsSome, OptionIsNone}`
        // signature checks (positive + negative cases).
        let usize_ty = Ty::Int(IntTy {
            width: IntWidth::Isize,
            signed: false,
        });
        let slice_u8_shared = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Slice {
                elem: Box::new(u8_ty.clone()),
            }),
        };
        let slice_u8_mut = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(Ty::Slice {
                elem: Box::new(u8_ty.clone()),
            }),
        };
        let slice_u32_shared = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Slice {
                elem: Box::new(u32_ty.clone()),
            }),
        };
        let split_shared_dst = Ty::Tuple {
            fields: vec![slice_u8_shared.clone(), slice_u8_shared.clone()],
        };
        let split_mut_dst = Ty::Tuple {
            fields: vec![slice_u8_mut.clone(), slice_u8_mut.clone()],
        };
        assert!(
            check_core_call(
                vec![
                    split_shared_dst.clone(),
                    slice_u8_shared.clone(),
                    usize_ty.clone(),
                ],
                2,
                CoreCallOp::SliceSplitAt {
                    mutability: Mutability::Shared,
                    elem: u8_ty.clone(),
                },
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .is_ok()
        );
        assert!(
            check_core_call(
                vec![split_mut_dst.clone(), slice_u8_mut.clone(), usize_ty.clone()],
                2,
                CoreCallOp::SliceSplitAt {
                    mutability: Mutability::Mut,
                    elem: u8_ty.clone(),
                },
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .is_ok()
        );
        for (label, locals, op) in [
            (
                "split_at_bad_mid_ty_with_valid_dst",
                vec![
                    split_shared_dst.clone(),
                    slice_u8_shared.clone(),
                    u32_ty.clone(),
                ],
                CoreCallOp::SliceSplitAt {
                    mutability: Mutability::Shared,
                    elem: u8_ty.clone(),
                },
            ),
            (
                "split_at_bad_elem_with_valid_dst",
                vec![
                    split_shared_dst.clone(),
                    slice_u32_shared.clone(),
                    usize_ty.clone(),
                ],
                CoreCallOp::SliceSplitAt {
                    mutability: Mutability::Shared,
                    elem: u8_ty.clone(),
                },
            ),
            (
                "split_at_bad_mut_with_valid_dst",
                vec![
                    split_shared_dst.clone(),
                    slice_u8_mut.clone(),
                    usize_ty.clone(),
                ],
                CoreCallOp::SliceSplitAt {
                    mutability: Mutability::Shared,
                    elem: u8_ty.clone(),
                },
            ),
            (
                "split_at_bad_dst_ty",
                vec![
                    split_mut_dst,
                    slice_u8_shared.clone(),
                    usize_ty.clone(),
                ],
                CoreCallOp::SliceSplitAt {
                    mutability: Mutability::Shared,
                    elem: u8_ty.clone(),
                },
            ),
        ] {
            let err = check_core_call(
                locals,
                2,
                op,
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .unwrap_err();
            assert!(err.contains("invalid CoreCall"), "{label}: {err}");
        }

        // `CoreCallOp::SliceIndexRangeFrom` checks the input mutability and
        // element against the destination, not just the destination.
        let range_from_usize = Ty::RangeFrom {
            elem: Box::new(usize_ty.clone()),
        };
        let u16_ty = Ty::Int(IntTy {
            width: IntWidth::I16,
            signed: false,
        });
        let slice_u16_shared = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Slice {
                elem: Box::new(u16_ty.clone()),
            }),
        };
        assert!(
            check_core_call(
                vec![
                    slice_u8_shared.clone(),
                    slice_u8_shared.clone(),
                    range_from_usize.clone(),
                ],
                2,
                CoreCallOp::SliceIndexRangeFrom {
                    mutability: Mutability::Shared,
                    elem: u8_ty.clone(),
                },
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .is_ok()
        );
        for (label, locals, op) in [
            (
                "range_from_shared_to_mut",
                vec![
                    slice_u8_mut.clone(),
                    slice_u8_shared.clone(),
                    range_from_usize.clone(),
                ],
                CoreCallOp::SliceIndexRangeFrom {
                    mutability: Mutability::Mut,
                    elem: u8_ty.clone(),
                },
            ),
            (
                "range_from_elem_mismatch",
                vec![
                    slice_u16_shared.clone(),
                    slice_u8_shared.clone(),
                    range_from_usize.clone(),
                ],
                CoreCallOp::SliceIndexRangeFrom {
                    mutability: Mutability::Shared,
                    elem: u16_ty.clone(),
                },
            ),
        ] {
            let err = check_core_call(
                locals,
                2,
                op,
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .unwrap_err();
            assert!(err.contains("invalid CoreCall"), "{label}: {err}");
        }

        // `CoreCallOp::{NumCheckedAdd, NumCheckedMul, NumCheckedSub}` admit
        // `Option<T>` results over matching operands only.
        let u8_ity = IntTy {
            width: IntWidth::I8,
            signed: false,
        };
        let opt_u8_ty = Ty::Option {
            elem: Box::new(u8_ty.clone()),
        };
        for op in [
            CoreCallOp::NumCheckedAdd(u8_ity),
            CoreCallOp::NumCheckedMul(u8_ity),
            CoreCallOp::NumCheckedSub(u8_ity),
        ] {
            assert!(
                check_core_call(
                    vec![opt_u8_ty.clone(), u8_ty.clone(), u8_ty.clone()],
                    2,
                    op.clone(),
                    vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                )
                .is_ok(),
                "{op:?}"
            );
            for (label, locals) in [
                (
                    "checked_bad_dst",
                    vec![u8_ty.clone(), u8_ty.clone(), u8_ty.clone()],
                ),
                (
                    "checked_bad_rhs",
                    vec![opt_u8_ty.clone(), u8_ty.clone(), u32_ty.clone()],
                ),
            ] {
                let err = check_core_call(
                    locals,
                    2,
                    op.clone(),
                    vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
                )
                .unwrap_err();
                assert!(err.contains("invalid CoreCall"), "{label} {op:?}: {err}");
            }
        }

        let i64_ity = IntTy {
            width: IntWidth::I64,
            signed: true,
        };
        let i64_ty = Ty::Int(i64_ity);
        assert!(
            check_core_call(
                vec![Ty::Bool, u64_ty.clone(), u64_ty.clone()],
                2,
                CoreCallOp::NumIsMultipleOf(u64_ity),
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .is_ok()
        );
        for (label, locals, op) in [
            (
                "is_multiple_of_bad_r_ty_width",
                vec![Ty::Bool, u64_ty.clone(), u32_ty.clone()],
                CoreCallOp::NumIsMultipleOf(u64_ity),
            ),
            (
                "is_multiple_of_bad_r_ty_sign",
                vec![Ty::Bool, u64_ty.clone(), i64_ty.clone()],
                CoreCallOp::NumIsMultipleOf(u64_ity),
            ),
            (
                "is_multiple_of_bad_l_ty",
                vec![Ty::Bool, u32_ty.clone(), u64_ty.clone()],
                CoreCallOp::NumIsMultipleOf(u64_ity),
            ),
            (
                "is_multiple_of_signed_rejected",
                vec![Ty::Bool, i64_ty.clone(), i64_ty],
                CoreCallOp::NumIsMultipleOf(i64_ity),
            ),
            (
                "is_multiple_of_bad_dst_ty",
                vec![u64_ty.clone(), u64_ty.clone(), u64_ty.clone()],
                CoreCallOp::NumIsMultipleOf(u64_ity),
            ),
        ] {
            let err = check_core_call(
                locals,
                2,
                op,
                vec![Operand::Copy { local: 1 }, Operand::Copy { local: 2 }],
            )
            .unwrap_err();
            assert!(err.contains("invalid CoreCall"), "{label}: {err}");
        }

        let ref_opt_u32 = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Option {
                elem: Box::new(u32_ty.clone()),
            }),
        };
        let ref_opt_u64 = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Option {
                elem: Box::new(u64_ty.clone()),
            }),
        };
        let ref_u32 = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(u32_ty.clone()),
        };
        for op_ctor in [
            |t| CoreCallOp::OptionIsSome { inner: t },
            |t| CoreCallOp::OptionIsNone { inner: t },
        ] {
            assert!(
                check_core_call(
                    vec![Ty::Bool, ref_opt_u32.clone()],
                    1,
                    op_ctor(u32_ty.clone()),
                    vec![Operand::Copy { local: 1 }],
                )
                .is_ok()
            );
            for (label, locals, op) in [
                (
                    "opt_pred_mismatched_inner",
                    vec![Ty::Bool, ref_opt_u64.clone()],
                    op_ctor(u32_ty.clone()),
                ),
                (
                    "opt_pred_non_option_pointee",
                    vec![Ty::Bool, ref_u32.clone()],
                    op_ctor(u32_ty.clone()),
                ),
                (
                    "opt_pred_bad_dst_ty",
                    vec![u32_ty.clone(), ref_opt_u32.clone()],
                    op_ctor(u32_ty.clone()),
                ),
            ] {
                let err = check_core_call(locals, 1, op, vec![Operand::Copy { local: 1 }])
                    .unwrap_err();
                assert!(err.contains("invalid CoreCall"), "{label}: {err}");
            }
        }

        // `check_place` rejects post-field, post-downcast, and nested `Deref`.
        let ref_u8_ty = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(u8_ty.clone()),
        };
        let mut_ref_u8_ty = Ty::Ref {
            mutability: Mutability::Mut,
            pointee: Box::new(u8_ty.clone()),
        };
        let tuple_ref_u8 = Ty::Tuple {
            fields: vec![ref_u8_ty.clone(), u8_ty.clone()],
        };
        let tuple_mut_ref_u8 = Ty::Tuple {
            fields: vec![mut_ref_u8_ty.clone(), u8_ty.clone()],
        };
        let opt_ref_u8 = Ty::Option {
            elem: Box::new(ref_u8_ty.clone()),
        };
        for (label, arg_ty, projection) in [
            (
                "post_field_deref",
                tuple_ref_u8,
                vec![
                    PlaceElem::Field {
                        index: 0,
                        ty: ref_u8_ty.clone(),
                    },
                    PlaceElem::Deref,
                ],
            ),
            (
                "post_downcast_field_deref",
                opt_ref_u8,
                vec![
                    PlaceElem::Downcast { variant_idx: 1 },
                    PlaceElem::Field {
                        index: 0,
                        ty: ref_u8_ty.clone(),
                    },
                    PlaceElem::Deref,
                ],
            ),
            (
                "nested_deref",
                ref_u8_ty,
                vec![PlaceElem::Deref, PlaceElem::Deref],
            ),
        ] {
            let err = Body::try_new(
                1,
                false,
                vec![u8_ty.clone(), arg_ty],
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::CopyPlace {
                                place: Place {
                                    local: 1,
                                    projection,
                                },
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::bad_deref_read".into(),
            )
            .unwrap_err();
            assert!(
                err.contains("nested or post-field deref projections are unsupported"),
                "{label}: {err}"
            );
        }
        let post_field_write_err = Body::try_new(
            2,
            false,
            vec![Ty::Unit, tuple_mut_ref_u8, u8_ty.clone()],
            vec![Block {
                statements: vec![Statement::AssignPlace {
                    place: Place {
                        local: 1,
                        projection: vec![
                            PlaceElem::Field {
                                index: 0,
                                ty: mut_ref_u8_ty,
                            },
                            PlaceElem::Deref,
                        ],
                    },
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 2 },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::bad_deref_write".into(),
        )
        .unwrap_err();
        assert!(
            post_field_write_err.contains("nested or post-field deref projections are unsupported"),
            "{post_field_write_err}"
        );

        // `check_place` rejects post-deref and nested `Downcast`.
        let opt_u8 = Ty::Option {
            elem: Box::new(u8_ty.clone()),
        };
        let ref_opt_u8 = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(opt_u8.clone()),
        };
        for (label, arg_ty, projection) in [
            (
                "post_deref_downcast",
                ref_opt_u8,
                vec![
                    PlaceElem::Deref,
                    PlaceElem::Downcast { variant_idx: 1 },
                    PlaceElem::Field {
                        index: 0,
                        ty: u8_ty.clone(),
                    },
                ],
            ),
            (
                "nested_downcast",
                opt_u8,
                vec![
                    PlaceElem::Downcast { variant_idx: 1 },
                    PlaceElem::Downcast { variant_idx: 1 },
                    PlaceElem::Field {
                        index: 0,
                        ty: u8_ty.clone(),
                    },
                ],
            ),
        ] {
            let err = Body::try_new(
                1,
                false,
                vec![u8_ty.clone(), arg_ty],
                vec![Block {
                    statements: vec![Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::CopyPlace {
                                place: Place {
                                    local: 1,
                                    projection,
                                },
                            },
                            with_retag: false,
                        },
                    }],
                    terminator: Terminator::Ret,
                }],
                "rust-path-v1::bad_downcast_read".into(),
            )
            .unwrap_err();
            assert!(
                err.contains("nested or post-deref downcast projections are unsupported"),
                "{label}: {err}"
            );
        }
    }
}
