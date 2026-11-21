// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Regression tests for #3929 and identifier-collision hygiene in generated
// field projections:
// - Ensure all derives compile cleanly under `#![deny(warnings,
//   non_ascii_idents)]` and `#![forbid(uncommon_codepoints, confusable_idents,
//   mixed_script_confusables)]` (catching both identifier lints and any
//   `#[allow(...)]` attributes that would conflict with crate-level `forbid`).
// - Ensure generated `___ZcField_*`, `___ZcAliasing`, and `___ZcAlignment`
//   identifiers do not collide with user-defined type names, field types,
//   generic parameters, or cascading `a` / `a_` field pairs.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![deny(warnings, non_ascii_idents)]
#![forbid(uncommon_codepoints, confusable_idents, mixed_script_confusables)]
#![allow(dead_code, non_camel_case_types)]

include!("include.rs");

mod vis_scope {
    use super::imp;

    #[derive(
        imp::KnownLayout,
        imp::FromBytes,
        imp::IntoBytes,
        imp::Immutable,
        imp::Unaligned,
        imp::ByteEq,
        imp::ByteHash,
        imp::Project,
    )]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub struct NamedFromBytes {
        pub pub_field: u8,
        pub(crate) crate_field: u8,
        pub(super) super_field: u8,
        priv_field: u8,
        pub r#type: u8,
        pub r#match: u8,
    }

    #[derive(imp::KnownLayout, imp::FromZeros, imp::Immutable, imp::Project)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub struct NamedFromZeros {
        priv_field: imp::Option<imp::core::num::NonZeroU8>,
        pub pub_field: bool,
    }

    #[derive(imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub struct NamedTryFromBytes {
        priv_field: bool,
        pub pub_field: imp::core::num::NonZeroU8,
    }

    #[derive(
        imp::KnownLayout,
        imp::FromBytes,
        imp::IntoBytes,
        imp::Immutable,
        imp::Unaligned,
        imp::ByteEq,
        imp::ByteHash,
        imp::Project,
    )]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    pub struct TupleStruct(u8, pub(super) u8, pub(crate) u8, pub u8);
}

#[derive(
    imp::KnownLayout,
    imp::FromBytes,
    imp::IntoBytes,
    imp::Immutable,
    imp::Unaligned,
    imp::ByteEq,
    imp::ByteHash,
    imp::Project,
)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct UnitStruct;

#[derive(
    imp::KnownLayout,
    imp::FromBytes,
    imp::IntoBytes,
    imp::Immutable,
    imp::Unaligned,
    imp::ByteEq,
    imp::ByteHash,
    imp::Project,
)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct EmptyBracedStruct {}

#[derive(
    imp::KnownLayout, imp::FromBytes, imp::IntoBytes, imp::Immutable, imp::Unaligned, imp::Project,
)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed)]
pub struct PackedStruct {
    pub a: u8,
    pub b: u16,
}

#[derive(
    imp::KnownLayout,
    imp::FromBytes,
    imp::IntoBytes,
    imp::Immutable,
    imp::Unaligned,
    imp::SplitAt,
    imp::Project,
)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct SliceDstStruct {
    pub head: u8,
    pub tail: [u8],
}

#[derive(imp::KnownLayout, imp::FromBytes, imp::Immutable, imp::Unaligned, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub union ReprCUnion {
    pub a: u8,
    pub b: [u8; 2],
}

#[derive(imp::KnownLayout, imp::FromZeros, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
pub union DefaultReprUnion {
    pub a: bool,
    pub b: [u8; 2],
}

#[derive(imp::KnownLayout, imp::FromZeros, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub enum ReprCEnum {
    Unit,
    Tuple(u8, bool),
    Struct { a: u8, r#type: bool },
}

#[derive(imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(i16)]
pub enum ReprIntEnum {
    Unit,
    Tuple(u8, imp::core::num::NonZeroU8),
    Struct { a: u8, b: bool },
}

macro_rules! define_in_macro {
    ($name:ident, $field:ident) => {
        #[derive(imp::KnownLayout, imp::FromBytes, imp::Project)]
        #[zerocopy(crate = "zerocopy_renamed")]
        #[repr(C)]
        pub struct $name {
            pub $field: u8,
        }
    };
}

define_in_macro!(MacroGeneratedStruct, macro_field);

// Outer type whose name matches the default field marker for field `b`.
// Critically, `___ZcField_b` wraps `bool` (not `FromBytes`), so if the inner
// `enum ___ZcField_b {}` ever shadowed this outer type in `HasField`, either
// compilation would fail or validation of field `a` would be corrupted.
#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
pub struct ___ZcField_b(pub bool);

#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct OuterTypeCollision {
    pub a: ___ZcField_b,
    pub b: u8,
}

// Type whose own identifier matches the default field marker for its field `a`.
#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct ___ZcField_a {
    pub a: bool,
}

#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
pub struct ___ZcAliasing(pub bool);

macro_rules! hidden_zc_field_a {
    () => {
        ___ZcField_a
    };
}

macro_rules! hidden_zc_field_b {
    () => {
        ___ZcField_b
    };
}

macro_rules! hidden_zc_aliasing {
    () => {
        ___ZcAliasing
    };
}

// Type-position macros hide `___ZcField_a`, `___ZcField_b`, and `___ZcAliasing`
// from unexpanded `DeriveInput` tokens; replayed `#ty` must still bind to the
// outer types rather than generated marker enums or trait-impl type parameters.
#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct UnexpandedMacroFieldCollision {
    pub a: hidden_zc_field_a!(),
    b: hidden_zc_field_b!(),
    pub c: hidden_zc_aliasing!(),
}

// Generic parameter collisions on structs, tuple structs, unions, and enums,
// including cascading collisions (`___ZcField_a` + `___ZcField__b`), raw
// identifiers (`r#___ZcField_a`), `a` vs `a_` field pairs, and internal
// `___ZcAliasing` / `___ZcAlignment` type parameters.
#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct CascadingGenericCollision<___ZcField_a, r#___ZcField__b, ___ZcAliasing, ___ZcAlignment> {
    pub a: u8,
    pub a_: u8,
    pub b: bool,
    pub b_: u8,
    pub _marker: imp::PhantomData<(___ZcField_a, r#___ZcField__b, ___ZcAliasing, ___ZcAlignment)>,
}

#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub struct TupleGenericCollision<___ZcField_0, ___ZcField_1, ___ZcAliasing, ___ZcAlignment>(
    pub u8,
    pub bool,
    pub imp::PhantomData<(___ZcField_0, ___ZcField_1, ___ZcAliasing, ___ZcAlignment)>,
);

#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
pub union UnionGenericCollision<___ZcField_a, ___ZcAliasing, ___ZcAlignment> {
    pub a: bool,
    pub b: u8,
    pub _marker: imp::PhantomData<(___ZcField_a, ___ZcAliasing, ___ZcAlignment)>,
}

#[derive(Clone, Copy, imp::KnownLayout, imp::TryFromBytes, imp::Immutable, imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
pub enum EnumGenericCollision<
    ___ZcField_0,
    ___ZcField_1,
    ___ZcField_a,
    ___ZcField___field_Struct,
    ___ZcField_tag,
    ___ZcField_variants,
    ___ZcAliasing,
    ___ZcAlignment,
> {
    Unit,
    Tuple(u8, bool),
    Struct {
        a: bool,
        b: u8,
        _m1:
            imp::PhantomData<(___ZcField_0, ___ZcField_1, ___ZcField_a, ___ZcField___field_Struct)>,
        _m2: imp::PhantomData<(___ZcField_tag, ___ZcField_variants, ___ZcAliasing, ___ZcAlignment)>,
    },
}

#[test]
fn test_collisions_preserve_validation_and_projection() {
    // `OuterTypeCollision.a` has type `___ZcField_b(bool)` at byte 0 and `b: u8`
    // at byte 1. Byte 0 must still be validated as `bool`.
    util::test_is_safe::<OuterTypeCollision, _>([0u8, 0xFF], true);
    util::test_is_safe::<OuterTypeCollision, _>([1u8, 0xFF], true);
    util::test_is_safe::<OuterTypeCollision, _>([2u8, 0xFF], false);

    // Self-named `___ZcField_a` must validate `a: bool`.
    util::test_is_safe::<___ZcField_a, _>([0u8], true);
    util::test_is_safe::<___ZcField_a, _>([1u8], true);
    util::test_is_safe::<___ZcField_a, _>([2u8], false);

    // `UnexpandedMacroFieldCollision`: all three fields wrap `bool`.
    util::test_is_safe::<UnexpandedMacroFieldCollision, _>([0u8, 1, 0], true);
    util::test_is_safe::<UnexpandedMacroFieldCollision, _>([2u8, 1, 0], false);
    util::test_is_safe::<UnexpandedMacroFieldCollision, _>([0u8, 2, 0], false);
    util::test_is_safe::<UnexpandedMacroFieldCollision, _>([0u8, 1, 2], false);

    // `CascadingGenericCollision`: `[a, a_, b, b_]` where `b` (index 2) is `bool`.
    type Cascaded = CascadingGenericCollision<u16, u32, u64, usize>;
    util::test_is_safe::<Cascaded, _>([0xAAu8, 0xBB, 1, 0xCC], true);
    util::test_is_safe::<Cascaded, _>([0xAAu8, 0xBB, 2, 0xCC], false);

    let mut cascaded = Cascaded { a: 10, a_: 20, b: false, b_: 30, _marker: imp::PhantomData };
    let mut ptr = imp::Ptr::from_mut(&mut cascaded);
    *ptr.reborrow()
        .project::<
            imp::project_clients::ProjectDerive,
            _,
            { imp::STRUCT_VARIANT_ID },
            { imp::ident_id!(a) },
        >()
        .unwrap()
        .as_mut() = 11;
    *ptr.reborrow()
        .project::<
            imp::project_clients::ProjectDerive,
            _,
            { imp::STRUCT_VARIANT_ID },
            { imp::ident_id!(a_) },
        >()
        .unwrap()
        .as_mut() = 22;
    *ptr.reborrow()
        .project::<
            imp::project_clients::ProjectDerive,
            _,
            { imp::STRUCT_VARIANT_ID },
            { imp::ident_id!(b) },
        >()
        .unwrap()
        .as_mut() = true;
    *ptr.reborrow()
        .project::<
            imp::project_clients::ProjectDerive,
            _,
            { imp::STRUCT_VARIANT_ID },
            { imp::ident_id!(b_) },
        >()
        .unwrap()
        .as_mut() = 33;
    imp::assert_eq!(cascaded.a, 11);
    imp::assert_eq!(cascaded.a_, 22);
    imp::assert!(cascaded.b);
    imp::assert_eq!(cascaded.b_, 33);

    // `TupleGenericCollision`: `(u8, bool, PhantomData<...>)`.
    type TupleCollided = TupleGenericCollision<u16, u32, u64, usize>;
    util::test_is_safe::<TupleCollided, _>([0x7Fu8, 0], true);
    util::test_is_safe::<TupleCollided, _>([0x7Fu8, 1], true);
    util::test_is_safe::<TupleCollided, _>([0x7Fu8, 2], false);

    // `UnionGenericCollision`: `a: bool`, `b: u8` — valid for all initialized bytes
    // because `b: u8` accepts every initialized byte, while `a: bool` only
    // accepts 0/1 when alone.
    type UnionCollided = UnionGenericCollision<u16, u32, u64>;
    util::test_is_safe::<UnionCollided, _>([2u8], true);

    // `EnumGenericCollision`: tag 0 = Unit, tag 1 = Tuple(u8, bool),
    // tag 2 = Struct { a: bool, b: u8 }.
    type EnumCollided = EnumGenericCollision<u8, u16, u32, u64, usize, i8, i16, i32>;
    util::test_is_safe::<EnumCollided, _>([0u8, 0xFF, 0xFF], true);
    util::test_is_safe::<EnumCollided, _>([1u8, 0xFF, 1], true);
    util::test_is_safe::<EnumCollided, _>([1u8, 0xFF, 2], false);
    util::test_is_safe::<EnumCollided, _>([2u8, 1, 0xFF], true);
    util::test_is_safe::<EnumCollided, _>([2u8, 2, 0xFF], false);
    util::test_is_safe::<EnumCollided, _>([3u8, 0, 0], false);
}
