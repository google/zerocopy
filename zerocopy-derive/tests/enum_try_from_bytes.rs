// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(Eq, PartialEq, Debug, imp::Immutable, imp::KnownLayout, imp::TryFromBytes)]
#[repr(u8)]
enum Foo {
    A,
}

util_assert_impl_all!(Foo: imp::TryFromBytes);

#[test]
fn test_foo() {
    imp::assert_eq!(<Foo as imp::TryFromBytes>::try_read_from_bytes(&[0]), imp::Ok(Foo::A));
    imp::assert!(<Foo as imp::TryFromBytes>::try_read_from_bytes(&[]).is_err());
    imp::assert!(<Foo as imp::TryFromBytes>::try_read_from_bytes(&[1]).is_err());
    imp::assert!(<Foo as imp::TryFromBytes>::try_read_from_bytes(&[0, 0]).is_err());
}

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes)]
#[repr(u16)]
enum Bar {
    A = 0,
}

util_assert_impl_all!(Bar: imp::TryFromBytes);

#[test]
fn test_bar() {
    imp::assert_eq!(<Bar as imp::TryFromBytes>::try_read_from_bytes(&[0, 0]), imp::Ok(Bar::A));
    imp::assert!(<Bar as imp::TryFromBytes>::try_read_from_bytes(&[]).is_err());
    imp::assert!(<Bar as imp::TryFromBytes>::try_read_from_bytes(&[0]).is_err());
    imp::assert!(<Bar as imp::TryFromBytes>::try_read_from_bytes(&[0, 1]).is_err());
    imp::assert!(<Bar as imp::TryFromBytes>::try_read_from_bytes(&[0, 0, 0]).is_err());
}

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes)]
#[repr(u32)]
enum Baz {
    A = 1,
    B = 0,
}

util_assert_impl_all!(Baz: imp::TryFromBytes);

#[test]
fn test_baz() {
    imp::assert_eq!(
        <Baz as imp::TryFromBytes>::try_read_from_bytes(imp::IntoBytes::as_bytes(&1u32)),
        imp::Ok(Baz::A)
    );
    imp::assert_eq!(
        <Baz as imp::TryFromBytes>::try_read_from_bytes(imp::IntoBytes::as_bytes(&0u32)),
        imp::Ok(Baz::B)
    );
    imp::assert!(<Baz as imp::TryFromBytes>::try_read_from_bytes(&[]).is_err());
    imp::assert!(<Baz as imp::TryFromBytes>::try_read_from_bytes(&[0]).is_err());
    imp::assert!(<Baz as imp::TryFromBytes>::try_read_from_bytes(&[0, 0]).is_err());
    imp::assert!(<Baz as imp::TryFromBytes>::try_read_from_bytes(&[0, 0, 0]).is_err());
    imp::assert!(<Baz as imp::TryFromBytes>::try_read_from_bytes(&[0, 0, 0, 0, 0]).is_err());
}

// Test hygiene - make sure that `i8` being shadowed doesn't cause problems for
// the code emitted by the derive.
type i8 = bool;

const THREE: ::core::primitive::i8 = 3;

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes)]
#[repr(i8)]
enum Blah {
    A = 1,
    B = 0,
    C = 1 + 2,
    D = 3 + THREE,
}

util_assert_impl_all!(Blah: imp::TryFromBytes);

#[test]
fn test_blah() {
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from_bytes(imp::IntoBytes::as_bytes(&1i8)),
        imp::Ok(Blah::A)
    );
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from_bytes(imp::IntoBytes::as_bytes(&0i8)),
        imp::Ok(Blah::B)
    );
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from_bytes(imp::IntoBytes::as_bytes(&3i8)),
        imp::Ok(Blah::C)
    );
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from_bytes(imp::IntoBytes::as_bytes(&6i8)),
        imp::Ok(Blah::D)
    );
    imp::assert!(<Blah as imp::TryFromBytes>::try_read_from_bytes(&[]).is_err());
    imp::assert!(<Blah as imp::TryFromBytes>::try_read_from_bytes(&[4]).is_err());
    imp::assert!(<Blah as imp::TryFromBytes>::try_read_from_bytes(&[0, 0]).is_err());
}

#[derive(
    Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes, imp::IntoBytes,
)]
#[repr(C)]
enum FieldlessButNotUnitOnly {
    A,
    B(),
    C {},
}

#[test]
fn test_fieldless_but_not_unit_only() {
    const SIZE: usize = ::core::mem::size_of::<FieldlessButNotUnitOnly>();
    let disc: [u8; SIZE] = ::zerocopy::transmute!(FieldlessButNotUnitOnly::A);
    imp::assert_eq!(
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from_bytes(&disc[..]),
        imp::Ok(FieldlessButNotUnitOnly::A)
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(FieldlessButNotUnitOnly::B());
    imp::assert_eq!(
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from_bytes(&disc[..]),
        imp::Ok(FieldlessButNotUnitOnly::B())
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(FieldlessButNotUnitOnly::C {});
    imp::assert_eq!(
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from_bytes(&disc[..]),
        imp::Ok(FieldlessButNotUnitOnly::C {})
    );
    imp::assert!(<FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from_bytes(
        &[0xFF; SIZE][..]
    )
    .is_err());
}

#[derive(
    Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes, imp::IntoBytes,
)]
#[repr(C)]
enum WeirdDiscriminants {
    A = -7,
    B,
    C = 33,
}

#[test]
fn test_weird_discriminants() {
    const SIZE: usize = ::core::mem::size_of::<WeirdDiscriminants>();
    let disc: [u8; SIZE] = ::zerocopy::transmute!(WeirdDiscriminants::A);
    imp::assert_eq!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from_bytes(&disc[..]),
        imp::Ok(WeirdDiscriminants::A)
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(WeirdDiscriminants::B);
    imp::assert_eq!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from_bytes(&disc[..]),
        imp::Ok(WeirdDiscriminants::B)
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(WeirdDiscriminants::C);
    imp::assert_eq!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from_bytes(&disc[..]),
        imp::Ok(WeirdDiscriminants::C)
    );
    imp::assert!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from_bytes(&[0xFF; SIZE][..]).is_err()
    );
}

// Technically non-portable since this is only `IntoBytes` if the discriminant
// is an `i32` or `u32`, but we'll cross that bridge when we get to it...
#[derive(
    Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes, imp::IntoBytes,
)]
#[repr(C)]
enum HasFields {
    A(u32),
    B { foo: ::core::num::NonZeroU32 },
}

#[test]
fn test_has_fields() {
    const SIZE: usize = ::core::mem::size_of::<HasFields>();

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(HasFields::A(10));
    imp::assert_eq!(
        <HasFields as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFields::A(10)),
    );

    let bytes: [u8; SIZE] =
        ::zerocopy::transmute!(HasFields::B { foo: ::core::num::NonZeroU32::new(123456).unwrap() });
    imp::assert_eq!(
        <HasFields as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFields::B { foo: ::core::num::NonZeroU32::new(123456).unwrap() }),
    );
}

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes)]
#[repr(C, align(16))]
enum HasFieldsAligned {
    A(u32),
    B { foo: ::core::num::NonZeroU32 },
}

util_assert_impl_all!(HasFieldsAligned: imp::TryFromBytes);

#[test]
fn test_has_fields_aligned() {
    const SIZE: usize = ::core::mem::size_of::<HasFieldsAligned>();

    #[derive(imp::IntoBytes)]
    #[repr(C)]
    struct BytesOfHasFieldsAligned {
        has_fields: HasFields,
        padding: [u8; 8],
    }

    let wrap = |has_fields| BytesOfHasFieldsAligned { has_fields, padding: [0; 8] };

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(wrap(HasFields::A(10)));
    imp::assert_eq!(
        <HasFieldsAligned as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFieldsAligned::A(10)),
    );

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(wrap(HasFields::B {
        foo: ::core::num::NonZeroU32::new(123456).unwrap()
    }));
    imp::assert_eq!(
        <HasFieldsAligned as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFieldsAligned::B { foo: ::core::num::NonZeroU32::new(123456).unwrap() }),
    );
}

#[derive(
    Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes, imp::IntoBytes,
)]
#[repr(u32)]
enum HasFieldsPrimitive {
    A(u32),
    B { foo: ::core::num::NonZeroU32 },
}

#[test]
fn test_has_fields_primitive() {
    const SIZE: usize = ::core::mem::size_of::<HasFieldsPrimitive>();

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(HasFieldsPrimitive::A(10));
    imp::assert_eq!(
        <HasFieldsPrimitive as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFieldsPrimitive::A(10)),
    );

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(HasFieldsPrimitive::B {
        foo: ::core::num::NonZeroU32::new(123456).unwrap(),
    });
    imp::assert_eq!(
        <HasFieldsPrimitive as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFieldsPrimitive::B { foo: ::core::num::NonZeroU32::new(123456).unwrap() }),
    );
}

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::Immutable, imp::TryFromBytes)]
#[repr(u32, align(16))]
enum HasFieldsPrimitiveAligned {
    A(u32),
    B { foo: ::core::num::NonZeroU32 },
}

util_assert_impl_all!(HasFieldsPrimitiveAligned: imp::TryFromBytes);

#[test]
fn test_has_fields_primitive_aligned() {
    const SIZE: usize = ::core::mem::size_of::<HasFieldsPrimitiveAligned>();

    #[derive(imp::IntoBytes)]
    #[repr(C)]
    struct BytesOfHasFieldsPrimitiveAligned {
        has_fields: HasFieldsPrimitive,
        padding: [u8; 8],
    }

    let wrap = |has_fields| BytesOfHasFieldsPrimitiveAligned { has_fields, padding: [0; 8] };

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(wrap(HasFieldsPrimitive::A(10)));
    imp::assert_eq!(
        <HasFieldsPrimitiveAligned as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFieldsPrimitiveAligned::A(10)),
    );

    let bytes: [u8; SIZE] = ::zerocopy::transmute!(wrap(HasFieldsPrimitive::B {
        foo: ::core::num::NonZeroU32::new(123456).unwrap()
    }));
    imp::assert_eq!(
        <HasFieldsPrimitiveAligned as imp::TryFromBytes>::try_read_from_bytes(&bytes[..]),
        imp::Ok(HasFieldsPrimitiveAligned::B {
            foo: ::core::num::NonZeroU32::new(123456).unwrap()
        }),
    );
}

#[derive(imp::TryFromBytes)]
#[repr(align(4), u32)]
enum HasReprAlignFirst {
    A,
    B,
}

util_assert_impl_all!(HasReprAlignFirst: imp::TryFromBytes);

#[derive(imp::KnownLayout, imp::TryFromBytes, imp::Immutable)]
#[repr(u8)]
enum Complex {
    UnitLike,
    StructLike { a: u8, b: u16 },
    TupleLike(bool, char),
}

util_assert_impl_all!(Complex: imp::TryFromBytes);

#[derive(imp::KnownLayout, imp::TryFromBytes, imp::Immutable)]
#[repr(u8)]
enum ComplexWithGenerics<X, Y> {
    UnitLike,
    StructLike { a: u8, b: X },
    TupleLike(bool, Y),
}

util_assert_impl_all!(ComplexWithGenerics<u16, char>: imp::TryFromBytes);

#[derive(imp::KnownLayout, imp::TryFromBytes, imp::Immutable)]
#[repr(C)]
enum GenericWithLifetimes<'a, 'b, X: 'a, Y: 'b> {
    Foo(::core::marker::PhantomData<&'a X>),
    Bar(::core::marker::PhantomData<&'b Y>),
}

#[derive(Clone, Copy, imp::TryFromBytes)]
struct A;

#[derive(imp::TryFromBytes)]
#[repr(C)]
enum B {
    A(A),
    A2 { a: A },
}
