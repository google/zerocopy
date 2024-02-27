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

#[derive(Eq, PartialEq, Debug, imp::NoCell, imp::KnownLayout, imp::TryFromBytes)]
#[repr(u8)]
enum Foo {
    A,
}

util_assert_impl_all!(Foo: imp::TryFromBytes);

#[test]
fn test_foo() {
    imp::assert_eq!(<Foo as imp::TryFromBytes>::try_read_from(&[0]), imp::Some(Foo::A));
    imp::assert_eq!(<Foo as imp::TryFromBytes>::try_read_from(&[]), imp::None);
    imp::assert_eq!(<Foo as imp::TryFromBytes>::try_read_from(&[1]), imp::None);
    imp::assert_eq!(<Foo as imp::TryFromBytes>::try_read_from(&[0, 0]), imp::None);
}

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::NoCell, imp::TryFromBytes)]
#[repr(u16)]
enum Bar {
    A = 0,
}

util_assert_impl_all!(Bar: imp::TryFromBytes);

#[test]
fn test_bar() {
    imp::assert_eq!(<Bar as imp::TryFromBytes>::try_read_from(&[0, 0]), imp::Some(Bar::A));
    imp::assert_eq!(<Bar as imp::TryFromBytes>::try_read_from(&[]), imp::None);
    imp::assert_eq!(<Bar as imp::TryFromBytes>::try_read_from(&[0]), imp::None);
    imp::assert_eq!(<Bar as imp::TryFromBytes>::try_read_from(&[0, 1]), imp::None);
    imp::assert_eq!(<Bar as imp::TryFromBytes>::try_read_from(&[0, 0, 0]), imp::None);
}

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::NoCell, imp::TryFromBytes)]
#[repr(u32)]
enum Baz {
    A = 1,
    B = 0,
}

util_assert_impl_all!(Baz: imp::TryFromBytes);

#[test]
fn test_baz() {
    imp::assert_eq!(
        <Baz as imp::TryFromBytes>::try_read_from(imp::IntoBytes::as_bytes(&1u32)),
        imp::Some(Baz::A)
    );
    imp::assert_eq!(
        <Baz as imp::TryFromBytes>::try_read_from(imp::IntoBytes::as_bytes(&0u32)),
        imp::Some(Baz::B)
    );
    imp::assert_eq!(<Baz as imp::TryFromBytes>::try_read_from(&[]), imp::None);
    imp::assert_eq!(<Baz as imp::TryFromBytes>::try_read_from(&[0]), imp::None);
    imp::assert_eq!(<Baz as imp::TryFromBytes>::try_read_from(&[0, 0]), imp::None);
    imp::assert_eq!(<Baz as imp::TryFromBytes>::try_read_from(&[0, 0, 0]), imp::None);
    imp::assert_eq!(<Baz as imp::TryFromBytes>::try_read_from(&[0, 0, 0, 0, 0]), imp::None);
}

// Test hygiene - make sure that `i8` being shadowed doesn't cause problems for
// the code emitted by the derive.
type i8 = bool;

const THREE: ::core::primitive::i8 = 3;

#[derive(Eq, PartialEq, Debug, imp::KnownLayout, imp::NoCell, imp::TryFromBytes)]
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
        <Blah as imp::TryFromBytes>::try_read_from(imp::IntoBytes::as_bytes(&1i8)),
        imp::Some(Blah::A)
    );
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from(imp::IntoBytes::as_bytes(&0i8)),
        imp::Some(Blah::B)
    );
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from(imp::IntoBytes::as_bytes(&3i8)),
        imp::Some(Blah::C)
    );
    imp::assert_eq!(
        <Blah as imp::TryFromBytes>::try_read_from(imp::IntoBytes::as_bytes(&6i8)),
        imp::Some(Blah::D)
    );
    imp::assert_eq!(<Blah as imp::TryFromBytes>::try_read_from(&[]), imp::None);
    imp::assert_eq!(<Blah as imp::TryFromBytes>::try_read_from(&[4]), imp::None);
    imp::assert_eq!(<Blah as imp::TryFromBytes>::try_read_from(&[0, 0]), imp::None);
}

#[derive(
    Eq, PartialEq, Debug, imp::KnownLayout, imp::NoCell, imp::TryFromBytes, imp::IntoBytes,
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
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from(&disc[..]),
        imp::Some(FieldlessButNotUnitOnly::A)
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(FieldlessButNotUnitOnly::B());
    imp::assert_eq!(
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from(&disc[..]),
        imp::Some(FieldlessButNotUnitOnly::B())
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(FieldlessButNotUnitOnly::C {});
    imp::assert_eq!(
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from(&disc[..]),
        imp::Some(FieldlessButNotUnitOnly::C {})
    );
    imp::assert_eq!(
        <FieldlessButNotUnitOnly as imp::TryFromBytes>::try_read_from(&[0xFF; SIZE][..]),
        imp::None
    );
}

#[derive(
    Eq, PartialEq, Debug, imp::KnownLayout, imp::NoCell, imp::TryFromBytes, imp::IntoBytes,
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
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from(&disc[..]),
        imp::Some(WeirdDiscriminants::A)
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(WeirdDiscriminants::B);
    imp::assert_eq!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from(&disc[..]),
        imp::Some(WeirdDiscriminants::B)
    );
    let disc: [u8; SIZE] = ::zerocopy::transmute!(WeirdDiscriminants::C);
    imp::assert_eq!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from(&disc[..]),
        imp::Some(WeirdDiscriminants::C)
    );
    imp::assert_eq!(
        <WeirdDiscriminants as imp::TryFromBytes>::try_read_from(&[0xFF; SIZE][..]),
        imp::None
    );
}
