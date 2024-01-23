// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(warnings)]

use std::convert::TryFrom;

use syn::Field;

mod util;

use {
    static_assertions::assert_impl_all,
    zerocopy::{IntoBytes, KnownLayout, TryFromBytes},
};

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum Foo {
    A,
}

assert_impl_all!(Foo: TryFromBytes);

#[test]
fn test_foo() {
    assert_eq!(Foo::try_read_from(&[0]), Some(Foo::A));
    assert_eq!(Foo::try_read_from(&[]), None);
    assert_eq!(Foo::try_read_from(&[1]), None);
    assert_eq!(Foo::try_read_from(&[0, 0]), None);
}

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes)]
#[repr(u16)]
enum Bar {
    A = 0,
}

assert_impl_all!(Bar: TryFromBytes);

#[test]
fn test_bar() {
    assert_eq!(Bar::try_read_from(&[0, 0]), Some(Bar::A));
    assert_eq!(Bar::try_read_from(&[]), None);
    assert_eq!(Bar::try_read_from(&[0]), None);
    assert_eq!(Bar::try_read_from(&[0, 1]), None);
    assert_eq!(Bar::try_read_from(&[0, 0, 0]), None);
}

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes)]
#[repr(u32)]
enum Baz {
    A = 1,
    B = 0,
}

assert_impl_all!(Baz: TryFromBytes);

#[test]
fn test_baz() {
    assert_eq!(Baz::try_read_from(1u32.as_bytes()), Some(Baz::A));
    assert_eq!(Baz::try_read_from(0u32.as_bytes()), Some(Baz::B));
    assert_eq!(Baz::try_read_from(&[]), None);
    assert_eq!(Baz::try_read_from(&[0]), None);
    assert_eq!(Baz::try_read_from(&[0, 0]), None);
    assert_eq!(Baz::try_read_from(&[0, 0, 0]), None);
    assert_eq!(Baz::try_read_from(&[0, 0, 0, 0, 0]), None);
}

// Test hygiene - make sure that `i8` being shadowed doesn't cause problems for
// the code emitted by the derive.
type i8 = bool;

const THREE: core::primitive::i8 = 3;

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes)]
#[repr(i8)]
enum Blah {
    A = 1,
    B = 0,
    C = 1 + 2,
    D = 3 + THREE,
}

assert_impl_all!(Blah: TryFromBytes);

#[test]
fn test_blah() {
    assert_eq!(Blah::try_read_from(1i8.as_bytes()), Some(Blah::A));
    assert_eq!(Blah::try_read_from(0i8.as_bytes()), Some(Blah::B));
    assert_eq!(Blah::try_read_from(3i8.as_bytes()), Some(Blah::C));
    assert_eq!(Blah::try_read_from(6i8.as_bytes()), Some(Blah::D));
    assert_eq!(Blah::try_read_from(&[]), None);
    assert_eq!(Blah::try_read_from(&[4]), None);
    assert_eq!(Blah::try_read_from(&[0, 0]), None);
}

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes, IntoBytes)]
#[repr(C)]
enum FieldlessButNotUnitOnly {
    A,
    B(),
    C {},
}

#[test]
fn test_fieldless_but_not_unit_only() {
    const SIZE: usize = core::mem::size_of::<FieldlessButNotUnitOnly>();
    let disc: [u8; SIZE] = zerocopy::transmute!(FieldlessButNotUnitOnly::A);
    assert_eq!(FieldlessButNotUnitOnly::try_read_from(&disc[..]), Some(FieldlessButNotUnitOnly::A));
    let disc: [u8; SIZE] = zerocopy::transmute!(FieldlessButNotUnitOnly::B());
    assert_eq!(
        FieldlessButNotUnitOnly::try_read_from(&disc[..]),
        Some(FieldlessButNotUnitOnly::B())
    );
    let disc: [u8; SIZE] = zerocopy::transmute!(FieldlessButNotUnitOnly::C {});
    assert_eq!(
        FieldlessButNotUnitOnly::try_read_from(&disc[..]),
        Some(FieldlessButNotUnitOnly::C {})
    );
    assert_eq!(FieldlessButNotUnitOnly::try_read_from(&[0xFF; SIZE][..]), None);
}

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes, IntoBytes)]
#[repr(C)]
enum WeirdDiscriminants {
    A = -7,
    B,
    C = 33,
}

#[test]
fn test_weird_discriminants() {
    const SIZE: usize = core::mem::size_of::<WeirdDiscriminants>();
    let disc: [u8; SIZE] = zerocopy::transmute!(WeirdDiscriminants::A);
    assert_eq!(WeirdDiscriminants::try_read_from(&disc[..]), Some(WeirdDiscriminants::A));
    let disc: [u8; SIZE] = zerocopy::transmute!(WeirdDiscriminants::B);
    assert_eq!(WeirdDiscriminants::try_read_from(&disc[..]), Some(WeirdDiscriminants::B));
    let disc: [u8; SIZE] = zerocopy::transmute!(WeirdDiscriminants::C);
    assert_eq!(WeirdDiscriminants::try_read_from(&disc[..]), Some(WeirdDiscriminants::C));
    assert_eq!(WeirdDiscriminants::try_read_from(&[0xFF; SIZE][..]), None);
}
