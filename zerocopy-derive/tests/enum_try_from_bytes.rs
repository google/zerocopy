// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(warnings)]

use std::convert::TryFrom;

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
    assert_eq!(Foo::try_from_ref(&[0]), Some(&Foo::A));
    assert_eq!(Foo::try_from_ref(&[]), None);
    assert_eq!(Foo::try_from_ref(&[1]), None);
    assert_eq!(Foo::try_from_ref(&[0, 0]), None);
}

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes)]
#[repr(u16)]
enum Bar {
    A = 0,
}

assert_impl_all!(Bar: TryFromBytes);

#[test]
fn test_bar() {
    assert_eq!(Bar::try_from_ref(&[0, 0]), Some(&Bar::A));
    assert_eq!(Bar::try_from_ref(&[]), None);
    assert_eq!(Bar::try_from_ref(&[0]), None);
    assert_eq!(Bar::try_from_ref(&[0, 1]), None);
    assert_eq!(Bar::try_from_ref(&[0, 0, 0]), None);
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
    assert_eq!(Baz::try_from_ref(1u32.as_bytes()), Some(&Baz::A));
    assert_eq!(Baz::try_from_ref(0u32.as_bytes()), Some(&Baz::B));
    assert_eq!(Baz::try_from_ref(&[]), None);
    assert_eq!(Baz::try_from_ref(&[0]), None);
    assert_eq!(Baz::try_from_ref(&[0, 0]), None);
    assert_eq!(Baz::try_from_ref(&[0, 0, 0]), None);
    assert_eq!(Baz::try_from_ref(&[0, 0, 0, 0, 0]), None);
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
    assert_eq!(Blah::try_from_ref(1i8.as_bytes()), Some(&Blah::A));
    assert_eq!(Blah::try_from_ref(0i8.as_bytes()), Some(&Blah::B));
    assert_eq!(Blah::try_from_ref(3i8.as_bytes()), Some(&Blah::C));
    assert_eq!(Blah::try_from_ref(6i8.as_bytes()), Some(&Blah::D));
    assert_eq!(Blah::try_from_ref(&[]), None);
    assert_eq!(Blah::try_from_ref(&[4]), None);
    assert_eq!(Blah::try_from_ref(&[0, 0]), None);
}

#[derive(Eq, PartialEq, Debug, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum FieldlessButNotUnitOnly {
    A,
    B(),
    C {},
}

#[test]
fn test_fieldless_but_not_unit_only() {
    assert_eq!(
        FieldlessButNotUnitOnly::try_from_ref(0u8.as_bytes()),
        Some(&FieldlessButNotUnitOnly::A)
    );
    assert_eq!(
        FieldlessButNotUnitOnly::try_from_ref(1u8.as_bytes()),
        Some(&FieldlessButNotUnitOnly::B())
    );
    assert_eq!(
        FieldlessButNotUnitOnly::try_from_ref(2u8.as_bytes()),
        Some(&FieldlessButNotUnitOnly::C {})
    );
    assert_eq!(FieldlessButNotUnitOnly::try_from_ref(&[]), None);
    assert_eq!(FieldlessButNotUnitOnly::try_from_ref(&[3]), None);
    assert_eq!(FieldlessButNotUnitOnly::try_from_ref(&[0, 0]), None);
}
