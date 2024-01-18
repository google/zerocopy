// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(warnings)]

mod util;

use std::{marker::PhantomData, option::IntoIter};

use {
    static_assertions::assert_impl_all,
    zerocopy::{FromBytes, FromZeros, KnownLayout, TryFromBytes},
};

use crate::util::AU16;

// A struct is `TryFromBytes` if:
// - all fields are `TryFromBytes`

#[test]
fn zst() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&());
    let candidate = candidate.forget_aligned().forget_valid();
    let is_bit_valid = <()>::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(TryFromBytes, FromZeros, FromBytes)]
#[repr(C)]
struct One {
    a: u8,
}

assert_impl_all!(One: TryFromBytes);

#[test]
fn one() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&One { a: 42 });
    let candidate = candidate.forget_aligned().forget_valid();
    let is_bit_valid = One::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(TryFromBytes, FromZeros)]
#[repr(C)]
struct Two {
    a: bool,
    b: (),
}

assert_impl_all!(Two: TryFromBytes);

#[test]
fn two() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&Two { a: false, b: () });
    let candidate = candidate.forget_aligned().forget_valid();
    let is_bit_valid = Two::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[test]
fn two_bad() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&[2u8][..]);
    let candidate = candidate.forget_aligned().forget_valid();

    // SAFETY:
    // - The cast `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
    //   *mut U`.
    // - The size of the object referenced by the resulting pointer is equal to
    //   the size of the object referenced by `self`.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut Two) };

    // SAFETY: `candidate`'s referent is as-initialized as `Two`.
    let candidate = unsafe { candidate.assume_as_initialized() };

    let is_bit_valid = Two::is_bit_valid(candidate);
    assert!(!is_bit_valid);
}

#[derive(TryFromBytes, FromZeros, FromBytes)]
#[repr(C)]
struct Unsized {
    a: [u8],
}

assert_impl_all!(Unsized: TryFromBytes);

#[test]
fn un_sized() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&[16, 12, 42][..]);
    let candidate = candidate.forget_aligned().forget_valid();

    // SAFETY:
    // - The cast `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
    //   *mut U`.
    // - The size of the object referenced by the resulting pointer is equal to
    //   the size of the object referenced by `self`.
    // - The alignment of `Unsized` is equal to the alignment of `[u8]`.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut Unsized) };

    // SAFETY: `candidate`'s referent is as-initialized as `Two`.
    let candidate = unsafe { candidate.assume_as_initialized() };
    let is_bit_valid = Unsized::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(TryFromBytes, FromZeros, FromBytes)]
#[repr(C)]
struct TypeParams<'a, T: ?Sized, I: Iterator> {
    a: I::Item,
    b: u8,
    c: PhantomData<&'a [u8]>,
    d: PhantomData<&'static str>,
    e: PhantomData<String>,
    f: T,
}

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: TryFromBytes);
assert_impl_all!(TypeParams<'static, AU16, IntoIter<()>>: TryFromBytes);
assert_impl_all!(TypeParams<'static, [AU16], IntoIter<()>>: TryFromBytes);

// Deriving `TryFromBytes` should work if the struct has bounded parameters.

#[derive(TryFromBytes, FromZeros, FromBytes)]
#[repr(transparent)]
struct WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + TryFromBytes, const N: usize>(
    PhantomData<&'a &'b ()>,
    [T],
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + TryFromBytes;

assert_impl_all!(WithParams<'static, 'static, u8, 42>: TryFromBytes);

#[derive(Debug, PartialEq, Eq, TryFromBytes, KnownLayout)]
#[repr(C, packed)]
struct CPacked {
    a: u8,
    // NOTE: The `u32` type is not guaranteed to have alignment 4, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(4))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u32` here. Luckily, these tests run in CI on
    // platforms on which `u32` has alignment 4, so this isn't that big of a
    // deal.
    b: u32,
}

#[test]
fn c_packed() {
    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = CPacked::try_from_ref(candidate);
    assert_eq!(converted, Some(&CPacked { a: 42, b: u32::MAX }));
}

#[derive(TryFromBytes, KnownLayout)]
#[repr(C, packed)]
struct CPackedUnsized {
    a: u8,
    // NOTE: The `u32` type is not guaranteed to have alignment 4, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(4))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u32` here. Luckily, these tests run in CI on
    // platforms on which `u32` has alignment 4, so this isn't that big of a
    // deal.
    b: [u32],
}

#[test]
fn c_packed_unsized() {
    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = CPackedUnsized::try_from_ref(candidate);
    assert!(converted.is_some());
}

#[derive(TryFromBytes)]
#[repr(packed)]
struct PackedUnsized {
    a: u8,
    // NOTE: The `u32` type is not guaranteed to have alignment 4, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(4))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u32` here. Luckily, these tests run in CI on
    // platforms on which `u32` has alignment 4, so this isn't that big of a
    // deal.
    b: [u32],
}

#[test]
fn packed_unsized() {
    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = CPackedUnsized::try_from_ref(candidate);
    assert!(converted.is_some());

    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = CPackedUnsized::try_from_ref(candidate);
    assert!(converted.is_none());

    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = CPackedUnsized::try_from_ref(candidate);
    assert!(converted.is_some());
}
