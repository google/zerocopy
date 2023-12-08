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
    zerocopy::{FromBytes, FromZeros, TryFromBytes},
};

use crate::util::AU16;

// A struct is `TryFromBytes` if:
// - all fields are `TryFromBytes`

#[derive(TryFromBytes, FromZeros, FromBytes)]
struct Zst;

assert_impl_all!(Zst: TryFromBytes);

#[test]
fn zst() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&Zst);
    let candidate = candidate.forget_aligned().forget_valid();
    let is_bit_valid = Zst::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(TryFromBytes, FromZeros, FromBytes)]
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
struct Two {
    a: bool,
    b: Zst,
}

assert_impl_all!(Two: TryFromBytes);

#[test]
fn two() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&Two { a: false, b: Zst });
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
    // - The alignment of `Unsized` is equal to the alignment of `[u8]`.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut Two) };

    // SAFETY: `candidate`'s referent is as-initialized as `Two`.
    let candidate = unsafe { candidate.assume_as_initialized() };

    let is_bit_valid = Two::is_bit_valid(candidate);
    assert!(!is_bit_valid);
}

#[derive(TryFromBytes, FromZeros, FromBytes)]
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
struct WithParams<'a: 'b, 'b: 'a, const N: usize, T: 'a + 'b + TryFromBytes>(
    PhantomData<&'a &'b ()>,
    [T],
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + TryFromBytes;

assert_impl_all!(WithParams<'static, 'static, 42, u8>: TryFromBytes);
