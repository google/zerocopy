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
// - any of its fields are `TryFromBytes`

#[derive(TryFromBytes, FromZeros, FromBytes)]
union One {
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
union Two {
    a: bool,
    b: bool,
}

assert_impl_all!(Two: TryFromBytes);

#[test]
fn two() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate_a = zerocopy::Ptr::from_ref(&Two { a: false });
    let candidate_a = candidate_a.forget_aligned().forget_valid();
    let is_bit_valid = Two::is_bit_valid(candidate_a);
    assert!(is_bit_valid);

    let candidate_b = zerocopy::Ptr::from_ref(&Two { b: true });
    let candidate_b = candidate_b.forget_aligned().forget_valid();
    let is_bit_valid = Two::is_bit_valid(candidate_b);
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

#[derive(TryFromBytes, FromZeros)]
#[repr(C)]
union BoolAndZst {
    a: bool,
    b: (),
}

#[test]
fn bool_and_zst() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = zerocopy::Ptr::from_ref(&[2u8][..]);
    let candidate = candidate.forget_aligned().forget_valid();

    // SAFETY:
    // - The cast `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
    //   *mut U`.
    // - The size of the object referenced by the resulting pointer is equal to
    //   the size of the object referenced by `self`.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut BoolAndZst) };

    // SAFETY: `candidate`'s referent is as-initialized as `BoolAndZst`.
    let candidate = unsafe { candidate.assume_as_initialized() };

    let is_bit_valid = BoolAndZst::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(TryFromBytes, FromZeros, FromBytes)]
#[repr(C)]
union TypeParams<'a, T: Copy, I: Iterator>
where
    I::Item: Copy,
{
    a: I::Item,
    b: u8,
    c: PhantomData<&'a [u8]>,
    d: PhantomData<&'static str>,
    e: PhantomData<String>,
    f: T,
}

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: TryFromBytes);
assert_impl_all!(TypeParams<'static, AU16, IntoIter<()>>: TryFromBytes);
assert_impl_all!(TypeParams<'static, [AU16; 2], IntoIter<()>>: TryFromBytes);

// Deriving `TryFromBytes` should work if the union has bounded parameters.

#[derive(TryFromBytes, FromZeros, FromBytes)]
#[repr(C)]
union WithParams<'a: 'b, 'b: 'a, const N: usize, T: 'a + 'b + TryFromBytes>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + TryFromBytes + Copy,
{
    a: PhantomData<&'a &'b ()>,
    b: T,
}

assert_impl_all!(WithParams<'static, 'static, 42, u8>: TryFromBytes);
