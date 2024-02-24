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

// A struct is `imp::TryFromBytes` if:
// - any of its fields are `imp::TryFromBytes`

#[derive(imp::NoCell, imp::FromBytes)]
union One {
    a: u8,
}

util_assert_impl_all!(One: imp::TryFromBytes);

#[test]
fn one() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&One { a: 42 });
    let candidate = candidate.forget_aligned();
    // SAFETY: `&One` consists entirely of initialized bytes.
    let candidate = unsafe { candidate.assume_initialized() };
    let is_bit_valid = <One as imp::TryFromBytes>::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(imp::NoCell, imp::FromZeros)]
#[repr(C)]
union Two {
    a: bool,
    b: bool,
}

util_assert_impl_all!(Two: imp::TryFromBytes);

#[test]
fn two() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate_a = ::zerocopy::Ptr::from_ref(&Two { a: false });
    let candidate_a = candidate_a.forget_aligned();
    // SAFETY: `&Two` consists entirely of initialized bytes.
    let candidate_a = unsafe { candidate_a.assume_initialized() };
    let is_bit_valid = <Two as imp::TryFromBytes>::is_bit_valid(candidate_a);
    assert!(is_bit_valid);

    let candidate_b = ::zerocopy::Ptr::from_ref(&Two { b: true });
    let candidate_b = candidate_b.forget_aligned();
    // SAFETY: `&Two` consists entirely of initialized bytes.
    let candidate_b = unsafe { candidate_b.assume_initialized() };
    let is_bit_valid = <Two as imp::TryFromBytes>::is_bit_valid(candidate_b);
    assert!(is_bit_valid);
}

#[test]
fn two_bad() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&[2u8][..]);
    let candidate = candidate.forget_aligned();
    // SAFETY: `&[u8]` consists entirely of initialized bytes.
    let candidate = unsafe { candidate.assume_initialized() };

    // SAFETY:
    // - The cast `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
    //   *mut U`.
    // - The size of the object referenced by the resulting pointer is equal to
    //   the size of the object referenced by `self`.
    // - `Two` does not contain any `UnsafeCell`s.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut Two) };

    // SAFETY: `candidate`'s referent is as-initialized as `Two`.
    let candidate = unsafe { candidate.assume_initialized() };

    let is_bit_valid = <Two as imp::TryFromBytes>::is_bit_valid(candidate);
    assert!(!is_bit_valid);
}

#[derive(imp::NoCell, imp::FromZeros)]
#[repr(C)]
union BoolAndZst {
    a: bool,
    b: (),
}

#[test]
fn bool_and_zst() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&[2u8][..]);
    let candidate = candidate.forget_aligned();
    // SAFETY: `&[u8]` consists entirely of initialized bytes.
    let candidate = unsafe { candidate.assume_initialized() };

    // SAFETY:
    // - The cast `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
    //   *mut U`.
    // - The size of the object referenced by the resulting pointer is equal to
    //   the size of the object referenced by `self`.
    // - `BoolAndZst` does not contain any `UnsafeCell`s.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut BoolAndZst) };

    // SAFETY: `candidate`'s referent is fully initialized.
    let candidate = unsafe { candidate.assume_initialized() };

    let is_bit_valid = <BoolAndZst as imp::TryFromBytes>::is_bit_valid(candidate);
    assert!(is_bit_valid);
}

#[derive(imp::NoCell, imp::FromBytes)]
#[repr(C)]
union TypeParams<'a, T: imp::Copy, I: imp::Iterator>
where
    I::Item: imp::Copy,
{
    a: I::Item,
    b: u8,
    c: imp::PhantomData<&'a [u8]>,
    d: imp::PhantomData<&'static str>,
    e: imp::PhantomData<imp::String>,
    f: T,
}

util_assert_impl_all!(TypeParams<'static, (), imp::IntoIter<()>>: imp::TryFromBytes);
util_assert_impl_all!(TypeParams<'static, util::AU16, imp::IntoIter<()>>: imp::TryFromBytes);
util_assert_impl_all!(TypeParams<'static, [util::AU16; 2], imp::IntoIter<()>>: imp::TryFromBytes);

// Deriving `imp::TryFromBytes` should work if the union has bounded parameters.

#[derive(imp::NoCell, imp::FromBytes)]
#[repr(C)]
union WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::TryFromBytes, const N: usize>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::TryFromBytes + imp::Copy,
{
    a: imp::PhantomData<&'a &'b ()>,
    b: T,
}

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::TryFromBytes);
