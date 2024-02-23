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
// - all fields are `imp::TryFromBytes`

#[test]
fn zst() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&());
    let candidate = candidate.forget_aligned();
    // SAFETY: `&()` trivially consists entirely of initialized bytes.
    let candidate = unsafe { candidate.assume_initialized() };
    let is_bit_valid = <() as imp::TryFromBytes>::is_bit_valid(candidate);
    imp::assert!(is_bit_valid);
}

#[derive(imp::FromBytes)]
#[repr(C)]
struct One {
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
    imp::assert!(is_bit_valid);
}

#[derive(imp::FromZeros)]
#[repr(C)]
struct Two {
    a: bool,
    b: (),
}

util_assert_impl_all!(Two: imp::TryFromBytes);

#[test]
fn two() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&Two { a: false, b: () });
    let candidate = candidate.forget_aligned();
    // SAFETY: `&Two` consists entirely of initialized bytes.
    let candidate = unsafe { candidate.assume_initialized() };
    let is_bit_valid = <Two as imp::TryFromBytes>::is_bit_valid(candidate);
    imp::assert!(is_bit_valid);
}

#[test]
fn two_bad() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&[2u8][..]);
    let candidate = candidate.forget_aligned();
    // SAFETY: `&Two` consists entirely of initialized bytes.
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
    imp::assert!(!is_bit_valid);
}

#[derive(imp::FromBytes)]
#[repr(C)]
struct Unsized {
    a: [u8],
}

util_assert_impl_all!(Unsized: imp::TryFromBytes);

#[test]
fn un_sized() {
    // TODO(#5): Use `try_transmute` in this test once it's available.
    let candidate = ::zerocopy::Ptr::from_ref(&[16, 12, 42][..]);
    let candidate = candidate.forget_aligned();
    // SAFETY: `&Unsized` consists entirely of initialized bytes.
    let candidate = unsafe { candidate.assume_initialized() };

    // SAFETY:
    // - The cast `cast(p)` is implemented exactly as follows: `|p: *mut T| p as
    //   *mut U`.
    // - The size of the object referenced by the resulting pointer is equal to
    //   the size of the object referenced by `self`.
    // - The alignment of `Unsized` is equal to the alignment of `[u8]`.
    // - `Unsized` does not contain any `UnsafeCell`s.
    let candidate = unsafe { candidate.cast_unsized(|p| p as *mut Unsized) };

    // SAFETY: `candidate`'s referent is as-initialized as `Two`.
    let candidate = unsafe { candidate.assume_initialized() };
    let is_bit_valid = <Unsized as imp::TryFromBytes>::is_bit_valid(candidate);
    imp::assert!(is_bit_valid);
}

#[derive(imp::FromBytes)]
#[repr(C)]
struct TypeParams<'a, T: ?imp::Sized, I: imp::Iterator> {
    a: I::Item,
    b: u8,
    c: imp::PhantomData<&'a [u8]>,
    d: imp::PhantomData<&'static str>,
    e: imp::PhantomData<imp::String>,
    f: T,
}

util_assert_impl_all!(TypeParams<'static, (), imp::IntoIter<()>>: imp::TryFromBytes);
util_assert_impl_all!(TypeParams<'static, util::AU16, imp::IntoIter<()>>: imp::TryFromBytes);
util_assert_impl_all!(TypeParams<'static, [util::AU16], imp::IntoIter<()>>: imp::TryFromBytes);

// Deriving `imp::TryFromBytes` should work if the struct has bounded parameters.

#[derive(imp::FromBytes)]
#[repr(transparent)]
struct WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::TryFromBytes, const N: usize>(
    imp::PhantomData<&'a &'b ()>,
    [T],
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::TryFromBytes;

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::TryFromBytes);

#[derive(Debug, PartialEq, Eq, imp::TryFromBytes, imp::NoCell, imp::KnownLayout)]
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
    let converted = <CPacked as imp::TryFromBytes>::try_from_ref(candidate);
    imp::assert_eq!(converted, imp::Some(&CPacked { a: 42, b: u32::MAX }));
}

#[derive(imp::TryFromBytes, imp::KnownLayout, imp::NoCell)]
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
    let converted = <CPackedUnsized as imp::TryFromBytes>::try_from_ref(candidate);
    imp::assert!(converted.is_some());
}

#[derive(imp::TryFromBytes)]
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
    let converted = <CPackedUnsized as imp::TryFromBytes>::try_from_ref(candidate);
    imp::assert!(converted.is_some());

    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = <CPackedUnsized as imp::TryFromBytes>::try_from_ref(candidate);
    imp::assert!(converted.is_none());

    let candidate = &[42u8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    let converted = <CPackedUnsized as imp::TryFromBytes>::try_from_ref(candidate);
    imp::assert!(converted.is_some());
}
