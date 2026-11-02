// Copyright 2026 The Fuchsia Authors
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

// A struct is `HasNullPointerOptimization` if:
// - it is `repr(transparent)`, and
// - it has exactly one field, which is `HasNullPointerOptimization`
//
// `Option` of such a struct is always `TryFromBytes` and `FromZeros`. It is
// `FromBytes` if the struct wraps a `NonZeroXxx`, and `IntoBytes` or
// `Unaligned` if the struct is.

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct Ref<'a> {
    a: &'a u8,
}

util_assert_impl_all!(Ref<'static>: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<Ref<'static>>: imp::TryFromBytes, imp::FromZeros);
util_assert_not_impl_any!(imp::Option<Ref<'static>>: imp::FromBytes, imp::IntoBytes, imp::Unaligned);

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct RefMut<'a>(&'a mut util::NotZerocopy);

util_assert_impl_all!(RefMut<'static>: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<RefMut<'static>>: imp::TryFromBytes, imp::FromZeros);

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct NonNullPtr(::core::ptr::NonNull<imp::UnsafeCell<u8>>);

util_assert_impl_all!(NonNullPtr: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<NonNullPtr>: imp::TryFromBytes, imp::FromZeros);

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct FnPtr(fn(u8) -> u16);

util_assert_impl_all!(FnPtr: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<FnPtr>: imp::TryFromBytes, imp::FromZeros);
util_assert_not_impl_any!(imp::Option<FnPtr>: imp::FromBytes, imp::IntoBytes, imp::Unaligned);

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct UnsafeExternCFnPtr(unsafe extern "C" fn());

util_assert_impl_all!(UnsafeExternCFnPtr: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<UnsafeExternCFnPtr>: imp::TryFromBytes, imp::FromZeros);

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct NonZero(::core::num::NonZeroU32);

util_assert_impl_all!(NonZero: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<NonZero>: imp::TryFromBytes, imp::FromZeros, imp::FromBytes);
// `NonZero` doesn't derive `IntoBytes` or `Unaligned`.
util_assert_not_impl_any!(imp::Option<NonZero>: imp::IntoBytes, imp::Unaligned);

#[derive(imp::HasNullPointerOptimization, imp::IntoBytes, imp::Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct UserId(::core::num::NonZeroU32);

util_assert_impl_all!(UserId: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<UserId>:
    imp::TryFromBytes,
    imp::FromZeros,
    imp::FromBytes,
    imp::IntoBytes,
    imp::Immutable,
);
util_assert_not_impl_any!(imp::Option<UserId>: imp::Unaligned);

#[derive(imp::HasNullPointerOptimization, imp::IntoBytes, imp::Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct NonZeroSigned {
    a: ::core::num::NonZeroI8,
}

util_assert_impl_all!(NonZeroSigned: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<NonZeroSigned>:
    imp::TryFromBytes,
    imp::FromZeros,
    imp::FromBytes,
    imp::IntoBytes,
    imp::Unaligned,
);

// The null pointer optimization is preserved through nested
// `repr(transparent)` structs.

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct Nested<'a>(Ref<'a>);

util_assert_impl_all!(Nested<'static>: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<Nested<'static>>: imp::TryFromBytes, imp::FromZeros);

// Deriving `HasNullPointerOptimization` on a generic struct makes it
// `HasNullPointerOptimization` only when its field is.

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct Generic<T>(T);

util_assert_impl_all!(Generic<&'static u8>: imp::HasNullPointerOptimization);
util_assert_impl_all!(Generic<Generic<&'static u8>>: imp::HasNullPointerOptimization);
util_assert_impl_all!(Generic<::core::num::NonZeroU64>: imp::HasNullPointerOptimization);
util_assert_impl_all!(imp::Option<Generic<::core::num::NonZeroU64>>: imp::FromBytes);
util_assert_impl_all!(imp::Option<Generic<Generic<NonZero>>>: imp::FromBytes);
util_assert_not_impl_any!(imp::Option<Generic<&'static u8>>: imp::FromBytes);
util_assert_not_impl_any!(Generic<u8>: imp::HasNullPointerOptimization);
util_assert_not_impl_any!(Generic<&'static [u8]>: imp::HasNullPointerOptimization);
util_assert_not_impl_any!(Generic<*const u8>: imp::HasNullPointerOptimization);
util_assert_not_impl_any!(Generic<imp::Option<&'static u8>>: imp::HasNullPointerOptimization);
util_assert_not_impl_any!(imp::Option<Generic<u8>>: imp::FromZeros);
util_assert_not_impl_any!(imp::Option<Generic<&'static [u8]>>: imp::FromZeros);

// Deriving `HasNullPointerOptimization` should work if the struct has bounded
// parameters.

#[derive(imp::HasNullPointerOptimization)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(transparent)]
struct WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::Copy, const N: usize>(&'a &'b [T; N])
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::Copy;

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::HasNullPointerOptimization);

#[test]
fn test_new_zeroed_is_none() {
    imp::assert!(<imp::Option<Ref<'static>> as imp::FromZeros>::new_zeroed().is_none());
    imp::assert!(<imp::Option<Nested<'static>> as imp::FromZeros>::new_zeroed().is_none());
    imp::assert!(<imp::Option<Generic<FnPtr>> as imp::FromZeros>::new_zeroed().is_none());

    let x = 0u8;
    let mut opt = imp::Some(Nested(Ref { a: &x }));
    imp::FromZeros::zero(&mut opt);
    imp::assert!(opt.is_none());
}

#[test]
fn test_try_from_bytes_accepts_only_zeros() {
    let zeros = [0u8; ::core::mem::size_of::<Nested<'static>>()];
    let res = <imp::Option<Nested<'static>> as imp::TryFromBytes>::try_read_from_bytes(&zeros[..]);
    imp::assert!(imp::matches!(res, imp::Ok(imp::None)));

    let mut nonzero = [0u8; ::core::mem::size_of::<Nested<'static>>()];
    nonzero[0] = 1;
    let res =
        <imp::Option<Nested<'static>> as imp::TryFromBytes>::try_read_from_bytes(&nonzero[..]);
    imp::assert!(res.is_err());
}

#[test]
fn test_try_from_bytes_nonzero_accepts_all_bit_patterns() {
    // Every non-zero bit pattern is a valid `NonZeroU32`, so every bit pattern
    // is a valid `Option<NonZero>`, including through nested and generic
    // `repr(transparent)` structs.
    let res = <imp::Option<NonZero> as imp::TryFromBytes>::try_read_from_bytes(&[0u8; 4][..]);
    imp::assert!(imp::matches!(res, imp::Ok(imp::None)));

    let res = <imp::Option<NonZero> as imp::TryFromBytes>::try_read_from_bytes(&[0xFF; 4][..]);
    imp::assert_eq!(res.ok().map(|o| o.map(|n| n.0.get())), imp::Some(imp::Some(u32::MAX)));

    let res =
        <imp::Option<Generic<NonZero>> as imp::TryFromBytes>::try_read_from_bytes(&[0xFF; 4][..]);
    imp::assert_eq!(res.ok().map(|o| o.map(|n| (n.0).0.get())), imp::Some(imp::Some(u32::MAX)));

    let res = <imp::Option<NonZeroSigned> as imp::TryFromBytes>::try_read_from_bytes(&[0x80][..]);
    imp::assert_eq!(res.ok().map(|o| o.map(|n| n.a.get())), imp::Some(imp::Some(i8::MIN)));

    imp::assert!(<imp::Option<NonZero> as imp::FromZeros>::new_zeroed().is_none());
}

#[test]
fn test_from_bytes_into_bytes_round_trip() {
    let id = <imp::Option<UserId> as imp::FromBytes>::read_from_bytes(&[0xFF; 4][..]);
    let id = id.ok().flatten();
    imp::assert_eq!(id.as_ref().map(|id| id.0.get()), imp::Some(u32::MAX));
    imp::assert_eq!(imp::IntoBytes::as_bytes(&id), [0xFF; 4]);

    let none = <imp::Option<UserId> as imp::FromZeros>::new_zeroed();
    imp::assert_eq!(imp::IntoBytes::as_bytes(&none), [0; 4]);

    let mut bytes = [0x80u8];
    {
        let opt = <imp::Option<NonZeroSigned> as imp::FromBytes>::mut_from_bytes(&mut bytes[..]);
        let opt = opt.ok().unwrap();
        imp::assert_eq!(opt.as_ref().map(|n| n.a.get()), imp::Some(i8::MIN));
        *opt = imp::None;
    }
    imp::assert_eq!(bytes, [0]);
}
