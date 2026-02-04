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

// `derive(Unaligned)` fails without a repr.
#[derive(imp::FromBytes, imp::IntoBytes, imp::Unaligned)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
struct Foo {
    a: u8,
}

util_assert_impl_all!(Foo: imp::FromBytes, imp::IntoBytes);
util_assert_not_impl_any!(Foo: imp::Unaligned);

// Invalid enum for FromZeros (must have discriminant 0).
#[derive(imp::FromZeros)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum BadFromZerosEnum {
    A = 1,
    B = 2,
}

util_assert_not_impl_any!(BadFromZerosEnum: imp::FromZeros);

// Invalid enum for FromBytes (must have 256 variants).
#[derive(imp::FromBytes)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum BadFromBytesEnum {
    A = 0,
}

util_assert_not_impl_any!(BadFromBytesEnum: imp::FromBytes);

// Invalid enum for IntoBytes (invalid repr).
#[derive(imp::IntoBytes)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(Rust)]
enum BadIntoBytesEnum {
    A,
}

util_assert_not_impl_any!(BadIntoBytesEnum: imp::IntoBytes);

// Invalid enum for Unaligned (invalid repr).
#[derive(imp::Unaligned)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u16)]
enum BadUnalignedEnum {
    A,
}

util_assert_not_impl_any!(BadUnalignedEnum: imp::Unaligned);

// Invalid enum for TryFromBytes (invalid repr).
#[derive(imp::TryFromBytes)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(Rust)]
enum BadTryFromBytesEnum {
    A,
}

util_assert_not_impl_any!(BadTryFromBytesEnum: imp::TryFromBytes);

// Invalid union for IntoBytes (invalid repr).
#[derive(imp::IntoBytes)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(Rust)]
union BadIntoBytesUnion {
    a: u8,
}

util_assert_not_impl_any!(BadIntoBytesUnion: imp::IntoBytes);

// Invalid union for Unaligned (invalid repr).
#[derive(imp::Unaligned)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(Rust)]
union BadUnalignedUnion {
    a: u8,
}

util_assert_not_impl_any!(BadUnalignedUnion: imp::Unaligned);

// Invalid union for IntoBytes (generic).
#[derive(imp::IntoBytes)]
#[zerocopy(derive_fail_silently)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
union BadIntoBytesUnionGeneric<T: imp::Copy> {
    a: T,
}

util_assert_not_impl_any!(BadIntoBytesUnionGeneric<u8>: imp::IntoBytes);
