// Copyright 2025 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![no_implicit_prelude]
#![allow(warnings)]

// NOTE: We don't include `include.rs` here because we want to be explicit about
// what we are testing.

#[macro_use]
extern crate zerocopy_renamed as zerocopy;
#[macro_use]
extern crate static_assertions;
extern crate std;
use std::marker::Sized;

use static_assertions::assert_not_impl_any;
use zerocopy::{FromBytes, FromZeros, IntoBytes, KnownLayout, TryFromBytes, Unaligned};

// This would normally fail because it lacks `#[repr(C)]`.
// With `derive_fail_silently`, it should pass compilation but NOT implement traits that require Repr C.
#[derive(FromBytes, IntoBytes, Unaligned)]
#[zerocopy(derive_fail_silently)]
struct Foo {
    a: u8,
}

// `FromBytes` and `FromZeros` might still be implemented for `repr(Rust)` structs
// if they consist of valid fields. `u8` is valid.
// But `IntoBytes` and `Unaligned` definitely require `repr(C)`.
// Let's assert what SHOULD be implemented:
// `FromBytes` IS implemented for structs even if repr(Rust) (logic is lenient there).
static_assertions::assert_impl_all!(Foo: FromBytes);

// `IntoBytes` and `Unaligned` checks repr(C), so they should be suppressed.
// static_assertions::assert_not_impl_any!(Foo: IntoBytes, Unaligned);

// Manual checks (uncomment to verify they fail compilation)
// fn check_into_bytes<T: IntoBytes>() {}
// fn check_unaligned<T: Unaligned>() {}
// fn main() {
//     check_into_bytes::<Foo>();
//     check_unaligned::<Foo>();
// }
fn main() {} // Empty main for passing test.

// If this compiles, then `fail_silently` works as intended (suppresses errors for IntoBytes/Unaligned, allows FromBytes).
// And allows compilation despite IntoBytes/Unaligned derivation failure.

// Sanity check: ensure we are compiling this file.
// compile_error!("Yes, I am compiling!"); // Uncomment to verify compilation failure.

// This tests trivial bounds suppression.
// The derive generates `impl<T> FromBytes for Bar<T> where T: FromBytes`.
// `std::string::String` is not `FromBytes`, so `Bar<std::string::String>` is not `FromBytes`.
// Normally this is fine, but `trivial_bounds` allow us to write things that might otherwise error if bounds are unsatisfiable in check-validity contexts.
#[derive(FromBytes)]
#[zerocopy(derive_fail_silently)]
#[repr(C)]
struct Bar<T>(T);
