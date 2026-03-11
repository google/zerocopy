// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![feature(trivial_bounds)]

extern crate zerocopy;

#[path = "../util.rs"]
mod util;

use static_assertions::assert_impl_all;
use zerocopy::{AsBytes, FromBytes, FromZeroes, Unaligned};

use self::util::{NotZerocopy, AU16};

fn main() {}

// These tests are compiled with the `trivial_bounds` feature enabled. We emit
// code which is designed to fail compilation for types we wish to reject. E.g.:
//
//   #[derive(FromZeroes)]
//   struct Foo(NotZerocopy);
//
// It would be unsound to emit an impl of `FromZeroes for Foo` in this case. Our
// custom derives are designed to cause compilation to fail for this type.
// `trivial_bounds` instead allows this code to succeed by simply not emitting
// `impl FromZeroes for Foo`. This isn't a soundness issue, but is likely
// confusing to users.
//
// As of this writing, the code in this file only fails to compile thanks to the
// use of `assert_impl_all!`, which depends upon the incorrect trait bounds.
//
// TODO(https://github.com/rust-lang/rust/issues/48214): If support is ever
// added for `#[deny(trivially_false_bounds)]` as discussed in the
// `trivial_bounds` tracking issue, we should emit that annotation in our
// derives. That will result in the `#[derive(...)]` annotations in this file
// failing to compile, not just the `assert_impl_all!` calls.

//
// FromZeroes errors
//

#[derive(FromZeroes)]
struct FromZeroes1 {
    value: NotZerocopy,
}

assert_impl_all!(FromZeroes1: FromZeroes);

//
// FromBytes errors
//

#[derive(FromBytes)]
struct FromBytes1 {
    value: NotZerocopy,
}

assert_impl_all!(FromBytes1: FromBytes);

//
// AsBytes errors
//

#[derive(AsBytes)]
#[repr(C)]
struct AsBytes1 {
    value: NotZerocopy,
}

assert_impl_all!(AsBytes1: AsBytes);

//
// Unaligned errors
//

#[derive(Unaligned)]
#[repr(C)]
struct Unaligned1 {
    aligned: AU16,
}

assert_impl_all!(Unaligned1: Unaligned);
