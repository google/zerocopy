// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[path = "../util.rs"]
mod util;

use test_util::*;

use core::marker::PhantomData;

use {
    static_assertions::assert_impl_all,
    zerocopy::{AsBytes, FromBytes, FromZeroes, Unaligned},
};

use self::util::NotZerocopy;

fn main() {}

// Test generic transparent structs

#[derive(AsBytes, FromZeroes, FromBytes, Unaligned)]
#[repr(transparent)]
struct TransparentStruct<T> {
    inner: T,
    _phantom: PhantomData<()>,
}

// It should be legal to derive these traits on a transparent struct, but it
// must also ensure the traits are only implemented when the inner type
// implements them.
assert_impl_all!(TransparentStruct<NotZerocopy>: FromZeroes);
//~^ ERROR: the trait bound `NotZerocopy: FromZeroes` is not satisfied
assert_impl_all!(TransparentStruct<NotZerocopy>: FromBytes);
//~^ ERROR: the trait bound `NotZerocopy: FromBytes` is not satisfied
assert_impl_all!(TransparentStruct<NotZerocopy>: AsBytes);
//~^ ERROR: the trait bound `NotZerocopy: AsBytes` is not satisfied
assert_impl_all!(TransparentStruct<NotZerocopy>: Unaligned);
//~^ ERROR: the trait bound `NotZerocopy: Unaligned` is not satisfied
