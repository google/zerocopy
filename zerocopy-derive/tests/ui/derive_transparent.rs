// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

#[path = "../util.rs"]
mod util;

use core::marker::PhantomData;

use {
    static_assertions::assert_impl_all,
    zerocopy::{AsBytes, FromBytes, Unaligned},
};

use self::util::NotZerocopy;

fn main() {}

// Test generic transparent structs

#[derive(AsBytes, FromBytes, Unaligned)]
#[repr(transparent)]
struct TransparentStruct<T> {
    inner: T,
    _phantom: PhantomData<()>,
}

// It should be legal to derive these traits on a transparent struct, but it
// must also ensure the traits are only implemented when the inner type
// implements them.
assert_impl_all!(TransparentStruct<NotZerocopy>: FromBytes);
assert_impl_all!(TransparentStruct<NotZerocopy>: AsBytes);
assert_impl_all!(TransparentStruct<NotZerocopy>: Unaligned);
