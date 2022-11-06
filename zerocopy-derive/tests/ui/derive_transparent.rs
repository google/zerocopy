// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

#[path = "../util.rs"]
#[macro_use]
mod util;

use self::util::{NotAsBytes, AU16};

fn main() {}

use core::marker::PhantomData;
use zerocopy::{AsBytes, FromBytes, Unaligned};

// Test generic transparent structs

#[derive(AsBytes, FromBytes, Unaligned)]
#[repr(transparent)]
struct TransparentStruct<T> {
    inner: T,
    _phantom: PhantomData<()>,
}

// A type that does not implement `AsBytes`.
pub struct NotAsBytes;

// It should be legal to derive these traits on a transparent struct, but it
// must also ensure the traits are only implemented when the inner type
// implements them.
assert_is_as_bytes!(TransparentStruct<NotAsBytes>);
assert_is_from_bytes!(TransparentStruct<char>);
assert_is_unaligned!(TransparentStruct<AU16>);
