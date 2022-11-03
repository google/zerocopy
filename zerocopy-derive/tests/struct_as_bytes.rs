// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

mod util;

use std::{marker::PhantomData, option::IntoIter};

use zerocopy::AsBytes;

use crate::util::AU16;

struct IsAsBytes<T: AsBytes>(T);

// Fail compilation if `$ty: !AsBytes`.
macro_rules! is_as_bytes {
    ($ty:ty) => {
        const _: () = {
            let _: IsAsBytes<$ty>;
        };
    };
}

// A struct is `AsBytes` if:
// - all fields are `AsBytes`
// - `repr(C)` or `repr(transparent)` and
//   - no padding (size of struct equals sum of size of field types)
// - `repr(packed)`

#[derive(AsBytes)]
#[repr(C)]
struct CZst;

is_as_bytes!(CZst);

#[derive(AsBytes)]
#[repr(C)]
struct C {
    a: u8,
    b: u8,
    c: AU16,
}

is_as_bytes!(C);

#[derive(AsBytes)]
#[repr(transparent)]
struct Transparent {
    a: u8,
    b: CZst,
}

is_as_bytes!(Transparent);

#[derive(AsBytes)]
#[repr(C, packed)]
struct CZstPacked;

is_as_bytes!(CZstPacked);

#[derive(AsBytes)]
#[repr(C, packed)]
struct CPacked {
    a: u8,
    // NOTE: The `u16` type is not guaranteed to have alignment 2, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(2))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u16` here. Luckily, these tests run in CI on
    // platforms on which `u16` has alignment 2, so this isn't that big of a
    // deal.
    b: u16,
}

is_as_bytes!(CPacked);
