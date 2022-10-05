// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use std::{marker::PhantomData, option::IntoIter};

use zerocopy::AsBytes;

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
    c: u16,
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
    b: u16,
}

is_as_bytes!(CPacked);
