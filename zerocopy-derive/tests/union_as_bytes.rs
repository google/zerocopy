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

// A union is `AsBytes` if:
// - all fields are `AsBytes`
// - `repr(C)` or `repr(transparent)` and
//   - no padding (size of union equals size of each field type)
// - `repr(packed)`

#[derive(AsBytes, Clone, Copy)]
#[repr(C)]
union CZst {
    a: (),
}

is_as_bytes!(CZst);

#[derive(AsBytes)]
#[repr(C)]
union C {
    a: u8,
    b: u8,
}

is_as_bytes!(C);

// Transparent unions are unstable; see issue #60405
// <https://github.com/rust-lang/rust/issues/60405> for more information.

// #[derive(AsBytes)]
// #[repr(transparent)]
// union Transparent {
//     a: u8,
//     b: CZst,
// }

// is_as_bytes!(Transparent);

#[derive(AsBytes)]
#[repr(C, packed)]
union CZstPacked {
    a: (),
}

is_as_bytes!(CZstPacked);

#[derive(AsBytes)]
#[repr(C, packed)]
union CPacked {
    a: u8,
    b: i8,
}

is_as_bytes!(CPacked);

#[derive(AsBytes)]
#[repr(C, packed)]
union CMultibytePacked {
    a: i32,
    b: u32,
    c: f32,
}

is_as_bytes!(CMultibytePacked);
