// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use std::{marker::PhantomData, option::IntoIter};

use {static_assertions::assert_impl_all, zerocopy::AsBytes};

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

assert_impl_all!(CZst: AsBytes);

#[derive(AsBytes)]
#[repr(C)]
union C {
    a: u8,
    b: u8,
}

assert_impl_all!(C: AsBytes);

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

assert_impl_all!(CZstPacked: AsBytes);

#[derive(AsBytes)]
#[repr(C, packed)]
union CPacked {
    a: u8,
    b: i8,
}

assert_impl_all!(CPacked: AsBytes);

#[derive(AsBytes)]
#[repr(C, packed)]
union CMultibytePacked {
    a: i32,
    b: u32,
    c: f32,
}

assert_impl_all!(CMultibytePacked: AsBytes);
