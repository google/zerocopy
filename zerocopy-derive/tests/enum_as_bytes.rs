// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use zerocopy::AsBytes;

// An enum is `AsBytes` if if has a defined repr.

#[derive(AsBytes)]
#[repr(C)]
enum C {
    A,
}

assert_is_as_bytes!(C);

#[derive(AsBytes)]
#[repr(u8)]
enum U8 {
    A,
}

assert_is_as_bytes!(U8);

#[derive(AsBytes)]
#[repr(u16)]
enum U16 {
    A,
}

assert_is_as_bytes!(U16);

#[derive(AsBytes)]
#[repr(u32)]
enum U32 {
    A,
}

assert_is_as_bytes!(U32);

#[derive(AsBytes)]
#[repr(u64)]
enum U64 {
    A,
}

assert_is_as_bytes!(U64);

#[derive(AsBytes)]
#[repr(usize)]
enum Usize {
    A,
}

assert_is_as_bytes!(Usize);

#[derive(AsBytes)]
#[repr(i8)]
enum I8 {
    A,
}

assert_is_as_bytes!(I8);

#[derive(AsBytes)]
#[repr(i16)]
enum I16 {
    A,
}

assert_is_as_bytes!(I16);

#[derive(AsBytes)]
#[repr(i32)]
enum I32 {
    A,
}

assert_is_as_bytes!(I32);

#[derive(AsBytes)]
#[repr(i64)]
enum I64 {
    A,
}

assert_is_as_bytes!(I64);

#[derive(AsBytes)]
#[repr(isize)]
enum Isize {
    A,
}

assert_is_as_bytes!(Isize);
