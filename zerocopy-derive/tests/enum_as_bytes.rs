// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use {static_assertions::assert_impl_all, zerocopy::AsBytes};

// An enum is `AsBytes` if if has a defined repr.

#[derive(AsBytes)]
#[repr(C)]
enum C {
    A,
}

assert_impl_all!(C: AsBytes);

#[derive(AsBytes)]
#[repr(u8)]
enum U8 {
    A,
}

assert_impl_all!(U8: AsBytes);

#[derive(AsBytes)]
#[repr(u16)]
enum U16 {
    A,
}

assert_impl_all!(U16: AsBytes);

#[derive(AsBytes)]
#[repr(u32)]
enum U32 {
    A,
}

assert_impl_all!(U32: AsBytes);

#[derive(AsBytes)]
#[repr(u64)]
enum U64 {
    A,
}

assert_impl_all!(U64: AsBytes);

#[derive(AsBytes)]
#[repr(usize)]
enum Usize {
    A,
}

assert_impl_all!(Usize: AsBytes);

#[derive(AsBytes)]
#[repr(i8)]
enum I8 {
    A,
}

assert_impl_all!(I8: AsBytes);

#[derive(AsBytes)]
#[repr(i16)]
enum I16 {
    A,
}

assert_impl_all!(I16: AsBytes);

#[derive(AsBytes)]
#[repr(i32)]
enum I32 {
    A,
}

assert_impl_all!(I32: AsBytes);

#[derive(AsBytes)]
#[repr(i64)]
enum I64 {
    A,
}

assert_impl_all!(I64: AsBytes);

#[derive(AsBytes)]
#[repr(isize)]
enum Isize {
    A,
}

assert_impl_all!(Isize: AsBytes);
