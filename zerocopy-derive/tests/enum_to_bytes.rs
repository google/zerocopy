// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(warnings)]

use {static_assertions::assert_impl_all, zerocopy::IntoBytes};

// An enum is `IntoBytes` if if has a defined repr.

#[derive(IntoBytes)]
#[repr(C)]
enum C {
    A,
}

assert_impl_all!(C: IntoBytes);

#[derive(IntoBytes)]
#[repr(u8)]
enum U8 {
    A,
}

assert_impl_all!(U8: IntoBytes);

#[derive(IntoBytes)]
#[repr(u16)]
enum U16 {
    A,
}

assert_impl_all!(U16: IntoBytes);

#[derive(IntoBytes)]
#[repr(u32)]
enum U32 {
    A,
}

assert_impl_all!(U32: IntoBytes);

#[derive(IntoBytes)]
#[repr(u64)]
enum U64 {
    A,
}

assert_impl_all!(U64: IntoBytes);

#[derive(IntoBytes)]
#[repr(usize)]
enum Usize {
    A,
}

assert_impl_all!(Usize: IntoBytes);

#[derive(IntoBytes)]
#[repr(i8)]
enum I8 {
    A,
}

assert_impl_all!(I8: IntoBytes);

#[derive(IntoBytes)]
#[repr(i16)]
enum I16 {
    A,
}

assert_impl_all!(I16: IntoBytes);

#[derive(IntoBytes)]
#[repr(i32)]
enum I32 {
    A,
}

assert_impl_all!(I32: IntoBytes);

#[derive(IntoBytes)]
#[repr(i64)]
enum I64 {
    A,
}

assert_impl_all!(I64: IntoBytes);

#[derive(IntoBytes)]
#[repr(isize)]
enum Isize {
    A,
}

assert_impl_all!(Isize: IntoBytes);
