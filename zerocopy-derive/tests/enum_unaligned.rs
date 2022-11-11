// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use {static_assertions::assert_impl_all, zerocopy::Unaligned};

// An enum is `Unaligned` if:
// - No `repr(align(N > 1))`
// - `repr(u8)` or `repr(i8)`

#[derive(Unaligned)]
#[repr(u8)]
enum Foo {
    A,
}

assert_impl_all!(Foo: Unaligned);

#[derive(Unaligned)]
#[repr(i8)]
enum Bar {
    A,
}

assert_impl_all!(Bar: Unaligned);

#[derive(Unaligned)]
#[repr(u8, align(1))]
enum Baz {
    A,
}

assert_impl_all!(Baz: Unaligned);

#[derive(Unaligned)]
#[repr(i8, align(1))]
enum Blah {
    B,
}

assert_impl_all!(Blah: Unaligned);
