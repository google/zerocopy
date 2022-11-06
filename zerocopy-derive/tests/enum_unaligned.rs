// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use zerocopy::Unaligned;

// An enum is `Unaligned` if:
// - No `repr(align(N > 1))`
// - `repr(u8)` or `repr(i8)`

#[derive(Unaligned)]
#[repr(u8)]
enum Foo {
    A,
}

assert_is_unaligned!(Foo);

#[derive(Unaligned)]
#[repr(i8)]
enum Bar {
    A,
}

assert_is_unaligned!(Bar);

#[derive(Unaligned)]
#[repr(u8, align(1))]
enum Baz {
    A,
}

assert_is_unaligned!(Baz);

#[derive(Unaligned)]
#[repr(i8, align(1))]
enum Blah {
    B,
}

assert_is_unaligned!(Blah);
