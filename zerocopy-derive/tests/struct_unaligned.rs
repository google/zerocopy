// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{marker::PhantomData, option::IntoIter};

use zerocopy::Unaligned;

use crate::util::AU16;

// A struct is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields Unaligned
//   - `repr(packed)`

#[derive(Unaligned)]
#[repr(C)]
struct Foo {
    a: u8,
}

assert_is_unaligned!(Foo);

#[derive(Unaligned)]
#[repr(transparent)]
struct Bar {
    a: u8,
}

assert_is_unaligned!(Bar);

#[derive(Unaligned)]
#[repr(packed)]
struct Baz {
    // NOTE: The `u16` type is not guaranteed to have alignment 2, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(2))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u16` here. Luckily, these tests run in CI on
    // platforms on which `u16` has alignment 2, so this isn't that big of a
    // deal.
    a: u16,
}

assert_is_unaligned!(Baz);

#[derive(Unaligned)]
#[repr(C, align(1))]
struct FooAlign {
    a: u8,
}

assert_is_unaligned!(FooAlign);

#[derive(Unaligned)]
#[repr(transparent)]
struct Unsized {
    a: [u8],
}

assert_is_unaligned!(Unsized);

#[derive(Unaligned)]
#[repr(C)]
struct TypeParams<'a, T: ?Sized, I: Iterator> {
    a: I::Item,
    b: u8,
    c: PhantomData<&'a [u8]>,
    d: PhantomData<&'static str>,
    e: PhantomData<String>,
    f: T,
}

assert_is_unaligned!(TypeParams<'static, (), IntoIter<()>>);
assert_is_unaligned!(TypeParams<'static, u8, IntoIter<()>>);
assert_is_unaligned!(TypeParams<'static, [u8], IntoIter<()>>);
