// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use std::{marker::PhantomData, option::IntoIter};

use zerocopy::Unaligned;

struct IsUnaligned<T: Unaligned>(T);

// Fail compilation if `$ty: !Unaligned`.
macro_rules! is_unaligned {
    ($ty:ty) => {
        const _: () = {
            let _: IsUnaligned<$ty>;
        };
    };
}

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

is_unaligned!(Foo);

#[derive(Unaligned)]
#[repr(transparent)]
struct Bar {
    a: u8,
}

is_unaligned!(Bar);

#[derive(Unaligned)]
#[repr(packed)]
struct Baz {
    a: u16,
}

is_unaligned!(Baz);

#[derive(Unaligned)]
#[repr(C, align(1))]
struct FooAlign {
    a: u8,
}

is_unaligned!(FooAlign);

#[derive(Unaligned)]
#[repr(C)]
struct TypeParams<'a, T, I: Iterator> {
    a: T,
    c: I::Item,
    d: u8,
    e: PhantomData<&'a [u8]>,
    f: PhantomData<&'static str>,
    g: PhantomData<String>,
}

is_unaligned!(TypeParams<'static, (), IntoIter<()>>);
