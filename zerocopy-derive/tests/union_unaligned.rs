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

// A union is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields `Unaligned`
//   - `repr(packed)`

#[derive(Unaligned)]
#[repr(C)]
union Foo {
    a: u8,
}

is_unaligned!(Foo);

// Transparent unions are unstable; see issue #60405
// <https://github.com/rust-lang/rust/issues/60405> for more information.

// #[derive(Unaligned)]
// #[repr(transparent)]
// union Bar {
//     a: u8,
// }

// is_unaligned!(Bar);

#[derive(Unaligned)]
#[repr(packed)]
union Baz {
    a: u16,
}

is_unaligned!(Baz);

#[derive(Unaligned)]
#[repr(C, align(1))]
union FooAlign {
    a: u8,
}

is_unaligned!(FooAlign);

#[derive(Unaligned)]
#[repr(C)]
union TypeParams<'a, T: Copy, I: Iterator>
where
    I::Item: Copy,
{
    a: T,
    c: I::Item,
    d: u8,
    e: PhantomData<&'a [u8]>,
    f: PhantomData<&'static str>,
    g: PhantomData<String>,
}

is_unaligned!(TypeParams<'static, (), IntoIter<()>>);
