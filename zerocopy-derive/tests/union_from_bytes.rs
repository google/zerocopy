// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use std::{marker::PhantomData, option::IntoIter};

use zerocopy::FromBytes;

struct IsFromBytes<T: FromBytes>(T);

// Fail compilation if `$ty: !FromBytes`.
macro_rules! is_from_bytes {
    ($ty:ty) => {
        const _: () = {
            let _: IsFromBytes<$ty>;
        };
    };
}

// A union is `FromBytes` if:
// - all fields are `FromBytes`

#[derive(Clone, Copy, FromBytes)]
union Zst {
    a: (),
}

is_from_bytes!(Zst);

#[derive(FromBytes)]
union One {
    a: u8,
}

is_from_bytes!(One);

#[derive(FromBytes)]
union Two {
    a: u8,
    b: Zst,
}

is_from_bytes!(Two);

#[derive(FromBytes)]
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

is_from_bytes!(TypeParams<'static, (), IntoIter<()>>);
