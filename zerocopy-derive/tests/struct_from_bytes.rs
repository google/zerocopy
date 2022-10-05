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

// A struct is `FromBytes` if:
// - all fields are `FromBytes`

#[derive(FromBytes)]
struct Zst;

is_from_bytes!(Zst);

#[derive(FromBytes)]
struct One {
    a: u8,
}

is_from_bytes!(One);

#[derive(FromBytes)]
struct Two {
    a: u8,
    b: Zst,
}

is_from_bytes!(Two);

#[derive(FromBytes)]
struct TypeParams<'a, T, I: Iterator> {
    a: T,
    c: I::Item,
    d: u8,
    e: PhantomData<&'a [u8]>,
    f: PhantomData<&'static str>,
    g: PhantomData<String>,
}

is_from_bytes!(TypeParams<'static, (), IntoIter<()>>);
