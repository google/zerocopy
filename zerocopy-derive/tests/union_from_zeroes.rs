// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{marker::PhantomData, option::IntoIter};

use {static_assertions::assert_impl_all, zerocopy::FromZeroes};

// A union is `FromZeroes` if:
// - all fields are `FromZeroes`

#[derive(Clone, Copy, FromZeroes)]
union Zst {
    a: (),
}

assert_impl_all!(Zst: FromZeroes);

#[derive(FromZeroes)]
union One {
    a: bool,
}

assert_impl_all!(One: FromZeroes);

#[derive(FromZeroes)]
union Two {
    a: bool,
    b: Zst,
}

assert_impl_all!(Two: FromZeroes);

#[derive(FromZeroes)]
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

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: FromZeroes);
