// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{marker::PhantomData, option::IntoIter};

use {static_assertions::assert_impl_all, zerocopy::FromZeroes};

use crate::util::AU16;

// A struct is `FromZeroes` if:
// - all fields are `FromZeroes`

#[derive(FromZeroes)]
struct Zst;

assert_impl_all!(Zst: FromZeroes);

#[derive(FromZeroes)]
struct One {
    a: bool,
}

assert_impl_all!(One: FromZeroes);

#[derive(FromZeroes)]
struct Two {
    a: bool,
    b: Zst,
}

assert_impl_all!(Two: FromZeroes);

#[derive(FromZeroes)]
struct Unsized {
    a: [u8],
}

assert_impl_all!(Unsized: FromZeroes);

#[derive(FromZeroes)]
struct TypeParams<'a, T: ?Sized, I: Iterator> {
    a: I::Item,
    b: u8,
    c: PhantomData<&'a [u8]>,
    d: PhantomData<&'static str>,
    e: PhantomData<String>,
    f: T,
}

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: FromZeroes);
assert_impl_all!(TypeParams<'static, AU16, IntoIter<()>>: FromZeroes);
assert_impl_all!(TypeParams<'static, [AU16], IntoIter<()>>: FromZeroes);
