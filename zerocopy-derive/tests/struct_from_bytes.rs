// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{marker::PhantomData, option::IntoIter};
use zerocopy::FromBytes;

// A struct is `FromBytes` if:
// - all fields are `FromBytes`

#[derive(FromBytes)]
struct Zst;

assert_is_from_bytes!(Zst);

#[derive(FromBytes)]
struct One {
    a: u8,
}

assert_is_from_bytes!(One);

#[derive(FromBytes)]
struct Two {
    a: u8,
    b: Zst,
}

assert_is_from_bytes!(Two);

#[derive(FromBytes)]
struct TypeParams<'a, T, I: Iterator> {
    a: T,
    c: I::Item,
    d: u8,
    e: PhantomData<&'a [u8]>,
    f: PhantomData<&'static str>,
    g: PhantomData<String>,
}

assert_is_from_bytes!(TypeParams<'static, (), IntoIter<()>>);
