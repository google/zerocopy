// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use std::{marker::PhantomData, option::IntoIter};

use {
    static_assertions::assert_impl_all,
    zerocopy::{FromBytes, FromZeroes},
};

// A union is `FromBytes` if:
// - all fields are `FromBytes`

#[derive(Clone, Copy, FromZeroes, FromBytes)]
union Zst {
    a: (),
}

assert_impl_all!(Zst: FromBytes);

#[derive(FromZeroes, FromBytes)]
union One {
    a: u8,
}

assert_impl_all!(One: FromBytes);

#[derive(FromZeroes, FromBytes)]
union Two {
    a: u8,
    b: Zst,
}

assert_impl_all!(Two: FromBytes);

#[derive(FromZeroes, FromBytes)]
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

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: FromBytes);
