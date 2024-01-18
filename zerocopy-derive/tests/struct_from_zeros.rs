// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{marker::PhantomData, option::IntoIter};

use {static_assertions::assert_impl_all, zerocopy::FromZeros};

use crate::util::AU16;

// A struct is `FromZeros` if:
// - all fields are `FromZeros`

#[derive(FromZeros)]
struct Zst;

assert_impl_all!(Zst: FromZeros);

#[derive(FromZeros)]
struct One {
    a: bool,
}

assert_impl_all!(One: FromZeros);

#[derive(FromZeros)]
struct Two {
    a: bool,
    b: Zst,
}

assert_impl_all!(Two: FromZeros);

#[derive(FromZeros)]
struct Unsized {
    a: [u8],
}

assert_impl_all!(Unsized: FromZeros);

#[derive(FromZeros)]
struct TypeParams<'a, T: ?Sized, I: Iterator> {
    a: I::Item,
    b: u8,
    c: PhantomData<&'a [u8]>,
    d: PhantomData<&'static str>,
    e: PhantomData<String>,
    f: T,
}

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: FromZeros);
assert_impl_all!(TypeParams<'static, AU16, IntoIter<()>>: FromZeros);
assert_impl_all!(TypeParams<'static, [AU16], IntoIter<()>>: FromZeros);

// Deriving `FromZeros` should work if the struct has bounded parameters.

#[derive(FromZeros)]
#[repr(transparent)]
struct WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + FromZeros, const N: usize>(
    [T; N],
    PhantomData<&'a &'b ()>,
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + FromZeros;

assert_impl_all!(WithParams<'static, 'static, u8, 42>: FromZeros);
