// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// Make sure that macro hygiene will ensure that when we reference "zerocopy",
// that will work properly even if they've renamed the crate.

#![allow(warnings)]

extern crate zerocopy as _zerocopy;

use std::{marker::PhantomData, option::IntoIter};

use _zerocopy::FromBytes;

#[derive(FromBytes)]
struct TypeParams<'a, T, I: Iterator> {
    a: T,
    c: I::Item,
    d: u8,
    e: PhantomData<&'a [u8]>,
    f: PhantomData<&'static str>,
    g: PhantomData<String>,
}

const _FOO: () = {
    let _: IsFromBytes<TypeParams<'static, (), IntoIter<()>>>;
};

struct IsFromBytes<T: FromBytes>(PhantomData<T>);
