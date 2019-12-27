// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use std::marker::PhantomData;
use std::option::IntoIter;

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

// A struct is FromBytes if:
// - repr(C) or repr(transparent)
// - all fields are FromBytes

#[derive(FromBytes)]
#[repr(C)]
struct CZst;

is_from_bytes!(CZst);

#[derive(FromBytes)]
#[repr(C)]
struct C {
    a: u8,
}

is_from_bytes!(C);

#[derive(FromBytes)]
#[repr(transparent)]
struct Transparent {
    a: u8,
    b: CZst,
}

is_from_bytes!(Transparent);

#[derive(FromBytes)]
#[repr(C, packed)]
struct CZstPacked;

is_from_bytes!(CZstPacked);

#[derive(FromBytes)]
#[repr(C, packed)]
struct CPacked {
    a: u8,
}

is_from_bytes!(CPacked);

#[derive(FromBytes)]
#[repr(C)]
struct TypeParams<'a, T, I: Iterator> {
    a: T,
    c: I::Item,
    d: u8,
    e: PhantomData<&'a [u8]>,
    f: PhantomData<&'static str>,
    g: PhantomData<String>,
}

is_from_bytes!(TypeParams<'static, (), IntoIter<()>>);
