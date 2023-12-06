// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{cell::UnsafeCell, marker::PhantomData, option::IntoIter};

use {static_assertions::assert_impl_all, zerocopy::NoCell};

#[derive(Clone, Copy, NoCell)]
union Zst {
    a: (),
}

assert_impl_all!(Zst: NoCell);

#[derive(NoCell)]
union One {
    a: bool,
}

assert_impl_all!(One: NoCell);

#[derive(NoCell)]
union Two {
    a: bool,
    b: Zst,
}

assert_impl_all!(Two: NoCell);

#[derive(NoCell)]
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

assert_impl_all!(TypeParams<'static, (), IntoIter<()>>: NoCell);

// Deriving `NoCell` should work if the union has bounded parameters.

#[derive(NoCell)]
#[repr(C)]
union WithParams<'a: 'b, 'b: 'a, const N: usize, T: 'a + 'b + NoCell>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + Copy + NoCell,
{
    a: [T; N],
    b: PhantomData<&'a &'b ()>,
    c: PhantomData<UnsafeCell<()>>,
    d: &'a UnsafeCell<()>,
}

assert_impl_all!(WithParams<'static, 'static, 42, u8>: NoCell);
