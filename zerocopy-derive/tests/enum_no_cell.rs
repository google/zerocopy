// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

mod util;

use {
    core::cell::UnsafeCell, core::marker::PhantomData, static_assertions::assert_impl_all,
    zerocopy::NoCell,
};

#[derive(NoCell)]
enum Foo {
    A,
}

assert_impl_all!(Foo: NoCell);

#[derive(NoCell)]
enum Bar {
    A = 0,
}

assert_impl_all!(Bar: NoCell);

#[derive(NoCell)]
enum Baz {
    A = 1,
    B = 0,
}

assert_impl_all!(Baz: NoCell);

// Deriving `NoCell` should work if the enum has bounded parameters.

#[derive(NoCell)]
#[repr(C)]
enum WithParams<'a: 'b, 'b: 'a, const N: usize, T: 'a + 'b + NoCell>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + NoCell,
{
    Variant([T; N], PhantomData<&'a &'b ()>),
    UnsafeCell(PhantomData<UnsafeCell<()>>, &'a UnsafeCell<()>),
}

assert_impl_all!(WithParams<'static, 'static, 42, u8>: NoCell);
