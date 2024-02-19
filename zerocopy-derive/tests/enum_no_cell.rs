// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(imp::NoCell)]
enum Foo {
    A,
}

util_assert_impl_all!(Foo: imp::NoCell);

#[derive(imp::NoCell)]
enum Bar {
    A = 0,
}

util_assert_impl_all!(Bar: imp::NoCell);

#[derive(imp::NoCell)]
enum Baz {
    A = 1,
    B = 0,
}

util_assert_impl_all!(Baz: imp::NoCell);

// Deriving `NoCell` should work if the enum has bounded parameters.

#[derive(imp::NoCell)]
#[repr(C)]
enum WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::NoCell, const N: ::core::primitive::usize>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::NoCell,
{
    Variant([T; N], imp::PhantomData<&'a &'b ()>),
    UnsafeCell(imp::PhantomData<imp::UnsafeCell<()>>, &'a imp::UnsafeCell<()>),
}

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::NoCell);
