// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(imp::KnownLayout)]
enum Foo {
    A,
}

util_assert_impl_all!(Foo: imp::KnownLayout);

#[derive(imp::KnownLayout)]
enum Bar {
    A = 0,
}

util_assert_impl_all!(Bar: imp::KnownLayout);

#[derive(imp::KnownLayout)]
enum Baz {
    A = 1,
    B = 0,
}

util_assert_impl_all!(Baz: imp::KnownLayout);

// Deriving `KnownLayout` should work if the enum has bounded parameters.

#[derive(imp::KnownLayout)]
#[repr(C)]
enum WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::KnownLayout, const N: usize>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::KnownLayout,
{
    Variant([T; N], imp::PhantomData<&'a &'b ()>),
}

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::KnownLayout);
