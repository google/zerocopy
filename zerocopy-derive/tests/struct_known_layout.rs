// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(imp::KnownLayout)]
struct Zst;

util_assert_impl_all!(Zst: imp::KnownLayout);

#[derive(imp::KnownLayout)]
struct One {
    a: bool,
}

util_assert_impl_all!(One: imp::KnownLayout);

#[derive(imp::KnownLayout)]
struct Two {
    a: bool,
    b: Zst,
}

util_assert_impl_all!(Two: imp::KnownLayout);

#[derive(imp::KnownLayout)]
struct TypeParams<'a, T, I: imp::Iterator> {
    a: I::Item,
    b: u8,
    c: imp::PhantomData<&'a [::core::primitive::u8]>,
    d: imp::PhantomData<&'static ::core::primitive::str>,
    e: imp::PhantomData<imp::String>,
    f: T,
}

util_assert_impl_all!(TypeParams<'static, (), imp::IntoIter<()>>: imp::KnownLayout);
util_assert_impl_all!(TypeParams<'static, util::AU16, imp::IntoIter<()>>: imp::KnownLayout);

// Deriving `KnownLayout` should work if the struct has bounded parameters.

#[derive(imp::KnownLayout)]
#[repr(C)]
struct WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::KnownLayout, const N: usize>(
    [T; N],
    imp::PhantomData<&'a &'b ()>,
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::KnownLayout;

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::KnownLayout);
