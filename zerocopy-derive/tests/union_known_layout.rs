// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(Clone, Copy, imp::KnownLayout)]
union Zst {
    a: (),
}

util_assert_impl_all!(Zst: imp::KnownLayout);

#[derive(imp::KnownLayout)]
union One {
    a: bool,
}

util_assert_impl_all!(One: imp::KnownLayout);

#[derive(imp::KnownLayout)]
union Two {
    a: bool,
    b: Zst,
}

util_assert_impl_all!(Two: imp::KnownLayout);

#[derive(imp::KnownLayout)]
union TypeParams<'a, T: imp::Copy, I: imp::Iterator>
where
    I::Item: imp::Copy,
{
    a: T,
    c: I::Item,
    d: u8,
    e: imp::PhantomData<&'a [u8]>,
    f: imp::PhantomData<&'static str>,
    g: imp::PhantomData<imp::String>,
}

util_assert_impl_all!(TypeParams<'static, (), imp::IntoIter<()>>: imp::KnownLayout);

// Deriving `imp::KnownLayout` should work if the union has bounded parameters.

#[derive(imp::KnownLayout)]
#[repr(C)]
union WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::KnownLayout, const N: usize>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::Copy + imp::KnownLayout,
{
    a: [T; N],
    b: imp::PhantomData<&'a &'b ()>,
}

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::KnownLayout);
