// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(Clone, Copy, imp::NoCell)]
union Zst {
    a: (),
}

util_assert_impl_all!(Zst: imp::NoCell);

#[derive(imp::NoCell)]
union One {
    a: bool,
}

util_assert_impl_all!(One: imp::NoCell);

#[derive(imp::NoCell)]
union Two {
    a: bool,
    b: Zst,
}

util_assert_impl_all!(Two: imp::NoCell);

#[derive(imp::NoCell)]
union TypeParams<'a, T: imp::Copy, I: imp::Iterator>
where
    I::Item: imp::Copy,
{
    a: T,
    c: I::Item,
    d: u8,
    e: imp::PhantomData<&'a [::core::primitive::u8]>,
    f: imp::PhantomData<&'static ::core::primitive::str>,
    g: imp::PhantomData<imp::String>,
}

util_assert_impl_all!(TypeParams<'static, (), imp::IntoIter<()>>: imp::NoCell);

// Deriving `imp::NoCell` should work if the union has bounded parameters.

#[derive(imp::NoCell)]
#[repr(C)]
union WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::NoCell, const N: usize>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::Copy + imp::NoCell,
{
    a: [T; N],
    b: imp::PhantomData<&'a &'b ()>,
    c: imp::PhantomData<imp::UnsafeCell<()>>,
    d: &'a imp::UnsafeCell<()>,
}

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::NoCell);
