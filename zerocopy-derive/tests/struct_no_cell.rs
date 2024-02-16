// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(imp::NoCell)]
struct Zst;

util_assert_impl_all!(Zst: imp::NoCell);

#[derive(imp::NoCell)]
struct One {
    a: bool,
}

util_assert_impl_all!(One: imp::NoCell);

#[derive(imp::NoCell)]
struct Two {
    a: bool,
    b: Zst,
}

util_assert_impl_all!(Two: imp::NoCell);

#[derive(imp::NoCell)]
struct Three {
    a: [u8],
}

util_assert_impl_all!(Three: imp::NoCell);

#[derive(imp::NoCell)]
struct Four<'a> {
    field: &'a imp::UnsafeCell<u8>,
}

util_assert_impl_all!(Four<'static>: imp::NoCell);

#[derive(imp::NoCell)]
struct TypeParams<'a, T, U, I: imp::Iterator> {
    a: I::Item,
    b: u8,
    c: imp::PhantomData<&'a [::core::primitive::u8]>,
    d: imp::PhantomData<&'static ::core::primitive::str>,
    e: imp::PhantomData<imp::String>,
    f: imp::PhantomData<U>,
    g: T,
}

util_assert_impl_all!(TypeParams<'static, (), (), imp::IntoIter<()>>: imp::NoCell);
util_assert_impl_all!(TypeParams<'static, util::AU16, util::AU16, imp::IntoIter<()>>: imp::NoCell);
util_assert_impl_all!(TypeParams<'static, util::AU16, imp::UnsafeCell<u8>, imp::IntoIter<()>>: imp::NoCell);
util_assert_not_impl_any!(TypeParams<'static, imp::UnsafeCell<()>, (), imp::IntoIter<()>>: imp::NoCell);
util_assert_not_impl_any!(TypeParams<'static, [imp::UnsafeCell<u8>; 0], (), imp::IntoIter<()>>: imp::NoCell);
util_assert_not_impl_any!(TypeParams<'static, (), (), imp::IntoIter<imp::UnsafeCell<()>>>: imp::NoCell);

trait Trait {
    type Assoc;
}

impl<T> Trait for imp::UnsafeCell<T> {
    type Assoc = T;
}

#[derive(imp::NoCell)]
struct WithAssocType<T: Trait> {
    field: <T as Trait>::Assoc,
}

util_assert_impl_all!(WithAssocType<imp::UnsafeCell<u8>>: imp::NoCell);

// Deriving `NoCell` should work if the struct has bounded parameters.

#[derive(imp::NoCell)]
#[repr(C)]
struct WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::NoCell, const N: usize>(
    [T; N],
    imp::PhantomData<&'a &'b ()>,
    imp::PhantomData<imp::UnsafeCell<()>>,
    &'a imp::UnsafeCell<()>,
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::NoCell;

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::NoCell);
