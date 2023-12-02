// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{cell::UnsafeCell, marker::PhantomData, option::IntoIter};

use {
    static_assertions::{assert_impl_all, assert_not_impl_any},
    zerocopy::NoCell,
};

use crate::util::AU16;

#[derive(NoCell)]
struct Zst;

assert_impl_all!(Zst: NoCell);

#[derive(NoCell)]
struct One {
    a: bool,
}

assert_impl_all!(One: NoCell);

#[derive(NoCell)]
struct Two {
    a: bool,
    b: Zst,
}

assert_impl_all!(Two: NoCell);

#[derive(NoCell)]
struct Three {
    a: [u8],
}

assert_impl_all!(Three: NoCell);

#[derive(NoCell)]
struct Four<'a> {
    field: &'a UnsafeCell<u8>,
}

assert_impl_all!(Four<'static>: NoCell);

#[derive(NoCell)]
struct TypeParams<'a, T, U, I: Iterator> {
    a: I::Item,
    b: u8,
    c: PhantomData<&'a [u8]>,
    d: PhantomData<&'static str>,
    e: PhantomData<String>,
    f: PhantomData<U>,
    g: T,
}

assert_impl_all!(TypeParams<'static, (), (), IntoIter<()>>: NoCell);
assert_impl_all!(TypeParams<'static, AU16, AU16, IntoIter<()>>: NoCell);
assert_impl_all!(TypeParams<'static, AU16, UnsafeCell<u8>, IntoIter<()>>: NoCell);
assert_not_impl_any!(TypeParams<'static, UnsafeCell<()>, (), IntoIter<()>>: NoCell);
assert_not_impl_any!(TypeParams<'static, [UnsafeCell<u8>; 0], (), IntoIter<()>>: NoCell);
assert_not_impl_any!(TypeParams<'static, (), (), IntoIter<UnsafeCell<()>>>: NoCell);

trait Trait {
    type Assoc;
}

impl<T> Trait for UnsafeCell<T> {
    type Assoc = T;
}

#[derive(NoCell)]
struct WithAssocType<T: Trait> {
    field: <T as Trait>::Assoc,
}

assert_impl_all!(WithAssocType<UnsafeCell<u8>>: NoCell);

// Deriving `NoCell` should work if the struct has bounded parameters.

#[derive(NoCell)]
#[repr(C)]
struct WithParams<'a: 'b, 'b: 'a, const N: usize, T: 'a + 'b + NoCell>(
    [T; N],
    PhantomData<&'a &'b ()>,
    PhantomData<UnsafeCell<()>>,
    &'a UnsafeCell<()>,
)
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + NoCell;

assert_impl_all!(WithParams<'static, 'static, 42, u8>: NoCell);
