// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

mod util;

use {static_assertions::assert_impl_all, zerocopy::KnownLayout};

#[derive(KnownLayout)]
enum Foo {
    A,
}

assert_impl_all!(Foo: KnownLayout);

#[derive(KnownLayout)]
enum Bar {
    A = 0,
}

assert_impl_all!(Bar: KnownLayout);

#[derive(KnownLayout)]
enum Baz {
    A = 1,
    B = 0,
}

assert_impl_all!(Baz: KnownLayout);
