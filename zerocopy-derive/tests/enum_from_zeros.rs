// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

#[derive(imp::FromZeros)]
#[repr(C)]
enum Foo {
    A,
}

util_assert_impl_all!(Foo: imp::FromZeros);

#[derive(imp::FromZeros)]
#[repr(C)]
enum Bar {
    A = 0,
}

util_assert_impl_all!(Bar: imp::FromZeros);

#[derive(imp::FromZeros)]
#[repr(C)]
enum Baz {
    A = 1,
    B = 0,
}

util_assert_impl_all!(Baz: imp::FromZeros);
