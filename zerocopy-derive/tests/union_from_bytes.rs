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

// A union is `imp::FromBytes` if:
// - all fields are `imp::FromBytes`

#[derive(Clone, Copy, imp::NoCell, imp::FromBytes)]
union Zst {
    a: (),
}

util_assert_impl_all!(Zst: imp::FromBytes);

#[derive(imp::NoCell, imp::FromBytes)]
union One {
    a: u8,
}

util_assert_impl_all!(One: imp::FromBytes);

#[derive(imp::NoCell, imp::FromBytes)]
union Two {
    a: u8,
    b: Zst,
}

util_assert_impl_all!(Two: imp::FromBytes);

#[derive(imp::NoCell, imp::FromBytes)]
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

util_assert_impl_all!(TypeParams<'static, (), imp::IntoIter<()>>: imp::FromBytes);

// Deriving `imp::FromBytes` should work if the union has bounded parameters.

#[derive(imp::NoCell, imp::FromBytes)]
#[repr(C)]
union WithParams<'a: 'b, 'b: 'a, T: 'a + 'b + imp::FromBytes, const N: usize>
where
    'a: 'b,
    'b: 'a,
    T: 'a + 'b + imp::Copy + imp::FromBytes,
{
    a: [T; N],
    b: imp::PhantomData<&'a &'b ()>,
}

util_assert_impl_all!(WithParams<'static, 'static, u8, 42>: imp::FromBytes);
