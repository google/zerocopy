// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
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

trait Associated {
    type Item;
}

struct Kind;

impl Associated for Kind {
    type Item = u8;
}

// Both enum helpers need the bound from the original where clause.
#[derive(imp::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
enum WithWhere<T>
where
    T: Associated,
{
    Value(T::Item, imp::PhantomData<T>),
}

util_assert_impl_all!(WithWhere<Kind>: imp::TryFromBytes);

#[derive(imp::FromZeros)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(i8)]
enum ExplicitZero {
    Zero = (0),
}

#[derive(imp::FromZeros)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(i8)]
enum ImpliedZero {
    Negative = -(1),
    Zero,
}

util_assert_impl_all!(ExplicitZero: imp::FromZeros);
util_assert_impl_all!(ImpliedZero: imp::FromZeros);

#[derive(imp::IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct ParenthesizedSlice {
    head: u16,
    tail: ([u16]),
}

util_assert_impl_all!(ParenthesizedSlice: imp::IntoBytes);

#[test]
fn zero_variants() {
    match <ExplicitZero as imp::FromZeros>::new_zeroed() {
        ExplicitZero::Zero => {}
    }
    match <ImpliedZero as imp::FromZeros>::new_zeroed() {
        ImpliedZero::Zero => {}
        _ => ::core::panic!("expected the implicitly numbered zero variant"),
    }
}
