// Copyright 2022 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

use util::*;
use zerocopy::transmute;

fn main() {
    // `transmute` requires that the destination type implements `FromBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `NotZerocopy: FromBytes` is not satisfied
    const DST_NOT_FROM_BYTES: NotZerocopy = transmute!(AU16(0));

    // Although this is not a soundness requirement, we currently require that the
    // size of the destination type is not smaller than the size of the source type.
    //@[msrv, stable, nightly]~ ERROR: cannot transmute between types of different sizes, or dependently-sized types
    //@[stable, nightly]~ ERROR: transmuting from 2-byte type to 1-byte type: `AU16` -> `u8`
    const DECREASE_SIZE: u8 = transmute!(AU16(0));

    // `transmute!` does not support transmuting from a smaller type to a larger
    // one.
    //@[msrv, stable, nightly]~ ERROR: cannot transmute between types of different sizes, or dependently-sized types
    //@[stable, nightly]~ ERROR: transmuting from 1-byte type to 2-byte type: `u8` -> `Transmute<u8, AU16>`
    const INCREASE_SIZE: AU16 = transmute!(#![allow(shrink)] 0u8);

    // `transmute!` does not support transmuting from a smaller type to a larger
    // one.
    //@[msrv, stable, nightly]~ ERROR: cannot transmute between types of different sizes, or dependently-sized types
    //@[stable, nightly]~ ERROR: transmuting from 1-byte type to 2-byte type: `u8` -> `AU16`
    const INCREASE_SIZE: AU16 = transmute!(0u8);

    // `transmute` requires that the source type implements `IntoBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `NotZerocopy<AU16>: IntoBytes` is not satisfied
    const SRC_NOT_AS_BYTES: AU16 = transmute!(NotZerocopy(AU16(0)));

    // It is unclear whether we can or should support this transmutation, especially
    // in a const context. This test ensures that even if such a transmutation
    // becomes valid due to the requisite implementations of `FromBytes` being
    // added, that we re-examine whether it should specifically be valid in a const
    // context.
    //@[msrv, stable, nightly]~ ERROR: the trait bound `*const usize: IntoBytes` is not satisfied
    const POINTER_VALUE: usize = transmute!(&0usize as *const usize);
}
