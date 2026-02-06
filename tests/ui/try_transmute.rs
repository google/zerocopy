// Copyright 2022 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

use util::*;
use zerocopy::try_transmute;

fn main() {
    //@[msrv, stable, nightly]~ ERROR: the trait bound `NotZerocopy: TryFromBytes` is not satisfied
    let dst_not_try_from_bytes: Result<NotZerocopy, _> = try_transmute!(AU16(0));

    //@[msrv, stable, nightly]~ ERROR: cannot transmute between types of different sizes, or dependently-sized types
    let _decrease_size: Result<u8, _> = try_transmute!(AU16(0));

    //@[msrv, stable, nightly]~ ERROR: cannot transmute between types of different sizes, or dependently-sized types
    let _increase_size: Result<AU16, _> = try_transmute!(0u8);

    // `try_transmute` requires that the source type implements `IntoBytes`
    //@[msrv, stable, nightly]~ ERROR: the trait bound `NotZerocopy<AU16>: IntoBytes` is not satisfied
    let src_not_into_bytes: Result<AU16, _> = try_transmute!(NotZerocopy(AU16(0)));
}
