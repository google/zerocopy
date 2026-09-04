// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]
#![forbid(unsafe_code)]

use zerocopy_renamed::{Immutable, IntoBytes};

#[derive(Immutable, IntoBytes)]
//~^ ERROR: the trait bound
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct PaddedTail {
    tag: u8,
    values: [u32],
}

impl zerocopy_renamed::util::macro_util::DynamicPaddingFree<PaddedTail, true> for () {}
//~^ ERROR: the trait bound

fn main() {}
