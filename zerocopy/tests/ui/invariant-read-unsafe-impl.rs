// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `Read` is sealed, so downstream code cannot implement it even by writing
// `unsafe impl` (#3613).

include!("../include.rs");

use core::cell::Cell;

use zerocopy::pointer::invariant::{Read, Shared};

enum LocalReason {}

unsafe impl Read<Shared, LocalReason> for Cell<u8> {}
//~^ ERROR: is not satisfied

fn main() {}
