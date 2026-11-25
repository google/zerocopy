// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `Read` justifies `unsafe` pointer conversions, so downstream code must not be
// able to implement it, even for a local reason type that the orphan rules
// would otherwise permit (#3613).

include!("../include.rs");

use core::cell::Cell;

use zerocopy::pointer::invariant::{Read, Shared};

enum LocalReason {}

impl Read<Shared, LocalReason> for Cell<u8> {}
//~^ ERROR: requires an `unsafe impl` declaration

fn main() {}
