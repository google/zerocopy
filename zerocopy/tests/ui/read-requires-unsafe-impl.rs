// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![forbid(unsafe_code)]

include!("../include.rs");

use std::{cell::Cell, vec::Vec};

use zerocopy::pointer::invariant::{Read, Shared};

struct CallerReason;

impl Read<Shared, CallerReason> for Cell<Vec<u8>> {}
//~[msrv, stable, nightly]^ ERROR: requires an `unsafe impl` declaration

impl Read<Shared, CallerReason> for Vec<u8> {}
//~[msrv, stable, nightly]^ ERROR: requires an `unsafe impl` declaration

fn main() {}
