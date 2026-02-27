// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy::transmute_ref;
use zerocopy_derive::*;

#[path = "formats/loco.rs"]
mod loco;

#[derive(IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
struct MinimalViableSource {
    header: [u8; 4],
    trailer: [[u8; 2]],
}

#[unsafe(no_mangle)]
fn codegen_test(source: &MinimalViableSource) -> &loco::Packet {
    transmute_ref!(source)
}
