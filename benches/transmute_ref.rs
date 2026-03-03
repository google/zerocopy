// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy::transmute_ref;
use zerocopy_derive::*;

#[path = "formats/coco.rs"]
mod format;

#[derive(IntoBytes, KnownLayout, Immutable)]
#[repr(C, align(2))]
struct MinimalViableSource {
    header: [u8; 4],
    trailer: [[u8; 2]],
}

#[unsafe(no_mangle)]
fn codegen_test(source: &MinimalViableSource) -> &format::LocoPacket {
    transmute_ref!(source)
}
