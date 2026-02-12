// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy::FromBytes;

#[path = "formats/loco.rs"]
mod loco;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8], count: usize) -> Option<&loco::Packet> {
    match FromBytes::ref_from_suffix_with_elems(source, count) {
        Ok((_rest, packet)) => Some(packet),
        _ => None,
    }
}
