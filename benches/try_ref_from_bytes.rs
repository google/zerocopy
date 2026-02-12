// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy::TryFromBytes;

#[path = "formats/coco.rs"]
mod coco;

#[unsafe(no_mangle)]
fn codegen_test(source: &[u8]) -> Option<&coco::Packet> {
    TryFromBytes::try_ref_from_bytes(source).ok()
}
