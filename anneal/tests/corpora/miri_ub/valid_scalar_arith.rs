// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

fn main() {
    let x: u32 = 0x1234_5678;
    let y: u32 = (x ^ 0x00ff_00ff) | 3;
    let shifted: u32 = y >> 4;
    let narrow: u16 = shifted as u16;
    if narrow == 0 {
        let _ = narrow;
    }
}
