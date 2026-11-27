// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[repr(u8)]
enum SmallTag {
    A = 0,
    B = 1,
}

fn main() {
    let bad: u8 = 9;
    let _e: SmallTag = unsafe { core::mem::transmute(bad) };
}
