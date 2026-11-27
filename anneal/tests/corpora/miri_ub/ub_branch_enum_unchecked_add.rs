// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[repr(u8)]
enum Mode {
    Safe = 1,
    Overflow = 2,
}

const SELECTED: Mode = Mode::Overflow;

fn main() {
    let rhs: i32 = match SELECTED {
        Mode::Safe => 1,
        Mode::Overflow => i32::MAX,
    };
    let _ = unsafe { 1i32.unchecked_add(rhs) };
}
