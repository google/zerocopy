// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

fn main() {
    let buf: [u32; 2] = [0; 2];
    let odd = unsafe { (buf.as_ptr() as *const u8).add(1) as *const u32 };
    let v = unsafe { odd.read() };
    let _ = v ^ 1;
}
