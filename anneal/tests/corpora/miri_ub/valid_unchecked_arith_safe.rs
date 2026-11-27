// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

fn main() {
    let a: i32 = unsafe { 40i32.unchecked_add(2) };
    let b: i32 = unsafe { a.unchecked_sub(7) };
    let c: i32 = unsafe { b.unchecked_mul(3) };
    let _ = c ^ 5;
}
