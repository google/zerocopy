// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

unsafe extern "C" fn pre_main_ub() {
    unsafe { core::hint::unreachable_unchecked() }
}

#[used]
#[unsafe(link_section = ".init_array")]
static CTOR_ENTRY: unsafe extern "C" fn() = pre_main_ub;

fn main() {}
