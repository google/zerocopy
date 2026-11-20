// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

pub struct UnusedUnmodeled {
    pub label: &'static str,
}

fn clamp_gap(a: u32, b: u32) -> u32 {
    let d = a.saturating_sub(b);
    core::cmp::min(d.leading_zeros(), 16)
}

pub fn selected(a: u32, b: u32) -> u32 {
    clamp_gap(a, b)
}
