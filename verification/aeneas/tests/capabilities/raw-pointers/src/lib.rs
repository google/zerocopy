// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::ptr::NonNull;

pub fn cast(pointer: *const u32) -> *const u8 {
    pointer as *const u8
}

pub fn with_len(pointer: *const u8, count: usize) -> *const [u8] {
    core::ptr::slice_from_raw_parts(pointer, count)
}

pub fn nonnull(pointer: *mut u8) -> Option<NonNull<u8>> {
    NonNull::new(pointer)
}
