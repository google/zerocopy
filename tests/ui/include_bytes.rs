// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[macro_use]
extern crate zerocopy;

fn main() {
    // Should fail because the file is 4 bytes long, not 8.
    let _: u64 = include_bytes!("../include_bytes.data");
    // Should fail because `UnsafeCell<u32>: !FromBytes`.
    let _: core::cell::UnsafeCell<u32> = include_bytes!("../include_bytes.data");
}
