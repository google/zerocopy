// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

use zerocopy::transmute_ref;

fn main() {}

fn ref_dst_mutable() {
    // `transmute_ref!` requires that its destination type be an immutable
    // reference.
    let _: &mut u8 = transmute_ref!(&0u8);
}
