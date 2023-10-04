// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

use zerocopy::{transmute_ref, AsBytes};

fn main() {}

fn transmute_ref<T: AsBytes>(t: &T) -> &u8 {
    // `transmute_ref!` requires the source type to be concrete.
    transmute_ref!(t)
}
