// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/util.rs");

extern crate zerocopy;

use zerocopy::transmute;

fn main() {}

// `transmute!` does not support transmuting from a smaller type to a larger
// one.
const INCREASE_SIZE: AU16 = transmute!(0u8);
