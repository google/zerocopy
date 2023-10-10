// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

use zerocopy::transmute_ref;

fn main() {}

// `transmute_ref!` does not support transmuting from a smaller type to a larger
// one.
const INCREASE_SIZE: &[u8; 2] = transmute_ref!(&0u8);
