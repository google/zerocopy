// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/util.rs");

extern crate zerocopy;

use zerocopy::transmute_ref;

fn main() {}

// `transmute_ref!` does not support transmuting from a type of smaller
// alignment to one of larger alignment.
const INCREASE_ALIGNMENT: &AU16 = transmute_ref!(&[0u8; 2]);
