// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/include.rs");

#[macro_use]
extern crate zerocopy;

use util::NotZerocopy;

fn main() {}

// Should fail because `NotZerocopy<u32>: !FromBytes`.
const NOT_FROM_BYTES: NotZerocopy<u32> = include_value!("../../testdata/include_value/data");
