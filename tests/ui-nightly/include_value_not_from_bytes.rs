// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/util.rs");

#[macro_use]
extern crate zerocopy;

fn main() {}

// Should fail because `NotZerocopy<u32>: !FromBytes`.
const NOT_FROM_BYTES: NotZerocopy<u32> = include_value!("../../testdata/include_value/data");
