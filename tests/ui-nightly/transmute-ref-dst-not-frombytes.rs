// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/util.rs");

extern crate zerocopy;

use zerocopy::transmute_ref;

fn main() {}

// `transmute_ref` requires that the destination type implements `FromBytes`
const DST_NOT_FROM_BYTES: &NotZerocopy = transmute_ref!(&AU16(0));
