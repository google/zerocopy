// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/util.rs");

extern crate zerocopy;

use zerocopy::transmute;

fn main() {}

// `transmute` requires that the source type implements `AsBytes`
const SRC_NOT_AS_BYTES: AU16 = transmute!(NotZerocopy(AU16(0)));
