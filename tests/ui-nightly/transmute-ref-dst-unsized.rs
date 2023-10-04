// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

use zerocopy::transmute_ref;

fn main() {}

// `transmute_ref!` does not support transmuting into an unsized destination
// type.
const DST_UNSIZED: &[u8] = transmute_ref!(&[0u8; 1]);
