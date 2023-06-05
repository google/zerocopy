// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.
extern crate zerocopy;

include!("../../zerocopy-derive/tests/util.rs");

// The source type must be `FromBytes`.
const DST_NOT_FROM_BYTES: NotZerocopy<AU16> = zerocopy::transmute!(AU16(0));

fn main() {
    _ = DST_NOT_FROM_BYTES;
}
