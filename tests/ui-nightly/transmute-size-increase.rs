// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.
extern crate zerocopy;

// It is usually unsound to increase the size of a transmuted value.
const SIZE_INCREASE: [u8; 2] = zerocopy::transmute!([0u8; 1]);

fn main() {
    _ = SIZE_INCREASE;
}
