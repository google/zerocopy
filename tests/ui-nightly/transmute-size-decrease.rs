// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.
extern crate zerocopy;

// It is unsupported to decrease the size of a transmuted value.
const SIZE_DECREASE: [u8; 1] = zerocopy::transmute!([0u8; 2]);

fn main() {
    _ = SIZE_DECREASE;
}
