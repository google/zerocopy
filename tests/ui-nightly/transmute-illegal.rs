// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

fn main() {}

// It is unsound to inspect the usize value of a pointer during const eval.
const POINTER_VALUE: usize = zerocopy::transmute!(&0usize as *const usize);

// `transmute!` and `try_transmute!` enforce size equality.
const TOO_LARGE: u64 = zerocopy::transmute!(0u8);
const TRY_TOO_LARGE: Option<u64> = zerocopy::try_transmute!(0u8);
const TOO_SMALL: u8 = zerocopy::transmute!(0u64);
const TRY_TOO_SMALL: Option<u8> = zerocopy::try_transmute!(0u64);
