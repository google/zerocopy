// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

fn main() {}

// It is unsound to inspect the usize value of a pointer during const eval.
const POINTER_VALUE: usize = zerocopy::transmute!(&0usize as *const usize);
