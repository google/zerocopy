// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

use zerocopy::transmute;

fn main() {}

// It is unclear whether we can or should support this transmutation, especially
// in a const context. This test ensures that even if such a transmutation
// becomes valid due to the requisite implementations of `FromBytes` being
// added, that we re-examine whether it should specifically be valid in a const
// context.
const POINTER_VALUE: usize = transmute!(&0usize as *const usize);
