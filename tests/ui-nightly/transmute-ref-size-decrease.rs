// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

extern crate zerocopy;

use zerocopy::transmute_ref;

fn main() {}

// Although this is not a soundness requirement, we currently require that the
// size of the destination type is not smaller than the size of the source type.
const DECREASE_SIZE: &u8 = transmute_ref!(&[0u8; 2]);
