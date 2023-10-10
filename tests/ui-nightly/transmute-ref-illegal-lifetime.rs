// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

fn main() {}

fn increase_lifetime() {
    let x = 0u64;
    // It is illegal to increase the lifetime scope.
    let _: &'static u64 = zerocopy::transmute_ref!(&x);
}
