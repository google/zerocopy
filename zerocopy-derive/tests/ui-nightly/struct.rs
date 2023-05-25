// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[macro_use]
extern crate zerocopy;

#[path = "../util.rs"]
mod util;

use self::util::AU16;

fn main() {}

//
// AsBytes errors
//

#[derive(AsBytes)]
#[repr(C)]
struct AsBytes1<T>(T);

#[derive(AsBytes)]
#[repr(C)]
struct AsBytes2 {
    foo: u8,
    bar: AU16,
}

//
// Unaligned errors
//

#[derive(Unaligned)]
#[repr(C, align(2))]
struct Unaligned1;

#[derive(Unaligned)]
#[repr(transparent, align(2))]
struct Unaligned2 {
    foo: u8,
}

#[derive(Unaligned)]
#[repr(packed, align(2))]
struct Unaligned3;

#[derive(Unaligned)]
#[repr(align(1), align(2))]
struct Unaligned4;

#[derive(Unaligned)]
#[repr(align(2), align(4))]
struct Unaligned5;
