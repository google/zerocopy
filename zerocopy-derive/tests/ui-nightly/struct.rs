// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[macro_use]
extern crate zerocopy;

#[path = "../util.rs"]
mod util;

use static_assertions::assert_impl_all;
use zerocopy::KnownLayout;

use self::util::AU16;

fn main() {}

//
// KnownLayout errors
//

#[derive(KnownLayout)]
struct KnownLayout1([u8]);

assert_impl_all!(KnownLayout1: KnownLayout);

#[derive(KnownLayout)]
struct KnownLayout2<T: ?Sized>(T);

assert_impl_all!(KnownLayout2<[u8]>: KnownLayout);

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
