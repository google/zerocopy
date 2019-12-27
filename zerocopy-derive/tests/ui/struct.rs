// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[macro_use]
extern crate zerocopy;

fn main() {}

//
// Generic errors
//

#[derive(FromBytes)]
#[repr("foo")]
struct Generic1;

#[derive(FromBytes)]
#[repr(foo)]
struct Generic2;

#[derive(FromBytes)]
#[repr(u8)]
struct Generic3;

#[derive(FromBytes)]
#[repr(i8)]
struct Generic4;

#[derive(FromBytes)]
#[repr(u16)]
struct Generic5;

#[derive(FromBytes)]
#[repr(i16)]
struct Generic6;

#[derive(FromBytes)]
#[repr(u32)]
struct Generic7;

#[derive(FromBytes)]
#[repr(i32)]
struct Generic8;

#[derive(FromBytes)]
#[repr(u64)]
struct Generic9;

#[derive(FromBytes)]
#[repr(i64)]
struct Generic10;

#[derive(FromBytes)]
#[repr(usize)]
struct Generic11;

#[derive(FromBytes)]
#[repr(isize)]
struct Generic12;

#[derive(FromBytes)]
#[repr(transparent, packed)]
struct Generic14;

#[derive(FromBytes)]
#[repr(C, transparent)]
struct Generic15;

#[derive(FromBytes)]
struct Generic16;

//
// FromBytes errors
//

#[derive(FromBytes)]
#[repr(packed)]
struct FromBytes1;

//
// AsBytes errors
//

#[derive(AsBytes)]
#[repr(C)]
struct AsBytes1<T>(T);

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
