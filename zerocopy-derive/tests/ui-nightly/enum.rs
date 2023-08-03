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
enum Generic1 {
    A,
}

#[derive(FromBytes)]
#[repr(foo)]
enum Generic2 {
    A,
}

#[derive(FromBytes)]
#[repr(transparent)]
enum Generic3 {
    A,
}

#[derive(FromBytes)]
#[repr(u8, u16)]
enum Generic4 {
    A,
}

#[derive(FromBytes)]
enum Generic5 {
    A,
}

//
// FromBytes errors
//

#[derive(FromBytes)]
#[repr(C)]
enum FromBytes1 {
    A,
}

#[derive(FromBytes)]
#[repr(usize)]
enum FromBytes2 {
    A,
}

#[derive(FromBytes)]
#[repr(isize)]
enum FromBytes3 {
    A,
}

#[derive(FromBytes)]
#[repr(u32)]
enum FromBytes4 {
    A,
}

#[derive(FromBytes)]
#[repr(i32)]
enum FromBytes5 {
    A,
}

#[derive(FromBytes)]
#[repr(u64)]
enum FromBytes6 {
    A,
}

#[derive(FromBytes)]
#[repr(i64)]
enum FromBytes7 {
    A,
}

//
// Unaligned errors
//

#[derive(Unaligned)]
#[repr(C)]
enum Unaligned1 {
    A,
}

#[derive(Unaligned)]
#[repr(u16)]
enum Unaligned2 {
    A,
}

#[derive(Unaligned)]
#[repr(i16)]
enum Unaligned3 {
    A,
}

#[derive(Unaligned)]
#[repr(u32)]
enum Unaligned4 {
    A,
}

#[derive(Unaligned)]
#[repr(i32)]
enum Unaligned5 {
    A,
}

#[derive(Unaligned)]
#[repr(u64)]
enum Unaligned6 {
    A,
}

#[derive(Unaligned)]
#[repr(i64)]
enum Unaligned7 {
    A,
}

#[derive(Unaligned)]
#[repr(usize)]
enum Unaligned8 {
    A,
}

#[derive(Unaligned)]
#[repr(isize)]
enum Unaligned9 {
    A,
}

#[derive(Unaligned)]
#[repr(u8, align(2))]
enum Unaligned10 {
    A,
}

#[derive(Unaligned)]
#[repr(i8, align(2))]
enum Unaligned11 {
    A,
}

#[derive(Unaligned)]
#[repr(align(1), align(2))]
enum Unaligned12 {
    A,
}

#[derive(Unaligned)]
#[repr(align(2), align(4))]
enum Unaligned13 {
    A,
}
