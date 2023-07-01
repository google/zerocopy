// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[macro_use]
extern crate zerocopy;

fn main() {}

//
// Generic errors
//

#[derive(FromZeroes, FromBytes)]
#[repr("foo")]
//~^ ERROR: meta item in `repr` must be an identifier
//~| ERROR: unrecognized representation hint
enum Generic1 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(foo)]
//~^ ERROR: unrecognized representation hint
//~| ERROR: unrecognized representation hint
enum Generic2 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(transparent)]
//~^ ERROR: unsupported representation for deriving FromBytes, AsBytes, or Unaligned on an enum
enum Generic3 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(u8, u16)]
//~^ ERROR: conflicting representation hints
//~| ERROR: conflicting representation hints
enum Generic4 {
    A,
}

#[derive(FromZeroes, FromBytes)]
//~^ ERROR: must have a non-align #[repr(...)] attribute in order to guarantee this type's memory layout
enum Generic5 {
    A,
}

//
// FromZeroes errors
//

#[derive(FromZeroes)]
enum FromZeroes1 {
    //~^ ERROR: only C-like enums can implement FromZeroes
    A(u8),
}

#[derive(FromZeroes)]
enum FromZeroes2 {
    //~^ ERROR: only C-like enums can implement FromZeroes
    A,
    B(u8),
}

#[derive(FromZeroes)]
enum FromZeroes3 {
    //~^ ERROR: FromZeroes only supported on enums with a variant that has a discriminant of `0`
    A = 1,
    B,
}

//
// FromBytes errors
//

#[derive(FromZeroes, FromBytes)]
#[repr(C)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes1 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(usize)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes2 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(isize)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes3 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(u32)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes4 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(i32)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes5 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(u64)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes6 {
    A,
}

#[derive(FromZeroes, FromBytes)]
#[repr(i64)]
//~^ ERROR: FromBytes requires repr of "u8", "u16", "i8", or "i16"
enum FromBytes7 {
    A,
}

//
// Unaligned errors
//

#[derive(Unaligned)]
#[repr(C)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment
enum Unaligned1 {
    A,
}

#[derive(Unaligned)]
#[repr(u16)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned2 {
    A,
}

#[derive(Unaligned)]
#[repr(i16)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned3 {
    A,
}

#[derive(Unaligned)]
#[repr(u32)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned4 {
    A,
}

#[derive(Unaligned)]
#[repr(i32)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned5 {
    A,
}

#[derive(Unaligned)]
#[repr(u64)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned6 {
    A,
}

#[derive(Unaligned)]
#[repr(i64)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned7 {
    A,
}

#[derive(Unaligned)]
#[repr(usize)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned8 {
    A,
}

#[derive(Unaligned)]
#[repr(isize)]
//~^ ERROR: Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))
enum Unaligned9 {
    A,
}

#[derive(Unaligned)]
#[repr(u8, align(2))]
//~^ ERROR: cannot derive Unaligned with repr(align(N > 1))
enum Unaligned10 {
    A,
}

#[derive(Unaligned)]
#[repr(i8, align(2))]
//~^ ERROR: cannot derive Unaligned with repr(align(N > 1))
enum Unaligned11 {
    A,
}

#[derive(Unaligned)]
#[repr(align(1), align(2))]
//~^ ERROR: cannot derive Unaligned with repr(align(N > 1))
enum Unaligned12 {
    A,
}

#[derive(Unaligned)]
#[repr(align(2), align(4))]
//~^ ERROR: cannot derive Unaligned with repr(align(N > 1))
enum Unaligned13 {
    A,
}
