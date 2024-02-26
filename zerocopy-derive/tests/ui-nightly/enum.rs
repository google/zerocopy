// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

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
// NoCell errors
//

#[derive(NoCell)]
enum NoCell1 {
    A(core::cell::UnsafeCell<()>),
}

#[derive(NoCell)]
enum Never {}

#[derive(NoCell)]
enum NoCell2 {
    Uninhabited(Never, core::cell::UnsafeCell<u8>),
    Inhabited(u8),
}

//
// TryFromBytes errors
//

#[derive(TryFromBytes)]
enum TryFromBytes1 {
    A,
}

#[derive(TryFromBytes)]
#[repr(u8)]
enum TryFromBytes2 {
    A(u8),
}

//
// FromZeros errors
//

#[derive(FromZeros)]
enum FromZeros1 {
    A(u8),
}

#[derive(FromZeros)]
enum FromZeros2 {
    A,
    B(u8),
}

#[derive(FromZeros)]
enum FromZeros3 {
    A = 1,
    B,
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
