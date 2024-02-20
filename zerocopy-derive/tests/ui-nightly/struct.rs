// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[macro_use]
extern crate zerocopy;

#[path = "../include.rs"]
mod util;

use zerocopy::KnownLayout;

use self::util::util::AU16;

fn main() {}

//
// KnownLayout errors
//

struct NotKnownLayout;

struct NotKnownLayoutDst([u8]);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          N |        N |              N |        N |      KL00 |
#[derive(KnownLayout)]
struct KL00(u8, NotKnownLayoutDst);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          N |        N |              Y |        N |      KL02 |
#[derive(KnownLayout)]
struct KL02(u8, [u8]);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          Y |        N |              N |        N |      KL08 |
#[derive(KnownLayout)]
#[repr(C)]
struct KL08(u8, NotKnownLayoutDst);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          Y |        N |              N |        Y |      KL09 |
#[derive(KnownLayout)]
#[repr(C)]
struct KL09(NotKnownLayout, NotKnownLayout);

//
// NoCell errors
//

#[derive(NoCell)]
struct NoCell1 {
    a: core::cell::UnsafeCell<()>,
}

#[derive(NoCell)]
struct NoCell2 {
    a: [core::cell::UnsafeCell<u8>; 0],
}

//
// TryFromBytes errors
//

#[derive(TryFromBytes)]
#[repr(packed)]
struct TryFromBytesPacked {
    foo: AU16,
}

#[derive(TryFromBytes)]
#[repr(packed(1))]
struct TryFromBytesPackedN {
    foo: AU16,
}

#[derive(TryFromBytes)]
#[repr(C, packed)]
struct TryFromBytesCPacked {
    foo: AU16,
}

#[derive(TryFromBytes)]
#[repr(C, packed(1))]
struct TryFromBytesCPackedN {
    foo: AU16,
}

//
// IntoBytes errors
//

// Since `IntoBytes1` has at least one generic parameter, an `IntoBytes` impl is
// emitted in which each field type is given an `Unaligned` bound. Since `foo`'s
// type doesn't implement `Unaligned`, this should fail.
#[derive(IntoBytes)]
#[repr(C)]
struct IntoBytes1<T> {
    foo: AU16,
    bar: T,
}

#[derive(IntoBytes)]
#[repr(C)]
struct IntoBytes2 {
    foo: u8,
    bar: AU16,
}

#[derive(IntoBytes)]
#[repr(C, packed(2))]
struct IntoBytes3 {
    foo: u8,
    // We'd prefer to use AU64 here, but you can't use aligned types in
    // packed structs.
    bar: u64,
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
