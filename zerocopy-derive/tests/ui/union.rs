// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[macro_use]
extern crate zerocopy_renamed;

#[path = "../include.rs"]
mod util;

use std::mem::ManuallyDrop;

use self::util::util::AU16;

fn main() {}

//
// Immutable errors
//

//@[msrv, stable, nightly]~ ERROR: the trait bound `UnsafeCell<()>: zerocopy_renamed::Immutable` is not satisfied
#[derive(Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
union Immutable1 {
    a: ManuallyDrop<core::cell::UnsafeCell<()>>,
}

//
// IntoBytes errors
//

//@[msrv, stable, nightly]~ ERROR: unsupported on types with type parameters
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
union IntoBytes1<T> {
    foo: ManuallyDrop<T>,
}

//@[msrv]~ ERROR: the trait bound `(): PaddingFree<IntoBytes2, 1_usize>` is not satisfied
//@[stable, nightly]~ ERROR: `IntoBytes2` has 1 total byte(s) of padding
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
union IntoBytes2 {
    foo: u8,
    bar: [u8; 2],
}

// Need a `repr` attribute
//@[msrv, stable, nightly]~ ERROR: must be #[repr(C)], #[repr(packed)], or #[repr(transparent)]
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
union IntoBytes3 {
    foo: u8,
}

// `repr(packed(2))` isn't equivalent to `repr(packed)`
//@[msrv, stable, nightly]~ ERROR: must be #[repr(C)], #[repr(packed)], or #[repr(transparent)]
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed(2))]
union IntoBytes4 {
    foo: u8,
}

//
// Unaligned errors
//

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[msrv, stable, nightly]~ ERROR: cannot derive `Unaligned` on type with alignment greater than 1
#[repr(C, align(2))]
union Unaligned1 {
    foo: i16,
    bar: AU16,
}

// Transparent unions are unstable; see issue #60405
// <https://github.com/rust-lang/rust/issues/60405> for more information.

// #[derive(Unaligned)]
// #[repr(transparent, align(2))]
// union Unaligned2 {
//     foo: u8,
// }

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[msrv, stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(packed, align(2))]
//@[stable, nightly]~ ERROR: type has conflicting packed and align representation hints
union Unaligned3 {
    foo: u8,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[msrv, stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(align(1), align(2))]
struct Unaligned4 {
    foo: u8,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[msrv, stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(align(2), align(4))]
struct Unaligned5 {
    foo: u8,
}

//@[msrv, stable, nightly]~ ERROR: must have #[repr(C)], #[repr(transparent)], or #[repr(packed)] attribute in order to guarantee this type's alignment
#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
union Unaligned6 {
    foo: i16,
    bar: AU16,
}

//@[msrv, stable, nightly]~ ERROR: must have #[repr(C)], #[repr(transparent)], or #[repr(packed)] attribute in order to guarantee this type's alignment
#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed(2))]
//@[stable, nightly]~ ERROR: packed type cannot transitively contain a `#[repr(align)]` type
union Unaligned7 {
    foo: i16,
    bar: AU16,
}
