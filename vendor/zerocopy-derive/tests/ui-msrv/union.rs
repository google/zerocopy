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

#[derive(Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
union Immutable1 {
    a: ManuallyDrop<core::cell::UnsafeCell<()>>,
}

//
// IntoBytes errors
//

#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
union IntoBytes1<T> {
    foo: ManuallyDrop<T>,
}

#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
union IntoBytes2 {
    foo: u8,
    bar: [u8; 2],
}

// Need a `repr` attribute
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
union IntoBytes3 {
    foo: u8,
}

// `repr(packed(2))` isn't equivalent to `repr(packed)`
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
#[repr(packed, align(2))]
union Unaligned3 {
    foo: u8,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(align(1), align(2))]
struct Unaligned4 {
    foo: u8,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(align(2), align(4))]
struct Unaligned5 {
    foo: u8,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
union Unaligned6 {
    foo: i16,
    bar: AU16,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed(2))]
union Unaligned7 {
    foo: i16,
    bar: AU16,
}
