// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code, unused_braces)]

extern crate zerocopy_renamed;

fn main() {}

macro_rules! field_type {
    () => {
        u8
    };
}

trait Select<const N: usize> {
    type Assoc;
}

macro_rules! selection {
    () => {
        0
    };
}

mod immutable {
    #[derive(zerocopy_derive::Immutable)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct Value(field_type!());
    //~[msrv, stable, nightly]^ ERROR: cannot derive `Immutable` for a type containing a macro invocation in a field type
}

mod from_zeros {
    #[derive(zerocopy_derive::FromZeros)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct Value(field_type!());
    //~[msrv, stable, nightly]^ ERROR: cannot derive `FromZeros` for a type containing a macro invocation in a field type
}

mod from_bytes {
    #[derive(zerocopy_derive::FromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct Value(field_type!());
    //~[msrv, stable, nightly]^ ERROR: cannot derive `FromBytes` for a type containing a macro invocation in a field type
}

mod unaligned {
    #[derive(zerocopy_derive::Unaligned)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Value(field_type!());
    //~[msrv, stable, nightly]^ ERROR: cannot derive `Unaligned` for a type containing a macro invocation in a field type
}

mod split_at {
    macro_rules! trailing_type {
        () => {
            [u8]
        };
    }

    #[derive(zerocopy_derive::SplitAt)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Value(u8, trailing_type!());
    //~[msrv, stable, nightly]^ ERROR: cannot derive `SplitAt` for a type containing a macro invocation in a field type
}

mod generic_bounds {
    use super::Select;

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct KnownLayout<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `KnownLayout` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::Immutable)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct Immutable<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `Immutable` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct TryFromBytes<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::FromZeros)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct FromZeros<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `FromZeros` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::FromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct FromBytes<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `FromBytes` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::IntoBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(transparent)]
    struct IntoBytes<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `IntoBytes` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::Unaligned)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Unaligned<T: Select<{ selection!() }>>(T::Assoc);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `Unaligned` for a type containing a macro invocation in generic parameters or predicates

    #[derive(zerocopy_derive::SplitAt)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct SplitAt<T: Select<{ selection!() }>>(u8, [T::Assoc]);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `SplitAt` for a type containing a macro invocation in generic parameters or predicates
}
