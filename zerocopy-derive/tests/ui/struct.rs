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

use zerocopy_renamed::{IntoBytes, KnownLayout};

use self::util::util::AU16;

fn main() {}

//
// KnownLayout errors
//

struct NotKnownLayout;

struct NotKnownLayoutDst([u8]);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          N |        N |              N |        N |      KL00 |
//@[stable, nightly]~ ERROR: the size for values of type `[u8]` cannot be known at compilation time
#[derive(KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
struct KL00(u8, NotKnownLayoutDst);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          N |        N |              Y |        N |      KL02 |
//@[stable, nightly]~ ERROR: the size for values of type `[u8]` cannot be known at compilation time
#[derive(KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
struct KL02(u8, [u8]);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          Y |        N |              N |        N |      KL08 |
//@[stable, nightly]~ ERROR: the trait bound `NotKnownLayoutDst: zerocopy_renamed::KnownLayout` is not satisfied
#[derive(KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct KL08(u8, NotKnownLayoutDst);

// | `repr(C)`? | generic? | `KnownLayout`? | `Sized`? | Type Name |
// |          Y |        N |              N |        Y |      KL09 |
//@[stable, nightly]~ ERROR: the trait bound `NotKnownLayout: zerocopy_renamed::KnownLayout` is not satisfied
#[derive(KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct KL09(NotKnownLayout, NotKnownLayout);

//
// Immutable errors
//

//@[stable, nightly]~ ERROR: the trait bound `UnsafeCell<()>: zerocopy_renamed::Immutable` is not satisfied
#[derive(Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
struct Immutable1 {
    a: core::cell::UnsafeCell<()>,
}

//@[stable, nightly]~ ERROR: the trait bound `UnsafeCell<u8>: zerocopy_renamed::Immutable` is not satisfied
#[derive(Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
struct Immutable2 {
    a: [core::cell::UnsafeCell<u8>; 0],
}

//
// TryFromBytes errors
//

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed)]
//@[stable, nightly]~ ERROR: packed type cannot transitively contain a `#[repr(align)]` type
struct TryFromBytesPacked {
    foo: AU16,
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed(1))]
//@[stable, nightly]~ ERROR: packed type cannot transitively contain a `#[repr(align)]` type
struct TryFromBytesPackedN {
    foo: AU16,
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed)]
//@[stable, nightly]~ ERROR: packed type cannot transitively contain a `#[repr(align)]` type
struct TryFromBytesCPacked {
    foo: AU16,
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed(1))]
//@[stable, nightly]~ ERROR: packed type cannot transitively contain a `#[repr(align)]` type
struct TryFromBytesCPackedN {
    foo: AU16,
}

//
// IntoBytes errors
//

// Since `IntoBytes1` has at least one generic parameter, an `IntoBytes` impl is
// emitted in which each field type is given an `Unaligned` bound. Since `foo`'s
// type doesn't implement `Unaligned`, this should fail.
//@[stable, nightly]~ ERROR: the trait bound `AU16: zerocopy_renamed::Unaligned` is not satisfied
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct IntoBytes1<T> {
    foo: AU16,
    bar: T,
}

//@[stable, nightly]~ ERROR: `IntoBytes2` has 1 total byte(s) of padding
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct IntoBytes2 {
    foo: u8,
    bar: AU16,
}

//@[stable, nightly]~ ERROR: `IntoBytes3` has 1 total byte(s) of padding
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed(2))]
struct IntoBytes3 {
    foo: u8,
    // We'd prefer to use AU64 here, but you can't use aligned types in
    // packed structs.
    bar: u64,
}

type SliceU8 = [u8];

// Padding between `u8` and `SliceU8`. `SliceU8` doesn't syntactically look like
// a slice, so this case is handled by our `Sized` support.
//
// NOTE(#1708): This exists to ensure that our error messages are good when a
// field is unsized.
//@[stable, nightly]~ ERROR: the size for values of type `[u8]` cannot be known at compilation time
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct IntoBytes4 {
    a: u8,
    //@[stable, nightly]~ ERROR: `[u8]` is unsized
    b: SliceU8,
}

// Padding between `u8` and `[u16]`. `[u16]` is syntactically identifiable as a
// slice, so this case is handled by our `repr(C)` slice DST support.
//@[msrv]~ ERROR: the trait bound `(): DynamicPaddingFree<IntoBytes5, true>` is not satisfied
//@[stable, nightly]~ ERROR: `IntoBytes5` has one or more padding bytes
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct IntoBytes5 {
    a: u8,
    b: [u16],
}

// Trailing padding after `[u8]`. `[u8]` is syntactically identifiable as a
// slice, so this case is handled by our `repr(C)` slice DST support.
//@[msrv]~ ERROR: the trait bound `(): DynamicPaddingFree<IntoBytes6, true>` is not satisfied
//@[stable, nightly]~ ERROR: `IntoBytes6` has one or more padding bytes
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct IntoBytes6 {
    a: u16,
    b: [u8],
}

// Padding between `u8` and `u16` and also trailing padding after `[u8]`. `[u8]`
// is syntactically identifiable as a slice, so this case is handled by our
// `repr(C)` slice DST support.
//@[msrv]~ ERROR: the trait bound `(): DynamicPaddingFree<IntoBytes7, true>` is not satisfied
//@[stable, nightly]~ ERROR: `IntoBytes7` has one or more padding bytes
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct IntoBytes7 {
    a: u8,
    b: u16,
    c: [u8],
}

#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[msrv, stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(C, C)] // zerocopy-derive conservatively treats these as conflicting reprs
struct IntoBytes8 {
    a: u8,
}

//@[stable, nightly]~ ERROR: must have a non-align #[repr(...)] attribute in order to guarantee this type's memory layout
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
struct IntoBytes9<T> {
    t: T,
}

//@[stable, nightly]~ ERROR: must have a non-align #[repr(...)] attribute in order to guarantee this type's memory layout
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed(2))]
struct IntoBytes10<T> {
    t: T,
}

// `repr(C, packed(2))` is not equivalent to `repr(C, packed)`.
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed(2))]
struct IntoBytes11<T> {
    t0: T,
    // Add a second field to avoid triggering the "repr(C) struct with one
    // field" special case.
    t1: T,
}

fn is_into_bytes_11<T: IntoBytes>() {
    if false {
        //@[stable, nightly]~ ERROR: the trait bound `AU16: zerocopy_renamed::Unaligned` is not satisfied
        is_into_bytes_11::<IntoBytes11<AU16>>();
    }
}

// `repr(C, align(2))` is not sufficient to guarantee the layout of this type.
//@[stable, nightly]~ ERROR: must have a non-align #[repr(...)] attribute in order to guarantee this type's memory layout
#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, align(2))]
struct IntoBytes12<T> {
    t: T,
}

//
// Unaligned errors
//

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[stable, nightly]~ ERROR: cannot derive `Unaligned` on type with alignment greater than 1
#[repr(C, align(2))]
struct Unaligned1;

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[stable, nightly]~ ERROR: this conflicts with another representation hint
//@[stable, nightly]~ ERROR: transparent struct cannot have other repr hints
#[repr(transparent, align(2))]
struct Unaligned2 {
    foo: u8,
}

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(packed, align(2))]
//@[stable, nightly]~ ERROR: type has conflicting packed and align representation hints
struct Unaligned3;

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(align(1), align(2))]
struct Unaligned4;

#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[stable, nightly]~ ERROR: this conflicts with another representation hint
#[repr(align(2), align(4))]
struct Unaligned5;

//@[stable, nightly]~ ERROR: must have #[repr(C)], #[repr(transparent)], or #[repr(packed)] attribute in order to guarantee this type's alignment
#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
struct Unaligned6;

//@[stable, nightly]~ ERROR: must have #[repr(C)], #[repr(transparent)], or #[repr(packed)] attribute in order to guarantee this type's alignment
#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(packed(2))]
struct Unaligned7;

// Test the error message emitted when conflicting reprs appear on different
// lines. On the nightly compiler, this emits a "joint span" that spans both
// problematic repr token trees and everything in between.
#[derive(Copy, Clone)]
//@[nightly]~ ERROR: this conflicts with another representation hint
#[repr(packed(2), C)]
#[derive(Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
//@[stable]~ ERROR: this conflicts with another representation hint
#[repr(C, packed(2))]
struct WeirdReprSpan;

//@[msrv, stable, nightly]~ ERROR: the trait bound `SplitAtNotKnownLayout: zerocopy_renamed::KnownLayout` is not satisfied
#[derive(SplitAt)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct SplitAtNotKnownLayout([u8]);

//@[msrv, stable, nightly]~ ERROR: the trait bound `u8: SplitAt` is not satisfied
//@[msrv]~ ERROR: type mismatch resolving `<u8 as zerocopy_renamed::KnownLayout>::PointerMetadata == usize`
#[derive(SplitAt, KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct SplitAtSized(u8);
