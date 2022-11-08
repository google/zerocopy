// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

#[macro_use]
mod util;

use std::{marker::PhantomData, mem::ManuallyDrop, option::IntoIter};

use zerocopy::AsBytes;

use self::util::AU16;

// A struct is `AsBytes` if:
// - all fields are `AsBytes`
// - `repr(C)` or `repr(transparent)` and
//   - no padding (size of struct equals sum of size of field types)
// - `repr(packed)`

#[derive(AsBytes)]
#[repr(C)]
struct CZst;

assert_is_as_bytes!(CZst);

#[derive(AsBytes)]
#[repr(C)]
struct C {
    a: u8,
    b: u8,
    c: AU16,
}

assert_is_as_bytes!(C);

#[derive(AsBytes)]
#[repr(transparent)]
struct Transparent {
    a: u8,
    b: CZst,
}

assert_is_as_bytes!(Transparent);

#[derive(AsBytes)]
#[repr(transparent)]
struct TransparentGeneric<T: ?Sized> {
    a: CZst,
    b: T,
}

assert_is_as_bytes!(TransparentGeneric<u64>);
assert_is_as_bytes!(TransparentGeneric<[u64]>);

#[derive(AsBytes)]
#[repr(C, packed)]
struct CZstPacked;

assert_is_as_bytes!(CZstPacked);

#[derive(AsBytes)]
#[repr(C, packed)]
struct CPacked {
    a: u8,
    // NOTE: The `u16` type is not guaranteed to have alignment 2, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(2))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u16` here. Luckily, these tests run in CI on
    // platforms on which `u16` has alignment 2, so this isn't that big of a
    // deal.
    b: u16,
}

assert_is_as_bytes!(CPacked);

#[derive(AsBytes)]
#[repr(C, packed)]
struct CPackedGeneric<T, U: ?Sized> {
    t: T,
    // Unsized types stored in `repr(packed)` structs must not be dropped
    // because dropping them in-place might be unsound depending on the
    // alignment of the outer struct. Sized types can be dropped by first being
    // moved to an aligned stack variable, but this isn't possible with unsized
    // types.
    u: ManuallyDrop<U>,
}

assert_is_as_bytes!(CPackedGeneric<u8, AU16>);
assert_is_as_bytes!(CPackedGeneric<u8, [AU16]>);

#[derive(AsBytes)]
#[repr(packed)]
struct Packed {
    a: u8,
    // NOTE: The `u16` type is not guaranteed to have alignment 2, although it
    // does on many platforms. However, to fix this would require a custom type
    // with a `#[repr(align(2))]` attribute, and `#[repr(packed)]` types are not
    // allowed to transitively contain `#[repr(align(...))]` types. Thus, we
    // have no choice but to use `u16` here. Luckily, these tests run in CI on
    // platforms on which `u16` has alignment 2, so this isn't that big of a
    // deal.
    b: u16,
}

assert_is_as_bytes!(Packed);

#[derive(AsBytes)]
#[repr(packed)]
struct PackedGeneric<T, U: ?Sized> {
    t: T,
    // Unsized types stored in `repr(packed)` structs must not be dropped
    // because dropping them in-place might be unsound depending on the
    // alignment of the outer struct. Sized types can be dropped by first being
    // moved to an aligned stack variable, but this isn't possible with unsized
    // types.
    u: ManuallyDrop<U>,
}

assert_is_as_bytes!(PackedGeneric<u8, AU16>);
assert_is_as_bytes!(PackedGeneric<u8, [AU16]>);

#[derive(AsBytes)]
#[repr(transparent)]
struct Unsized {
    a: [u8],
}

assert_is_as_bytes!(Unsized);
