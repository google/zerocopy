// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use zerocopy::{AsBytes, FromBytes};

/// A type that doesn't implement any zerocopy traits.
pub struct NotZerocopy(());

/// A `u16` with alignment 2.
///
/// Though `u16` has alignment 2 on some platforms, it's not guaranteed. By
/// contrast, `AU16` is guaranteed to have alignment 2.
#[derive(FromBytes, AsBytes, Copy, Clone)]
#[repr(C, align(2))]
pub struct AU16(u16);

#[allow(unused_macros)]
macro_rules! assert_is_as_bytes {
    ($ty:ty) => {
        const _: () = {
            const fn is_as_bytes<T: zerocopy::AsBytes + ?Sized>() {}
            const _: () = is_as_bytes::<$ty>();
        };
    };
}

#[allow(unused_macros)]
macro_rules! assert_is_from_bytes {
    ($ty:ty) => {
        const _: () = {
            const fn is_from_bytes<T: zerocopy::FromBytes + ?Sized>() {}
            const _: () = is_from_bytes::<$ty>();
        };
    };
}

#[allow(unused_macros)]
macro_rules! assert_is_unaligned {
    ($ty:ty) => {
        const _: () = {
            const fn is_unaligned<T: zerocopy::Unaligned + ?Sized>() {}
            const _: () = is_unaligned::<$ty>();
        };
    };
}
