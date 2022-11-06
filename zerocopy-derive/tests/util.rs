// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use zerocopy::AsBytes;

// A `u16` with alignment 2.
//
// Though `u16` has alignment 2 on some platforms, it's not guaranteed.
// By contrast, `AU16` is guaranteed to have alignment 2.
#[derive(AsBytes, Copy, Clone)]
#[repr(C, align(2))]
pub struct AU16(u16);

#[allow(unused_macros)]
macro_rules! assert_is_as_bytes {
    ($ty:ty) => {
        const _: () = {
            struct IsAsBytes<T: zerocopy::AsBytes>(T);
            const _: fn($ty) -> IsAsBytes<$ty> = IsAsBytes::<$ty>;
        };
    };
}

#[allow(unused_macros)]
macro_rules! assert_is_from_bytes {
    ($ty:ty) => {
        const _: () = {
            struct IsFromBytes<T: zerocopy::FromBytes>(T);
            const _: fn($ty) -> IsFromBytes<$ty> = IsFromBytes::<$ty>;
        };
    };
}

#[allow(unused_macros)]
macro_rules! assert_is_unaligned {
    ($ty:ty) => {
        const _: () = {
            struct IsUnaligned<T: zerocopy::Unaligned>(T);
            const _: fn($ty) -> IsUnaligned<$ty> = IsUnaligned::<$ty>;
        };
    };
}
