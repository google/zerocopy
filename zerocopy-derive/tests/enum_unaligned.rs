// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use zerocopy::Unaligned;

struct IsUnaligned<T: Unaligned>(T);

// Fail compilation if `$ty: !Unaligned`.
macro_rules! is_unaligned {
    ($ty:ty) => {
        const _: () = {
            let _: IsUnaligned<$ty>;
        };
    };
}

// An enum is `Unaligned` if:
// - No `repr(align(N > 1))`
// - `repr(u8)` or `repr(i8)`

#[derive(Unaligned)]
#[repr(u8)]
enum Foo {
    A,
}

is_unaligned!(Foo);

#[derive(Unaligned)]
#[repr(i8)]
enum Bar {
    A,
}

is_unaligned!(Bar);

#[derive(Unaligned)]
#[repr(u8, align(1))]
enum Baz {
    A,
}

is_unaligned!(Baz);

#[derive(Unaligned)]
#[repr(i8, align(1))]
enum Blah {
    B,
}

is_unaligned!(Blah);
