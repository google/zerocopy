// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use zerocopy::{AsBytes, FromBytes, FromZeroes, Unaligned};

// Ensure that types that are use'd and types that are referenced by path work.

mod foo {
    use zerocopy::{AsBytes, FromBytes, FromZeroes, Unaligned};

    #[derive(FromZeroes, FromBytes, AsBytes, Unaligned)]
    #[repr(C)]
    pub struct Foo {
        foo: u8,
    }

    #[derive(FromZeroes, FromBytes, AsBytes, Unaligned)]
    #[repr(C)]
    pub struct Bar {
        bar: u8,
    }
}

use foo::Foo;

#[derive(FromZeroes, FromBytes, AsBytes, Unaligned)]
#[repr(C)]
struct Baz {
    foo: Foo,
    bar: foo::Bar,
}
