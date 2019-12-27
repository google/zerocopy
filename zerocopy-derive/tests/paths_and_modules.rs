// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![allow(warnings)]

use zerocopy::FromBytes;

// Ensure that types that are use'd and types that are referenced by path work.

mod foo {
    use zerocopy::FromBytes;

    #[derive(FromBytes)]
    #[repr(C, align(8))]
    pub struct Foo {
        foo: u8,
    }

    #[derive(FromBytes)]
    #[repr(C)]
    pub struct Bar {
        bar: u8,
    }
}

use foo::Foo;

#[derive(FromBytes)]
#[repr(C)]
struct Baz {
    foo: Foo,
    bar: foo::Bar,
}
