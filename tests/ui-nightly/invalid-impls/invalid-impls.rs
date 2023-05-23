// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// Since some macros from `macros.rs` are unused.
#![allow(unused)]

extern crate zerocopy;
extern crate zerocopy_derive;

include!("../../../src/macros.rs");

use zerocopy::*;
use zerocopy_derive::*;

fn main() {}

#[derive(FromZeroes, FromBytes, AsBytes, Unaligned)]
#[repr(transparent)]
struct Foo<T>(T);

impl_or_verify!(T => FromZeroes for Foo<T>);
impl_or_verify!(T => FromBytes for Foo<T>);
impl_or_verify!(T => AsBytes for Foo<T>);
impl_or_verify!(T => Unaligned for Foo<T>);
