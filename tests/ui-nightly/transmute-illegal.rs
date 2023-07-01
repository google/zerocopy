// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

include!("../../zerocopy-derive/tests/util.rs");

extern crate zerocopy;

use zerocopy::transmute;

fn main() {}

// It is unsupported to inspect the usize value of a pointer during const eval.
const POINTER_VALUE: usize = transmute!(&0usize as *const usize);
//~^ ERROR: the trait bound `*const usize: AsBytes` is not satisfied

const SRC_NOT_AS_BYTES: AU16 = transmute!(NotZerocopy(AU16(0)));
//~^ ERROR: the trait bound `NotZerocopy<AU16>: AsBytes` is not satisfied

const DST_NOT_FROM_BYTES: NotZerocopy<AU16> = transmute!(AU16(0));
//~^ ERROR: the trait bound `NotZerocopy<AU16>: FromBytes` is not satisfied

const INCREASE_SIZE: AU16 = transmute!(0u8);
//~^ ERROR: cannot transmute between types of different sizes, or dependently-sized types

const DECREASE_SIZE: u8 = transmute!(AU16(0));
//~^ ERROR: cannot transmute between types of different sizes, or dependently-sized types
