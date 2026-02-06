// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

use zerocopy::transmute_mut;

fn main() {}

const ARRAY_OF_U8S: [u8; 2] = [0u8; 2];

// `transmute_mut!` cannot, generally speaking, be used in const contexts.
//@[msrv]~ ERROR: mutable references are not allowed in constants
//@[msrv]~ ERROR: calls in constants are limited to constant functions, tuple structs and tuple variants
//@[msrv]~ ERROR: temporary value dropped while borrowed
//@[stable]~ ERROR: cannot call non-const method `Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut_inference_helper` in constants
//@[stable]~ ERROR: cannot call non-const method `Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut` in constants
//@[nightly]~ ERROR: cannot call non-const method `zerocopy::util::macro_util::Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut_inference_helper` in constants
//@[nightly]~ ERROR: cannot call non-const method `zerocopy::util::macro_util::Wrap::<&mut [u8; 2], &mut [u8; 2]>::transmute_mut` in constants
const CONST_CONTEXT: &mut [u8; 2] = transmute_mut!(&mut ARRAY_OF_U8S);
