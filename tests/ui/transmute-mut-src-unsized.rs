// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy::transmute_mut;

fn main() {}

// `transmute_mut!` does not support transmuting from an unsized source type to
// a sized destination type.
const SRC_UNSIZED: &mut [u8; 1] = transmute_mut!(&mut [0u8][..]);
//~[msrv, stable]^ ERROR: the method `transmute_mut` exists for struct `Wrap<&mut [u8], &mut [u8; 1]>`, but its trait bounds were not satisfied
//~[nightly]^^ ERROR: transmute_mut` exists for struct `zerocopy::util::macro_util::Wrap<&mut [u8], &mut [u8; 1]>`, but its trait bounds were not satisfied
