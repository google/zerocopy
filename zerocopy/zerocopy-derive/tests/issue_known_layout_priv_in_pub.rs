// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![deny(warnings)]

include!("include.rs");

macro_rules! foo {
    () => {
        #[derive(imp::KnownLayout)]
        #[zerocopy(crate = "zerocopy_renamed")]
        #[repr(C)]
        pub struct Foo([imp::u8]);
    };
}

foo! {}

#[test]
fn test_known_layout_priv_in_pub() {
    // Compilation is enough to verify the fix
}
