// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(non_camel_case_types)]

extern crate zerocopy_renamed;

fn main() {}

type ___ZerocopyTag = [u16; 0];

#[derive(zerocopy_derive::IntoBytes)]
//~[msrv]^ ERROR: PaddingFree
//~[stable, nightly]^^ ERROR: has 1 total byte(s) of padding
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum Padded {
    Variant(___ZerocopyTag),
}

mod top_level_macro {
    macro_rules! field_type {
        () => {
            u8
        };
    }

    #[derive(zerocopy_derive::IntoBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Variant(field_type!()),
        //~[msrv, stable, nightly]^ ERROR: cannot derive `IntoBytes` for a type containing a macro invocation in a field type
    }
}

mod nested_macro {
    macro_rules! len {
        () => {
            1
        };
    }

    #[derive(zerocopy_derive::IntoBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(transparent)]
    struct Packet([u8; len!()]);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `IntoBytes` for a type containing a macro invocation in a field type
}
