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

mod known_layout_direct {
    type __Zerocopy_Field_header = [u8; 8];

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet {
        header: __Zerocopy_Field_header,
        //~[msrv, stable, nightly]^ ERROR: cannot derive `KnownLayout` because the unqualified identifier `__Zerocopy_Field_header` is reserved for generated code
        bytes: [u8],
    }
}

mod known_layout_nested_macro {
    macro_rules! len {
        () => {
            8
        };
    }

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet {
        header: [u8; len!()],
        //~[msrv, stable, nightly]^ ERROR: cannot derive `KnownLayout` for a type containing a macro invocation in a field type
        bytes: [u8],
    }
}

mod known_layout_macro {
    type __Zerocopy_Field_header = [u8; 8];

    macro_rules! header {
        () => {
            __Zerocopy_Field_header
        };
    }

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet {
        header: header!(),
        //~[msrv, stable, nightly]^ ERROR: cannot derive `KnownLayout` for a type containing a macro invocation in a field type
        bytes: [u8],
    }
}

mod known_layout_qualified {
    mod types {
        pub type __Zerocopy_Field_header = [u8; 8];
    }

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet {
        header: crate::known_layout_qualified::types::__Zerocopy_Field_header,
        bytes: [u8],
    }
}

mod known_layout_generic_marker_capture {
    trait Assoc {
        type Type;
    }

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet<__Zerocopy_Field_header>
    //~^ ERROR: cannot derive `KnownLayout` because the unqualified identifier `__Zerocopy_Field_header` is reserved for generated code
    where
        Self: Assoc,
    {
        header: <Self as Assoc>::Type,
        bytes: [u8],
    }
}

mod known_layout_use_root {
    type __Zerocopy_Field_0 = u8;

    #[derive(zerocopy_derive::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet(
        [u8; {
            use __Zerocopy_Field_0 as T;
            //~[msrv, stable, nightly]^ ERROR: cannot derive `KnownLayout` because the unqualified identifier `__Zerocopy_Field_0` is reserved for generated code
            core::mem::size_of::<T>()
        }],
        [u8],
    );
}
