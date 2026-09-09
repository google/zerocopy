// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code, unused_macros)]
#![forbid(unsafe_code)]

macro_rules! field_type {
    () => {
        u8
    };
}

#[repr(transparent)]
struct CfgAttr(bool);

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` does not support `cfg_attr`
    #[repr(C)]
    #[cfg_attr(all(), cfg(any()))]
    struct CfgAttr(u8);
}

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports `cfg`, `derive`, `allow`, and `doc` attributes
    #[repr(C)]
    #[deprecated]
    struct Unsupported(u8);
}

// A captured type fragment is expanded separately each time it is
// transcribed. In particular, a stateful function-like proc macro could
// expand to different types in the declaration and the unsafe impl bounds.
// Reject all type macros, including through the directly callable internal
// emitter arms. A declarative macro is sufficient to exercise that syntax.
zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports field types
    #[repr(C)]
    struct MacroStruct(field_type!());
}

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports field types
    #[repr(C)]
    union MacroUnion {
        byte: field_type!(),
    }
}

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports field types
    @emit
    [C]
    []
    struct DirectMacroStruct(field_type!());
}

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports field types
    @emit
    [C]
    []
    union DirectMacroUnion {
        byte: field_type!(),
    }
}

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports field types
    @parse
    [C]
    [{ all() }]
    [(doc [= "forwarded"])]
    struct DirectParseMacroStruct(field_type!());
}

zerocopy::cryptocorrosion_derive_traits! { //~[msrv, stable, nightly] ERROR: `cryptocorrosion_derive_traits!` only supports field types
    @parse
    [C]
    [{ all() }]
    [(doc [= "forwarded"])]
    union DirectParseMacroUnion {
        byte: field_type!(),
    }
}

fn main() {}
