// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

include!("../include.rs");

fn main() {}

zerocopy::cryptocorrosion_derive_traits! {
//~[msrv, stable, nightly]^ ERROR: unsupported attribute in `cryptocorrosion_derive_traits!`: only `#[doc]`, `#[derive]`, `#[allow]`, `#[warn]`, and `#[deny]` are permitted
    #[repr(C)]
    #[inline]
    pub struct UnpermittedAttribute(u8);
}

zerocopy::cryptocorrosion_derive_traits! {
//~[msrv, stable, nightly]^ ERROR: unsupported attribute in `cryptocorrosion_derive_traits!`: only `#[doc]`, `#[derive]`, `#[allow]`, `#[warn]`, and `#[deny]` are permitted
    #[repr(C)]
    #[cfg(feature = "disabled")]
    pub struct CfgNotPermitted(u8);
}

zerocopy::cryptocorrosion_derive_traits! {
//~[msrv, stable, nightly]^ ERROR: unsupported attribute in `cryptocorrosion_derive_traits!`: only `#[doc]`, `#[derive]`, `#[allow]`, `#[warn]`, and `#[deny]` are permitted
    #[repr(C)]
    #[doc::rewrite]
    pub struct QualifiedAttributeNotPermitted(u8);
}

zerocopy::cryptocorrosion_derive_traits! {
//~[msrv, stable, nightly]^ ERROR: unsupported attribute in `cryptocorrosion_derive_traits!`: only `#[doc]`, `#[derive]`, `#[allow]`, `#[warn]`, and `#[deny]` are permitted
    @munch_attrs
    tag: (__internal_cryptocorrosion_muncher_tag)
    repr: (C)
    attrs: ()
    tokens: (#[doc::rewrite] pub struct DirectQualifiedInTokensNotPermitted(u8);)
}

zerocopy::cryptocorrosion_derive_traits! {
//~[msrv, stable, nightly]^ ERROR: unsupported attribute in `cryptocorrosion_derive_traits!`: only `#[doc]`, `#[derive]`, `#[allow]`, `#[warn]`, and `#[deny]` are permitted
    @munch_attrs
    tag: (__internal_cryptocorrosion_muncher_tag)
    repr: (C)
    attrs: (#[doc::rewrite])
    tokens: (pub struct DirectStructEmitterNotPermitted(u8);)
}

zerocopy::cryptocorrosion_derive_traits! {
//~[msrv, stable, nightly]^ ERROR: unsupported attribute in `cryptocorrosion_derive_traits!`: only `#[doc]`, `#[derive]`, `#[allow]`, `#[warn]`, and `#[deny]` are permitted
    @munch_attrs
    tag: (__internal_cryptocorrosion_muncher_tag)
    repr: (C)
    attrs: (#[doc::rewrite])
    tokens: (pub union DirectUnionEmitterNotPermitted { a: u8, })
}
