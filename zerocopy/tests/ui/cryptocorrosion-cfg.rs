// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//@[msrv, stable, nightly] check-pass

#![allow(dead_code)]
#![forbid(unsafe_code)]

use zerocopy::{FromBytes, FromZeros, Immutable, IntoBytes, TryFromBytes};

mod struct_definition {
    use super::*;

    #[repr(transparent)]
    struct Packet(bool);

    zerocopy::cryptocorrosion_derive_traits! {
        #[repr(C)]
        #[cfg(any())]
        struct Packet(u8);
    }

    static_assertions::assert_not_impl_any!(
        Packet: TryFromBytes, FromZeros, FromBytes, IntoBytes, Immutable
    );
}

mod union_definition {
    use super::*;

    #[repr(transparent)]
    struct Packet(bool);

    zerocopy::cryptocorrosion_derive_traits! {
        #[repr(C)]
        #[cfg(any())]
        union Packet {
            byte: u8,
        }
    }

    static_assertions::assert_not_impl_any!(
        Packet: TryFromBytes, FromZeros, FromBytes, IntoBytes, Immutable
    );
}

mod direct_parse_struct_definition {
    use super::*;

    #[repr(transparent)]
    struct Packet(bool);

    zerocopy::cryptocorrosion_derive_traits! {
        @parse
        [C]
        [{ all() } { any() }]
        [(derive (Copy, Clone)) (allow (dead_code)) (doc [= "disabled"])]
        struct Packet(u8);
    }

    static_assertions::assert_not_impl_any!(
        Packet: TryFromBytes, FromZeros, FromBytes, IntoBytes, Immutable
    );
}

mod direct_parse_union_definition {
    use super::*;

    #[repr(transparent)]
    struct Packet(bool);

    zerocopy::cryptocorrosion_derive_traits! {
        @parse
        [C]
        [{ all() } { any() }]
        [(derive (Copy, Clone)) (allow (dead_code)) (doc [= "disabled"])]
        union Packet {
            byte: u8,
        }
    }

    static_assertions::assert_not_impl_any!(
        Packet: TryFromBytes, FromZeros, FromBytes, IntoBytes, Immutable
    );
}

mod complete_expansion {
    zerocopy::cryptocorrosion_derive_traits! {
        #[repr(Rust)]
        #[cfg(any())]
        struct DisabledInvalidStructRepr(u8);
    }

    zerocopy::cryptocorrosion_derive_traits! {
        #[repr(Rust)]
        #[cfg(any())]
        union DisabledInvalidUnionRepr {
            byte: u8,
        }
    }
}

mod cfg_true {
    use super::*;

    zerocopy::cryptocorrosion_derive_traits! {
        #[repr(transparent)]
        #[derive(Copy, Clone)]
        #[cfg(all())]
        #[allow(non_camel_case_types)]
        /// The declaration and all five impls are enabled together.
        struct enabled_struct(u8);
    }

    zerocopy::cryptocorrosion_derive_traits! {
        #[repr(C)]
        #[derive(Copy, Clone)]
        #[cfg(all())]
        #[allow(non_camel_case_types)]
        /// The declaration and all five impls are enabled together.
        union enabled_union {
            byte: u8,
        }
    }

    static_assertions::assert_impl_all!(
        enabled_struct: Copy, Clone, TryFromBytes, FromZeros, FromBytes, IntoBytes, Immutable
    );
    static_assertions::assert_impl_all!(
        enabled_union: Copy, Clone, TryFromBytes, FromZeros, FromBytes, IntoBytes, Immutable
    );
}

fn main() {}
