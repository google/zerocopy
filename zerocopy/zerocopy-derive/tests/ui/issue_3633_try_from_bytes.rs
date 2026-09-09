// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(non_ascii_idents, non_camel_case_types, non_snake_case, unreachable_patterns)]

extern crate zerocopy_renamed;

fn main() {}

mod direct {
    type ___ZerocopyTagPrimitive = bool;

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Flag(___ZerocopyTagPrimitive),
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `___ZerocopyTagPrimitive` is reserved for generated code
        Other,
    }
}

mod field_type_macro {
    type ___ZerocopyTagPrimitive = bool;

    macro_rules! flag {
        () => {
            ___ZerocopyTagPrimitive
        };
    }

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Flag(flag!()),
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` for a type containing a macro invocation in a field type
        Other,
    }
}

mod qualified {
    mod types {
        pub type ___ZerocopyTagPrimitive = bool;
    }

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Flag(crate::qualified::types::___ZerocopyTagPrimitive),
        Other,
    }
}

mod method_generic_prefix {
    type ___ZcAlignment = bool;

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct Packet(___ZcAlignment);
    //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `___ZcAlignment` is reserved for generated code
}

mod field_marker_prefix {
    type ẕfield = bool;

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct Packet {
        field: ẕfield,
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `ẕfield` is reserved for generated code
    }
}

mod field_marker_target_prefix {
    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    struct ẕfield {
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `ẕfield` is reserved for generated code
        field: bool,
    }
}

mod nontrivial_enum_target_prefix {
    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum ___ZcAlignment {
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `___ZcAlignment` is reserved for generated code
        Flag(bool),
        Other,
    }
}

mod generic_field_marker_capture {
    trait Assoc {
        type Type;
    }

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(transparent)]
    struct Packet<ẕ0>(<Self as Assoc>::Type)
    //~^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `ẕ0` is reserved for generated code
    where
        Self: Assoc;
}

mod use_tree_capture {
    mod helpers {
        pub const VARIANT: usize = 1;
    }

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Variant(
            [bool; {
                use helpers::VARIANT as ___ZerocopyTag;
                ___ZerocopyTag
                //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `___ZerocopyTag` is reserved for generated code
            }],
        ),
        Other,
    }
}

mod pattern_capture {
    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Variant(
            [bool; {
                match 1u8 {
                    ___ZEROCOPY_TAG_Variant => 1,
                    //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` because the unqualified identifier `___ZEROCOPY_TAG_Variant` is reserved for generated code
                    _ => 2,
                }
            }],
        ),
        Other,
    }
}

mod contextual_self {
    trait N {
        const N: usize;
    }

    impl<T> N for T {
        const N: usize = 0;
    }

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Flag([bool; Self::N]),
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` with `Self` in an enum field type
        Other,
    }

    impl Packet {
        const N: usize = 1;
    }
}

mod contextual_self_in_generics {
    trait Select<T: ?Sized> {
        type Assoc;
    }

    #[derive(zerocopy_derive::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet<T: Select<Self>> {
        //~[msrv, stable, nightly]^ ERROR: cannot derive `TryFromBytes` with `Self` in generic parameters or predicates
        Flag(T::Assoc),
        Other,
    }
}
