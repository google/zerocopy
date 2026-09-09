// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_implicit_prelude]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

include!("include.rs");

#[derive(imp::KnownLayout, imp::Immutable, imp::FromBytes, imp::IntoBytes, imp::Unaligned)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct InspectableBlock(
    [u8; {
        const N: usize = 1;
        N
    }],
);

util_assert_impl_all!(
    InspectableBlock:
        imp::KnownLayout,
        imp::Immutable,
        imp::FromBytes,
        imp::IntoBytes,
        imp::Unaligned,
);

mod discarded_generic_defaults {
    use super::*;

    macro_rules! default_type {
        () => {
            u8
        };
    }

    // These defaults are expanded only in the source declaration. The
    // generated impls discard them while preserving the parameters, bounds,
    // const parameter types, and where predicates.
    #[derive(imp::Immutable, imp::FromBytes, imp::IntoBytes, imp::Unaligned)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct ImplOnly<T = default_type!()>(T);

    util_assert_impl_all!(
        ImplOnly:
            imp::Immutable,
            imp::TryFromBytes,
            imp::FromZeros,
            imp::FromBytes,
            imp::IntoBytes,
            imp::Unaligned,
    );
}

mod trivial_from_bytes_validator {
    use super::*;

    type ___ZcAlignment = u8;

    // A trivial validator refers only to `Self`, so its method generic cannot
    // capture this field type.
    #[derive(imp::FromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(transparent)]
    struct Packet(___ZcAlignment);

    #[derive(imp::FromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    union UnionPacket {
        value: ___ZcAlignment,
    }

    util_assert_impl_all!(Packet: imp::FromBytes);
    util_assert_impl_all!(UnionPacket: imp::FromBytes);
}

mod target_named_like_method_generic {
    use super::*;

    mod try_from_bytes_struct {
        use super::*;

        #[derive(imp::TryFromBytes)]
        #[zerocopy(crate = "zerocopy_renamed")]
        struct ___ZcAlignment(bool);

        util_assert_impl_all!(___ZcAlignment: imp::TryFromBytes);
    }

    mod try_from_bytes_union {
        use super::*;

        #[derive(imp::TryFromBytes)]
        #[zerocopy(crate = "zerocopy_renamed")]
        union ___ZcAlignment {
            value: bool,
        }

        util_assert_impl_all!(___ZcAlignment: imp::TryFromBytes);
    }

    mod from_zeros_struct {
        use super::*;

        #[derive(imp::FromZeros)]
        #[zerocopy(crate = "zerocopy_renamed")]
        struct ___ZcAlignment(u8);

        util_assert_impl_all!(___ZcAlignment: imp::FromZeros);
    }

    mod generic_from_bytes_struct {
        use super::*;

        #[derive(imp::FromBytes)]
        #[zerocopy(crate = "zerocopy_renamed")]
        struct ___ZcAlignment<T>(T);

        util_assert_impl_all!(___ZcAlignment<u8>: imp::FromBytes);
    }
}

mod zero_field_target_named_like_field_marker {
    use super::*;

    mod try_from_bytes {
        use super::*;

        #[allow(non_camel_case_types)]
        #[derive(imp::TryFromBytes)]
        #[zerocopy(crate = "zerocopy_renamed")]
        struct ẕUnit<const N: usize>;

        util_assert_impl_all!(ẕUnit<0>: imp::TryFromBytes);
    }

    mod trivial_from_bytes {
        use super::*;

        #[derive(imp::FromBytes)]
        #[zerocopy(crate = "zerocopy_renamed")]
        struct ___ZcAlignment;

        util_assert_impl_all!(___ZcAlignment: imp::FromBytes);
    }
}

mod known_layout {
    use super::*;

    pub mod types {
        pub type __Zerocopy_Field_header = [u8; 8];
    }

    #[derive(imp::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet {
        header: crate::known_layout::types::__Zerocopy_Field_header,
        bytes: [u8],
    }

    #[test]
    fn qualified_reserved_field_type_is_not_captured_by_a_generated_helper() {
        imp::assert_eq!(<Packet as imp::KnownLayout>::size_for_metadata(0), imp::Some(8));
        imp::assert_eq!(<Packet as imp::KnownLayout>::size_for_metadata(1), imp::Some(9));
    }
}

mod known_layout_trailing_dst {
    use super::*;

    pub mod types {
        pub type __ZerocopyKnownLayoutMaybeUninit = [u8];
    }

    #[derive(imp::KnownLayout)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Packet {
        header: u8,
        bytes: crate::known_layout_trailing_dst::types::__ZerocopyKnownLayoutMaybeUninit,
    }

    #[test]
    fn qualified_reserved_trailing_dst_is_not_captured_by_a_generated_helper() {
        imp::assert_eq!(<Packet as imp::KnownLayout>::size_for_metadata(0), imp::Some(1));
        imp::assert_eq!(<Packet as imp::KnownLayout>::size_for_metadata(1), imp::Some(2));
    }
}

mod try_from_bytes {
    use super::*;

    pub mod types {
        pub type ___ZerocopyTagPrimitive = bool;
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Flag(crate::try_from_bytes::types::___ZerocopyTagPrimitive),
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum NamedPacket {
        Flag { value: crate::try_from_bytes::types::___ZerocopyTagPrimitive },
    }

    #[test]
    fn qualified_reserved_field_type_is_not_captured_by_a_generated_helper() {
        crate::util::test_is_bit_valid::<Packet, _>([0u8, 0], true);
        crate::util::test_is_bit_valid::<Packet, _>([0u8, 2], false);
        crate::util::test_is_bit_valid::<NamedPacket, _>([0u8, 0], true);
        crate::util::test_is_bit_valid::<NamedPacket, _>([0u8, 2], false);
    }
}

mod into_bytes {
    use super::*;

    const max_and_disc_size: usize = 0;

    mod types {
        pub type ___ZerocopyTag = [u16; 0];
    }

    use types::___ZerocopyTag;

    #[derive(imp::IntoBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u16)]
    enum PaddingFree {
        Variant(___ZerocopyTag),
    }

    #[derive(imp::IntoBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum ExistingCallerName {
        Variant([u8; max_and_disc_size]),
    }

    util_assert_impl_all!(PaddingFree: imp::IntoBytes);
    util_assert_impl_all!(ExistingCallerName: imp::IntoBytes);

    #[test]
    fn field_type_is_not_captured_by_the_generated_tag() {
        imp::assert_eq!(::core::mem::size_of::<PaddingFree>(), 2);
    }
}

mod qualified_roots {
    use super::*;

    mod self_root {
        use super::*;

        type __Zerocopy_Field_header = [u8; 8];

        #[derive(imp::KnownLayout)]
        #[zerocopy(crate = "zerocopy_renamed")]
        #[repr(C)]
        struct Packet {
            header: self::__Zerocopy_Field_header,
            bytes: [u8],
        }

        #[test]
        fn self_qualified_reserved_name_is_not_captured() {
            imp::assert_eq!(<Packet as imp::KnownLayout>::size_for_metadata(1), imp::Some(9));
        }
    }

    mod super_root {
        use super::*;

        type __Zerocopy_Field_header = [u8; 8];

        mod nested {
            use super::*;

            #[derive(imp::KnownLayout)]
            #[zerocopy(crate = "zerocopy_renamed")]
            #[repr(C)]
            struct Packet {
                header: super::__Zerocopy_Field_header,
                bytes: [u8],
            }

            #[test]
            fn super_qualified_reserved_name_is_not_captured() {
                imp::assert_eq!(<Packet as imp::KnownLayout>::size_for_metadata(1), imp::Some(9),);
            }
        }
    }

    mod qself {
        use super::*;

        trait Layout {
            type __Zerocopy_Field_header;
        }

        impl Layout for () {
            type __Zerocopy_Field_header = [u8; 8];
        }

        struct Length;

        impl Length {
            const __Zerocopy_Field_len: usize = 8;
        }

        #[derive(imp::KnownLayout)]
        #[zerocopy(crate = "zerocopy_renamed")]
        #[repr(C)]
        struct Packet<T: Layout> {
            header: <T as Layout>::__Zerocopy_Field_header,
            prefix: [u8; <Length>::__Zerocopy_Field_len],
            bytes: [u8],
        }

        #[test]
        fn qself_qualified_reserved_names_are_not_captured() {
            imp::assert_eq!(<Packet<()> as imp::KnownLayout>::size_for_metadata(1), imp::Some(17),);
        }
    }
}

mod nested_contextual_self {
    use super::*;

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet {
        Empty(
            [bool; {
                struct Local(::core::marker::PhantomData<Self>);
                ::core::mem::size_of::<Local>()
            }],
        ),
        Other,
    }

    #[test]
    fn self_in_a_nested_type_denotes_that_type() {
        crate::util::test_is_bit_valid::<Packet, _>([0u8], true);
        crate::util::test_is_bit_valid::<Packet, _>([2u8], false);
    }
}

mod imported_helper_capture {
    use super::*;

    trait UserType {}

    impl UserType for u8 {}

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet<CastSized: UserType, Projection: UserType> {
        Variant(CastSized, Projection, bool),
        Other,
    }

    util_assert_impl_all!(Packet<u8, u8>: imp::TryFromBytes);

    #[test]
    fn generic_parameters_are_not_captured_by_projection_helpers() {
        crate::util::test_is_bit_valid::<Packet<u8, u8>, _>([0u8, 0, 0, 0], true);
        crate::util::test_is_bit_valid::<Packet<u8, u8>, _>([0u8, 0, 0, 2], false);
    }
}

mod const_parameter_shadowing {
    use super::*;

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(u8)]
    enum Packet<const ___ZEROCOPY_TAG_A: u8> {
        A(u8),
        B(bool),
    }

    util_assert_impl_all!(Packet<1>: imp::TryFromBytes);

    #[test]
    fn generated_tag_constant_shadows_the_const_parameter() {
        crate::util::test_is_bit_valid::<Packet<1>, _>([0u8, 2], true);
        crate::util::test_is_bit_valid::<Packet<1>, _>([1u8, 2], false);
    }
}
