// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use synstructure::test_derive;

macro_rules! impl_synstructure_derive {
    ($($outer:ident => $inner:ident),* $(,)?) => {
        $(
            #[allow(non_snake_case)]
            fn $outer(s: synstructure::Structure) -> proc_macro2::TokenStream {
                super::$inner(s.ast())
            }
        )*
    };
}

impl_synstructure_derive!(
    KnownLayout => derive_known_layout_inner,
    Immutable => derive_no_cell_inner,
    TryFromBytes => derive_try_from_bytes_inner,
    FromZeros => derive_from_zeros_inner,
    FromBytes => derive_from_bytes_inner,
    IntoBytes => derive_into_bytes_inner,
    Unaligned => derive_unaligned_inner,
);

#[test]
fn test_known_layout() {
    test_derive! {
        KnownLayout {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::KnownLayout for Foo<>
            where
                Self: ::zerocopy::util::macro_util::core_reexport::marker::Sized,
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                type PointerMetadata = ();

                const LAYOUT: ::zerocopy::DstLayout = ::zerocopy::DstLayout::for_type::<Self>();

                #[inline(always)]
                fn raw_from_ptr_len(
                    bytes: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<u8>,
                    _meta: (),
                ) -> ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self> {
                    bytes.cast::<Self>()
                }

                #[inline(always)]
                fn pointer_to_metadata(
                    _ptr: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self>,
                ) -> () {
                }
            }
        } no_build
    }
}

#[test]
fn test_immutable() {
    test_derive! {
        Immutable {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::Immutable for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_try_from_bytes() {
    test_derive! {
        TryFromBytes {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::TryFromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>
                ) -> bool {
                    true
                }
            }
        } no_build
    }
}

#[test]
fn test_from_zeros() {
    test_derive! {
        FromZeros {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::TryFromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>
                ) -> bool {
                    true
                }
            }

            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::FromZeros for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_from_bytes() {
    test_derive! {
        FromBytes {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::TryFromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>
                ) -> bool {
                    true
                }
            }

            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::FromZeros for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }

            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::FromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_into_bytes() {
    test_derive! {
        IntoBytes {
            #[repr(C)]
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::IntoBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_unaligned() {
    test_derive! {
        Unaligned {
            #[repr(C)]
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::Unaligned for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}
