#[allow(
    deprecated,
    private_bounds,
    non_local_definitions,
    non_camel_case_types,
    non_upper_case_globals,
    non_snake_case,
    non_ascii_idents,
    clippy::missing_inline_in_public_items,
)]
#[deny(ambiguous_associated_items)]
#[automatically_derived]
const _: () = {
    unsafe impl ::zerocopy::TryFromBytes for Foo {
        fn only_derive_is_allowed_to_implement_this_trait() {}
        fn is_bit_valid(
            _candidate: ::zerocopy::Maybe<Self>,
        ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool {
            if false {
                fn assert_is_from_bytes<T>()
                where
                    T: ::zerocopy::FromBytes,
                    T: ?::zerocopy::util::macro_util::core_reexport::marker::Sized,
                {}
                assert_is_from_bytes::<Self>();
            }
            true
        }
    }
};
#[allow(
    deprecated,
    private_bounds,
    non_local_definitions,
    non_camel_case_types,
    non_upper_case_globals,
    non_snake_case,
    non_ascii_idents,
    clippy::missing_inline_in_public_items,
)]
#[deny(ambiguous_associated_items)]
#[automatically_derived]
const _: () = {
    unsafe impl ::zerocopy::FromZeros for Foo {
        fn only_derive_is_allowed_to_implement_this_trait() {}
    }
};
#[allow(
    deprecated,
    private_bounds,
    non_local_definitions,
    non_camel_case_types,
    non_upper_case_globals,
    non_snake_case,
    non_ascii_idents,
    clippy::missing_inline_in_public_items,
)]
#[deny(ambiguous_associated_items)]
#[automatically_derived]
const _: () = {
    unsafe impl ::zerocopy::FromBytes for Foo {
        fn only_derive_is_allowed_to_implement_this_trait() {}
    }
};
