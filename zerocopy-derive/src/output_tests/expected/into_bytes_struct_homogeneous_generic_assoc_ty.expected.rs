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
    unsafe impl<P: Config> ::zerocopy::IntoBytes for Foo<P>
    where
        P::BaseField: ::zerocopy::IntoBytes,
        P::BaseField: ::zerocopy::IntoBytes,
        P::BaseField: ::zerocopy::IntoBytes,
    {
        fn only_derive_is_allowed_to_implement_this_trait() {}
    }
};
