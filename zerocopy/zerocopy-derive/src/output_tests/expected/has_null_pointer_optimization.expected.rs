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
    unsafe impl<'a, T: Copy> ::zerocopy::HasNullPointerOptimization for Foo<'a, T>
    where
        Self: Sized,
        &'a T: ::zerocopy::HasNullPointerOptimization,
    {
        fn only_derive_is_allowed_to_implement_this_trait() {}
        type NonZeroValidity = <&'a T as ::zerocopy::HasNullPointerOptimization>::NonZeroValidity;
    }
};
