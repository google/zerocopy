// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Derive macros for [zerocopy]'s traits.
//!
//! [zerocopy]: https://docs.rs/zerocopy

// Sometimes we want to use lints which were added after our MSRV.
// `unknown_lints` is `warn` by default and we deny warnings in CI, so without
// this attribute, any unknown lint would cause a CI failure when testing with
// our MSRV.
#![allow(unknown_lints)]
#![deny(renamed_and_removed_lints)]
#![deny(clippy::all, clippy::missing_safety_doc, clippy::undocumented_unsafe_blocks)]
#![deny(
    rustdoc::bare_urls,
    rustdoc::broken_intra_doc_links,
    rustdoc::invalid_codeblock_attributes,
    rustdoc::invalid_html_tags,
    rustdoc::invalid_rust_codeblocks,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_intra_doc_links
)]
#![recursion_limit = "128"]

mod ext;
mod repr;

use {
    proc_macro2::Span,
    quote::quote,
    syn::{
        parse_quote, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Error, Expr, ExprLit,
        GenericParam, Ident, Lit,
    },
};

use {crate::ext::*, crate::repr::*};

// TODO(https://github.com/rust-lang/rust/issues/54140): Some errors could be
// made better if we could add multiple lines of error output like this:
//
// error: unsupported representation
//   --> enum.rs:28:8
//    |
// 28 | #[repr(transparent)]
//    |
// help: required by the derive of FromBytes
//
// Instead, we have more verbose error messages like "unsupported representation
// for deriving FromZeroes, FromBytes, AsBytes, or Unaligned on an enum"
//
// This will probably require Span::error
// (https://doc.rust-lang.org/nightly/proc_macro/struct.Span.html#method.error),
// which is currently unstable. Revisit this once it's stable.

#[proc_macro_derive(FromZeroes)]
pub fn derive_from_zeroes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_from_zeroes_struct(&ast, strct),
        Data::Enum(enm) => derive_from_zeroes_enum(&ast, enm),
        Data::Union(unn) => derive_from_zeroes_union(&ast, unn),
    }
    .into()
}

#[proc_macro_derive(FromBytes)]
pub fn derive_from_bytes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_from_bytes_struct(&ast, strct),
        Data::Enum(enm) => derive_from_bytes_enum(&ast, enm),
        Data::Union(unn) => derive_from_bytes_union(&ast, unn),
    }
    .into()
}

#[proc_macro_derive(AsBytes)]
pub fn derive_as_bytes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_as_bytes_struct(&ast, strct),
        Data::Enum(enm) => derive_as_bytes_enum(&ast, enm),
        Data::Union(unn) => derive_as_bytes_union(&ast, unn),
    }
    .into()
}

#[proc_macro_derive(Unaligned)]
pub fn derive_unaligned(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_unaligned_struct(&ast, strct),
        Data::Enum(enm) => derive_unaligned_enum(&ast, enm),
        Data::Union(unn) => derive_unaligned_union(&ast, unn),
    }
    .into()
}

// Unwraps a `Result<_, Vec<Error>>`, converting any `Err` value into a
// `TokenStream` and returning it.
macro_rules! try_or_print {
    ($e:expr) => {
        match $e {
            Ok(x) => x,
            Err(errors) => return print_all_errors(errors),
        }
    };
}

const STRUCT_UNION_ALLOWED_REPR_COMBINATIONS: &[&[StructRepr]] = &[
    &[StructRepr::C],
    &[StructRepr::Transparent],
    &[StructRepr::Packed],
    &[StructRepr::C, StructRepr::Packed],
];

// A struct is `FromZeroes` if:
// - all fields are `FromZeroes`

fn derive_from_zeroes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    impl_block(ast, strct, "FromZeroes", true, None)
}

// An enum is `FromZeroes` if:
// - all of its variants are fieldless
// - one of the variants has a discriminant of `0`

fn derive_from_zeroes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_c_like() {
        return Error::new_spanned(ast, "only C-like enums can implement FromZeroes")
            .to_compile_error();
    }

    let has_explicit_zero_discriminant =
        enm.variants.iter().filter_map(|v| v.discriminant.as_ref()).any(|(_, e)| {
            if let Expr::Lit(ExprLit { lit: Lit::Int(i), .. }) = e {
                i.base10_parse::<usize>().ok() == Some(0)
            } else {
                false
            }
        });
    // If the first variant of an enum does not specify its discriminant, it is set to zero:
    // https://doc.rust-lang.org/reference/items/enumerations.html#custom-discriminant-values-for-fieldless-enumerations
    let has_implicit_zero_discriminant =
        enm.variants.iter().next().map(|v| v.discriminant.is_none()) == Some(true);

    if !has_explicit_zero_discriminant && !has_implicit_zero_discriminant {
        return Error::new_spanned(
            ast,
            "FromZeroes only supported on enums with a variant that has a discriminant of `0`",
        )
        .to_compile_error();
    }

    impl_block(ast, enm, "FromZeroes", true, None)
}

// Like structs, unions are `FromZeroes` if
// - all fields are `FromZeroes`

fn derive_from_zeroes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    impl_block(ast, unn, "FromZeroes", true, None)
}

// A struct is `FromBytes` if:
// - all fields are `FromBytes`

fn derive_from_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    impl_block(ast, strct, "FromBytes", true, None)
}

// An enum is `FromBytes` if:
// - Every possible bit pattern must be valid, which means that every bit
//   pattern must correspond to a different enum variant. Thus, for an enum
//   whose layout takes up N bytes, there must be 2^N variants.
// - Since we must know N, only representations which guarantee the layout's
//   size are allowed. These are `repr(uN)` and `repr(iN)` (`repr(C)` implies an
//   implementation-defined size). `usize` and `isize` technically guarantee the
//   layout's size, but would require us to know how large those are on the
//   target platform. This isn't terribly difficult - we could emit a const
//   expression that could call `core::mem::size_of` in order to determine the
//   size and check against the number of enum variants, but a) this would be
//   platform-specific and, b) even on Rust's smallest bit width platform (32),
//   this would require ~4 billion enum variants, which obviously isn't a thing.

fn derive_from_bytes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_c_like() {
        return Error::new_spanned(ast, "only C-like enums can implement FromBytes")
            .to_compile_error();
    }

    let reprs = try_or_print!(ENUM_FROM_BYTES_CFG.validate_reprs(ast));

    let variants_required = match reprs.as_slice() {
        [EnumRepr::U8] | [EnumRepr::I8] => 1usize << 8,
        [EnumRepr::U16] | [EnumRepr::I16] => 1usize << 16,
        // `validate_reprs` has already validated that it's one of the preceding
        // patterns.
        _ => unreachable!(),
    };
    if enm.variants.len() != variants_required {
        return Error::new_spanned(
            ast,
            format!(
                "FromBytes only supported on {} enum with {} variants",
                reprs[0], variants_required
            ),
        )
        .to_compile_error();
    }

    impl_block(ast, enm, "FromBytes", true, None)
}

#[rustfmt::skip]
const ENUM_FROM_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        allowed_combinations_message: r#"FromBytes requires repr of "u8", "u16", "i8", or "i16""#,
        derive_unaligned: false,
        allowed_combinations: &[
            &[U8],
            &[U16],
            &[I8],
            &[I16],
        ],
        disallowed_but_legal_combinations: &[
            &[C],
            &[U32],
            &[I32],
            &[U64],
            &[I64],
            &[Usize],
            &[Isize],
        ],
    }
};

// Like structs, unions are `FromBytes` if
// - all fields are `FromBytes`

fn derive_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    impl_block(ast, unn, "FromBytes", true, None)
}

// A struct is `AsBytes` if:
// - all fields are `AsBytes`
// - `repr(C)` or `repr(transparent)` and
//   - no padding (size of struct equals sum of size of field types)
// - `repr(packed)`

fn derive_as_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_AS_BYTES_CFG.validate_reprs(ast));
    let is_transparent = reprs.contains(&StructRepr::Transparent);
    let is_packed = reprs.contains(&StructRepr::Packed);

    // TODO(#10): Support type parameters for non-transparent, non-packed
    // structs.
    if !ast.generics.params.is_empty() && !is_transparent && !is_packed {
        return Error::new(
            Span::call_site(),
            "unsupported on generic structs that are not repr(transparent) or repr(packed)",
        )
        .to_compile_error();
    }

    // We don't need a padding check if the struct is repr(transparent) or
    // repr(packed).
    // - repr(transparent): The layout and ABI of the whole struct is the same
    //   as its only non-ZST field (meaning there's no padding outside of that
    //   field) and we require that field to be `AsBytes` (meaning there's no
    //   padding in that field).
    // - repr(packed): Any inter-field padding bytes are removed, meaning that
    //   any padding bytes would need to come from the fields, all of which
    //   we require to be `AsBytes` (meaning they don't have any padding).
    let padding_check = if is_transparent || is_packed { None } else { Some(PaddingCheck::Struct) };
    impl_block(ast, strct, "AsBytes", true, padding_check)
}

const STRUCT_UNION_AS_BYTES_CFG: Config<StructRepr> = Config {
    // Since `disallowed_but_legal_combinations` is empty, this message will
    // never actually be emitted.
    allowed_combinations_message: r#"AsBytes requires either a) repr "C" or "transparent" with all fields implementing AsBytes or, b) repr "packed""#,
    derive_unaligned: false,
    allowed_combinations: STRUCT_UNION_ALLOWED_REPR_COMBINATIONS,
    disallowed_but_legal_combinations: &[],
};

// An enum is `AsBytes` if it is C-like and has a defined repr.

fn derive_as_bytes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_c_like() {
        return Error::new_spanned(ast, "only C-like enums can implement AsBytes")
            .to_compile_error();
    }

    // We don't care what the repr is; we only care that it is one of the
    // allowed ones.
    let _: Vec<repr::EnumRepr> = try_or_print!(ENUM_AS_BYTES_CFG.validate_reprs(ast));
    impl_block(ast, enm, "AsBytes", false, None)
}

#[rustfmt::skip]
const ENUM_AS_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        // Since `disallowed_but_legal_combinations` is empty, this message will
        // never actually be emitted.
        allowed_combinations_message: r#"AsBytes requires repr of "C", "u8", "u16", "u32", "u64", "usize", "i8", "i16", "i32", "i64", or "isize""#,
        derive_unaligned: false,
        allowed_combinations: &[
            &[C],
            &[U8],
            &[U16],
            &[I8],
            &[I16],
            &[U32],
            &[I32],
            &[U64],
            &[I64],
            &[Usize],
            &[Isize],
        ],
        disallowed_but_legal_combinations: &[],
    }
};

// A union is `AsBytes` if:
// - all fields are `AsBytes`
// - `repr(C)`, `repr(transparent)`, or `repr(packed)`
// - no padding (size of union equals size of each field type)

fn derive_as_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#10): Support type parameters.
    if !ast.generics.params.is_empty() {
        return Error::new(Span::call_site(), "unsupported on types with type parameters")
            .to_compile_error();
    }

    try_or_print!(STRUCT_UNION_AS_BYTES_CFG.validate_reprs(ast));

    impl_block(ast, unn, "AsBytes", true, Some(PaddingCheck::Union))
}

// A struct is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields `Unaligned`
//   - `repr(packed)`

fn derive_unaligned_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_UNALIGNED_CFG.validate_reprs(ast));
    let require_trait_bound = !reprs.contains(&StructRepr::Packed);

    impl_block(ast, strct, "Unaligned", require_trait_bound, None)
}

const STRUCT_UNION_UNALIGNED_CFG: Config<StructRepr> = Config {
    // Since `disallowed_but_legal_combinations` is empty, this message will
    // never actually be emitted.
    allowed_combinations_message: r#"Unaligned requires either a) repr "C" or "transparent" with all fields implementing Unaligned or, b) repr "packed""#,
    derive_unaligned: true,
    allowed_combinations: STRUCT_UNION_ALLOWED_REPR_COMBINATIONS,
    disallowed_but_legal_combinations: &[],
};

// An enum is `Unaligned` if:
// - No `repr(align(N > 1))`
// - `repr(u8)` or `repr(i8)`

fn derive_unaligned_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_c_like() {
        return Error::new_spanned(ast, "only C-like enums can implement Unaligned")
            .to_compile_error();
    }

    // The only valid reprs are `u8` and `i8`, and optionally `align(1)`. We
    // don't actually care what the reprs are so long as they satisfy that
    // requirement.
    let _: Vec<repr::EnumRepr> = try_or_print!(ENUM_UNALIGNED_CFG.validate_reprs(ast));

    // C-like enums cannot currently have type parameters, so this value of true
    // for `require_trait_bounds` doesn't really do anything. But it's
    // marginally more future-proof in case that restriction is lifted in the
    // future.
    impl_block(ast, enm, "Unaligned", true, None)
}

#[rustfmt::skip]
const ENUM_UNALIGNED_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        allowed_combinations_message:
            r#"Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))"#,
        derive_unaligned: true,
        allowed_combinations: &[
            &[U8],
            &[I8],
        ],
        disallowed_but_legal_combinations: &[
            &[C],
            &[U16],
            &[U32],
            &[U64],
            &[Usize],
            &[I16],
            &[I32],
            &[I64],
            &[Isize],
        ],
    }
};

// Like structs, a union is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields `Unaligned`
//   - `repr(packed)`

fn derive_unaligned_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_UNALIGNED_CFG.validate_reprs(ast));
    let require_trait_bound = !reprs.contains(&StructRepr::Packed);

    impl_block(ast, unn, "Unaligned", require_trait_bound, None)
}

// This enum describes what kind of padding check needs to be generated for the
// associated impl.
enum PaddingCheck {
    // Check that the sum of the fields' sizes exactly equals the struct's size.
    Struct,
    // Check that the size of each field exactly equals the union's size.
    Union,
}

impl PaddingCheck {
    /// Returns the ident of the macro to call in order to validate that a type
    /// passes the padding check encoded by `PaddingCheck`.
    fn validator_macro_ident(&self) -> Ident {
        let s = match self {
            PaddingCheck::Struct => "struct_has_padding",
            PaddingCheck::Union => "union_has_padding",
        };

        Ident::new(s, Span::call_site())
    }
}

fn impl_block<D: DataExt>(
    input: &DeriveInput,
    data: &D,
    trait_name: &str,
    require_trait_bound: bool,
    padding_check: Option<PaddingCheck>,
) -> proc_macro2::TokenStream {
    // In this documentation, we will refer to this hypothetical struct:
    //
    //   #[derive(FromBytes)]
    //   struct Foo<T, I: Iterator>
    //   where
    //       T: Copy,
    //       I: Clone,
    //       I::Item: Clone,
    //   {
    //       a: u8,
    //       b: T,
    //       c: I::Item,
    //   }
    //
    // We extract the field types, which in this case are `u8`, `T`, and
    // `I::Item`. We re-use the existing parameters and where clauses. If
    // `require_trait_bound == true` (as it is for `FromBytes), we add where
    // bounds for each field's type:
    //
    //   impl<T, I: Iterator> FromBytes for Foo<T, I>
    //   where
    //       T: Copy,
    //       I: Clone,
    //       I::Item: Clone,
    //       T: FromBytes,
    //       I::Item: FromBytes,
    //   {
    //   }
    //
    // NOTE: It is standard practice to only emit bounds for the type parameters
    // themselves, not for field types based on those parameters (e.g., `T` vs
    // `T::Foo`). For a discussion of why this is standard practice, see
    // https://github.com/rust-lang/rust/issues/26925.
    //
    // The reason we diverge from this standard is that doing it that way for us
    // would be unsound. E.g., consider a type, `T` where `T: FromBytes` but
    // `T::Foo: !FromBytes`. It would not be sound for us to accept a type with
    // a `T::Foo` field as `FromBytes` simply because `T: FromBytes`.
    //
    // While there's no getting around this requirement for us, it does have the
    // pretty serious downside that, when lifetimes are involved, the trait
    // solver ties itself in knots:
    //
    //     #[derive(Unaligned)]
    //     #[repr(C)]
    //     struct Dup<'a, 'b> {
    //         a: PhantomData<&'a u8>,
    //         b: PhantomData<&'b u8>,
    //     }
    //
    //     error[E0283]: type annotations required: cannot resolve `core::marker::PhantomData<&'a u8>: zerocopy::Unaligned`
    //      --> src/main.rs:6:10
    //       |
    //     6 | #[derive(Unaligned)]
    //       |          ^^^^^^^^^
    //       |
    //       = note: required by `zerocopy::Unaligned`

    let type_ident = &input.ident;
    let trait_ident = Ident::new(trait_name, Span::call_site());
    let field_types = data.field_types();

    let field_type_bounds = require_trait_bound
        .then(|| field_types.iter().map(|ty| parse_quote!(#ty: zerocopy::#trait_ident)))
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

    // Don't bother emitting a padding check if there are no fields.
    #[allow(unstable_name_collisions)] // See `BoolExt` below
    let padding_check_bound = padding_check.and_then(|check| (!field_types.is_empty()).then_some(check)).map(|check| {
        let fields = field_types.iter();
        let validator_macro = check.validator_macro_ident();
        parse_quote!(
            zerocopy::macro_util::HasPadding<#type_ident, {zerocopy::#validator_macro!(#type_ident, #(#fields),*)}>:
                zerocopy::macro_util::ShouldBe<false>
        )
    });

    let bounds = input
        .generics
        .where_clause
        .as_ref()
        .map(|where_clause| where_clause.predicates.iter())
        .into_iter()
        .flatten()
        .chain(field_type_bounds.iter())
        .chain(padding_check_bound.iter());

    // The parameters with trait bounds, but without type defaults.
    let params = input.generics.params.clone().into_iter().map(|mut param| {
        match &mut param {
            GenericParam::Type(ty) => ty.default = None,
            GenericParam::Const(cnst) => cnst.default = None,
            GenericParam::Lifetime(_) => {}
        }
        quote!(#param)
    });
    // The identifiers of the parameters without trait bounds or type defaults.
    let param_idents = input.generics.params.iter().map(|param| match param {
        GenericParam::Type(ty) => {
            let ident = &ty.ident;
            quote!(#ident)
        }
        GenericParam::Lifetime(l) => quote!(#l),
        GenericParam::Const(cnst) => quote!(#cnst),
    });

    quote! {
        unsafe impl < #(#params),* > zerocopy::#trait_ident for #type_ident < #(#param_idents),* >
        where
            #(#bounds,)*
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
    }
}

fn print_all_errors(errors: Vec<Error>) -> proc_macro2::TokenStream {
    errors.iter().map(Error::to_compile_error).collect()
}

// A polyfill for `Option::then_some`, which was added after our MSRV.
//
// TODO(#67): Remove this once our MSRV is >= 1.62.
trait BoolExt {
    fn then_some<T>(self, t: T) -> Option<T>;
}

impl BoolExt for bool {
    fn then_some<T>(self, t: T) -> Option<T> {
        if self {
            Some(t)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_repr_orderings() {
        // Validate that the repr lists in the various configs are in the
        // canonical order. If they aren't, then our algorithm to look up in
        // those lists won't work.

        // TODO(https://github.com/rust-lang/rust/issues/53485): Remove once
        // `Vec::is_sorted` is stabilized.
        fn is_sorted_and_deduped<T: Clone + Ord>(ts: &[T]) -> bool {
            let mut sorted = ts.to_vec();
            sorted.sort();
            sorted.dedup();
            ts == sorted.as_slice()
        }

        fn elements_are_sorted_and_deduped<T: Clone + Ord>(lists: &[&[T]]) -> bool {
            lists.iter().all(|list| is_sorted_and_deduped(list))
        }

        fn config_is_sorted<T: KindRepr + Clone>(config: &Config<T>) -> bool {
            elements_are_sorted_and_deduped(config.allowed_combinations)
                && elements_are_sorted_and_deduped(config.disallowed_but_legal_combinations)
        }

        assert!(config_is_sorted(&STRUCT_UNION_UNALIGNED_CFG));
        assert!(config_is_sorted(&ENUM_FROM_BYTES_CFG));
        assert!(config_is_sorted(&ENUM_UNALIGNED_CFG));
    }

    #[test]
    fn test_config_repr_no_overlap() {
        // Validate that no set of reprs appears in both the
        // `allowed_combinations` and `disallowed_but_legal_combinations` lists.

        fn overlap<T: Eq>(a: &[T], b: &[T]) -> bool {
            a.iter().any(|elem| b.contains(elem))
        }

        fn config_overlaps<T: KindRepr + Eq>(config: &Config<T>) -> bool {
            overlap(config.allowed_combinations, config.disallowed_but_legal_combinations)
        }

        assert!(!config_overlaps(&STRUCT_UNION_UNALIGNED_CFG));
        assert!(!config_overlaps(&ENUM_FROM_BYTES_CFG));
        assert!(!config_overlaps(&ENUM_UNALIGNED_CFG));
    }
}
