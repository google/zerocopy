// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Derive macros for [zerocopy]'s traits.
//!
//! [zerocopy]: https://docs.rs/zerocopy

// Sometimes we want to use lints which were added after our MSRV.
// `unknown_lints` is `warn` by default and we deny warnings in CI, so without
// this attribute, any unknown lint would cause a CI failure when testing with
// our MSRV.
#![allow(unknown_lints)]
#![deny(renamed_and_removed_lints)]
#![deny(clippy::all, clippy::missing_safety_doc)]
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
    syn::visit::{self, Visit},
    syn::{
        parse_quote, punctuated::Punctuated, token::Comma, Data, DataEnum, DataStruct, DataUnion,
        DeriveInput, Error, GenericParam, Ident, Lifetime, Type, TypePath,
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
// for deriving FromBytes, AsBytes, or Unaligned on an enum"
//
// This will probably require Span::error
// (https://doc.rust-lang.org/nightly/proc_macro/struct.Span.html#method.error),
// which is currently unstable. Revisit this once it's stable.

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

// A struct is `FromBytes` if:
// - all fields are `FromBytes`

fn derive_from_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    impl_block(ast, strct, "FromBytes", true, PaddingCheck::None)
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

    impl_block(ast, enm, "FromBytes", true, PaddingCheck::None)
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
    impl_block(ast, unn, "FromBytes", true, PaddingCheck::None)
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
    let padding_check =
        if is_transparent || is_packed { PaddingCheck::None } else { PaddingCheck::Struct };
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
    impl_block(ast, enm, "AsBytes", false, PaddingCheck::None)
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

    impl_block(ast, unn, "AsBytes", true, PaddingCheck::Union)
}

// A struct is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields `Unaligned`
//   - `repr(packed)`

fn derive_unaligned_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_UNALIGNED_CFG.validate_reprs(ast));
    let require_trait_bound = !reprs.contains(&StructRepr::Packed);

    impl_block(ast, strct, "Unaligned", require_trait_bound, PaddingCheck::None)
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
    impl_block(ast, enm, "Unaligned", true, PaddingCheck::None)
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

    impl_block(ast, unn, "Unaligned", require_trait_bound, PaddingCheck::None)
}

// This enum describes what kind of padding check needs to be generated for the
// associated impl.
enum PaddingCheck {
    // No additional padding check is required.
    None,
    // Check that the sum of the fields' sizes exactly equals the struct's size.
    Struct,
    // Check that the size of each field exactly equals the union's size.
    Union,
}

fn impl_block<D: DataExt>(
    input: &DeriveInput,
    data: &D,
    trait_name: &str,
    require_trait_bound: bool,
    padding_check: PaddingCheck,
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
    // First, we extract the field types, which in this case are `u8`, `T`, and
    // `I::Item`. We use the names of the type parameters to split the field
    // types into two sets - a set of types which are based on the type
    // parameters, and a set of types which are not. First, we re-use the
    // existing parameters and where clauses, generating an `impl` block like:
    //
    //   impl<T, I: Iterator> FromBytes for Foo<T, I>
    //   where
    //       T: Copy,
    //       I: Clone,
    //       I::Item: Clone,
    //   {
    //   }
    //
    // Then, we use the list of types which are based on the type parameters to
    // generate new entries in the `where` clause:
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
    // Finally, we use a different technique to generate the bounds for the
    // types which are not based on type parameters:
    //
    //
    //   fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {
    //       struct ImplementsFromBytes<F: ?Sized + FromBytes>(PhantomData<F>);
    //       let _: ImplementsFromBytes<u8>;
    //   }
    //
    // It would be easier to put all types in the where clause, but that won't
    // work until the trivial_bounds feature is stabilized (#48214).
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
    //
    //     error[E0283]: type annotations required: cannot resolve `core::marker::PhantomData<&'a u8>: zerocopy::Unaligned`
    //      --> src/main.rs:6:10
    //       |
    //     6 | #[derive(Unaligned)]
    //       |          ^^^^^^^^^
    //       |
    //       = note: required by `zerocopy::Unaligned`

    // A visitor which is used to walk a field's type and determine whether any
    // of its definition is based on the type or lifetime parameters on a type.
    struct FromTypeParamVisit<'a, 'b>(&'a Punctuated<GenericParam, Comma>, &'b mut bool);

    impl<'a, 'b> Visit<'a> for FromTypeParamVisit<'a, 'b> {
        fn visit_lifetime(&mut self, i: &'a Lifetime) {
            visit::visit_lifetime(self, i);
            if self.0.iter().any(|param| {
                if let GenericParam::Lifetime(param) = param {
                    param.lifetime.ident == i.ident
                } else {
                    false
                }
            }) {
                *self.1 = true;
            }
        }

        fn visit_type_path(&mut self, i: &'a TypePath) {
            visit::visit_type_path(self, i);
            if self.0.iter().any(|param| {
                if let GenericParam::Type(param) = param {
                    i.path.segments.first().unwrap().ident == param.ident
                } else {
                    false
                }
            }) {
                *self.1 = true;
            }
        }
    }

    // Whether this type is based on one of the type parameters. E.g., given the
    // type parameters `<T>`, `T`, `T::Foo`, and `(T::Foo, String)` are all
    // based on the type parameters, while `String` and `(String, Box<()>)` are
    // not.
    let is_from_type_param = |ty: &Type| {
        let mut ret = false;
        FromTypeParamVisit(&input.generics.params, &mut ret).visit_type(ty);
        ret
    };

    let trait_ident = Ident::new(trait_name, Span::call_site());

    let field_types = data.nested_types();
    let type_param_field_types = field_types.iter().filter(|ty| is_from_type_param(ty));
    let non_type_param_field_types = field_types.iter().filter(|ty| !is_from_type_param(ty));

    // Add a new set of where clause predicates of the form `T: Trait` for each
    // of the types of the struct's fields (but only the ones whose types are
    // based on one of the type parameters).
    let mut generics = input.generics.clone();
    let where_clause = generics.make_where_clause();
    if require_trait_bound {
        for ty in type_param_field_types {
            let bound = parse_quote!(#ty: zerocopy::#trait_ident);
            where_clause.predicates.push(bound);
        }
    }

    let type_ident = &input.ident;
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

    if require_trait_bound {
        for ty in non_type_param_field_types {
            where_clause.predicates.push(parse_quote!(#ty: zerocopy::#trait_ident));
        }
    }

    match (field_types.is_empty(), padding_check) {
        (true, _) | (false, PaddingCheck::None) => (),
        (false, PaddingCheck::Struct) => {
            let fields = field_types.iter();
            // `parse_quote!` doesn't parse macro invocations in const generics
            // properly without enabling syn's `full` feature, so the type has
            // to be manually constructed as `syn::Type::Verbatim`.
            //
            // This where clause is equivalent to adding:
            // ```
            // HasPadding<Foo, {struct_has_padding!(Foo, a, b, ...)}>: ShouldBe<false>
            // ```
            // with fully-qualified paths.
            where_clause.predicates.push(syn::WherePredicate::Type(syn::PredicateType {
                lifetimes: None,
                bounded_ty: syn::Type::Verbatim(quote!(zerocopy::derive_util::HasPadding<#type_ident, {zerocopy::struct_has_padding!(#type_ident, #(#fields),*)}>)),
                colon_token: syn::Token![:](Span::mixed_site()),
                bounds: parse_quote!(zerocopy::derive_util::ShouldBe<false>),
            }));
        }
        (false, PaddingCheck::Union) => {
            let fields = field_types.iter();
            // `parse_quote!` doesn't parse macro invocations in const generics
            // properly without enabling syn's `full` feature, so the type has
            // to be manually constructed as `syn::Type::Verbatim`.
            //
            // This where clause is equivalent to adding:
            // ```
            // HasPadding<Foo, {union_has_padding!(Foo, a, b, ...)}>: ShouldBe<false>
            // ```
            // with fully-qualified paths.
            where_clause.predicates.push(syn::WherePredicate::Type(syn::PredicateType {
                lifetimes: None,
                bounded_ty: syn::Type::Verbatim(quote!(zerocopy::derive_util::HasPadding<#type_ident, {zerocopy::union_has_padding!(#type_ident, #(#fields),*)}>)),
                colon_token: syn::Token![:](Span::mixed_site()),
                bounds: parse_quote!(zerocopy::derive_util::ShouldBe<false>),
            }));
        }
    }

    // We use a constant to force the compiler to emit an error when a concrete
    // type does not satisfy the where clauses on its impl.
    let use_concrete = if input.generics.params.is_empty() {
        Some(quote! {
            const _: () = {
                fn must_implement_trait<T: zerocopy::#trait_ident + ?::core::marker::Sized>() {}
                let _ = must_implement_trait::<#type_ident>;
            };
        })
    } else {
        None
    };

    quote! {
        unsafe impl < #(#params),* > zerocopy::#trait_ident for #type_ident < #(#param_idents),* > #where_clause {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
        #use_concrete
    }
}

fn print_all_errors(errors: Vec<Error>) -> proc_macro2::TokenStream {
    errors.iter().map(Error::to_compile_error).collect()
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
