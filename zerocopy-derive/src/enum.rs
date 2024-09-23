// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use ::proc_macro2::TokenStream;
use ::quote::quote;
use ::syn::{DataEnum, Fields, Ident};

use crate::{Ctx, EnumRepr, Trait};

/// Returns the repr for the tag enum, given the collection of reprs on the
/// enum.
///
/// This function returns:
/// - `Some(C)` for `repr(C)`
/// - `Some(int)` for `repr(int)` and `repr(C, int)`
/// - `None` for all other reprs
pub(crate) fn tag_repr(reprs: &[EnumRepr]) -> Option<&EnumRepr> {
    let mut result = None;
    for repr in reprs {
        match repr {
            EnumRepr::C => result = Some(repr),
            EnumRepr::U8
            | EnumRepr::U16
            | EnumRepr::U32
            | EnumRepr::U64
            | EnumRepr::Usize
            | EnumRepr::I8
            | EnumRepr::I16
            | EnumRepr::I32
            | EnumRepr::I64
            | EnumRepr::Isize => {
                return Some(repr);
            }
            _ => (),
        }
    }
    result
}

/// Generates a tag enum for the given enum. This generates an enum with the
/// same `repr`s, variants, and corresponding discriminants, but none of the
/// fields.
pub(crate) fn generate_tag_enum(mut ctx: Ctx<'_, DataEnum>, repr: &EnumRepr) -> TokenStream {
    let variants = ctx.data.variants.iter().map(|v| {
        let ident = &v.ident;
        if let Some((eq, discriminant)) = &v.discriminant {
            quote! { #ident #eq #discriminant }
        } else {
            quote! { #ident }
        }
    });

    let tag_ident = ctx.call_site_ident("Tag");
    quote! {
        #[repr(#repr)]
        #[allow(dead_code)]
        enum #tag_ident {
            #(#variants,)*
        }
    }
}

/// Generates a constant for the tag associated with each variant of the enum.
/// When we match on the enum's tag, each arm matches one of these constants. We
/// have to use constants here because:
///
/// - The type that we're matching on is not the type of the tag, it's an
///   integer of the same size as the tag type and with the same bit patterns.
/// - We can't read the enum tag as an enum because the bytes may not represent
///   a valid variant.
/// - Patterns do not currently support const expressions, so we have to assign
///   these constants to names rather than use them inline in the `match`
///   statement.
fn generate_tag_consts(mut ctx: Ctx<'_, DataEnum>) -> TokenStream {
    let tags = ctx.data.variants.iter().map(|v| {
        let mut ctx = ctx.reborrow();
        let variant_ident = &v.ident;
        let tag_const_ident = ctx.tag_const_ident(variant_ident);
        let tag_primitive_alias_ident = ctx.tag_primitive_alias_ident();
        let tag_enum_ident = ctx.tag_enum_ident();
        quote! {
            // This casts the enum variant to its discriminant, and then
            // converts the discriminant to the target integral type via a
            // numeric cast [1].
            //
            // Because these are the same size, this is defined to be a no-op
            // and therefore is a lossless conversion [2].
            //
            // [1]: https://doc.rust-lang.org/stable/reference/expressions/operator-expr.html#enum-cast
            // [2]: https://doc.rust-lang.org/stable/reference/expressions/operator-expr.html#numeric-cast
            #[allow(non_upper_case_globals)]
            const #tag_const_ident: #tag_primitive_alias_ident =
                #tag_enum_ident::#variant_ident as #tag_primitive_alias_ident;
        }
    });

    quote! {
        #(#tags)*
    }
}

/// Generates variant structs for the given enum variant.
///
/// These are structs associated with each variant of an enum. They are
/// `repr(C)` tuple structs with the same fields as the variant after a
/// `MaybeUninit<#inner_tag_alias_ident>`.
///
/// In order to unify the generated types for `repr(C)` and `repr(int)` enums,
/// we use a "fused" representation with fields for both an inner tag and an
/// outer tag. Depending on the repr, we will set one of these tags to the tag
/// type and the other to `()`. This lets us generate the same code but put the
/// tags in different locations.
fn generate_variant_structs(mut ctx: Ctx<'_, DataEnum>) -> TokenStream {
    let (impl_generics, ty_generics, where_clause) = ctx.ast.generics.split_for_impl();

    // All variant structs have a `PhantomData<MyEnum<...>>` field because we
    // don't know which generic parameters each variant will use, and unused
    // generic parameters are a compile error.
    let enum_name = &ctx.ast.ident;
    let phantom_ty = quote! {
        core_reexport::marker::PhantomData<#enum_name #ty_generics>
    };

    let variant_structs = ctx.data.variants.iter().filter_map(|variant| {
        // We don't generate variant structs for unit variants because we only
        // need to check the tag. This helps cut down our generated code a bit.
        if matches!(variant.fields, Fields::Unit) {
            return None;
        }

        let trait_path = Trait::TryFromBytes.derive_path();
        let variant_struct_ident = ctx.reborrow().variant_struct_ident(&variant.ident);
        let field_types = variant.fields.iter().map(|f| &f.ty);

        let inner_tag_alias_ident = ctx.inner_tag_alias_ident();
        Some(quote! {
            #[repr(C)]
            #[allow(non_snake_case)]
            #[derive(#trait_path)]
            struct #variant_struct_ident #impl_generics (
                core_reexport::mem::MaybeUninit<#inner_tag_alias_ident>,
                #(#field_types,)*
                #phantom_ty,
            ) #where_clause;
        })
    });

    quote! {
        #(#variant_structs)*
    }
}

fn generate_variants_union(mut ctx: Ctx<'_, DataEnum>) -> TokenStream {
    let generics = &ctx.ast.generics;
    let (_, ty_generics, _) = generics.split_for_impl();

    let variants_union_ident = ctx.variants_union_ident();
    let nonempty_field_ident = ctx.nonempty_field_ident();

    let fields = ctx.data.variants.iter().filter_map(|variant| {
        // We don't generate variant structs for unit variants because we only
        // need to check the tag. This helps cut down our generated code a bit.
        if matches!(variant.fields, Fields::Unit) {
            return None;
        }

        // Field names are prefixed with `field_` to prevent name collision with
        // the `nonempty` field.
        let field_name =
            ctx.spanned_ident(&format!("field_{}", &variant.ident), variant.ident.span());
        let variant_struct_ident = ctx.reborrow().variant_struct_ident(&variant.ident);

        Some(quote! {
            #field_name: core_reexport::mem::ManuallyDrop<
                #variant_struct_ident #ty_generics
            >,
        })
    });

    quote! {
        #[repr(C)]
        #[allow(non_snake_case)]
        union #variants_union_ident #generics {
            #(#fields)*
            // Enums can have variants with no fields, but unions must
            // have at least one field. So we just add a trailing unit
            // to ensure that this union always has at least one field.
            // Because this union is `repr(C)`, this unit type does not
            // affect the layout.
            #nonempty_field_ident: (),
        }
    }
}

/// Generates an implementation of `is_bit_valid` for an arbitrary enum.
///
/// The general process is:
///
/// 1. Generate a tag enum. This is an enum with the same repr, variants, and
///    corresponding discriminants as the original enum, but without any fields
///    on the variants. This gives us access to an enum where the variants have
///    the same discriminants as the one we're writing `is_bit_valid` for.
/// 2. Make constants from the variants of the tag enum. We need these because
///    we can't put const exprs in match arms.
/// 3. Generate variant structs. These are structs which have the same fields as
///    each variant of the enum, and are `#[repr(C)]` with an optional "inner
///    tag".
/// 4. Generate a variants union, with one field for each variant struct type.
/// 5. And finally, our raw enum is a `#[repr(C)]` struct of an "outer tag" and
///    the variants union.
///
/// See these reference links for fully-worked example decompositions.
///
/// - `repr(C)`: <https://doc.rust-lang.org/reference/type-layout.html#reprc-enums-with-fields>
/// - `repr(int)`: <https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-enums-with-fields>
/// - `repr(C, int)`: <https://doc.rust-lang.org/reference/type-layout.html#combining-primitive-representations-of-enums-with-fields-and-reprc>
pub(crate) fn derive_is_bit_valid(mut ctx: Ctx<'_, DataEnum>, reprs: &[EnumRepr]) -> TokenStream {
    let repr =
        tag_repr(reprs).expect("cannot derive is_bit_valid for enum without a well-defined repr");

    let trait_path = Trait::TryFromBytes.crate_path();
    let tag_enum = generate_tag_enum(ctx.reborrow(), repr);
    let tag_consts = generate_tag_consts(ctx.reborrow());

    let tag_type_ident = ctx.call_site_ident("Tag");
    let (outer_tag_type, inner_tag_type) = if matches!(repr, EnumRepr::C) {
        (quote! { #tag_type_ident }, quote! { () })
    } else {
        (quote! { () }, quote! { #tag_type_ident })
    };

    let generics = &ctx.ast.generics;
    let variant_structs = generate_variant_structs(ctx.reborrow());
    let variants_union = generate_variants_union(ctx.reborrow());

    let aliasing_ty_ident = ctx.aliasing_ty_ident();
    let tag_primitive_alias_ident = ctx.tag_primitive_alias_ident();
    let tag_enum_ident = ctx.tag_enum_ident();
    let outer_tag_alias_ident = ctx.outer_tag_alias_ident();
    let inner_tag_alias_ident = ctx.inner_tag_alias_ident();
    let variants_union_ident = ctx.variants_union_ident();
    let raw_enum_struct_ident = ctx.raw_enum_struct_ident();

    let (_, ty_generics, _) = generics.split_for_impl();
    let match_arms = ctx.data.variants.iter().map(|variant| {
        let tag_ident = ctx.reborrow().tag_const_ident(&variant.ident);
        let variant_struct_ident = ctx.reborrow().variant_struct_ident(&variant.ident);

        if matches!(variant.fields, Fields::Unit) {
            // Unit variants don't need any further validation beyond checking
            // the tag.
            quote! {
                #tag_ident => true
            }
        } else {
            let variants_union_ident = ctx.variants_union_ident();
            quote! {
                #tag_ident => {
                    // SAFETY:
                    // - This cast is from a `repr(C)` union which has a field
                    //   of type `variant_struct_ident` to that variant struct
                    //   type itself. This addresses a subset of the bytes
                    //   addressed by `variants`.
                    // - The returned pointer is cast from `p`, and so has the
                    //   same provenance as `p`.
                    // - We checked that the tag of the enum matched the
                    //   constant for this variant, so this cast preserves
                    //   types and locations of all fields. Therefore, any
                    //   `UnsafeCell`s will have the same location as in the
                    //   original type.
                    let variant = unsafe {
                        variants.cast_unsized(
                            |p: *mut #variants_union_ident #ty_generics| {
                                p as *mut #variant_struct_ident #ty_generics
                            }
                        )
                    };
                    // SAFETY: `cast_unsized` removes the initialization
                    // invariant from `p`, so we re-assert that all of the bytes
                    // are initialized.
                    let variant = unsafe { variant.assume_initialized() };
                    <
                        #variant_struct_ident #ty_generics as #trait_path
                    >::is_bit_valid(variant)
                }
            }
        }
    });

    quote! {
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern of the
        // enum's tag corresponds to one of the enum's discriminants. Then, we
        // check the bit validity of each field of the corresponding variant.
        // Thus, this is a sound implementation of `is_bit_valid`.
        fn is_bit_valid<#aliasing_ty_ident>(
            mut candidate: ::zerocopy::Maybe<'_, Self, #aliasing_ty_ident>,
        ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
        where
            #aliasing_ty_ident: ::zerocopy::pointer::invariant::Aliasing
                + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
        {
            use ::zerocopy::util::macro_util::core_reexport;

            #tag_enum

            type #tag_primitive_alias_ident = ::zerocopy::util::macro_util::SizeToTag<
                { core_reexport::mem::size_of::<#tag_enum_ident>() },
            >;

            #tag_consts

            type #outer_tag_alias_ident = #outer_tag_type;
            type #inner_tag_alias_ident = #inner_tag_type;

            #variant_structs

            #variants_union

            #[repr(C)]
            struct #raw_enum_struct_ident #generics {
                tag: #outer_tag_alias_ident,
                variants: #variants_union_ident #ty_generics,
            }

            let tag = {
                // SAFETY:
                // - The provided cast addresses a subset of the bytes addressed
                //   by `candidate` because it addresses the starting tag of the
                //   enum.
                // - Because the pointer is cast from `candidate`, it has the
                //   same provenance as it.
                // - There are no `UnsafeCell`s in the tag because it is a
                //   primitive integer.
                let tag_ptr = unsafe {
                    candidate.reborrow().cast_unsized(|p: *mut Self| {
                        p as *mut #tag_primitive_alias_ident
                    })
                };
                // SAFETY: `tag_ptr` is casted from `candidate`, whose referent
                // is `Initialized`. Since we have not written uninitialized
                // bytes into the referent, `tag_ptr` is also `Initialized`.
                let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                tag_ptr.bikeshed_recall_valid().read_unaligned()
            };

            // SAFETY:
            // - The raw enum has the same fields in the same locations as the
            //   input enum, and may have a lower alignment. This guarantees
            //   that it addresses a subset of the bytes addressed by
            //   `candidate`.
            // - The returned pointer is cast from `p`, and so has the same
            //   provenance as `p`.
            // - The raw enum has the same types at the same locations as the
            //   original enum, and so preserves the locations of any
            //   `UnsafeCell`s.
            let raw_enum = unsafe {
                candidate.cast_unsized(|p: *mut Self| {
                    p as *mut #raw_enum_struct_ident #ty_generics
                })
            };
            // SAFETY: `cast_unsized` removes the initialization invariant from
            // `p`, so we re-assert that all of the bytes are initialized.
            let raw_enum = unsafe { raw_enum.assume_initialized() };
            // SAFETY:
            // - This projection returns a subfield of `this` using
            //   `addr_of_mut!`.
            // - Because the subfield pointer is derived from `this`, it has the
            //   same provenance.
            // - The locations of `UnsafeCell`s in the subfield match the
            //   locations of `UnsafeCell`s in `this`. This is because the
            //   subfield pointer just points to a smaller portion of the
            //   overall struct.
            let variants = unsafe {
                raw_enum.project(|p: *mut #raw_enum_struct_ident #ty_generics| {
                    core_reexport::ptr::addr_of_mut!((*p).variants)
                })
            };

            #[allow(non_upper_case_globals)]
            match tag {
                #(#match_arms,)*
                _ => false,
            }
        }
    }
}

pub(crate) trait EnumCtxExt {
    fn tag_enum_ident(&mut self) -> Ident;
    fn tag_const_ident(&mut self, variant_ident: &Ident) -> Ident;
    fn tag_primitive_alias_ident(&mut self) -> Ident;
    fn inner_tag_alias_ident(&mut self) -> Ident;
    fn outer_tag_alias_ident(&mut self) -> Ident;
    fn variant_struct_ident(&mut self, variant_ident: &Ident) -> Ident;
    fn variants_union_ident(&mut self) -> Ident;
    fn nonempty_field_ident(&mut self) -> Ident;
    fn raw_enum_struct_ident(&mut self) -> Ident;
    fn aliasing_ty_ident(&mut self) -> Ident;
}

impl<'a> EnumCtxExt for Ctx<'a, DataEnum> {
    fn tag_enum_ident(&mut self) -> Ident {
        self.call_site_ident("Tag")
    }

    fn tag_const_ident(&mut self, variant_ident: &Ident) -> Ident {
        self.spanned_ident(&format!("TAG_{}", variant_ident), variant_ident.span())
    }

    fn tag_primitive_alias_ident(&mut self) -> Ident {
        self.call_site_ident("TagPrimitive")
    }

    fn inner_tag_alias_ident(&mut self) -> Ident {
        self.call_site_ident("InnerTag")
    }

    fn outer_tag_alias_ident(&mut self) -> Ident {
        self.call_site_ident("OuterTag")
    }

    fn variant_struct_ident(&mut self, variant_ident: &Ident) -> Ident {
        self.spanned_ident(&format!("VariantStruct_{}", variant_ident), variant_ident.span())
    }

    fn variants_union_ident(&mut self) -> Ident {
        self.call_site_ident("Variants")
    }

    fn nonempty_field_ident(&mut self) -> Ident {
        self.call_site_ident("nonempty")
    }

    fn raw_enum_struct_ident(&mut self) -> Ident {
        self.call_site_ident("RawEnum")
    }

    fn aliasing_ty_ident(&mut self) -> Ident {
        self.call_site_ident("Aliasing")
    }
}
