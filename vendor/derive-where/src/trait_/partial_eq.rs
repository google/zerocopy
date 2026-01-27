//! [`PartialEq`](trait@std::cmp::PartialEq) implementation.

use std::ops::Deref;

use proc_macro2::TokenStream;
use quote::quote;

use super::common_ord::build_incomparable_pattern;
use crate::{
	util, Data, DeriveTrait, DeriveWhere, Item, SimpleType, SplitGenerics, Trait, TraitImpl,
};

/// [`TraitImpl`] for [`PartialEq`](trait@std::cmp::PartialEq).
pub struct PartialEq;

impl TraitImpl for PartialEq {
	fn as_str() -> &'static str {
		"PartialEq"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::PartialEq
	}

	fn path(&self) -> syn::Path {
		util::path_from_strs(&["core", "cmp", "PartialEq"])
	}

	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		item: &Item,
		_generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		let body = {
			match item {
				// If the whole item is incomparable return false
				item if item.is_incomparable() => {
					quote! { false }
				}
				// If there is more than one variant and not all variants are empty, check for
				// discriminant and match on variant data.
				Item::Enum { variants, .. } if variants.len() > 1 && !item.is_empty(**self) => {
					// Return `true` in the rest pattern if there are any empty variants
					// that are not incomparable.
					let rest = if variants
						.iter()
						.any(|variant| variant.is_empty(**self) && !variant.is_incomparable())
					{
						quote! { true }
					} else {
						#[cfg(not(feature = "safe"))]
						// This follows the standard implementation.
						quote! { unsafe { ::core::hint::unreachable_unchecked() } }
						#[cfg(feature = "safe")]
						quote! { ::core::unreachable!("comparing variants yielded unexpected results") }
					};

					// Return `false` for all incomparable variants
					let incomparable = build_incomparable_pattern(variants).into_iter();

					quote! {
						if ::core::mem::discriminant(self) == ::core::mem::discriminant(__other) {
							match (self, __other) {
								#body
								#((#incomparable, ..) => false,)*
								_ => #rest,
							}
						} else {
							false
						}
					}
				}
				// If there is more than one variant and all are empty, check for
				// discriminant and simply return `true` if it is not incomparable.
				Item::Enum { variants, .. } if variants.len() > 1 && item.is_empty(**self) => {
					let incomparable = build_incomparable_pattern(variants).into_iter();
					quote! {
						if ::core::mem::discriminant(self) == ::core::mem::discriminant(__other) {
							#(if ::core::matches!(self, #incomparable) {
								return false;
							})*
							true
						} else {
							false
						}
					}
				}
				// If there is only one variant and it's empty or if the struct is empty, simply
				// return `true`.
				item if item.is_empty(**self) => {
					quote! { true }
				}
				_ => {
					quote! {
						match (self, __other) {
							#body
						}
					}
				}
			}
		};

		quote! {
			#[inline]
			fn eq(&self, __other: &Self) -> bool {
				#body
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		if data.is_empty(**self) || data.is_incomparable() {
			TokenStream::new()
		} else {
			match data.simple_type() {
				SimpleType::Struct(fields) | SimpleType::Tuple(fields) => {
					let self_pattern = &fields.self_pattern;
					let other_pattern = &fields.other_pattern;
					let trait_path = self.path();
					let self_ident = data.iter_self_ident(**self);
					let other_ident = data.iter_other_ident(**self);

					quote! {
						(#self_pattern, #other_pattern) =>
							true #(&& #trait_path::eq(#self_ident, #other_ident))*,
					}
				}
				SimpleType::Unit(_) => TokenStream::new(),
				SimpleType::Union => unreachable!("unexpected trait for union"),
			}
		}
	}
}

impl Deref for PartialEq {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::PartialEq
	}
}
