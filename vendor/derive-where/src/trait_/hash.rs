//! [`Hash`](trait@std::hash::Hash) implementation.

use std::ops::Deref;

use proc_macro2::TokenStream;
use quote::quote;

use crate::{
	util, Data, DataType, DeriveTrait, DeriveWhere, Item, SimpleType, SplitGenerics, Trait,
	TraitImpl,
};

/// [`TraitImpl`] for [`Hash`](trait@std::hash::Hash).
pub struct Hash;

impl TraitImpl for Hash {
	fn as_str() -> &'static str {
		"Hash"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Hash
	}

	fn path(&self) -> syn::Path {
		util::path_from_strs(&["core", "hash", "Hash"])
	}

	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		_item: &Item,
		_generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		quote! {
			fn hash<__H: ::core::hash::Hasher>(&self, __state: &mut __H) {
				match self {
					#body
				}
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		let self_pattern = data.self_pattern();
		let trait_path = self.path();

		// Add hashing the variant if this is an enum.
		let discriminant = if let DataType::Variant { .. } = data.type_ {
			Some(quote! { #trait_path::hash(&::core::mem::discriminant(self), __state); })
		} else {
			None
		};

		match data.simple_type() {
			SimpleType::Struct(_) | SimpleType::Tuple(_) => {
				let self_ident = data.iter_self_ident(**self);

				quote! {
					#self_pattern => {
						#discriminant
						#(#trait_path::hash(#self_ident, __state);)*
					}
				}
			}
			SimpleType::Unit(_) => {
				quote! {
					#self_pattern => {
						#discriminant
					}
				}
			}
			SimpleType::Union => unreachable!("unexpected trait for union"),
		}
	}
}

impl Deref for Hash {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Hash
	}
}
