//! [`Default`](trait@std::default::Default) implementation.

use std::ops::Deref;

use proc_macro2::TokenStream;
use quote::quote;

use crate::{
	util, Data, DeriveTrait, DeriveWhere, Item, SimpleType, SplitGenerics, Trait, TraitImpl,
};

/// [`TraitImpl`] for [`Default`](trait@std::default::Default).
pub struct Default;

impl TraitImpl for Default {
	fn as_str() -> &'static str {
		"Default"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Default
	}

	fn path(&self) -> syn::Path {
		util::path_from_strs(&["core", "default", "Default"])
	}

	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		_item: &Item,
		_generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		quote! {
			fn default() -> Self {
				#body
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		if data.is_default() {
			let path = &data.path;

			match data.simple_type() {
				SimpleType::Struct(_) => {
					let fields = data.iter_field_ident(**self);
					let trait_path = self.path();

					quote! { #path { #(#fields: #trait_path::default()),* } }
				}
				SimpleType::Tuple(_) => {
					let trait_path = self.path();
					let fields = data
						.iter_fields(**self)
						.map(|_| quote! { #trait_path::default() });

					quote! { #path(#(#fields),*) }
				}
				SimpleType::Unit(_) => {
					quote! { #path }
				}
				SimpleType::Union => unreachable!("unexpected trait for union"),
			}
		}
		// Skip `Default` implementation if variant isn't marked with a `default` attribute.
		else {
			TokenStream::new()
		}
	}
}

impl Deref for Default {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Default
	}
}
