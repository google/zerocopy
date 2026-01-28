//! [`Debug`](trait@std::fmt::Debug) implementation.

use std::ops::Deref;

use proc_macro2::TokenStream;
use quote::quote;

use crate::{
	util, Data, DeriveTrait, DeriveWhere, Item, SimpleType, SplitGenerics, Trait, TraitImpl,
};

/// [`TraitImpl`] for [`Debug`](trait@std::fmt::Debug).
pub struct Debug;

impl TraitImpl for Debug {
	fn as_str() -> &'static str {
		"Debug"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Debug
	}

	fn path(&self) -> syn::Path {
		util::path_from_strs(&["core", "fmt", "Debug"])
	}

	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		_item: &Item,
		_generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		quote! {
			fn fmt(&self, __f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
				match self {
					#body
				}
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		let self_pattern = &data.self_pattern();
		let debug_name = data.ident.to_string();

		match data.simple_type() {
			SimpleType::Struct(_) => {
				let self_ident = data.iter_self_ident(**self);
				let debug_fields = data.iter_field_ident(**self).map(|field| field.to_string());

				let finish = if data.any_skip_trait(**self) {
					quote! { finish_non_exhaustive }
				} else {
					quote! { finish }
				};

				quote! {
					#self_pattern => {
						let mut __builder = ::core::fmt::Formatter::debug_struct(__f, #debug_name);
						#(::core::fmt::DebugStruct::field(&mut __builder, #debug_fields, #self_ident);)*
						::core::fmt::DebugStruct::#finish(&mut __builder)
					}
				}
			}
			SimpleType::Tuple(_) => {
				let self_ident = data.iter_self_ident(**self);

				quote! {
					#self_pattern => {
						let mut __builder = ::core::fmt::Formatter::debug_tuple(__f, #debug_name);
						#(::core::fmt::DebugTuple::field(&mut __builder, #self_ident);)*
						::core::fmt::DebugTuple::finish(&mut __builder)
					}
				}
			}
			SimpleType::Unit(_) => {
				quote! { #self_pattern => ::core::fmt::Formatter::write_str(__f, #debug_name), }
			}
			SimpleType::Union => unreachable!("unexpected trait for union"),
		}
	}
}

impl Deref for Debug {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Debug
	}
}
