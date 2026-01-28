//! [`Ord`](trait@std::cmp::Ord) implementation.

use std::ops::Deref;

use proc_macro2::TokenStream;
use quote::quote;

use super::common_ord;
use crate::{
	util, Data, DeriveTrait, DeriveWhere, Item, SimpleType, SplitGenerics, Trait, TraitImpl,
};

/// [`TraitImpl`] for [`Ord`](trait@std::cmp::Ord).
pub struct Ord;

impl TraitImpl for Ord {
	fn as_str() -> &'static str {
		"Ord"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Ord
	}

	fn path(&self) -> syn::Path {
		util::path_from_strs(&["core", "cmp", "Ord"])
	}

	fn build_signature(
		&self,
		derive_where: &DeriveWhere,
		item: &Item,
		generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		let body = common_ord::build_ord_signature(item, generics, derive_where, self, body);

		quote! {
			#[inline]
			fn cmp(&self, __other: &Self) -> ::core::cmp::Ordering {
				#body
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		if data.is_empty(**self) {
			TokenStream::new()
		} else {
			match data.simple_type() {
				SimpleType::Struct(fields) | SimpleType::Tuple(fields) => {
					let self_pattern = &fields.self_pattern;
					let other_pattern = &fields.other_pattern;
					let body = common_ord::build_ord_body(self, data);

					quote! {
						(#self_pattern, #other_pattern) => #body,
					}
				}
				SimpleType::Unit(_) => TokenStream::new(),
				SimpleType::Union => unreachable!("unexpected trait for union"),
			}
		}
	}
}

impl Deref for Ord {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Ord
	}
}
