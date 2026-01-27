//! [`Eq`](trait@std::cmp::Eq) implementation.

use std::{borrow::Cow, ops::Deref};

use proc_macro2::TokenStream;
use quote::quote;
use syn::{DeriveInput, Ident, ImplGenerics, Path, TypeGenerics, WhereClause};

use crate::{util, Data, DeriveTrait, DeriveWhere, Item, SplitGenerics, Trait, TraitImpl};

/// [`TraitImpl`] for [`Eq`](trait@std::cmp::Eq).
pub struct Eq;

impl TraitImpl for Eq {
	fn as_str() -> &'static str {
		"Eq"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Eq
	}

	fn path(&self) -> Path {
		util::path_from_strs(&["core", "cmp", "Eq"])
	}

	fn additional_impl(&self) -> Option<(Path, TokenStream)> {
		Some((self.path(), quote! {}))
	}

	fn impl_item(
		&self,
		_: Option<&Path>,
		_: &DeriveInput,
		imp: &ImplGenerics<'_>,
		ident: &Ident,
		ty: &TypeGenerics<'_>,
		where_clause: &Option<Cow<'_, WhereClause>>,
		body: TokenStream,
	) -> TokenStream {
		quote! {
			const _: () = {
				trait DeriveWhereAssertEq {
					fn assert(&self);
				}

				impl #imp DeriveWhereAssertEq for #ident #ty
				#where_clause
				{
					#body
				}
			};
		}
	}

	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		_item: &Item,
		_generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		quote! {
			fn assert(&self) {
				struct __AssertEq<__T: ::core::cmp::Eq + ?::core::marker::Sized>(::core::marker::PhantomData<__T>);

				#body
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		let types = data.iter_fields(**self).map(|field| field.type_);

		quote! {
			#(let _: __AssertEq<#types>;)*
		}
	}
}

impl Deref for Eq {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Eq
	}
}
