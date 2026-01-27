//! Common functionality between
//! [`Deserialize`](https://docs.rs/serde/latest/serde/derive.Deserialize.html) and
//! [`Serialize`](https://docs.rs/serde/latest/serde/derive.Serialize.html).

use std::borrow::Cow;

use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
	punctuated::Punctuated, spanned::Spanned, Attribute, DeriveInput, Expr, ExprLit, Ident, Lit,
	Meta, Path, Token, WhereClause,
};

use crate::{util, Error, Result, Trait, DERIVE_WHERE};

/// Parse `#[serde(crate = "...")]`.
pub fn parse_derive_trait(
	trait_: Trait,
	attrs: &[Attribute],
	span: Span,
	list: Option<Punctuated<Meta, Token![,]>>,
) -> Result<Option<Path>> {
	if list.is_some() {
		return Err(Error::options(span, trait_.as_str()));
	}

	let mut crate_ = None;

	for attr in attrs {
		if !attr.path().is_ident("serde") {
			continue;
		}

		if let Meta::List(list) = &attr.meta {
			if let Ok(nested) =
				list.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
			{
				for meta in nested {
					if meta.path().is_ident("bound") {
						return Err(Error::serde_bound(meta.span()));
					}

					if !meta.path().is_ident("crate") {
						continue;
					}

					match &meta {
						Meta::NameValue(name_value) => {
							// Check for duplicate `crate` option.
							if crate_.is_none() {
								let path = match &name_value.value {
									Expr::Lit(ExprLit {
										lit: Lit::Str(lit_str),
										..
									}) => match lit_str.parse::<Path>() {
										Ok(path) => path,
										Err(error) => {
											return Err(Error::path(lit_str.span(), error))
										}
									},
									_ => return Err(Error::option_syntax(name_value.value.span())),
								};

								crate_ = Some(path);
							} else {
								return Err(Error::option_duplicate(name_value.span(), "crate"));
							}
						}
						_ => {
							return Err(Error::option_syntax(meta.span()));
						}
					}
				}
			}
		}
	}

	Ok(crate_)
}

/// Implement Serde trait.
pub fn impl_item(
	derive_where: Option<&Path>,
	serde: &Path,
	trait_: Ident,
	bound: Ident,
	full_item: &DeriveInput,
	where_clause: &Option<Cow<'_, WhereClause>>,
) -> TokenStream {
	let derive_where = derive_where
		.map(Cow::Borrowed)
		.unwrap_or_else(|| Cow::Owned(util::path_from_strs(&[DERIVE_WHERE])));

	let bounds = if let Some(where_clause) = where_clause {
		where_clause.predicates.to_token_stream().to_string()
	} else {
		String::new()
	};

	quote! {
		#[::core::prelude::v1::derive(#serde::#trait_)]
		#[serde(bound(#bound = #bounds))]
		#[#derive_where::derive_where_serde]
		#full_item
	}
}
