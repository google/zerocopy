//! [`Deserialize`](https://docs.rs/serde/latest/serde/derive.Deserialize.html) implementation.

use std::{borrow::Cow, ops::Deref};

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
	punctuated::Punctuated, Attribute, DeriveInput, Ident, ImplGenerics, Meta, Path, Result,
	TypeGenerics, WhereClause,
};

use super::serde;
use crate::{util, DeriveTrait, Trait, TraitImpl};

/// [`TraitImpl`] for [`Deserialize`](https://docs.rs/serde/latest/serde/derive.Deserialize.html).
#[derive(Eq, PartialEq)]
pub struct Deserialize {
	/// [`Deserialize`](https://docs.rs/serde/latest/serde/derive.Deserialize.html) path.
	pub crate_: Option<Path>,
}

impl TraitImpl for Deserialize {
	fn as_str() -> &'static str
	where
		Self: Sized,
	{
		"Deserialize"
	}

	fn default_derive_trait() -> super::DeriveTrait
	where
		Self: Sized,
	{
		DeriveTrait::Deserialize(Self { crate_: None })
	}

	fn parse_derive_trait(
		attrs: &[Attribute],
		span: Span,
		list: Option<Punctuated<Meta, syn::Token![,]>>,
	) -> Result<DeriveTrait>
	where
		Self: Sized,
	{
		Ok(DeriveTrait::Deserialize(Self {
			crate_: serde::parse_derive_trait(Trait::Deserialize, attrs, span, list)?,
		}))
	}

	fn path(&self) -> Path {
		let crate_ = self.crate_();
		syn::parse2::<Path>(quote! { #crate_::Deserialize<'de> }).unwrap()
	}

	fn impl_item(
		&self,
		crate_: Option<&Path>,
		full_item: &DeriveInput,
		_: &ImplGenerics<'_>,
		_: &Ident,
		_: &TypeGenerics<'_>,
		where_clause: &Option<Cow<'_, WhereClause>>,
		_: TokenStream,
	) -> TokenStream {
		serde::impl_item(
			crate_,
			&self.crate_(),
			format_ident!("Deserialize"),
			format_ident!("deserialize"),
			full_item,
			where_clause,
		)
	}
}

impl Deserialize {
	/// Returns the path to the root crate for this trait.
	fn crate_(&self) -> Path {
		if let Some(crate_) = &self.crate_ {
			crate_.clone()
		} else {
			util::path_from_strs(&["serde"])
		}
	}
}

impl Deref for Deserialize {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Deserialize
	}
}
