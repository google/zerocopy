//! [`Serialize`](https://docs.rs/serde/latest/serde/derive.Serialize.html) implementation.

use std::{borrow::Cow, ops::Deref};

use proc_macro2::{Span, TokenStream};
use quote::format_ident;
use syn::{
	punctuated::Punctuated, Attribute, DeriveInput, Ident, ImplGenerics, Meta, Path, Result,
	TypeGenerics, WhereClause,
};

use super::serde;
use crate::{util, DeriveTrait, Trait, TraitImpl};

/// [`TraitImpl`] for [`Serialize`](https://docs.rs/serde/latest/serde/derive.Serialize.html).
#[derive(Eq, PartialEq)]
pub struct Serialize {
	/// [`Serialize`](https://docs.rs/serde/latest/serde/derive.Serialize.html) path.
	pub crate_: Option<Path>,
}

impl TraitImpl for Serialize {
	fn as_str() -> &'static str
	where
		Self: Sized,
	{
		"Serialize"
	}

	fn default_derive_trait() -> super::DeriveTrait
	where
		Self: Sized,
	{
		DeriveTrait::Serialize(Self { crate_: None })
	}

	fn parse_derive_trait(
		attrs: &[Attribute],
		span: Span,
		list: Option<Punctuated<Meta, syn::Token![,]>>,
	) -> Result<DeriveTrait>
	where
		Self: Sized,
	{
		Ok(DeriveTrait::Serialize(Self {
			crate_: serde::parse_derive_trait(Trait::Serialize, attrs, span, list)?,
		}))
	}

	fn path(&self) -> Path {
		util::path_from_root_and_strs(self.crate_(), &["Serialize"])
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
			format_ident!("Serialize"),
			format_ident!("serialize"),
			full_item,
			where_clause,
		)
	}
}

impl Serialize {
	/// Returns the path to the root crate for this trait.
	fn crate_(&self) -> Path {
		if let Some(crate_) = &self.crate_ {
			crate_.clone()
		} else {
			util::path_from_strs(&["serde"])
		}
	}
}

impl Deref for Serialize {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Serialize
	}
}
