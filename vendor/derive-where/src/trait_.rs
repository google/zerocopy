//! Individual implementation for all traits.

pub mod clone;
mod common_ord;
pub mod copy;
pub mod debug;
pub mod default;
#[cfg(feature = "serde")]
pub mod deserialize;
pub mod eq;
pub mod hash;
pub mod ord;
pub mod partial_eq;
pub mod partial_ord;
#[cfg(feature = "serde")]
mod serde;
#[cfg(feature = "serde")]
pub mod serialize;
#[cfg(feature = "zeroize")]
pub mod zeroize;
#[cfg(feature = "zeroize")]
pub mod zeroize_on_drop;

use std::{borrow::Cow, ops::Deref};

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
	parse::{Parse, ParseStream},
	punctuated::Punctuated,
	spanned::Spanned,
	Attribute, DeriveInput, Ident, ImplGenerics, Meta, Path, Result, Token, TraitBound,
	TraitBoundModifier, TypeGenerics, TypeParamBound, WhereClause,
};

use crate::{util::MetaListExt, Data, DeriveWhere, Error, Item, SplitGenerics};

/// Type implementing [`TraitImpl`] for every trait.
#[derive(Clone, Copy, Eq, PartialEq)]
#[cfg_attr(test, derive(Debug))]
pub enum Trait {
	/// [`Clone`].
	Clone,
	/// [`Copy`].
	Copy,
	/// [`Debug`](std::fmt::Debug).
	Debug,
	/// [`Default`].
	Default,
	/// [`Deserialize`](https://docs.rs/serde/latest/serde/derive.Deserialize.html).
	#[cfg(feature = "serde")]
	Deserialize,
	/// [`Eq`].
	Eq,
	/// [`Hash`](std::hash::Hash).
	Hash,
	/// [`Ord`].
	Ord,
	/// [`PartialEq`].
	PartialEq,
	/// [`PartialOrd`].
	PartialOrd,
	/// [`Serialize`](https://docs.rs/serde/latest/serde/derive.Serialize.html).
	#[cfg(feature = "serde")]
	Serialize,
	/// [`Zeroize`](https://docs.rs/zeroize/latest/zeroize/trait.Zeroize.html).
	#[cfg(feature = "zeroize")]
	Zeroize,
	/// [`ZeroizeOnDrop`](https://docs.rs/zeroize/latest/zeroize/trait.ZeroizeOnDrop.html).
	#[cfg(feature = "zeroize")]
	ZeroizeOnDrop,
}

macro_rules! trait_dispatch {
	($self:expr, $method:ident($($par:expr),*)) => {
		match $self {
			Trait::Clone => clone::Clone::$method($($par),*),
			Trait::Copy => copy::Copy::$method($($par),*),
			Trait::Debug => debug::Debug::$method($($par),*),
			Trait::Default => default::Default::$method($($par),*),
			#[cfg(feature = "serde")]
			Trait::Deserialize => deserialize::Deserialize::$method($($par),*),
			Trait::Eq => eq::Eq::$method($($par),*),
			Trait::Hash => hash::Hash::$method($($par),*),
			Trait::Ord => ord::Ord::$method($($par),*),
			Trait::PartialEq => partial_eq::PartialEq::$method($($par),*),
			Trait::PartialOrd => partial_ord::PartialOrd::$method($($par),*),
			#[cfg(feature = "serde")]
			Trait::Serialize => serialize::Serialize::$method($($par),*),
			#[cfg(feature = "zeroize")]
			Trait::Zeroize => zeroize::Zeroize::$method($($par),*),
			#[cfg(feature = "zeroize")]
			Trait::ZeroizeOnDrop => zeroize_on_drop::ZeroizeOnDrop::$method($($par),*),
		}
	};
}

impl Trait {
	/// Create [`Trait`] from [`Path`].
	pub fn from_path(path: &Path) -> Result<Self> {
		if let Some(ident) = path.get_ident() {
			use Trait::*;

			match ident.to_string().as_str() {
				"Clone" => Ok(Clone),
				"Copy" => Ok(Copy),
				"Debug" => Ok(Debug),
				"Default" => Ok(Default),
				#[cfg(feature = "serde")]
				"Deserialize" => Ok(Deserialize),
				#[cfg(not(feature = "serde"))]
				"Deserialize" => Err(Error::serde_feature(path.span())),
				"Eq" => Ok(Eq),
				"Hash" => Ok(Hash),
				"Ord" => Ok(Ord),
				"PartialEq" => Ok(PartialEq),
				"PartialOrd" => Ok(PartialOrd),
				#[cfg(feature = "serde")]
				"Serialize" => Ok(Serialize),
				#[cfg(not(feature = "serde"))]
				"Serialize" => Err(Error::serde_feature(path.span())),
				#[cfg(feature = "zeroize")]
				"Zeroize" => Ok(Zeroize),
				#[cfg(not(feature = "zeroize"))]
				"Zeroize" => Err(Error::zeroize_feature(path.span())),
				#[cfg(feature = "zeroize")]
				"ZeroizeOnDrop" => Ok(ZeroizeOnDrop),
				#[cfg(not(feature = "zeroize"))]
				"ZeroizeOnDrop" => Err(Error::zeroize_feature(path.span())),
				"crate" => Err(Error::crate_(path.span())),
				_ => Err(Error::trait_(path.span())),
			}
		} else {
			Err(Error::trait_(path.span()))
		}
	}

	/// Re-direct to [`TraitImpl::as_str()`].
	pub fn as_str(&self) -> &'static str {
		trait_dispatch!(self, as_str())
	}

	/// Re-direct to [`TraitImpl::default_derive_trait()`].
	pub fn default_derive_trait(&self) -> DeriveTrait {
		trait_dispatch!(self, default_derive_trait())
	}

	/// Re-direct to [`TraitImpl::parse_derive_trait()`].
	pub fn parse_derive_trait(
		&self,
		attrs: &[Attribute],
		span: Span,
		list: Option<Punctuated<Meta, Token![,]>>,
	) -> Result<DeriveTrait> {
		trait_dispatch!(self, parse_derive_trait(attrs, span, list))
	}

	/// Re-direct to [`TraitImpl::supports_union()`].
	pub fn supports_union(&self) -> bool {
		trait_dispatch!(self, supports_union())
	}

	/// Re-direct to [`TraitImpl::additional_where_bounds()`].
	pub fn additional_where_bounds(&self, data: &Item) -> Option<TypeParamBound> {
		trait_dispatch!(self, additional_where_bounds(data))
	}
}

/// Trait to implement.
#[derive(Eq, PartialEq)]
pub enum DeriveTrait {
	/// [`Clone`].
	Clone,
	/// [`Copy`].
	Copy,
	/// [`Debug`](std::fmt::Debug).
	Debug,
	/// [`Default`].
	Default,
	/// [`Deserialize`](https://docs.rs/serde/latest/serde/derive.Deserialize.html).
	#[cfg(feature = "serde")]
	Deserialize(deserialize::Deserialize),
	/// [`Eq`].
	Eq,
	/// [`Hash`](std::hash::Hash).
	Hash,
	/// [`Ord`].
	Ord,
	/// [`PartialEq`].
	PartialEq,
	/// [`PartialOrd`].
	PartialOrd,
	/// [`Serialize`](https://docs.rs/serde/latest/serde/derive.Serialize.html).
	#[cfg(feature = "serde")]
	Serialize(serialize::Serialize),
	/// [`Zeroize`](https://docs.rs/zeroize/latest/zeroize/trait.Zeroize.html).
	#[cfg(feature = "zeroize")]
	Zeroize(zeroize::Zeroize),
	/// [`ZeroizeOnDrop`](https://docs.rs/zeroize/latest/zeroize/trait.ZeroizeOnDrop.html).
	#[cfg(feature = "zeroize")]
	ZeroizeOnDrop(zeroize_on_drop::ZeroizeOnDrop),
}

impl Deref for DeriveTrait {
	type Target = dyn TraitImpl;

	fn deref(&self) -> &Self::Target {
		use DeriveTrait::*;

		match self {
			Clone => &clone::Clone,
			Copy => &copy::Copy,
			Debug => &debug::Debug,
			Default => &default::Default,
			#[cfg(feature = "serde")]
			Deserialize(trait_) => trait_,
			Eq => &eq::Eq,
			Hash => &hash::Hash,
			Ord => &ord::Ord,
			PartialEq => &partial_eq::PartialEq,
			PartialOrd => &partial_ord::PartialOrd,
			#[cfg(feature = "serde")]
			Serialize(trait_) => trait_,
			#[cfg(feature = "zeroize")]
			Zeroize(trait_) => trait_,
			#[cfg(feature = "zeroize")]
			ZeroizeOnDrop(trait_) => trait_,
		}
	}
}

impl PartialEq<Trait> for &DeriveTrait {
	fn eq(&self, other: &Trait) -> bool {
		let trait_: &Trait = self;
		trait_ == other
	}
}

impl DeriveTrait {
	/// Returns where-clause bounds for the trait in respect of the item type.
	pub fn where_bounds(&self, data: &Item) -> Punctuated<TypeParamBound, Token![+]> {
		let mut list = Punctuated::new();

		list.push(TypeParamBound::Trait(TraitBound {
			paren_token: None,
			modifier: TraitBoundModifier::None,
			lifetimes: None,
			path: self.path(),
		}));

		// Add bounds specific to the trait.
		if let Some(bound) = self.additional_where_bounds(data) {
			list.push(bound)
		}

		list
	}

	/// Create [`DeriveTrait`] from [`ParseStream`].
	pub fn from_stream(
		attrs: &[Attribute],
		span: Span,
		data: &syn::Data,
		input: ParseStream,
	) -> Result<(Span, Self)> {
		match Meta::parse(input) {
			Ok(meta) => {
				let trait_ = Trait::from_path(meta.path())?;

				if let syn::Data::Union(_) = data {
					// Make sure this `Trait` supports unions.
					if !trait_.supports_union() {
						return Err(Error::union(span));
					}
				}

				match &meta {
					Meta::Path(path) => Ok((
						path.span(),
						trait_.parse_derive_trait(attrs, meta.span(), None)?,
					)),
					Meta::List(list) => {
						let nested = list.parse_non_empty_nested_metas()?;

						// This will return an error if no options are supported.
						Ok((
							list.span(),
							trait_.parse_derive_trait(attrs, meta.span(), Some(nested))?,
						))
					}
					Meta::NameValue(name_value) => Err(Error::option_syntax(name_value.span())),
				}
			}
			Err(error) => Err(Error::trait_syntax(error.span())),
		}
	}
}

/// Single trait implementation. Parses attributes and constructs `impl`s.
pub trait TraitImpl: Deref<Target = Trait> {
	/// [`str`] representation of this [`Trait`].
	/// Used to compare against [`Ident`](struct@syn::Ident)s and create error
	/// messages.
	fn as_str() -> &'static str
	where
		Self: Sized;

	/// Associated [`DeriveTrait`].
	fn default_derive_trait() -> DeriveTrait
	where
		Self: Sized;

	/// Parse a `derive_where` trait with it's options.
	fn parse_derive_trait(
		_attrs: &[Attribute],
		span: Span,
		list: Option<Punctuated<Meta, Token![,]>>,
	) -> Result<DeriveTrait>
	where
		Self: Sized,
	{
		if list.is_some() {
			Err(Error::options(span, Self::as_str()))
		} else {
			Ok(Self::default_derive_trait())
		}
	}

	/// Returns `true` if [`Trait`] supports unions.
	fn supports_union() -> bool
	where
		Self: Sized,
	{
		false
	}

	/// Additional bounds to add to [`WhereClause`].
	fn additional_where_bounds(_data: &Item) -> Option<TypeParamBound>
	where
		Self: Sized,
	{
		None
	}

	/// Returns fully qualified [`Path`] for this trait.
	fn path(&self) -> Path;

	/// Additional implementation to add for this [`Trait`].
	fn additional_impl(&self) -> Option<(Path, TokenStream)> {
		None
	}

	/// Trait to implement. Only used by [`Eq`] and
	/// [`ZeroizeOnDrop`](https://docs.rs/zeroize/latest/zeroize/trait.ZeroizeOnDrop.html).
	#[allow(clippy::too_many_arguments)]
	fn impl_item(
		&self,
		_crate_: Option<&Path>,
		_full_item: &DeriveInput,
		imp: &ImplGenerics<'_>,
		ident: &Ident,
		ty: &TypeGenerics<'_>,
		where_clause: &Option<Cow<'_, WhereClause>>,
		body: TokenStream,
	) -> TokenStream {
		let path = self.path();

		quote! {
			#[automatically_derived]
			impl #imp #path for #ident #ty
			#where_clause
			{
				#body
			}
		}
	}

	/// Build method signature for this [`Trait`].
	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		_item: &Item,
		_generics: &SplitGenerics<'_>,
		_body: &TokenStream,
	) -> TokenStream {
		TokenStream::new()
	}

	/// Build method body for this [`Trait`].
	fn build_body(&self, _derive_where: &DeriveWhere, _data: &Data) -> TokenStream {
		TokenStream::new()
	}
}
