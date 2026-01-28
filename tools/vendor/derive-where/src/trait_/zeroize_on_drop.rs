//! [`ZeroizeOnDrop`](https://docs.rs/zeroize/latest/zeroize/trait.ZeroizeOnDrop.html) implementation.

use std::{borrow::Cow, iter, ops::Deref};

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
	punctuated::Punctuated, spanned::Spanned, Attribute, DeriveInput, Expr, ExprLit, ExprPath,
	Ident, ImplGenerics, Lit, Meta, Path, Result, Token, TypeGenerics, WhereClause,
};

use crate::{util, DeriveTrait, DeriveWhere, Error, Item, SplitGenerics, Trait, TraitImpl};
#[cfg(feature = "zeroize-on-drop")]
use crate::{Data, SimpleType};

/// [`TraitImpl`] for [`ZeroizeOnDrop`](https://docs.rs/zeroize/latest/zeroize/trait.ZeroizeOnDrop.html).
#[derive(Eq, PartialEq)]
pub struct ZeroizeOnDrop {
	/// [`ZeroizeOnDrop`](https://docs.rs/zeroize/latest/zeroize/trait.ZeroizeOnDrop.html) path.
	pub crate_: Option<Path>,
	/// If `Drop` should be implemented.
	pub no_drop: bool,
}

impl TraitImpl for ZeroizeOnDrop {
	fn as_str() -> &'static str {
		"ZeroizeOnDrop"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::ZeroizeOnDrop(Self {
			crate_: None,
			no_drop: false,
		})
	}

	fn parse_derive_trait(
		_: &[Attribute],
		_: Span,
		list: Option<Punctuated<Meta, Token![,]>>,
	) -> Result<DeriveTrait> {
		let list = if let Some(list) = list {
			list
		} else {
			return Ok(Self::default_derive_trait());
		};

		let mut crate_ = None;
		#[cfg_attr(not(feature = "zeroize-on-drop"), allow(unused_mut))]
		let mut no_drop = false;

		for meta in list {
			match &meta {
				Meta::Path(path) => {
					if path.is_ident("no_drop") {
						// Check for duplicate `no_drop` option.
						#[cfg(feature = "zeroize-on-drop")]
						if !no_drop {
							no_drop = true;
							continue;
						} else {
							return Err(Error::option_duplicate(path.span(), "no_drop"));
						}

						#[cfg(not(feature = "zeroize-on-drop"))]
						return Err(Error::zeroize_on_drop_feature(path.span()));
					}

					return Err(Error::option_trait(path.span(), Self::as_str()));
				}
				Meta::NameValue(name_value) => {
					if name_value.path.is_ident("crate") {
						// Check for duplicate `crate` option.
						if crate_.is_none() {
							let path = match &name_value.value {
								Expr::Lit(ExprLit {
									lit: Lit::Str(lit_str),
									..
								}) => match lit_str.parse::<Path>() {
									Ok(path) => path,
									Err(error) => return Err(Error::path(lit_str.span(), error)),
								},
								Expr::Path(ExprPath { path, .. }) => path.clone(),
								_ => return Err(Error::option_syntax(name_value.value.span())),
							};

							if path == util::path_from_strs(&["zeroize"]) {
								return Err(Error::path_unnecessary(path.span(), "::zeroize"));
							}

							crate_ = Some(path);
						} else {
							return Err(Error::option_duplicate(name_value.span(), "crate"));
						}
					} else {
						return Err(Error::option_trait(name_value.path.span(), Self::as_str()));
					}
				}
				_ => {
					return Err(Error::option_syntax(meta.span()));
				}
			}
		}

		Ok(DeriveTrait::ZeroizeOnDrop(Self { crate_, no_drop }))
	}

	fn path(&self) -> syn::Path {
		util::path_from_root_and_strs(self.crate_(), &["ZeroizeOnDrop"])
	}

	fn additional_impl(&self) -> Option<(Path, TokenStream)> {
		#[cfg(feature = "zeroize-on-drop")]
		return Some((self.path(), quote! {}));
		#[cfg(not(feature = "zeroize-on-drop"))]
		None
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
		let path = if self.no_drop {
			Path {
				leading_colon: None,
				segments: Punctuated::from_iter(iter::once(util::path_segment(
					"DeriveWhereAssertZeroizeOnDrop",
				))),
			}
		} else {
			util::path_from_strs(&["core", "ops", "Drop"])
		};

		let imp = quote! {
			impl #imp #path for #ident #ty
			#where_clause
			{
				#body
			}
		};

		if self.no_drop {
			quote! {
				const _: () = {
					trait DeriveWhereAssertZeroizeOnDrop {
						fn assert(&mut self);
					}

					#imp
				};
			}
		} else {
			quote! {
				#[automatically_derived]
				#imp
			}
		}
	}

	fn build_signature(
		&self,
		_derive_where: &DeriveWhere,
		item: &Item,
		_generics: &SplitGenerics<'_>,
		body: &TokenStream,
	) -> TokenStream {
		match item {
			Item::Item(data) if data.is_empty(**self) => quote! {
				fn drop(&mut self) { }
			},
			#[cfg(feature = "zeroize-on-drop")]
			_ => {
				if self.no_drop {
					let zeroize_on_drop = self.path();

					quote! {
						fn assert(&mut self) {
							trait AssertZeroizeOnDrop {
								fn __derive_where_zeroize_on_drop(&mut self);
							}

							impl<T: #zeroize_on_drop + ?::core::marker::Sized> AssertZeroizeOnDrop for T {
								fn __derive_where_zeroize_on_drop(&mut self) {}
							}

							match self {
								#body
							}
						}
					}
				} else {
					let zeroize = util::path_from_root_and_strs(self.crate_(), &["Zeroize"]);
					let zeroize_on_drop = self.path();

					quote! {
						fn drop(&mut self) {
							trait AssertZeroizeOnDrop {
								fn __derive_where_zeroize_or_on_drop(self);
							}

							impl<T: #zeroize_on_drop + ?::core::marker::Sized> AssertZeroizeOnDrop for &&mut T {
								fn __derive_where_zeroize_or_on_drop(self) {}
							}

							trait AssertZeroize {
								fn __derive_where_zeroize_or_on_drop(&mut self);
							}

							impl<T: #zeroize + ?::core::marker::Sized> AssertZeroize for T {
								fn __derive_where_zeroize_or_on_drop(&mut self) {
									#zeroize::zeroize(self);
								}
							}

							match self {
								#body
							}
						}
					}
				}
			}
			#[cfg(not(feature = "zeroize-on-drop"))]
			_ => {
				// Use unused variables.
				let _ = body;

				let path = util::path_from_root_and_strs(self.crate_(), &["Zeroize"]);

				quote! {
					fn drop(&mut self) {
						#path::zeroize(self);
					}
				}
			}
		}
	}

	#[cfg(feature = "zeroize-on-drop")]
	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		match data.simple_type() {
			#[cfg(feature = "zeroize-on-drop")]
			SimpleType::Struct(fields) | SimpleType::Tuple(fields) => {
				let self_pattern = fields.self_pattern_mut();
				let self_ident = data.iter_self_ident(**self);

				if self.no_drop {
					quote! {
						#self_pattern => {
							#(#self_ident.__derive_where_zeroize_on_drop();)*
						}
					}
				} else {
					quote! {
						#self_pattern => {
							#(#self_ident.__derive_where_zeroize_or_on_drop();)*
						}
					}
				}
			}
			#[cfg(not(feature = "zeroize-on-drop"))]
			SimpleType::Struct(fields) | SimpleType::Tuple(fields) => {
				// Use unused variables.
				let _ = fields;

				let path = util::path_from_root_and_strs(trait_.crate_(), &["Zeroize"]);

				quote! {
					#path::zeroize(self);
				}
			}
			SimpleType::Unit(_) => TokenStream::new(),
			SimpleType::Union => unreachable!("unexpected trait for union"),
		}
	}
}

impl ZeroizeOnDrop {
	/// Returns the path to the root crate for this trait.
	fn crate_(&self) -> Path {
		if let Some(crate_) = &self.crate_ {
			crate_.clone()
		} else {
			util::path_from_strs(&["zeroize"])
		}
	}
}

impl Deref for ZeroizeOnDrop {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::ZeroizeOnDrop
	}
}
