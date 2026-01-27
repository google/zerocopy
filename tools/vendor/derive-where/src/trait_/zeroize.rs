//! [`Zeroize`](https://docs.rs/zeroize/latest/zeroize/trait.Zeroize.html) implementation.

use std::ops::Deref;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
	punctuated::Punctuated, spanned::Spanned, Attribute, Expr, ExprLit, ExprPath, Lit, Meta, Path,
	Result, Token,
};

use crate::{
	util, Data, DeriveTrait, DeriveWhere, Error, Item, SimpleType, SplitGenerics, Trait, TraitImpl,
};

/// [`TraitImpl`] for [`Zeroize`](https://docs.rs/zeroize/latest/zeroize/trait.Zeroize.html).
#[derive(Eq, PartialEq)]
pub struct Zeroize {
	/// [`Zeroize`](https://docs.rs/zeroize/latest/zeroize/trait.Zeroize.html) path.
	pub crate_: Option<Path>,
}

impl TraitImpl for Zeroize {
	fn as_str() -> &'static str {
		"Zeroize"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Zeroize(Self { crate_: None })
	}

	fn parse_derive_trait(
		_: &[Attribute],
		_span: Span,
		list: Option<Punctuated<Meta, Token![,]>>,
	) -> Result<DeriveTrait> {
		let list = if let Some(list) = list {
			list
		} else {
			return Ok(Self::default_derive_trait());
		};

		let mut crate_ = None;

		for meta in list {
			match &meta {
				Meta::Path(path) => {
					if path.is_ident("drop") {
						return Err(Error::deprecated_zeroize_drop(path.span()));
					} else {
						return Err(Error::option_trait(path.span(), Self::as_str()));
					}
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

		Ok(DeriveTrait::Zeroize(Self { crate_ }))
	}

	fn path(&self) -> syn::Path {
		util::path_from_root_and_strs(self.crate_(), &["Zeroize"])
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
				fn zeroize(&mut self) { }
			},
			_ => {
				let trait_path = self.path();
				quote! {
					fn zeroize(&mut self) {
						use #trait_path;

						match self {
							#body
						}
					}
				}
			}
		}
	}

	fn build_body(&self, _derive_where: &DeriveWhere, data: &Data) -> TokenStream {
		match data.simple_type() {
			SimpleType::Struct(fields) | SimpleType::Tuple(fields) => {
				let trait_path = self.path();
				let self_pattern = fields.self_pattern_mut();

				let body = data
					.iter_fields(**self)
					.zip(data.iter_self_ident(**self))
					.map(|(field, self_ident)| {
						if field.attr.zeroize_fqs.0 {
							quote! { #trait_path::zeroize(#self_ident); }
						} else {
							quote! { #self_ident.zeroize(); }
						}
					});

				quote! {
					#self_pattern => {
						#(#body)*
					}
				}
			}
			SimpleType::Unit(_) => TokenStream::new(),
			SimpleType::Union => unreachable!("unexpected trait for union"),
		}
	}
}

impl Zeroize {
	/// Returns the path to the root crate for this trait.
	fn crate_(&self) -> Path {
		if let Some(crate_) = &self.crate_ {
			crate_.clone()
		} else {
			util::path_from_strs(&["zeroize"])
		}
	}
}

impl Deref for Zeroize {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Zeroize
	}
}
