//! Parsing implementation for `#[derive_where(crate = ...)]`.

use proc_macro2::Span;
use syn::{spanned::Spanned, Expr, ExprLit, ExprPath, Lit, Meta, Path, Result};

use crate::{util, Error, DERIVE_WHERE};

/// Parses `#[derive_where(crate = ...)]`.
pub fn parse_crate(meta: Meta) -> Result<(Path, Span)> {
	if let Meta::NameValue(name_value) = meta {
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

		if path == util::path_from_strs(&[DERIVE_WHERE]) {
			Err(Error::path_unnecessary(
				path.span(),
				&format!("::{}", DERIVE_WHERE),
			))
		} else {
			Ok((path, name_value.span()))
		}
	} else {
		Err(Error::option_syntax(meta.span()))
	}
}
