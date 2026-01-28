//! [`Copy`](trait@std::marker::Copy) implementation.

use std::ops::Deref;

use crate::{util, DeriveTrait, Trait, TraitImpl};

/// [`TraitImpl`] for [`Copy`](trait@std::marker::Copy).
pub struct Copy;

impl TraitImpl for Copy {
	fn as_str() -> &'static str {
		"Copy"
	}

	fn default_derive_trait() -> DeriveTrait {
		DeriveTrait::Copy
	}

	fn supports_union() -> bool {
		true
	}

	fn path(&self) -> syn::Path {
		util::path_from_strs(&["core", "marker", "Copy"])
	}
}

impl Deref for Copy {
	type Target = Trait;

	fn deref(&self) -> &Self::Target {
		&Trait::Copy
	}
}
