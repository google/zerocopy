// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use syn::{FnArg, Generics, Type, TypeParamBound};

/// Utilities for translating Rust function signatures into Lean compatible forms.
///
/// This includes handling generics, detecting statefulness (mutable references),
/// and determining necessary type classes (like `[Verifiable T]`).
pub struct SignatureTranslator;

impl SignatureTranslator {
    /// Generates Lean generic parameters and type class constraints from Rust generics.
    ///
    /// # Arugments
    /// * `generics` - The Rust generics AST.
    ///
    /// # Returns
    /// An iterator/string of space-separated Lean parameters.
    /// e.g. `{T : Type} [Verifiable T]`
    pub fn translate_generics(generics: &Generics) -> String {
        let mut out = String::new();
        for param in &generics.params {
            match param {
                syn::GenericParam::Type(t) => {
                    // `{T}` implicitly assumes simple Type unless `Type u` etc.
                    out.push_str(&format!("{{{}}} [Verifiable {}] ", t.ident, t.ident));

                    // Iterate bounds to find other traits (e.g. Display, Clone, etc.)
                    // and lift them as instance arguments.
                    for bound in &t.bounds {
                        if let TypeParamBound::Trait(trait_bound) = bound {
                            if let Some(segment) = trait_bound.path.segments.last() {
                                let trait_name = &segment.ident;
                                // Naming: instTDisplay
                                let param_name = &t.ident;
                                out.push_str(&format!(
                                    "[inst{}{}: {} {}] ",
                                    param_name, trait_name, trait_name, param_name
                                ));
                            }
                        }
                    }
                }
                syn::GenericParam::Const(c) => {
                    // `{C : Int}` etc. Simplistic mapping for now.
                    out.push_str(&format!("{{{}: Int}} ", c.ident));
                }
                syn::GenericParam::Lifetime(_) => {
                    // Lifetimes are erased in the pure Lean translation usually.
                }
            }
        }
        out
    }

    /// Detects if a function is stateful based on its arguments.
    ///
    /// A function is considered stateful if it takes any mutable reference arguments (`&mut T`).
    /// This affects how the spec is desugared (handling back-translation of state).
    pub fn detect_statefulness(args: &[FnArg]) -> bool {
        for arg in args {
            if let FnArg::Typed(pat_type) = arg {
                if let Type::Reference(r) = &*pat_type.ty {
                    if r.mutability.is_some() {
                        return true;
                    }
                }
            }
        }
        false
    }
}
