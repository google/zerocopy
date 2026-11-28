// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `anneal-lower-cpp`: lowers a `RawCppBundle` (schema v1, emitted by
//! `anneal-clang-dump`) to a `CapturedCpp.lean` file defining a
//! `Trusted.CppAst.CppProgram`.
//!
//! The pipeline parses the bundle, applies the language-policy gate, runs
//! the per-function SSENF gate and CFG lowering, and renders deterministic
//! Lean. Every stage fails closed
//! with a [`LowerError`]; there is no best-effort output.

pub mod error;
pub mod ir;
pub mod lower;
pub mod raw;
pub mod ssenf;

pub use error::LowerError;
pub use lower::Options;

/// Options for rendering the Lean file.
#[derive(Debug, Clone)]
pub struct EmitOptions {
    pub lower: Options,
    /// Lean namespace for the generated definitions.
    pub namespace: String,
}

impl Default for EmitOptions {
    fn default() -> Self {
        EmitOptions { lower: Options::default(), namespace: "CapturedCpp".to_owned() }
    }
}

/// Parses and lowers a bundle, returning the `Trusted.CppAst` program.
pub fn lower_bundle_json(text: &str, opts: &Options) -> Result<ir::Program, LowerError> {
    let bundle = raw::parse_bundle(text)?;
    lower::lower_bundle(&bundle, opts)
}

/// Parses, lowers, and renders a bundle as the contents of
/// `CapturedCpp.lean`.
pub fn lower_bundle_json_to_lean(text: &str, opts: &EmitOptions) -> Result<String, LowerError> {
    let bundle = raw::parse_bundle(text)?;
    let program = lower::lower_bundle(&bundle, &opts.lower)?;
    if !is_lean_namespace(&opts.namespace) {
        return Err(LowerError::Malformed {
            detail: format!("`{}` is not a valid Lean namespace", opts.namespace),
        });
    }
    Ok(program.lean(&ir::EmitMeta {
        namespace: &opts.namespace,
        tu_main_file: &bundle.tu_main_file,
        target_triple: &bundle.target_triple,
        lang_standard: &bundle.lang_policy.lang_standard,
    }))
}

fn is_lean_namespace(s: &str) -> bool {
    !s.is_empty()
        && s.split('.').all(|part| {
            let mut cs = part.chars();
            matches!(cs.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
                && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}
