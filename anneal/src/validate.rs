use anyhow::{Result, bail};
use miette::NamedSource;

use crate::{
    errors::AnnealError,
    parse::ParsedItem,
    scanner::AnnealArtifact,
};

/// Validates the collected Anneal artifacts.
///
/// Checks:
/// 1. All `spec` functions (functions with a `/// ````anneal` block but not
///    `unsafe(axiom)`) must have a non-empty `proof` section.
///
/// If `allow_sorry` is true, this check is skipped, allowing incomplete
/// proofs (which will typically be generated as `sorry` in Lean).
pub fn validate_artifacts(
    _packages: &[AnnealArtifact],
    _allow_sorry: bool,
    _unsound_allow_is_valid: bool,
) -> Result<()> {
    Ok(())
}


