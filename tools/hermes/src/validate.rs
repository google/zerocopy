use anyhow::{bail, Result};

use crate::{
    parse::{attr::FunctionBlockInner, ParsedItem},
    scanner::HermesArtifact,
};

/// Validates the collected Hermes artifacts.
///
/// Checks:
/// 1. All `spec` functions (functions with a `/// ````hermes` block but not `unsafe(axiom)`)
///    must have a non-empty `proof` section.
///
/// If `allow_sorry` is true, this check is skipped, allowing incomplete proofs
/// (which will typically be generated as `sorry` in Lean).
pub fn validate_artifacts(packages: &[HermesArtifact], allow_sorry: bool) -> Result<()> {
    if allow_sorry {
        return Ok(());
    }

    let mut has_errors = false;

    for package in packages {
        for item in &package.items {
            if let ParsedItem::Function(func) = &item.item {
                if let FunctionBlockInner::Proof { lines, .. } = &func.hermes.inner {
                    if lines.is_empty() {
                        // We need a way to report this error with miette. For
                        // now, we'll eprintln and set has_errors.
                        eprintln!(
                             "Error: Function `{}` has a missing `proof` section.\n  --> {}\n  Help: Use `--allow-sorry` to generate a placeholder `sorry`.",
                             func.item.name(),
                             item.source_file.display(),
                         );
                        has_errors = true;
                    }
                }
            }
        }
    }

    if has_errors {
        bail!("Validation failed: Missing proofs detected.");
    }

    Ok(())
}
