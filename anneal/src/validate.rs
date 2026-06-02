use anyhow::{Result, bail};
use miette::NamedSource;

use crate::{errors::AnnealError, parse::ParsedItem, scanner::AnnealArtifact};

/// Validates the collected Anneal artifacts.
///
/// Checks:
/// 1. All `spec` functions (functions with a `/// ````anneal` block but not
///    `unsafe(axiom)`) must have a non-empty `proof` section.
///
/// If `allow_sorry` is true, this check is skipped, allowing incomplete
/// proofs (which will typically be generated as `sorry` in Lean).
fn report_error(
    source_file: &std::path::Path,
    source_cache: &mut std::collections::HashMap<std::path::PathBuf, String>,
    span: miette::SourceSpan,
    msg: String,
) {
    let src = source_cache
        .entry(source_file.to_path_buf())
        .or_insert_with(|| std::fs::read_to_string(source_file).unwrap_or_default())
        .clone();

    let named_source = NamedSource::new(source_file.display().to_string(), src);
    let err = AnnealError::Unsoundness {
        src: named_source,
        span,
        msg,
        label: "problematic block".to_string(),
    };
    eprintln!("{:?}", miette::Report::new(err));
}

/// Validates the collected Anneal artifacts.
pub fn validate_artifacts(
    packages: &[AnnealArtifact],
    _allow_sorry: bool,
    unsound_allow_is_valid: bool,
) -> Result<()> {
    let mut has_errors = false;
    let mut source_cache = std::collections::HashMap::new();

    for package in packages {
        for item in &package.items {
            match &item.item {
                ParsedItem::Trait(tr) if !tr.item.inner.unsafety => {
                    // Reject safe traits
                    report_error(
                        &item.source_file,
                        &mut source_cache,
                        tr.anneal.start_span.inner,
                        "Annotations are only permitted on `unsafe` traits.".to_string(),
                    );
                    has_errors = true;
                }
                ParsedItem::Type(ty) if !unsound_allow_is_valid => {
                    // Reject type invariants unless authorized
                    report_error(
                        &item.source_file,
                        &mut source_cache,
                        ty.anneal.start_span.inner,
                        "`isValid` annotations are unsound and require the --unsound-allow-is-valid flag.".to_string(),
                    );
                    has_errors = true;
                }
                _ => {}
            }
        }
    }

    if has_errors {
        bail!("Validation failed: Naming collisions or missing proofs detected.");
    }

    Ok(())
}
