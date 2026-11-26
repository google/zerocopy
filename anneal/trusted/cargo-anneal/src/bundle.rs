// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the canonical source inventory and deterministic rendering of
//! audited resources and bundled `theory/` libraries embedded into
//! `cargo-anneal`.

pub use crate::{
    core::inspect::schema::DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON,
    theory_bundle::{
        BundledTheory, BundledTheoryModule, LEGACY_THEORY_BUNDLE_DESTINATION,
        PACKAGED_THEORY_BUNDLE_CRATE_REL, PACKAGED_THEORY_BUNDLE_DESTINATION,
        THEORY_BUNDLE_MANIFEST, TheoryBundleEntry, TheoryBundleManifest,
        load_theory_bundle_manifest, parse_bundled_theory, prepare_packaged_theory_destination,
        render_bundled_theory,
    },
    trusted_bundle::{
        BUNDLE_HEADER, BundleError, CORRESPONDENCE_ADAPTER_DIR, CORRESPONDENCE_ADAPTER_PATHS,
        CORRESPONDENCE_PROOF_DIR, CORRESPONDENCE_PROOF_PATHS, CORRESPONDENCE_PROVENANCE_NOTE,
        LEGACY_BUNDLE_DESTINATION, MINIRUST_UPSTREAM_PIN_PATH, PACKAGED_BUNDLE_CRATE_REL,
        PACKAGED_BUNDLE_DESTINATION, PROVENANCE_SOURCES, RenderedBundleParts,
        TRUSTED_BUNDLE_SOURCES, UPSTREAM_PIN_PATH, prepare_packaged_bundle_destination,
        render_bundled_resources, render_bundled_resources_parts, render_correspondence_provenance,
        render_correspondence_provenance_from_checkout, validate_bundle_source,
        validate_destination_path, validate_parent_directories,
    },
};

// Generated deterministically by `build.rs` into `$OUT_DIR` from canonical
// workspace sources (or from `packaged/bundled_theory.json` in standalone
// `.crate` builds), keeping edits to `theory/` free of checked-in monolith
// conflicts while binding the compiled binary to audited bytes.
pub(crate) const EMBEDDED_THEORY_BUNDLE_JSON: &str =
    include_str!(concat!(env!("OUT_DIR"), "/bundled_theory.json"));

/// Return the parsed, self-verified [`BundledTheory`] generated into
/// `$OUT_DIR/bundled_theory.json` by `build.rs`.
pub fn embedded_theory_bundle() -> Result<BundledTheory, BundleError> {
    parse_bundled_theory(EMBEDDED_THEORY_BUNDLE_JSON)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory_bundle::REQUIRED_THEORY_BUNDLE_PATH;

    #[test]
    fn provenance_sources_match_component_lists() {
        let expected: Vec<&str> = [UPSTREAM_PIN_PATH, MINIRUST_UPSTREAM_PIN_PATH]
            .into_iter()
            .chain(CORRESPONDENCE_ADAPTER_PATHS.iter().copied())
            .chain(CORRESPONDENCE_PROOF_PATHS.iter().copied())
            .collect();
        assert_eq!(PROVENANCE_SOURCES, expected.as_slice());
    }

    #[test]
    fn embedded_theory_bundle_is_self_consistent() {
        let bundled = embedded_theory_bundle().expect("embedded theory bundle must verify");
        assert_eq!(bundled.schema_version, 1);
        assert!(bundled.modules.iter().any(|m| m.path == REQUIRED_THEORY_BUNDLE_PATH));
    }

    #[test]
    fn parse_bundled_theory_rejects_tampered_and_invalid_payloads() {
        let valid = embedded_theory_bundle().unwrap();
        let mut tampered = valid.clone();
        tampered.modules[0].content.push_str("\n-- tampered\n");
        let err = parse_bundled_theory(&serde_json::to_string(&tampered).unwrap()).unwrap_err();
        assert!(err.to_string().contains("SHA-256 mismatch"), "{err}");

        let mut dup = valid.clone();
        let first = dup.modules[0].clone();
        dup.modules.push(first);
        let err = parse_bundled_theory(&serde_json::to_string(&dup).unwrap()).unwrap_err();
        assert!(err.to_string().contains("duplicate theory bundle path"), "{err}");

        let mut unsorted = valid.clone();
        unsorted.modules.swap(0, 1);
        let err = parse_bundled_theory(&serde_json::to_string(&unsorted).unwrap()).unwrap_err();
        assert!(err.to_string().contains("unsorted theory bundle entry"), "{err}");

        let mut escaped = valid.clone();
        escaped.modules[0].path = "trusted/lean/Trusted.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&escaped).unwrap()).unwrap_err();
        assert!(err.to_string().contains("must reside under theory/Anneal/"), "{err}");

        let mut traversal = valid.clone();
        traversal.modules[0].path = "theory/Anneal/../Trusted.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&traversal).unwrap()).unwrap_err();
        assert!(err.to_string().contains("invalid relative theory bundle path"), "{err}");

        let mut umbrella = valid.clone();
        umbrella.modules[0].path = "theory/Anneal.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&umbrella).unwrap()).unwrap_err();
        assert!(err.to_string().contains("must name a module under theory/Anneal/"), "{err}");

        let mut missing_required = valid;
        missing_required.modules.retain(|m| m.path != REQUIRED_THEORY_BUNDLE_PATH);
        let err = parse_bundled_theory(&serde_json::to_string(&missing_required).unwrap())
            .unwrap_err();
        assert!(err.to_string().contains("missing required theory module"), "{err}");
    }

    #[test]
    fn theory_bundle_identifier_helpers_match_core() {
        for ident in [
            "",
            "A",
            "MirWp",
            "Step_Wp2",
            "_leading_underscore",
            "2leading_digit",
            "with-hyphen",
            "with.dot",
            "with space",
            "αβγ",
        ] {
            assert_eq!(
                crate::theory_bundle::is_lean_ident(ident),
                crate::core::is_lean_ident(ident),
                "is_lean_ident mismatch on {ident:?}"
            );
        }
        for path in [
            "",
            "a",
            "theory/Anneal/MirWp.lean",
            "/abs/path",
            "./dot",
            "a/./b",
            "a/../b",
            "..",
            ".",
            "a//b",
            "a/b/",
        ] {
            assert_eq!(
                crate::theory_bundle::is_clean_relative_path(path),
                crate::core::is_clean_relative_path(path),
                "is_clean_relative_path mismatch on {path:?}"
            );
        }
    }
}
