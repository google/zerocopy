// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Seam 4: the closed positive `#![feature(...)]` allowlist, accepted
//! features, and operator-allowed unstable features.

use super::*;

/// Seam 4: Closed positive `#![feature(...)]` allowlist (empty `[]` for normal
/// crates) rejects unstable lang and lib features, admits and records
/// `ACCEPTED_LANG_FEATURES` (`doc_alias`), and preserves `zerocopy`-style
/// inactive `#![cfg_attr(..., feature(...))]` lines until activated.
#[test]
fn seam_4_positive_feature_allowlist_and_accepted_features() {
    // Disallowed unstable lang features (including `f16`), unstable lib
    // features (`core_intrinsics`, `ptr_metadata`, `const_eval_select`), and
    // `doc_cfg`.
    let rejected_features: &[(&str, &str)] = &[
        (
            "rustc_attrs",
            "#![feature(rustc_attrs)]\n\
             #[rustc_inherit_overflow_checks]\n\
             pub fn selected(x: u64) -> u64 { x }\n",
        ),
        ("custom_mir", "#![feature(custom_mir)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("specialization", "#![feature(specialization)]\npub fn selected(x: u64) -> u64 { x }\n"),
        (
            "generic_const_exprs",
            "#![feature(generic_const_exprs)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
        (
            "adt_const_params",
            "#![feature(adt_const_params)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
        ("intrinsics", "#![feature(intrinsics)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("f16", "#![feature(f16)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("doc_cfg", "#![feature(doc_cfg)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("rustc_private", "#![feature(rustc_private)]\npub fn selected(x: u64) -> u64 { x }\n"),
        // Unstable library features (missed by lang-only checks).
        ("core_intrinsics", "#![feature(core_intrinsics)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("ptr_metadata", "#![feature(ptr_metadata)]\npub fn selected(x: u64) -> u64 { x }\n"),
        (
            "const_eval_select",
            "#![feature(const_eval_select)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
    ];

    for (feature, src) in rejected_features {
        let fixture = Capture::new(src.as_bytes());
        let out = fixture.selected_command().output().expect("capture disallowed feature");
        assert_refused(feature, &fixture, &out, "unsupported", feature);
    }

    // Non-word `#![feature(...)]` entries fail closed uniformly before
    // expansion.
    let non_word = Capture::new(
        b"#![feature(no_core = \"x\")]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let non_word_out = non_word.selected_command().output().expect("capture non-word feature");
    assert_refused(
        "non-word feature attr",
        &non_word,
        &non_word_out,
        "unsupported",
        "must list feature identifiers",
    );

    // Already-stabilized `ACCEPTED_LANG_FEATURES` (which `-Zallow-features=`
    // skips) activate nothing unstable: capture admits them untainted and
    // records them, directly or through an active `cfg_attr`.
    for src in [
        "#![feature(doc_alias)]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![cfg_attr(all(), feature(doc_alias))]\npub fn selected(x: u64) -> u64 { x }\n",
    ] {
        let fixture = Capture::new(src.as_bytes());
        let out = fixture.selected_command().output().expect("capture accepted feature");
        assert!(out.status.success(), "{src}: {out:?}");
        let configuration = &fixture.manifest()["configuration"];
        assert_eq!(configuration["stabilized_features_present"], json!(["doc_alias"]), "{src}");
        for key in [
            "allowed_unstable_features",
            "observed_unstable_features",
            "incomplete_observed_unstable_features",
        ] {
            assert!(configuration.get(key).is_none(), "{src}: unexpected {key}");
        }
    }

    // Positive control mirroring `zerocopy/src/lib.rs:318-325`: inactive
    // `#![cfg_attr(..., feature(...))]` declarations stay admitted under
    // default cfgs, and fail closed as soon as a `--cfg` activates any of them.
    let zerocopy_style = Capture::new(
        b"#![cfg_attr(doc_cfg, feature(doc_cfg))]\n\
          #![cfg_attr(feature = \"float-nightly\", feature(f16, f128))]\n\
          #![cfg_attr(coverage_nightly, feature(coverage_attribute))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let default_out = zerocopy_style
        .selected_command()
        .output()
        .expect("capture inactive zerocopy-style cfg_attr");
    assert!(default_out.status.success(), "{default_out:?}");

    let activated_doc_cfg = Capture::new(
        b"#![cfg_attr(doc_cfg, feature(doc_cfg))]\n\
          #![cfg_attr(feature = \"float-nightly\", feature(f16, f128))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let doc_cfg_out = activated_doc_cfg
        .selected_command()
        .arg("--cfg=doc_cfg")
        .output()
        .expect("capture activated doc_cfg");
    assert_refused("activated doc_cfg", &activated_doc_cfg, &doc_cfg_out, "unsupported", "doc_cfg");

    let activated_float = Capture::new(
        b"#![cfg_attr(doc_cfg, feature(doc_cfg))]\n\
          #![cfg_attr(feature = \"float-nightly\", feature(f16, f128))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let float_out = activated_float
        .selected_command()
        .arg("--cfg=feature=\"float-nightly\"")
        .output()
        .expect("capture activated float-nightly");
    assert_refused(
        "activated float-nightly",
        &activated_float,
        &float_out,
        "unsupported",
        "f128, f16",
    );
}

/// Seam 4b: `--allow-unstable-feature` admits exactly the named unstable
/// features (recording what the operator allowed, what the crate enabled, and
/// which enabled features `rustc` marks incomplete), never the hard-ban floor,
/// and keeps `-Zallow-features` enforcing the allowlist under active
/// `cfg_attr`.
#[test]
fn seam_4b_operator_allowed_unstable_features() {
    let selected = "pub fn selected(x: u64) -> u64 { x }\n";

    // Allowed and enabled: recorded as allowed and observed.
    let doc_cfg = Capture::new(format!("#![feature(doc_cfg)]\n{selected}").as_bytes());
    let out = doc_cfg
        .selected_command()
        .arg("--allow-unstable-feature=doc_cfg")
        .output()
        .expect("capture allowed doc_cfg");
    assert!(out.status.success(), "{out:?}");
    let configuration = &doc_cfg.manifest()["configuration"];
    assert_eq!(configuration["allowed_unstable_features"], json!(["doc_cfg"]));
    assert_eq!(configuration["observed_unstable_features"], json!(["doc_cfg"]));
    assert!(configuration.get("incomplete_observed_unstable_features").is_none());
    assert!(configuration.get("stabilized_features_present").is_none());

    // Allowed but unused: recorded as allowed only. Repeated and
    // comma-separated flags normalize to one sorted list.
    let unused = Capture::new(selected.as_bytes());
    let out = unused
        .selected_command()
        .arg("--allow-unstable-feature=doc_cfg,allocator_api")
        .arg("--allow-unstable-feature")
        .arg("doc_cfg")
        .output()
        .expect("capture unused allowlist");
    assert!(out.status.success(), "{out:?}");
    let configuration = &unused.manifest()["configuration"];
    assert_eq!(configuration["allowed_unstable_features"], json!(["allocator_api", "doc_cfg"]));
    assert!(configuration.get("observed_unstable_features").is_none());

    // Incomplete features stay admissible but are flagged.
    let incomplete = Capture::new(format!("#![feature(specialization)]\n{selected}").as_bytes());
    let out = incomplete
        .selected_command()
        .arg("--allow-unstable-feature=specialization")
        .output()
        .expect("capture allowed specialization");
    assert!(out.status.success(), "{out:?}");
    let configuration = &incomplete.manifest()["configuration"];
    assert_eq!(configuration["observed_unstable_features"], json!(["specialization"]));
    assert_eq!(configuration["incomplete_observed_unstable_features"], json!(["specialization"]));

    // Naming an already-stabilized feature is harmless: it is allowed but
    // never observed, and the attribute is recorded as stabilized.
    let stabilized = Capture::new(format!("#![feature(doc_alias)]\n{selected}").as_bytes());
    let out = stabilized
        .selected_command()
        .arg("--allow-unstable-feature=doc_alias")
        .output()
        .expect("capture allowed stabilized feature");
    assert!(out.status.success(), "{out:?}");
    let configuration = &stabilized.manifest()["configuration"];
    assert_eq!(configuration["allowed_unstable_features"], json!(["doc_alias"]));
    assert!(configuration.get("observed_unstable_features").is_none());
    assert_eq!(configuration["stabilized_features_present"], json!(["doc_alias"]));

    // Features outside the operator's list still fail closed, including under
    // an active `cfg_attr` and for library features.
    for (label, src) in [
        ("cfg_attr allocator_api", "#![cfg_attr(all(), feature(allocator_api))]\n"),
        ("lib ptr_metadata", "#![feature(doc_cfg, ptr_metadata)]\n"),
    ] {
        let fixture = Capture::new(format!("{src}{selected}").as_bytes());
        let out = fixture
            .selected_command()
            .arg("--allow-unstable-feature=doc_cfg")
            .output()
            .expect("capture feature outside allowlist");
        let needle = if label.starts_with("lib") { "ptr_metadata" } else { "allocator_api" };
        assert_refused(label, &fixture, &out, "unsupported", needle);
    }

    // The hard-ban floor cannot be allowed, whether or not the crate enables
    // the feature.
    for banned in
        ["rustc_attrs", "rustc_private", "ergonomic_clones", "custom_mir", "core_intrinsics"]
    {
        for src in [selected.to_owned(), format!("#![feature({banned})]\n{selected}")] {
            let fixture = Capture::new(src.as_bytes());
            let out = fixture
                .selected_command()
                .arg(format!("--allow-unstable-feature=doc_cfg,{banned}"))
                .output()
                .expect("capture hard-banned feature");
            assert_refused(banned, &fixture, &out, "unsupported", "cannot be allowed");
        }
    }

    // Malformed names and `--stdlib-crate` conflicts are usage errors.
    for args in [
        vec!["--allow-unstable-feature=*"],
        vec!["--allow-unstable-feature=Doc_cfg"],
        vec!["--allow-unstable-feature=doc_cfg,"],
        vec!["--allow-unstable-feature=doc-cfg"],
        vec!["--allow-unstable-feature=doc_cfg", "--stdlib-crate=core"],
    ] {
        let fixture = Capture::new(selected.as_bytes());
        let out = fixture.selected_command().args(&args).output().expect("capture bad usage");
        assert_eq!(out.status.code(), Some(2), "{args:?}: {out:?}");
        assert_eq!(status(&out)["status"], "tool_failed", "{args:?}");
        fixture.assert_no_capture_artifacts();
    }
}
