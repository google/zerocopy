// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Help, version, and malformed-argument handling, and the bundled skill
//! and example.

use super::*;

#[test]
fn help_and_version_work_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &[][..],
            &["help"],
            &["-h"],
            &["--help"],
            #[cfg(feature = "setup")]
            &["setup", "-h"],
            #[cfg(feature = "setup")]
            &["setup", "--help"],
            #[cfg(feature = "setup")]
            &["help", "setup"],
            &["verify", "-h"],
            &["verify", "--help"],
            &["help", "verify"],
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, "Usage:", "");
            assert!(output.stderr.is_empty(), "{output:?}");
        }
        for arg in ["-V", "--version"] {
            let output = command(route, project.path())
                .arg(arg)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(
                &output,
                0,
                &format!("cargo-anneal {}", cargo_anneal::cli::PKG_VERSION),
                "",
            );
            assert!(output.stderr.is_empty(), "{output:?}");
        }
    }
}

#[test]
fn bundled_skill_is_discoverable_and_matches_the_source_file() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for (args, hint) in [
            (&["--help"][..], "Print the bundled agent skill"),
            (&["verify", "--help"][..], "cargo anneal skill"),
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, hint, "");
            assert!(output.stderr.is_empty(), "{output:?}");
        }

        let output = command(route, project.path())
            .arg("skill")
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 0, "", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        assert_eq!(
            output.stdout,
            include_bytes!("../../../../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md")
        );

        // Companion skills print byte-for-byte from their packaged copies,
        // which `ci/check_skills.py` keeps identical to `anneal/skills/`.
        const SPEC_AUTHORING: &[u8] = include_bytes!(
            "../../../../trusted/cargo-anneal/assets/skills/spec-authoring/SKILL.md"
        );
        const PROOF_SCALING: &[u8] =
            include_bytes!("../../../../trusted/cargo-anneal/assets/skills/proof-scaling/SKILL.md");
        for (topic, canonical) in [
            (
                "cargo-anneal",
                &include_bytes!("../../../../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md")[..],
            ),
            ("spec-authoring", SPEC_AUTHORING),
            ("proof-scaling", PROOF_SCALING),
        ] {
            let output = command(route, project.path())
                .args(["skill", topic])
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            assert_eq!(output.stdout, canonical, "skill {topic}");
        }
        let output = command(route, project.path())
            .args(["skill", "list"])
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        for topic in ["cargo-anneal", "spec-authoring", "proof-scaling"] {
            assert_result(&output, 0, topic, "");
        }
        let output = command(route, project.path())
            .args(["skill", "no-such-topic"])
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 2, "", "no-such-topic");
    }
}

#[test]
fn bundled_example_matches_the_verified_fixture() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        let output = command(route, project.path())
            .args(["skill", "--example"])
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 0, "cargo anneal verify --request request.json", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).expect("UTF-8 example");
        let sections: Vec<_> = stdout.trim_end().split("\n\n## ").skip(1).collect();
        assert_eq!(
            sections,
            [
                concat!(
                    "`lib.rs`\n\n```rust\n",
                    include_str!("../../../../trusted/cargo-anneal/assets/scalar/lib.rs"),
                    "```",
                ),
                concat!(
                    "`request.json`\n\n```json\n",
                    include_str!("../../../../trusted/cargo-anneal/assets/scalar/request.json"),
                    "```",
                ),
                concat!(
                    "`Spec.lean`\n\n```lean\n",
                    include_str!("../../../../trusted/cargo-anneal/assets/scalar/Spec.lean"),
                    "```",
                ),
                concat!(
                    "`Proof.lean`\n\n```lean\n",
                    include_str!("../../../../trusted/cargo-anneal/assets/scalar/Proof.lean"),
                    "```",
                ),
            ],
        );
    }
}

#[test]
fn malformed_arguments_fail_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &["unknown"][..],
            &["--unknown"],
            #[cfg(not(feature = "setup"))]
            &["setup"],
            #[cfg(feature = "setup")]
            &["setup", "--unknown"],
            #[cfg(feature = "setup")]
            &["setup", "--local-archive"],
            &["verify"],
            &["verify", "--request"],
            &["verify", "--request", "request.json", "--unknown"],
            &["verify", "--request", "request.json", "--manifest-path", "Cargo.toml"],
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 2, "", "error:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
    }
}
