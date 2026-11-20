// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI regressions for operating-system strings that are not valid UTF-8.

#![cfg(unix)]

use std::ffi::OsString;
use std::fs;
use std::os::unix::ffi::OsStringExt;
use std::path::Path;
use std::process::{Command, Output};

fn auditor(root: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-audit"));
    command
        .env_clear()
        .arg("--anneal-root")
        .arg(root)
        .arg("--lean")
        .arg(root.join("missing-lean"));
    command
}

fn stderr(output: &Output) -> String {
    String::from_utf8(output.stderr.clone()).unwrap()
}

#[test]
fn ignores_non_utf8_environment_entries_outside_the_allowlist() {
    let root = tempfile::tempdir().unwrap();
    let baseline = auditor(root.path()).output().unwrap();
    assert_eq!(baseline.status.code(), Some(1));
    assert!(stderr(&baseline).contains("Trusted check failed (snapshot)"));

    for (key, value) in [
        (
            OsString::from_vec(b"ANNEAL_TEST_\xff".to_vec()),
            "value".into(),
        ),
        (
            "ANNEAL_TEST_INVALID_UTF8".into(),
            OsString::from_vec(vec![0xff]),
        ),
    ] {
        let output = auditor(root.path()).env(key, value).output().unwrap();
        assert_eq!(output.status.code(), baseline.status.code());
        assert_eq!(output.stdout, baseline.stdout);
        assert_eq!(output.stderr, baseline.stderr);
    }
}

#[test]
fn reports_non_utf8_values_in_retained_environment_entries() {
    let root = tempfile::tempdir().unwrap();
    for key in ["HOME", "TMPDIR", "LANG", "LC_ALL"] {
        let output = auditor(root.path())
            .env(key, OsString::from_vec(vec![0xff]))
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{key}: {output:?}");
        assert!(
            stderr(&output).contains(&format!("environment variable {key} is not valid UTF-8")),
            "{key}: {output:?}"
        );
    }
}

#[test]
fn handles_non_utf8_path_arguments_before_help_and_version() {
    let root = tempfile::tempdir().unwrap();
    let non_utf8 = root.path().join(OsString::from_vec(vec![0xff]));
    for flag in ["--help", "--version"] {
        let output = auditor(&non_utf8).arg(flag).output().unwrap();
        assert!(output.status.success(), "{flag}: {output:?}");
        assert!(output.stderr.is_empty(), "{flag}: {output:?}");
        assert!(
            String::from_utf8(output.stdout)
                .unwrap()
                .contains("anneal-audit")
        );
    }
}

#[test]
fn preserves_non_utf8_repository_and_lean_path_arguments() {
    let root = tempfile::tempdir().unwrap();
    let non_utf8 = root.path().join(OsString::from_vec(vec![0xff]));
    fs::create_dir(&non_utf8).unwrap();
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for relative in [
        "trusted/lean/Trusted.lean",
        "trusted/lean/lean-toolchain",
        "trusted/lean/foundation-lock.json",
        "trusted/audit/TrustedBoundary.lean",
    ] {
        let target = non_utf8.join(relative);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::copy(checkout.join(relative), target).unwrap();
    }
    let lean = non_utf8.join(OsString::from_vec(vec![0xfe]));
    fs::write(&lean, b"not the pinned Lean binary").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit"))
        .env_clear()
        .arg("--anneal-root")
        .arg(&non_utf8)
        .arg("--lean")
        .arg(&lean)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(
        stderr(&output).contains("Lean binary SHA-256 differs from lock"),
        "{output:?}"
    );
}
