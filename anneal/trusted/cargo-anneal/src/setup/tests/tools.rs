// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests: Bundle layout and tool resolution.

use std::{
    fs,
    path::{Path, PathBuf},
};

use super::*;

#[test]
fn resolve_tools_prefers_explicit_then_installed_then_sibling() {
    let bundle_dir = tempfile::tempdir().expect("create synthetic bundle");
    let installed = Bundle::new(bundle_dir.path().to_path_buf());
    fs::create_dir_all(installed.lean().parent().unwrap()).expect("create lean bin dir");
    fs::write(installed.lean(), b"lean").expect("write synthetic lean binary");

    let explicit = resolve_tools(
        ToolOverrides {
            capture: Some(PathBuf::from("/explicit/capture")),
            sysroot: Some(PathBuf::from("/explicit/sysroot")),
            lean: Some(PathBuf::from("/explicit/lean")),
        },
        Some(&installed),
        cli(),
    )
    .expect("resolve explicit tools");
    assert_eq!(explicit.capture, Path::new("/explicit/capture"));
    assert_eq!(
        explicit.sysroot.as_deref(),
        Some(Path::new("/explicit/sysroot"))
    );
    assert_eq!(explicit.lean.as_deref(), Some(Path::new("/explicit/lean")));

    let from_installed = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
        .expect("resolve installed tools");
    assert_eq!(from_installed.capture, installed.capture());
    assert_eq!(from_installed.sysroot, Some(installed.sysroot()));
    assert_eq!(from_installed.lean, Some(installed.lean()));

    let fallback =
        resolve_tools(ToolOverrides::default(), None, cli()).expect("resolve sibling capture");
    assert_eq!(
        fallback.capture,
        Path::new("/workspace/target/debug/anneal-rustc-capture")
    );
    assert_eq!(fallback.sysroot, None);
    assert_eq!(fallback.lean, None);
}

#[test]
fn resolve_tools_falls_back_when_installed_bundle_lacks_lean() {
    let bundle_dir = tempfile::tempdir().expect("create bundle without lean");
    let installed = Bundle::new(bundle_dir.path().to_path_buf());

    let without_lean = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
        .expect("resolve installed tools");
    assert_eq!(without_lean.capture, installed.capture());
    assert_eq!(without_lean.sysroot, Some(installed.sysroot()));
    assert_eq!(without_lean.lean, None);

    let with_override = resolve_tools(
        ToolOverrides {
            lean: Some(PathBuf::from("/explicit/lean")),
            ..ToolOverrides::default()
        },
        Some(&installed),
        cli(),
    )
    .expect("resolve explicit Lean");
    assert_eq!(
        with_override.lean.as_deref(),
        Some(Path::new("/explicit/lean"))
    );

    fs::create_dir_all(installed.lean().parent().unwrap()).expect("create lean bin dir");
    fs::write(installed.lean(), b"lean").expect("write synthetic lean binary");
    let with_lean = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
        .expect("resolve installed Lean");
    assert_eq!(with_lean.lean, Some(installed.lean()));
}

#[test]
fn sibling_capture_requires_an_absolute_executable_path() {
    let unknown = sibling_capture(unknown_cli())
        .expect_err("an unknown executable must not select a capture driver");
    assert!(
        unknown.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
        "{unknown}"
    );
    assert!(unknown.contains("executable path unavailable"), "{unknown}");

    for relative in [
        "",
        "cargo-anneal",
        "./cargo-anneal",
        "target/debug/cargo-anneal",
    ] {
        let failure = sibling_capture(Ok(PathBuf::from(relative)))
            .expect_err("a relative executable must not select a capture driver");
        assert!(
            failure.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
            "{relative:?}: {failure}"
        );
        assert!(
            failure.contains("is not absolute"),
            "{relative:?}: {failure}"
        );
    }

    assert_eq!(
        sibling_capture(cli()),
        Ok(PathBuf::from(
            "/workspace/target/debug/anneal-rustc-capture"
        ))
    );
}

#[test]
fn resolve_tools_needs_the_executable_path_only_for_the_sibling() {
    let explicit = resolve_tools(
        ToolOverrides {
            capture: Some(PathBuf::from("/explicit/capture")),
            ..ToolOverrides::default()
        },
        None,
        unknown_cli(),
    )
    .expect("an explicit capture driver needs no executable path");
    assert_eq!(explicit.capture, Path::new("/explicit/capture"));

    let bundle_dir = tempfile::tempdir().expect("create synthetic bundle");
    let installed = Bundle::new(bundle_dir.path().to_path_buf());
    let from_installed =
        resolve_tools(ToolOverrides::default(), Some(&installed), unknown_cli())
            .expect("an installed capture driver needs no executable path");
    assert_eq!(from_installed.capture, installed.capture());

    for current_exe in [
        unknown_cli(),
        Ok(PathBuf::new()),
        Ok(PathBuf::from("cargo-anneal")),
    ] {
        let failure = resolve_tools(ToolOverrides::default(), None, current_exe)
            .expect_err("the sibling fallback must fail closed");
        assert!(
            failure.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
            "{failure}"
        );
    }
}

#[test]
fn custom_locations_install_only_the_requested_archive() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("current-run.tar.zst");
    write_archive(&archive);
    let ordinary = temp.path().join("ordinary-cache");
    let root = install_at(Some(archive), exocrate::Location::Custom(ordinary.clone()))
        .expect("install requested local archive");
    assert!(root.starts_with(&ordinary), "{}", root.display());
    assert_eq!(
        fs::read(root.join("marker.txt")).expect("read installed marker"),
        b"archive under test"
    );

    for (name, contents) in [("missing", None), ("broken", Some(b"bad"))] {
        let archive = temp.path().join(format!("{name}.tar.zst"));
        if let Some(contents) = contents {
            fs::write(&archive, contents).expect("write broken archive");
        }
        let fresh = temp.path().join(format!("{name}-cache"));
        let error = install_at(Some(archive), exocrate::Location::Custom(fresh))
            .expect_err("another location's installation must not satisfy setup");
        assert!(error.contains("failed to install Anneal toolchain"));
    }

    assert_eq!(
        fs::read(root.join("marker.txt")).expect("ordinary cache survives"),
        b"archive under test"
    );
}
