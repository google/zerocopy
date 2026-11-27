// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared fixtures and Lean correspondence DSL for `anneal-audit-tests`.

#![allow(dead_code)]

pub mod correspondence_dsl;

use std::{
    collections::BTreeMap,
    fs, io,
    path::{Path, PathBuf},
};

use anneal_audit::{Checker, Failure, ImportEdge, Json, ModuleArtifacts};
use anneal_testkit::{LeanAuditFixture, OleanCachePolicy};

pub const HEADER: &str = "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\n";

pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
}

pub fn copy_dir_all(src: &Path, dst: &Path) -> io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(&entry.path(), &dst.join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.join(entry.file_name()))?;
        }
    }
    Ok(())
}

/// Copies the root build files, `trusted/root-manifest.sha256`, and the Cargo
/// workspace member crates that `check_cargo_boundary` inspects from the real
/// checkout into `root`.
pub fn copy_cargo_workspace(root: &Path) {
    let checkout = repo_root();
    for rel in [
        "Cargo.toml",
        "Cargo.lock",
        "flake.nix",
        "flake.lock",
        "trusted/root-manifest.sha256",
        "trusted/audit/Cargo.toml",
        "tests/testkit/Cargo.toml",
        "tests/audit/Cargo.toml",
        "tests/cargo-anneal/Cargo.toml",
        "tests/itree_diff/Cargo.toml",
        "tests/rustc-capture/Cargo.toml",
        "tests/differential/Cargo.toml",
        "tools/anneal-spec/Cargo.toml",
        "tools/anneal-spec/Cargo.lock",
        "tools/anneal-spec/lower/Cargo.toml",
        "tools/anneal-spec/macros/Cargo.toml",
    ] {
        let dest = root.join(rel);
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::copy(checkout.join(rel), dest).unwrap();
    }
    for rel in ["trusted/rustc-capture", "trusted/cargo-anneal"] {
        copy_dir_all(&checkout.join(rel), &root.join(rel)).unwrap();
    }
}

pub struct TempFixture {
    pub inner: LeanAuditFixture,
    pub root: PathBuf,
}

impl TempFixture {
    pub fn new(source: Option<&str>) -> Self {
        Self::with_cache_policy(source, OleanCachePolicy::Shared)
    }

    pub fn isolated(source: Option<&str>) -> Self {
        Self::with_cache_policy(source, OleanCachePolicy::Isolated)
    }

    pub fn with_cache_policy(source: Option<&str>, cache_policy: OleanCachePolicy) -> Self {
        let inner = LeanAuditFixture::with_cache_policy(
            &repo_root(),
            "anneal-boundary-test-",
            source,
            false,
            cache_policy,
        )
        .unwrap();
        let root = inner.root().to_path_buf();
        Self { inner, root }
    }

    pub fn checker(&self) -> Checker {
        self.checker_with_lean(None)
    }

    pub fn checker_with_lean(&self, lean: Option<&Path>) -> Checker {
        let env = self.inner.checker_env().unwrap();
        Checker::new_with_env(&self.root, lean, env).unwrap()
    }

    pub fn check_expected(
        &mut self,
        expected_code: Option<i32>,
        expected_phase: Option<&str>,
        expected_executed: Option<bool>,
    ) -> Result<Json, Failure> {
        let mut checker = self.checker();
        checker.set_require_mir_wp(false);
        let outcome = checker.run();
        match &outcome {
            Err(err) => {
                assert_eq!(
                    Some(err.code),
                    expected_code,
                    "unexpected error code for {}: {err}",
                    err.phase
                );
                if let Some(phase) = expected_phase {
                    assert_eq!(err.phase, phase, "unexpected phase: {err}");
                }
                if let Some(exp_exec) = expected_executed {
                    assert_eq!(
                        checker.execution_began(),
                        exp_exec,
                        "unexpected execution_began for {err}"
                    );
                }
            }
            Ok(_) => {
                assert!(
                    expected_code.is_none(),
                    "expected rejection {:?}, got success",
                    expected_phase
                );
            }
        }
        outcome
    }
}

/// Compiles `body` as `module` into `out_dir` directly with `lean --setup`,
/// bypassing repository `"preflight"`, and registers the compiled `.olean` and
/// its import edges with the checker's admitted toolchain so later forged
/// modules and inspector requests can import it.
///
/// The setup descriptor lists `Init.Core` and every module in `imports`.
pub fn compile_forged_module(
    checker: &mut Checker,
    src_root: &Path,
    out_dir: &Path,
    imports: &[&str],
    module: &str,
    body: &str,
) {
    let rel = module.replace('.', "/");
    let src = src_root.join(format!("{rel}.lean"));
    fs::create_dir_all(src.parent().unwrap()).unwrap();
    fs::write(&src, body).unwrap();
    let out = out_dir.join(format!("{rel}.olean"));
    fs::create_dir_all(out.parent().unwrap()).unwrap();
    let edges: Vec<ImportEdge> = ["Init.Core"]
        .iter()
        .chain(imports)
        .map(|imp| ImportEdge {
            module: (*imp).to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    let setup_path = checker.write_setup_json(module, &edges).unwrap();
    checker
        .process(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                setup_path.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let available = BTreeMap::from([("olean", out.to_string_lossy().into_owned())]);
    let arts = ModuleArtifacts::from_available(&available, "test", String::new).unwrap();
    let adm = checker.admitted_mut().unwrap();
    adm.artifacts.insert(module.to_string(), arts);
    adm.graph.insert(module.to_string(), edges);
}

/// Writes `source` to `script` and runs it with `lean --run`.
pub fn run_lean_script(checker: &mut Checker, label: &str, script: &Path, source: &str) {
    fs::write(script, source).unwrap();
    checker
        .process(
            label,
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "--run".to_string(),
                script.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
}
