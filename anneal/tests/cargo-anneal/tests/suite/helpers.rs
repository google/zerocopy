// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared test helpers for the `cargo-anneal` integration test suite.

use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    sync::{Mutex, OnceLock},
    thread,
    time::Duration,
};

use anneal_testkit::{
    ExecutedRun, Invocation, StagedWorkspace, ToolchainEnv, ToolchainMode,
    VerifyFailureReceipt, VerifyReceipt, VerifySuccessReceipt, WorkspaceBuilder,
    assertions::{assert_outcome_exit, assert_rejected},
    workspace::Building,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

pub const DEFAULT_TIMEOUT: Duration = Duration::from_secs(180);

pub const SCALAR_SPEC: &str =
    include_str!("../../../../trusted/cargo-anneal/assets/scalar/Spec.lean");
pub const SCALAR_PROOF: &str =
    include_str!("../../../../trusted/cargo-anneal/assets/scalar/Proof.lean");
pub const SCALAR_SOURCE: &str =
    include_str!("../../../../trusted/cargo-anneal/assets/scalar/lib.rs");
pub const SCALAR_UNSUPPORTED: &str = include_str!("../../../corpora/scalar/unsupported.rs");
pub const SCALAR_DEPENDENCY: &str = include_str!("../../../corpora/scalar/dependency.rs");

/// Returns the cached workspace toolchain paths, discovering the workspace
/// `cargo-anneal-test-bin` binary alongside ambient or sibling `capture`,
/// `lean`, and `sysroot` paths.
pub fn workspace_tools() -> &'static ToolchainEnv {
    static TOOLS: OnceLock<ToolchainEnv> = OnceLock::new();
    TOOLS.get_or_init(|| {
        let cli_bin = PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"));
        ToolchainEnv::resolve(ToolchainMode::WorkspaceBuild {
            cli_bin: Some(cli_bin),
            capture_bin: None,
            auditor_bin: None,
        })
        .expect("resolve workspace toolchain environment")
    })
}

/// Returns the `anneal/` workspace crate root.
pub fn anneal_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonicalize anneal root")
}

/// Returns the declarative corpus root (`anneal/tests/corpora`).
pub fn corpora_dir() -> PathBuf {
    anneal_root().join("tests/corpora")
}

/// Returns a path inside `anneal/tests/corpora`.
pub fn corpus_path(rel: &str) -> PathBuf {
    corpora_dir().join(rel)
}

/// Computes lowercase hex SHA-256 of `bytes`.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

/// Creates a new isolated workspace builder with the suite's default timeout.
pub fn new_workspace(prefix: &str) -> WorkspaceBuilder<Building> {
    WorkspaceBuilder::new(prefix, DEFAULT_TIMEOUT).expect("create workspace builder")
}

/// Stages all `(relative_path, bytes)` entries into a fresh `StagedWorkspace`.
pub fn stage_work_files(prefix: &str, files: &[(&str, &[u8])]) -> StagedWorkspace {
    let mut builder = new_workspace(prefix);
    for (rel, bytes) in files {
        builder.write_work_file(rel, bytes).expect("write work file");
    }
    builder.stage().expect("stage workspace")
}

/// Runs `cargo-anneal verify` via `StagedWorkspace::run_verify` using `&str`
/// arguments, propagating workspace tool flags (`--capture`, `--sysroot`,
/// `--lean`).
pub fn run_verify_strs(staged: &StagedWorkspace, args: &[&str]) -> ExecutedRun<VerifyReceipt> {
    let os_args: Vec<&OsStr> = args.iter().map(OsStr::new).collect();
    staged.run_verify(workspace_tools(), &os_args).expect("execute cargo-anneal verify")
}

/// Constructs a `cargo-anneal verify` [`Invocation`] pinned to test tools.
pub fn verify_invocation(args: &[&OsStr]) -> Invocation {
    let tools = workspace_tools();
    let cli = tools.cli.as_deref().expect("workspace cli binary");
    let capture = tools.capture.as_deref().expect("workspace capture binary");
    let mut inv = Invocation::new(cli, &["verify", "--format", "json"])
        .arg("--capture")
        .arg(capture)
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot);
    for arg in args {
        inv = inv.arg(arg);
    }
    inv
}

/// Forwards host env vars needed by `cargo metadata` in shortcut runs.
pub fn with_host_cargo_env(mut inv: Invocation) -> Invocation {
    for key in ["PATH", "HOME", "CARGO_HOME", "RUSTUP_HOME", "TMPDIR"] {
        if let Some(val) = env::var_os(key) {
            inv = inv.env(key, val);
        }
    }
    inv
}

/// Executes a pre-built `verify` command and parses its Schema v3 receipt.
pub fn run_verify_inv(staged: &StagedWorkspace, inv: &Invocation) -> ExecutedRun<VerifyReceipt> {
    let raw = staged.exec(inv).expect("execute cargo-anneal verify");
    let receipt = VerifyReceipt::from_json_slice(&raw.process.stdout).unwrap_or_else(|err| {
        panic!("parse verify receipt failed: {err}\n{}", raw.process.describe())
    });
    ExecutedRun { output: receipt, process: raw.process }
}

/// Wraps [`SCALAR_SPEC`]'s copyright header around `imports` and `decls`.
pub fn lean_source(imports: &str, declarations: &str) -> String {
    let (header, _) = SCALAR_SPEC.split_once("module\nprelude").expect("scalar Spec.lean header");
    format!("{header}prelude\n{imports}\n\n{declarations}\n")
}

/// Wraps [`SCALAR_SPEC`]'s copyright header in a `module`-mode Lean source.
pub fn lean_module_source(imports: &str, declarations: &str) -> String {
    let (header, _) = SCALAR_SPEC.split_once("module\nprelude").expect("scalar Spec.lean header");
    format!("{header}module\nprelude\n{imports}\n\n{declarations}\n")
}

/// Asserts a verified receipt exit code, schema version, and `audit.replay`.
pub fn expect_verified<'a>(
    run: &'a ExecutedRun<VerifyReceipt>,
    expected_status: &str,
    expected_replay: bool,
) -> &'a VerifySuccessReceipt {
    assert_outcome_exit(&run.process, 0).unwrap();
    let VerifyReceipt::Verified(receipt) = &run.output else {
        panic!("expected verified receipt, got {:?}", run.output);
    };
    assert_eq!(receipt.schema_version, 3, "unexpected schema_version: {receipt:?}");
    assert_eq!(receipt.status, expected_status, "unexpected status: {receipt:?}");
    assert_eq!(
        receipt.audit.get("replay").and_then(Value::as_bool),
        Some(expected_replay),
        "unexpected audit.replay in {:?}",
        receipt.audit
    );
    receipt
}

/// Asserts a failed verification receipt exit code, status, phase, and detail.
pub fn expect_failed<'a>(
    run: &'a ExecutedRun<VerifyReceipt>,
    expected_code: i32,
    expected_status: &str,
    expected_phase: Option<&str>,
    detail_substr: &str,
) -> &'a VerifyFailureReceipt {
    assert_outcome_exit(&run.process, expected_code).unwrap();
    assert_rejected(&run.output, expected_status, expected_phase, detail_substr).unwrap()
}

/// Builds a Schema 1 `verify --request` payload with separate rust/proof roots.
pub fn subcrate_request_json(
    rust_root: &Path,
    crate_root_rel: &str,
    crate_name: &str,
    proof_root: &Path,
) -> Value {
    json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_root,
            "crate_root": crate_root_rel,
            "crate_name": crate_name,
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": [crate_root_rel]
        },
        "scope": { "kind": "crate" },
        "proof": {
            "source_root": proof_root,
            "sources": [
                { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                { "module": "Proof", "path": "Proof.lean", "role": "proof" }
            ]
        }
    })
}

/// Writes `value` as pretty JSON to `path` and returns `path`.
pub fn write_json_file(path: &Path, value: &Value) -> PathBuf {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create parent dir");
    }
    fs::write(path, serde_json::to_vec_pretty(value).expect("serialize JSON"))
        .expect("write JSON file");
    path.to_path_buf()
}

/// Materializes `rust/` and `lean/` baseline files and returns the request.
pub fn write_scalar_baseline(work_dir: &Path) -> Value {
    let rust = work_dir.join("rust");
    let lean = work_dir.join("lean");
    fs::create_dir_all(&rust).expect("create rust dir");
    fs::create_dir_all(&lean).expect("create lean dir");
    fs::write(rust.join("lib.rs"), SCALAR_SOURCE).expect("write scalar lib.rs");
    fs::write(lean.join("Spec.lean"), SCALAR_SPEC).expect("write scalar Spec.lean");
    fs::write(lean.join("Proof.lean"), SCALAR_PROOF).expect("write scalar Proof.lean");
    fs::write(lean.join("Proof.olean"), b"not a Lean object file").expect("write spoof olean");
    subcrate_request_json(&rust, "lib.rs", "scalar", &lean)
}

/// Returns a sorted list of immediate child paths in `dir`.
pub fn sorted_dir_entries(dir: &Path) -> Vec<PathBuf> {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()))
        .map(|res| res.expect("dir entry").path())
        .collect();
    entries.sort();
    entries
}

/// Executes `items` concurrently using `max_workers` threads and returns
/// results in the original order.
pub fn run_parallel<T, R, F>(items: Vec<T>, max_workers: usize, f: F) -> Vec<R>
where
    T: Send,
    R: Send,
    F: Fn(T) -> R + Sync,
{
    let total = items.len();
    if total == 0 {
        return Vec::new();
    }
    let workers = max_workers.max(1).min(total);
    let queue: Mutex<Vec<Option<T>>> = Mutex::new(items.into_iter().map(Some).collect());
    let next_idx = Mutex::new(0usize);
    let results: Mutex<Vec<Option<R>>> = Mutex::new((0..total).map(|_| None).collect());

    thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let (idx, item) = {
                    let mut idx_guard = next_idx.lock().unwrap();
                    let cur = *idx_guard;
                    if cur >= total {
                        return;
                    }
                    *idx_guard += 1;
                    drop(idx_guard);
                    let mut q = queue.lock().unwrap();
                    let item = q[cur].take().expect("item taken once");
                    (cur, item)
                };
                let out = f(item);
                let mut res_guard = results.lock().unwrap();
                res_guard[idx] = Some(out);
            });
        }
    });

    results
        .into_inner()
        .unwrap()
        .into_iter()
        .map(|slot| slot.expect("every work item produced a result"))
        .collect()
}
