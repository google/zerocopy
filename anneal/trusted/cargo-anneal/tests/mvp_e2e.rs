// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exercise the installed verification boundary with real Rust and Lean tools.
//!
//! Build `anneal-rustc-capture` before running this test. The harness accepts
//! `ANNEAL_CLI`, `ANNEAL_CAPTURE`, `ANNEAL_LEAN`, and `ANNEAL_SYSROOT`
//! overrides (along with `ANNEAL_TEST_RUST_SYSROOT` and
//! `ANNEAL_TEST_INSTALL_ROOT` fallback settings) for separately installed
//! tools. Missing tools fail the test with setup diagnostics; they never turn
//! it into a skipped pass.

use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};

use serde_json::{Value, json};
use tempfile::TempDir;

const SPEC: &str = include_str!("fixtures/scalar/Spec.lean");
const PROOF: &str = include_str!("fixtures/scalar/Proof.lean");
const SOURCE: &str = include_str!("fixtures/scalar/lib.rs");
const UNSUPPORTED: &str = include_str!("fixtures/scalar/unsupported.rs");
const DEPENDENCY: &str = include_str!("fixtures/scalar/dependency.rs");

struct Tools {
    cli: PathBuf,
    capture: PathBuf,
    lean: PathBuf,
    sysroot: PathBuf,
    install_root: Option<PathBuf>,
}

impl Tools {
    fn discover() -> Self {
        let install_root = override_path("ANNEAL_TEST_INSTALL_ROOT");
        // Prefer an explicit `ANNEAL_CLI` override, then the freshly built
        // test binary (`CARGO_BIN_EXE_cargo-anneal`). Never read
        // `ANNEAL_TEST_CARGO_ANNEAL` here so CI's installed-smoke variable
        // does not silently switch workspace tests off the build.
        let cli = first_override(&["ANNEAL_CLI"])
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_CLI");
        // Prefer an explicit `ANNEAL_CAPTURE` override, then the freshly built
        // sibling beside `cli`, then an explicit `ANNEAL_TEST_INSTALL_ROOT`
        // bundle (never a user-global install).
        let capture = first_override(&["ANNEAL_CAPTURE"])
            .or_else(|| {
                let sibling = cli.with_file_name("anneal-rustc-capture");
                sibling.is_file().then_some(sibling)
            })
            .or_else(|| install_root.as_ref().map(|root| root.join("bin/anneal-rustc-capture")))
            .unwrap_or_else(|| cli.with_file_name("anneal-rustc-capture"));
        let capture = required_file(
            capture,
            "anneal-rustc-capture; build it before running this test",
            "ANNEAL_CAPTURE",
        );
        let lean = first_override(&["ANNEAL_LEAN"])
            .or_else(|| install_root.as_ref().map(|root| root.join("lean/bin/lean")))
            .unwrap_or_else(cargo_anneal::default_lean_path);
        let lean = required_file(lean, "the pinned Lean executable", "ANNEAL_LEAN");
        let sysroot = first_override(&["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"])
            .or_else(|| install_root.as_ref().map(|root| root.join("rust")))
            .unwrap_or_else(|| {
                let output = Command::new("rustup")
                    .args(["run", "nightly-2026-05-31", "rustc", "--print", "sysroot"])
                    .output()
                    .expect("install the pinned compiler or set ANNEAL_SYSROOT");
                assert!(
                    output.status.success(),
                    "cannot find the pinned compiler sysroot; set ANNEAL_SYSROOT:\n{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                PathBuf::from(
                    String::from_utf8(output.stdout).expect("rustc sysroot must be UTF-8").trim(),
                )
            });
        assert!(
            sysroot.join("lib").is_dir(),
            "missing compiler sysroot {}; set ANNEAL_SYSROOT",
            sysroot.display()
        );
        let sysroot = fs::canonicalize(sysroot).expect("resolve test sysroot path");
        Self { cli, capture, lean, sysroot, install_root }
    }

    fn command(&self) -> Command {
        let mut command = Command::new(&self.cli);
        command
            .arg("verify")
            .arg("--capture")
            .arg(&self.capture)
            .arg("--lean")
            .arg(&self.lean)
            .arg("--sysroot")
            .arg(&self.sysroot);
        command
    }
}

fn override_path(name: &str) -> Option<PathBuf> {
    std::env::var_os(name).filter(|value| !value.is_empty()).map(PathBuf::from)
}

fn first_override(names: &[&str]) -> Option<PathBuf> {
    names.iter().copied().find_map(override_path)
}

fn required_file(path: PathBuf, description: &str, variable: &str) -> PathBuf {
    assert!(path.is_file(), "missing {description} at {}; set {variable}", path.display());
    fs::canonicalize(path).expect("resolve test tool path")
}

struct Fixture {
    directory: TempDir,
    request: Value,
}

impl Fixture {
    fn new() -> Self {
        let directory = tempfile::Builder::new()
            .prefix("anneal-mvp-e2e-")
            .tempdir()
            .expect("create regression fixture");
        let rust = directory.path().join("rust");
        let lean = directory.path().join("lean");
        fs::create_dir(&rust).unwrap();
        fs::create_dir(&lean).unwrap();
        fs::write(rust.join("lib.rs"), SOURCE).unwrap();
        fs::write(lean.join("Spec.lean"), SPEC).unwrap();
        fs::write(lean.join("Proof.lean"), PROOF).unwrap();
        // Adjacent compiled files must not replace the declared proof source.
        fs::write(lean.join("Proof.olean"), b"not a Lean object file").unwrap();
        let request = json!({
            "schema_version": 1,
            "compilation": {
                "source_root": rust,
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {
                "source_root": lean,
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"}
                ]
            }
        });
        Self { directory, request }
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.directory.path().join(relative)
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        fs::write(self.path(relative), contents).unwrap();
    }

    fn run(&self, tools: &Tools, name: &str, request: &Value) -> Receipt {
        let request_path = self.path(&format!("{name}.json"));
        fs::write(&request_path, serde_json::to_vec_pretty(request).unwrap()).unwrap();
        self.execute(
            name,
            tools
                .command()
                .arg("--request")
                .arg(request_path)
                .arg("--artifacts")
                .arg(self.path(name)),
        )
    }

    fn execute(&self, name: &str, command: &mut Command) -> Receipt {
        eprintln!("MVP CLI regression: {name}");
        let output = command
            .current_dir(self.directory.path())
            .output()
            .unwrap_or_else(|error| panic!("cannot run {name}: {error}"));
        let value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "{name} did not return a JSON receipt: {error}\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
        });
        Receipt { name: name.to_owned(), value, output }
    }
}

struct Receipt {
    name: String,
    value: Value,
    output: Output,
}

impl Receipt {
    fn expect(&self, code: i32, status: &str, phase: Option<&str>) {
        assert_eq!(
            self.output.status.code(),
            Some(code),
            "{} returned an unexpected exit code:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(
            self.value["schema_version"], 3,
            "{}: {}",
            self.name, self.value
        );
        assert!(
            self.value.get("tainted").is_none(),
            "{}: {}",
            self.name,
            self.value
        );
        assert_eq!(
            self.value["status"], status,
            "{}: {}",
            self.name, self.value
        );
        if let Some(phase) = phase {
            assert_eq!(self.value["phase"], phase, "{}: {}", self.name, self.value);
        }
    }

    /// Require the rejection to come from a specific acceptance guard, so a
    /// negative cannot pass because some unrelated check failed first.
    fn expect_detail(&self, fragment: &str) {
        let detail = self.value["detail"].as_str().unwrap_or_default();
        assert!(
            detail.contains(fragment),
            "{}: expected detail containing {fragment:?}: {}",
            self.name,
            self.value
        );
    }
}

fn lean_source(imports: &str, declarations: &str) -> String {
    let (header, _) = SPEC.split_once("prelude").unwrap();
    format!("{header}prelude\n{imports}\n\n{declarations}\n")
}

fn selected(request: &Value) -> Value {
    let mut request = request.clone();
    request["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
    request
}

#[cfg(unix)]
#[test]
fn canonicalizes_symlinked_temporary_directory_source_bindings() {
    use std::{fmt::Write as _, os::unix::fs::symlink};

    use sha2::{Digest, Sha256};

    fn sha256_hex(bytes: &[u8]) -> String {
        let mut hex = String::with_capacity(64);
        for byte in Sha256::digest(bytes) {
            let _ = write!(&mut hex, "{byte:02x}");
        }
        hex
    }

    let tools = Tools::discover();
    let fixture = Fixture::new();
    let temporary = fixture.path("temporary-physical");
    let alias = fixture.path("temporary-alias");
    fs::create_dir(&temporary).unwrap();
    symlink(&temporary, &alias).unwrap();
    let request = fixture.path("symlinked-request.json");
    fs::write(&request, serde_json::to_vec_pretty(&fixture.request).unwrap()).unwrap();

    // Set TMPDIR only for the verifier process. The Rust test's own temporary
    // directory and other concurrently scheduled tests keep their environment.
    let accepted = fixture.execute(
        "symlinked-temporary-directory",
        tools
            .command()
            .env("TMPDIR", &alias)
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(fixture.path("symlinked-artifacts")),
    );
    accepted.expect(0, "crate_verified", None);
    assert_eq!(accepted.value["audit"]["exactType"], true);
    assert_eq!(accepted.value["audit"]["replay"], true);
    let bytes = fs::read(fixture.path("symlinked-artifacts/capture/capture.json")).unwrap();
    let captured: Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(captured["source_files"].as_array().unwrap().len(), 1);
    let input = &captured["source_files"][0];
    let input_path = PathBuf::from(input["path"].as_str().unwrap());
    assert!(input_path.starts_with(fs::canonicalize(&temporary).unwrap()));
    assert_eq!(input["path"], captured["configuration"]["crate_root"]);
    assert_eq!(input["sha256"], sha256_hex(SOURCE.as_bytes()));
    assert_eq!(input["sha256"], accepted.value["sources"][0]["sha256"]);
    assert_eq!(accepted.value["capture_sha256"], sha256_hex(&bytes));
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());

    // Canonical temporary paths must not broaden the compiler's read allowlist.
    // An absolute include exists on disk but is not a declared source input.
    let undeclared = fixture.path("undeclared.rs");
    fs::write(&undeclared, "0").unwrap();
    fixture.write(
        "rust/lib.rs",
        format!(
            "pub fn zero() -> u64 {{ include!({}) }}\n",
            serde_json::to_string(&undeclared).unwrap()
        ),
    );
    fixture
        .execute(
            "undeclared-through-symlinked-temporary-directory",
            tools
                .command()
                .env("TMPDIR", &alias)
                .arg("--request")
                .arg(&request)
                .arg("--artifacts")
                .arg(fixture.path("undeclared-artifacts")),
        )
        .expect(1, "unsupported", Some("capture"));
    assert!(!fixture.path("undeclared-artifacts/capture/capture.json").exists());
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());
}

// Keep this mutation matrix in one test so its backend invocations stay serial.
// Other tests also launch Lean; use one Rust test thread to bound their memory.
#[test]
fn verifies_real_source_and_rejects_boundary_mutations() {
    let tools = Tools::discover();
    let fixture = Fixture::new();

    let accepted = fixture.run(&tools, "whole-crate", &fixture.request);
    accepted.expect(0, "crate_verified", None);
    assert_eq!(accepted.value["experimental"], true);
    assert_eq!(accepted.value["scope"], json!({"kind": "crate"}));
    assert_eq!(accepted.value["selected"][0]["path"], "zero");
    for field in [
        "request_sha256",
        "capture_sha256",
        "capture_binary_sha256",
        "model_manifest_sha256",
        "specification_manifest_sha256",
    ] {
        assert_eq!(accepted.value[field].as_str().unwrap().len(), 64);
    }
    // Only locked digests authenticate toolchain files. The receipt keeps them
    // apart from the recorded capture digest and from unhashed components.
    assert_eq!(
        accepted.value["toolchain_identity"],
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules"
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Lean sysroot .ir/.ir.sig companions outside the locks",
                "Rust compiler and sysroot, identified by their reported commit"
            ]
        })
    );
    let provenance = &accepted.value["correspondence_provenance"];
    assert_eq!(provenance["schema_version"], 1);
    assert_eq!(provenance["upstream_repository"], "https://github.com/proofs-rs/lean-miri.git");
    assert_eq!(provenance["upstream_commit"], "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a");
    assert_eq!(provenance["build_lean_toolchain"], "leanprover/lean4:v4.34.1");
    assert_eq!(
        provenance["sysroot_foundation_manifest_sha256"],
        cargo_anneal::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256
    );
    assert_eq!(provenance["upstream_pin_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(provenance["correspondence_adapters"].as_object().unwrap().len(), 7);
    assert_eq!(
        provenance["correspondence_adapters"]
            ["trusted/correspondence/Trusted/Correspondence.lean"]
            .as_str()
            .unwrap()
            .len(),
        64
    );
    assert_eq!(provenance["patched_files"].as_array().unwrap().len(), 13);
    assert_eq!(provenance["correspondence_proofs"].as_object().unwrap().len(), 16);
    for proof_key in [
        "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
        "correspondence/Anneal/MirCorrespondenceProof.lean",
    ] {
        assert_eq!(provenance["correspondence_proofs"][proof_key].as_str().unwrap().len(), 64);
    }
    for lean_key in [
        "trusted/lean/Trusted.lean",
        "trusted/lean/Trusted/MirAst.lean",
        "trusted/lean/Trusted/MirSemantics.lean",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
    ] {
        assert_eq!(provenance["trusted_lean"][lean_key].as_str().unwrap().len(), 64);
    }
    assert!(provenance["note"].as_str().unwrap().contains("anneal-audit --require-correspondence"));
    // Verify the receipt provenance matches the canonical constant extracted by
    // `flake.nix`, and matches the installed omnibus archive copy when present.
    let bundled_source = fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/bundled_resources.rs"),
    )
    .expect("read bundled_resources.rs");
    let provenance_lines: Vec<&str> = bundled_source
        .lines()
        .filter_map(|line| {
            line.strip_prefix("const CORRESPONDENCE_PROVENANCE_JSON: &str = ")
                .and_then(|rest| rest.strip_suffix(';'))
        })
        .collect();
    assert_eq!(provenance_lines.len(), 1, "expected unique CORRESPONDENCE_PROVENANCE_JSON line");
    let raw_provenance_json: String = serde_json::from_str(provenance_lines[0])
        .expect("decode CORRESPONDENCE_PROVENANCE_JSON string literal");
    let bundled_provenance: Value = serde_json::from_str(&raw_provenance_json)
        .expect("parse CORRESPONDENCE_PROVENANCE_JSON object");
    assert_eq!(provenance, &bundled_provenance);
    if let Some(install_root) = &tools.install_root {
        let archive_path = install_root.join("share/anneal/correspondence-provenance.json");
        let archive_bytes = fs::read(&archive_path).unwrap_or_else(|err| {
            panic!("read installed archive provenance {}: {err}", archive_path.display())
        });
        let archive_provenance: Value =
            serde_json::from_slice(&archive_bytes).expect("parse archive provenance JSON");
        assert_eq!(
            &archive_provenance, provenance,
            "installed share/anneal/correspondence-provenance.json must match receipt"
        );
    }
    assert!(fixture.path("whole-crate/capture/Captured.lean").is_file());
    assert!(fixture.path("whole-crate/generated/Expected.lean").is_file());
    assert!(fixture.path("whole-crate/audit-request.json").is_file());
    assert!(fixture.path("whole-crate/result.json").is_file());

    // Keep the specification and proof fixed while changing the Rust body.
    // A fresh successful capture must not let the old source proof verify
    // a different implementation.
    fixture.write("rust/lib.rs", SOURCE.replace("    0\n", "    1\n"));
    fixture.run(&tools, "changed-source", &fixture.request).expect(
        1,
        "proof_failed",
        Some("audit"),
    );
    let changed_capture: Value = serde_json::from_slice(
        &fs::read(fixture.path("changed-source/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_ne!(
        accepted.value["sources"][0]["sha256"],
        changed_capture["source_files"][0]["sha256"]
    );
    fixture.write("rust/lib.rs", SOURCE);

    // Each negative compiles a different attempted shortcut around the
    // canonical closed theorem. Require rejection by the `targetAudit` guard
    // in `TrustedBoundary.lean` that each shortcut targets, not a missing
    // tool, malformed receipt, or unrelated failure that could make a negative
    // pass vacuously: the exact type comparison for a different or weakened
    // root, and the fixed axiom policy for an authored axiom or `sorryAx`.
    for (name, declarations, rejection) in [
        (
            "wrong-root",
            "theorem Proof.verify : True := True.intro",
            "policy:target theorem type differs from Expected",
        ),
        (
            "axiom",
            "axiom fabricated : Expected.claim\ntheorem Proof.verify : Expected.claim := fabricated",
            "policy:unapproved axiom fabricated from Proof",
        ),
        (
            "sorry",
            "theorem Proof.verify : Expected.claim := by sorry",
            "policy:unapproved axiom sorryAx from Init.Prelude",
        ),
        (
            "extra-hypothesis",
            "theorem Proof.verify (assumed : Expected.claim) : Expected.claim := assumed",
            "policy:target theorem type differs from Expected",
        ),
    ] {
        fixture.write("lean/Proof.lean", lean_source("import Expected", declarations));
        let rejected = fixture.run(&tools, name, &fixture.request);
        rejected.expect(1, "proof_failed", Some("audit"));
        rejected.expect_detail(rejection);
    }
    fixture.write("lean/Proof.lean", PROOF);

    let mut wrong_role = fixture.request.clone();
    wrong_role["proof"]["sources"][0]["role"] = json!("proof");
    fixture.run(&tools, "wrong-declaration-role", &wrong_role).expect(
        1,
        "unsupported",
        Some("proof"),
    );

    let shadowed = PROOF
        .replace(
            "theorem verify : Expected.claim := by",
            "def Spec.specs : Specs := ⟨fun _ _ => False, fun _ => True⟩\n\n\
             theorem verify : CrateTheorem ⟨Captured.program, Spec.specs⟩ := by",
        )
        .replace(", totalCorrectness⟩", ", True.intro⟩");
    // `def Spec.specs` inside `namespace Proof` declares `Proof.Spec.specs`,
    // which then shadows the reviewed `Spec.specs` in the theorem statement.
    // The exact type comparison must reject the substituted specification.
    fixture.write("lean/Proof.lean", shadowed);
    let rejected = fixture.run(&tools, "shadowed-specification", &fixture.request);
    rejected.expect(1, "proof_failed", Some("audit"));
    rejected.expect_detail("policy:target theorem type differs from Expected");
    fixture.write("lean/Proof.lean", PROOF);

    // Syntax can conceal a specification dependency in a proof-role module.
    // Check the origin boundary itself, rather than crediting an unrelated
    // elaboration error as rejection of the hidden helper.
    fixture.write(
        "lean/Extra.lean",
        lean_source("import Trusted.MirSemantics", "macro \"hiddenProperty\" : term => `(True)"),
    );
    fixture.write(
        "lean/Spec.lean",
        lean_source(
            "import Trusted.MirSemantics\nimport Extra",
            "namespace Spec\ndef specs : Trusted.MirSemantics.Specs :=\n  ⟨fun _ _ => False, fun _ => hiddenProperty⟩\nend Spec",
        ),
    );
    let mut hidden_spec = fixture.request.clone();
    hidden_spec["proof"]["sources"].as_array_mut().unwrap().push(json!({
        "module": "Extra", "path": "Extra.lean", "role": "proof"
    }));
    let hidden = fixture.run(&tools, "hidden-specification-macro", &hidden_spec);
    hidden.expect(1, "proof_failed", Some("audit"));
    let detail = hidden.value["detail"].as_str().unwrap();
    assert!(
        detail.contains("specification")
            || detail.contains("role")
            || detail.contains("Spec cannot import Extra"),
        "macro fixture must fail at the specification origin boundary: {detail}"
    );
    fixture.write("lean/Spec.lean", SPEC);

    // Selected-unit success intentionally leaves unrelated items uncovered;
    // the same crate must fail whole-crate capture. Test both observations
    // so a partial success cannot be presented as complete coverage.
    fixture.write("rust/lib.rs", UNSUPPORTED);
    let mut selected_request = selected(&fixture.request);
    selected_request["scope"]["roots"] = json!(["zero", "zero"]);
    selected_request["compilation"]["cfg"] = json!(["omega", "alpha", "omega"]);
    let normalized = fixture.run(&tools, "selected-outside-closure", &selected_request);
    normalized.expect(0, "selected_unit_verified", None);
    assert_eq!(normalized.value["scope"]["roots"], json!(["zero"]));
    assert_eq!(normalized.value["configuration"]["cfg"], json!(["alpha", "omega"]));
    assert!(
        normalized.value["census"]
            .as_array()
            .unwrap()
            .iter()
            .any(|item| { item["path"] == "unsupported" && item["selected"] == false })
    );
    selected_request["scope"]["roots"] = json!(["zero"]);
    selected_request["compilation"]["cfg"] = json!(["alpha", "omega"]);
    let ordered = fixture.run(&tools, "normalized-request", &selected_request);
    ordered.expect(0, "selected_unit_verified", None);
    assert_eq!(normalized.value["request_sha256"], ordered.value["request_sha256"]);
    fixture.run(&tools, "whole-unsupported", &fixture.request).expect(
        1,
        "unsupported",
        Some("capture"),
    );

    fixture.write("rust/lib.rs", DEPENDENCY);
    fixture.run(&tools, "unsupported-dependency", &selected(&fixture.request)).expect(
        1,
        "unsupported",
        Some("capture"),
    );
    fixture.write("rust/lib.rs", SOURCE);

    let manifest = fixture.path("rust/Cargo.toml");
    let manifest_base = "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[lib]\npath = \"lib.rs\"\n";
    fixture.write(
        "rust/Cargo.toml",
        format!("{manifest_base}[features]\ndefault = [\"extra\"]\nextra = []\n"),
    );
    fixture
        .execute(
            "cargo-default-features",
            tools
                .command()
                .arg("--manifest-path")
                .arg(&manifest)
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(1, "unsupported", Some("cargo"));
    fixture.write("rust/Cargo.toml", manifest_base);
    fs::remove_file(fixture.path("lean/Extra.lean")).unwrap();
    // Hidden directories inside `--proof-dir` and ambient `RUSTC` overrides
    // must not perturb the Cargo shortcut.
    fs::create_dir(fixture.path("lean/.cache")).unwrap();
    fixture.write("lean/.cache/Ignored.lean", b"not valid Lean syntax");
    fixture
        .execute(
            "cargo-feature-free-library",
            tools
                .command()
                .env("RUSTC", fixture.path("nonexistent-rustc"))
                .arg("--manifest-path")
                .arg(&manifest)
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(0, "crate_verified", None);

    // Workspace-root compiler overrides must also be refused when verifying a
    // member crate via `--manifest-path`.
    let ws_root = fixture.path("workspace-override");
    fs::create_dir_all(ws_root.join(".cargo")).unwrap();
    fs::create_dir_all(ws_root.join("member")).unwrap();
    fs::write(
        ws_root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"member\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    fs::write(
        ws_root.join(".cargo/config.toml"),
        "[build]\nrustflags = [\"--cfg=override_flag\"]\n",
    )
    .unwrap();
    fs::write(ws_root.join("member/Cargo.toml"), manifest_base).unwrap();
    fs::write(ws_root.join("member/lib.rs"), SOURCE).unwrap();
    fixture
        .execute(
            "cargo-workspace-compiler-override",
            tools
                .command()
                .arg("--manifest-path")
                .arg(ws_root.join("member/Cargo.toml"))
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(1, "unsupported", Some("cargo"));

    // Runner-owned names choose private staging destinations and claim the
    // model, captured subject, or generated expectation. Each spelling must be
    // refused before Lean compiles any authored source.
    for module in ["Anneal.Shadow", "Anneal", "Trusted", "Trusted.Shadow", "Captured", "Expected"] {
        let mut reserved = fixture.request.clone();
        reserved["proof"]["sources"].as_array_mut().unwrap().push(json!({
            "module": module, "path": "Proof.lean", "role": "proof"
        }));
        let rejected = fixture.run(&tools, &format!("reserved-module-{module}"), &reserved);
        rejected.expect(1, "unsupported", Some("proof"));
        assert_eq!(
            rejected.value["detail"], "invalid, duplicate or reserved proof module",
            "{module}: {}",
            rejected.value
        );
    }

    // Retention must preserve caller-owned evidence even when the new
    // request itself is invalid. This checks operation ordering as well as
    // the create-only filesystem rule.
    let mut invalid = fixture.request.clone();
    invalid["schema_version"] = json!(0);
    let sentinel = fixture.path("whole-crate/sentinel");
    fs::write(&sentinel, b"keep existing evidence").unwrap();
    fixture.run(&tools, "whole-crate", &invalid).expect(2, "tool_failed", Some("retention"));
    assert_eq!(fs::read(sentinel).unwrap(), b"keep existing evidence");

    let request_path = fixture.path("missing-capture.json");
    fs::write(&request_path, serde_json::to_vec(&fixture.request).unwrap()).unwrap();
    fixture
        .execute(
            "missing-capture-is-an-error",
            Command::new(&tools.cli)
                .arg("verify")
                .arg("--request")
                .arg(request_path)
                .arg("--capture")
                .arg(fixture.path("missing-capture"))
                .arg("--lean")
                .arg(&tools.lean)
                .arg("--sysroot")
                .arg(&tools.sysroot),
        )
        .expect(2, "tool_failed", Some("capture-tool"));

    // This source never returns. Its root still requires safety of every
    // reachable prefix, while the authored property proves no return exists.
    fixture.write("rust/lib.rs", include_str!("fixtures/spin/lib.rs"));
    fixture.write("lean/Spec.lean", include_str!("fixtures/spin/Spec.lean"));
    fixture.write("lean/Proof.lean", include_str!("fixtures/spin/Proof.lean"));
    fixture.run(&tools, "safe-divergence", &fixture.request).expect(0, "crate_verified", None);
}

#[test]
fn unsafe_contracts_remain_bound_to_function_identities() {
    let tools = Tools::discover();
    let fixture = Fixture::new();
    let original = include_str!("fixtures/unsafe_identity/lib.rs");
    fixture.write("rust/lib.rs", original);
    fixture.write("lean/Spec.lean", include_str!("fixtures/unsafe_identity/Spec.lean"));
    fixture.write("lean/Proof.lean", include_str!("fixtures/unsafe_identity/Proof.lean"));
    fixture.run(&tools, "unsafe-identity-before", &fixture.request).expect(
        0,
        "crate_verified",
        None,
    );

    // Preserve the captured operational bodies and the reviewed specification
    // while moving the uncallable body from `locked` to the unrestricted
    // `open`. An ordinal predicate would follow the faulting body's old slot
    // and accept. Keep both Lean sources unchanged. Rewriting a predicate in
    // response to the mutation would change the reviewed contract instead of
    // testing its binding.
    let changed = original
        .replace("fn locked", "fn temporary")
        .replace("fn open", "fn locked")
        .replace("fn temporary", "fn open");
    fixture.write("rust/lib.rs", changed);
    fixture.run(&tools, "unsafe-identity-after", &fixture.request).expect(
        1,
        "proof_failed",
        Some("audit"),
    );
}

#[test]
fn declared_cfg_cannot_expand_compiler_response_files() {
    let tools = Tools::discover();
    let fixture = Fixture::new();
    fixture.write(
        "rust/lib.rs",
        format!("{SOURCE}\n#[cfg(not(injected))]\ncompile_error!(\"missing declared cfg\");\n"),
    );
    // This file is deliberately outside source_root and source_files. Its
    // harmless second cfg would make the compilation succeed if rustc treated
    // a declared cfg as an argument file instead of a literal cfg value.
    let response = fixture.path("compiler-flags.rsp");
    fs::write(&response, b"dummy\n--cfg\ninjected\n").unwrap();
    for (name, path) in
        [("cfg-existing-response", response), ("cfg-missing-response", fixture.path("missing.rsp"))]
    {
        let mut request = fixture.request.clone();
        request["compilation"]["cfg"] = json!([format!("@{}", path.to_str().unwrap())]);
        let receipt = fixture.run(&tools, name, &request);
        receipt.expect(2, "compiler_failed", Some("capture"));
        let stderr = String::from_utf8_lossy(&receipt.output.stderr);
        assert!(
            stderr.contains("invalid `--cfg` argument"),
            "missing compiler diagnostic on stderr: {stderr}"
        );
        let diagnostic =
            fs::read_to_string(fixture.path(&format!("{name}/capture.stderr"))).unwrap();
        assert!(diagnostic.contains("invalid `--cfg` argument"));
        assert!(!diagnostic.contains("failed to load argument file"));
        assert!(!fixture.path(&format!("{name}/capture/capture.json")).exists());
    }

    // A normal bare flag and a quoted @ string remain unchanged in the
    // authenticated configuration and still verify with the installed tools.
    let mut request = fixture.request.clone();
    let cfg = json!([r#"feature="@literal""#, "injected"]);
    request["compilation"]["cfg"] = cfg.clone();
    let receipt = fixture.run(&tools, "cfg-literal-values", &request);
    receipt.expect(0, "crate_verified", None);
    assert_eq!(receipt.value["configuration"]["cfg"], cfg);
}

#[cfg(unix)]
#[test]
fn rustc_mode_symlinks_replay_export_lean_lib_and_unpinned_taint() {
    use std::os::unix::fs::symlink;

    let tools = Tools::discover();
    let fixture = Fixture::new();

    // Place Rust and Lean files in disjoint physical locations and expose them
    // through Bazel-like runfiles symlinks to verify logical prefix staging.
    let cas = fixture.path("cas");
    fs::create_dir(&cas).unwrap();
    fs::write(cas.join("scalar_lib.rs"), format!("pub mod helper;\n{SOURCE}")).unwrap();
    fs::write(cas.join("helper_phys.rs"), "pub fn unused() -> u64 { 1 }\n").unwrap();
    fs::write(
        cas.join("scalar_spec.lean"),
        SPEC.replace("namespace Spec", "namespace Contract").replace("end Spec", "end Contract"),
    )
    .unwrap();
    fs::write(
        cas.join("scalar_proof.lean"),
        PROOF
            .replace("Spec.expectedReturn", "Contract.expectedReturn")
            .replace("Spec.returnsZero", "Contract.returnsZero")
            .replace("namespace Proof", "namespace Spec.Helper")
            .replace("end Proof", "end Spec.Helper")
            .replace("theorem verify :", "theorem custom_verify :"),
    )
    .unwrap();

    let runfiles = fixture.path("runfiles/pkg/src");
    fs::create_dir_all(&runfiles).unwrap();
    symlink(cas.join("scalar_lib.rs"), runfiles.join("lib.rs")).unwrap();
    symlink(cas.join("helper_phys.rs"), runfiles.join("helper.rs")).unwrap();
    symlink(cas.join("scalar_spec.lean"), runfiles.join("Contract.lean")).unwrap();
    symlink(cas.join("scalar_proof.lean"), runfiles.join("Spec.Helper.lean")).unwrap();

    // 1. Passing rustc-mode run with symlinked sibling modules, strict roles,
    //    qualified entrypoints, and --export-lean-lib.
    let pass_artifacts = fixture.path("rustc-pass");
    let pass = fixture.execute(
        "rustc-pass",
        tools
            .command()
            .arg("--artifacts")
            .arg(&pass_artifacts)
            .arg("--export-lean-lib")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args(["--crate-name", "scalar", "--select", "zero", "--source-file"])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!("Contract={}", runfiles.join("Contract.lean").display()))
            .arg("--proof-file")
            .arg(format!("Spec.Helper={}", runfiles.join("Spec.Helper.lean").display()))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    pass.expect(0, "selected_unit_verified", None);
    assert_eq!(pass.value["taint_reasons"], json!([]));
    assert!(pass.output.stderr.is_empty());
    let sandbox_kind = pass.value["elaboration_sandbox"]
        .as_str()
        .expect("receipt includes elaboration_sandbox");
    assert!(
        matches!(sandbox_kind, "linux_bwrap" | "linux_landlock_seccomp"),
        "expected active ExecSeal sandbox, got {sandbox_kind:?}"
    );
    assert!(
        !pass.value["deferred"].as_array().unwrap().iter().any(|d| d
            .as_str()
            .is_some_and(|s| s.contains("hostile Lean elaborator"))),
        "sandboxed run must omit hostile Lean elaborator effects from deferred: {}",
        pass.value["deferred"]
    );
    let lean_lib = pass_artifacts.join("lean-lib");
    assert!(lean_lib.join("Trusted/MirAst.olean").is_file());
    assert!(lean_lib.join("Anneal/MirWp.olean").is_file());
    assert!(lean_lib.join("Captured.olean").is_file());
    assert!(lean_lib.join("Contract.olean").is_file());
    assert!(lean_lib.join("Spec/Helper.olean").is_file());
    assert!(!lean_lib.join("lean-toolchain").exists());
    assert!(!lean_lib.join("Spec/Helper.ir").exists());
    assert!(!lean_lib.join("Spec/Helper.ir.sig").exists());

    // 2. Self-contained request.json in <artifacts> replays via --request.
    let replay = fixture.execute(
        "rustc-replay",
        tools
            .command()
            .arg("--request")
            .arg(pass_artifacts.join("request.json"))
            .arg("--artifacts")
            .arg(fixture.path("rustc-replay")),
    );
    replay.expect(0, "selected_unit_verified", None);
    assert_eq!(replay.value["request_sha256"], pass.value["request_sha256"]);

    // 3. Proof failure still exports compiled .olean files before Checker
    //    drops.
    let bad_proof = lean_source(
        "import Expected",
        "namespace Proof\n\ntheorem verify : True := True.intro\n\nend Proof",
    );
    fs::write(cas.join("bad_proof.lean"), bad_proof).unwrap();
    let bad_link = runfiles.join("BadProof.lean");
    symlink(cas.join("bad_proof.lean"), &bad_link).unwrap();
    let fail_artifacts = fixture.path("rustc-proof-fail");
    let failed = fixture.execute(
        "rustc-proof-failed-export",
        tools
            .command()
            .arg("--artifacts")
            .arg(&fail_artifacts)
            .arg("--export-lean-lib")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args(["--crate-name", "scalar", "--select", "zero", "--source-file"])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!("Contract={}", runfiles.join("Contract.lean").display()))
            .arg("--proof-file")
            .arg(format!("Proof={}", bad_link.display()))
            .args(["--spec-decl", "Contract:Contract.specs"]),
    );
    failed.expect(1, "proof_failed", Some("audit"));
    assert!(fail_artifacts.join("lean-lib/Captured.olean").is_file());
    assert!(fail_artifacts.join("lean-lib/Contract.olean").is_file());
    assert!(
        !fail_artifacts.join("lean-lib/Proof.olean").exists(),
        "authored proof-role .olean must not be exported on proof_failed"
    );

    // 4. Early header error before target-lib exists does not fail with ENOENT.
    let header_err_link = runfiles.join("BadImportProof.lean");
    fs::write(cas.join("bad_import.lean"), lean_source("import MissingModule", "def x := 1"))
        .unwrap();
    symlink(cas.join("bad_import.lean"), &header_err_link).unwrap();
    let early_artifacts = fixture.path("rustc-early-fail");
    let early = fixture.execute(
        "rustc-early-fail-export",
        tools
            .command()
            .arg("--artifacts")
            .arg(&early_artifacts)
            .arg("--export-lean-lib")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args(["--crate-name", "scalar", "--select", "zero", "--source-file"])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!("Contract={}", runfiles.join("Contract.lean").display()))
            .arg("--proof-file")
            .arg(format!("Proof={}", header_err_link.display()))
            .args(["--spec-decl", "Contract:Contract.specs"]),
    );
    early.expect(1, "proof_failed", Some("audit"));
    assert!(!early_artifacts.join("lean-lib").exists());

    // 5. Unpinned Lean runtime taint receipt + stderr warning banner.
    let unpinned = fixture.execute(
        "unpinned-lean-selected",
        tools
            .command()
            .arg("--allow-unpinned-lean")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args(["--crate-name", "scalar", "--select", "zero", "--source-file"])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!("Contract={}", runfiles.join("Contract.lean").display()))
            .arg("--proof-file")
            .arg(format!("Spec.Helper={}", runfiles.join("Spec.Helper.lean").display()))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    unpinned.expect(0, "tainted_selected_unit_verified", None);
    assert!(
        String::from_utf8_lossy(&unpinned.output.stderr).contains("TAINTED"),
        "expected TAINTED banner on stderr"
    );
    assert_eq!(unpinned.value["taint_reasons"], json!(["unpinned_lean"]));
    assert_eq!(unpinned.value["correspondence_provenance"]["applicable"], json!(false));
    assert_eq!(unpinned.value["toolchain_identity"]["sha256_locked"], json!([]));
    assert!(
        unpinned.value["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|a| a == "faithful pinned compiler capture")
    );
    let u = &unpinned.value["unpinned_lean"];
    assert_eq!(u["expected_toolchain"], "leanprover/lean4:v4.34.1");
    assert_eq!(u["lean_binary_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(u["sysroot_modules_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(u["foundation_modules"].as_array().unwrap().len(), 6);
    assert!(u["admitted_sysroot_module_count"].as_u64().unwrap() >= 6);
    assert_eq!(
        u["sysroot_modules_sha256"],
        unpinned.value["audit"]["unpinnedLean"]["sysrootModulesSha256"]
    );

    // 6. Unsandboxed elaboration taint receipt + stderr warning banner.
    let unsandboxed = fixture.execute(
        "unsandboxed-elaboration-selected",
        tools
            .command()
            .arg("--allow-unsandboxed-elaboration")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args([
                "--crate-name",
                "scalar",
                "--select",
                "zero",
                "--source-file",
            ])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!(
                "Contract={}",
                runfiles.join("Contract.lean").display()
            ))
            .arg("--proof-file")
            .arg(format!(
                "Spec.Helper={}",
                runfiles.join("Spec.Helper.lean").display()
            ))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    unsandboxed.expect(0, "tainted_selected_unit_verified", None);
    assert!(
        String::from_utf8_lossy(&unsandboxed.output.stderr).contains("TAINTED"),
        "expected TAINTED banner on stderr"
    );
    assert_eq!(
        unsandboxed.value["taint_reasons"],
        json!(["unsandboxed_elaboration"])
    );
    assert_eq!(unsandboxed.value["elaboration_sandbox"], json!("none"));
    assert!(
        unsandboxed.value["deferred"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d
                .as_str()
                .is_some_and(|s| s.contains("hostile Lean elaborator"))),
        "unsandboxed run must keep hostile Lean elaborator effects in deferred: {}",
        unsandboxed.value["deferred"]
    );
    assert!(
        unsandboxed.value.get("sorry_declarations").is_none(),
        "sorry_declarations must be omitted without --allow-sorry-in-proof: {}",
        unsandboxed.value
    );

    // 7. Clean proof with `--allow-sorry-in-proof` still taints the receipt
    //    (Uniform Flag-Driven Taint Law) and emits `sorry_declarations: []`.
    let clean_allow_sorry = fixture.execute(
        "allow-sorry-clean-proof",
        tools
            .command()
            .arg("--allow-sorry-in-proof")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args([
                "--crate-name",
                "scalar",
                "--select",
                "zero",
                "--source-file",
            ])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!(
                "Contract={}",
                runfiles.join("Contract.lean").display()
            ))
            .arg("--proof-file")
            .arg(format!(
                "Spec.Helper={}",
                runfiles.join("Spec.Helper.lean").display()
            ))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    clean_allow_sorry.expect(0, "tainted_selected_unit_verified", None);
    assert!(
        String::from_utf8_lossy(&clean_allow_sorry.output.stderr).contains("TAINTED"),
        "expected TAINTED banner on stderr"
    );
    assert_eq!(
        clean_allow_sorry.value["taint_reasons"],
        json!(["sorry_in_proof"])
    );
    assert_eq!(clean_allow_sorry.value["sorry_declarations"], json!([]));
    assert!(matches!(
        clean_allow_sorry.value["elaboration_sandbox"].as_str(),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    ));

    // 8. Proof with `sorry`: rejected without `--allow-sorry-in-proof` (with
    //    `elaboration_sandbox` populated on the post-sandbox `FailureReceipt`),
    //    admitted with `--allow-sorry-in-proof` recording `sorry_declarations`,
    //    and combined with all 3 relaxation flags in canonical sorted order.
    let sorry_proof = runfiles.join("SorryProof.lean");
    fs::write(
        &sorry_proof,
        "prelude\n\
         import Expected\n\
         namespace Spec.Helper\n\
         theorem lemma_hole : Expected.claim := sorry\n\
         theorem custom_verify : Expected.claim := lemma_hole\n\
         end Spec.Helper\n",
    )
    .unwrap();
    let strict_sorry = fixture.execute(
        "sorry-proof-strict-rejected",
        tools
            .command()
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args([
                "--crate-name",
                "scalar",
                "--select",
                "zero",
                "--source-file",
            ])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!(
                "Contract={}",
                runfiles.join("Contract.lean").display()
            ))
            .arg("--proof-file")
            .arg(format!("Spec.Helper={}", sorry_proof.display()))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    strict_sorry.expect(1, "proof_failed", Some("audit"));
    strict_sorry.expect_detail("unapproved axiom sorryAx");
    assert_eq!(strict_sorry.value["taint_reasons"], json!([]));
    assert!(
        matches!(
            strict_sorry.value["elaboration_sandbox"].as_str(),
            Some("linux_bwrap" | "linux_landlock_seccomp")
        ),
        "post-sandbox failure receipt must record elaboration_sandbox: {}",
        strict_sorry.value
    );

    let sandboxed_sorry = fixture.execute(
        "sorry-proof-sandboxed-allow-sorry",
        tools
            .command()
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args([
                "--crate-name",
                "scalar",
                "--select",
                "zero",
                "--source-file",
            ])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!(
                "Contract={}",
                runfiles.join("Contract.lean").display()
            ))
            .arg("--proof-file")
            .arg(format!("Spec.Helper={}", sorry_proof.display()))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
                "--allow-sorry-in-proof",
            ]),
    );
    sandboxed_sorry.expect(0, "tainted_selected_unit_verified", None);
    assert!(
        String::from_utf8_lossy(&sandboxed_sorry.output.stderr).contains("TAINTED"),
        "expected TAINTED banner on stderr"
    );
    assert_eq!(
        sandboxed_sorry.value["taint_reasons"],
        json!(["sorry_in_proof"])
    );
    assert_eq!(
        sandboxed_sorry.value["sorry_declarations"],
        json!(["Spec.Helper.lemma_hole"])
    );
    assert!(
        matches!(
            sandboxed_sorry.value["elaboration_sandbox"].as_str(),
            Some("linux_bwrap" | "linux_landlock_seccomp")
        ),
        "{}",
        sandboxed_sorry.value
    );

    let all_three_taints = fixture.execute(
        "sorry-proof-all-three-taints",
        tools
            .command()
            .args([
                "--allow-unsandboxed-elaboration",
                "--allow-unpinned-lean",
                "--allow-sorry-in-proof",
            ])
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args([
                "--crate-name",
                "scalar",
                "--select",
                "zero",
                "--source-file",
            ])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!(
                "Contract={}",
                runfiles.join("Contract.lean").display()
            ))
            .arg("--proof-file")
            .arg(format!("Spec.Helper={}", sorry_proof.display()))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    all_three_taints.expect(0, "tainted_selected_unit_verified", None);
    assert_eq!(
        all_three_taints.value["taint_reasons"],
        json!(["sorry_in_proof", "unpinned_lean", "unsandboxed_elaboration"])
    );
    assert_eq!(all_three_taints.value["elaboration_sandbox"], json!("none"));
    assert_eq!(
        all_three_taints.value["sorry_declarations"],
        json!(["Spec.Helper.lemma_hole"])
    );
    assert!(all_three_taints.value.get("unpinned_lean").is_some());
    assert!(
        all_three_taints.value["deferred"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d
                .as_str()
                .is_some_and(|s| s.contains("hostile Lean elaborator"))),
        "{}",
        all_three_taints.value
    );

    // 9. Specification `sorry` is STILL rejected even with
    //    `--allow-sorry-in-proof`, and the failure receipt records both
    //    `taint_reasons: ["sorry_in_proof"]` and `elaboration_sandbox`.
    let sorry_spec = runfiles.join("SorryContract.lean");
    fs::write(
        &sorry_spec,
        "prelude\n\
         import Trusted.MirSemantics\n\
         namespace Contract\n\
         theorem bad_spec_hole : True := sorry\n\
         def specs (_ : Trusted.MirSemantics.Program) : Prop := True\n\
         end Contract\n",
    )
    .unwrap();
    let spec_sorry_rejected = fixture.execute(
        "sorry-spec-rejected-even-with-allow-sorry",
        tools
            .command()
            .arg("--allow-sorry-in-proof")
            .arg("rustc")
            .arg(runfiles.join("lib.rs"))
            .args([
                "--crate-name",
                "scalar",
                "--select",
                "zero",
                "--source-file",
            ])
            .arg(runfiles.join("helper.rs"))
            .arg("--spec-file")
            .arg(format!("Contract={}", sorry_spec.display()))
            .arg("--proof-file")
            .arg(format!("Spec.Helper={}", sorry_proof.display()))
            .args([
                "--spec-decl",
                "Contract:Contract.specs",
                "--theorem",
                "Spec.Helper:Spec.Helper.custom_verify",
            ]),
    );
    spec_sorry_rejected.expect(1, "proof_failed", Some("audit"));
    spec_sorry_rejected.expect_detail("Lean.Parser.Term.sorry");
    assert_eq!(
        spec_sorry_rejected.value["taint_reasons"],
        json!(["sorry_in_proof"])
    );
    assert!(
        matches!(
            spec_sorry_rejected.value["elaboration_sandbox"].as_str(),
            Some("linux_bwrap" | "linux_landlock_seccomp")
        ),
        "{}",
        spec_sorry_rejected.value
    );
}

#[test]
fn balances_large_captured_lists_through_lean_and_target_audit() {
    use std::fmt::Write as _;

    use cargo_anneal::{
        Checker, TargetAuditRequest, TargetBindings, TargetModule, TargetRole, sha256_bytes,
    };

    let tools = Tools::discover();
    let fixture = Fixture::new();

    // Assemble the shared trusted `MirAst` bundle plus a minimal test-local
    // `Trusted.MirSemantics` `UnitTheorem` model (`bodies.length = expected`)
    // so this test isolates `Captured.lean` + `Trusted.MirAst` elaboration and
    // kernel replay (full `Trusted.MirSemantics.CrateTheorem` on 70+ bodies
    // hits Lean's `maxRecDepth` inside `bodiesHaveUniqueIdentities`, which is
    // an orthogonal semantic-evaluator limit outside `lean.rs`).
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let bundle_root = fixture.path("bundle");
    for rel in [
        "trusted/audit/TrustedBoundary.lean",
        "trusted/audit/library-lock.json",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
        "trusted/lean/Trusted.lean",
    ] {
        let dest = bundle_root.join(rel);
        fs::create_dir_all(dest.parent().unwrap()).unwrap();
        fs::copy(repo_root.join(rel), dest).unwrap();
    }

    let mut base_modules = Vec::new();
    for (module, rel) in [
        ("Trusted.MirAst.Types", "trusted/lean/Trusted/MirAst/Types.lean"),
        ("Trusted.MirAst.Places", "trusted/lean/Trusted/MirAst/Places.lean"),
        ("Trusted.MirAst.Rvalues", "trusted/lean/Trusted/MirAst/Rvalues.lean"),
        ("Trusted.MirAst.Statements", "trusted/lean/Trusted/MirAst/Statements.lean"),
        ("Trusted.MirAst.Terminators", "trusted/lean/Trusted/MirAst/Terminators.lean"),
        ("Trusted.MirAst.Body", "trusted/lean/Trusted/MirAst/Body.lean"),
        ("Trusted.MirAst", "trusted/lean/Trusted/MirAst.lean"),
    ] {
        let src = repo_root.join(rel);
        let bytes = fs::read(&src).unwrap();
        base_modules.push(TargetModule {
            module: module.to_owned(),
            source: src,
            expected_sha256: sha256_bytes(&bytes),
            role: TargetRole::Model,
        });
    }

    let run_capture_and_audit = |tag: &str, rust_src: &str, expected_bodies: usize| {
        let crate_root = fixture.path(&format!("{tag}/lib.rs"));
        fs::create_dir_all(crate_root.parent().unwrap()).unwrap();
        fs::write(&crate_root, rust_src).unwrap();

        let capture_out = fixture.path(&format!("{tag}-capture"));
        let capture_out_status = Command::new(&tools.capture)
            .arg("capture")
            .arg("--crate-root")
            .arg(&crate_root)
            .arg(format!("--crate-name=large_{tag}"))
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&capture_out)
            .arg("--source-file")
            .arg(&crate_root)
            .arg("--scope=crate")
            .arg("--sysroot")
            .arg(&tools.sysroot)
            .env("LD_LIBRARY_PATH", tools.sysroot.join("lib"))
            .output()
            .expect("run anneal-rustc-capture on large crate");
        assert!(
            capture_out_status.status.success(),
            "capture ({tag}) failed: {}\n{}",
            String::from_utf8_lossy(&capture_out_status.stdout),
            String::from_utf8_lossy(&capture_out_status.stderr)
        );

        let capture_manifest: Value =
            serde_json::from_slice(&fs::read(capture_out.join("capture.json")).unwrap()).unwrap();
        let captured_path = capture_out.join("Captured.lean");
        let captured_lean = fs::read_to_string(&captured_path).unwrap();
        assert!(
            captured_lean.contains("(_root_.List.append "),
            "expected balanced _root_.List.append chunks in {tag} Captured.lean"
        );

        let target_dir = fixture.path(&format!("{tag}-lean"));
        fs::create_dir_all(&target_dir).unwrap();
        let make_lean = |name: &str, role: TargetRole, imports: &str, body: &str| {
            let path = target_dir.join(format!("{name}.lean"));
            let contents = lean_source(imports, body);
            fs::write(&path, contents.as_bytes()).unwrap();
            TargetModule {
                module: name.to_owned(),
                source: path,
                expected_sha256: sha256_bytes(contents.as_bytes()),
                role,
            }
        };

        let mut modules = base_modules.clone();
        modules.push(make_lean(
            "Trusted.MirSemantics",
            TargetRole::Model,
            "import Trusted.MirAst",
            &format!(
                "namespace Trusted.MirSemantics\n\n\
                 structure Crate where\n  \
                   program : Trusted.MirAst.Program\n  \
                   specs : Trusted.MirAst.Program → Prop\n\n\
                 def UnitTheorem (c : Crate) : Prop :=\n  \
                   c.program.bodies.length = {expected_bodies} ∧ c.specs c.program\n\n\
                 end Trusted.MirSemantics"
            ),
        ));
        modules.push(TargetModule {
            module: "Captured".to_owned(),
            expected_sha256: sha256_bytes(captured_lean.as_bytes()),
            source: captured_path,
            role: TargetRole::Capture,
        });
        modules.push(make_lean(
            "Spec",
            TargetRole::Specification,
            "import Trusted.MirAst",
            &format!(
                "namespace Spec\n\
                 def specs (p : Trusted.MirAst.Program) : Prop :=\n  \
                   p.bodies.length = {expected_bodies}\n\
                 end Spec"
            ),
        ));
        modules.push(make_lean(
            "Expected",
            TargetRole::Expected,
            "import Trusted.MirSemantics\nimport Captured\nimport Spec",
            "namespace Expected\n\
             def claim : Prop := Trusted.MirSemantics.UnitTheorem \
               (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
             end Expected",
        ));
        modules.push(make_lean(
            "Proof",
            TargetRole::Proof,
            "import Expected",
            &format!(
                "namespace Proof\n\
                 theorem bodies_len : Captured.program.bodies.length = {expected_bodies} := rfl\n\
                 theorem verify : Expected.claim := ⟨bodies_len, bodies_len⟩\n\
                 end Proof"
            ),
        ));

        let h = sha256_bytes(format!("large-capture-binding-{tag}").as_bytes());
        let request = TargetAuditRequest {
            modules,
            theorem_module: "Proof".to_owned(),
            theorem_name: "Proof.verify".to_owned(),
            expected_module: "Expected".to_owned(),
            expected_declaration: "Expected.claim".to_owned(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
            subject_declaration: "Captured.program".to_owned(),
            specification_declaration: "Spec.specs".to_owned(),
            bindings: TargetBindings {
                request_sha256: h.clone(),
                capture_sha256: h.clone(),
                model_manifest_sha256: h.clone(),
                specification_manifest_sha256: h,
            },
            allow_sorry_in_proof: false,
        };

        let mut checker = Checker::new(&bundle_root, Some(&tools.lean)).unwrap();
        let report = checker
            .run_target(&request)
            .unwrap_or_else(|e| panic!("target audit failed for {tag}: {e}"));
        assert_eq!(report["replay"], json!(true), "{report}");
        assert_eq!(report["exactType"], json!(true), "{report}");
        assert_eq!(report["theorem"], json!("Proof.verify"), "{report}");
        (capture_manifest, captured_lean)
    };

    // 1. Multi-body crate exercising chunking across bodies, locals, statements,
    // switch targets, enum discriminants, and >= 100-char identities.
    let mut rust_src = String::new();
    for i in 0..69 {
        let _ = writeln!(&mut rust_src, "pub fn fn_{i:02}() -> u64 {{ 0 }}");
    }
    rust_src.push_str("pub enum LargeEnum {\n");
    for i in 0..70 {
        let _ = writeln!(&mut rust_src, "    V{i},");
    }
    rust_src.push_str("}\n");
    let long_mod = format!("m_{}", "x".repeat(75));
    let _ = writeln!(&mut rust_src, "pub mod {long_mod} {{");
    rust_src.push_str("    pub fn long_fn(e: crate::LargeEnum) -> u64 {\n");
    for i in 0..85 {
        let _ = writeln!(&mut rust_src, "        let _v_{i}: u64 = 0;");
    }
    rust_src.push_str("        match e {\n");
    for i in 0..70 {
        let _ = writeln!(&mut rust_src, "            crate::LargeEnum::V{i} => {},", i + 1);
    }
    rust_src.push_str("        }\n    }\n}\n");

    let (capture_manifest, _) = run_capture_and_audit("bodies", &rust_src, 70);
    let bodies = capture_manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 70);
    assert!(
        bodies.iter().any(|b| b["identity"].as_str().unwrap().len() >= 100),
        "expected >= 100-char function identity"
    );
    assert!(
        bodies.iter().any(|b| {
            b["blocks"]
                .as_array()
                .unwrap()
                .iter()
                .map(|blk| blk["statements"].as_array().unwrap().len())
                .sum::<usize>()
                >= 250
        }),
        "expected >= 250 MIR statements in captured body"
    );

    // 2. 1970-variant enum (`discriminants : List Nat`): unchunked `[...]`
    // triggers Lean 4.34.1 `maximum recursion depth has been reached` in
    // `Captured.lean` elaboration, whereas balanced chunking succeeds.
    let mut wide_enum_src = String::from("pub enum WideEnum {\n");
    for i in 0..1970 {
        let _ = writeln!(&mut wide_enum_src, "    V{i},");
    }
    wide_enum_src.push_str("}\npub fn use_wide(_: WideEnum) -> u64 { 0 }\n");
    run_capture_and_audit("wide_enum", &wide_enum_src, 1);
}
