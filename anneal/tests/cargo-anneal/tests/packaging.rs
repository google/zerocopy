// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end tests for Cargo split-plane packaging (`package-check`,
//! `--unit`/`--slice`, Receipt v3 digests, and digest-pinned setup).

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use cargo_anneal::{
    packaging::{
        EvidenceVerifyOptions, inspect_contract_plane, validate_crate_cargo_toml,
        verify_evidence_carrier_dir,
    },
    sha256_bytes,
};
use serde_json::{Value, json};
use tempfile::TempDir;

const SPEC: &str = include_str!("../../../trusted/cargo-anneal/assets/scalar/Spec.lean");
const PROOF: &str = include_str!("../../../trusted/cargo-anneal/assets/scalar/Proof.lean");

fn cli_bin() -> PathBuf {
    if let Some(path) = std::env::var_os("ANNEAL_CLI").filter(|v| !v.is_empty()) {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))
}

fn discover_live_tools() -> Option<(PathBuf, PathBuf, PathBuf, PathBuf)> {
    let cli = cli_bin();
    let capture = std::env::var_os("ANNEAL_CAPTURE")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
        ["anneal-rustc-capture", "anneal-rustc-capture-test-bin"]
            .into_iter()
            .map(|name| cli.with_file_name(name))
            .find(|p| p.is_file())
    })?;
    let lean = std::env::var_os("ANNEAL_LEAN")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(cargo_anneal::default_lean_path);
    if !lean.is_file() {
        return None;
    }
    let sysroot = std::env::var_os("ANNEAL_SYSROOT")
        .or_else(|| std::env::var_os("ANNEAL_TEST_RUST_SYSROOT"))
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            let out = Command::new("rustup")
                .args(["run", "nightly-2026-05-31", "rustc", "--print", "sysroot"])
                .output()
                .ok()?;
            if !out.status.success() {
                return None;
            }
            Some(PathBuf::from(String::from_utf8(out.stdout).ok()?.trim()))
        })?;
    if !sysroot.join("lib").is_dir() {
        return None;
    }
    Some((cli, capture, lean, fs::canonicalize(sysroot).ok()?))
}

fn write_split_plane_crate(dir: &Path, exclude_proofs: bool) {
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::create_dir_all(dir.join("anneal/specs")).unwrap();
    fs::create_dir_all(dir.join("proofs/01_zero")).unwrap();
    let exclude_line = if exclude_proofs { "exclude = [\".*\", \"/proofs\"]\n" } else { "" };
    fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\n\
             name = \"demo-pkg\"\n\
             version = \"0.1.0\"\n\
             edition = \"2021\"\n\
             license = \"MIT\"\n\
             description = \"split plane fixture\"\n\
             rust-version = \"1.56.0\"\n\
             {exclude_line}\n\
             [package.metadata.anneal]\n\
             manifest = \"anneal/anneal.toml\"\n\
             evidence_crate = \"demo-pkg-anneal-proofs\"\n\
             \n\
             [lints.rust]\n\
             unexpected_cfgs = {{ level = \"warn\", check-cfg = [\"cfg(anneal)\"] }}\n"
        ),
    )
    .unwrap();
    // `cfg(anneal)` is declared through `[lints.rust]` rather than a build
    // script: `cargo anneal verify` refuses build scripts it cannot model.
    fs::write(
        dir.join("src/lib.rs"),
        "#[cfg_attr(anneal, doc = \"zero spec\")]\npub fn zero() -> u64 { 0 }\n",
    )
    .unwrap();
    fs::write(
        dir.join("anneal/anneal.toml"),
        "schema_version = 1\n\
         \n\
         [package]\n\
         spec_format = \"anneal-lean-v1\"\n\
         lean_compat = \">=4.34.1, <4.36.0\"\n\
         mir_model_schema = 1\n\
         \n\
         [evidence]\n\
         carrier_crate = \"demo-pkg-anneal-proofs\"\n\
         \n\
         [slices.default]\n\
         target = \"x86_64-unknown-linux-gnu\"\n\
         default_features = false\n\
         features = []\n\
         panic = \"unwind\"\n\
         \n\
         [[units]]\n\
         id = \"01_zero\"\n\
         scope = { kind = \"selected_unit\", roots = [\"zero\"] }\n\
         specification = \"Spec.specs\"\n\
         spec_modules = [{ module = \"Spec\", path = \"specs/Spec.lean\" }]\n",
    )
    .unwrap();
    fs::write(dir.join("anneal/specs/Spec.lean"), SPEC).unwrap();
    fs::write(dir.join("proofs/01_zero/Proof.lean"), PROOF).unwrap();
}

#[test]
fn package_check_validates_msrv_crate_and_cargo_package_roundtrip() {
    let tmp = TempDir::new().unwrap();
    write_split_plane_crate(tmp.path(), true);

    let out = Command::new(cli_bin())
        .args(["package-check", "--manifest-path"])
        .arg(tmp.path().join("Cargo.toml"))
        .arg("--run-cargo-package")
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "package-check failed:\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(report["status"], "package_ok");
    assert_eq!(report["crate_name"], "demo-pkg");
    assert_eq!(report["rust_version"], "1.56.0");
    assert!(report["packaged_crate_compressed_bytes"].as_u64().unwrap() > 0);
    assert!(report["plane1_bytes"].as_u64().unwrap() < 64 * 1024);
}

#[test]
fn package_check_rejects_proof_leak_into_crate_tarball() {
    let tmp = TempDir::new().unwrap();
    write_split_plane_crate(tmp.path(), false);

    let out = Command::new(cli_bin())
        .args(["package-check", "--manifest-path"])
        .arg(tmp.path().join("Cargo.toml"))
        .arg("--run-cargo-package")
        .output()
        .unwrap();
    assert!(!out.status.success());
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(report["status"], "package_rejected");
    assert!(
        report["detail"].as_str().unwrap().contains("E_ANNEAL_PROOF_IN_CONTRACT_PLANE"),
        "{report}"
    );
}

#[test]
fn live_verify_unit_and_evidence_carrier_roundtrip_and_tamper_detection() {
    let Some((cli, capture, lean, sysroot)) = discover_live_tools() else {
        panic!("live verification tools not available; build anneal-rustc-capture first");
    };
    let tmp = TempDir::new().unwrap();
    let crate_dir = tmp.path().join("crate");
    write_split_plane_crate(&crate_dir, true);

    let pkg_out = Command::new(&cli)
        .args(["package-check", "--manifest-path"])
        .arg(crate_dir.join("Cargo.toml"))
        .output()
        .unwrap();
    assert!(pkg_out.status.success(), "{}", String::from_utf8_lossy(&pkg_out.stdout));
    let pkg_report: Value = serde_json::from_slice(&pkg_out.stdout).unwrap();

    let out = Command::new(&cli)
        .args(["verify", "--capture"])
        .arg(&capture)
        .arg("--lean")
        .arg(&lean)
        .arg("--sysroot")
        .arg(&sysroot)
        .arg("--manifest-path")
        .arg(crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(crate_dir.join("proofs/01_zero"))
        .args(["--unit", "01_zero", "--slice", "default"])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "verify --unit failed:\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let receipt: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(receipt["status"], "selected_unit_verified");
    assert_eq!(
        receipt["source_closure_sha256"], pkg_report["source_closure_sha256"],
        "verify receipt must match package-check source_closure_sha256"
    );
    let canonical_prog_sha = receipt["canonical_program_sha256"].as_str().unwrap().to_owned();
    let sem_profile = receipt["semantic_profile"].clone();

    // Assemble a Plane 2 `<crate>-anneal-proofs` directory and verify via CLI.
    let ev_dir = tmp.path().join("demo-pkg-anneal-proofs");
    fs::create_dir_all(ev_dir.join("proofs/01_zero")).unwrap();
    fs::create_dir_all(ev_dir.join("receipts/default")).unwrap();
    fs::write(ev_dir.join("proofs/01_zero/Proof.lean"), PROOF).unwrap();
    let receipt_bytes = out.stdout;
    fs::write(ev_dir.join("receipts/default/01_zero.receipt.json"), &receipt_bytes).unwrap();

    let evidence_manifest = json!({
        "schema_version": 1,
        "subject": {
            "crate_name": "demo-pkg",
            "crate_version": "0.1.0",
            "source_closure_sha256": pkg_report["source_closure_sha256"],
            "specification_manifest_sha256": pkg_report["specification_manifest_sha256"],
            "anneal_toml_sha256": pkg_report["anneal_toml_sha256"],
        },
        "proof_units": {
            "01_zero": {
                "theorem": "Proof.verify",
                "shard_mode": "none",
                "proof_sources": [{
                    "module": "Proof",
                    "path": "proofs/01_zero/Proof.lean",
                    "sha256": sha256_bytes(PROOF.as_bytes()),
                }],
            }
        },
        "slices": {
            "default": {
                "semantic_profile": sem_profile,
                "rustc_commit_sha": "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
                "lean_toolchain": "leanprover/lean4:v4.34.1",
                "units": {
                    "01_zero": {
                        "canonical_program_sha256": canonical_prog_sha,
                        "receipt_path": "receipts/default/01_zero.receipt.json",
                        "receipt_sha256": sha256_bytes(&receipt_bytes),
                    }
                }
            }
        }
    });
    fs::write(
        ev_dir.join("anneal-evidence.json"),
        serde_json::to_vec_pretty(&evidence_manifest).unwrap(),
    )
    .unwrap();

    let ev_check = Command::new(&cli)
        .args(["package-check", "--manifest-path"])
        .arg(crate_dir.join("Cargo.toml"))
        .arg("--evidence-dir")
        .arg(&ev_dir)
        .arg("--require-untainted")
        .output()
        .unwrap();
    assert!(
        ev_check.status.success(),
        "evidence check failed:\n{}",
        String::from_utf8_lossy(&ev_check.stdout)
    );

    // Tampering `specification_manifest_sha256` inside a Slice receipt on an
    // unchanged Rust body must fail closed.
    let mut bad_receipt = receipt.clone();
    bad_receipt["specification_manifest_sha256"] = json!("0".repeat(64));
    let bad_bytes = serde_json::to_vec_pretty(&bad_receipt).unwrap();
    fs::write(ev_dir.join("receipts/default/01_zero.receipt.json"), &bad_bytes).unwrap();
    let mut bad_manifest = evidence_manifest.clone();
    bad_manifest["slices"]["default"]["units"]["01_zero"]["receipt_sha256"] =
        json!(sha256_bytes(&bad_bytes));
    fs::write(
        ev_dir.join("anneal-evidence.json"),
        serde_json::to_vec_pretty(&bad_manifest).unwrap(),
    )
    .unwrap();
    let bad_spec_res = Command::new(&cli)
        .args(["package-check", "--manifest-path"])
        .arg(crate_dir.join("Cargo.toml"))
        .arg("--evidence-dir")
        .arg(&ev_dir)
        .output()
        .unwrap();
    assert!(!bad_spec_res.status.success());

    fs::write(ev_dir.join("receipts/default/01_zero.receipt.json"), &receipt_bytes).unwrap();
    fs::write(
        ev_dir.join("anneal-evidence.json"),
        serde_json::to_vec_pretty(&evidence_manifest).unwrap(),
    )
    .unwrap();

    // Mutating `src/lib.rs` (even with empty `.cargo-checksum.json`) fails with
    // `E_ANNEAL_SOURCE_CLOSURE_MISMATCH`.
    fs::write(crate_dir.join(".cargo-checksum.json"), "{\"files\":{}}\n").unwrap();
    fs::write(
        crate_dir.join("src/lib.rs"),
        "#[cfg_attr(anneal, doc = \"zero spec\")]\npub fn zero() -> u64 { 1 }\n",
    )
    .unwrap();
    let tampered = Command::new(&cli)
        .args(["package-check", "--manifest-path"])
        .arg(crate_dir.join("Cargo.toml"))
        .arg("--evidence-dir")
        .arg(&ev_dir)
        .output()
        .unwrap();
    assert!(!tampered.status.success());
    let tampered_json: Value = serde_json::from_slice(&tampered.stdout).unwrap();
    assert!(
        tampered_json["detail"].as_str().unwrap().contains("E_ANNEAL_SOURCE_CLOSURE_MISMATCH"),
        "{tampered_json}"
    );

    // Confirm programmatic `verify_evidence_carrier_dir` works cleanly.
    fs::write(
        crate_dir.join("src/lib.rs"),
        "#[cfg_attr(anneal, doc = \"zero spec\")]\npub fn zero() -> u64 { 0 }\n",
    )
    .unwrap();
    let pkg = validate_crate_cargo_toml(&crate_dir).unwrap();
    let closure = cargo_anneal::packaging::compute_source_closure_sha256(
        &crate_dir,
        &pkg.name,
        &pkg.edition,
        &pkg.cargo_semantics(),
        &[],
    )
    .unwrap();
    let plane1 = inspect_contract_plane(&crate_dir, &pkg.anneal_manifest_rel).unwrap();
    let (_, rep) = verify_evidence_carrier_dir(
        &crate_dir,
        &pkg,
        &closure,
        &plane1,
        &ev_dir,
        &EvidenceVerifyOptions { require_untainted: true, require_attestation: false },
    )
    .unwrap();
    assert_eq!(rep.crate_name, "demo-pkg");
}

#[test]
fn verify_unit_handles_cfg_any_and_rejects_pre160_optional_dep_feature() {
    let Some((cli, capture, lean, sysroot)) = discover_live_tools() else {
        panic!("live verification tools not available; build anneal-rustc-capture first");
    };
    let tmp = TempDir::new().unwrap();
    let crate_dir = tmp.path().join("crate");
    write_split_plane_crate(&crate_dir, true);

    // Pre-1.60 optional dep activation (`derive = ["fake-opt"]`) and
    // uninhabited `[target.'cfg(any())'.dependencies]` pin.
    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\n\
         name = \"demo-pkg\"\n\
         version = \"0.1.0\"\n\
         edition = \"2021\"\n\
         license = \"MIT\"\n\
         description = \"split plane fixture\"\n\
         rust-version = \"1.56.0\"\n\
         exclude = [\".*\", \"/proofs\"]\n\
         \n\
         [package.metadata.anneal]\n\
         manifest = \"anneal/anneal.toml\"\n\
         evidence_crate = \"demo-pkg-anneal-proofs\"\n\
         \n\
         [features]\n\
         derive = [\"fake-opt\"]\n\
         \n\
         [dependencies]\n\
         fake-opt = { version = \"=0.1.0\", path = \"fake-opt\", optional = true }\n\
         \n\
         [target.'cfg(any())'.dependencies]\n\
         fake-opt = { version = \"=0.1.0\", path = \"fake-opt\" }\n\
         \n\
         [lints.rust]\n\
         unexpected_cfgs = { level = \"warn\", check-cfg = [\"cfg(anneal)\"] }\n",
    )
    .unwrap();
    fs::create_dir_all(crate_dir.join("fake-opt/src")).unwrap();
    fs::write(
        crate_dir.join("fake-opt/Cargo.toml"),
        "[package]\nname = \"fake-opt\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    fs::write(crate_dir.join("fake-opt/src/lib.rs"), "").unwrap();

    // Update anneal.toml to add both `default` and `with_derive` slices.
    let toml_orig = fs::read_to_string(crate_dir.join("anneal/anneal.toml")).unwrap();
    fs::write(
        crate_dir.join("anneal/anneal.toml"),
        format!(
            "{toml_orig}\n\
             [slices.with_derive]\n\
             target = \"x86_64-unknown-linux-gnu\"\n\
             default_features = false\n\
             features = [\"derive\"]\n\
             panic = \"unwind\"\n"
        ),
    )
    .unwrap();

    // `default` ignores `[target.'cfg(any())'.dependencies]` and passes.
    let ok_out = Command::new(&cli)
        .args(["verify", "--capture"])
        .arg(&capture)
        .arg("--lean")
        .arg(&lean)
        .arg("--sysroot")
        .arg(&sysroot)
        .arg("--manifest-path")
        .arg(crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(crate_dir.join("proofs/01_zero"))
        .args(["--unit", "01_zero", "--slice", "default"])
        .output()
        .unwrap();
    assert!(
        ok_out.status.success(),
        "cfg(any()) dep should be ignored:\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&ok_out.stdout),
        String::from_utf8_lossy(&ok_out.stderr)
    );

    // `with_derive` must fail closed on pre-1.60 optional-dep activation.
    let rej_out = Command::new(&cli)
        .args(["verify", "--capture"])
        .arg(&capture)
        .arg("--lean")
        .arg(&lean)
        .arg("--sysroot")
        .arg(&sysroot)
        .arg("--manifest-path")
        .arg(crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(crate_dir.join("proofs/01_zero"))
        .args(["--unit", "01_zero", "--slice", "with_derive"])
        .output()
        .unwrap();
    assert!(!rej_out.status.success());
    let rej_json: Value = serde_json::from_slice(&rej_out.stdout).unwrap();
    assert!(
        rej_json["detail"].as_str().unwrap().contains("slice activates external dependency"),
        "{rej_json}"
    );
}

#[cfg(feature = "setup")]
#[test]
fn setup_expected_sha256_rejects_mismatch_before_unpack() {
    let tmp = TempDir::new().unwrap();
    let bad_archive = tmp.path().join("bad.tar.zst");
    fs::write(&bad_archive, b"corrupt non-zstd payload").unwrap();

    let out = Command::new(cli_bin())
        .env("XDG_CACHE_HOME", tmp.path().join("cache"))
        .args(["setup", "--local-archive"])
        .arg(&bad_archive)
        .args([
            "--expected-sha256",
            "0000000000000000000000000000000000000000000000000000000000000000",
            "--clear-old",
        ])
        .output()
        .unwrap();
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("SHA-256 mismatch"), "{stderr}");
}
