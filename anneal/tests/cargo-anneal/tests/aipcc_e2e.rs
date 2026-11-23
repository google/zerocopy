// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end verification regressions for bundled `Anneal.AiPcc`.
//!
//! Exercises real `cargo-anneal verify` with `anneal-rustc-capture` and the
//! pinned Lean toolchain proving:
//! 1. Verbatim `zerocopy/src/` `<usize as PointerMetadata>::from_elem_count`
//!    and `<usize as PointerMetadata>::to_elem_count` using bundled
//!    `import Anneal.AiPcc.MirPcc`
//!    (`AutoProve.bodyVerified_of_autoVerifyAcyclic`) with zero manual WP
//!    stepping, emitting an untainted Receipt v3.
//! 2. A real signed-integer (`i8`, `i32`, `isize`) crate covering signed
//!    comparisons, arithmetic, unary negation/not, bitwise ops, shifts, and
//!    signed-to-unsigned casts using bundled `import Anneal.AiPcc.MirPcc`
//!    with zero manual WP stepping, emitting an untainted Receipt v3.

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use serde_json::{json, Value};
use tempfile::TempDir;

const ZEROCOPY_SOURCE_FILES: &[&str] = &[
    "byte_slice.rs",
    "byteorder.rs",
    "deprecated.rs",
    "error.rs",
    "impls.rs",
    "layout.rs",
    "lib.rs",
    "macros.rs",
    "pointer/inner.rs",
    "pointer/invariant.rs",
    "pointer/mod.rs",
    "pointer/ptr.rs",
    "pointer/transmute.rs",
    "ref.rs",
    "split_at.rs",
    "util/macro_util.rs",
    "util/macros.rs",
    "util/mod.rs",
    "wrappers.rs",
];

const AIPCC_SPEC: &str = r#"module
prelude
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirSemantics

def specs : Specs :=
  { safety := fun _ _ => True
    property := fun _ => True }

end Spec

end
"#;

const AIPCC_TWO_BODY_PROOF: &str = r#"module
prelude
public import Expected
import Anneal.AiPcc.MirPcc

namespace Proof

open Trusted.MirSemantics Anneal.MirWp Anneal.AiPcc

private theorem body0_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl rfl rfl

private theorem body1_verified :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl rfl rfl

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, True.intro⟩
  have hAll : BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
    ⟨body0_verified, body1_verified, True.intro⟩
  intro defId body found
  have hSub := bodiesVerified_getElem hAll defId body found
  rw [Nat.zero_add] at hSub
  exact hSub

end Proof
"#;

const SIGNED_CRATE_LIB: &str = r#"#![no_std]

pub fn signed_branch_arith(x: i32) -> i32 {
    if x >= -100 {
        if x <= 100 {
            let y = (x + 10) - 5;
            let z = (y ^ !x) * 3;
            -z
        } else {
            100
        }
    } else {
        -100
    }
}

pub fn signed_isize_casts(x: isize, y: i8) -> usize {
    let shifted = (x << (y & 7)) >> 1;
    ((shifted + 1) as usize) ^ ((y as isize) as usize)
}
"#;

struct Tools {
    cli: PathBuf,
    capture: PathBuf,
    lean: PathBuf,
    sysroot: PathBuf,
}

impl Tools {
    fn discover() -> Self {
        let install_root = override_path("ANNEAL_TEST_INSTALL_ROOT");
        let cli = first_override(&["ANNEAL_CLI"])
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_CLI");
        let capture = first_override(&["ANNEAL_CAPTURE"])
            .or_else(|| {
                ["anneal-rustc-capture", "anneal-rustc-capture-test-bin"]
                    .into_iter()
                    .map(|name| cli.with_file_name(name))
                    .find(|sibling| sibling.is_file())
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
        Self { cli, capture, lean, sysroot }
    }

    fn verify_command(&self) -> Command {
        let mut command = Command::new(&self.cli);
        command
            .arg("verify")
            .args(["--format", "json"])
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
    names.iter().find_map(|name| override_path(name))
}

fn required_file(path: PathBuf, what: &str, variable: &str) -> PathBuf {
    assert!(path.is_file(), "missing {what} at {}; set {variable}", path.display());
    fs::canonicalize(path).expect("resolve test tool path")
}

fn run_request(tools: &Tools, dir: &Path, name: &str, request: &Value) -> (Value, Output) {
    let req_path = dir.join(format!("{name}.json"));
    fs::write(&req_path, serde_json::to_vec_pretty(request).unwrap()).unwrap();
    let artifacts = dir.join(format!("artifacts-{name}"));
    let output = tools
        .verify_command()
        .current_dir(dir)
        .arg("--request")
        .arg(&req_path)
        .arg("--artifacts")
        .arg(&artifacts)
        .output()
        .unwrap_or_else(|e| panic!("failed to run {name}: {e}"));
    let value = serde_json::from_slice(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "{name} did not emit JSON receipt: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (value, output)
}

fn assert_untainted_receipt(name: &str, value: &Value, output: &Output, expected_status: &str) {
    assert_eq!(
        output.status.code(),
        Some(0),
        "{name} failed unexpectedly:\n{value}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(value["schema_version"], 3, "{name}: {value}");
    assert!(value.get("tainted").is_none(), "{name}: {value}");
    if let Some(reasons) = value.get("taint_reasons") {
        assert_eq!(reasons, &json!([]), "{name}: {value}");
    }
    assert_eq!(value["status"], expected_status, "{name}: {value}");
    assert_eq!(value["audit"]["exactType"], true, "{name}: {value}");
    assert_eq!(value["audit"]["replay"], true, "{name}: {value}");
    let axioms = value["audit"]["axioms"]
        .as_array()
        .unwrap_or_else(|| panic!("{name}: missing axioms array: {value}"));
    for ax in axioms {
        let ax_str = ax.as_str().unwrap_or_default();
        assert!(
            matches!(ax_str, "propext" | "Classical.choice" | "Quot.sound"),
            "{name}: unexpected axiom {ax_str:?} in {value}"
        );
    }
}

/// Proves verbatim `zerocopy/src/` `<usize as PointerMetadata>` elem-count
/// helpers via bundled `Anneal.AiPcc.MirPcc` with zero manual WP stepping.
#[test]
fn verifies_verbatim_zerocopy_usize_metadata_via_bundled_aipcc() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(lean_dir.join("Spec.lean"), AIPCC_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), AIPCC_TWO_BODY_PROOF).unwrap();

    let zc_src =
        fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../zerocopy/src"))
            .expect("locate unmodified zerocopy/src");
    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": zc_src.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "zerocopy",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": ["no_zerocopy_allocator_api_1_100_0"],
            "env": {"CARGO_PKG_VERSION": "0.8.64"},
            "source_files": ZEROCOPY_SOURCE_FILES
        },
        "scope": {
            "kind": "selected_unit",
            "roots": [
                "<usize as PointerMetadata>::from_elem_count",
                "<usize as PointerMetadata>::to_elem_count"
            ]
        },
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let (value, output) = run_request(&tools, dir.path(), "zerocopy-aipcc-ok", &request);
    assert_untainted_receipt("zerocopy-aipcc-ok", &value, &output, "selected_unit_verified");
}

/// Proves a signed-integer (`i8`, `i32`, `isize`) crate end-to-end via bundled
/// `Anneal.AiPcc.MirPcc` with zero manual WP stepping.
#[test]
fn verifies_signed_integer_crate_via_bundled_aipcc() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(rust_dir.join("lib.rs"), SIGNED_CRATE_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), AIPCC_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), AIPCC_TWO_BODY_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "signed_aipcc_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let (value, output) = run_request(&tools, dir.path(), "signed-aipcc-ok", &request);
    assert_untainted_receipt("signed-aipcc-ok", &value, &output, "crate_verified");
}
