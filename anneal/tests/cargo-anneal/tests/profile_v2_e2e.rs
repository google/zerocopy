// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end Profile v2 (`mirProfileVersion = 2`) verification regressions.
//!
//! Exercises real `cargo-anneal verify` with `anneal-rustc-capture` and the
//! pinned Lean toolchain across:
//! 1. Verbatim `zerocopy/src/byte_slice.rs`
//!    `<&[u8] as SplitByteSlice>::split_at_unchecked` under `UnitTheoremV2`
//!    with non-vacuous `SpecsV2.safety` and functional `SpecsV2.property`.
//! 2. Raw pointer `*const u32` aligned load and `*mut u8` store updating
//!    `out.callerMem` under `CrateTheoremV2`.
//! 3. Fail-closed negative cases: proofs rejected for unsound caller
//!    preconditions (omitted `mid <= len`, missing alignment, null pointer,
//!    read-only write), and capture refusing bodies that mix reference and
//!    raw-pointer locals, which Profile v2 cannot check without an aliasing
//!    model (verbatim `<&mut [u8] as SplitByteSlice>::split_at_unchecked`,
//!    `from_raw_parts`, and a returned reference to a stack local).

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use serde_json::{Value, json};
use tempfile::TempDir;

const ZEROCOPY_SPEC: &str = include_str!("fixtures/profile_v2_zerocopy/Spec.lean");
const ZEROCOPY_PROOF: &str = include_str!("fixtures/profile_v2_zerocopy/Proof.lean");
const RAW_PTR_LIB: &str = include_str!("fixtures/profile_v2_raw_ptr/lib.rs");
const RAW_PTR_SPEC: &str = include_str!("fixtures/profile_v2_raw_ptr/Spec.lean");
const RAW_PTR_PROOF: &str = include_str!("fixtures/profile_v2_raw_ptr/Proof.lean");

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

struct Receipt {
    name: String,
    value: Value,
    output: Output,
}

impl Receipt {
    fn expect_ok(&self, status: &str) {
        assert_eq!(
            self.output.status.code(),
            Some(0),
            "{} failed unexpectedly:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.value["schema_version"], 3, "{}: {}", self.name, self.value);
        assert!(self.value.get("tainted").is_none(), "{}: {}", self.name, self.value);
        assert_eq!(self.value["status"], status, "{}: {}", self.name, self.value);
        assert_eq!(self.value["audit"]["exactType"], true, "{}: {}", self.name, self.value);
        assert_eq!(self.value["audit"]["replay"], true, "{}: {}", self.name, self.value);
        assert_eq!(
            self.value["audit"]["axioms"],
            json!(["propext"]),
            "{}: {}",
            self.name,
            self.value
        );
    }

    /// Profile v2 receipts must disclose the assumptions `ValidEntryArgsV2`
    /// and the missing aliasing model place on callers, and must not claim
    /// `lean-miri` correspondence.
    fn expect_profile_v2_assumptions(&self) {
        let semantics = self.value["assumptions"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .find(|a| a.starts_with("experimental Profile v2 MIR semantics"))
            .unwrap_or_else(|| {
                panic!("{}: missing Profile v2 assumption: {}", self.name, self.value)
            });
        for needle in [
            "no aliasing model",
            "raw-pointer arguments are assumed to carry provenance",
            "including those of unsafe functions",
            "decode to a valid value of the pointee type",
        ] {
            assert!(semantics.contains(needle), "{}: {needle:?} not in {semantics:?}", self.name);
        }
        assert_eq!(
            self.value["correspondence_provenance"]["applicable"],
            false,
            "{}: {}",
            self.name,
            self.value
        );
    }

    fn expect_proof_failed(&self) {
        assert_eq!(
            self.output.status.code(),
            Some(1),
            "{} must fail closed:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.value["schema_version"], 3, "{}: {}", self.name, self.value);
        assert_eq!(self.value["status"], "proof_failed", "{}: {}", self.name, self.value);
        assert_eq!(self.value["phase"], "audit", "{}: {}", self.name, self.value);
    }

    fn expect_capture_refused(&self, needle: &str) {
        assert_eq!(
            self.output.status.code(),
            Some(1),
            "{} must fail closed:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.value["status"], "unsupported", "{}: {}", self.name, self.value);
        assert_eq!(self.value["phase"], "capture", "{}: {}", self.name, self.value);
        let detail = self.value["detail"].as_str().unwrap_or_default();
        assert!(detail.contains(needle), "{}: {}", self.name, self.value);
    }
}

/// Capture refusal for bodies mixing reference and raw-pointer locals.
const MIXED_REFS_AND_RAW_PTRS: &str = "body mixes reference and raw-pointer locals";

fn run_request(tools: &Tools, dir: &Path, name: &str, request: &Value) -> Receipt {
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
    Receipt { name: name.to_owned(), value, output }
}

/// Verifies the unmodified `zerocopy/src/byte_slice.rs` `split_at_unchecked`
/// implementation for `&[u8]` end-to-end under `UnitTheoremV2` (`["propext"]`,
/// zero taint), confirms that omitting the `mid <= len` safety precondition is
/// rejected fail-closed, and confirms that capture refuses the `&mut [u8]`
/// implementation, which derives references from raw pointers.
#[test]
fn verifies_verbatim_zerocopy_split_at_unchecked_and_rejects_missing_bounds() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ZEROCOPY_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ZEROCOPY_PROOF).unwrap();

    let zc_src = fs::canonicalize(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../zerocopy/src"),
    )
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
                "<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"
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

    let ok = run_request(&tools, dir.path(), "zerocopy-split-at-ok", &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-zerocopy-split-at-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative 1: weaken splitAtSafety to omit `mid <= len` on verbatim
    // zerocopy.
    let bad_spec = ZEROCOPY_SPEC.replace(
        "mid.bits.toNat ≤ len.toNat",
        "True",
    );
    assert_ne!(bad_spec, ZEROCOPY_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_spec).unwrap();
    run_request(&tools, dir.path(), "zerocopy-split-at-missing-bounds", &request)
        .expect_proof_failed();

    // Negative 2: the `&mut [u8]` implementation mixes `&mut [u8]` and
    // `*mut u8` locals, so capture refuses it until Profile v2 models
    // aliasing.
    let mut mut_request = request.clone();
    mut_request["scope"]["roots"] =
        json!(["<&mut [u8] as byte_slice::SplitByteSlice>::split_at_unchecked"]);
    run_request(&tools, dir.path(), "zerocopy-split-at-mut-refused", &mut_request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Verifies raw pointer `*const u32` load and `*mut u8` store updating
/// `out.callerMem` under `CrateTheoremV2`, confirms that proofs are rejected
/// for missing alignment, null pointers, and read-only stores, and confirms
/// that capture refuses bodies that turn raw pointers into references or cast
/// `*const T` to `*mut T`.
#[test]
fn verifies_raw_pointer_load_store_and_rejects_unsound_callers() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), RAW_PTR_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), RAW_PTR_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), RAW_PTR_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "raw_ptr_demo",
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

    let ok = run_request(&tools, dir.path(), "raw-ptr-ok", &request);
    ok.expect_ok("crate_verified");
    ok.expect_profile_v2_assumptions();
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-raw-ptr-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative 2: missing alignment precondition on `*const u32`.
    let no_align = RAW_PTR_SPEC.replace(
        "isAligned a pv.offsetBytes.toNat 2 = true ∧",
        "True ∧",
    );
    assert_ne!(no_align, RAW_PTR_SPEC);
    fs::write(lean_dir.join("Spec.lean"), no_align).unwrap();
    run_request(&tools, dir.path(), "raw-ptr-missing-align", &request).expect_proof_failed();

    // Negative 3: missing non-null / live allocation precondition on
    // `*const u32`.
    let allow_null = RAW_PTR_SPEC.replacen("| none => False", "| none => True", 1);
    assert_ne!(allow_null, RAW_PTR_SPEC);
    fs::write(lean_dir.join("Spec.lean"), allow_null).unwrap();
    run_request(&tools, dir.path(), "raw-ptr-allow-null", &request).expect_proof_failed();

    // Negative 4: missing `.mut` precondition on `*mut u8` write.
    let no_mut = RAW_PTR_SPEC.replace("a.mutability = .mut ∧", "True ∧");
    assert_ne!(no_mut, RAW_PTR_SPEC);
    fs::write(lean_dir.join("Spec.lean"), no_mut).unwrap();
    run_request(&tools, dir.path(), "raw-ptr-readonly-write", &request).expect_proof_failed();

    // Negative 5: `from_raw_parts` turns a `*const u8` into a `&[u8]`, so the
    // body mixes reference and raw-pointer locals and capture refuses it.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub unsafe fn make_slice<'a>(p: *const u8, len: usize) -> &'a [u8] {\n\
             unsafe { core::slice::from_raw_parts(p, len) }\n\
         }\n",
    )
    .unwrap();
    run_request(&tools, dir.path(), "slice-from-raw-parts-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);

    // Negative 6: returning a dangling stack reference `&*(&raw const x)` also
    // mixes reference and raw-pointer locals.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub unsafe fn dangling<'a>(x: u8) -> &'a u8 {\n\
             unsafe { &*(&raw const x) }\n\
         }\n",
    )
    .unwrap();
    run_request(&tools, dir.path(), "dangling-stack-ref-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);

    // Negative 7: `&raw const x as *mut u32` would let the body write to the
    // immutable binding `x`, which Profile v2 cannot detect, so capture
    // refuses the cast.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn write_via_const() -> u32 {\n\
             let x: u32 = 1;\n\
             let p = &raw const x as *mut u32;\n\
             unsafe { *p = 2 };\n\
             x\n\
         }\n",
    )
    .unwrap();
    run_request(&tools, dir.path(), "write-via-const-refused", &request)
        .expect_capture_refused("`*const T` to `*mut T`");
}
