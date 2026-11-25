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
//!    `from_raw_parts`, and a returned reference to a stack local), or cast
//!    `*const T` to `*mut T`.

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::OnceLock,
};

use anneal_testkit::{
    SharedOleanCache, ToolchainEnv, ToolchainMode, VerifyReceipt, assert_rejected,
    assert_verified_untainted,
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

/// Capture refusal for bodies mixing reference and raw-pointer locals.
const MIXED_REFS_AND_RAW_PTRS: &str = "body mixes reference and raw-pointer locals";

fn tools() -> &'static ToolchainEnv {
    static TOOLS: OnceLock<ToolchainEnv> = OnceLock::new();
    TOOLS.get_or_init(|| {
        ToolchainEnv::resolve(ToolchainMode::WorkspaceBuild {
            cli_bin: Some(PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))),
            capture_bin: None,
            auditor_bin: None,
        })
        .expect("resolve Profile v2 e2e toolchain coordinates")
    })
}

fn shared_cache() -> &'static SharedOleanCache {
    static CACHE: OnceLock<SharedOleanCache> = OnceLock::new();
    CACHE.get_or_init(|| {
        SharedOleanCache::shared().expect("initialize persistent shared OleanCache")
    })
}

struct VerifyOutcome {
    name: String,
    receipt: VerifyReceipt,
    output: Output,
}

impl VerifyOutcome {
    fn expect_ok(&self, expected_status: &str) {
        assert_eq!(
            self.output.status.code(),
            Some(0),
            "{} failed unexpectedly:\nstdout:\n{}\nstderr:\n{}",
            self.name,
            String::from_utf8_lossy(&self.output.stdout),
            String::from_utf8_lossy(&self.output.stderr)
        );
        let verified = assert_verified_untainted(&self.receipt).unwrap_or_else(|error| {
            panic!(
                "{}: {error}\nstdout:\n{}",
                self.name,
                String::from_utf8_lossy(&self.output.stdout)
            )
        });
        assert_eq!(verified.status, expected_status, "{}: {:?}", self.name, verified);
        assert_eq!(verified.audit["exactType"], true, "{}: {}", self.name, verified.audit);
        assert_eq!(verified.audit["replay"], true, "{}: {}", self.name, verified.audit);
        assert_eq!(
            verified.audit["axioms"],
            json!(["propext"]),
            "{}: {}",
            self.name,
            verified.audit
        );
    }

    /// Profile v2 receipts must disclose the assumptions `ValidEntryArgsV2`
    /// and the missing aliasing model place on callers, and must not claim
    /// `lean-miri` correspondence.
    fn expect_profile_v2_assumptions(&self) {
        let VerifyReceipt::Verified(verified) = &self.receipt else {
            panic!("{}: expected verified receipt, got {:?}", self.name, self.receipt);
        };
        let semantics = verified
            .assumptions
            .iter()
            .find(|a| a.starts_with("experimental Profile v2 MIR semantics"))
            .unwrap_or_else(|| {
                panic!("{}: missing Profile v2 assumption: {:?}", self.name, verified.assumptions)
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
            verified.correspondence_provenance["applicable"], false,
            "{}: {}",
            self.name, verified.correspondence_provenance
        );
    }

    fn expect_proof_failed(&self) {
        assert_eq!(
            self.output.status.code(),
            Some(1),
            "{} must fail closed:\nstdout:\n{}\nstderr:\n{}",
            self.name,
            String::from_utf8_lossy(&self.output.stdout),
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_rejected(&self.receipt, "proof_failed", Some("audit"), "").unwrap_or_else(|error| {
            panic!(
                "{}: {error}\nstdout:\n{}",
                self.name,
                String::from_utf8_lossy(&self.output.stdout)
            )
        });
    }

    fn expect_capture_refused(&self, needle: &str) {
        assert_eq!(
            self.output.status.code(),
            Some(1),
            "{} must fail closed:\nstdout:\n{}\nstderr:\n{}",
            self.name,
            String::from_utf8_lossy(&self.output.stdout),
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_rejected(&self.receipt, "unsupported", Some("capture"), needle).unwrap_or_else(
            |error| {
                panic!(
                    "{}: {error}\nstdout:\n{}",
                    self.name,
                    String::from_utf8_lossy(&self.output.stdout)
                )
            },
        );
    }
}

fn run_request(dir: &Path, name: &str, request: &Value) -> VerifyOutcome {
    let tools = tools();
    let cache = shared_cache();
    let cli = tools.cli.as_deref().expect("resolved cargo-anneal binary");
    let capture = tools
        .capture
        .as_deref()
        .expect("resolved anneal-rustc-capture binary; build it before running this test");

    let req_path = dir.join(format!("{name}.json"));
    fs::write(&req_path, serde_json::to_vec_pretty(request).unwrap()).unwrap();
    let artifacts = dir.join(format!("artifacts-{name}"));
    let output = Command::new(cli)
        .current_dir(dir)
        .env("HOME", cache.home_dir())
        .env("XDG_CACHE_HOME", cache.xdg_cache_home())
        .arg("verify")
        .arg("--capture")
        .arg(capture)
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot)
        .arg("--request")
        .arg(&req_path)
        .arg("--artifacts")
        .arg(&artifacts)
        .output()
        .unwrap_or_else(|e| panic!("failed to run {name}: {e}"));
    let receipt = VerifyReceipt::from_json_slice(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "{name} did not emit valid Schema v3 JSON receipt: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    VerifyOutcome { name: name.to_owned(), receipt, output }
}

fn zerocopy_request(lean_dir: &Path, root: &str) -> Value {
    let zc_src =
        fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../zerocopy/src"))
            .expect("locate unmodified zerocopy/src");
    json!({
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
            "roots": [root]
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
    })
}

fn stage_zerocopy_case(spec: &str, root: &str) -> (TempDir, Value) {
    let dir = TempDir::new().unwrap();
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(lean_dir.join("Spec.lean"), spec).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ZEROCOPY_PROOF).unwrap();
    let request = zerocopy_request(&lean_dir, root);
    (dir, request)
}

fn stage_raw_ptr_case(lib_src: &str, spec: &str) -> (TempDir, Value) {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(rust_dir.join("lib.rs"), lib_src).unwrap();
    fs::write(lean_dir.join("Spec.lean"), spec).unwrap();
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
    (dir, request)
}

/// Verifies the unmodified `zerocopy/src/byte_slice.rs` `split_at_unchecked`
/// implementation for `&[u8]` end-to-end under `UnitTheoremV2` (`["propext"]`,
/// zero taint).
#[test]
fn verifies_verbatim_zerocopy_split_at_unchecked() {
    let (dir, request) = stage_zerocopy_case(
        ZEROCOPY_SPEC,
        "<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked",
    );
    let ok = run_request(dir.path(), "zerocopy-split-at-ok", &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-zerocopy-split-at-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
}

/// Weakening `splitAtSafety` to omit `mid <= len` on verbatim `zerocopy`
/// must fail closed during audit.
#[test]
fn rejects_verbatim_zerocopy_split_at_unchecked_missing_bounds() {
    let bad_spec = ZEROCOPY_SPEC.replace("mid.bits.toNat ≤ len.toNat", "True");
    assert_ne!(bad_spec, ZEROCOPY_SPEC);
    let (dir, request) =
        stage_zerocopy_case(&bad_spec, "<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked");
    run_request(dir.path(), "zerocopy-split-at-missing-bounds", &request).expect_proof_failed();
}

/// The `&mut [u8]` `split_at_unchecked` implementation mixes `&mut [u8]` and
/// `*mut u8` locals, so capture refuses it until Profile v2 models aliasing.
#[test]
fn refuses_verbatim_zerocopy_split_at_unchecked_mut_slice() {
    let (dir, request) = stage_zerocopy_case(
        ZEROCOPY_SPEC,
        "<&mut [u8] as byte_slice::SplitByteSlice>::split_at_unchecked",
    );
    run_request(dir.path(), "zerocopy-split-at-mut-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Verifies raw pointer `*const u32` load and `*mut u8` store updating
/// `out.callerMem` under `CrateTheoremV2`.
#[test]
fn verifies_raw_pointer_load_and_store() {
    let (dir, request) = stage_raw_ptr_case(RAW_PTR_LIB, RAW_PTR_SPEC);
    let ok = run_request(dir.path(), "raw-ptr-ok", &request);
    ok.expect_ok("crate_verified");
    ok.expect_profile_v2_assumptions();
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-raw-ptr-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
}

/// Missing alignment precondition on `*const u32` must fail closed.
#[test]
fn rejects_raw_pointer_load_missing_alignment() {
    let no_align = RAW_PTR_SPEC.replace("isAligned a pv.offsetBytes.toNat 2 = true ∧", "True ∧");
    assert_ne!(no_align, RAW_PTR_SPEC);
    let (dir, request) = stage_raw_ptr_case(RAW_PTR_LIB, &no_align);
    run_request(dir.path(), "raw-ptr-missing-align", &request).expect_proof_failed();
}

/// Missing non-null / live allocation precondition on `*const u32` must fail
/// closed.
#[test]
fn rejects_raw_pointer_load_allowing_null() {
    let allow_null = RAW_PTR_SPEC.replacen("| none => False", "| none => True", 1);
    assert_ne!(allow_null, RAW_PTR_SPEC);
    let (dir, request) = stage_raw_ptr_case(RAW_PTR_LIB, &allow_null);
    run_request(dir.path(), "raw-ptr-allow-null", &request).expect_proof_failed();
}

/// Missing `.mut` precondition on `*mut u8` write must fail closed.
#[test]
fn rejects_raw_pointer_store_without_mutability() {
    let no_mut = RAW_PTR_SPEC.replace("a.mutability = .mut ∧", "True ∧");
    assert_ne!(no_mut, RAW_PTR_SPEC);
    let (dir, request) = stage_raw_ptr_case(RAW_PTR_LIB, &no_mut);
    run_request(dir.path(), "raw-ptr-readonly-write", &request).expect_proof_failed();
}

/// `from_raw_parts` turns a `*const u8` into a `&[u8]`, so the body mixes
/// reference and raw-pointer locals and capture refuses it.
#[test]
fn refuses_slice_from_raw_parts_mixing_refs_and_raw_ptrs() {
    let (dir, request) = stage_raw_ptr_case(
        "pub unsafe fn make_slice<'a>(p: *const u8, len: usize) -> &'a [u8] {\n\
             unsafe { core::slice::from_raw_parts(p, len) }\n\
         }\n",
        RAW_PTR_SPEC,
    );
    run_request(dir.path(), "slice-from-raw-parts-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Returning a dangling stack reference `&*(&raw const x)` mixes reference
/// and raw-pointer locals and capture refuses it.
#[test]
fn refuses_dangling_stack_ref_mixing_refs_and_raw_ptrs() {
    let (dir, request) = stage_raw_ptr_case(
        "pub unsafe fn dangling<'a>(x: u8) -> &'a u8 {\n\
             unsafe { &*(&raw const x) }\n\
         }\n",
        RAW_PTR_SPEC,
    );
    run_request(dir.path(), "dangling-stack-ref-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Casting `&raw const x as *mut u32` would let the body write to the
/// immutable binding `x`, which Profile v2 cannot detect, so capture refuses
/// the cast.
#[test]
fn refuses_const_to_mut_raw_ptr_cast() {
    let (dir, request) = stage_raw_ptr_case(
        "pub fn write_via_const() -> u32 {\n\
             let x: u32 = 1;\n\
             let p = &raw const x as *mut u32;\n\
             unsafe { *p = 2 };\n\
             x\n\
         }\n",
        RAW_PTR_SPEC,
    );
    run_request(dir.path(), "write-via-const-refused", &request)
        .expect_capture_refused("`*const T` to `*mut T`");
}
