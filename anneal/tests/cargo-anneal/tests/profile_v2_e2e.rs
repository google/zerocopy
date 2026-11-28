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
//!    read-only write, missing `Vec::with_capacity` `isize::MAX` bound), and
//!    capture refusing bodies that mix reference and
//!    raw-pointer locals, which Profile v2 cannot check without an aliasing
//!    model (verbatim `<&mut [u8] as SplitByteSlice>::split_at_unchecked`,
//!    `from_raw_parts`, and a returned reference to a stack local), or cast
//!    `*const T` to `*mut T`.
//! 4. `-Coverflow-checks=yes` capture (`compilation.overflow_checks`): a
//!    guarded `u8` increment verifies under both panic strategies, proving its
//!    overflow `Assert` never fires, while one proof of the wrapping result of
//!    an unguarded increment verifies without overflow checks and is rejected
//!    with them.
//! 5. Heap allocation contracts (`Vec<u8>` and `Box<[u8]>` / `Box<u64>`) under
//!    `CrateTheoremV2` with `--panic abort`.

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
const OVERFLOW_LIB: &str = include_str!("fixtures/profile_v2_overflow/lib.rs");
const OVERFLOW_STEPS: &str = include_str!("fixtures/profile_v2_overflow/StepLemmas.lean");
const GUARDED_SPEC: &str = include_str!("fixtures/profile_v2_overflow/GuardedSpec.lean");
const GUARDED_PROOF: &str = include_str!("fixtures/profile_v2_overflow/GuardedProof.lean");
const WRAPPING_SPEC: &str = include_str!("fixtures/profile_v2_overflow/WrappingSpec.lean");
const WRAPPING_PROOF: &str = include_str!("fixtures/profile_v2_overflow/WrappingProof.lean");
const ARRAYS_LIB: &str = include_str!("fixtures/profile_v2_arrays/lib.rs");
const ARRAYS_SPEC: &str = include_str!("fixtures/profile_v2_arrays/Spec.lean");
const ARRAYS_PROOF: &str = include_str!("fixtures/profile_v2_arrays/Proof.lean");
const PANIC_ABORT_LIB: &str = include_str!("fixtures/profile_v2_panic_abort/lib.rs");
const PANIC_ABORT_SPEC: &str = include_str!("fixtures/profile_v2_panic_abort/Spec.lean");
const PANIC_ABORT_PROOF: &str = include_str!("fixtures/profile_v2_panic_abort/Proof.lean");
const CORE_CONTRACTS_LIB: &str =
    include_str!("fixtures/profile_v2_core_contracts/lib.rs");
const CORE_CONTRACTS_SPEC: &str =
    include_str!("fixtures/profile_v2_core_contracts/Spec.lean");
const CORE_CONTRACTS_PROOF: &str =
    include_str!("fixtures/profile_v2_core_contracts/Proof.lean");
const ALLOC_LIB: &str = include_str!("fixtures/profile_v2_alloc/lib.rs");
const ALLOC_SPEC: &str = include_str!("fixtures/profile_v2_alloc/Spec.lean");
const ALLOC_PROOF: &str = include_str!("fixtures/profile_v2_alloc/Proof.lean");

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
        assert!(verified.spec_warnings.is_empty(), "{}: {:?}", self.name, verified.spec_warnings);
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
        .args(["verify", "--format", "json"])
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
                {"module": "Spec", "path": "Spec.lean",
                 "role": "specification"},
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
                {"module": "Spec", "path": "Spec.lean",
                 "role": "specification"},
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

    // Default `--format human` (without `-v`) must disclose Profile v2's
    // entry-validity narrowing verbatim rather than collapsing it into a
    // baseline assumption count.
    let tools = tools();
    let cache = shared_cache();
    let human_out = Command::new(tools.cli.as_deref().expect("resolved cargo-anneal binary"))
        .current_dir(dir.path())
        .env("HOME", cache.home_dir())
        .env("XDG_CACHE_HOME", cache.xdg_cache_home())
        .args(["verify", "--request"])
        .arg(dir.path().join("raw-ptr-ok.json"))
        .arg("--capture")
        .arg(tools.capture.as_deref().expect("resolved anneal-rustc-capture binary"))
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot)
        .output()
        .expect("run default human-format Profile v2 verify");
    assert_eq!(
        human_out.status.code(),
        Some(0),
        "default human verify failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&human_out.stdout),
        String::from_utf8_lossy(&human_out.stderr),
    );
    let human_card = String::from_utf8_lossy(&human_out.stdout);
    assert!(human_card.contains("[STAGE 0 ALPHA -- EXPERIMENTAL]"), "{human_card}");
    assert!(
        human_card.contains("! CAVEAT   : experimental Profile v2 MIR semantics:")
            && human_card.contains(
                "results say nothing about calls that pass references to \
                 uninitialized, invalid, or dangling memory"
            ),
        "default human card must disclose Profile v2 narrowing:\n{human_card}"
    );
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

/// Stages `fixtures/profile_v2_overflow` with the given specification and
/// proof, returning the request for `roots` captured under `panic`, with or
/// without `-Coverflow-checks=yes`. Both `buggy_add_u8` requests also capture
/// `zero_pair`, whose tuple keeps the program on Profile v2 when
/// `buggy_add_u8` has no `Assert`.
fn stage_overflow_case(
    spec: &str,
    proof: &str,
    roots: &[&str],
    panic: &str,
    overflow_checks: bool,
) -> (TempDir, Value) {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(rust_dir.join("lib.rs"), OVERFLOW_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), spec).unwrap();
    fs::write(lean_dir.join("Proof.lean"), proof).unwrap();
    fs::write(lean_dir.join("StepLemmas.lean"), OVERFLOW_STEPS).unwrap();
    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "overflow_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"],
            "panic": panic,
            "overflow_checks": overflow_checks
        },
        "scope": {"kind": "selected_unit", "roots": roots},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "StepLemmas", "path": "StepLemmas.lean", "role": "proof"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    (dir, request)
}

/// Reads the `capture.json` and `Captured.lean` that request `name` wrote.
fn captured_overflow_case(dir: &Path, name: &str) -> (Value, String) {
    let capture = dir.join(format!("artifacts-{name}/capture"));
    let capture_json: Value =
        serde_json::from_slice(&fs::read(capture.join("capture.json")).unwrap()).unwrap();
    let lean = fs::read_to_string(capture.join("Captured.lean")).unwrap();
    (capture_json, lean)
}

const OVERFLOW_ADD_ASSERT: &str = "AssertKind.overflow Trusted.MirAst.BinOp.add";
const WRAPPING_ROOTS: &[&str] = &["buggy_add_u8", "zero_pair"];

/// Verifies `guarded_add_u8` captured with `-Coverflow-checks=yes` under
/// `panic`: the saturating result and normal return with no divergence or
/// fault, so its `AddWithOverflow` `Assert` never fails.
fn verify_overflow_checked_guarded_add(panic: &str) {
    let name = format!("guarded-add-overflow-checks-{panic}");
    let (dir, request) =
        stage_overflow_case(GUARDED_SPEC, GUARDED_PROOF, &["guarded_add_u8"], panic, true);
    let ok = run_request(dir.path(), &name, &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let (capture_json, lean) = captured_overflow_case(dir.path(), &name);
    assert_eq!(capture_json["configuration"]["overflow_checks"], true, "{capture_json}");
    assert_eq!(capture_json["configuration"]["panic"], panic, "{capture_json}");
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert!(lean.contains("overflowChecks := true"), "{name}:\n{lean}");
    assert!(lean.contains(OVERFLOW_ADD_ASSERT), "{name}:\n{lean}");
}

#[test]
fn verifies_overflow_checked_guarded_add_under_panic_abort() {
    verify_overflow_checked_guarded_add("abort");
}

#[test]
fn verifies_overflow_checked_guarded_add_under_panic_unwind() {
    verify_overflow_checked_guarded_add("unwind");
}

/// Without overflow checks, `buggy_add_u8`'s `x + 1` is a wrapping `Add`, and
/// a proof that it returns `(x + 1) % 256` verifies.
#[test]
fn verifies_wrapping_add_without_overflow_checks() {
    let name = "wrapping-add-no-overflow-checks";
    let (dir, request) =
        stage_overflow_case(WRAPPING_SPEC, WRAPPING_PROOF, WRAPPING_ROOTS, "abort", false);
    let ok = run_request(dir.path(), name, &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let (capture_json, lean) = captured_overflow_case(dir.path(), name);
    assert_eq!(capture_json["configuration"]["overflow_checks"], false, "{capture_json}");
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert!(lean.contains("overflowChecks := false"), "{lean}");
    assert!(!lean.contains("AssertKind.overflow"), "{lean}");
}

/// With overflow checks, the same specification and proof are rejected,
/// because `x = 255` fails the overflow `Assert`.
#[test]
fn rejects_wrapping_add_proof_with_overflow_checks() {
    let name = "wrapping-add-overflow-checks";
    let (dir, request) =
        stage_overflow_case(WRAPPING_SPEC, WRAPPING_PROOF, WRAPPING_ROOTS, "abort", true);
    run_request(dir.path(), name, &request).expect_proof_failed();
    let (capture_json, lean) = captured_overflow_case(dir.path(), name);
    assert_eq!(capture_json["configuration"]["overflow_checks"], true, "{capture_json}");
    assert!(lean.contains(OVERFLOW_ADD_ASSERT), "{lean}");
}

/// Verifies fixed-size arrays `[T; N]`, `Repeat`, `ConstantIndex`, `Unsize`
/// (`&[u8; 3] -> &[u8]`), `.rodata` array constants, projected
/// `Rvalue::Discriminant` (`discriminant(*a)`), `int::to_le_bytes`, and
/// `<[u8; 4] as PartialEq>::eq` under `UnitTheoremV2` (`["propext"]`, zero
/// taint), plus four functional spec mismatch rejections and a capture-level
/// rejection for dynamic array indexing.
#[test]
fn verifies_profile_v2_arrays_and_rejects_unsound_specs() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), ARRAYS_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ARRAYS_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ARRAYS_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "profile_v2_arrays",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {
            "kind": "selected_unit",
            "roots": [
                "pack_le_rev",
                "repeat_unsize_len",
                "tag_eq",
                "matches_pattern"
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

    let ok = run_request(dir.path(), "arrays-ok", &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-arrays-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative 1: wrong byte order in `pack_le_rev` spec.
    let bad_pack = ARRAYS_SPEC.replace(
        "⟨.array [.scalar ⟨.i8, false, hi⟩, .scalar ⟨.i8, false, lo⟩], q.callerMem⟩",
        "⟨.array [.scalar ⟨.i8, false, lo⟩, .scalar ⟨.i8, false, hi⟩], q.callerMem⟩",
    );
    assert_ne!(bad_pack, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_pack).unwrap();
    run_request(dir.path(), "arrays-wrong-le-order", &request).expect_proof_failed();

    // Negative 2: wrong slice length in `repeat_unsize_len` spec.
    let bad_len = ARRAYS_SPEC.replace(
        "⟨.scalar ⟨.isize, false, BitVec.ofNat 128 3⟩, q.callerMem⟩",
        "⟨.scalar ⟨.isize, false, BitVec.ofNat 128 4⟩, q.callerMem⟩",
    );
    assert_ne!(bad_len, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_len).unwrap();
    run_request(dir.path(), "arrays-wrong-repeat-len", &request).expect_proof_failed();

    // Negative 3: inverted boolean result in `tag_eq` spec.
    let bad_tag = ARRAYS_SPEC.replace(
        "⟨.bool (Nat.beq ba.toNat bb.toNat), q.callerMem⟩",
        "⟨.bool (!(Nat.beq ba.toNat bb.toNat)), q.callerMem⟩",
    );
    assert_ne!(bad_tag, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_tag).unwrap();
    run_request(dir.path(), "arrays-wrong-tag-eq", &request).expect_proof_failed();

    // Negative 4: wrong `.rodata` pattern byte in `matches_pattern` spec.
    let bad_pat = ARRAYS_SPEC.replace(
        "Nat.beq b3.toNat 4",
        "Nat.beq b3.toNat 5",
    );
    assert_ne!(bad_pat, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_pat).unwrap();
    run_request(dir.path(), "arrays-wrong-rodata-pattern", &request)
        .expect_proof_failed();

    // Negative 5 (capture): dynamic array indexing (`PlaceElem::Index`) is
    // refused fail-closed at capture time.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn dyn_idx(a: &[u8; 4], i: usize) -> u8 { a[i] }\n",
    )
    .unwrap();
    let bad_req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "profile_v2_arrays",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {
            "kind": "selected_unit",
            "roots": ["dyn_idx"]
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
    run_request(dir.path(), "arrays-dyn-index-refused", &bad_req)
        .expect_capture_refused("unsupported place projection `Index(");
}

/// Verifies safe `safe_div_ceil` and `write_then_div` under `--panic abort`
/// (`SafeContractV2` covering both `{ allowAbort := true }` abort on `b = 0`—
/// including pre-abort `&mut` mutation visibility in `postAbort`—and
/// `noAbort` when `b != 0`), and confirms `--panic unwind`, omitted panic
/// strategy (defaulting to unwind), and weakened `EffectMaskV2.noAbort`
/// preconditions fail closed.
#[test]
fn verifies_panic_abort_div_ceil_and_rejects_panic_unwind() {
    let tools = tools();
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), PANIC_ABORT_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), PANIC_ABORT_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), PANIC_ABORT_PROOF).unwrap();

    let base_request = |panic: Option<&str>| {
        let mut compilation = json!({
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "panic_abort_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        });
        if let Some(strategy) = panic {
            compilation["panic"] = json!(strategy);
        }
        json!({
            "schema_version": 1,
            "compilation": compilation,
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
        })
    };

    let abort_request = base_request(Some("abort"));
    let ok = run_request(dir.path(), "panic-abort-ok", &abort_request);
    ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(abort_verified) = &ok.receipt else {
        panic!("expected verified receipt, got {:?}", ok.receipt);
    };
    let abort_assumptions: Vec<&str> =
        abort_verified.assumptions.iter().map(String::as_str).collect();
    assert!(
        abort_assumptions.iter().any(|a| {
            a.starts_with(
                "--panic abort models failed non-optional safe assertions \
                 and admitted core::panicking calls as .aborted",
            )
                && a.contains("panic hooks and handlers")
                && a.contains("caller-memory effects before the panic")
                && !a.contains("overflow")
        }),
        "expected explicit --panic abort receipt assumption, got {abort_assumptions:?}"
    );
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-panic-abort-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert_eq!(capture_json["program"]["panic"], "abort", "{capture_json}");
    assert_eq!(capture_json["program"]["has_local_panic_handler"], false, "{capture_json}");

    // Negative 1: explicit `--panic unwind` fails closed on aborting paths.
    run_request(dir.path(), "panic-unwind-rejected", &base_request(Some("unwind")))
        .expect_proof_failed();

    // Negative 2: omitted panic strategy defaults to unwind and fails closed.
    run_request(dir.path(), "panic-default-rejected", &base_request(None))
        .expect_proof_failed();

    // Negative 3: weakening `divCeilNoAbort` `behaviorPre` under `noAbort`
    // fails closed even under `--panic abort`.
    let weak_spec = PANIC_ABORT_SPEC.replace("b.bits.toNat ≠ 0", "True");
    assert_ne!(weak_spec, PANIC_ABORT_SPEC);
    fs::write(lean_dir.join("Spec.lean"), weak_spec).unwrap();
    run_request(dir.path(), "panic-abort-weak-no-abort", &abort_request)
        .expect_proof_failed();

    // Negative 4: asserting entry `q.callerMem` instead of post-mutation
    // `extractCallerMemory q.callerMem mem'` in `writeThenDivSlotPost` fails
    // closed because `*slot = a` mutates caller memory before aborting.
    let stale_mem_spec = PANIC_ABORT_SPEC.replace(
        "cm = extractCallerMemory q.callerMem mem'",
        "cm = q.callerMem",
    );
    assert_ne!(stale_mem_spec, PANIC_ABORT_SPEC);
    fs::write(lean_dir.join("Spec.lean"), stale_mem_spec).unwrap();
    run_request(dir.path(), "panic-abort-stale-preabort-mem", &abort_request)
        .expect_proof_failed();

    // Check 5: optional overflow checks (`-Coverflow-checks=yes`) under
    // `--panic abort` abort cleanly like the other safe panics, because
    // `evalAssertFailure` models them as runtime panics when
    // `Program.overflowChecks` is set.
    //
    // First confirm stable `a + b` under `--panic abort --overflow-checks`
    // captures with `overflowChecks := true` and an
    // `AssertKind.overflow BinOp.add` terminator.
    let overflow_add_dir = dir.path().join("overflow-add");
    fs::create_dir_all(&overflow_add_dir).unwrap();
    let overflow_add_src = overflow_add_dir.join("lib.rs");
    fs::write(
        &overflow_add_src,
        "pub fn f(a: u8, b: u8) -> u8 {\n\
             a + b\n\
         }\n",
    )
    .unwrap();
    let overflow_add_out = dir.path().join("overflow-add-capture");
    let add_cap_out = Command::new(tools.capture.as_deref().expect("capture bin"))
        .args([
            "capture",
            "--crate-root",
            overflow_add_src.to_str().unwrap(),
            "--crate-name",
            "overflow_add_demo",
            "--crate-type",
            "lib",
            "--edition",
            "2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--panic",
            "abort",
            "--overflow-checks",
            "--scope",
            "crate",
            "--out-dir",
            overflow_add_out.to_str().unwrap(),
            "--sysroot",
            tools.sysroot.to_str().unwrap(),
            "--source-file",
            overflow_add_src.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        add_cap_out.status.success(),
        "overflow-add capture failed: {}",
        String::from_utf8_lossy(&add_cap_out.stdout)
    );
    let overflow_add_lean = fs::read_to_string(overflow_add_out.join("Captured.lean")).unwrap();
    assert!(
        overflow_add_lean.contains("overflowChecks := true")
            && overflow_add_lean
                .contains("Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.add"),
        "{overflow_add_lean}"
    );

    // Next kernel-check via `cargo-anneal verify` on real captured
    // `-Coverflow-checks=yes` bodies whose assert condition is a bare scalar
    // (`-a` -> `AssertKind.overflowNeg`, `a << b` ->
    // `AssertKind.overflow BinOp.shl`) that overflowing inputs reach
    // `.done (.aborted _)`. Both proofs fail to typecheck if optional overflow
    // asserts fault under `--panic abort --overflow-checks`.
    let overflow_rust_dir = dir.path().join("overflow-rust");
    let overflow_lean_dir = dir.path().join("overflow-lean");
    fs::create_dir_all(&overflow_rust_dir).unwrap();
    fs::create_dir_all(&overflow_lean_dir).unwrap();
    fs::write(
        overflow_rust_dir.join("lib.rs"),
        "pub unsafe fn f_neg(a: i8) -> i8 {\n\
             -a\n\
         }\n\
         pub unsafe fn f_shl(a: u8, b: u32) -> u8 {\n\
             a << b\n\
         }\n",
    )
    .unwrap();
    fs::write(
        overflow_lean_dir.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def qNegOverflow : Query :=
  { args := [.scalar ⟨.i8, true, BitVec.ofNat 128 128⟩] }

def qShlOverflow : Query :=
  { args := [
      .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
      .scalar ⟨.i32, false, BitVec.ofNat 128 8⟩] }

def safety (id : String) (q : Query) : Prop :=
  (id = "rust-path-v1::f_neg" ∧
    q.args = [.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩]) ∨
  (id = "rust-path-v1::f_shl" ∧
    q.args = [
      .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
      .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩])

def property (p : Program) : Prop :=
  (∃ cm, ReachesResultV2 (entryProgForBody p 0) qNegOverflow
    (.done (.aborted cm))) ∧
  (∃ cm, ReachesResultV2 (entryProgForBody p 1) qShlOverflow
    (.done (.aborted cm)))

def specs : SpecsV2 := ⟨safety, property⟩

end Spec
"#,
    )
    .unwrap();
    fs::write(
        overflow_lean_dir.join("Proof.lean"),
        r#"prelude
import Init.NotationExtra
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics

private theorem ite_bool_false {α : Type u} {b : Bool} {t e : α}
    (h : b = false) : (if b = true then t else e) = e := by
  rw [h]; rfl

private def mkS (defId bb st : Nat) (locs : List LocalSlot)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  ⟨[⟨defId, bb, st, locs, none, none, none⟩], cm, mem⟩

private inductive DetTerminates (p : Program) : State → Prop where
  | done {s : State} {out : TerminalOut} :
      evalStepV2Choice p 0 s = .done out → DetTerminates p s
  | step {s s' : State} :
      evalStepV2Choice p 0 s = .step s' →
      DetTerminates p s' →
      DetTerminates p s

private theorem det_step_eq {p : Program} {s : State}
    {r₁ r₂ : StepResult State TerminalOut}
    (h₁ : StepV2 p s r₁) (h₂ : evalStepV2Choice p 0 s = r₂) :
    r₁ = r₂ := by
  let ⟨c, hc, heq⟩ := h₁
  have hc0 : c = 0 := hc
  rw [hc0] at heq
  rw [← heq, h₂]

private theorem detTerminates_reaches {p : Program} {s₀ s : State}
    (hR : ReachesV2 p s₀ s) (hT : DetTerminates p s₀) :
    DetTerminates p s := by
  induction hR with
  | refl => exact hT
  | tail _ hStep ih =>
    cases ih with
    | done hD => cases det_step_eq hStep hD
    | step hS hNext =>
      cases det_step_eq hStep hS
      exact hNext

private theorem wf_of_detTerminates {p : Program} {q : Query}
    {s₀ : State} (hInit : initStateV2 p q = .ok s₀)
    (hT : DetTerminates p s₀) : WellFormedV2 p q := by
  refine ⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, fun k hFault => ?_⟩
  unfold ReachesResultV2 at hFault
  rw [hInit] at hFault
  let ⟨s, hR, hSt⟩ := hFault
  cases detTerminates_reaches hR hT with
  | done hD => cases det_step_eq hSt hD
  | step hS _ => cases det_step_eq hSt hS

private theorem body0_steps (cm : CallerMemory) (mem : MemoryState) :
    DetTerminates (entryProgForBody Captured.program 0)
      (mkS 0 0 0
        [.immediate none,
         .immediate (some (.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩)),
         .dead, .immediate none] cm mem) := by
  let v1 : Val := .scalar ⟨.i8, true, BitVec.ofNat 128 1⟩
  let vm1 : Val := .scalar ⟨.i8, true, BitVec.ofNat 128 255⟩
  refine .step (s' := mkS 0 0 1 [.immediate none, .immediate (some v1), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 2 [.immediate none, .immediate (some v1), .immediate (some v1), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 3 [.immediate none, .immediate (some v1), .immediate (some v1), .immediate (some (.bool false))] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 0 [.immediate none, .immediate (some v1), .immediate (some v1), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 1 [.immediate (some vm1), .immediate (some v1), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 2 [.immediate (some vm1), .immediate (some v1), .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem body0_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : q.args = [.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩]) :
    WellFormedV2 (entryProgForBody Captured.program 0) q := by
  cases q with
  | mk args cm =>
    dsimp only at hSafe
    subst hSafe
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩], cm⟩ =
        .ok (mkS 0 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩)),
           .dead, .immediate none] cm (entryMemoryWithCaller cm)) := by
      unfold initStateV2 entryProgForBody Captured.program
        Trusted.MirSemantics.getElem?
      dsimp only
      have h1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
      have h2 : (!(true : Bool)) = false := rfl
      rw [ite_bool_false h1, hMem, ite_bool_false h2]
      rfl
    exact wf_of_detTerminates hInit (body0_steps cm (entryMemoryWithCaller cm))

private theorem body1_steps (cm : CallerMemory) (mem : MemoryState) :
    DetTerminates (entryProgForBody Captured.program 1)
      (mkS 1 0 0
        [.immediate none,
         .immediate (some (.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩)),
         .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 2⟩)),
         .dead, .dead, .immediate none] cm mem) := by
  let va : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩
  let vb : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩
  let vr : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 4⟩
  refine .step (s' := mkS 1 0 1 [.immediate none, .immediate (some va), .immediate (some vb), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 2 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 3 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 4 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 5 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate (some (.bool true))] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 0 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 1 [.immediate (some vr), .immediate (some va), .immediate (some vb), .immediate none, .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 2 [.immediate (some vr), .immediate (some va), .immediate (some vb), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 3 [.immediate (some vr), .immediate (some va), .immediate (some vb), .dead, .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem body1_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q)
    (hSafe : q.args = [
      .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
      .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩]) :
    WellFormedV2 (entryProgForBody Captured.program 1) q := by
  cases q with
  | mk args cm =>
    dsimp only at hSafe
    subst hSafe
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 1)
          ⟨[.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
            .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩], cm⟩ =
        .ok (mkS 1 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩)),
           .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 2⟩)),
           .dead, .dead, .immediate none] cm (entryMemoryWithCaller cm)) := by
      unfold initStateV2 entryProgForBody Captured.program
        Trusted.MirSemantics.getElem?
      dsimp only
      have h1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
      have h2 : (!(true : Bool)) = false := rfl
      rw [ite_bool_false h1, hMem, ite_bool_false h2]
      rfl
    exact wf_of_detTerminates hInit (body1_steps cm (entryMemoryWithCaller cm))

private theorem neg_overflow_aborts :
    ∃ cm, ReachesResultV2 (entryProgForBody Captured.program 0)
      Spec.qNegOverflow (.done (.aborted cm)) :=
  ⟨_, _, .tail (.tail (.tail (.refl _) ⟨0, rfl, rfl⟩)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩, ⟨0, rfl, rfl⟩⟩

private theorem shl_overflow_aborts :
    ∃ cm, ReachesResultV2 (entryProgForBody Captured.program 1)
      Spec.qShlOverflow (.done (.aborted cm)) :=
  ⟨_, _, .tail (.tail (.tail (.tail (.tail (.refl _)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩, ⟨0, rfl, rfl⟩⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
      cases hSafe rfl with
      | inl h => exact body0_wf q hValid h.2
      | inr h =>
        exact False.elim
          ((by decide : Captured.body_0.identity ≠ "rust-path-v1::f_shl") h.1)
    | succ n =>
      cases n with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
        cases hSafe rfl with
        | inl h =>
          exact False.elim
            ((by decide : Captured.body_1.identity ≠ "rust-path-v1::f_neg") h.1)
        | inr h => exact body1_wf q hValid h.2
      | succ _ =>
        change none = some body at hBody
        cases hBody
  · exact ⟨neg_overflow_aborts, shl_overflow_aborts⟩

end Proof
"#,
    )
    .unwrap();
    let overflow_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": overflow_rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "optional_overflow_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "overflow_checks": true,
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": overflow_lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let overflow_ok = run_request(
        dir.path(),
        "panic-abort-optional-overflow",
        &overflow_request,
    );
    overflow_ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(overflow_verified) = &overflow_ok.receipt else {
        panic!("expected verified receipt, got {:?}", overflow_ok.receipt);
    };
    assert!(overflow_verified.spec_warnings.is_empty(), "{overflow_verified:?}");
    let overflow_assumptions: Vec<&str> =
        overflow_verified.assumptions.iter().map(String::as_str).collect();
    assert!(
        overflow_assumptions.iter().any(|a| {
            a.starts_with(
                "--panic abort models failed non-optional safe assertions, admitted \
                 core::panicking calls, and, under --overflow-checks, failed overflow \
                 checks as .aborted",
            ) && a.contains("panic hooks and handlers")
                && a.contains("a build that elides the overflow checks wraps")
        }),
        "expected --panic abort --overflow-checks receipt assumption, got \
         {overflow_assumptions:?}"
    );
    let overflow_captured = fs::read_to_string(
        dir.path().join("artifacts-panic-abort-optional-overflow/capture/Captured.lean"),
    )
    .unwrap();
    assert!(
        overflow_captured.contains("overflowChecks := true"),
        "{overflow_captured}"
    );
    assert!(
        overflow_captured.contains("Trusted.MirAst.AssertKind.overflowNeg"),
        "{overflow_captured}"
    );
    assert!(
        overflow_captured
            .contains("Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.shl"),
        "{overflow_captured}"
    );

    // Check 6: a `#![no_std]` binary with a crate-local `#[panic_handler]`
    // compiled with `--panic abort` keeps failing safe `Assert`s fail-closed
    // as `.fault .unsupported` (and omits the default-runtime `.aborted`
    // receipt assumption).
    let local_handler_rust = dir.path().join("local-handler-rust");
    let local_handler_lean = dir.path().join("local-handler-lean");
    fs::create_dir_all(&local_handler_rust).unwrap();
    fs::create_dir_all(&local_handler_lean).unwrap();
    fs::write(
        local_handler_rust.join("main.rs"),
        "#![no_std]\n\
         #![no_main]\n\
         use core::panic::PanicInfo;\n\
         #[panic_handler]\n\
         fn panic(_info: &PanicInfo<'_>) -> ! {\n\
             loop {}\n\
         }\n\
         pub unsafe fn div_u64(a: u64, b: u64, _tag: (u8, u8, u8)) -> u64 {\n\
             a / b\n\
         }\n",
    )
    .unwrap();
    fs::write(
        local_handler_lean.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def vTag : Val :=
  .tuple [
    .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩,
    .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩,
    .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩]

def qDivZero : Query :=
  { args := [
      .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
      .scalar ⟨.i64, false, BitVec.ofNat 128 0⟩,
      vTag] }

def safety (_id : String) (q : Query) : Prop :=
  q.args = [
    .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
    .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩,
    vTag]

def property (p : Program) : Prop :=
  ReachesResultV2 (entryProgForBody p 0) qDivZero (.fault .unsupported) ∧
  ¬ WellFormedV2 (entryProgForBody p 0) qDivZero

def specs : SpecsV2 := {
  safety := safety
  property := property
}

end Spec
"#,
    )
    .unwrap();
    fs::write(
        local_handler_lean.join("Proof.lean"),
        r#"prelude
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics

private theorem ite_bool_false {α : Type u} {b : Bool} {t e : α}
    (h : b = false) : (if b = true then t else e) = e := by
  rw [h]; rfl

private def mkS (defId bb st : Nat) (locs : List LocalSlot)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  ⟨[⟨defId, bb, st, locs, none, none, none⟩], cm, mem⟩

private inductive DetTerminates (p : Program) : State → Prop where
  | done {s : State} {out : TerminalOut} :
      evalStepV2Choice p 0 s = .done out → DetTerminates p s
  | step {s s' : State} :
      evalStepV2Choice p 0 s = .step s' →
      DetTerminates p s' →
      DetTerminates p s

private theorem det_step_eq {p : Program} {s : State}
    {r₁ r₂ : StepResult State TerminalOut}
    (h₁ : StepV2 p s r₁) (h₂ : evalStepV2Choice p 0 s = r₂) :
    r₁ = r₂ := by
  let ⟨c, hc, heq⟩ := h₁
  have hc0 : c = 0 := hc
  rw [hc0] at heq
  rw [← heq, h₂]

private theorem detTerminates_reaches {p : Program} {s₀ s : State}
    (hR : ReachesV2 p s₀ s) (hT : DetTerminates p s₀) :
    DetTerminates p s := by
  induction hR with
  | refl => exact hT
  | tail _ hStep ih =>
    cases ih with
    | done hD => cases det_step_eq hStep hD
    | step hS hNext =>
      cases det_step_eq hStep hS
      exact hNext

private theorem wf_of_detTerminates {p : Program} {q : Query}
    {s₀ : State} (hInit : initStateV2 p q = .ok s₀)
    (hT : DetTerminates p s₀) : WellFormedV2 p q := by
  refine ⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, fun k hFault => ?_⟩
  unfold ReachesResultV2 at hFault
  rw [hInit] at hFault
  let ⟨s, hR, hSt⟩ := hFault
  cases detTerminates_reaches hR hT with
  | done hD => cases det_step_eq hSt hD
  | step hS _ => cases det_step_eq hSt hS

private theorem div_steps (cm : CallerMemory) (mem : MemoryState) :
    DetTerminates (entryProgForBody Captured.program 0)
      (mkS 0 0 0
        [.immediate none,
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩)),
         .immediate (some Spec.vTag),
         .dead, .dead, .immediate none] cm mem) := by
  let va : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩
  let vb : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩
  let vt : Val := Spec.vTag
  refine .step (s' := mkS 0 0 1
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 2
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 3
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate none,
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 4
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate (some vb),
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 5
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate (some vb),
     .immediate (some (.bool false))] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 0
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate (some vb),
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 1
    [.immediate (some va), .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate none, .immediate none,
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 2
    [.immediate (some va), .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 3
    [.immediate (some va), .immediate (some va), .immediate (some vb),
     .immediate (some vt), .dead, .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem div_ok_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hArgs : q.args = [
      .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
      .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩,
      Spec.vTag]) :
    WellFormedV2 (entryProgForBody Captured.program 0) q := by
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩,
            Spec.vTag], cm⟩ =
        .ok (mkS 0 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩)),
           .immediate (some Spec.vTag),
           .dead, .dead, .immediate none] cm (entryMemoryWithCaller cm)) := by
      unfold initStateV2 entryProgForBody Captured.program
        Trusted.MirSemantics.getElem?
      dsimp only
      have h1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
      have h2 : (!(true : Bool)) = false := rfl
      rw [ite_bool_false h1, hMem, ite_bool_false h2]
      rfl
    exact wf_of_detTerminates hInit (div_steps cm (entryMemoryWithCaller cm))

private theorem div_zero_unsupported :
    ReachesResultV2 (entryProgForBody Captured.program 0) Spec.qDivZero
      (.fault .unsupported) :=
  ⟨_, .tail (.tail (.tail (.tail (.tail (.refl _) ⟨0, rfl, rfl⟩)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩,
    ⟨0, rfl, rfl⟩⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => div_ok_wf q hValid (hSafe rfl)⟩
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · exact ⟨div_zero_unsupported,
      fun hWf => hWf.2 .unsupported div_zero_unsupported⟩

end Proof
"#,
    )
    .unwrap();
    let local_handler_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": local_handler_rust.to_str().unwrap(),
            "crate_root": "main.rs",
            "crate_name": "local_handler_demo",
            "crate_type": "bin",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["main.rs"]
        },
        "scope": {"kind": "selected_unit", "roots": ["div_u64"]},
        "proof": {
            "source_root": local_handler_lean.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let lh_ok = run_request(
        dir.path(),
        "panic-abort-local-handler",
        &local_handler_request,
    );
    lh_ok.expect_ok("selected_unit_verified");
    let lh_capture: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-panic-abort-local-handler/capture/capture.json"))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(lh_capture["program"]["panic"], "abort", "{lh_capture}");
    assert_eq!(lh_capture["program"]["has_local_panic_handler"], true, "{lh_capture}");
    let VerifyReceipt::Verified(lh_verified) = &lh_ok.receipt else {
        panic!("expected verified receipt, got {:?}", lh_ok.receipt);
    };
    let lh_assumptions: Vec<&str> =
        lh_verified.assumptions.iter().map(String::as_str).collect();
    assert!(
        !lh_assumptions.iter().any(|a| a.contains("as .aborted")),
        "local #[panic_handler] receipt must not claim .aborted modeling: {lh_assumptions:?}"
    );
}

#[cfg(unix)]
#[test]
fn expect_proof_failed_rejects_resource_limit_reasons() {
    use std::os::unix::process::ExitStatusExt;

    let make_outcome = |reason: Option<&str>| {
        let mut raw = json!({
            "schema_version": 3,
            "taint_reasons": [],
            "elaboration_sandbox": "linux_bwrap",
            "status": "proof_failed",
            "phase": "audit",
            "detail": "limit exceeded",
            "artifacts": null
        });
        if let Some(r) = reason {
            raw["reason"] = json!(r);
        }
        let stdout = serde_json::to_vec(&raw).unwrap();
        let receipt = VerifyReceipt::from_json_slice(&stdout).unwrap();
        VerifyOutcome {
            name: format!("synthetic-{reason:?}"),
            receipt,
            output: Output {
                status: std::process::ExitStatus::from_raw(1 << 8),
                stdout,
                stderr: Vec::new(),
            },
        }
    };

    // Ordinary `proof_failed` (absent `reason`) is credited.
    make_outcome(None).expect_proof_failed();

    // Resource-limit `proof_failed` must panic instead of crediting a kill.
    for reason in ["heartbeat_limit_exceeded", "recursion_depth_exceeded"] {
        let outcome = make_outcome(Some(reason));
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            outcome.expect_proof_failed();
        }));
        assert!(res.is_err(), "expect_proof_failed must refuse reason={reason}");
    }
}

/// Verifies a `#![forbid(unsafe_code)]` `&mut [u8]` slice pattern
/// (`matches!(s, [])`, lowered via `RawPtrKind::FakeForPtrMetadata` and
/// `UnOp::PtrMetadata`) end-to-end under `CrateTheoremV2` and
/// `BodySatisfiesSafeContractV2` (`["propext"]`, zero taint), while confirming
/// that a wrong functional postcondition fails audit and mixing `&mut [u8]`
/// with a real raw-pointer local is still refused at capture time.
#[test]
fn verifies_safe_mut_slice_pattern_via_fake_ptr_metadata() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    let safe_rust = "#![no_std]\n\
                     #![forbid(unsafe_code)]\n\n\
                     pub fn is_empty_mut_slice(s: &mut [u8]) -> bool {\n\
                         matches!(s, [])\n\
                     }\n";
    let spec_src = r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def isEmptyMutSliceContract : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := EffectMaskV2.noAbort
  postReturn := fun q out =>
    match q.args with
    | [.slicePtr _ len] =>
      out.ret = .bool (Nat.beq len.toNat 0) ∧
      out.callerMem = q.callerMem
    | _ => False
}

def property (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some body0 => BodySatisfiesSafeContractV2 p 0 body0 isEmptyMutSliceContract
  | none => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
"#;
    let proof_src = r#"prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Anneal.MirWp.V2StepShield
import Captured
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem decodeScalar_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  dsimp only
  have hMod : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact h)
  rw [hTr, hMod]
  rfl

private theorem int_ofNat_beq_eq_nat_beq (a b : Nat) :
    (Int.ofNat a == Int.ofNat b) = Nat.beq a b := by
  change decide (Int.ofNat a = Int.ofNat b) = Nat.beq a b
  cases hB : Nat.beq a b with
  | true =>
    have hEq : a = b := Nat.eq_of_beq_eq_true hB
    subst hEq
    exact decide_eq_true rfl
  | false =>
    exact decide_eq_false (fun hEq => by
      have hab : a = b := Int.ofNat.inj hEq
      subst hab
      rw [Nat.beq_refl] at hB
      cases hB)

private theorem evalBinOp_isize_eq {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) :
    evalBinOp .eq
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.bool (Nat.beq a b)) := by
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false (rfl : BinOp.eq.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb, int_ofNat_beq_eq_nat_beq]

private theorem initLocalsLoop_body0 (ptrAid : Option AllocId) (ptrOff len : UInt64) :
    initLocalsLoop Captured.body_0
      [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len]
      0 Captured.body_0.locals =
    [.immediate none,
     .immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)),
     .immediate none,
     .immediate none,
     .immediate none,
     .immediate none,
     .immediate none] :=
  rfl

private theorem is_empty_mut_slice_exec (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    execProgV2 (entryProgForBody Captured.program 0) 14 q
      (Spec.isEmptyMutSliceContract.post q) := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  let ⟨v0, hArgs1, hCheck0⟩ := checkArgsMatchV2_singleton_inv hMatch
  let ⟨ptr0, len, hV0, hPtrW⟩ := checkValV2_slice_u8_inv hCheck0
  subst hV0
  cases ptr0 with
  | mk ptrAid ptrOff ptrW =>
    dsimp only at hPtrW
    subst hPtrW
    let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
    let m : MemoryState := entryMemoryWithCaller q.callerMem
    have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
      cases q; dsimp only at hArgs1; rw [hArgs1]
    have hRefValid0 :
        refValidInMem m .mut (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok () := by
      have hRefs' :
          refsValidInMemList m
            [.ref .mut (.slice (.int .i8 false))]
            [.slicePtr ptr len] = true := by
        rw [← hArgs1]; exact hRefs
      dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
      cases hR : refValidInMem m .mut (.slice (.int .i8 false)) (.slicePtr ptr len) with
      | error _ => rw [hR] at hRefs'; cases hRefs'
      | ok u => cases u; rfl
    have hLenLt64 : len.toNat < Nat.pow 2 64 := len.toBitVec.isLt
    have hTr : truncateBits .isize (BitVec.ofNat 128 len.toNat) = BitVec.ofNat 128 len.toNat :=
      truncateBits_ofNat_of_lt .isize hLenLt64
    have hWfLen :
        checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 len.toNat⟩)
          (.int .isize false) = true := by
      unfold checkValV2 checkVal Val.ty? ScalarVal.wf
      dsimp only
      rw [hTr, beq_self_eq_true]
      rfl
    have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
      extractCallerMemory_entry q.callerMem hCM
    let ctx : BodyCtx := ⟨Captured.program, 0, Captured.body_0⟩
    have h_body : ctx.HasBody := rfl
    have hValid' : ValidEntryArgsV2 Captured.body_0 ⟨[.slicePtr ptr len], q.callerMem⟩ := by
      rw [← hQ]; exact hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.slicePtr ptr len], q.callerMem⟩ =
        .ok (State.mk [FrameState.mk 0 0 0
          [.immediate none,
           .immediate (some (.slicePtr ptr len)),
           .immediate none,
           .immediate none,
           .immediate none,
           .immediate none,
           .immediate none]
          none none none]
          q.callerMem m) := by
      have h0 := ctx.initStateV2_ok_of h_body (by decide) hValid'
      change initStateV2 ctx.entryProg _ = _
      rw [h0]
      change Except.ok (State.mk [FrameState.mk 0 0 0
        (initLocalsLoop Captured.body_0
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len]
          0 Captured.body_0.locals) none none none] q.callerMem m) = _
      rw [initLocalsLoop_body0]
    rw [hQ]
    unfold execProgV2
    rw [hInit]
    -- bb0 stmt 0: PlaceMention(_1) -> nop
    apply execOutcomeStateV2_step (by rfl)
    -- bb0 stmt 1: _3 = &raw const (fake) (*_1)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalFakeAddressOfRvalueV2, writePlaceDestV2, checkValV2,
        Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
      rw [hRefValid0]
      rfl)
    -- bb0 stmt 2: _4 = PtrMetadata(move _3)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!(MirTy.int IntWidth.isize false).beq (MirTy.int IntWidth.isize false)) = false)]
      rw [hTr]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hWfLen (by rfl) (by rfl)])
    -- bb0 stmt 3: _2 = Use(move _4)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, isMemoryCopyReprTyV2, copyReprOfTyV2,
        evalRvalueV2, evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!(MirTy.int IntWidth.isize false).beq (MirTy.int IntWidth.isize false)) = false)]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hWfLen (by rfl) (by rfl)]
      rfl)
    -- bb0 stmt 4: _5 = Use(const 0_usize)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalOperandToSlotV2, evalConstLit, Trusted.MirSemantics.getElem?]
      rw [ite_bool_false (by decide : (truncateBits .isize (BitVec.ofNat 128 0) != BitVec.ofNat 128 0) = false)]
      rw [truncateBits_ofNat_of_lt .isize (by decide : 0 < intWidthModulus .isize)]
      dsimp only
      rw [ite_bool_false (rfl : (!(MirTy.int IntWidth.isize false).beq (MirTy.int IntWidth.isize false)) = false)]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)])
    -- bb0 stmt 5: _6 = Eq(move _2, move _5)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalPrimitiveOperandV2, evalOperandToSlotV2,
        Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [evalBinOp_isize_eq hLenLt64 (by decide)]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
    have hConst0 : evalConstLit .bool (.scalar (BitVec.ofNat 128 0)) = .ok (.bool false) := by
      unfold evalConstLit; dsimp only
      rw [ite_bool_false (by decide), ite_bool_true (by decide)]
    have hConst1 : evalConstLit .bool (.scalar (BitVec.ofNat 128 1)) = .ok (.bool true) := by
      unfold evalConstLit; dsimp only
      rw [ite_bool_false (by decide), ite_bool_false (by decide), ite_bool_true (by decide)]
    -- bb0 term: SwitchInt(move _6) -> [0: bb1, otherwise: bb2]
    cases hEmpty : Nat.beq len.toNat 0 with
    | false =>
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalPrimitiveOperandV2, evalOperandToSlotV2,
          evalBoolSwitchBranches, jumpToBlock, List.length, Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (rfl : Nat.beq 6 6 = true)]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false)]
        dsimp only
        rw [hConst0]
        rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
          checkAssignCopyHazardV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [hConst0]
        dsimp only
        rw [ite_bool_false (rfl : (!MirTy.bool.beq MirTy.bool) = false)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
          (by rfl) (by rfl) (by rfl),
          extractReturnMemoryV2_entryMemory, hExt]
        rfl)
      exact ⟨by rw [hEmpty], rfl⟩
    | true =>
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalPrimitiveOperandV2, evalOperandToSlotV2,
          evalBoolSwitchBranches, jumpToBlock, List.length, Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (rfl : Nat.beq 6 6 = true)]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false)]
        dsimp only
        rw [hConst0]
        rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
          checkAssignCopyHazardV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [hConst1]
        dsimp only
        rw [ite_bool_false (rfl : (!MirTy.bool.beq MirTy.bool) = false)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
          (by rfl) (by rfl) (by rfl),
          extractReturnMemoryV2_entryMemory, hExt]
        rfl)
      exact ⟨by rw [hEmpty], rfl⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
      exact (wellFormed_and_spec_of_execV2_base
        (entryProgForBody Captured.program 0) q 14
        (Spec.isEmptyMutSliceContract.post q)
        (is_empty_mut_slice_exec q hValid)).1.1
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · exact safeContract_soundness_of_execV2_base.2.1
      Captured.program 0 Captured.body_0 Spec.isEmptyMutSliceContract
      rfl (by decide)
      (fun q hValid _ => ⟨14, is_empty_mut_slice_exec q hValid⟩)

end Proof
"#;

    fs::write(rust_dir.join("lib.rs"), safe_rust).unwrap();
    fs::write(lean_dir.join("Spec.lean"), spec_src).unwrap();
    fs::write(lean_dir.join("Proof.lean"), proof_src).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "fake_ptr_meta_demo",
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

    let ok = run_request(dir.path(), "fake-ptr-meta-ok", &request);
    ok.expect_ok("crate_verified");
    ok.expect_profile_v2_assumptions();
    let capture_dir = dir.path().join("artifacts-fake-ptr-meta-ok/capture");
    let capture_json: Value =
        serde_json::from_slice(&fs::read(capture_dir.join("capture.json")).unwrap()).unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    let captured_lean = fs::read_to_string(capture_dir.join("Captured.lean")).unwrap();
    assert!(
        captured_lean.contains("Trusted.MirAst.Rvalue.fakeAddressOf"),
        "expected Rvalue.fakeAddressOf in Captured.lean:\n{captured_lean}"
    );

    // Negative 1 (audit): inverted emptiness postcondition must fail closed.
    let bad_spec = spec_src.replace("Nat.beq len.toNat 0", "!(Nat.beq len.toNat 0)");
    assert_ne!(bad_spec, spec_src);
    fs::write(lean_dir.join("Spec.lean"), bad_spec).unwrap();
    run_request(dir.path(), "fake-ptr-meta-wrong-spec", &request).expect_proof_failed();

    // Negative 2 (capture): adding a real raw-pointer local alongside
    // `&mut [u8]` must still fail closed with the mixed-locals refusal. The
    // local is `*mut`: a non-argument `*const P` local may still be promoted
    // to `BoxAsRef`, so its mixing refusal runs only after call lowering,
    // which rejects `core::ptr::null` first.
    fs::write(lean_dir.join("Spec.lean"), spec_src).unwrap();
    fs::write(
        rust_dir.join("lib.rs"),
        "#![no_std]\n\
         pub fn is_empty_mut_slice(s: &mut [u8]) -> bool {\n\
             let _real_raw: *mut u8 = core::ptr::null_mut();\n\
             matches!(s, [])\n\
         }\n",
    )
    .unwrap();
    run_request(dir.path(), "fake-ptr-meta-real-raw-mixed", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Profile v2 E2E test for Slice 1B `core` contracts (`Range<usize>` subslice,
/// `Option` unwrap/is_some/take/discriminant/downcast, scalar checked,
/// saturating, min, shift, leading_zeros, and `is_multiple_of`,
/// `slice::is_empty`, and `core::mem::replace`).
#[test]
fn verifies_core_contracts_and_rejects_missing_preconditions() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), CORE_CONTRACTS_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), CORE_CONTRACTS_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), CORE_CONTRACTS_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "profile_v2_core_contracts",
            "edition": "2024",
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
                {"module": "Spec", "path": "Spec.lean",
                 "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let ok = run_request(dir.path(), "core-contracts-ok", &request);
    ok.expect_ok("crate_verified");
    let cap_json_path = dir
        .path()
        .join("artifacts-core-contracts-ok/capture/capture.json");
    let capture_json: Value =
        serde_json::from_slice(&fs::read(cap_json_path).unwrap()).unwrap();
    assert_eq!(
        capture_json["program"]["mir_profile_version"], 2,
        "{capture_json}"
    );

    // Positive/negative twins for runtime `corePanicTrap` obligations: in each
    // pair `lib.rs` and `Proof.lean` are identical, Component 7
    // (`BodyVerifiedV2`) is fully discharged with zero metavariables against
    // `safetyPre := (· = okQuery)`, and only `Spec.testQuery` / `expectedOut`
    // changes from an admitted query (`expect_ok`) to a trapping query that
    // fails `rfl` on `BehaviorV2` (`corePanicTrap`).
    const TWIN_PROOF: &str = "\
prelude
import Spec
import Expected
import Anneal.MirWp
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp
theorem verify : Expected.claim := by
  have _ : ValidEntryArgsV2 Captured.body_0 Spec.okQuery :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hOk :=
    spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.okQuery)
      (out := Spec.okOut)
      (fuel := 30) rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      cases hBody
      refine ⟨rfl, rfl, fun q _ hSafe => ?_⟩
      have hEq : q = Spec.okQuery := hSafe rfl
      cases hEq
      exact hOk.1
    | succ _ => cases hBody
  · refine ⟨0, Captured.body_0, rfl, rfl, ?_⟩
    exact (spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.testQuery)
      (out := Spec.expectedOut)
      (fuel := 30) rfl).2.1
end Proof
";

    let run_trap_twin = |subdir: &str,
                         crate_name: &str,
                         rust_src: &str,
                         pos_name: &str,
                         pos_spec: &str,
                         neg_name: &str,
                         neg_spec: &str| {
        let sub_dir = dir.path().join(subdir);
        let sub_rust = sub_dir.join("rust");
        let sub_lean = sub_dir.join("lean");
        fs::create_dir_all(&sub_rust).unwrap();
        fs::create_dir_all(&sub_lean).unwrap();
        fs::write(sub_rust.join("lib.rs"), rust_src).unwrap();
        fs::write(sub_lean.join("Proof.lean"), TWIN_PROOF).unwrap();
        let req = json!({
            "schema_version": 1,
            "compilation": {
                "source_root": sub_rust.to_str().unwrap(),
                "crate_root": "lib.rs",
                "crate_name": crate_name,
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {
                "source_root": sub_lean.to_str().unwrap(),
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"}
                ]
            }
        });
        fs::write(sub_lean.join("Spec.lean"), pos_spec).unwrap();
        run_request(dir.path(), pos_name, &req).expect_ok("crate_verified");

        fs::write(sub_lean.join("Spec.lean"), neg_spec).unwrap();
        let neg = run_request(dir.path(), neg_name, &req);
        neg.expect_proof_failed();
        let detail = match &neg.receipt {
            VerifyReceipt::Failed(failure) => failure.detail.as_str(),
            VerifyReceipt::Verified(_) => "",
        };
        assert!(
            !detail.contains("command parser error")
                && !detail.contains("don't know how to synthesize")
                && !detail.contains("unassigned")
                && !detail.contains("Spec.okQuery"),
            "{neg_name} failed outside Spec.testQuery evaluation:\n{:?}",
            neg.receipt
        );
        assert!(
            detail.contains("Spec.testQuery")
                && detail.contains("execProgV2")
                && (detail.contains("Application type mismatch")
                    || detail.contains("not definitionally equal")
                    || detail.contains("Tactic `rfl` failed")),
            "{neg_name} did not fail on `rfl` over Spec.testQuery:\n{:?}",
            neg.receipt
        );
    };

    const SUBSLICE_SPEC_TMPL: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args :=
      [.slicePtr ⟨some 2, 0, .isize⟩ 2,
       .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩,
       .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩],
    callerMem :=
      ⟨[{ allocId := 2, alignLog2 := 0, mutability := .shared,
          bytes := [AllocByte.init 10 none, AllocByte.init 20 none],
          live := true }]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, 0, .isize⟩ 1, okQuery.callerMem⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, __OUT_OFF__, .isize⟩ 1, testQuery.callerMem⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::subslice\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    let subslice_pos = SUBSLICE_SPEC_TMPL
        .replace("__TEST_QUERY__", "okQuery")
        .replace("__OUT_OFF__", "0");
    let subslice_oob = SUBSLICE_SPEC_TMPL
        .replace(
            "__TEST_QUERY__",
            "\n\
             \x20 { args :=\n\
             \x20     [.slicePtr ⟨some 2, 0, .isize⟩ 2,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 3⟩,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 4⟩],\n\
             \x20   callerMem := okQuery.callerMem }",
        )
        .replace("__OUT_OFF__", "3");
    run_trap_twin(
        "subslice_twin",
        "subslice_trap_twin",
        "pub unsafe fn subslice<'a>(s: &'a [u8], a: usize, b: usize) -> &'a [u8] {\n    &s[a..b]\n}\n",
        "core-contracts-inbounds-subslice",
        &subslice_pos,
        "core-contracts-oob-subslice",
        &subslice_oob,
    );

    const SUBSLICE_OPT_SPEC_TMPL: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def noneOptU64Bytes : List AllocByte :=
  List.replicate 8 (AllocByte.init 0 none) ++
    List.replicate 8 AllocByte.uninit
def some42OptU64Bytes : List AllocByte :=
  (AllocByte.init 1 none :: List.replicate 7 (AllocByte.init 0 none)) ++
    (AllocByte.init 42 none :: List.replicate 7 (AllocByte.init 0 none))
def okQuery : Query :=
  { args :=
      [.slicePtr ⟨some 2, 0, .isize⟩ 2,
       .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩,
       .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩],
    callerMem :=
      ⟨[{ allocId := 2, alignLog2 := 3, mutability := .shared,
          bytes := noneOptU64Bytes ++ some42OptU64Bytes,
          live := true }]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, 0, .isize⟩ 1, okQuery.callerMem⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, __OUT_OFF__, .isize⟩ 1, testQuery.callerMem⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::subslice_opt\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    let subslice_opt_pos = SUBSLICE_OPT_SPEC_TMPL
        .replace("__TEST_QUERY__", "okQuery")
        .replace("__OUT_OFF__", "0");
    let subslice_opt_oob = SUBSLICE_OPT_SPEC_TMPL
        .replace(
            "__TEST_QUERY__",
            "\n\
             \x20 { args :=\n\
             \x20     [.slicePtr ⟨some 2, 0, .isize⟩ 2,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 3⟩],\n\
             \x20   callerMem := okQuery.callerMem }",
        )
        .replace("__OUT_OFF__", "32");
    run_trap_twin(
        "subslice_opt_twin",
        "subslice_opt_trap_twin",
        "pub unsafe fn subslice_opt<'a>(s: &'a [Option<u64>], a: usize, b: usize) -> &'a [Option<u64>] {\n    &s[a..b]\n}\n",
        "core-contracts-inbounds-subslice-opt-none",
        &subslice_opt_pos,
        "core-contracts-oob-subslice-opt-none",
        &subslice_opt_oob,
    );

    const UNWRAP_SPEC_TMPL: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args := [.optionVal (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩))],
    callerMem := ⟨[]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩, ⟨[]⟩⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 __OUT_VAL__⟩, ⟨[]⟩⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::opt_unwrap\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    let unwrap_pos = UNWRAP_SPEC_TMPL
        .replace("__TEST_QUERY__", "okQuery")
        .replace("__OUT_VAL__", "7");
    let unwrap_none = UNWRAP_SPEC_TMPL
        .replace("__TEST_QUERY__", "{ args := [.optionVal none], callerMem := ⟨[]⟩ }")
        .replace("__OUT_VAL__", "0");
    run_trap_twin(
        "unwrap_twin",
        "unwrap_trap_twin",
        "pub unsafe fn opt_unwrap(x: Option<u64>) -> u64 {\n    x.unwrap()\n}\n",
        "core-contracts-some-unwrap",
        &unwrap_pos,
        "core-contracts-none-unwrap",
        &unwrap_none,
    );

    // Negative 3: mutate `subslicePost` length (`b - a` -> `b - a + 1`) against
    // unmodified `Proof.lean`, failing purely on the unprovable postcondition.
    let bad_post = CORE_CONTRACTS_SPEC.replace(
        "UInt64.ofNat (bSv.bits.toNat - aSv.bits.toNat)",
        "UInt64.ofNat (bSv.bits.toNat - aSv.bits.toNat + 1)",
    );
    assert_ne!(bad_post, CORE_CONTRACTS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_post).unwrap();
    let neg3_name = "core-contracts-wrong-postcondition";
    run_request(dir.path(), neg3_name, &request).expect_proof_failed();
}

/// End-to-end verification of `assert!(dst < 16)` (`ebpf_core`
/// `EbpfInstruction::new` static `&str` `core::panicking::panic` pattern)
/// aborting under `--panic abort` (`CoreCallOp.panicAbort [rodataRef]`),
/// rejection under `--panic unwind`, `EffectMaskV2.noAbort`, crate-local
/// `#[panic_handler]`, and formatted `assert!(cond, "bad cond")`, plus
/// Profile v1 verification of `x / 16` with its verbatim preserved
/// `TerminatorKind.assert` (`AssertKind.divByZero`).
#[test]
fn verifies_ebpf_assert_aborts_under_panic_abort_and_const_div_stays_v1() {
    let tools = tools();
    let dir = TempDir::new().unwrap();

    // Check 1a: `check_ebpf_reg(dst: u8) -> u8` (`assert!(dst < 16); dst`)
    // verifies `SafeContractV2` under `--panic abort` (`dst >= 16` evaluates
    // the static `&str` `.rodataRef` message and steps to `.aborted cm`,
    // `dst < 16` returns `dst` with unchanged `cm`).
    let rust_dir = dir.path().join("ebpf-reg-rust");
    let lean_dir = dir.path().join("ebpf-reg-lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn check_ebpf_reg(dst: u8) -> u8 {\n\
             assert!(dst < 16);\n\
             dst\n\
         }\n",
    )
    .unwrap();
    fs::write(
        lean_dir.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def ebpfRegAllowAbort : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := { allowAbort := true }
  postReturn := fun q out =>
    match q.args with
    | [.scalar v] =>
      v.bits.toNat < 16 ∧ out.ret = .scalar v ∧ out.callerMem = q.callerMem
    | _ => False
  postAbort := fun q cm =>
    match q.args with
    | [.scalar v] => 16 ≤ v.bits.toNat ∧ cm = q.callerMem
    | _ => False
}

def property (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some body0 => BodySatisfiesSafeContractV2 p 0 body0 ebpfRegAllowAbort
  | none => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
"#,
    )
    .unwrap();
    fs::write(
        lean_dir.join("Proof.lean"),
        r#"prelude
import Init.NotationExtra
import Init.Data.Nat.Lemmas
import Init.Data.Int.Order
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem execOutcomeStateV2_step {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execOutcomeStateV2 p onDone onFault fuel s') :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hNext

private theorem execOutcomeStateV2_done {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out)
    (hDone : onDone out) :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hDone

private theorem allocId_le_maxAllocId {allocs : List Allocation} {a : Allocation}
    (h : a ∈ allocs) :
    a.allocId ≤ maxAllocId allocs := by
  induction allocs with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head _ =>
      change a.allocId ≤ Nat.max a.allocId (maxAllocId xs)
      exact Nat.le_max_left _ _
    | tail _ hIn =>
      change a.allocId ≤ Nat.max x.allocId (maxAllocId xs)
      exact Nat.le_trans (ih hIn) (Nat.le_max_right _ _)

private theorem findAllocation_cons_ne {aid : AllocId} {x : Allocation}
    {xs : List Allocation} (hNe : x.allocId ≠ aid) :
    findAllocation aid (x :: xs) = findAllocation aid xs := by
  change (if Nat.beq x.allocId aid then some x else findAllocation aid xs) =
    findAllocation aid xs
  cases hEq : Nat.beq x.allocId aid with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe

private theorem extractCallerMemory_cons_fresh {cm : CallerMemory}
    {x : Allocation} (hGt : maxAllocId cm.allocations < x.allocId)
    {next : AllocId} :
    extractCallerMemory cm { nextAllocId := next, allocations := x :: cm.allocations } =
      extractCallerMemory cm (entryMemoryWithCaller cm) := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    apply congrArg CallerMemory.mk
    have hEq : ∀ suff : List Allocation,
        (∀ a, a ∈ suff → a.allocId ≤ maxAllocId allocs) →
        extractCallerAllocations
          { nextAllocId := next, allocations := x :: allocs } suff =
          extractCallerAllocations (entryMemoryWithCaller ⟨allocs⟩) suff := by
      intro suff hBound
      induction suff with
      | nil => rfl
      | cons a rest ih =>
        unfold extractCallerAllocations
        have hLe : a.allocId ≤ maxAllocId allocs := hBound a (.head _)
        have hNe : x.allocId ≠ a.allocId :=
          Nat.ne_of_gt (Nat.lt_of_le_of_lt hLe hGt)
        rw [findAllocation_cons_ne hNe]
        change (findAllocation a.allocId allocs).getD a :: _ = _
        rw [ih (fun b hb => hBound b (.tail _ hb))]
        rfl
    exact hEq allocs (fun a ha => allocId_le_maxAllocId ha)

private theorem checkVal_u8_inv {v : Val}
    (h : checkValV2 v (.int .i8 false) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨.i8, false, bits⟩ ∧
      ScalarVal.wf ⟨.i8, false, bits⟩ = true ∧
      (!checkValV2 (.scalar ⟨.i8, false, bits⟩) (.int .i8 false)) = false := by
  cases v with
  | scalar sv =>
    cases sv with
    | mk w sg bits =>
      have h' :
          (match (if ScalarVal.wf { width := w, signed := sg, bits := bits } =
              true then some (MirTy.int w sg) else none) with
            | some vTy => vTy.beq (.int .i8 false)
            | none => false) = true := h
      cases hWf : ScalarVal.wf { width := w, signed := sg, bits := bits } with
      | false => rw [hWf] at h'; cases h'
      | true =>
        rw [hWf] at h'
        cases w <;> cases sg <;> cases h'
        exact ⟨bits, rfl, hWf, by rw [h]; rfl⟩
  | _ => first | cases h | (rename_i o; cases o <;> cases h)

private theorem checkArgs_u8 {args : List Val}
    (h : checkArgsMatchV2 args [.int .i8 false] = true) :
    ∃ bits : BitVec 128,
      args = [.scalar ⟨.i8, false, bits⟩] ∧
      ScalarVal.wf ⟨.i8, false, bits⟩ = true ∧
      (!checkValV2 (.scalar ⟨.i8, false, bits⟩) (.int .i8 false)) = false := by
  cases args with
  | nil => cases h
  | cons a0 rest =>
    cases rest with
    | cons a1 rest1 =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.int .i8 false) <;> rw [h0] at h <;> cases h
    | nil =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.int .i8 false) with
      | false => rw [h0] at h; cases h
      | true =>
        let ⟨bits, hEq, hWf, hNot⟩ := checkVal_u8_inv h0
        exact ⟨bits, by rw [hEq], hWf, hNot⟩

private theorem rm2_natNotElem_false_of_mem {x : Nat} {xs : List Nat}
    (h : x ∈ xs) : natNotElem x xs = false := by
  induction h with
  | head _ =>
    unfold natNotElem
    rw [Nat.beq_refl]
    rfl
  | tail _ _ ih =>
    unfold natNotElem
    rw [ih, Bool.and_false]

private theorem rm2_mem_allocIdsOf {a : Allocation} {l : List Allocation}
    (h : a ∈ l) : a.allocId ∈ allocIdsOf l := by
  induction h with
  | head _ => unfold allocIdsOf; exact .head _
  | tail _ _ ih => unfold allocIdsOf; exact .tail _ ih

private theorem rm2_calleeLive_nil_of_sub {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    rw [rm2_natNotElem_false_of_mem (h a (.head _)), Bool.and_false,
      Bool.false_and]
    exact rm2_calleeLive_nil_of_sub (fun b hb => h b (.tail _ hb))

/-- Returning from an unmodified entry memory exposes no callee-created heap
allocation, so the Profile v2 return memory is the extracted caller memory. -/
private theorem rm2_extractReturnMemoryV2_entry (cm : CallerMemory)
    (locals : List LocalSlot) :
    extractReturnMemoryV2 cm (entryMemoryWithCaller cm) locals =
      extractCallerMemory cm (entryMemoryWithCaller cm) := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_sub (ids := allocIdsOf cm.allocations)
      (l := (entryMemoryWithCaller cm).allocations)
      (fun _ ha => rm2_mem_allocIdsOf (l := cm.allocations) ha),
    List.append_nil]

private def mkS (bb st : Nat) (locs : List LocalSlot)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  ⟨[⟨0, bb, st, locs, none, none, none⟩], cm, mem⟩

private theorem body0_static_admitted :
    BodyStaticAdmittedV2 Captured.program Captured.body_0 = true := by
  decide

private theorem ite_bool_false {α : Type _} {b : Bool} {t e : α}
    (h : b = false) :
    (if b = true then t else e) = e := by
  rw [h]; rfl

private theorem body0_safeContract :
    BodySatisfiesSafeContractV2 Captured.program 0 Captured.body_0
      Spec.ebpfRegAllowAbort := by
  refine safeContract_soundness_of_execV2_base.2.1
    Captured.program 0 Captured.body_0 Spec.ebpfRegAllowAbort
    rfl body0_static_admitted (fun q hValid _ => ?_)
  cases q with
  | mk args cm =>
    let ⟨hMem, hArgs, _, _⟩ := hValid
    let ⟨bits, hEq, hWf, hSv⟩ := checkArgs_u8 hArgs
    subst hEq
    let sv : ScalarVal := ⟨.i8, false, bits⟩
    have hTr : truncateBits .i8 bits = bits := by
      unfold ScalarVal.wf at hWf
      exact eq_of_beq hWf
    let mem := entryMemoryWithCaller cm
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar sv], cm⟩ =
        .ok (mkS 0 0
          [.immediate none, .immediate (some (.scalar sv)),
           .dead, .dead, .dead, .dead]
          cm mem) :=
      initStateV2_ok_of_admitted (p := entryProgForBody Captured.program 0)
        rfl body0_static_admitted hValid
    have hCopy4 :
        evalStepV2 (entryProgForBody Captured.program 0)
          (mkS 0 3 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate none, .immediate none, .dead] cm mem) =
        .step (mkS 0 4 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate none,
            .immediate (some (.scalar sv)), .dead] cm mem) := by
      change (match (if (!checkValV2 (Val.scalar sv) (MirTy.int IntWidth.i8 false)) = true then
          Except.error FaultKind.unsupported
        else
          Except.ok
            ([LocalSlot.immediate none, LocalSlot.immediate (some (Val.scalar sv)),
              LocalSlot.immediate (some Val.unit), LocalSlot.immediate none,
              LocalSlot.immediate (some (Val.scalar sv)), LocalSlot.dead], mem)) with
        | Except.error k => StepResult.fault k
        | Except.ok (locals', mem') => StepResult.step (mkS 0 4 locals' cm mem')) = _
      rw [hSv]
      rfl
    let bLt : Bool :=
      decide (Int.ofNat (truncateBits .i8 bits).toNat < Int.ofNat 16)
    have hLtStep :
        evalStepV2 (entryProgForBody Captured.program 0)
          (mkS 0 4 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate none,
            .immediate (some (.scalar sv)), .dead] cm mem) =
        .step (mkS 0 5 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate (some (.bool bLt)),
            .immediate none, .dead] cm mem) := by
      have hBin :
          evalBinOp .lt (.scalar sv)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 16⟩) =
          .ok (.bool bLt) := rfl
      change (match (match evalBinOp .lt (.scalar sv)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 16⟩) with
          | Except.error k => Except.error k
          | Except.ok res =>
            Except.ok (res,
              [LocalSlot.immediate none, LocalSlot.immediate (some (Val.scalar sv)),
               LocalSlot.immediate (some Val.unit), LocalSlot.immediate none,
               LocalSlot.immediate none, LocalSlot.dead], mem)) with
        | Except.error k => StepResult.fault k
        | Except.ok (val, locals1, mem1) =>
          match writePlaceDestV2 locals1 mem1 (.local 3) .bool val with
          | Except.error k => StepResult.fault k
          | Except.ok (locals2, mem2) =>
            StepResult.step (mkS 0 5 locals2 cm mem2)) = _
      rw [hBin]
      have hChkBool : (!checkValV2 (.bool bLt) .bool) = false := by
        cases bLt <;> rfl
      change (match (if (!checkValV2 (.bool bLt) .bool) = true then
            Except.error FaultKind.unsupported
          else
            Except.ok
              ([LocalSlot.immediate none, LocalSlot.immediate (some (Val.scalar sv)),
                LocalSlot.immediate (some Val.unit),
                LocalSlot.immediate (some (Val.bool bLt)),
                LocalSlot.immediate none, LocalSlot.dead], mem)) with
        | Except.error k => StepResult.fault k
        | Except.ok (locals2, mem2) =>
          StepResult.step (mkS 0 5 locals2 cm mem2)) = _
      rw [hChkBool]
      rfl
    cases hBLt : bLt with
    | false =>
      have hGe16 : 16 ≤ bits.toNat := by
        have hNotLtI : ¬ (Int.ofNat (truncateBits .i8 bits).toNat < Int.ofNat 16) :=
          of_decide_eq_false hBLt
        rw [hTr] at hNotLtI
        have hNotLt : ¬ (bits.toNat < 16) := fun h => hNotLtI (Int.ofNat_lt.mpr h)
        exact Nat.le_of_not_lt hNotLt
      refine ⟨10, ?_⟩
      unfold execProgV2
      rw [hInit]
      refine execOutcomeStateV2_step (s' := mkS 0 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .dead, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 3
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step hCopy4 ?_
      have hLtStepF := hLtStep
      rw [hBLt] at hLtStepF
      refine execOutcomeStateV2_step hLtStepF ?_
      refine execOutcomeStateV2_step (s' := mkS 2 0
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 2 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 2 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .immediate none] cm mem) rfl ?_
      let roRawBytes : List RodataByte :=
        List.append
          [RodataByte.init 97, RodataByte.init 115, RodataByte.init 115,
           RodataByte.init 101, RodataByte.init 114, RodataByte.init 116,
           RodataByte.init 105, RodataByte.init 111, RodataByte.init 110,
           RodataByte.init 32, RodataByte.init 102, RodataByte.init 97,
           RodataByte.init 105, RodataByte.init 108, RodataByte.init 101,
           RodataByte.init 100]
          [RodataByte.init 58, RodataByte.init 32, RodataByte.init 100,
           RodataByte.init 115, RodataByte.init 116, RodataByte.init 32,
           RodataByte.init 60, RodataByte.init 32, RodataByte.init 49,
           RodataByte.init 54]
      let roAid : AllocId := mem.nextAllocId
      let roAlloc : Allocation := {
        allocId := roAid
        bytes := roRawBytes.map rodataByteToAllocByte
        alignLog2 := 0
        mutability := .shared
        live := true
      }
      let mem1 : MemoryState := {
        nextAllocId := roAid + 1
        allocations := roAlloc :: mem.allocations
      }
      have hFindRo : findAllocation roAid mem1.allocations = some roAlloc := by
        change (if Nat.beq roAid roAid then some roAlloc else _) = some roAlloc
        rw [Nat.beq_refl]; rfl
      have hRefRo :
          refValidInMem mem1 .shared .str
            (.slicePtr ⟨some roAid, UInt64.ofNat 0, .isize⟩ (UInt64.ofNat 26)) =
          .ok () := by
        dsimp only [refValidInMem, sliceFromRawPartsCheck, sliceRefRawCheck]
        rw [hFindRo]
        rfl
      have hUtf8Ro :
          (!strSliceUtf8InMem mem1 ⟨some roAid, UInt64.ofNat 0, .isize⟩
            (UInt64.ofNat 26)) = false := by
        dsimp only [strSliceUtf8InMem]
        rw [hFindRo]
        rfl
      let roConst : ConstOperand :=
        ⟨.ref .shared .str, .rodataRef roRawBytes 0 0 (some 26)⟩
      let abortLocals : List LocalSlot :=
        [.immediate none, .immediate (some (.scalar sv)),
         .immediate (some .unit), .immediate none, .dead, .immediate none]
      have hRodata :
          evalOperandToSlotV2 Captured.body_0.locals abortLocals mem
            (.constant roConst) =
          .ok (.ref .shared .str,
            some (.slicePtr ⟨some roAid, UInt64.ofNat 0, .isize⟩
              (UInt64.ofNat 26)),
            abortLocals, mem1) := by
        dsimp only [evalOperandToSlotV2, evalRodataRefConstV2, roConst,
          allocRodataMemory, MemoryState.reserveAllocId]
        have hG1 :
            (!Nat.blt roRawBytes.length isizeMaxBytes ||
              !Nat.ble 0 29 || !Nat.blt 0 (Nat.pow 2 64)) = false := by
          decide
        have hG2 : (!Nat.blt 26 (Nat.pow 2 64)) = false := by decide
        have hG3 : Mutability.beq .shared .mut = false := rfl
        rw [ite_bool_false hG1, ite_bool_false hG2, ite_bool_false hG3, hRefRo]
        dsimp only
        rw [ite_bool_false hUtf8Ro]
      have hAbortStep :
          evalStepV2 (entryProgForBody Captured.program 0)
            (mkS 2 2 abortLocals cm mem) =
          .done (.aborted (extractCallerMemory cm mem1)) := by
        change (match (match evalOperandToSlotV2 Captured.body_0.locals
              abortLocals mem (.constant roConst) with
            | Except.error k => Except.error k
            | Except.ok (_, none, _, _) => Except.error FaultKind.undefined
            | Except.ok (ty, some v, locals1, mem1') =>
              Except.ok ([(ty, v)], locals1, mem1')) with
          | Except.error k => StepResult.fault k
          | Except.ok (typedArgs, _, mem1') =>
            match validatePanicAbortArgs mem1' typedArgs with
            | Except.error k => StepResult.fault k
            | Except.ok () =>
              evalCorePanicAbort .abort .unreachable
                (extractCallerMemory cm mem1') false) = _
        rw [hRodata]
        dsimp only [validatePanicAbortArgs, IntWidth.beq]
        rw [hRefRo]
        dsimp only
        rw [ite_bool_false hUtf8Ro]
        rfl
      have hRoGt : maxAllocId cm.allocations < roAid := by
        change maxAllocId cm.allocations <
          Nat.max entryMemory.nextAllocId (maxAllocAndProvId cm.allocations + 1)
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_left _ _))
          (Nat.le_max_right _ _)
      have hCmEq : extractCallerMemory cm mem1 = cm :=
        (extractCallerMemory_cons_fresh hRoGt).trans
          (extractCallerMemory_entry cm hMem)
      exact execOutcomeStateV2_done hAbortStep ⟨rfl, hGe16, hCmEq⟩
    | true =>
      have hLt16 : bits.toNat < 16 := by
        have hLtI : Int.ofNat (truncateBits .i8 bits).toNat < Int.ofNat 16 :=
          of_decide_eq_true hBLt
        rw [hTr] at hLtI
        exact Int.ofNat_lt.mp hLtI
      refine ⟨15, ?_⟩
      unfold execProgV2
      rw [hInit]
      refine execOutcomeStateV2_step (s' := mkS 0 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .dead, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 3
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step hCopy4 ?_
      have hLtStepT := hLtStep
      rw [hBLt] at hLtStepT
      refine execOutcomeStateV2_step hLtStepT ?_
      refine execOutcomeStateV2_step (s' := mkS 1 0
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 3
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .dead, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 4
        [.immediate none, .immediate (some (.scalar sv)),
         .dead, .dead, .dead, .dead] cm mem) rfl ?_
      have hWrite0 :
          evalStepV2 (entryProgForBody Captured.program 0)
            (mkS 1 4 [.immediate none, .immediate (some (.scalar sv)),
              .dead, .dead, .dead, .dead] cm mem) =
          .step (mkS 1 5 [.immediate (some (.scalar sv)),
              .immediate (some (.scalar sv)),
              .dead, .dead, .dead, .dead] cm mem) := by
        change (match (if (!checkValV2 (Val.scalar sv) (MirTy.int IntWidth.i8 false)) = true then
            Except.error FaultKind.unsupported
          else
            Except.ok
              ([LocalSlot.immediate (some (Val.scalar sv)),
                LocalSlot.immediate (some (Val.scalar sv)),
                LocalSlot.dead, LocalSlot.dead, LocalSlot.dead, LocalSlot.dead], mem)) with
          | Except.error k => StepResult.fault k
          | Except.ok (locals', mem') => StepResult.step (mkS 1 5 locals' cm mem')) = _
        rw [hSv]
        rfl
      refine execOutcomeStateV2_step hWrite0 ?_
      exact execOutcomeStateV2_done rfl ⟨hLt16, rfl,
        (rm2_extractReturnMemoryV2_entry cm _).trans
          (extractCallerMemory_entry cm hMem)⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      exact ⟨rfl, body0_static_admitted, fun q hValid _ =>
        (body0_safeContract.2.2 q hValid trivial).1⟩
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · exact body0_safeContract

end Proof
"#,
    )
    .unwrap();
    let abort_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "ebpf_reg_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
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
    let abort_ok = run_request(dir.path(), "ebpf-reg-panic-abort", &abort_request);
    abort_ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(verified) = &abort_ok.receipt else {
        panic!("expected verified receipt, got {:?}", abort_ok.receipt);
    };
    assert!(verified.spec_warnings.is_empty(), "{verified:?}");
    assert!(
        verified.assumptions.iter().any(|a| a.contains("as .aborted")),
        "expected --panic abort assumption in receipt: {:?}",
        verified.assumptions
    );
    let captured_lean = fs::read_to_string(
        dir.path().join("artifacts-ebpf-reg-panic-abort/capture/Captured.lean"),
    )
    .unwrap();
    assert!(
        captured_lean.contains("Trusted.MirAst.CoreCallOp.panicAbort [")
            && captured_lean.contains("Trusted.MirAst.ConstLit.rodataRef")
            && !captured_lean.contains("TerminatorKind.assert"),
        "{captured_lean}"
    );

    // Check 1b: full `ebpf_core` `EbpfInstruction::new` shape
    // (`assert!(dst < 16); assert!(src < 16); ...`) captures cleanly under
    // `--panic abort` with two static `&str` `CoreCallOp.panicAbort`
    // terminators.
    let ebpf_full_dir = dir.path().join("ebpf-insn-full");
    fs::create_dir_all(&ebpf_full_dir).unwrap();
    let ebpf_full_src = ebpf_full_dir.join("lib.rs");
    fs::write(
        &ebpf_full_src,
        "pub fn ebpf_insn_new(code: u8, dst: u8, src: u8, offset: i16, imm: i32) -> u64 {\n\
             assert!(dst < 16);\n\
             assert!(src < 16);\n\
             (code as u64)\n\
                 | ((dst as u64) << 8)\n\
                 | ((src as u64) << 12)\n\
                 | ((offset as u16 as u64) << 16)\n\
                 | ((imm as u32 as u64) << 32)\n\
         }\n",
    )
    .unwrap();
    let ebpf_full_out = dir.path().join("ebpf-insn-full-capture");
    let ebpf_cap = Command::new(tools.capture.as_deref().expect("capture bin"))
        .args([
            "capture",
            "--crate-root",
            ebpf_full_src.to_str().unwrap(),
            "--crate-name",
            "ebpf_insn_full",
            "--crate-type",
            "lib",
            "--edition",
            "2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--panic",
            "abort",
            "--scope",
            "crate",
            "--out-dir",
            ebpf_full_out.to_str().unwrap(),
            "--sysroot",
            tools.sysroot.to_str().unwrap(),
            "--source-file",
            ebpf_full_src.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        ebpf_cap.status.success(),
        "ebpf_insn_new capture failed: {}",
        String::from_utf8_lossy(&ebpf_cap.stdout)
    );
    let ebpf_full_lean = fs::read_to_string(ebpf_full_out.join("Captured.lean")).unwrap();
    assert_eq!(
        ebpf_full_lean
            .matches("Trusted.MirAst.CoreCallOp.panicAbort [")
            .count(),
        2,
        "{ebpf_full_lean}"
    );

    // Check 2: under `--panic unwind`, `check_ebpf_reg` keeps the diverging
    // `core::panicking::panic` call as `TerminatorKind.unsupported` (selecting
    // Profile v1) and fails verification on the abort path.
    let mut unwind_request = abort_request.clone();
    unwind_request["compilation"]["panic"] = json!("unwind");
    run_request(dir.path(), "ebpf-reg-panic-unwind", &unwind_request)
        .expect_proof_failed();

    // Check 3: `EffectMaskV2.noAbort` rejects `check_ebpf_reg` without a
    // `dst < 16` precondition even under `--panic abort`.
    let no_abort_lean = dir.path().join("ebpf-reg-noabort-lean");
    fs::create_dir_all(&no_abort_lean).unwrap();
    let spec_src = fs::read_to_string(lean_dir.join("Spec.lean")).unwrap();
    fs::write(
        no_abort_lean.join("Spec.lean"),
        spec_src.replace("effects := { allowAbort := true }", "effects := EffectMaskV2.noAbort"),
    )
    .unwrap();
    fs::copy(lean_dir.join("Proof.lean"), no_abort_lean.join("Proof.lean")).unwrap();
    let mut no_abort_request = abort_request.clone();
    no_abort_request["proof"]["source_root"] = json!(no_abort_lean.to_str().unwrap());
    run_request(dir.path(), "ebpf-reg-no-abort", &no_abort_request).expect_proof_failed();

    // Check 4: `#![no_std]` binary with crate-local `#[panic_handler]` keeps
    // `assert!(dst < 16)` unlowered as `TerminatorKind.unsupported` even under
    // `--panic abort` and fails verification, while formatted
    // `assert!(cond, "bad cond")` is refused fail-closed at capture.
    let lh_rust = dir.path().join("ebpf-reg-lh-rust");
    fs::create_dir_all(&lh_rust).unwrap();
    fs::write(
        lh_rust.join("main.rs"),
        "#![no_std]\n\
         #![no_main]\n\
         use core::panic::PanicInfo;\n\
         #[panic_handler]\n\
         fn panic(_info: &PanicInfo<'_>) -> ! { loop {} }\n\
         pub fn check_ebpf_reg_lh(dst: u8) -> u8 {\n\
             assert!(dst < 16);\n\
             dst\n\
         }\n",
    )
    .unwrap();
    let lh_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": lh_rust.to_str().unwrap(),
            "crate_root": "main.rs",
            "crate_name": "ebpf_reg_lh_demo",
            "crate_type": "bin",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["main.rs"]
        },
        "scope": {"kind": "selected_unit", "roots": ["check_ebpf_reg_lh"]},
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
    run_request(dir.path(), "ebpf-reg-local-handler", &lh_request)
        .expect_proof_failed();

    let fmt_rust = dir.path().join("assert-fmt-refused-rust");
    fs::create_dir_all(&fmt_rust).unwrap();
    fs::write(
        fmt_rust.join("lib.rs"),
        "pub fn assert_msg_refused(cond: bool, val: u8) -> u8 {\n\
             assert!(cond, \"bad cond\");\n\
             val\n\
         }\n",
    )
    .unwrap();
    let mut fmt_request = abort_request.clone();
    fmt_request["compilation"]["source_root"] = json!(fmt_rust.to_str().unwrap());
    fmt_request["compilation"]["crate_name"] = json!("assert_fmt_refused");
    run_request(dir.path(), "assert-fmt-refused", &fmt_request)
        .expect_capture_refused("Arguments");

    // Check 5: constant nonzero divisor `x / 16` preserves its primitive
    // `TerminatorKind.assert` (`AssertKind.divByZero`) verbatim without CFG
    // folding and still verifies cleanly on Profile v1 (`CrateTheorem`).
    let div16_rust = dir.path().join("div16-v1-rust");
    let div16_lean = dir.path().join("div16-v1-lean");
    fs::create_dir_all(&div16_rust).unwrap();
    fs::create_dir_all(&div16_lean).unwrap();
    fs::write(
        div16_rust.join("lib.rs"),
        "pub fn div_by_16(x: u64) -> u64 {\n\
             x / 16\n\
         }\n",
    )
    .unwrap();
    fs::write(
        div16_lean.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def property (p : Program) : Prop :=
  p.mirProfileVersion = 1

def specs : Specs := ⟨fun _ _ => True, property⟩

end Spec
"#,
    )
    .unwrap();
    fs::write(
        div16_lean.join("Proof.lean"),
        r#"prelude
import Init.NotationExtra
import Anneal.MirWp
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem wpOutcomeState_step {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStep p 0 s = .step s')
    (hNext : wpOutcomeState p onDone onFault fuel s') :
    wpOutcomeState p onDone onFault (fuel + 1) s :=
  ⟨⟨0, rfl⟩, fun c hc => by
    have hc0 : c = 0 := hc
    rw [hc0, hStep]
    exact hNext⟩

private theorem wpOutcomeState_done {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStep p 0 s = .done out)
    (hDone : onDone out) :
    wpOutcomeState p onDone onFault (fuel + 1) s :=
  ⟨⟨0, rfl⟩, fun c hc => by
    have hc0 : c = 0 := hc
    rw [hc0, hStep]
    exact hDone⟩

private theorem div16_evalBinOp (bits : BitVec 128)
    (hTr : truncateBits .i64 bits = bits)
    (hLt : bits.toNat < Nat.pow 2 64) :
    evalBinOp .div (.scalar ⟨.i64, false, bits⟩)
      (.scalar ⟨.i64, false, BitVec.ofNat 128 16⟩) =
      .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩) := by
  have hDivLt : Nat.div bits.toNat 16 < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLt
  have hDiv128 : Nat.div bits.toNat 16 < Nat.pow 2 128 :=
    Nat.lt_trans hDivLt (by decide)
  have hMod128 :
      (intEmod (Int.ofNat (Nat.div bits.toNat 16))
        (Int.ofNat (Nat.pow 2 128))).toNat = Nat.div bits.toNat 16 := by
    have hM : Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) =
        Nat.div bits.toNat 16 := Nat.mod_eq_of_lt hDiv128
    change (Int.ofNat (Nat.mod (Nat.div bits.toNat 16)
      (Nat.pow 2 128))).toNat = Nat.div bits.toNat 16
    rw [hM]; rfl
  have hTrEq :
      truncateBits .i64 (BitVec.ofNat 128 (Nat.div bits.toNat 16)) =
        BitVec.ofNat 128 (Nat.div bits.toNat 16) := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits]
    have hBv :
        (BitVec.ofNat 128 (Nat.div bits.toNat 16)).toNat =
          Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) := rfl
    have hM128 : Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) =
        Nat.div bits.toNat 16 := Nat.mod_eq_of_lt hDiv128
    rw [hBv, hM128]
    exact Nat.mod_eq_of_lt hDivLt
  dsimp only [evalBinOp, evalArithOp, decodeScalar]
  rw [hTr]
  change (if false then Except.error FaultKind.unsupported
    else if false then Except.error FaultKind.unsupported
    else if false then Except.error FaultKind.undefined
    else if false && true &&
        (Int.ofNat bits.toNat == signedMinInt .i64 &&
          Int.ofNat 16 == Neg.neg 1) then Except.error FaultKind.undefined
    else
      match truncateScalar .i64 false
          (intTdiv (Int.ofNat bits.toNat) (Int.ofNat 16)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if ((decide (intTdiv (Int.ofNat bits.toNat) (Int.ofNat 16) < 0) ||
            decide (intTdiv (Int.ofNat bits.toNat) (Int.ofNat 16) ≥
              HPow.hPow (2 : Int) 128)) || lossy) && false then Except.error FaultKind.undefined
        else if false then Except.error FaultKind.unsupported
        else Except.ok (Val.scalar val)) = _
  dsimp only [truncateScalar, intTdiv, bvOfInt]
  rw [hMod128, hTrEq]
  simp [Bool.and_false, bne_self_eq_false]

private theorem checkVal_u64_inv {v : Val}
    (h : checkVal v (.int .i64 false) = true) :
    ∃ bits : BitVec 128, v = .scalar ⟨.i64, false, bits⟩ ∧
      ScalarVal.wf ⟨.i64, false, bits⟩ = true := by
  unfold checkVal at h
  cases v with
  | scalar sv =>
    cases sv with
    | mk w s bits =>
      cases hwf : ScalarVal.wf ⟨w, s, bits⟩ with
      | false =>
        change (match if ScalarVal.wf ⟨w, s, bits⟩ then some (MirTy.int w s) else none with
          | some ty => MirTy.beq ty (.int .i64 false)
          | none => false) = true at h
        rw [hwf] at h; cases h
      | true =>
        change (match if ScalarVal.wf ⟨w, s, bits⟩ then some (MirTy.int w s) else none with
          | some ty => MirTy.beq ty (.int .i64 false)
          | none => false) = true at h
        rw [hwf] at h
        cases w with
        | i64 =>
          cases s with
          | false => exact ⟨bits, rfl, hwf⟩
          | true => cases h
        | _ => cases h
  | enumVal ety discr =>
    cases hValid : enumAdmitted ety && Nat.blt discr ety.discriminants.length with
    | false =>
      change (match if (enumAdmitted ety && Nat.blt discr ety.discriminants.length) = true
          then some (MirTy.enum ety) else none with
        | some ty => MirTy.beq ty (.int .i64 false)
        | none => false) = true at h
      rw [hValid] at h; cases h
    | true =>
      change (match if (enumAdmitted ety && Nat.blt discr ety.discriminants.length) = true
          then some (MirTy.enum ety) else none with
        | some ty => MirTy.beq ty (.int .i64 false)
        | none => false) = true at h
      rw [hValid] at h; cases h
  | tuple fs =>
    cases fs with
    | nil => cases h
    | cons a r1 =>
      cases r1 with
      | nil => cases a <;> cases h
      | cons b r2 =>
        cases r2 with
        | cons _ _ => cases a <;> cases b <;> cases h
        | nil =>
          cases a with
          | scalar sv =>
            cases b with
            | bool _ =>
              cases hwf : sv.wf with
              | false =>
                change (match if sv.wf = true
                    then some (MirTy.tuple [.int sv.width sv.signed, .bool])
                    else none with
                  | some ty => MirTy.beq ty (.int .i64 false)
                  | none => false) = true at h
                rw [hwf] at h; cases h
              | true =>
                change (match if sv.wf = true
                    then some (MirTy.tuple [.int sv.width sv.signed, .bool])
                    else none with
                  | some ty => MirTy.beq ty (.int .i64 false)
                  | none => false) = true at h
                rw [hwf] at h; cases h
            | _ => cases h
          | _ => cases h
  | _ => cases h

private theorem div16_wf (args : List Val) (hValid : ValidEntryArgs Captured.body_0 args) :
    WellFormed (entryProgForBody Captured.program 0) { args := args } := by
  change checkArgsMatch args [.int .i64 false] = true at hValid
  cases args with
  | nil => cases hValid
  | cons v rest =>
    cases rest with
    | cons a1 rest1 =>
      change checkVal v (.int .i64 false) && checkArgsMatch (a1 :: rest1) [] = true at hValid
      cases h0 : checkVal v (.int .i64 false) <;> rw [h0] at hValid <;> cases hValid
    | nil =>
      change checkVal v (.int .i64 false) && true = true at hValid
      cases h0 : checkVal v (.int .i64 false) with
      | false => rw [h0] at hValid; cases hValid
      | true =>
        let ⟨bits, hvEq, hwf⟩ := checkVal_u64_inv h0
        subst hvEq
        have hTr : truncateBits .i64 bits = bits := by
          unfold ScalarVal.wf at hwf
          exact eq_of_beq hwf
        have hLt : bits.toNat < Nat.pow 2 64 := by
          rw [← hTr, toNat_truncateBits]
          exact Nat.mod_lt _ (by decide)
        have hResWf :
            ScalarVal.wf ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩ = true := by
          have hDivLt : Nat.div bits.toNat 16 < Nat.pow 2 64 :=
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLt
          have hDiv128 : Nat.div bits.toNat 16 < Nat.pow 2 128 :=
            Nat.lt_trans hDivLt (by decide)
          have hResTr :
              truncateBits .i64 (BitVec.ofNat 128 (Nat.div bits.toNat 16)) =
                BitVec.ofNat 128 (Nat.div bits.toNat 16) := by
            apply bitVec_eq_of_toNat_eq
            rw [toNat_truncateBits]
            have hBv :
                (BitVec.ofNat 128 (Nat.div bits.toNat 16)).toNat =
                  Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) := rfl
            have hM128 : Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) =
                Nat.div bits.toNat 16 := Nat.mod_eq_of_lt hDiv128
            rw [hBv, hM128]
            exact Nat.mod_eq_of_lt hDivLt
          unfold ScalarVal.wf
          rw [hResTr]
          exact beq_self_eq_true _
        have hDiv : evalBinOp .div (.scalar ⟨.i64, false, bits⟩)
            (.scalar ⟨.i64, false, BitVec.ofNat 128 16⟩) =
            .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩) :=
          div16_evalBinOp bits hTr hLt
        let vIn : Val := .scalar ⟨.i64, false, bits⟩
        let vOut : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩
        have hCheckIn : checkVal vIn (.int .i64 false) = true := h0
        have hCheckOut : checkVal vOut (.int .i64 false) = true := by
          unfold checkVal
          change (match if ScalarVal.wf ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩
              then some (MirTy.int .i64 false) else none with
            | some ty => MirTy.beq ty (.int .i64 false)
            | none => false) = true
          rw [hResWf]; rfl
        have hInit :
            initState (entryProgForBody Captured.program 0) { args := [vIn] } =
            .ok (mkState 0 0 [.immediate none, .immediate (some vIn), .dead, .immediate none]) := by
          change (if (!(checkVal vIn (.int .i64 false) && true)) = true then
            Except.error FaultKind.unsupported
          else
            Except.ok (mkState 0 0 [.immediate none, .immediate (some vIn),
              .dead, .immediate none])) = _
          rw [hCheckIn]; rfl
        have hWp :
            wpProg (entryProgForBody Captured.program 0) 10
              { args := [vIn] } (fun _ => True) := by
          unfold wpProg
          rw [hInit]
          refine wpOutcomeState_step (s' := mkState 0 1
            [.immediate none, .immediate (some vIn), .immediate none,
             .immediate none]) rfl ?_
          have hCopy :
              evalStep (entryProgForBody Captured.program 0) 0
                (mkState 0 1 [.immediate none, .immediate (some vIn),
                  .immediate none, .immediate none]) =
              .step (mkState 0 2 [.immediate none, .immediate (some vIn),
                .immediate (some vIn), .immediate none]) := by
            change (match (if (!checkVal vIn (.int .i64 false)) = true then
                Except.error FaultKind.unsupported
              else
                Except.ok ([LocalSlot.immediate none,
                  LocalSlot.immediate (some vIn),
                  LocalSlot.immediate (some vIn),
                  LocalSlot.immediate none], entryMemory)) with
              | Except.error k => StepResult.fault k
              | Except.ok (locals', mem') => StepResult.step (mkState 0 2 locals' 0 mem')) = _
            rw [hCheckIn]; rfl
          refine wpOutcomeState_step hCopy ?_
          refine wpOutcomeState_step (s' := mkState 0 3
            [.immediate none, .immediate (some vIn), .immediate (some vIn),
             .immediate (some (.bool false))]) rfl ?_
          refine wpOutcomeState_step (s' := mkState 1 0
            [.immediate none, .immediate (some vIn), .immediate (some vIn),
             .immediate none]) rfl ?_
          have hDivStep :
              evalStep (entryProgForBody Captured.program 0) 0
                (mkState 1 0 [.immediate none, .immediate (some vIn),
                  .immediate (some vIn), .immediate none]) =
              .step (mkState 1 1 [.immediate (some vOut), .immediate (some vIn),
                .immediate none, .immediate none]) := by
            change (match (match evalBinOp .div vIn
                  (.scalar ⟨.i64, false, BitVec.ofNat 128 16⟩) with
              | Except.error k => Except.error k
              | Except.ok res =>
                Except.ok (res, [LocalSlot.immediate none,
                  LocalSlot.immediate (some vIn), LocalSlot.immediate none,
                  LocalSlot.immediate none], entryMemory)) with
              | Except.error k => StepResult.fault k
              | Except.ok (res, locals1, mem1) =>
                match writePlace locals1 mem1 0 (.int .i64 false) res with
                | Except.error k => StepResult.fault k
                | Except.ok (locals', mem') =>
                  StepResult.step (mkState 1 1 locals' 0 mem')) = _
            rw [hDiv]
            change (match (if (!checkVal vOut (.int .i64 false)) = true then
                Except.error FaultKind.unsupported
              else
                Except.ok ([LocalSlot.immediate (some vOut),
                  LocalSlot.immediate (some vIn), LocalSlot.immediate none,
                  LocalSlot.immediate none], entryMemory)) with
              | Except.error k => StepResult.fault k
              | Except.ok (locals', mem') =>
                StepResult.step (mkState 1 1 locals' 0 mem')) = _
            rw [hCheckOut]; rfl
          refine wpOutcomeState_step hDivStep ?_
          refine wpOutcomeState_step (s' := mkState 1 2
            [.immediate (some vOut), .immediate (some vIn), .dead,
             .immediate none]) rfl ?_
          exact wpOutcomeState_done rfl trivial
        exact (wellFormed_and_spec_of_wp_base _ _ 10 (fun _ => True) hWp).1.1

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, rfl⟩
  intro defId body hBody
  cases defId with
  | zero =>
    change some Captured.body_0 = some body at hBody
    cases hBody
    refine ⟨rfl, by decide, fun args hValid _ => div16_wf args hValid⟩
  | succ _ =>
    change none = some body at hBody
    cases hBody

end Proof
"#,
    )
    .unwrap();
    let div16_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": div16_rust.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "div16_v1_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": div16_lean.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let div16_ok = run_request(dir.path(), "div16-stays-v1", &div16_request);
    div16_ok.expect_ok("crate_verified");
    let div16_capture: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-div16-stays-v1/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(div16_capture["program"]["mir_profile_version"], 1, "{div16_capture}");
    let div16_lean_captured = fs::read_to_string(
        dir.path().join("artifacts-div16-stays-v1/capture/Captured.lean"),
    )
    .unwrap();
    assert!(
        div16_lean_captured.contains("TerminatorKind.assert")
            && div16_lean_captured.contains("AssertKind.divByZero"),
        "expected verbatim preserved DivByZero Assert on Profile v1:\n{div16_lean_captured}"
    );
}

/// Verifies `Vec<u8>`, `Box<[u8]>`, and `Box<u64>` allocation contracts under
/// `CrateTheoremV2` with `"panic": "abort"` (`["propext"]`, zero taint),
/// including the heap buffers visible to `post` on return and
/// `push_one(&mut Vec<u8>)` over every valid caller `Vec` that cannot
/// overflow its capacity, and
/// confirms fail-closed rejections for both weakening `Vec::with_capacity`'s
/// `isize::MAX` bound and omitting `"panic": "abort"` (`--panic unwind`).
#[test]
fn verifies_profile_v2_vec_and_box_contracts_and_rejects_missing_cap_bound() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), ALLOC_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ALLOC_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ALLOC_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "alloc_demo",
            "panic": "abort",
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

    let ok = run_request(dir.path(), "alloc-ok", &request);
    ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(verified) = &ok.receipt else {
        panic!("alloc-ok: expected verified receipt, got {:?}", ok.receipt);
    };
    assert_eq!(verified.configuration["panic"], "abort", "{:?}", verified.configuration);
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-alloc-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert_eq!(capture_json["configuration"]["panic"], "abort", "{capture_json}");
    let identities: Vec<&str> = capture_json["program"]["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| b["identity"].as_str().unwrap())
        .collect();
    assert_eq!(
        identities,
        vec![
            "rust-path-v1::vec_and_box_slice",
            "rust-path-v1::box_new_and_deref",
            "rust-path-v1::vec_with_cap_arg",
            "rust-path-v1::read_slice_and_box_len",
            "rust-path-v1::push_one",
        ],
        "{capture_json}"
    );
    let captured_lean =
        fs::read_to_string(dir.path().join("artifacts-alloc-ok/capture/Captured.lean")).unwrap();
    assert!(captured_lean.contains("CastKind.boxAsRef"), "{captured_lean}");

    // Negative 7: weaken `vecWithCapSafety` to omit `< isizeMaxBytes`.
    let bad_spec = ALLOC_SPEC.replace("capSv.bits.toNat < isizeMaxBytes", "True");
    assert_ne!(bad_spec, ALLOC_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_spec).unwrap();
    run_request(dir.path(), "alloc-missing-cap-bound", &request).expect_proof_failed();

    // Negative 8: restore valid `Spec.lean`, omit `"panic": "abort"`
    // (`--panic unwind` default), and confirm fail-closed capture rejection.
    fs::write(lean_dir.join("Spec.lean"), ALLOC_SPEC).unwrap();
    let mut unwind_request = request.clone();
    unwind_request["compilation"].as_object_mut().unwrap().remove("panic");
    let unwind = run_request(dir.path(), "alloc-unwind-rejected", &unwind_request);
    assert!(
        !unwind.output.status.success(),
        "alloc-unwind-rejected must fail closed:\n{:?}\nstderr:\n{}",
        unwind.receipt,
        String::from_utf8_lossy(&unwind.output.stderr)
    );
    let VerifyReceipt::Failed(failure) = &unwind.receipt else {
        panic!("alloc-unwind-rejected must fail closed: {:?}", unwind.receipt);
    };
    assert_eq!(failure.schema_version, 3, "{failure:?}");
    assert_ne!(failure.status, "crate_verified", "{failure:?}");
    assert_eq!(failure.phase, "capture", "{failure:?}");

    // Negative 9: a function mixing `&[u8]` / `&Box<u64>` with a genuine
    // `*const u64` raw pointer still fails closed in capture.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn mixed(s: &[u8], b: &Box<u64>) -> (usize, *const u64) {\n\
             (s.len(), &**b as *const u64)\n\
         }\n",
    )
    .unwrap();
    run_request(dir.path(), "alloc-mixed-raw-ptr-rejected", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Profile v2 E2E test for core scalar and slice operations: `count_ones`,
/// `trailing_zeros`, `checked_shl`, `overflowing_mul`, `from_le_bytes`,
/// `mem::size_of`, `next_power_of_two`, `next_multiple_of`, `div_ceil`,
/// `<[u16]>::get_unchecked(Range<usize>)`, and `<[u16]>::get_unchecked(usize)`,
/// including trap/UB twins for `corePanicTrap` and out-of-bounds indexing.
#[test]
fn verifies_core_scalar_ops_and_trap_twins() {
    let dir = TempDir::new().unwrap();

    // 1. Concrete end-to-end verification of `count_ones`, `trailing_zeros`,
    // `checked_shl`, `overflowing_mul`, `u16::from_le_bytes`, and
    // `core::mem::size_of`.
    let bundle_dir = dir.path().join("core_ops_bundle");
    let bundle_rust = bundle_dir.join("rust");
    let bundle_lean = bundle_dir.join("lean");
    fs::create_dir_all(&bundle_rust).unwrap();
    fs::create_dir_all(&bundle_lean).unwrap();
    fs::write(
        bundle_rust.join("lib.rs"),
        "pub unsafe fn core_ops_bundle(x: u8, bs: [u8; 2]) -> (u32, u32, Option<u8>, (u8, bool), u16, usize) {\n\
             (x.count_ones(), x.trailing_zeros(), x.checked_shl(2),\n\
              x.overflowing_mul(16), u16::from_le_bytes(bs),\n\
              core::mem::size_of::<Option<u64>>())\n\
         }\n",
    )
    .unwrap();
    fs::write(
        bundle_lean.join("Spec.lean"),
        "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args :=
      [.scalar ⟨.i8, false, BitVec.ofNat 128 12⟩,
       .array [.scalar ⟨.i8, false, BitVec.ofNat 128 0x34⟩,
               .scalar ⟨.i8, false, BitVec.ofNat 128 0x12⟩]],
    callerMem := ⟨[]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.tuple
      [.scalar ⟨.i32, false, BitVec.ofNat 128 2⟩,
       .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩,
       .optionVal (some (.scalar ⟨.i8, false, BitVec.ofNat 128 48⟩)),
       .tuple [.scalar ⟨.i8, false, BitVec.ofNat 128 192⟩, .bool false],
       .scalar ⟨.i16, false, BitVec.ofNat 128 0x1234⟩,
       .scalar ⟨.isize, false, BitVec.ofNat 128 16⟩],
     ⟨[]⟩⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::core_ops_bundle\" ∧
    BehaviorV2 (entryProgForBody p defId) okQuery okOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
",
    )
    .unwrap();
    fs::write(
        bundle_lean.join("Proof.lean"),
        "\
prelude
import Spec
import Expected
import Anneal.MirWp
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp
theorem verify : Expected.claim := by
  have hOk :=
    spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.okQuery)
      (out := Spec.okOut)
      (fuel := 40) rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      cases hBody
      refine ⟨rfl, rfl, fun q _ hSafe => ?_⟩
      have hEq : q = Spec.okQuery := hSafe rfl
      cases hEq
      exact hOk.1
    | succ _ => cases hBody
  · refine ⟨0, Captured.body_0, rfl, rfl, hOk.2.1⟩
end Proof
",
    )
    .unwrap();
    let bundle_req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": bundle_rust.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "core_ops_bundle",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": bundle_lean.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    run_request(dir.path(), "core-ops-bundle-ok", &bundle_req).expect_ok("crate_verified");

    // 2. Positive + trap/UB twins for `next_power_of_two`, `next_multiple_of`,
    // and `<[u16]>::get_unchecked(Range<usize>)`.
    const TWIN_PROOF: &str = "\
prelude
import Spec
import Expected
import Anneal.MirWp
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp
theorem verify : Expected.claim := by
  have hOk :=
    spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.okQuery)
      (out := Spec.okOut)
      (fuel := 30) rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      cases hBody
      refine ⟨rfl, rfl, fun q _ hSafe => ?_⟩
      have hEq : q = Spec.okQuery := hSafe rfl
      cases hEq
      exact hOk.1
    | succ _ => cases hBody
  · refine ⟨0, Captured.body_0, rfl, rfl, ?_⟩
    exact (spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.testQuery)
      (out := Spec.expectedOut)
      (fuel := 30) rfl).2.1
end Proof
";
    let run_twin = |subdir: &str,
                    crate_name: &str,
                    rust_src: &str,
                    pos_name: &str,
                    pos_spec: &str,
                    neg_name: &str,
                    neg_spec: &str| {
        let sub_dir = dir.path().join(subdir);
        let sub_rust = sub_dir.join("rust");
        let sub_lean = sub_dir.join("lean");
        fs::create_dir_all(&sub_rust).unwrap();
        fs::create_dir_all(&sub_lean).unwrap();
        fs::write(sub_rust.join("lib.rs"), rust_src).unwrap();
        fs::write(sub_lean.join("Proof.lean"), TWIN_PROOF).unwrap();
        let req = json!({
            "schema_version": 1,
            "compilation": {
                "source_root": sub_rust.to_str().unwrap(),
                "crate_root": "lib.rs",
                "crate_name": crate_name,
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {
                "source_root": sub_lean.to_str().unwrap(),
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"}
                ]
            }
        });
        fs::write(sub_lean.join("Spec.lean"), pos_spec).unwrap();
        run_request(dir.path(), pos_name, &req).expect_ok("crate_verified");
        fs::write(sub_lean.join("Spec.lean"), neg_spec).unwrap();
        let neg = run_request(dir.path(), neg_name, &req);
        neg.expect_proof_failed();
        let detail = match &neg.receipt {
            VerifyReceipt::Failed(failure) => failure.detail.as_str(),
            VerifyReceipt::Verified(_) => "",
        };
        assert!(
            detail.contains("Spec.testQuery")
                && detail.contains("execProgV2")
                && (detail.contains("Application type mismatch")
                    || detail.contains("not definitionally equal")
                    || detail.contains("Tactic `rfl` failed")),
            "{neg_name} did not fail on `rfl` over Spec.testQuery:\n{:?}",
            neg.receipt
        );
    };

    const POW2_SPEC: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query := { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 128⟩], callerMem := ⟨[]⟩ }
def okOut : TerminalOut := TerminalOut.returned ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 128⟩, ⟨[]⟩⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 __OUT_VAL__⟩, ⟨[]⟩⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::pow2\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    run_twin(
        "pow2_twin",
        "core_ops_pow2_twin",
        "pub unsafe fn pow2(x: u8) -> u8 {\n    x.next_power_of_two()\n}\n",
        "core-ops-pow2-ok",
        &POW2_SPEC
            .replace("__TEST_QUERY__", "okQuery")
            .replace("__OUT_VAL__", "128"),
        "core-ops-pow2-trap",
        &POW2_SPEC
            .replace(
                "__TEST_QUERY__",
                "{ args := [.scalar ⟨.i8, false, BitVec.ofNat 128 129⟩], callerMem := ⟨[]⟩ }",
            )
            .replace("__OUT_VAL__", "0"),
    );

    const MULT_SPEC: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 13⟩,
             .scalar ⟨.i8, false, BitVec.ofNat 128 4⟩], callerMem := ⟨[]⟩ }
def okOut : TerminalOut := TerminalOut.returned ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 16⟩, ⟨[]⟩⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 __OUT_VAL__⟩, ⟨[]⟩⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::mult\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    run_twin(
        "mult_twin",
        "core_ops_mult_twin",
        "pub unsafe fn mult(x: u8, rhs: u8) -> u8 {\n    x.next_multiple_of(rhs)\n}\n",
        "core-ops-mult-ok",
        &MULT_SPEC
            .replace("__TEST_QUERY__", "okQuery")
            .replace("__OUT_VAL__", "16"),
        "core-ops-mult-div0-trap",
        &MULT_SPEC
            .replace(
                "__TEST_QUERY__",
                "{ args := [.scalar ⟨.i8, false, BitVec.ofNat 128 13⟩, \
                 .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩], callerMem := ⟨[]⟩ }",
            )
            .replace("__OUT_VAL__", "0"),
    );

    const GET_U16_SPEC: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args :=
      [.slicePtr ⟨some 2, 0, .isize⟩ 2,
       .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩,
       .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩],
    callerMem :=
      ⟨[{ allocId := 2, alignLog2 := 1, mutability := .shared,
          bytes := [AllocByte.init 10 none, AllocByte.init 0 none,
                    AllocByte.init 20 none, AllocByte.init 0 none],
          live := true }]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, 2, .isize⟩ 1, okQuery.callerMem⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, 2, .isize⟩ 1, testQuery.callerMem⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::sub_u16\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    run_twin(
        "get_u16_twin",
        "core_ops_get_u16_twin",
        "pub unsafe fn sub_u16<'a>(s: &'a [u16], a: usize, b: usize) -> &'a [u16] {\n\
             unsafe { s.get_unchecked(a..b) }\n\
         }\n",
        "core-ops-get-u16-ok",
        &GET_U16_SPEC.replace("__TEST_QUERY__", "okQuery"),
        "core-ops-get-u16-oob",
        &GET_U16_SPEC.replace(
            "__TEST_QUERY__",
            "{ args := [.slicePtr ⟨some 2, 0, .isize⟩ 2, \
             .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩, \
             .scalar ⟨.isize, false, BitVec.ofNat 128 3⟩], callerMem := okQuery.callerMem }",
        ),
    );

    const DIV_CEIL_SPEC: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 13⟩,
             .scalar ⟨.i8, false, BitVec.ofNat 128 4⟩], callerMem := ⟨[]⟩ }
def okOut : TerminalOut := TerminalOut.returned ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 4⟩, ⟨[]⟩⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 __OUT_VAL__⟩, ⟨[]⟩⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::divc\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    run_twin(
        "div_ceil_twin",
        "core_ops_div_ceil_twin",
        "pub unsafe fn divc(x: u8, rhs: u8) -> u8 {\n    x.div_ceil(rhs)\n}\n",
        "core-ops-div-ceil-ok",
        &DIV_CEIL_SPEC
            .replace("__TEST_QUERY__", "okQuery")
            .replace("__OUT_VAL__", "4"),
        "core-ops-div-ceil-div0-trap",
        &DIV_CEIL_SPEC
            .replace(
                "__TEST_QUERY__",
                "{ args := [.scalar ⟨.i8, false, BitVec.ofNat 128 13⟩, \
                 .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩], callerMem := ⟨[]⟩ }",
            )
            .replace("__OUT_VAL__", "0"),
    );

    const GET_IDX_U16_SPEC: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args :=
      [.slicePtr ⟨some 2, 0, .isize⟩ 2,
       .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩],
    callerMem :=
      ⟨[{ allocId := 2, alignLog2 := 1, mutability := .shared,
          bytes := [AllocByte.init 10 none, AllocByte.init 0 none,
                    AllocByte.init 20 none, AllocByte.init 0 none],
          live := true }]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned ⟨.ptr ⟨some 2, 2, .isize⟩, okQuery.callerMem⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned ⟨.ptr ⟨some 2, 2, .isize⟩, testQuery.callerMem⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::elem_u16\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    run_twin(
        "get_idx_u16_twin",
        "core_ops_get_idx_u16_twin",
        "pub unsafe fn elem_u16<'a>(s: &'a [u16], idx: usize) -> &'a u16 {\n\
             unsafe { s.get_unchecked(idx) }\n\
         }\n",
        "core-ops-get-idx-u16-ok",
        &GET_IDX_U16_SPEC.replace("__TEST_QUERY__", "okQuery"),
        "core-ops-get-idx-u16-oob",
        &GET_IDX_U16_SPEC.replace(
            "__TEST_QUERY__",
            "{ args := [.slicePtr ⟨some 2, 0, .isize⟩ 2, \
             .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩], callerMem := okQuery.callerMem }",
        ),
    );
}
