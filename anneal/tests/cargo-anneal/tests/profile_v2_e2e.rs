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
//! 4. `-Coverflow-checks=yes` capture (`compilation.overflow_checks`): a
//!    guarded `u8` increment verifies under both panic strategies, proving its
//!    overflow `Assert` never fires, while one proof of the wrapping result of
//!    an unguarded increment verifies without overflow checks and is rejected
//!    with them.

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
            a.starts_with("--panic abort models failed non-optional safe assertions as .aborted")
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
                "--panic abort models failed non-optional safe assertions and, under \
                 --overflow-checks, failed overflow checks as .aborted",
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
         pub unsafe fn div_u64(a: u64, b: u64) -> u64 {\n\
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

def qDivZero : Query :=
  { args := [
      .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
      .scalar ⟨.i64, false, BitVec.ofNat 128 0⟩] }

def safety (_id : String) (q : Query) : Prop :=
  q.args = [
    .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
    .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩]

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
         .dead, .dead, .immediate none] cm mem) := by
  let va : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩
  let vb : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩
  refine .step (s' := mkS 0 0 1 [.immediate none, .immediate (some va), .immediate (some vb), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 2 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 3 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 4 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 5 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate (some (.bool false))] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 0 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 1 [.immediate (some va), .immediate (some va), .immediate (some vb), .immediate none, .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 2 [.immediate (some va), .immediate (some va), .immediate (some vb), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 3 [.immediate (some va), .immediate (some va), .immediate (some vb), .dead, .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem div_ok_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hArgs : q.args = [
      .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
      .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩]) :
    WellFormedV2 (entryProgForBody Captured.program 0) q := by
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩], cm⟩ =
        .ok (mkS 0 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩)),
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
