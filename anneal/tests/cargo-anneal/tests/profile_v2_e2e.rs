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

#[path = "profile_v2_e2e/alloc.rs"]
mod alloc;
#[path = "profile_v2_e2e/core_contracts.rs"]
mod core_contracts;
#[path = "profile_v2_e2e/ebpf_and_const_div.rs"]
mod ebpf_and_const_div;
#[path = "profile_v2_e2e/fake_ptr_metadata.rs"]
mod fake_ptr_metadata;
#[path = "profile_v2_e2e/overflow_and_arrays.rs"]
mod overflow_and_arrays;
#[path = "profile_v2_e2e/panic_abort.rs"]
mod panic_abort;
#[path = "profile_v2_e2e/zerocopy_and_raw_ptr.rs"]
mod zerocopy_and_raw_ptr;

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
