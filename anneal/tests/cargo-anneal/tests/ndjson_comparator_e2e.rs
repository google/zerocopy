// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration tests for the Universal NDJSON Comparator
//! (`5a`/`5b`/`5c`, default-ON on Lean `v4.35.0+`).
//!
//! Exercises live Lean `v4.35.0` `leanexport`, `nanoda_bin`, `con-ron`,
//! `con-leche`, and `lean4lean` through `Checker::run_target` with both
//! positive proofs (including `scalar` and unfolded canonical theorem types)
//! and adversarial negative fixtures (mutated claim, ill-typed export, custom
//! axiom, `opaque` stub, `partial def`, and `sorryAx` with and without
//! `--allow-sorry-in-proof`).
//!
//! The tests live in domain submodules under `tests/ndjson_comparator_e2e/`,
//! which share this file's helpers and imports through `use super::*`.

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use anneal_testkit::ToolchainEnv;
use cargo_anneal::{
    ActiveSandbox, Checker, PINNED_INIT_PRIMITIVES, PINNED_SYSTEM_PLATFORM_DECLS,
    STANDARD_PERMITTED_AXIOMS, SandboxMode, TargetAuditRequest, TargetBindings, TargetModule,
    TargetRole, sha256_bytes,
};
use serde_json::{Value, json};
use tempfile::TempDir;

const SCALAR_SPEC: &str = include_str!("../../../trusted/cargo-anneal/assets/scalar/Spec.lean");
const SCALAR_PROOF: &str = include_str!("../../../trusted/cargo-anneal/assets/scalar/Proof.lean");

fn repo_root() -> PathBuf {
    ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
        .expect("resolve anneal repository root")
}

/// Return `true` when `lean` is a regular file with sibling `v4.35.0+`
/// comparator binaries (`leanexport`, `nanoda_bin`, `con-ron`).
fn has_v435_comparator_tools(lean: &Path) -> bool {
    lean.is_file()
        && lean.parent().is_some_and(|bin_dir| {
            ["leanexport", "nanoda_bin", "con-ron"]
                .into_iter()
                .all(|tool| bin_dir.join(tool).is_file())
        })
}

/// Pure env-injectable core for locating a Lean `v4.35.0+` binary bundling
/// `leanexport`, `nanoda_bin`, and `con-ron` under `<prefix>/bin/`.
///
/// Fails closed (`Err`) whenever:
/// - `ANNEAL_LEAN_V435` is explicitly set (non-empty) to a missing or
///   incomplete toolchain (even in non-strict local mode), or
/// - EITHER `ANNEAL_CI_STRICT=1` OR `ANNEAL_REQUIRE_V435=1` is set and the
///   comparator tools are unavailable.
///
/// Returns `Ok(None)` only in non-strict local development when
/// `ANNEAL_LEAN_V435` is unset and no default `v4.35.0` toolchain is found.
fn discover_v435_lean_with_env(
    test_name: &str,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<Option<PathBuf>, String> {
    if let Some(raw) = get_env("ANNEAL_LEAN_V435").filter(|v| !v.is_empty()) {
        let p = PathBuf::from(raw);
        if has_v435_comparator_tools(&p) {
            return Ok(Some(p));
        }
        return Err(format!(
            "{test_name}: failing closed because ANNEAL_LEAN_V435={} is missing lean or sibling \
             v4.35.0+ comparator tools (leanexport, nanoda_bin, con-ron)",
            p.display()
        ));
    }

    let reason = if let Some(home) = get_env("HOME").filter(|v| !v.is_empty()) {
        let candidate =
            PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean");
        if has_v435_comparator_tools(&candidate) {
            return Ok(Some(candidate));
        }
        format!(
            "no Lean v4.35.0+ toolchain with comparator tools (leanexport, nanoda_bin, con-ron) \
             found at {}",
            candidate.display()
        )
    } else {
        "HOME is unset and ANNEAL_LEAN_V435 is unset; cannot locate Lean v4.35.0+ comparator tools"
            .to_owned()
    };

    let ci_strict = get_env("ANNEAL_CI_STRICT").is_some_and(|v| v == "1");
    let require_v435 = get_env("ANNEAL_REQUIRE_V435").is_some_and(|v| v == "1");
    if ci_strict || require_v435 {
        let mut active_gates = Vec::new();
        if ci_strict {
            active_gates.push("ANNEAL_CI_STRICT=1");
        }
        if require_v435 {
            active_gates.push("ANNEAL_REQUIRE_V435=1");
        }
        return Err(format!(
            "{test_name}: failing closed because {} is set, but {reason}",
            active_gates.join(" and ")
        ));
    }
    Ok(None)
}

/// Locate a Lean `v4.35.0+` binary bundling `leanexport`, `nanoda_bin`, and
/// `con-ron` under `<prefix>/bin/`.
///
/// Panics (fails closed) when an explicit `ANNEAL_LEAN_V435` override is
/// missing/incomplete or when `ANNEAL_CI_STRICT=1` / `ANNEAL_REQUIRE_V435=1`
/// is set and comparator tools are unavailable. In non-strict local dev with
/// `ANNEAL_LEAN_V435` unset, emits a standardized skip diagnostic naming both
/// strict variables and returns `None`.
fn require_or_skip_v435_lean(test_name: &str) -> Option<PathBuf> {
    match discover_v435_lean_with_env(test_name, |key| env::var_os(key)) {
        Ok(Some(lean)) => Some(lean),
        Ok(None) => {
            eprintln!(
                "[SKIP] {test_name}: Lean v4.35.0+ comparator tools (lean, leanexport, \
                 nanoda_bin, con-ron) are unavailable (set ANNEAL_CI_STRICT=1 or \
                 ANNEAL_REQUIRE_V435=1 to fail closed instead of skipping)"
            );
            None
        }
        Err(message) => panic!("{message}"),
    }
}

/// Stage a minimal self-contained `scalar` target verification workspace using
/// the canonical `trusted/lean` and `theory/Anneal` sources from the repository
/// plus a synthetic captured `zero()` program matching
/// `fixtures/scalar/lib.rs`.
fn build_scalar_target_request(
    stage_dir: &Path,
    spec_src: &str,
    proof_src: &str,
    allow_sorry_in_proof: bool,
) -> TargetAuditRequest {
    let root = repo_root();
    let mut modules = Vec::new();

    for rel in cargo_anneal::bundle::TRUSTED_BUNDLE_SOURCES {
        if rel.starts_with("trusted/lean/") && rel.ends_with(".lean") {
            let src = root.join(rel);
            let bytes = fs::read(&src).expect("read trusted lean module");
            modules.push(TargetModule {
                module: rel
                    .trim_start_matches("trusted/lean/")
                    .trim_end_matches(".lean")
                    .replace('/', "."),
                source: src,
                expected_sha256: sha256_bytes(&bytes),
                role: TargetRole::Model,
            });
        }
    }

    let bundled_theory = cargo_anneal::bundle::embedded_theory_bundle().unwrap();
    let theory_dir = stage_dir.join("theory");
    for entry in bundled_theory.modules {
        let dest = theory_dir.join(&entry.path);
        fs::create_dir_all(dest.parent().unwrap()).unwrap();
        fs::write(&dest, entry.content.as_bytes()).unwrap();
        modules.push(TargetModule {
            module: entry
                .path
                .trim_start_matches("theory/")
                .trim_end_matches(".lean")
                .replace('/', "."),
            source: dest,
            expected_sha256: entry.sha256,
            role: TargetRole::Proof,
        });
    }

    // Minimal closed `Captured.program` matching `pub fn zero() -> u64 { 0 }`,
    // in the `module` form `rustc-capture` emits.
    let captured_src = "\
module
prelude
public import Trusted.MirAst

@[expose] public section

namespace Captured
open Trusted.MirAst

def program : Program :=
  { bodies := [
      { argumentCount := 0
        locals := [.int .i64 false]
        basicBlocks := [
          { statements := [
              .assign { localId := 0, projection := [] }
                (.use (.constant { ty := .int .i64 false, lit := .scalar (BitVec.ofNat 128 0) }))
            ]
            terminator := .return_
            cleanup := false
          }
        ]
        isUnsafe := false
        identity := \"scalar::zero\"
      }
    ]
    entryDefId := 0
    pointerWidthBits := 64
    mirProfileVersion := 1
    scope := .unit
  }

end Captured

end
";
    let captured_path = stage_dir.join("Captured.lean");
    fs::write(&captured_path, captured_src).unwrap();
    modules.push(TargetModule {
        module: "Captured".to_owned(),
        source: captured_path,
        expected_sha256: sha256_bytes(captured_src.as_bytes()),
        role: TargetRole::Capture,
    });

    let spec_path = stage_dir.join("Spec.lean");
    fs::write(&spec_path, spec_src).unwrap();
    modules.push(TargetModule {
        module: "Spec".to_owned(),
        source: spec_path,
        expected_sha256: sha256_bytes(spec_src.as_bytes()),
        role: TargetRole::Specification,
    });

    // The `module`-mode `Expected.lean` that `cargo anneal verify` emits when
    // `Captured` and the specification are modules.
    let expected_src = "\
module
prelude
public import Trusted.MirSemantics
public import Captured
public import Spec

@[expose] public section

namespace Expected
def claim : Prop := _root_.Trusted.MirSemantics.UnitTheorem (_root_.Trusted.MirSemantics.Crate.mk _root_.Captured.program _root_.Spec.specs)
end Expected

end
";
    let expected_path = stage_dir.join("Expected.lean");
    fs::write(&expected_path, expected_src).unwrap();
    modules.push(TargetModule {
        module: "Expected".to_owned(),
        source: expected_path,
        expected_sha256: sha256_bytes(expected_src.as_bytes()),
        role: TargetRole::Expected,
    });

    let proof_path = stage_dir.join("Proof.lean");
    fs::write(&proof_path, proof_src).unwrap();
    modules.push(TargetModule {
        module: "Proof".to_owned(),
        source: proof_path,
        expected_sha256: sha256_bytes(proof_src.as_bytes()),
        role: TargetRole::Proof,
    });

    let zero_hash = "0".repeat(64);
    TargetAuditRequest {
        modules,
        theorem_module: "Proof".to_owned(),
        theorem_name: "Proof.verify".to_owned(),
        expected_module: "Expected".to_owned(),
        expected_declaration: "Expected.claim".to_owned(),
        canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
        subject_declaration: "Captured.program".to_owned(),
        specification_declaration: "Spec.specs".to_owned(),
        allow_sorry_in_proof,
        bindings: TargetBindings {
            request_sha256: zero_hash.clone(),
            capture_sha256: zero_hash.clone(),
            model_manifest_sha256: zero_hash.clone(),
            specification_manifest_sha256: zero_hash,
        },
    }
}

fn new_v435_checker(lean: &Path) -> Checker {
    let mut checker = Checker::new(&repo_root(), Some(lean)).expect("create checker");
    checker.set_allow_unpinned_lean(true);
    checker.set_sandbox_mode(SandboxMode::PreferBwrapOrLandlock);
    checker
}

#[path = "ndjson_comparator_e2e/scalar_and_adversarial_proofs.rs"]
mod scalar_and_adversarial_proofs;
#[cfg(unix)]
#[path = "ndjson_comparator_e2e/synthetic_comparator.rs"]
mod synthetic_comparator;
#[path = "ndjson_comparator_e2e/v435_preflight_and_gates.rs"]
mod v435_preflight_and_gates;
