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
//! and adversarial negative fixtures (mutated claim, custom axiom, `opaque`
//! stub, `partial def`, and `sorryAx` with and without
//! `--allow-sorry-in-proof`).

use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use cargo_anneal::{
    ActiveSandbox, Checker, PINNED_INIT_PRIMITIVES, SandboxMode, TargetAuditRequest,
    TargetBindings, TargetModule, TargetRole, sha256_bytes,
};
use serde_json::json;
use tempfile::TempDir;

const SCALAR_SPEC: &str = include_str!("fixtures/scalar/Spec.lean");
const SCALAR_PROOF: &str = include_str!("fixtures/scalar/Proof.lean");

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("trusted/")
        .parent()
        .expect("anneal/")
        .to_path_buf()
}

/// Locate a Lean `v4.35.0+` binary bundling `leanexport`, `nanoda_bin`, and
/// `con-ron` under `<prefix>/bin/`. Returns `None` on `v4.34.1`-only hosts so
/// workspace test suites running under `v4.34.1` do not fail spuriously.
fn discover_v435_lean() -> Option<PathBuf> {
    if let Some(raw) = env::var_os("ANNEAL_LEAN_V435")
        && !raw.is_empty()
    {
        let p = PathBuf::from(raw);
        if p.is_file() {
            return Some(p);
        }
    }
    let home = env::var_os("HOME").map(PathBuf::from)?;
    let candidate = home.join(".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean");
    if candidate.is_file() {
        return Some(candidate);
    }
    None
}

/// Stage a minimal self-contained `scalar` target verification workspace using
/// the canonical `trusted/lean` and `theory/Anneal` sources from the repository
/// plus a synthetic captured `zero()` program matching `fixtures/scalar/lib.rs`.
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

    // Minimal closed `Captured.program` matching `pub fn zero() -> u64 { 0 }`.
    let captured_src = "\
prelude
import Trusted.MirAst

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

    let expected_src = "\
prelude
import Trusted.MirSemantics
import Captured
import Spec

namespace Expected
def claim : Prop := _root_.Trusted.MirSemantics.UnitTheorem (_root_.Trusted.MirSemantics.Crate.mk _root_.Captured.program _root_.Spec.specs)
end Expected
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

#[test]
fn scalar_ndjson_comparator_default_dual_kernels_and_paranoid_quorum() {
    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 NDJSON comparator e2e test (v4.35.0 toolchain not installed)");
        return;
    };
    let tmp = TempDir::new().unwrap();
    let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, SCALAR_PROOF, false);

    // 1. Default run: 5a + 5b + 5c (`nanoda_bin` + `con-ron`), zero
    // `TrustedBoundary.lean` execution.
    let mut checker = new_v435_checker(&lean);
    let t0 = Instant::now();
    let report = checker.run_target(&req).expect("scalar NDJSON comparator must pass");
    let elapsed_ms = t0.elapsed().as_millis();
    eprintln!(
        "[real measurement] scalar full compile+audit: {elapsed_ms} ms | 5a+5b+5c breakdown: {}",
        report["timingMs"]
    );

    assert_eq!(report["auditMode"], json!("ndjson_comparator"));
    #[cfg(target_os = "linux")]
    assert_eq!(
        checker.active_sandbox(),
        Some(ActiveSandbox::LinuxBwrap),
        "must execute v4.35.0 NDJSON comparator under Tier-1 bwrap + seccomp"
    );
    assert_eq!(report["replay"], json!(true));
    assert_eq!(report["exactType"], json!(true));
    assert_eq!(report["pinnedPrimitivesCount"], json!(PINNED_INIT_PRIMITIVES.len()));
    assert_eq!(report["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));
    assert_eq!(report["paranoidQuorum"], json!(false));
    assert!(report.get("kernelsSkipped").is_none());
    assert_eq!(report["sorryDeclarations"], json!([]));

    // Verify `expectedConeSha256`, `proofNdjsonSha256`, `initPrimitivesSha256`
    // are 64-char hex digests.
    for key in ["expectedConeSha256", "proofNdjsonSha256", "initPrimitivesSha256"] {
        let hex = report[key].as_str().expect("missing digest");
        assert!(cargo_anneal::is_sha256_hex(hex), "invalid digest for {key}: {hex}");
    }

    // 2. Unfolded canonical theorem type (`UnitTheorem ⟨Captured.program,
    // Spec.specs⟩`, without importing `Expected`, matching `spin/Proof.lean`).
    let unfolded_proof = SCALAR_PROOF.replace(
        "theorem verify : Expected.claim := by",
        "theorem verify : UnitTheorem ⟨Captured.program, Spec.specs⟩ := by",
    );
    let tmp_unfolded = TempDir::new().unwrap();
    let req_unfolded =
        build_scalar_target_request(tmp_unfolded.path(), SCALAR_SPEC, &unfolded_proof, false);
    let rep_unfolded = checker
        .run_target(&req_unfolded)
        .expect("unfolded canonical theorem type must pass");
    assert_eq!(rep_unfolded["auditMode"], json!("ndjson_comparator"));
    assert_eq!(rep_unfolded["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));

    // 3. Optional `--paranoid-quorum` runs all four independent non-Replay
    // bundled Lean v4.35.0 NDJSON kernels (`nanoda_bin`, `con-ron`,
    // `con-leche`, `lean4lean`) directly inside `ExecSeal`.
    checker.set_paranoid_quorum(true);
    let t_paranoid = Instant::now();
    let rep_paranoid = checker
        .run_target(&req)
        .expect("scalar --paranoid-quorum must pass");
    eprintln!(
        "[real measurement] scalar --paranoid-quorum (4 kernels) full: {} ms | breakdown: {}",
        t_paranoid.elapsed().as_millis(),
        rep_paranoid["timingMs"]
    );
    assert_eq!(rep_paranoid["paranoidQuorum"], json!(true));
    assert_eq!(
        rep_paranoid["kernelsPassed"],
        json!(["nanoda_bin", "con-ron", "con-leche", "lean4lean"])
    );
    assert!(rep_paranoid.get("kernelsSkipped").is_none());
}

#[test]
fn scalar_ndjson_comparator_rejects_adversarial_proofs() {
    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 NDJSON comparator negative tests (v4.35.0 not installed)");
        return;
    };
    let mut checker = new_v435_checker(&lean);

    // 1. Wrong theorem statement (`theorem verify : True := True.intro`).
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = "prelude\nimport Expected\nnamespace Proof\ntheorem verify : True := True.intro\nend Proof\n";
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "wrong theorem statement must fail with policy code 1: {err}");
    }

    // 2. Unpermitted custom axiom in `Proof.lean`.
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = "prelude\nimport Expected\nnamespace Proof\naxiom cheat : Expected.claim\ntheorem verify : Expected.claim := cheat\nend Proof\n";
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "custom axiom must fail with policy code 1: {err}");
        assert!(err.message.contains("Proof.cheat"), "{err}");
    }

    // 3. Constructive `opaque` stub in `Proof.lean` (closed `.opaqueInfo` ban).
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = SCALAR_PROOF.replace(
            "theorem verify : Expected.claim := by",
            "opaque stubNat : Nat := 0\ntheorem useStub : stubNat = stubNat := rfl\ntheorem verify : Expected.claim := by\n  have _ := useStub",
        );
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, &bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "opaque stub must fail with policy code 1: {err}");
        assert!(err.message.contains("opaque"), "{err}");
    }

    // 4. `partial def` in `Proof.lean` (exported as opaque/partial and rejected
    // by the closed `.opaqueInfo` / `partial` ban).
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = SCALAR_PROOF.replace(
            "theorem verify : Expected.claim := by",
            "partial def loopNat (n : Nat) : Nat := loopNat (n + 1)\ntheorem usePartial : loopNat 0 = loopNat 0 := rfl\ntheorem verify : Expected.claim := by\n  have _ := usePartial",
        );
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, &bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "partial def must fail with policy code 1: {err}");
        assert!(
            err.message.contains("opaque") || err.message.contains("partial"),
            "{err}"
        );
    }

    // 5. `sorryAx` rejected by default, admitted only when
    // `allow_sorry_in_proof = true` (reporting `sorryDeclarations` and honest
    // `con-ron` skip).
    {
        let tmp = TempDir::new().unwrap();
        let sorry_proof = "prelude\nimport Expected\nnamespace Proof\ntheorem verify : Expected.claim := sorry\nend Proof\n";
        let req_strict = build_scalar_target_request(tmp.path(), SCALAR_SPEC, sorry_proof, false);
        let err = checker.run_target(&req_strict).unwrap_err();
        assert_eq!(err.code, 1, "sorry must be rejected when allow_sorry_in_proof=false: {err}");
        assert!(err.message.contains("sorryAx"), "{err}");

        let req_tainted = build_scalar_target_request(tmp.path(), SCALAR_SPEC, sorry_proof, true);
        let rep = checker
            .run_target(&req_tainted)
            .expect("sorry must pass when allow_sorry_in_proof=true");
        assert_eq!(rep["auditMode"], json!("ndjson_comparator"));
        assert_eq!(rep["sorryDeclarations"], json!(["Proof.verify"]));
        assert_eq!(rep["kernelsPassed"], json!(["nanoda_bin"]));
        assert_eq!(
            rep["kernelsSkipped"],
            json!([{"kernel": "con-ron", "reason": "sorryAx_present_under_allow_sorry_in_proof"}])
        );
    }
}

#[test]
fn spec_preflight_enforces_4130_bans_and_module_reservation_on_v435() {
    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 SpecPreflight e2e test (v4.35.0 toolchain not installed)");
        return;
    };
    let mut checker = new_v435_checker(&lean);

    // 1. Reserved toolchain/inspector roots must fail closed before preflight.
    for reserved in ["SpecPreflight", "SpecPreflight.Extra", "TrustedBoundary", "Init.System.IO"] {
        let tmp = TempDir::new().unwrap();
        let mut req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, SCALAR_PROOF, false);
        let dummy_src = tmp.path().join("Reserved.lean");
        let bytes = b"prelude\n";
        fs::write(&dummy_src, bytes).unwrap();
        req.modules.push(TargetModule {
            module: reserved.to_owned(),
            source: dummy_src,
            expected_sha256: sha256_bytes(bytes),
            role: TargetRole::Proof,
        });
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "reserved module `{reserved}` must fail with policy code 1: {err}");
        assert_eq!(err.phase, "target-input", "{err}");
    }

    // 2. #4130 spec-preflight parser/identifier bans must hold in
    // `SpecPreflight.lean` on Lean v4.35.0 (not only in `TrustedBoundary.lean`).
    let cases = [
        ("term-panic", "def p : Nat := panic! \"boom\"\n", "Lean.Parser.Term.panic"),
        ("direct-panic-core", "def pc : Nat := panicCore \"boom\"\n", "panicCore"),
        (
            "term-mod-cast",
            "theorem mc (n : Nat) : (n : Int) = (n : Int) := mod_cast (rfl : n = n)\n",
            "Lean.modCast",
        ),
        (
            "contract-decl-val",
            "def contracted (n : Nat) : Nat\nrequires True\nensures _ => True\n:= n\n",
            "Lean.Parser.Command.contractDeclVal",
        ),
        ("term-qed-try", "theorem t : True := ∎\n", "«term∎»"),
    ];
    for (label, snippet, expected_tok) in cases {
        let mut bad_spec = SCALAR_SPEC.replace("end Spec", &format!("{snippet}\nend Spec"));
        if label == "term-qed-try" {
            bad_spec = bad_spec.replace(
                "import Trusted.MirSemantics",
                "import Trusted.MirSemantics\nimport Init",
            );
        }
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &bad_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "{label} must fail with policy code 1: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(
            err.message.contains(expected_tok),
            "{label}: expected `{expected_tok}` in `{}`",
            err.message
        );
    }
}
