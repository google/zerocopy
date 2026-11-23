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

fn run_all_4_v435_kernels_raw(lean_bin: &Path, ndjson_path: &Path) {
    use std::process::Command;
    let bin_dir = lean_bin.parent().expect("bin/");
    let sysroot = bin_dir.parent().expect("sysroot/");
    let tmp = TempDir::new().unwrap();
    let cfg_path = tmp.path().join("nanoda_cfg.json");
    let cfg = cargo_anneal::ndjson_comparator::build_nanoda_config_json(
        ndjson_path.to_str().unwrap(),
        false,
        2,
    );
    fs::write(&cfg_path, serde_json::to_vec(&cfg).unwrap()).unwrap();

    let nanoda_out = Command::new(bin_dir.join("nanoda_bin")).arg(&cfg_path).output().unwrap();
    assert!(
        nanoda_out.status.success(),
        "nanoda_bin failed: {} {}",
        String::from_utf8_lossy(&nanoda_out.stdout),
        String::from_utf8_lossy(&nanoda_out.stderr)
    );

    for tool in ["con-ron", "con-leche"] {
        let out = Command::new(bin_dir.join(tool))
            .args(["--verified", "--jobs=1"])
            .arg(ndjson_path)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{tool} failed: {} {}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }

    let l4l_out = Command::new(bin_dir.join("lean4lean"))
        .arg("--import")
        .arg(ndjson_path)
        .env("LEAN_SYSROOT", sysroot)
        .env("LEAN_PATH", sysroot.join("lib/lean"))
        .output()
        .unwrap();
    assert!(
        l4l_out.status.success(),
        "lean4lean failed: {} {}",
        String::from_utf8_lossy(&l4l_out.stdout),
        String::from_utf8_lossy(&l4l_out.stderr)
    );
}

#[test]
fn m3_lambda_lifting_bit_trie_lrat_and_classical_em_on_v435() {
    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 M3 e2e test (v4.35.0 toolchain not installed)");
        return;
    };

    // Proof exercises:
    // 1. `Anneal.MirWp` via internal helper `Proof.totalCorrectness`,
    // 2. `Anneal.BitTrieLrat.sampleUnsat_verified` (LRAT checker theorem),
    // 3. `Anneal.ClassicalEm.prop_em` (uses `Classical.choice`, `Quot.sound`,
    //    `propext` strictly inside its proof body -> `PoC-2` conservation!),
    // 4. Universe-polymorphic helper `Proof.polyHelper.{u}` (`Option B`!).
    let rich_proof = "\
prelude
import Expected
import Anneal.MirWp
import Anneal.BitTrieLrat
import Anneal.ClassicalEm

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem polyHelper.{u} (α : Sort u) (h : α) : True ∨ ¬ True :=
  let _ := h
  Anneal.ClassicalEm.prop_em True

theorem execution :
    execProg (entryProgForBody Captured.program 0) 2 { args := [] }
      (fun outcome => outcome = Spec.expectedReturn) := rfl

theorem totalCorrectness : Spec.returnsZero Captured.program := by
  have _h_unsat := Anneal.BitTrieLrat.sampleUnsat_verified
  have _h_em := polyHelper.{1} Nat 0
  have ⟨post, terminates, out, returned, result⟩ :=
    wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
      { args := [] } 2 (fun outcome => outcome = Spec.expectedReturn)
      (wpProg_of_execProg execution)
  exact ⟨post, terminates, result ▸ returned⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, totalCorrectness⟩
  intro id body found
  cases id with
  | zero =>
      have same : Captured.program.bodies[0] = body := Option.some.inj found
      subst body
      refine ⟨found, rfl, ?_⟩
      intro args valid _
      cases args with
      | nil => exact totalCorrectness.1.1
      | cons _ _ => cases valid
  | succ id => cases found

end Proof
";

    let tmp_m3 = TempDir::new().unwrap();
    let req_m3 = build_scalar_target_request(tmp_m3.path(), SCALAR_SPEC, rich_proof, false);
    let mut checker = new_v435_checker(&lean);
    checker.set_paranoid_quorum(true);

    let t_m3 = Instant::now();
    let rep_m3 = checker.run_target(&req_m3).expect("M3 4-kernel quorum must pass");
    eprintln!(
        "[real measurement] M3 4-kernel run: {} ms | promo: {} | timing: {}",
        t_m3.elapsed().as_millis(),
        rep_m3["axiomPromotion"],
        rep_m3["timingMs"]
    );

    assert_eq!(rep_m3["kernelsPassed"], json!(["nanoda_bin", "con-ron", "con-leche", "lean4lean"]));
    let promo = &rep_m3["axiomPromotion"];
    assert_eq!(promo["mode"], json!("m3_lambda_lifted"));
    let pre_decls = promo["preM3Declarations"].as_u64().unwrap();
    let post_decls = promo["postM3Declarations"].as_u64().unwrap();
    assert!(
        post_decls < pre_decls,
        "M3 must prune theory proof bodies: post={post_decls} vs pre={pre_decls}"
    );
    let lifted_names: Vec<&str> = promo["liftedHypotheses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| h["name"].as_str().unwrap())
        .collect();
    assert!(lifted_names.contains(&"Anneal.BitTrieLrat.sampleUnsat_verified"), "{lifted_names:?}");
    assert!(lifted_names.contains(&"Anneal.ClassicalEm.prop_em"), "{lifted_names:?}");

    // PoC-2: `Classical.choice`, `Quot.sound`, and `propext` from `prop_em`'s
    // garbage-collected proof body MUST remain in `rep_m3["axioms"]`!
    assert_eq!(rep_m3["axioms"], json!(["Classical.choice", "Quot.sound", "propext"]));

    // Compare against `--full-theory-replay` opt-out!
    let mut full_checker = new_v435_checker(&lean);
    full_checker.set_paranoid_quorum(true);
    full_checker.set_full_theory_replay(true);
    let tmp_full = TempDir::new().unwrap();
    let req_full = build_scalar_target_request(tmp_full.path(), SCALAR_SPEC, rich_proof, false);
    let t_full = Instant::now();
    let rep_full =
        full_checker.run_target(&req_full).expect("--full-theory-replay 4-kernel quorum must pass");
    eprintln!(
        "[real measurement] --full-theory-replay 4-kernel run: {} ms | timing: {}",
        t_full.elapsed().as_millis(),
        rep_full["timingMs"]
    );
    assert_eq!(rep_full["axiomPromotion"]["mode"], json!("full_theory_replay"));
    assert_eq!(rep_full["replayedDeclarations"].as_u64().unwrap(), pre_decls);
}

#[test]
fn m3_live_pentest_negative_suite_and_multi_shard_zero_axiom_link_on_v435() {
    use std::{collections::BTreeSet, io::BufReader, process::Command};

    use cargo_anneal::{
        CanonicalArena, LiftedHypothesisRecord, M3LinkShardInput, ModularShardNode,
        StructuralCompareRequest, build_promoted_allowlist, compute_cone_digest,
        link_m3_shards_to_zero_axioms, ndjson_comparator::parse_ndjson_reader,
        verify_modular_shard_dag, verify_ndjson_and_apply_m3,
        verify_shard_binders_against_m3_env,
    };

    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 M3 pentest e2e suite (v4.35.0 not installed)");
        return;
    };
    let bin_dir = lean.parent().expect("bin/");
    let sysroot = bin_dir.parent().expect("sysroot/");
    let mut checker = new_v435_checker(&lean);

    // 1. Live PoC-1a: free `Type` carrier axiom in `Proof.lean` fails closed
    // (`code == 1`).
    {
        let tmp = TempDir::new().unwrap();
        let poc1a_proof = "\
prelude
import Expected
namespace Proof
axiom freeCarrier : ∀ (α : Type), Nonempty α → False
theorem verify : Expected.claim := False.elim (freeCarrier Nat ⟨0⟩)
end Proof
";
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, poc1a_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "PoC-1a must fail closed: {err}");
    }

    // 2. Live PoC-3: namespace prefix spoofing (`Anneal.MirWp.forgedFalse`)
    // fails closed (`code == 1`).
    {
        let tmp = TempDir::new().unwrap();
        let poc3_proof = "\
prelude
import Expected
import Anneal.MirWp
namespace Anneal.MirWp
axiom forgedFalse : Expected.claim
end Anneal.MirWp
namespace Proof
theorem verify : Expected.claim := Anneal.MirWp.forgedFalse
end Proof
";
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, poc3_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "PoC-3 must fail closed: {err}");
    }

    // 3. Live PoC-5a: Lean 4 `module` system `.olean` + `.olean.private` with
    // unexposed `sorry` is caught by `leanexport` + `build_promoted_allowlist`,
    // AND deleting `.olean.private` causes `leanexport` to fail closed!
    {
        let tmp = TempDir::new().unwrap();
        let mod_src = tmp.path().join("ModHidden.lean");
        fs::write(
            &mod_src,
            "module\nprelude\npublic import Init.Core\npublic section\ntheorem secretSorry : True := sorry\nend\n",
        )
        .unwrap();
        let st = Command::new(&lean)
            .args([
                "-R",
                tmp.path().to_str().unwrap(),
                "-o",
                tmp.path().join("ModHidden.olean").to_str().unwrap(),
                mod_src.to_str().unwrap(),
            ])
            .env("LEAN_SYSROOT", sysroot)
            .env(
                "LEAN_PATH",
                format!("{}:{}", tmp.path().display(), sysroot.join("lib/lean").display()),
            )
            .status()
            .unwrap();
        assert!(st.success(), "compile ModHidden.lean");
        assert!(tmp.path().join("ModHidden.olean.private").is_file());

        let exp_out = Command::new(bin_dir.join("leanexport"))
            .args(["ModHidden", "--", "secretSorry"])
            .env("LEAN_SYSROOT", sysroot)
            .env(
                "LEAN_PATH",
                format!("{}:{}", tmp.path().display(), sysroot.join("lib/lean").display()),
            )
            .output()
            .unwrap();
        assert!(exp_out.status.success());

        let init_out = Command::new(bin_dir.join("leanexport"))
            .arg("Init")
            .arg("--")
            .args(PINNED_INIT_PRIMITIVES)
            .env("LEAN_SYSROOT", sysroot)
            .env("LEAN_PATH", sysroot.join("lib/lean"))
            .output()
            .unwrap();
        assert!(init_out.status.success());

        let mut arena = CanonicalArena::new();
        let init_env =
            parse_ndjson_reader(BufReader::new(init_out.stdout.as_slice()), &mut arena, "init")
                .unwrap();
        let mod_env = parse_ndjson_reader(
            BufReader::new(exp_out.stdout.as_slice()),
            &mut arena,
            "mod_hidden",
        )
        .unwrap();
        let err_5a = build_promoted_allowlist(
            &mut arena,
            &init_env,
            &mod_env,
            &["secretSorry".to_owned()],
            &[],
            &"0".repeat(64),
        )
        .unwrap_err();
        assert_eq!(err_5a.code, 1, "PoC-5a sorryAx must be rejected: {err_5a}");
        assert!(err_5a.message.contains("sorryAx"), "{err_5a}");

        // Delete `.olean.private` -> `leanexport` must fail closed!
        fs::remove_file(tmp.path().join("ModHidden.olean.private")).unwrap();
        let missing_priv = Command::new(bin_dir.join("leanexport"))
            .args(["ModHidden", "--", "secretSorry"])
            .env("LEAN_SYSROOT", sysroot)
            .env(
                "LEAN_PATH",
                format!("{}:{}", tmp.path().display(), sysroot.join("lib/lean").display()),
            )
            .output()
            .unwrap();
        assert!(
            !missing_priv.status.success(),
            "leanexport must fail closed when .olean.private is removed"
        );

        // 4. Live Multi-Shard Tier-4 DAG (`AnnealTheory -> Shard1 -> Shard2`)
        // + PoC-6b + PoC-4 live Merkle rejection + PoC-7b 4-kernel link!
        let p_dir = tmp.path().join("shards");
        fs::create_dir_all(&p_dir).unwrap();
        let lean_path_env = format!("{}:{}", p_dir.display(), sysroot.join("lib/lean").display());
        let compile_mod = |name: &str, code: &str| {
            let src = p_dir.join(format!("{name}.lean"));
            fs::write(&src, code).unwrap();
            let st = Command::new(&lean)
                .args([
                    "-R",
                    p_dir.to_str().unwrap(),
                    "-o",
                    p_dir.join(format!("{name}.olean")).to_str().unwrap(),
                    "-j1",
                    src.to_str().unwrap(),
                ])
                .env("LEAN_SYSROOT", sysroot)
                .env("LEAN_PATH", &lean_path_env)
                .status()
                .unwrap();
            assert!(st.success(), "compile {name}");
        };
        let export_decls = |mods: &[&str], decls: &[&str]| -> Vec<u8> {
            let out = Command::new(bin_dir.join("leanexport"))
                .args(mods)
                .arg("--")
                .args(decls)
                .env("LEAN_SYSROOT", sysroot)
                .env("LEAN_PATH", &lean_path_env)
                .output()
                .unwrap();
            assert!(out.status.success(), "export {mods:?}");
            out.stdout
        };

        compile_mod(
            "AnnealTheory",
            "prelude\nimport Init.Core\nnamespace AnnealTheory\ndef tagNat (x : Nat) : Nat := x + 0\ntheorem add_zero_eq.{u} (α : Sort u) (_w : α) (n : Nat) : tagNat n = n := Nat.add_zero n\nend AnnealTheory\n",
        );
        compile_mod(
            "Common",
            "prelude\nimport Init.Core\nnamespace Trusted.MirSemantics\ndef Crate.mk (a b : Prop) : Prop := a ∧ b\ndef UnitTheorem (p : Prop) : Prop := p\nend Trusted.MirSemantics\nnamespace Captured\ndef p1 : Prop := ∀ n : Nat, n + 0 = n\ndef p2 : Prop := ∀ n : Nat, (n + 0) + 0 = n\nend Captured\nnamespace Spec\ndef s1 : Prop := True\ndef s2 : Prop := True\nend Spec\n",
        );
        compile_mod(
            "Exp1",
            "prelude\nimport Common\nnamespace Exp1\ndef claim : Prop := Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.p1 Spec.s1)\nend Exp1\n",
        );
        compile_mod(
            "Shard1",
            "prelude\nimport Exp1\nimport AnnealTheory\nnamespace Shard1\ntheorem verify : Exp1.claim := ⟨fun n => AnnealTheory.add_zero_eq.{1} Nat 0 n, True.intro⟩\nend Shard1\n",
        );
        compile_mod(
            "Exp2",
            "prelude\nimport Common\nnamespace Exp2\ndef claim : Prop := Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.p2 Spec.s2)\nend Exp2\n",
        );
        compile_mod(
            "Shard2",
            "prelude\nimport Exp2\nimport Shard1\nimport AnnealTheory\nnamespace Shard2\ntheorem verify : Exp2.claim := ⟨fun n => Eq.trans (AnnealTheory.add_zero_eq.{1} Nat 0 (n + 0)) (Shard1.verify.1 n), True.intro⟩\nend Shard2\n",
        );

        let ci_bytes = export_decls(&["AnnealTheory"], &["AnnealTheory.add_zero_eq"]);
        let exp1_bytes = export_decls(&["Exp1"], &["Exp1.claim"]);
        let s1_bytes = export_decls(&["Exp1", "Shard1"], &["Exp1.claim", "Shard1.verify"]);
        let exp2_bytes = export_decls(&["Exp2"], &["Exp2.claim"]);
        let s2_bytes = export_decls(&["Exp2", "Shard2"], &["Exp2.claim", "Shard2.verify"]);

        let mut link_arena = CanonicalArena::new();
        let link_init = parse_ndjson_reader(
            BufReader::new(init_out.stdout.as_slice()),
            &mut link_arena,
            "init",
        )
        .unwrap();
        let ci_env =
            parse_ndjson_reader(BufReader::new(ci_bytes.as_slice()), &mut link_arena, "ci")
                .unwrap();
        let base_allow = build_promoted_allowlist(
            &mut link_arena,
            &link_init,
            &ci_env,
            &["AnnealTheory".to_owned()],
            &[],
            &"1".repeat(64),
        )
        .unwrap();

        // Verify Shard 1 via M3 and run all 4 kernels on Shard 1's M3 stream!
        let exp1_env =
            parse_ndjson_reader(BufReader::new(exp1_bytes.as_slice()), &mut link_arena, "exp1")
                .unwrap();
        let s1_env =
            parse_ndjson_reader(BufReader::new(s1_bytes.as_slice()), &mut link_arena, "s1")
                .unwrap();
        let req1 = StructuralCompareRequest {
            theorem_name: "Shard1.verify",
            expected_declaration: "Exp1.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.p1",
            specification_declaration: "Spec.s1",
            allow_sorry_in_proof: false,
            forbidden_expected_roots: BTreeSet::from([
                "AnnealTheory".to_owned(),
                "Shard1".to_owned(),
            ]),
            forbidden_expected_modules: BTreeSet::from(["Shard1".to_owned()]),
            capture_modules: vec!["Captured".to_owned()],
            model_modules: vec!["Trusted.MirSemantics".to_owned()],
            specification_modules: vec!["Spec".to_owned()],
        };
        let m3_s1 = verify_ndjson_and_apply_m3(
            &mut link_arena,
            &link_init,
            &exp1_env,
            &s1_env,
            &sha256_bytes(&s1_bytes),
            &req1,
            &base_allow,
            false,
        )
        .unwrap();
        let (s1_m3_text, s1_m3_env) = m3_s1.rewritten_ndjson.unwrap();
        let s1_m3_file = p_dir.join("s1_m3.ndjson");
        fs::write(&s1_m3_file, s1_m3_text.as_bytes()).unwrap();
        run_all_4_v435_kernels_raw(&lean, &s1_m3_file);

        // Live PoC-4 check on `s1_bytes`: mutate `tagNat` -> cone mismatch!
        let s1_str = String::from_utf8(s1_bytes.clone()).unwrap();
        let mut tampered_lines = Vec::new();
        let mut mutated_tag_nat = false;
        let mut tag_nat_nid = None;
        for line in s1_str.lines() {
            if let Ok(mut obj) = serde_json::from_str::<serde_json::Value>(line) {
                if obj.get("str").and_then(|s| s.get("str")).and_then(|v| v.as_str())
                    == Some("tagNat")
                {
                    tag_nat_nid = obj.get("in").and_then(|v| v.as_u64());
                }
                if let Some(tnid) = tag_nat_nid
                    && let Some(def_obj) = obj.get_mut("def").and_then(|v| v.as_object_mut())
                    && def_obj.get("name").and_then(|v| v.as_u64()) == Some(tnid)
                {
                    def_obj["hints"] = json!("opaque");
                    mutated_tag_nat = true;
                }
                tampered_lines.push(serde_json::to_string(&obj).unwrap());
            }
        }
        assert!(mutated_tag_nat, "must locate AnnealTheory.tagNat in live export");
        let tampered_s1 = tampered_lines.join("\n") + "\n";
        let tampered_s1_env = parse_ndjson_reader(
            BufReader::new(tampered_s1.as_bytes()),
            &mut link_arena,
            "tampered_s1",
        )
        .unwrap();
        let err_poc4 = verify_ndjson_and_apply_m3(
            &mut link_arena,
            &link_init,
            &exp1_env,
            &tampered_s1_env,
            &sha256_bytes(tampered_s1.as_bytes()),
            &req1,
            &base_allow,
            false,
        )
        .unwrap_err();
        assert_eq!(err_poc4.code, 1, "Live PoC-4 must fail closed: {err_poc4}");
        assert!(err_poc4.message.contains("Merkle constant-cone mismatch"), "{err_poc4}");

        // Register `Shard1.verify`'s cone into Shard 2's allowlist (`Tier 4a`).
        let s1_thm_id = link_arena.intern_dotted_name("Shard1.verify");
        let s1_contract_cone =
            compute_cone_digest(&link_arena, &s1_env, s1_thm_id, "s1_cone").unwrap();
        let mut s2_allow = base_allow.clone();
        s2_allow.entries.insert(
            "Shard1.verify".to_owned(),
            cargo_anneal::PromotedTheoremEntry {
                name: "Shard1.verify".to_owned(),
                module: "Shard1".to_owned(),
                num_level_params: 0,
                cone_merkle_sha256: s1_contract_cone.clone(),
                used_foundation_axioms: m3_s1.summary.axioms.clone(),
                model_closure: m3_s1.summary.model_closure.clone(),
            },
        );

        let exp2_env =
            parse_ndjson_reader(BufReader::new(exp2_bytes.as_slice()), &mut link_arena, "exp2")
                .unwrap();
        let s2_env =
            parse_ndjson_reader(BufReader::new(s2_bytes.as_slice()), &mut link_arena, "s2")
                .unwrap();
        let req2 = StructuralCompareRequest {
            theorem_name: "Shard2.verify",
            expected_declaration: "Exp2.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.p2",
            specification_declaration: "Spec.s2",
            allow_sorry_in_proof: false,
            forbidden_expected_roots: BTreeSet::from([
                "AnnealTheory".to_owned(),
                "Shard1".to_owned(),
                "Shard2".to_owned(),
            ]),
            forbidden_expected_modules: BTreeSet::from(["Shard1".to_owned(), "Shard2".to_owned()]),
            capture_modules: vec!["Captured".to_owned()],
            model_modules: vec!["Trusted.MirSemantics".to_owned()],
            specification_modules: vec!["Spec".to_owned()],
        };
        let m3_s2 = verify_ndjson_and_apply_m3(
            &mut link_arena,
            &link_init,
            &exp2_env,
            &s2_env,
            &sha256_bytes(&s2_bytes),
            &req2,
            &s2_allow,
            false,
        )
        .unwrap();
        let (s2_m3_text, s2_m3_env) = m3_s2.rewritten_ndjson.unwrap();
        let s2_m3_file = p_dir.join("s2_m3.ndjson");
        fs::write(&s2_m3_file, s2_m3_text.as_bytes()).unwrap();
        run_all_4_v435_kernels_raw(&lean, &s2_m3_file);

        let s2_thm_id = link_arena.intern_dotted_name("Shard2.verify");
        let s2_contract_cone =
            compute_cone_digest(&link_arena, &s2_env, s2_thm_id, "s2_cone").unwrap();

        verify_shard_binders_against_m3_env(
            &mut link_arena,
            &s1_m3_env,
            &[&ci_env],
            "Shard1.verify",
            "Exp1.claim",
            &m3_s1.promotion_report.lifted_hypotheses,
        )
        .unwrap();
        verify_shard_binders_against_m3_env(
            &mut link_arena,
            &s2_m3_env,
            &[&ci_env, &s1_env],
            "Shard2.verify",
            "Exp2.claim",
            &m3_s2.promotion_report.lifted_hypotheses,
        )
        .unwrap();

        // Negative checks: reordering `[H1, H2] -> [H2, H1]` OR substituting
        // an allowlisted `AnnealTheory.add_zero_eq` entry for `Shard1.verify`
        // MUST fail closed on exact instantiated domain-type mismatch!
        assert_eq!(m3_s2.promotion_report.lifted_hypotheses.len(), 2);
        let mut reordered_s2 = m3_s2.promotion_report.lifted_hypotheses.clone();
        reordered_s2.swap(0, 1);
        let reorder_err = verify_shard_binders_against_m3_env(
            &mut link_arena,
            &s2_m3_env,
            &[&ci_env, &s1_env],
            "Shard2.verify",
            "Exp2.claim",
            &reordered_s2,
        )
        .unwrap_err();
        assert_eq!(reorder_err.code, 1);
        assert!(
            reorder_err.message.contains("instantiated type does not match"),
            "{reorder_err}"
        );

        let mut spoof_sub_s2 = m3_s2.promotion_report.lifted_hypotheses.clone();
        let theory_hyp = spoof_sub_s2
            .iter()
            .find(|h| h.name == "AnnealTheory.add_zero_eq")
            .unwrap()
            .clone();
        for h in &mut spoof_sub_s2 {
            *h = theory_hyp.clone();
        }
        let spoof_sub_err = verify_shard_binders_against_m3_env(
            &mut link_arena,
            &s2_m3_env,
            &[&ci_env, &s1_env],
            "Shard2.verify",
            "Exp2.claim",
            &spoof_sub_s2,
        )
        .unwrap_err();
        assert_eq!(spoof_sub_err.code, 1);
        assert!(
            spoof_sub_err.message.contains("instantiated type does not match"),
            "{spoof_sub_err}"
        );

        // Verify Tarjan union-SCC accepts `Shard2 -> Shard1`!
        let dag_ok = verify_modular_shard_dag(
            &[
                ModularShardNode {
                    shard_id: "shard1".to_owned(),
                    theorem_name: "Shard1.verify".to_owned(),
                    contract_cone_sha256: s1_contract_cone.clone(),
                    mir_direct_callees: BTreeSet::new(),
                    indirect_call_provenance: BTreeSet::new(),
                    m3_lifted_hypotheses: m3_s1.promotion_report.lifted_hypotheses.clone(),
                    local_axioms: m3_s1.summary.axioms.iter().cloned().collect(),
                    local_sorry_declarations: BTreeSet::new(),
                    local_taint_reasons: BTreeSet::new(),
                    local_model_closure: m3_s1.summary.model_closure.clone(),
                },
                ModularShardNode {
                    shard_id: "shard2".to_owned(),
                    theorem_name: "Shard2.verify".to_owned(),
                    contract_cone_sha256: s2_contract_cone.clone(),
                    mir_direct_callees: BTreeSet::from(["shard1".to_owned()]),
                    indirect_call_provenance: BTreeSet::new(),
                    m3_lifted_hypotheses: m3_s2.promotion_report.lifted_hypotheses.clone(),
                    local_axioms: m3_s2.summary.axioms.iter().cloned().collect(),
                    local_sorry_declarations: BTreeSet::new(),
                    local_taint_reasons: BTreeSet::new(),
                    local_model_closure: m3_s2.summary.model_closure.clone(),
                },
            ],
            &base_allow,
            &Default::default(),
        )
        .unwrap();
        assert_eq!(dag_ok.len(), 2);

        // Live PoC-6b: inject reverse proof hypothesis `Shard1 -> Shard2`
        // with 0 MIR calls -> REJECT by Tarjan union-SCC!
        let mut cyclic_s1_hyps = m3_s1.promotion_report.lifted_hypotheses.clone();
        cyclic_s1_hyps.push(LiftedHypothesisRecord {
            name: "Shard2.verify".to_owned(),
            universe_levels: Vec::new(),
            cone_merkle_sha256: s2_contract_cone.clone(),
            inherited_axioms: Vec::new(),
        });
        let err_6b = verify_modular_shard_dag(
            &[
                ModularShardNode {
                    shard_id: "shard1".to_owned(),
                    theorem_name: "Shard1.verify".to_owned(),
                    contract_cone_sha256: s1_contract_cone,
                    mir_direct_callees: BTreeSet::new(),
                    indirect_call_provenance: BTreeSet::new(),
                    m3_lifted_hypotheses: cyclic_s1_hyps,
                    local_axioms: BTreeSet::new(),
                    local_sorry_declarations: BTreeSet::new(),
                    local_taint_reasons: BTreeSet::new(),
                    local_model_closure: Vec::new(),
                },
                ModularShardNode {
                    shard_id: "shard2".to_owned(),
                    theorem_name: "Shard2.verify".to_owned(),
                    contract_cone_sha256: s2_contract_cone,
                    mir_direct_callees: BTreeSet::new(),
                    indirect_call_provenance: BTreeSet::new(),
                    m3_lifted_hypotheses: m3_s2.promotion_report.lifted_hypotheses.clone(),
                    local_axioms: BTreeSet::new(),
                    local_sorry_declarations: BTreeSet::new(),
                    local_taint_reasons: BTreeSet::new(),
                    local_model_closure: Vec::new(),
                },
            ],
            &base_allow,
            &Default::default(),
        )
        .unwrap_err();
        assert_eq!(err_6b.code, 1, "PoC-6b must fail closed: {err_6b}");
        assert!(
            err_6b.message.contains("cyclic modular shard dependency"),
            "PoC-6b must hit Tarjan SCC guard: {err_6b}"
        );

        // Live PoC-7b: Bottom-up Offline Zero-Axiom Stitcher across
        // `AnnealTheory -> Shard1 -> Shard2` across all 4 v4.35.0 kernels!
        let linked = link_m3_shards_to_zero_axioms(
            &mut link_arena,
            Some(&link_init),
            &ci_env,
            &[
                M3LinkShardInput {
                    shard_id: "s1".to_owned(),
                    m3_env: s1_m3_env,
                    theorem_name: "Shard1.verify".to_owned(),
                    expected_declaration: "Exp1.claim".to_owned(),
                    local_modules: BTreeSet::from(["Shard1".to_owned(), "Exp1".to_owned()]),
                    lifted_hypotheses: m3_s1.promotion_report.lifted_hypotheses,
                },
                M3LinkShardInput {
                    shard_id: "s2".to_owned(),
                    m3_env: s2_m3_env,
                    theorem_name: "Shard2.verify".to_owned(),
                    expected_declaration: "Exp2.claim".to_owned(),
                    local_modules: BTreeSet::from(["Shard2".to_owned(), "Exp2".to_owned()]),
                    lifted_hypotheses: m3_s2.promotion_report.lifted_hypotheses,
                },
            ],
        )
        .unwrap();
        assert_eq!(linked.linked_theorem_name, "AnnealLinked.s2.Shard2.verify_linked");
        let linked_file = p_dir.join("linked_zero_axiom.ndjson");
        fs::write(&linked_file, linked.linked_ndjson.as_bytes()).unwrap();
        run_all_4_v435_kernels_raw(&lean, &linked_file);
    }
}
