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
    ActiveSandbox, Checker, PINNED_INIT_PRIMITIVES, PINNED_SYSTEM_PLATFORM_DECLS,
    STANDARD_PERMITTED_AXIOMS, SandboxMode, TargetAuditRequest, TargetBindings, TargetModule,
    TargetRole, sha256_bytes,
};
use serde_json::json;
use tempfile::TempDir;

const SCALAR_SPEC: &str = include_str!("../../../trusted/cargo-anneal/assets/scalar/Spec.lean");
const SCALAR_PROOF: &str = include_str!("../../../trusted/cargo-anneal/assets/scalar/Proof.lean");

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
    if env::var_os("ANNEAL_REQUIRE_V435").is_some_and(|v| v == "1") {
        panic!("ANNEAL_REQUIRE_V435=1 is set, but no Lean v4.35.0+ toolchain was found");
    }
    None
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

    // `cargo anneal verify` accepts the audit metadata rather than failing
    // with `tool_failed`: the report carries the admitted import graph its
    // bundled-model trust-tier check requires. The scalar proof reaches the
    // `candidate:mir_ast` and `candidate:mir_semantics` model modules.
    assert_eq!(
        cargo_anneal::check_bundled_model_audit(&report),
        Ok(vec!["mir_ast", "mir_semantics"])
    );
    // Closures list only reached declarations: the imported but unreached
    // `Trusted.MirSemantics.CanaryFixtures` model module is in the graph but
    // in no closure, so `moduleIdentities` does not bind it either.
    const UNREACHED_MODEL: &str = "Trusted.MirSemantics.CanaryFixtures";
    assert!(report["graph"].get(UNREACHED_MODEL).is_some());
    for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
        for entry in report[key].as_array().expect("closure array") {
            assert_ne!(entry["module"], json!(UNREACHED_MODEL), "{key}: {entry}");
        }
    }
    assert!(report["moduleIdentities"].get(UNREACHED_MODEL).is_none());
    for key in [
        "expectedToolchain",
        "observedVersion",
        "leanBinarySha256",
        "foundationModules",
        "sysrootModulesSha256",
        "admittedSysrootModuleCount",
    ] {
        assert!(report["unpinnedLean"].get(key).is_some(), "missing unpinnedLean.{key}");
    }

    // Verify export, primitive, and comparator binary SHA-256 digests are
    // 64-char hex strings.
    for key in [
        "expectedConeSha256",
        "proofNdjsonSha256",
        "initPrimitivesSha256",
        "sysrootPinsSha256",
        "leanexportSha256",
        "nanodaBinSha256",
        "conRonSha256",
    ] {
        let hex = report[key].as_str().expect("missing digest");
        assert!(cargo_anneal::is_sha256_hex(hex), "invalid digest for {key}: {hex}");
    }

    // Every sysroot-named constant either export uses is content-pinned to
    // the clean sysroot re-export (`5-pin`).
    assert!(
        report["sysrootPinnedDeclarations"].as_u64().is_some_and(|n| n > 0),
        "{}",
        report["sysrootPinnedDeclarations"]
    );

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
    for key in ["conLecheSha256", "lean4leanSha256"] {
        let hex = rep_paranoid[key].as_str().expect("missing quorum kernel digest");
        assert!(cargo_anneal::is_sha256_hex(hex), "invalid digest for {key}: {hex}");
    }
    assert_eq!(rep_paranoid["paranoidQuorum"], json!(true));
    assert_eq!(
        rep_paranoid["kernelsPassed"],
        json!(["nanoda_bin", "con-ron", "con-leche", "lean4lean"])
    );
    assert!(rep_paranoid.get("kernelsSkipped").is_none());
}

/// Rewrite `proof_full.ndjson` so `theorem_name`'s value is its own type: the
/// export stays structurally valid (every referenced name and expression
/// exists, and the declaration's type and dependencies are unchanged), but
/// the theorem is ill-typed, so only a type-checking kernel can reject it.
fn ill_typed_theorem_export(ndjson: &str, theorem_name: &str) -> String {
    let mut names: std::collections::HashMap<u64, String> =
        std::collections::HashMap::from([(0, String::new())]);
    let mut lines: Vec<serde_json::Value> =
        ndjson.lines().map(|l| serde_json::from_str(l).expect("ndjson line")).collect();
    for v in &lines {
        let Some(id) = v["in"].as_u64() else { continue };
        // Numeric components (`"num"`) only occur in names the target
        // theorem's own name does not use; any name under one stays unnamed.
        let (Some(s), Some(pre)) =
            (v.get("str"), v["str"]["pre"].as_u64().and_then(|p| names.get(&p)))
        else {
            continue;
        };
        let seg = s["str"].as_str().unwrap();
        let full = if pre.is_empty() { seg.to_owned() } else { format!("{pre}.{seg}") };
        names.insert(id, full);
    }
    let name_id =
        names.iter().find(|(_, n)| n.as_str() == theorem_name).map(|(id, _)| *id).unwrap();
    let mut rewritten = 0;
    for v in &mut lines {
        if let Some(thm) = v.get_mut("thm").filter(|t| t["name"].as_u64() == Some(name_id)) {
            assert_ne!(thm["value"], thm["type"]);
            thm["value"] = thm["type"].clone();
            rewritten += 1;
        }
    }
    assert_eq!(rewritten, 1, "{theorem_name} theorem record");
    lines.iter().map(|v| format!("{v}\n")).collect()
}

/// Every kernel the comparator route relies on (`nanoda_bin` and `con-ron`
/// by default, plus `con-leche` and `lean4lean` under `--paranoid-quorum`)
/// rejects an ill-typed export in its configured invocation and accepts the
/// well-typed export it came from, so no kernel can be a no-op.
#[test]
fn ndjson_kernels_reject_ill_typed_proof_export() {
    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 NDJSON kernel rejection test (v4.35.0 not installed)");
        return;
    };
    let tmp = TempDir::new().unwrap();
    let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, SCALAR_PROOF, false);
    let mut checker = new_v435_checker(&lean);
    checker.set_paranoid_quorum(true);
    checker.run_target(&req).expect("scalar NDJSON comparator must pass");
    let exported = fs::read_to_string(checker.stage().join("ndjson/proof_full.ndjson")).unwrap();

    let kernels = ["nanoda_bin", "con-ron", "con-leche", "lean4lean"];
    let good = tmp.path().join("good.ndjson");
    fs::write(&good, &exported).unwrap();
    let verdicts = checker.run_ndjson_kernels(&good).unwrap();
    assert_eq!(verdicts.iter().map(|(k, _)| *k).collect::<Vec<_>>(), kernels);
    for (kernel, verdict) in &verdicts {
        assert!(verdict.is_ok(), "{kernel} must accept the well-typed export: {verdict:?}");
    }

    let bad = tmp.path().join("bad.ndjson");
    fs::write(&bad, ill_typed_theorem_export(&exported, "Proof.verify")).unwrap();
    let verdicts = checker.run_ndjson_kernels(&bad).unwrap();
    assert_eq!(verdicts.iter().map(|(k, _)| *k).collect::<Vec<_>>(), kernels);
    // `nanoda_bin`, `con-ron`, and `con-leche` report the failed definitional
    // equality check; `lean4lean` currently fails while reporting the error,
    // which the kernel runner's panic-marker check turns into a rejection.
    for (kernel, verdict) in verdicts {
        let err = verdict.expect_err(kernel);
        eprintln!("{kernel} rejected the ill-typed export: {err}");
        let reason = match kernel {
            "nanoda_bin" => "def_eq",
            "con-ron" | "con-leche" => "type mismatch in theorem",
            _ => continue,
        };
        assert_eq!(err.code, 1, "{kernel}: {err}");
        assert!(err.message.contains(reason), "{kernel}: {err}");
    }
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
            "public theorem verify : Expected.claim := by",
            "opaque stubNat : Nat := 0\ntheorem useStub : stubNat = stubNat := rfl\npublic theorem verify : Expected.claim := by\n  have _ := useStub",
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
            "public theorem verify : Expected.claim := by",
            "partial def loopNat (n : Nat) : Nat := loopNat (n + 1)\ntheorem usePartial : loopNat 0 = loopNat 0 := rfl\npublic theorem verify : Expected.claim := by\n  have _ := usePartial",
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

    // 6. A proof-module constant beneath `Trusted` fails closed even though
    // the umbrella `Trusted` module is a retained model module.
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = SCALAR_PROOF.replace(
            "public theorem verify : Expected.claim := by",
            "def _root_.Trusted.MirSemantics.evil : Nat := 0\ntheorem useEvil : Trusted.MirSemantics.evil = 0 := rfl\npublic theorem verify : Expected.claim := by\n  have _ := useEvil",
        );
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, &bad_proof, false);
        assert!(req.modules.iter().any(|m| m.module == "Trusted" && m.role == TargetRole::Model));
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "Trusted.* in Proof must fail with policy code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(
            err.message.contains("Trusted.MirSemantics.evil")
                && err.message.contains("outside model modules"),
            "{err}"
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
    // `SpecPreflight.lean` on Lean v4.35.0 (not only `TrustedBoundary.lean`).
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
        ("ns-init", "end Spec\nnamespace Init\nend Init\nnamespace Spec\n", "reserved namespace Init"),
        ("ns-std", "end Spec\nnamespace Std\nend Std\nnamespace Spec\n", "reserved namespace Std"),
        ("ns-nat", "end Spec\nnamespace Nat\nend Nat\nnamespace Spec\n", "reserved namespace Nat"),
        (
            "ns-internal-uv",
            "end Spec\nnamespace Internal.UV\nend Internal.UV\nnamespace Spec\n",
            "Internal.UV",
        ),
        (
            "ns-root-trusted",
            "end Spec\nnamespace _root_.Trusted\nend _root_.Trusted\nnamespace Spec\n",
            "_root_.Trusted",
        ),
        ("decl-bare-nat", "end Spec\ndef Nat : Nat := 0\nnamespace Spec\n", "reserved namespace Nat"),
    ];
    for (label, snippet, expected_tok) in cases {
        let mut bad_spec = SCALAR_SPEC.replace("end Spec", &format!("{snippet}\nend Spec"));
        if label == "term-qed-try" {
            bad_spec = bad_spec.replace(
                "import Trusted.MirSemantics",
                "import Trusted.MirSemantics\npublic import Init",
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

#[test]
fn ndjson_comparator_admits_system_platform_and_blocks_namespace_escapes_on_v435() {
    let Some(lean) = discover_v435_lean() else {
        eprintln!("skipping v4.35.0 System.Platform/isolation test (v4.35.0 toolchain not installed)");
        return;
    };
    let mut checker = new_v435_checker(&lean);

    // 1. Real `System.Platform.numBits` (referencing `Init.Prelude`
    // `opaque` `System.Platform.getNumBits`) in `Spec.lean` passes on v4.35.0
    // and records `"Init.Prelude"` provenance in `specificationClosure` and
    // `moduleIdentities`.
    let platform_spec = SCALAR_SPEC.replace(
        "⟨fun _ _ => True, returnsZero⟩",
        "⟨fun _ _ => System.Platform.numBits = 64 ∨ System.Platform.numBits = 32, returnsZero⟩",
    );
    assert!(platform_spec.contains("System.Platform.numBits"));
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &platform_spec, SCALAR_PROOF, false);
        let rep = checker
            .run_target(&req)
            .expect("System.Platform.numBits in Spec must pass on v4.35.0");
        assert_eq!(rep["auditMode"], json!("ndjson_comparator"));
        assert!(
            rep["moduleIdentities"].get("Init.Prelude").is_some(),
            "Init.Prelude provenance must appear in moduleIdentities: {}",
            rep["moduleIdentities"]
        );
        assert!(
            rep["specificationClosure"]
                .as_array()
                .expect("specificationClosure array")
                .iter()
                .any(|e| {
                    e["name"] == "System.Platform.getNumBits" && e["module"] == "Init.Prelude"
                }),
            "System.Platform.getNumBits must be attributed to Init.Prelude in specificationClosure: {}",
            rep["specificationClosure"]
        );
    }

    // 2. Unused `Spec` helper in a custom namespace referencing `runST`
    // (whose type transitively depends on `ST`) passes `SpecPreflight` and
    // fails closed in Action 5c via `spec_declared_consts` even though
    // `Spec.specs` does not use it; `System.FilePath` is blocked earlier in
    // `SpecPreflight`.
    let unused_sys_spec = SCALAR_SPEC.replace(
        "end Spec",
        "end Spec\nnamespace Contract\ndef unusedPath : System.FilePath := ⟨\"/etc/passwd\"⟩\nend Contract\nnamespace Spec\nend Spec",
    );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &unused_sys_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "unused Contract.unusedPath must fail with code 1: {err}");
        assert_eq!(err.phase, "spec-preflight", "{err}");
        assert!(err.message.contains("System.FilePath"), "{err}");
    }
    let unused_st_spec = SCALAR_SPEC
        .replace(
            "import Trusted.MirSemantics\n",
            "import Trusted.MirSemantics\npublic import Init.Control.StateRef\n",
        )
        .replace(
            "end Spec",
            "end Spec\nnamespace Contract\ndef unusedStHelper : Nat := runST (fun _ => pure 0)\nend Contract\nnamespace Spec\nend Spec",
        );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &unused_st_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "unused Contract.unusedStHelper must fail with code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(err.message.contains("ST"), "{err}");
    }

    // 2b. An unreferenced anonymous instance (whose name only elaboration
    // generates) calling `runST` is attributed to `Spec` by the
    // `"target-consts"` module index and fails closed in Action 5c.
    let anon_instance_spec = SCALAR_SPEC
        .replace(
            "import Trusted.MirSemantics\n",
            "import Trusted.MirSemantics\npublic import Init.Control.StateRef\n",
        )
        .replace(
            "end Spec",
            "end Spec\nnamespace Contract\nstructure Box where\n  n : Nat\ninstance : Inhabited Box := ⟨⟨runST (fun _ => pure 0)⟩⟩\nend Contract\nnamespace Spec\nend Spec",
        );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &anon_instance_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "anonymous runST instance must fail with code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(err.message.contains("ST"), "{err}");
    }

    // 2c. Compiler-generated specification constants (structure
    // constructors/projections, `deriving` instances, named and anonymous
    // instances, `where` and `let rec` auxiliaries) are exported and checked
    // without false rejections.
    let generated_spec = SCALAR_SPEC.replace(
        "end Spec",
        "structure Pair where\n  a : Nat\n  b : Nat\nderiving BEq, Repr, Inhabited\n\
         instance : Add Pair := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩\n\
         def sumTo (n : Nat) : Nat := go n 0\nwhere\n  go : Nat → Nat → Nat\n    | 0, acc => acc\n    | k + 1, acc => go k (acc + k + 1)\n\
         def twice (n : Nat) : Nat :=\n  let rec loop : Nat → Nat\n    | 0 => 0\n    | k + 1 => loop k + 2\n  loop n\n\
         end Spec",
    );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &generated_spec, SCALAR_PROOF, false);
        let rep = checker
            .run_target(&req)
            .expect("generated specification constants must pass on v4.35.0");
        assert_eq!(rep["auditMode"], json!("ndjson_comparator"));
    }

    // 3. `namespace Trusted` in `Spec.lean` fails closed in `SpecPreflight`.
    let trusted_ns_spec = SCALAR_SPEC.replace(
        "end Spec",
        "end Spec\nnamespace Trusted\ndef hijack : Nat := 0\nend Trusted\nnamespace Spec\nend Spec",
    );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &trusted_ns_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "namespace Trusted in Spec must fail with code 1: {err}");
        assert_eq!(err.phase, "spec-preflight", "{err}");
        assert!(err.message.contains("Trusted"), "{err}");
    }
}

/// A stub kernel that accepts every export.
#[cfg(unix)]
const ACCEPTING_KERNEL: &str = "#!/bin/sh\nexit 0\n";

/// Run `Checker::run_target` through the NDJSON comparator route against a
/// synthetic `v4.35.0` sysroot whose `lean` and `leanexport` are scripted and
/// whose `nanoda_bin` and `con-ron` are the given shell scripts, so CI
/// exercises the route without a `v4.35.0` install.
#[cfg(unix)]
fn run_synthetic_ndjson_pipeline(
    nanoda_bin_script: &str,
    con_ron_script: &str,
) -> (TempDir, Result<serde_json::Value, cargo_anneal::Failure>) {
    use std::os::unix::fs::PermissionsExt;

    let tmp = TempDir::new().unwrap();
    let sysroot = tmp.path().join("sysroot");
    let bin_dir = sysroot.join("bin");
    let init_lib = sysroot.join("lib/lean/Init");
    let init_src = sysroot.join("src/lean/Init");
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(&init_lib).unwrap();
    fs::create_dir_all(&init_src).unwrap();
    for m in ["Coe", "Core", "Notation", "Prelude", "SizeOf", "Tactics"] {
        fs::write(init_lib.join(format!("{m}.olean")), b"olean\x02\x00\x00").unwrap();
        fs::write(init_src.join(format!("{m}.lean")), b"prelude\n").unwrap();
    }

    // Precompute synthetic v3.1.0 NDJSON streams covering all pinned
    // primitives, standard axioms, `System.Platform`, `Expected.claim`, and
    // `Proof.verify`.
    let meta = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.35.0"}}}"#;
    let mut init_lines = vec![
        meta.to_owned(),
        r#"{"ie":0,"sort":0}"#.to_owned(),
        r#"{"il":1,"succ":0}"#.to_owned(),
        r#"{"ie":1,"sort":1}"#.to_owned(),
    ];
    let mut next_in = 1u64;
    let mut name_ids = std::collections::HashMap::<String, u64>::new();
    let mut intern = |dotted: &str, lines: &mut Vec<String>| -> u64 {
        let mut cur = 0u64;
        let mut pref = String::new();
        for seg in dotted.split('.') {
            if !pref.is_empty() {
                pref.push('.');
            }
            pref.push_str(seg);
            if let Some(&id) = name_ids.get(&pref) {
                cur = id;
            } else {
                let id = next_in;
                next_in += 1;
                lines.push(format!(r#"{{"in":{id},"str":{{"pre":{cur},"str":"{seg}"}}}}"#));
                name_ids.insert(pref.clone(), id);
                cur = id;
            }
        }
        cur
    };
    for prim in PINNED_INIT_PRIMITIVES {
        let nid = intern(prim, &mut init_lines);
        let line = match prim {
            "Quot" => format!(r#"{{"quot":{{"kind":"type","levelParams":[],"name":{nid},"type":1}}}}"#),
            "Quot.mk" => format!(r#"{{"quot":{{"kind":"ctor","levelParams":[],"name":{nid},"type":1}}}}"#),
            "Quot.lift" => format!(r#"{{"quot":{{"kind":"lift","levelParams":[],"name":{nid},"type":1}}}}"#),
            "Quot.ind" => format!(r#"{{"quot":{{"kind":"ind","levelParams":[],"name":{nid},"type":1}}}}"#),
            _ => format!(r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#),
        };
        init_lines.push(line);
    }
    for ax in STANDARD_PERMITTED_AXIOMS {
        let nid = intern(ax, &mut init_lines);
        init_lines.push(format!(r#"{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{nid},"type":0}}}}"#));
    }
    for decl in PINNED_SYSTEM_PLATFORM_DECLS {
        let nid = intern(decl, &mut init_lines);
        if decl == "System.Platform.getNumBits" {
            init_lines.push(format!(r#"{{"opaque":{{"all":[{nid}],"isUnsafe":false,"levelParams":[],"name":{nid},"type":1,"value":0}}}}"#));
        } else {
            init_lines.push(format!(r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#));
        }
    }
    let init_ndjson = init_lines.join("\n") + "\n";

    let expected_ndjson = [
        meta,
        r#"{"in":10,"str":{"pre":0,"str":"Trusted"}}"#,
        r#"{"in":11,"str":{"pre":10,"str":"MirSemantics"}}"#,
        r#"{"in":12,"str":{"pre":11,"str":"UnitTheorem"}}"#,
        r#"{"in":13,"str":{"pre":11,"str":"Crate"}}"#,
        r#"{"in":14,"str":{"pre":13,"str":"mk"}}"#,
        r#"{"in":15,"str":{"pre":0,"str":"Captured"}}"#,
        r#"{"in":16,"str":{"pre":15,"str":"program"}}"#,
        r#"{"in":17,"str":{"pre":0,"str":"Spec"}}"#,
        r#"{"in":18,"str":{"pre":17,"str":"specs"}}"#,
        r#"{"in":19,"str":{"pre":0,"str":"Expected"}}"#,
        r#"{"in":20,"str":{"pre":19,"str":"claim"}}"#,
        r#"{"ie":10,"sort":0}"#,
        r#"{"ie":11,"const":{"name":12,"us":[]}}"#,
        r#"{"ie":12,"const":{"name":14,"us":[]}}"#,
        r#"{"ie":13,"const":{"name":16,"us":[]}}"#,
        r#"{"ie":14,"const":{"name":18,"us":[]}}"#,
        r#"{"ie":15,"app":{"arg":13,"fn":12}}"#,
        r#"{"ie":16,"app":{"arg":14,"fn":15}}"#,
        r#"{"ie":17,"app":{"arg":16,"fn":11}}"#,
        r#"{"def":{"all":[12],"hints":"abbrev","levelParams":[],"name":12,"safety":"safe","type":10,"value":10}}"#,
        r#"{"def":{"all":[14],"hints":"abbrev","levelParams":[],"name":14,"safety":"safe","type":10,"value":10}}"#,
        r#"{"def":{"all":[16],"hints":"abbrev","levelParams":[],"name":16,"safety":"safe","type":10,"value":10}}"#,
        r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
        r#"{"def":{"all":[20],"hints":"abbrev","levelParams":[],"name":20,"safety":"safe","type":10,"value":17}}"#,
    ]
    .join("\n")
        + "\n";

    let proof_ndjson = [
        expected_ndjson.trim_end(),
        r#"{"in":21,"str":{"pre":0,"str":"Proof"}}"#,
        r#"{"in":22,"str":{"pre":21,"str":"verify"}}"#,
        r#"{"ie":20,"const":{"name":20,"us":[]}}"#,
        r#"{"thm":{"all":[22],"levelParams":[],"name":22,"type":20,"value":10}}"#,
    ]
    .join("\n")
        + "\n";

    let fixtures_dir = tmp.path().join("ndjson_fixtures");
    fs::create_dir_all(&fixtures_dir).unwrap();
    fs::write(fixtures_dir.join("init.ndjson"), init_ndjson).unwrap();
    fs::write(fixtures_dir.join("expected.ndjson"), expected_ndjson).unwrap();
    fs::write(fixtures_dir.join("proof.ndjson"), proof_ndjson).unwrap();

    let lean_bin = bin_dir.join("lean");
    let lean_script = format!(
        r#"#!/usr/bin/env python3
import json, pathlib, sys
args = sys.argv[1:]
if args == ["--version"]:
    print("Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit 0000000000000000000000000000000000000000, Release)")
    sys.exit(0)
if args == ["--print-prefix"]:
    print({sysroot:?})
    sys.exit(0)
if "--run" in args:
    idx = args.index("--run")
    req = json.loads(pathlib.Path(args[idx + 2]).read_text())
    mode = req["mode"]
    out = pathlib.Path(args[idx + 3])
    if mode == "headers":
        res = {{"headers": [{{"module": m, "imports": [], "isModule": False}} for m, _ in req["sources"]]}}
    elif mode == "resolve-imports":
        edge = lambda m: {{"module": m, "isMeta": False, "importAll": False, "isExported": True}}
        res = {{"graph": {{
            "Init.Prelude": [],
            "Init.Core": [edge(m) for m in ("Init.Prelude", "Init.Coe", "Init.Notation", "Init.SizeOf", "Init.Tactics")],
            "Init.Coe": [edge("Init.Prelude")],
            "Init.Notation": [edge("Init.Prelude")],
            "Init.SizeOf": [edge("Init.Prelude")],
            "Init.Tactics": [edge("Init.Prelude")],
        }}}}
    elif mode == "spec-preflight":
        res = {{"checked": [m for m, _ in req["sources"]]}}
    elif mode == "sysroot-consts":
        res = {{"sysrootConsts": [["Init.Core", ["Classical.choice", "Quot.sound", "propext"]]]}}
    elif mode == "target-consts":
        listing = {{
            "Trusted.MirSemantics": ["Trusted.MirSemantics.Crate.mk", "Trusted.MirSemantics.UnitTheorem"],
            "Trusted.Unused": ["Trusted.Unused.helper"],
            "Captured": ["Captured.program"],
            "Spec": ["Spec.specs"],
            "Expected": ["Expected.claim"],
        }}
        res = {{"targetConsts": [[m, listing[m], [], []] for m, _ in req["targets"]]}}
    else:
        raise RuntimeError(f"unexpected mode {{mode}}")
    out.write_text(json.dumps({{"ok": True, "result": res}}))
    sys.exit(0)
if "-o" in args:
    pathlib.Path(args[args.index("-o") + 1]).write_bytes(b"olean\x02\x00\x00")
    sys.exit(0)
sys.exit(0)
"#,
        sysroot = sysroot.to_string_lossy()
    );
    fs::write(&lean_bin, lean_script).unwrap();
    fs::set_permissions(&lean_bin, fs::Permissions::from_mode(0o755)).unwrap();

    let leanexport_bin = bin_dir.join("leanexport");
    let leanexport_script = format!(
        r#"#!/usr/bin/env python3
import pathlib, sys
args = sys.argv[1:]
fixtures = pathlib.Path({fixtures:?})
if "--ignore-missing" in args:
    sys.exit("unexpected --ignore-missing")
if "Proof.verify" in args:
    sys.stdout.write((fixtures / "proof.ndjson").read_text())
elif "Expected.claim" in args:
    sys.stdout.write((fixtures / "expected.ndjson").read_text())
elif args and args[0] == "Init":
    sys.stdout.write((fixtures / "init.ndjson").read_text())
else:
    sys.exit(f"unexpected leanexport arguments {{args}}")
"#,
        fixtures = fixtures_dir.to_string_lossy()
    );
    fs::write(&leanexport_bin, leanexport_script).unwrap();
    fs::set_permissions(&leanexport_bin, fs::Permissions::from_mode(0o755)).unwrap();

    for (tool, script) in [("nanoda_bin", nanoda_bin_script), ("con-ron", con_ron_script)] {
        let p = bin_dir.join(tool);
        fs::write(&p, script).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(0o755)).unwrap();
    }

    let target_dir = tmp.path().join("target");
    fs::create_dir_all(&target_dir).unwrap();
    let files = [
        ("Trusted/MirSemantics.lean", "prelude\n", TargetRole::Model),
        ("Trusted/Unused.lean", "prelude\n", TargetRole::Model),
        ("Captured.lean", "prelude\n", TargetRole::Capture),
        ("Spec.lean", "prelude\n", TargetRole::Specification),
        ("Expected.lean", "prelude\n", TargetRole::Expected),
        ("Proof.lean", "prelude\n", TargetRole::Proof),
    ];
    let mut modules = Vec::new();
    for (rel, content, role) in files {
        let p = target_dir.join(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(&p, content).unwrap();
        modules.push(TargetModule {
            module: rel.trim_end_matches(".lean").replace('/', "."),
            source: p,
            expected_sha256: sha256_bytes(content.as_bytes()),
            role,
        });
    }
    let zero_hash = "0".repeat(64);
    let req = TargetAuditRequest {
        modules,
        theorem_module: "Proof".to_owned(),
        theorem_name: "Proof.verify".to_owned(),
        expected_module: "Expected".to_owned(),
        expected_declaration: "Expected.claim".to_owned(),
        canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
        subject_declaration: "Captured.program".to_owned(),
        specification_declaration: "Spec.specs".to_owned(),
        allow_sorry_in_proof: false,
        bindings: TargetBindings {
            request_sha256: zero_hash.clone(),
            capture_sha256: zero_hash.clone(),
            model_manifest_sha256: zero_hash.clone(),
            specification_manifest_sha256: zero_hash,
        },
    };

    let mut checker = Checker::new(&repo_root(), Some(&lean_bin)).expect("create checker");
    checker.set_allow_unpinned_lean(true);
    checker.set_sandbox_mode(SandboxMode::Unsandboxed);
    let res = checker.run_target(&req);
    (tmp, res)
}

#[cfg(unix)]
#[test]
fn synthetic_ndjson_comparator_runs_full_target_audit_pipeline_without_v435_install() {
    let (_tmp, res) = run_synthetic_ndjson_pipeline(ACCEPTING_KERNEL, ACCEPTING_KERNEL);
    let report = res.expect("synthetic NDJSON comparator run_target must succeed");
    assert_eq!(report["auditMode"], json!("ndjson_comparator"));
    assert_eq!(report["replay"], json!(true));
    assert_eq!(report["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));
    for key in ["leanexportSha256", "nanodaBinSha256", "conRonSha256"] {
        assert!(cargo_anneal::is_sha256_hex(report[key].as_str().unwrap()));
    }
    // The report carries the admitted import graph, and each closure lists
    // exactly the declarations it reaches, attributed to their modules, so
    // the unreached `Trusted.Unused` model module appears in no closure and
    // receives no `moduleIdentities` entry.
    let graph = report["graph"].as_object().expect("audit.graph must be an object");
    for module in [
        "Trusted.MirSemantics",
        "Trusted.Unused",
        "Captured",
        "Spec",
        "Expected",
        "Init.Prelude",
        "Init.Core",
    ] {
        assert!(graph.contains_key(module), "audit.graph lacks {module}: {graph:?}");
    }
    let closure = |key: &str| -> Vec<(String, String)> {
        report[key]
            .as_array()
            .unwrap_or_else(|| panic!("missing {key}"))
            .iter()
            .map(|e| {
                (e["name"].as_str().unwrap().to_owned(), e["module"].as_str().unwrap().to_owned())
            })
            .collect()
    };
    let model = closure("modelClosure");
    assert!(model.contains(&(
        "Trusted.MirSemantics.UnitTheorem".to_owned(),
        "Trusted.MirSemantics".to_owned()
    )));
    assert!(model.iter().all(|(_, m)| m == "Trusted.MirSemantics" || m.starts_with("Init.")));
    assert!(
        closure("subjectClosure").contains(&("Captured.program".to_owned(), "Captured".to_owned()))
    );
    assert!(
        closure("specificationClosure").contains(&("Spec.specs".to_owned(), "Spec".to_owned()))
    );
    for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
        assert!(
            closure(key)
                .iter()
                .all(|(n, m)| n != m && m != "Trusted.Unused" && graph.contains_key(m)),
            "{key}"
        );
    }
    let identities = report["moduleIdentities"].as_object().expect("moduleIdentities");
    assert!(identities.contains_key("Trusted.MirSemantics"), "{identities:?}");
    assert!(!identities.contains_key("Trusted.Unused"), "{identities:?}");
}

/// The comparator route fails closed whenever either required kernel rejects
/// the export, by a nonzero exit or by a Lean panic marker on stderr despite
/// exit code 0, without a `v4.35.0` install.
#[cfg(unix)]
#[test]
fn synthetic_ndjson_comparator_fails_closed_when_a_stub_kernel_rejects() {
    let rejecting = "#!/bin/sh\necho 'type mismatch' >&2\nexit 1\n";
    let panicking = "#!/bin/sh\necho 'PANIC at Lean.Kernel' >&2\nexit 0\n";
    for (label, nanoda_bin, con_ron, code, needle) in [
        ("nanoda_bin exit 1", rejecting, ACCEPTING_KERNEL, 1, "nanoda_bin rejected proof export"),
        ("con-ron exit 1", ACCEPTING_KERNEL, rejecting, 1, "con-ron rejected proof export"),
        ("nanoda_bin panic", panicking, ACCEPTING_KERNEL, 2, "Lean runtime panic marker"),
        ("con-ron panic", ACCEPTING_KERNEL, panicking, 2, "Lean runtime panic marker"),
    ] {
        let (_tmp, res) = run_synthetic_ndjson_pipeline(nanoda_bin, con_ron);
        let err = res.expect_err(label);
        assert_eq!(err.code, code, "{label}: {err}");
        assert!(err.message.contains(needle), "{label}: {err}");
        let phase = if nanoda_bin == ACCEPTING_KERNEL { "con-ron" } else { "nanoda" };
        assert!(err.phase.contains(phase), "{label}: {err}");
    }
}
