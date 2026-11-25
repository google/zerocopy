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

#[test]
fn scalar_ndjson_comparator_default_dual_kernels_and_paranoid_quorum() {
    let Some(lean) =
        require_or_skip_v435_lean("scalar_ndjson_comparator_default_dual_kernels_and_paranoid_quorum")
    else {
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
    let mut lines: Vec<Value> =
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
    let Some(lean) = require_or_skip_v435_lean("ndjson_kernels_reject_ill_typed_proof_export")
    else {
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
    let Some(lean) = require_or_skip_v435_lean("scalar_ndjson_comparator_rejects_adversarial_proofs")
    else {
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
    let Some(lean) =
        require_or_skip_v435_lean("spec_preflight_enforces_4130_bans_and_module_reservation_on_v435")
    else {
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
    let Some(lean) = require_or_skip_v435_lean(
        "ndjson_comparator_admits_system_platform_and_blocks_namespace_escapes_on_v435",
    ) else {
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

#[test]
fn v435_strict_skip_gate_fails_closed_under_ci_strict_and_require_v435() {
    let tmp = TempDir::new().unwrap();
    let empty_home = tmp.path().join("empty_home");
    fs::create_dir_all(&empty_home).unwrap();

    // 1. Non-strict local dev: missing toolchain skips (`Ok(None)`).
    let local_env = |key: &str| match key {
        "HOME" => Some(empty_home.as_os_str().to_os_string()),
        _ => None,
    };
    assert_eq!(
        discover_v435_lean_with_env("sample_v435_test", local_env).unwrap(),
        None
    );

    // 2. `ANNEAL_CI_STRICT=1` fails closed when v4.35.0 comparator tools are
    // missing, even if `ANNEAL_REQUIRE_V435` is unset.
    let ci_strict_env = |key: &str| match key {
        "HOME" => Some(empty_home.as_os_str().to_os_string()),
        "ANNEAL_CI_STRICT" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", ci_strict_env).unwrap_err();
    assert!(err.contains("ANNEAL_CI_STRICT=1"), "{err}");
    assert!(err.contains("sample_v435_test"), "{err}");

    // 3. `ANNEAL_REQUIRE_V435=1` fails closed independently.
    let require_env = |key: &str| match key {
        "HOME" => Some(empty_home.as_os_str().to_os_string()),
        "ANNEAL_REQUIRE_V435" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", require_env).unwrap_err();
    assert!(err.contains("ANNEAL_REQUIRE_V435=1"), "{err}");

    // 4. Unset `HOME` under `ANNEAL_CI_STRICT=1` must still fail closed rather
    // than returning `None` early.
    let no_home_strict = |key: &str| match key {
        "ANNEAL_CI_STRICT" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", no_home_strict).unwrap_err();
    assert!(err.contains("ANNEAL_CI_STRICT=1"), "{err}");

    // 5. Explicit `ANNEAL_LEAN_V435` pointing to a `lean` binary that lacks
    // sibling `leanexport`/`nanoda_bin`/`con-ron` fails closed even in
    // non-strict mode (never silently skips).
    let partial_bin = tmp.path().join("partial/bin");
    fs::create_dir_all(&partial_bin).unwrap();
    let partial_lean = partial_bin.join("lean");
    fs::write(&partial_lean, b"stub").unwrap();
    let partial_non_strict_env = |key: &str| match key {
        "ANNEAL_LEAN_V435" => Some(partial_lean.as_os_str().to_os_string()),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", partial_non_strict_env).unwrap_err();
    assert!(err.contains("ANNEAL_LEAN_V435=") && err.contains("comparator tools"), "{err}");
    let partial_strict_env = |key: &str| match key {
        "ANNEAL_LEAN_V435" => Some(partial_lean.as_os_str().to_os_string()),
        "ANNEAL_CI_STRICT" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", partial_strict_env).unwrap_err();
    assert!(err.contains("ANNEAL_LEAN_V435=") && err.contains("comparator tools"), "{err}");

    // 6. Complete `ANNEAL_LEAN_V435` with sibling `leanexport`, `nanoda_bin`,
    // and `con-ron` succeeds.
    for tool in ["leanexport", "nanoda_bin", "con-ron"] {
        fs::write(partial_bin.join(tool), b"stub").unwrap();
    }
    assert_eq!(
        discover_v435_lean_with_env("sample_v435_test", partial_non_strict_env).unwrap(),
        Some(partial_lean)
    );
}

#[cfg(unix)]
mod synthetic_comparator {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    const SYNTHETIC_META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.35.0"}}}"#;

    /// Shared Python 3 NDJSON stream validator embedded in the inspecting
    /// `nanoda_bin` and `con-ron` stubs. Rejects malformed JSON, duplicate
    /// object keys, missing/wrong metadata, dangling table references,
    /// forbidden markers, unsafe/partial declarations, unpermitted axioms,
    /// missing required roots, and tampered `Expected.claim` bodies.
    const PYTHON_NDJSON_VALIDATOR: &str = r#"
import json, os, pathlib, sys

STANDARD_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
REQUIRED_DECLS = {
    "Expected.claim",
    "Proof.verify",
    "Trusted.MirSemantics.UnitTheorem",
    "Trusted.MirSemantics.Crate.mk",
    "Captured.program",
    "Spec.specs",
}
REQUIRED_CLAIM_CONSTS = {
    "Trusted.MirSemantics.UnitTheorem",
    "Trusted.MirSemantics.Crate.mk",
    "Captured.program",
    "Spec.specs",
}
FORBIDDEN_MARKER = "ANNEAL_FORBIDDEN_MARKER"

def fail(msg):
    sys.stderr.write(f"stub-inspector-error: {msg}\n")
    sys.exit(2)

def parse_json_strict(text, ctx):
    def no_dups(pairs):
        out = {}
        for k, v in pairs:
            if k in out:
                raise ValueError(f"duplicate JSON key {k!r}")
            out[k] = v
        return out
    try:
        return json.loads(text, object_pairs_hook=no_dups)
    except Exception as exc:
        fail(f"{ctx}: invalid JSON: {exc}")

def collect_expr_consts(expr_id, exprs, names):
    seen = set()
    stack = [expr_id]
    consts = set()
    while stack:
        eid = stack.pop()
        if eid in seen:
            continue
        seen.add(eid)
        rec = exprs.get(eid)
        if rec is None:
            fail(f"dangling expr reference {eid}")
        if "const" in rec:
            nid = rec["const"]["name"]
            if nid not in names:
                fail(f"dangling const name reference {nid}")
            consts.add(names[nid])
        elif "app" in rec:
            stack.append(rec["app"]["fn"])
            stack.append(rec["app"]["arg"])
        elif "lam" in rec:
            stack.append(rec["lam"]["type"])
            stack.append(rec["lam"]["body"])
        elif "forallE" in rec:
            stack.append(rec["forallE"]["type"])
            stack.append(rec["forallE"]["body"])
        elif "letE" in rec:
            stack.append(rec["letE"]["type"])
            stack.append(rec["letE"]["value"])
            stack.append(rec["letE"]["body"])
        elif "proj" in rec:
            stack.append(rec["proj"]["struct"])
        elif "mdata" in rec:
            stack.append(rec["mdata"]["expr"])
    return consts

def validate_ndjson(ndjson_path, permitted_axioms):
    if not ndjson_path.is_file():
        fail(f"missing NDJSON file {ndjson_path}")
    raw_lines = [ln for ln in ndjson_path.read_text(encoding="utf-8").splitlines() if ln]
    if not raw_lines:
        fail(f"empty NDJSON stream at {ndjson_path}")

    meta_obj = parse_json_strict(raw_lines[0], f"{ndjson_path}:1")
    if not isinstance(meta_obj, dict) or list(meta_obj.keys()) != ["meta"]:
        fail("line 1 must contain only 'meta'")
    meta = meta_obj["meta"]
    if meta.get("format", {}).get("version") != "3.1.0":
        fail(f"unexpected NDJSON format version: {meta.get('format')}")
    if not meta.get("exporter", {}).get("name") or not meta.get("lean", {}).get("version"):
        fail(f"incomplete NDJSON metadata header: {meta}")

    names = {0: ""}
    levels = {0}
    exprs = {}
    decls = {}
    axioms = []

    for line_no, line in enumerate(raw_lines[1:], start=2):
        if FORBIDDEN_MARKER in line:
            fail(f"line {line_no}: forbidden marker {FORBIDDEN_MARKER} detected")
        obj = parse_json_strict(line, f"{ndjson_path}:{line_no}")
        if not isinstance(obj, dict):
            fail(f"line {line_no}: expected JSON object")
        if "in" in obj:
            if len(obj) != 2:
                fail(f"line {line_no}: name entry must have 2 keys")
            idx = obj["in"]
            if not isinstance(idx, int) or idx in names:
                fail(f"line {line_no}: invalid or duplicate name index {idx!r}")
            if "str" in obj:
                pre = obj["str"]["pre"]
                seg = obj["str"]["str"]
                if pre not in names or not isinstance(seg, str):
                    fail(f"line {line_no}: malformed Name.str")
                names[idx] = f"{names[pre]}.{seg}" if names[pre] else seg
            elif "num" in obj:
                pre = obj["num"]["pre"]
                num = obj["num"]["i"]
                if pre not in names or not isinstance(num, int):
                    fail(f"line {line_no}: malformed Name.num")
                names[idx] = f"{names[pre]}.{num}" if names[pre] else str(num)
            else:
                fail(f"line {line_no}: unknown name variant")
        elif "il" in obj:
            if len(obj) != 2:
                fail(f"line {line_no}: level entry must have 2 keys")
            idx = obj["il"]
            if not isinstance(idx, int) or idx in levels:
                fail(f"line {line_no}: invalid or duplicate level index {idx!r}")
            levels.add(idx)
        elif "ie" in obj:
            if len(obj) != 2:
                fail(f"line {line_no}: expr entry must have 2 keys")
            idx = obj["ie"]
            if not isinstance(idx, int) or idx in exprs:
                fail(f"line {line_no}: invalid or duplicate expr index {idx!r}")
            exprs[idx] = obj
        else:
            if len(obj) != 1:
                fail(f"line {line_no}: declaration record must have exactly 1 key")
            tag, rec = next(iter(obj.items()))
            if tag not in ("axiom", "def", "thm", "opaque", "quot", "inductive"):
                fail(f"line {line_no}: unknown record tag {tag!r}")
            if tag == "inductive":
                for sub_key in ("types", "ctors", "recs"):
                    for item in rec.get(sub_key, []):
                        if item.get("isUnsafe", False):
                            fail(f"line {line_no}: unsafe inductive item")
                        nid = item["name"]
                        if nid not in names:
                            fail(f"line {line_no}: dangling inductive name {nid}")
                        decls[names[nid]] = (sub_key, item)
                continue
            nid = rec["name"]
            if nid not in names:
                fail(f"line {line_no}: dangling decl name {nid}")
            dname = names[nid]
            if dname in decls:
                fail(f"line {line_no}: duplicate declaration {dname}")
            if tag == "axiom":
                if rec.get("isUnsafe", False):
                    fail(f"line {line_no}: unsafe axiom {dname}")
                if dname not in permitted_axioms:
                    fail(f"line {line_no}: unpermitted axiom {dname}")
                axioms.append(dname)
            elif tag == "def":
                if rec.get("safety") != "safe":
                    fail(f"line {line_no}: non-safe def {dname}: {rec.get('safety')}")
            elif tag == "opaque":
                if rec.get("isUnsafe", False):
                    fail(f"line {line_no}: unsafe opaque {dname}")
            decls[dname] = (tag, rec)

    missing = sorted(REQUIRED_DECLS - set(decls.keys()))
    if missing:
        fail(f"missing required declarations in NDJSON stream: {missing}")

    claim_tag, claim_rec = decls["Expected.claim"]
    if claim_tag != "def":
        fail(f"Expected.claim must be a def, found {claim_tag}")
    claim_ty_expr = exprs.get(claim_rec["type"])
    if not isinstance(claim_ty_expr, dict) or claim_ty_expr.get("sort") != 0:
        fail(f"tampered Expected.claim type expr: expected Prop (sort 0), got {claim_ty_expr}")
    claim_val_expr = exprs.get(claim_rec["value"])
    if not isinstance(claim_val_expr, dict) or "app" not in claim_val_expr:
        fail(f"tampered Expected.claim value expr: expected app, got {claim_val_expr}")
    claim_consts = collect_expr_consts(claim_rec["value"], exprs, names)
    missing_claim_consts = sorted(REQUIRED_CLAIM_CONSTS - claim_consts)
    if missing_claim_consts:
        fail(f"tampered Expected.claim body missing canonical roots: {missing_claim_consts}")

    verify_tag, _ = decls["Proof.verify"]
    if verify_tag != "thm":
        fail(f"Proof.verify must be a thm, found {verify_tag}")

    return {"decl_count": len(decls), "axioms": sorted(axioms), "line_count": len(raw_lines)}

def record_invocation(log_path, entry):
    if log_path:
        with open(log_path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry) + "\n")
"#;

    const NANODA_STUB_BODY: &str = r#"
args = sys.argv[1:]
if len(args) != 1:
    fail(f"nanoda_bin expected exactly 1 config argument, got {args!r}")
cfg_path = pathlib.Path(args[0])
if cfg_path.name != "nanoda_config.json" or not cfg_path.is_file():
    fail(f"nanoda_bin expected nanoda_config.json file, got {cfg_path}")
cfg = parse_json_strict(cfg_path.read_text(encoding="utf-8"), str(cfg_path))
expected_keys = {
    "use_stdin",
    "export_file_path",
    "permitted_axioms",
    "unpermitted_axiom_hard_error",
    "num_threads",
    "nat_extension",
    "string_extension",
}
if set(cfg.keys()) != expected_keys:
    fail(f"nanoda_config.json keys mismatch: got {sorted(cfg.keys())}")
if cfg["use_stdin"] is not False:
    fail(f"nanoda_config.json use_stdin must be false, got {cfg['use_stdin']!r}")
if cfg["unpermitted_axiom_hard_error"] is not True:
    fail("nanoda_config.json unpermitted_axiom_hard_error must be true")
if cfg["nat_extension"] is not True or cfg["string_extension"] is not True:
    fail("nanoda_config.json nat_extension and string_extension must be true")
if type(cfg["num_threads"]) is not int or not (1 <= cfg["num_threads"] <= 4):
    fail(f"nanoda_config.json invalid num_threads: {cfg['num_threads']!r}")
permitted = cfg["permitted_axioms"]
if not isinstance(permitted, list) or not all(isinstance(x, str) for x in permitted):
    fail(f"nanoda_config.json invalid permitted_axioms: {permitted!r}")
if set(permitted) != STANDARD_AXIOMS:
    fail(f"nanoda_config.json unexpected permitted_axioms: {permitted!r}")
export_path = pathlib.Path(cfg["export_file_path"])
if export_path.name != "proof_full.ndjson":
    fail(f"nanoda_config.json unexpected export_file_path: {export_path}")

stats = validate_ndjson(export_path, set(permitted))
record_invocation(LOG_PATH, {
    "tool": "nanoda_bin",
    "argv": args,
    "config": cfg,
    "stats": stats,
})
forced_exit = FORCED_EXIT
env_exit = os.environ.get("ANNEAL_STUB_NANODA_EXIT")
if env_exit:
    forced_exit = int(env_exit)
if FORCED_DIAG:
    sys.stderr.write(f"{FORCED_DIAG}\n")
sys.exit(forced_exit)
"#;

    const CON_RON_STUB_BODY: &str = r#"
args = sys.argv[1:]
if len(args) != 3:
    fail(f"con-ron expected 3 arguments (--verified --jobs=N <proof_full.ndjson>), got {args!r}")
if args[0] != "--verified":
    fail(f"con-ron arg[0] must be --verified, got {args[0]!r}")
if not args[1].startswith("--jobs="):
    fail(f"con-ron arg[1] must be --jobs=N, got {args[1]!r}")
jobs_str = args[1][len("--jobs="):]
if not jobs_str.isdigit() or not (1 <= int(jobs_str) <= 2):
    fail(f"con-ron invalid --jobs value: {args[1]!r}")
ndjson_path = pathlib.Path(args[2])
if ndjson_path.name != "proof_full.ndjson":
    fail(f"con-ron unexpected NDJSON path: {ndjson_path}")

stats = validate_ndjson(ndjson_path, STANDARD_AXIOMS)
record_invocation(LOG_PATH, {
    "tool": "con-ron",
    "argv": args,
    "jobs": int(jobs_str),
    "stats": stats,
})
forced_exit = FORCED_EXIT
env_exit = os.environ.get("ANNEAL_STUB_CON_RON_EXIT")
if env_exit:
    forced_exit = int(env_exit)
if FORCED_DIAG:
    sys.stderr.write(f"{FORCED_DIAG}\n")
sys.exit(forced_exit)
"#;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum StubBehavior {
        Accept,
        Fail { exit_code: i32, diagnostic: &'static str },
        PanicAtExitZero { diagnostic: &'static str },
    }

    impl StubBehavior {
        fn exit_code(self) -> i32 {
            match self {
                Self::Accept | Self::PanicAtExitZero { .. } => 0,
                Self::Fail { exit_code, .. } => exit_code,
            }
        }

        fn diagnostic(self) -> &'static str {
            match self {
                Self::Accept => "",
                Self::Fail { diagnostic, .. } | Self::PanicAtExitZero { diagnostic } => diagnostic,
            }
        }
    }

    #[derive(Clone, Debug)]
    struct SyntheticHarnessConfig {
        omit_init_primitive: Option<&'static str>,
        tamper_expected_claim_in_expected: bool,
        tamper_expected_claim_in_proof: bool,
        inject_custom_axiom_in_proof: Option<&'static str>,
        nanoda_behavior: StubBehavior,
        con_ron_behavior: StubBehavior,
    }

    impl Default for SyntheticHarnessConfig {
        fn default() -> Self {
            Self {
                omit_init_primitive: None,
                tamper_expected_claim_in_expected: false,
                tamper_expected_claim_in_proof: false,
                inject_custom_axiom_in_proof: None,
                nanoda_behavior: StubBehavior::Accept,
                con_ron_behavior: StubBehavior::Accept,
            }
        }
    }

    struct SyntheticComparatorHarness {
        tmp: TempDir,
        lean_bin: PathBuf,
        nanoda_bin: PathBuf,
        con_ron_bin: PathBuf,
        fixtures_dir: PathBuf,
        invocation_log: PathBuf,
        request: TargetAuditRequest,
    }

    fn build_init_ndjson(omit_primitive: Option<&str>) -> String {
        let mut init_lines = vec![
            SYNTHETIC_META.to_owned(),
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
            if omit_primitive == Some(prim) {
                continue;
            }
            let nid = intern(prim, &mut init_lines);
            let line = match prim {
                "Quot" => {
                    format!(r#"{{"quot":{{"kind":"type","levelParams":[],"name":{nid},"type":1}}}}"#)
                }
                "Quot.mk" => {
                    format!(r#"{{"quot":{{"kind":"ctor","levelParams":[],"name":{nid},"type":1}}}}"#)
                }
                "Quot.lift" => {
                    format!(r#"{{"quot":{{"kind":"lift","levelParams":[],"name":{nid},"type":1}}}}"#)
                }
                "Quot.ind" => {
                    format!(r#"{{"quot":{{"kind":"ind","levelParams":[],"name":{nid},"type":1}}}}"#)
                }
                _ => format!(
                    r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#
                ),
            };
            init_lines.push(line);
        }
        for ax in STANDARD_PERMITTED_AXIOMS {
            let nid = intern(ax, &mut init_lines);
            init_lines.push(format!(
                r#"{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{nid},"type":0}}}}"#
            ));
        }
        for decl in PINNED_SYSTEM_PLATFORM_DECLS {
            let nid = intern(decl, &mut init_lines);
            if decl == "System.Platform.getNumBits" {
                init_lines.push(format!(
                    r#"{{"opaque":{{"all":[{nid}],"isUnsafe":false,"levelParams":[],"name":{nid},"type":1,"value":0}}}}"#
                ));
            } else {
                init_lines.push(format!(
                    r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#
                ));
            }
        }
        init_lines.join("\n") + "\n"
    }

    fn build_expected_ndjson(tamper_claim: bool) -> String {
        let claim_value_expr = if tamper_claim { 10 } else { 17 };
        [
            SYNTHETIC_META.to_owned(),
            r#"{"in":10,"str":{"pre":0,"str":"Trusted"}}"#.to_owned(),
            r#"{"in":11,"str":{"pre":10,"str":"MirSemantics"}}"#.to_owned(),
            r#"{"in":12,"str":{"pre":11,"str":"UnitTheorem"}}"#.to_owned(),
            r#"{"in":13,"str":{"pre":11,"str":"Crate"}}"#.to_owned(),
            r#"{"in":14,"str":{"pre":13,"str":"mk"}}"#.to_owned(),
            r#"{"in":15,"str":{"pre":0,"str":"Captured"}}"#.to_owned(),
            r#"{"in":16,"str":{"pre":15,"str":"program"}}"#.to_owned(),
            r#"{"in":17,"str":{"pre":0,"str":"Spec"}}"#.to_owned(),
            r#"{"in":18,"str":{"pre":17,"str":"specs"}}"#.to_owned(),
            r#"{"in":19,"str":{"pre":0,"str":"Expected"}}"#.to_owned(),
            r#"{"in":20,"str":{"pre":19,"str":"claim"}}"#.to_owned(),
            r#"{"ie":10,"sort":0}"#.to_owned(),
            r#"{"ie":11,"const":{"name":12,"us":[]}}"#.to_owned(),
            r#"{"ie":12,"const":{"name":14,"us":[]}}"#.to_owned(),
            r#"{"ie":13,"const":{"name":16,"us":[]}}"#.to_owned(),
            r#"{"ie":14,"const":{"name":18,"us":[]}}"#.to_owned(),
            r#"{"ie":15,"app":{"arg":13,"fn":12}}"#.to_owned(),
            r#"{"ie":16,"app":{"arg":14,"fn":15}}"#.to_owned(),
            r#"{"ie":17,"app":{"arg":16,"fn":11}}"#.to_owned(),
            r#"{"def":{"all":[12],"hints":"abbrev","levelParams":[],"name":12,"safety":"safe","type":10,"value":10}}"#.to_owned(),
            r#"{"def":{"all":[14],"hints":"abbrev","levelParams":[],"name":14,"safety":"safe","type":10,"value":10}}"#.to_owned(),
            r#"{"def":{"all":[16],"hints":"abbrev","levelParams":[],"name":16,"safety":"safe","type":10,"value":10}}"#.to_owned(),
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#.to_owned(),
            format!(
                r#"{{"def":{{"all":[20],"hints":"abbrev","levelParams":[],"name":20,"safety":"safe","type":10,"value":{claim_value_expr}}}}}"#
            ),
        ]
        .join("\n")
            + "\n"
    }

    fn build_proof_ndjson(tamper_claim: bool, custom_axiom: Option<&str>) -> String {
        let base_expected = build_expected_ndjson(tamper_claim);
        let mut lines = vec![
            base_expected.trim_end().to_owned(),
            r#"{"in":21,"str":{"pre":0,"str":"Proof"}}"#.to_owned(),
            r#"{"in":22,"str":{"pre":21,"str":"verify"}}"#.to_owned(),
            r#"{"ie":20,"const":{"name":20,"us":[]}}"#.to_owned(),
        ];
        if let Some(ax_leaf) = custom_axiom {
            lines.push(format!(r#"{{"in":23,"str":{{"pre":21,"str":"{ax_leaf}"}}}}"#));
            lines.push(r#"{"ie":21,"const":{"name":23,"us":[]}}"#.to_owned());
            lines.push(
                r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":23,"type":20}}"#.to_owned(),
            );
            lines.push(
                r#"{"thm":{"all":[22],"levelParams":[],"name":22,"type":20,"value":21}}"#.to_owned(),
            );
        } else {
            lines.push(
                r#"{"thm":{"all":[22],"levelParams":[],"name":22,"type":20,"value":10}}"#.to_owned(),
            );
        }
        lines.join("\n") + "\n"
    }

    fn render_inspecting_stub(body: &str, log_path: &Path, behavior: StubBehavior) -> String {
        let log_json = serde_json::to_string(&log_path.to_string_lossy()).unwrap();
        let diag_json = serde_json::to_string(behavior.diagnostic()).unwrap();
        format!(
            "#!/usr/bin/env python3\n{PYTHON_NDJSON_VALIDATOR}\nLOG_PATH = {log_json}\nFORCED_EXIT = {}\nFORCED_DIAG = {diag_json}\n{body}",
            behavior.exit_code()
        )
    }

    impl SyntheticComparatorHarness {
        fn new(cfg: SyntheticHarnessConfig) -> Self {
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

            let fixtures_dir = tmp.path().join("ndjson_fixtures");
            fs::create_dir_all(&fixtures_dir).unwrap();
            fs::write(
                fixtures_dir.join("init.ndjson"),
                build_init_ndjson(cfg.omit_init_primitive),
            )
            .unwrap();
            fs::write(
                fixtures_dir.join("expected.ndjson"),
                build_expected_ndjson(cfg.tamper_expected_claim_in_expected),
            )
            .unwrap();
            fs::write(
                fixtures_dir.join("proof.ndjson"),
                build_proof_ndjson(
                    cfg.tamper_expected_claim_in_proof,
                    cfg.inject_custom_axiom_in_proof,
                ),
            )
            .unwrap();

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

            let invocation_log = tmp.path().join("stub_invocations.jsonl");
            let nanoda_bin = bin_dir.join("nanoda_bin");
            fs::write(
                &nanoda_bin,
                render_inspecting_stub(NANODA_STUB_BODY, &invocation_log, cfg.nanoda_behavior),
            )
            .unwrap();
            fs::set_permissions(&nanoda_bin, fs::Permissions::from_mode(0o755)).unwrap();

            let con_ron_bin = bin_dir.join("con-ron");
            fs::write(
                &con_ron_bin,
                render_inspecting_stub(CON_RON_STUB_BODY, &invocation_log, cfg.con_ron_behavior),
            )
            .unwrap();
            fs::set_permissions(&con_ron_bin, fs::Permissions::from_mode(0o755)).unwrap();

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
            let request = TargetAuditRequest {
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

            Self {
                tmp,
                lean_bin,
                nanoda_bin,
                con_ron_bin,
                fixtures_dir,
                invocation_log,
                request,
            }
        }

        fn checker(&self) -> Checker {
            let mut checker =
                Checker::new(&repo_root(), Some(&self.lean_bin)).expect("create checker");
            checker.set_allow_unpinned_lean(true);
            checker.set_sandbox_mode(SandboxMode::Unsandboxed);
            checker
        }

        fn invocations(&self) -> Vec<Value> {
            if !self.invocation_log.is_file() {
                return Vec::new();
            }
            fs::read_to_string(&self.invocation_log)
                .unwrap()
                .lines()
                .filter(|line| !line.is_empty())
                .map(|line| serde_json::from_str::<Value>(line).expect("valid invocation log JSON"))
                .collect()
        }
    }

    /// Run `Checker::run_target` through the NDJSON comparator route against
    /// a synthetic `v4.35.0` sysroot whose `nanoda_bin` and `con-ron` stubs
    /// inspect CLI flags and NDJSON payloads before applying their configured
    /// [`StubBehavior`].
    fn run_synthetic_ndjson_pipeline(
        nanoda_behavior: StubBehavior,
        con_ron_behavior: StubBehavior,
    ) -> (SyntheticComparatorHarness, Result<Value, cargo_anneal::Failure>) {
        let harness = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
            nanoda_behavior,
            con_ron_behavior,
            ..Default::default()
        });
        let mut checker = harness.checker();
        let res = checker.run_target(&harness.request);
        (harness, res)
    }

    #[test]
    fn synthetic_ndjson_comparator_runs_full_target_audit_pipeline_without_v435_install() {
        let (harness, res) =
            run_synthetic_ndjson_pipeline(StubBehavior::Accept, StubBehavior::Accept);
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
                    (
                        e["name"].as_str().unwrap().to_owned(),
                        e["module"].as_str().unwrap().to_owned(),
                    )
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
            closure("subjectClosure")
                .contains(&("Captured.program".to_owned(), "Captured".to_owned()))
        );
        assert!(
            closure("specificationClosure")
                .contains(&("Spec.specs".to_owned(), "Spec".to_owned()))
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

        // Confirm both inspecting kernel stubs actually ran in order and
        // validated exact CLI flags, config JSON, and NDJSON declarations.
        let calls = harness.invocations();
        let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
        assert_eq!(tools, vec!["nanoda_bin", "con-ron"]);
        assert_eq!(calls[0]["config"]["unpermitted_axiom_hard_error"], json!(true));
        assert_eq!(calls[0]["config"]["nat_extension"], json!(true));
        assert_eq!(calls[0]["config"]["string_extension"], json!(true));
        assert_eq!(calls[1]["argv"][0], json!("--verified"));
        assert!(calls[0]["stats"]["decl_count"].as_u64().is_some_and(|n| n >= 6));
        assert!(calls[1]["stats"]["decl_count"].as_u64().is_some_and(|n| n >= 6));
    }

    /// The comparator route fails closed whenever either required kernel
    /// rejects the export, by a nonzero exit or by a Lean panic marker on
    /// stderr despite exit code 0, without a `v4.35.0` install.
    #[test]
    fn synthetic_ndjson_comparator_fails_closed_when_a_stub_kernel_rejects() {
        let rejecting = StubBehavior::Fail { exit_code: 1, diagnostic: "type mismatch" };
        let panicking = StubBehavior::PanicAtExitZero { diagnostic: "PANIC at Lean.Kernel" };
        for (label, nanoda_bin, con_ron, code, needle) in [
            (
                "nanoda_bin exit 1",
                rejecting,
                StubBehavior::Accept,
                1,
                "nanoda_bin rejected proof export",
            ),
            (
                "con-ron exit 1",
                StubBehavior::Accept,
                rejecting,
                1,
                "con-ron rejected proof export",
            ),
            ("nanoda_bin panic", panicking, StubBehavior::Accept, 2, "Lean runtime panic marker"),
            ("con-ron panic", StubBehavior::Accept, panicking, 2, "Lean runtime panic marker"),
        ] {
            let (harness, res) = run_synthetic_ndjson_pipeline(nanoda_bin, con_ron);
            let err = res.expect_err(label);
            assert_eq!(err.code, code, "{label}: {err}");
            assert!(err.message.contains(needle), "{label}: {err}");
            let (phase, expected_tools): (&str, &[&str]) = if nanoda_bin == StubBehavior::Accept {
                ("con-ron", &["nanoda_bin", "con-ron"])
            } else {
                ("nanoda", &["nanoda_bin"])
            };
            assert!(err.phase.contains(phase), "{label}: {err}");
            let calls = harness.invocations();
            let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
            assert_eq!(tools, expected_tools, "{label}");
        }
    }

    #[test]
    fn synthetic_ndjson_comparator_rejects_nanoda_nonzero_exit() {
        let (harness, res) = run_synthetic_ndjson_pipeline(
            StubBehavior::Fail {
                exit_code: 1,
                diagnostic: "injected nanoda_bin kernel rejection",
            },
            StubBehavior::Accept,
        );
        let err = res.unwrap_err();
        assert_eq!(err.code, 1, "nanoda_bin failure must fail with policy code 1: {err}");
        assert_eq!(err.phase, "ndjson-nanoda", "{err}");
        assert!(err.message.contains("injected nanoda_bin kernel rejection"), "{err}");

        // Must fail closed before invoking `con-ron`.
        let calls = harness.invocations();
        let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
        assert_eq!(tools, vec!["nanoda_bin"]);
    }

    #[test]
    fn synthetic_ndjson_comparator_rejects_con_ron_nonzero_exit() {
        let (harness, res) = run_synthetic_ndjson_pipeline(
            StubBehavior::Accept,
            StubBehavior::Fail { exit_code: 1, diagnostic: "injected con-ron kernel rejection" },
        );
        let err = res.unwrap_err();
        assert_eq!(err.code, 1, "con-ron failure must fail with policy code 1: {err}");
        assert_eq!(err.phase, "ndjson-con-ron", "{err}");
        assert!(err.message.contains("injected con-ron kernel rejection"), "{err}");

        let calls = harness.invocations();
        let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
        assert_eq!(tools, vec!["nanoda_bin", "con-ron"]);
    }

    #[test]
    fn synthetic_ndjson_comparator_rejects_tampered_expected_claim() {
        // 1. Tampering `Expected.claim` in the untrusted proof export diverges
        // from trusted `expected_cone.ndjson`.
        let proof_tamper = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
            tamper_expected_claim_in_proof: true,
            ..Default::default()
        });
        let mut checker = proof_tamper.checker();
        let err = checker.run_target(&proof_tamper.request).unwrap_err();
        assert_eq!(err.code, 1, "proof-side Expected.claim tamper must fail with code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(
            err.message.contains("Expected.claim")
                && err.message.contains("differs between trusted expected export and proof export"),
            "{err}"
        );
        assert!(proof_tamper.invocations().is_empty());

        // 2. Tampering `Expected.claim` identically in BOTH exports still fails
        // canonical claim-body verification.
        let both_tamper = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
            tamper_expected_claim_in_expected: true,
            tamper_expected_claim_in_proof: true,
            ..Default::default()
        });
        let mut checker = both_tamper.checker();
        let err = checker.run_target(&both_tamper.request).unwrap_err();
        assert_eq!(err.code, 1, "canonical Expected.claim tamper must fail with code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(
            err.message.contains("Expected.claim")
                && err.message.contains("differs from canonical root application"),
            "{err}"
        );
        assert!(both_tamper.invocations().is_empty());
    }

    #[test]
    fn synthetic_ndjson_comparator_rejects_missing_init_primitive_and_custom_axiom() {
        // 1. Missing pinned `Init` primitive (`Nat.gcd`) fails closed.
        let missing_prim = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
            omit_init_primitive: Some("Nat.gcd"),
            ..Default::default()
        });
        let mut checker = missing_prim.checker();
        let err = checker.run_target(&missing_prim.request).unwrap_err();
        assert_eq!(err.code, 2, "missing Init primitive must fail with operational code 2: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(err.message.contains("Nat.gcd"), "{err}");
        assert!(missing_prim.invocations().is_empty());

        // 2. Unexpected custom axiom (`Proof.cheat`) in exported NDJSON fails
        // closed with policy code 1.
        let custom_ax = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
            inject_custom_axiom_in_proof: Some("cheat"),
            ..Default::default()
        });
        let mut checker = custom_ax.checker();
        let err = checker.run_target(&custom_ax.request).unwrap_err();
        assert_eq!(err.code, 1, "custom axiom must fail with policy code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(
            err.message.contains("unpermitted axiom `Proof.cheat` in proof export"),
            "{err}"
        );
        assert!(custom_ax.invocations().is_empty());
    }

    #[test]
    fn synthetic_inspecting_stubs_reject_malformed_cli_and_ndjson_directly() {
        let harness = SyntheticComparatorHarness::new(SyntheticHarnessConfig::default());
        let scratch = harness.tmp.path().join("direct_stub_cases");
        fs::create_dir_all(&scratch).unwrap();
        let valid_proof = harness.fixtures_dir.join("proof.ndjson");
        let staged_valid = scratch.join("proof_full.ndjson");
        fs::copy(&valid_proof, &staged_valid).unwrap();

        let write_nanoda_cfg = |name: &str, ndjson: &Path, hard_err: bool| -> PathBuf {
            let dir = scratch.join(name);
            fs::create_dir_all(&dir).unwrap();
            let cfg_path = dir.join("nanoda_config.json");
            let cfg = json!({
                "use_stdin": false,
                "export_file_path": ndjson.to_string_lossy(),
                "permitted_axioms": STANDARD_PERMITTED_AXIOMS,
                "unpermitted_axiom_hard_error": hard_err,
                "num_threads": 2,
                "nat_extension": true,
                "string_extension": true,
            });
            fs::write(&cfg_path, serde_json::to_vec(&cfg).unwrap()).unwrap();
            cfg_path
        };

        // 1. `nanoda_bin` rejects weakened config
        // (`unpermitted_axiom_hard_error: false`).
        let weak_cfg = write_nanoda_cfg("weak_cfg", &staged_valid, false);
        let out = Command::new(&harness.nanoda_bin).arg(&weak_cfg).output().unwrap();
        assert!(!out.status.success(), "nanoda_bin stub must reject hard_error=false");
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("unpermitted_axiom_hard_error"),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );

        // 2. `con-ron` rejects wrong flag where `--verified` is required.
        let out = Command::new(&harness.con_ron_bin)
            .args(["--unverified", "--jobs=2", staged_valid.to_str().unwrap()])
            .output()
            .unwrap();
        assert!(!out.status.success(), "con-ron stub must reject --unverified");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("must be --verified"), "{stderr}");

        // 3. Both stubs reject tampered `Expected.claim`, custom axioms,
        // forbidden markers, and malformed JSON.
        let tampered_dir = scratch.join("tampered");
        fs::create_dir_all(&tampered_dir).unwrap();
        let tampered_ndjson = tampered_dir.join("proof_full.ndjson");
        fs::write(&tampered_ndjson, build_proof_ndjson(true, None)).unwrap();

        let axiom_dir = scratch.join("custom_axiom");
        fs::create_dir_all(&axiom_dir).unwrap();
        let axiom_ndjson = axiom_dir.join("proof_full.ndjson");
        fs::write(&axiom_ndjson, build_proof_ndjson(false, Some("cheat"))).unwrap();

        let marker_dir = scratch.join("forbidden_marker");
        fs::create_dir_all(&marker_dir).unwrap();
        let marker_ndjson = marker_dir.join("proof_full.ndjson");
        let mut with_marker = build_proof_ndjson(false, None);
        with_marker.push_str(r#"{"in":99,"str":{"pre":0,"str":"ANNEAL_FORBIDDEN_MARKER"}}"#);
        with_marker.push('\n');
        fs::write(&marker_ndjson, with_marker).unwrap();

        let malformed_dir = scratch.join("malformed");
        fs::create_dir_all(&malformed_dir).unwrap();
        let malformed_ndjson = malformed_dir.join("proof_full.ndjson");
        fs::write(&malformed_ndjson, format!("{SYNTHETIC_META}\n{{not-json\n")).unwrap();

        for (label, bad_ndjson, expected_substr) in [
            ("tampered-claim", &tampered_ndjson, "tampered Expected.claim"),
            ("custom-axiom", &axiom_ndjson, "unpermitted axiom Proof.cheat"),
            ("forbidden-marker", &marker_ndjson, "ANNEAL_FORBIDDEN_MARKER"),
            ("malformed-json", &malformed_ndjson, "invalid JSON"),
        ] {
            let cfg = write_nanoda_cfg(label, bad_ndjson, true);
            let nanoda_out = Command::new(&harness.nanoda_bin).arg(&cfg).output().unwrap();
            assert!(
                !nanoda_out.status.success(),
                "nanoda_bin stub must reject {label}"
            );
            let nanoda_err = String::from_utf8_lossy(&nanoda_out.stderr);
            assert!(
                nanoda_err.contains(expected_substr),
                "nanoda_bin {label}: expected `{expected_substr}` in `{nanoda_err}`"
            );

            let con_ron_out = Command::new(&harness.con_ron_bin)
                .args(["--verified", "--jobs=2", bad_ndjson.to_str().unwrap()])
                .output()
                .unwrap();
            assert!(
                !con_ron_out.status.success(),
                "con-ron stub must reject {label}"
            );
            let con_ron_err = String::from_utf8_lossy(&con_ron_out.stderr);
            assert!(
                con_ron_err.contains(expected_substr),
                "con-ron {label}: expected `{expected_substr}` in `{con_ron_err}`"
            );
        }

        // 4. Fault-injection env vars work on direct stub invocations.
        let valid_cfg = write_nanoda_cfg("valid_fault_inject", &staged_valid, true);
        let out = Command::new(&harness.nanoda_bin)
            .arg(&valid_cfg)
            .env("ANNEAL_STUB_NANODA_EXIT", "1")
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(1));

        let out = Command::new(&harness.con_ron_bin)
            .args(["--verified", "--jobs=2", staged_valid.to_str().unwrap()])
            .env("ANNEAL_STUB_CON_RON_EXIT", "1")
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(1));
    }
}
