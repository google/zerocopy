// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Axiom policy, compiler-override and initializer metadata, and the
//! classification of proof versus operational failures.

use super::*;

/// The inspector pins the original foundation's axiom list itself. A request
/// that widens, narrows or relabels that list is refused before any closure.
#[test]
fn rejects_axiom_policy_other_than_the_original_foundation() {
    let f = Fixture::new(PROOF);
    let mut checker = f.accepted_checker();
    let original = checker.admitted().unwrap().axioms.clone();
    let mut widened = original.clone();
    widened.push(("Lean.ofReduceBool".into(), "Init.Core".into()));
    let relabeled: Vec<(String, String)> = original
        .iter()
        .map(|(name, _)| (name.clone(), "Proof".to_string()))
        .collect();
    for axioms in [widened, original[1..].to_vec(), relabeled] {
        checker.admitted_mut().unwrap().axioms = axioms;
        reject_inspected(
            &mut checker,
            f.request.clone(),
            "target axiom policy differs from the original foundation",
        );
    }
}

#[test]
fn rejects_axiom_and_sorry_through_opaque_helpers() {
    Fixture::new("prelude\nimport Expected\naxiom hidden : Expected.claim\nopaque helper : Expected.claim := hidden\ntheorem Proof.verify : Expected.claim := helper\n").reject("unapproved axiom");
    Fixture::new("prelude\nimport Expected\nopaque helper : Expected.claim := by sorry\ntheorem Proof.verify : Expected.claim := helper\n").reject("sorryAx");
}

/// Lean v4.34.1 elaborates `native_decide` and `decide +native` into fresh
/// `._native.*` auxiliary axioms rather than referencing `Lean.ofReduceBool`
/// directly. Because `Checker::run_target` elaborates authored target proofs
/// without repository syntactic preflight, the target audit's foundation-axiom
/// allowlist is the defense that rejects both direct and opaque-helper
/// native-evaluation proofs.
#[test]
fn rejects_native_evaluation_auxiliary_axioms() {
    let decidable_goal = "(BitVec.ofNat 8 7).toNat = 7 ∧ \
        BitVec.and (BitVec.ofNat 8 7) (BitVec.ofNat 8 7) = BitVec.ofNat 8 7";
    for (body, expected_aux_prefix) in [
        (
            format!(
                "theorem Proof.verify : Expected.claim := \
                 by change {decidable_goal}; native_decide\n"
            ),
            "Proof.verify._native.native_decide.",
        ),
        (
            format!(
                "theorem Proof.verify : Expected.claim := \
                 by change {decidable_goal}; decide +native\n"
            ),
            "Proof.verify._native.decide.",
        ),
        (
            format!(
                "opaque helper : Expected.claim := \
                 by change {decidable_goal}; native_decide\n\
                 theorem Proof.verify : Expected.claim := helper\n"
            ),
            "helper._native.native_decide.",
        ),
        (
            format!(
                "opaque helper : Expected.claim := \
                 by change {decidable_goal}; decide +native\n\
                 theorem Proof.verify : Expected.claim := helper\n"
            ),
            "helper._native.decide.",
        ),
    ] {
        let source = format!("prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n{body}");
        let failure = Fixture::new(&source).run().unwrap_err();
        assert_eq!(failure.code, 1, "{failure}");
        assert_eq!(failure.phase, "target-audit", "{failure}");
        assert!(failure.message.contains("unapproved axiom"), "{failure}");
        assert!(
            failure.message.contains(expected_aux_prefix),
            "expected {expected_aux_prefix:?} in {failure}"
        );
    }
}

#[test]
fn rejects_authored_unchecked_compiler_override() {
    Fixture::new("prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\nunsafe def nativeHelper : Nat := 1\n@[implemented_by nativeHelper] def logicalHelper : Nat := 0\ntheorem Proof.verify : Expected.claim := And.intro rfl (by have h : logicalHelper = 0 := rfl; exact BitVec.and_self)\n")
        .reject("unchecked compiler override");
}

/// Authored extern and csimp metadata, including a scoped csimp entry, is
/// refused on a logically reached helper. Each alternative root reaches only
/// its own helper through `have`, so the selected clean root is accepted.
#[test]
fn rejects_authored_extern_and_csimp_metadata() {
    let f = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         @[extern \"anneal_audit_extern_helper\"] def externHelper (n : Nat) : Nat := n\n\
         def globalSlow (n : Nat) : Nat := n\n\
         def globalFast (n : Nat) : Nat := n\n\
         @[csimp] theorem globalSlow_eq : @globalSlow = @globalFast := rfl\n\
         def scopedSlow (n : Nat) : Nat := n\n\
         def scopedFast (n : Nat) : Nat := n\n\
         namespace Replacement\n\
         @[scoped csimp] theorem scopedSlow_eq : @scopedSlow = @scopedFast := rfl\n\
         end Replacement\n\
         theorem Proof.verify : Expected.claim := by exact And.intro rfl BitVec.and_self\n\
         theorem Proof.usesExtern : Expected.claim := And.intro rfl (by have h : externHelper = externHelper := rfl; exact BitVec.and_self)\n\
         theorem Proof.usesGlobalCsimp : Expected.claim := And.intro rfl (by have h : globalSlow = globalSlow := rfl; exact BitVec.and_self)\n\
         theorem Proof.usesScopedCsimp : Expected.claim := And.intro rfl (by have h : scopedSlow = scopedSlow := rfl; exact BitVec.and_self)\n",
    );
    let mut checker = f.accepted_checker();
    for (theorem, text) in [
        (
            "Proof.usesExtern",
            "unchecked compiler override on logical dependency externHelper",
        ),
        (
            "Proof.usesGlobalCsimp",
            "authored compiler replacement on logical dependency globalSlow",
        ),
        (
            "Proof.usesScopedCsimp",
            "authored compiler replacement on logical dependency scopedSlow",
        ),
    ] {
        let mut request = f.request.clone();
        request.theorem_name = theorem.into();
        reject_inspected(&mut checker, request, text);
    }
}

/// Authored `@[export]`, `@[init]`, and `@[builtin_init]` hooks in `Proof` or
/// non-`Proof` target modules are refused even when logically unreached, while
/// legitimate baseline `Init` `@[init]`/`@[export]` entries remain accepted.
#[test]
fn rejects_authored_export_init_and_builtin_init_metadata() {
    // 1. Pinned `Fixture`: unreached `@[export]` in `Proof` fails closed
    //    through `"target-export"` -> `"target-audit"`.
    Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         @[export anneal_audit_export_helper] def exportHelper (n : Nat) : Nat := n\n\
         theorem Proof.verify : Expected.claim := by exact And.intro rfl BitVec.and_self\n",
    )
    .reject_audit("unchecked compiler export override on exportHelper");

    // 2. Unpinned target mode: baseline `Init.Data.Random` (`@[init]` on
    //    `IO.stdGenRef`, plus `Init.Prelude` `@[export]`) stays accepted,
    //    while authored `@[init]` and `@[builtin_init]` in unreached `Proof`
    //    or non-`Proof` target modules (`Spec`/`Captured`) fail closed.
    let mut f_ok = Fixture::new(
        "import Expected\nimport Init.Data.Random\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let clean_spec = "import Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    f_ok.set("Spec", TargetRole::Specification, clean_spec);
    let mut chk = cargo_anneal::Checker::new(&f_ok.root, None).unwrap();
    chk.set_allow_unpinned_lean(true);
    let report = chk.run_target(&f_ok.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);

    let recompile_and_inspect = |chk: &mut cargo_anneal::Checker,
                                 f: &mut Fixture,
                                 role: TargetRole,
                                 mod_name: &str,
                                 src: &str|
     -> Failure {
        f.set(mod_name, role, src);
        let m = f.request.modules.iter().find(|x| x.module == mod_name).unwrap();
        let staged_src = chk.stage().join("ro").join(format!("{mod_name}.lean"));
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = fs::set_permissions(&staged_src, fs::Permissions::from_mode(0o600));
        }
        fs::copy(&m.source, &staged_src).unwrap();
        let hdr_json = chk.inspect_headers(&[(mod_name.to_string(), staged_src.clone())]).unwrap();
        let hdrs: cargo_anneal::PreflightResult = serde_json::from_value(hdr_json).unwrap();
        let header = hdrs.headers.into_iter().next().unwrap();
        let dest_olean = chk.stage().join("lib").join(format!("{mod_name}.olean"));
        if dest_olean.exists() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let _ = fs::set_permissions(&dest_olean, fs::Permissions::from_mode(0o600));
            }
        }
        chk.compile_lean_module(
            mod_name,
            &staged_src,
            header.imports,
            header.is_module,
            "lib",
            false,
            true,
        )
        .unwrap();
        chk.inspect_target(&f.request).unwrap_err()
    };

    for (label, proof_decl, expected) in [
        (
            "proof-init",
            "@[init] def initHelper : IO Unit := pure ()\n",
            "unchecked compiler init override on initHelper",
        ),
        (
            "proof-builtin-init",
            "@[builtin_init] def builtinInitHelper : IO Unit := pure ()\n",
            "unchecked compiler builtin_init override on builtinInitHelper",
        ),
    ] {
        let proof_src = format!(
            "import Expected\n{proof_decl}\
             theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n"
        );
        let err =
            recompile_and_inspect(&mut chk, &mut f_ok, TargetRole::Proof, "Proof", &proof_src);
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }
    // Restore clean `Proof` (and re-run headers-matched `Spec` / `Captured`)
    // before testing non-`Proof` target modules.
    f_ok.set(
        "Proof",
        TargetRole::Proof,
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    chk.set_allow_unpinned_lean(true);
    chk.run_target(&f_ok.request).unwrap();

    // 3. Direct non-`Proof` target module check (`Spec` for `@[export]`,
    //    `Captured` for `@[init]` / `@[builtin_init]`) bypassing preflight.
    let err_spec_export = recompile_and_inspect(
        &mut chk,
        &mut f_ok,
        TargetRole::Specification,
        "Spec",
        "import Model\n\
         @[export anneal_spec_export] def Spec.badExport (n : Nat) : Nat := n\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    assert_eq!(
        (err_spec_export.code, err_spec_export.phase.as_str()),
        (1, "target-audit"),
        "spec-export: {err_spec_export}"
    );
    assert!(
        err_spec_export
            .message
            .contains("unchecked compiler export override on Spec.badExport in Spec"),
        "spec-export: {err_spec_export}"
    );
    f_ok.set("Spec", TargetRole::Specification, clean_spec);
    chk.run_target(&f_ok.request).unwrap();

    for (label, decl, expected) in [
        (
            "capture-init",
            "@[init] def Captured.badInit : IO Unit := pure ()\n",
            "unchecked compiler init override on Captured.badInit in Captured",
        ),
        (
            "capture-builtin-init",
            "@[builtin_init] def Captured.badBuiltinInit : IO Unit := pure ()\n",
            "unchecked compiler builtin_init override on Captured.badBuiltinInit in Captured",
        ),
    ] {
        let cap_src =
            format!("import Model\n{decl}def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n");
        let err =
            recompile_and_inspect(&mut chk, &mut f_ok, TargetRole::Capture, "Captured", &cap_src);
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }
}

/// Expected source is a convenience for authors, not the root authority. Pure
/// name resolution cannot replace the proposition constructed by the inspector.
#[test]
fn rejects_compiled_expected_true_and_namespace_shadowing() {
    let proof = "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := True.intro\n";
    let mut f = Fixture::new(proof);
    f.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\ndef Expected.claim : Prop := True\n",
    );
    f.reject("Expected body differs");
    let mut f = Fixture::new(proof);
    f.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 8\n",
    );
    f.set("Spec", TargetRole::Specification,
        "prelude\nimport Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\ndef Expected.Trusted.MirSemantics.UnitTheorem (_ : Trusted.MirSemantics.Crate) : Prop := True\n");
    f.set("Expected", TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\nnamespace Expected\ndef claim : Prop := Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n");
    f.reject("Expected body differs");
}

#[test]
fn classifies_ordinary_elaboration_rejection_as_proof_failure() {
    let failure = Fixture::new(
        "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := True.intro\n",
    )
    .run()
    .unwrap_err();
    assert_eq!(failure.code, 1, "{failure}");
    assert_eq!(failure.phase, "compile-Proof");
}

/// Exercise actual pinned compiler failure reporting for deterministic Lean
/// proof resource limits (`runtime.maxHeartbeats`, `runtime.maxRecDepth`)
/// inside `compile-Proof`: both classify as exit-1 `proof_failed` with explicit
/// sub-reasons (`heartbeat_limit_exceeded` / `recursion_depth_exceeded`).
#[test]
fn classifies_proof_resource_limits_as_proof_failure() {
    for (body, expected_kind, expected_reason) in [
        (
            "set_option maxHeartbeats 1 in\nexample : (List.range 10000).foldl Nat.add 0 = 49995000 := by decide",
            "runtime.maxHeartbeats",
            "heartbeat_limit_exceeded",
        ),
        (
            "def wrong : Nat := \"bad\"\nset_option maxHeartbeats 1 in\nexample : (List.range 10000).foldl Nat.add 0 = 49995000 := by decide",
            "runtime.maxHeartbeats",
            "heartbeat_limit_exceeded",
        ),
        (
            "set_option maxRecDepth 2 in\nexample : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))))",
            "runtime.maxRecDepth",
            "recursion_depth_exceeded",
        ),
    ] {
        let failure = Fixture::new(&format!("prelude\nimport Expected\n{body}\n"))
            .run()
            .unwrap_err();
        assert_eq!(failure.code, 1, "{failure}");
        assert_eq!(failure.phase, "compile-Proof", "{failure}");
        assert_eq!(failure.reason.as_deref(), Some(expected_reason), "{failure:?}");
        assert!(failure.message.contains("stdout:"), "{failure}");
        assert!(failure.message.contains("stderr:"), "{failure}");
        assert!(failure.message.contains(expected_kind), "{failure}");
        assert!(failure.message.contains(expected_reason), "{failure}");
        if body.starts_with("def wrong") {
            assert!(failure.message.contains("Type mismatch"), "{failure}");
        }
    }
}

/// Exercise actual pinned compiler failure reporting for true operational
/// failures: native OOM panics inside `compile-Proof` and `runtime.*` resource
/// limits inside non-`Proof` modules must stay exit-2 `tool_failed`.
#[test]
fn classifies_native_failures_and_non_proof_resource_limits_as_operational() {
    for body in [
        "#eval (Array.replicate (2^128) (0 : UInt8)).size",
        "def wrong : Nat := \"bad\"\n#eval (Array.replicate (2^128) (0 : UInt8)).size",
    ] {
        // lean_mk_array rejects a Nat that does not fit size_t before
        // allocating the array, so this probes native OOM without exhausting
        // host memory.
        let failure = Fixture::new(&format!("prelude\nimport Expected\n{body}\n"))
            .run()
            .unwrap_err();
        assert_eq!(failure.code, 2, "{failure}");
        assert_eq!(failure.phase, "compile-Proof", "{failure}");
        assert!(failure.message.contains("stdout:"), "{failure}");
        assert!(failure.message.contains("stderr:"), "{failure}");
        assert!(
            failure.message.contains("INTERNAL PANIC: out of memory"),
            "{failure}"
        );
        // Lean 4.34.1 elaborates commands on a worker task while the main
        // thread drains JSON diagnostics in `SnapshotTree.runAndReport`.
        // Under CPU contention, the native OOM's `std::exit(1)` can
        // terminate the process before the main thread buffers the earlier
        // `Type mismatch` JSON on stdout; classification remains code 2
        // either way, and `stage::process_tests` deterministically covers
        // combined stdout JSON + stderr `INTERNAL PANIC`.
    }

    // A `runtime.maxHeartbeats` failure inside a non-`Proof` module (such as
    // `Captured`) must remain operational (exit 2), never downgraded to
    // `proof_failed`.
    let mut non_proof = Fixture::new(
        "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := by exact ⟨rfl, rfl⟩\n",
    );
    non_proof.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         set_option maxHeartbeats 1 in\n\
         example : (List.range 10000).foldl Nat.add 0 = 49995000 := by decide\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
    );
    let failure = non_proof.run().unwrap_err();
    assert_eq!(failure.code, 2, "{failure}");
    assert_eq!(failure.phase, "compile-Captured", "{failure}");
    assert!(failure.reason.is_none(), "{failure:?}");
    assert!(failure.message.contains("runtime.maxHeartbeats"), "{failure}");
}
