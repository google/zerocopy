// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specification effects and compiler overrides, Profile v2 theorems, and
//! the specification preflight module index.

use super::*;

/// Compiling a `TargetRole::Specification` module passes `-DautoImplicit=false`
/// and `-DrelaxedAutoImplicit=false`, rejecting undeclared multi-letter and
/// single-letter typo identifiers at `compile-Spec` while leaving
/// `TargetRole::Proof` auto-implicits unaffected;
/// `set_option autoImplicit true` inside a specification is also rejected
/// fail-closed in `"spec-preflight"`.
#[test]
fn spec_compilation_rejects_auto_implicit_typos_while_proof_unaffected() {
    for (label, decl, typo_ident) in [
        (
            "relaxed-auto-implicit-typo",
            "def Spec.typoRelaxed (n : Nat) : pre_ok → True := fun _ => True.intro\n",
            "pre_ok",
        ),
        (
            "single-letter-auto-implicit-typo",
            "def Spec.typoSingle (n : Nat) : q → True := fun _ => True.intro\n",
            "q",
        ),
    ] {
        let mut f = Fixture::new(PROOF);
        f.set(
            "Spec",
            TargetRole::Specification,
            &format!(
                "prelude\nimport Model\n{decl}\
                 def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"
            ),
        );
        let err = f.run().unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "compile-Spec", "{label}: {err}");
        assert!(
            err.message.contains("Unknown identifier")
                && err.message.contains(typo_ident)
                && err.message.contains("autoImplicit"),
            "{label}: expected autoImplicit rejection for {typo_ident}, got: {err}"
        );
    }

    // Attempting to re-enable `autoImplicit` via `set_option ... in` fails in
    // `"spec-preflight"` before elaboration.
    let mut f_opt = Fixture::new(PROOF);
    f_opt.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         set_option autoImplicit true in\n\
         def Spec.typoOpt (n : Nat) : pre_ok → True := fun _ => True.intro\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let err = f_opt.run().unwrap_err();
    assert_eq!(err.code, 1, "set_option autoImplicit true: {err}");
    assert_eq!(
        err.phase, "spec-preflight",
        "set_option autoImplicit true: {err}"
    );
    assert!(
        err.message.contains("unsupported option autoImplicit"),
        "set_option autoImplicit true: {err}"
    );

    // Proof modules remain unaffected (single-letter `autoImplicit` still
    // compiles and passes `"target-audit"` in `TargetRole::Proof`).
    let f_proof_ok = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.autoHelper (h : p = p) : p = p := h\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let report = f_proof_ok.run().unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
}

/// `"spec-preflight"` explicitly rejects `include_str`, `Init/Util.lean`'s
/// `lean_dbg_*` externs, `Lean.LoadDynlib` / `loadDynlib`, `Init.System.*`,
/// and `Std.Internal.UV.*` (including through `open` resolution), and
/// `"target-audit"` enforces the transitive spec ban as well.
#[test]
fn spec_preflight_and_target_audit_reject_io_debug_dynlib_and_uv() {
    for (label, expected_msg, body) in [
        ("include_str", "disallowed syntax", "def s : String := include_str \"Cargo.toml\"\n"),
        ("dbgSleep", "disallowed identifier", "def f : Nat := dbgSleep 0 (fun _ => 1)\n"),
        ("dbgTrace", "disallowed identifier", "def f : Nat := dbgTrace \"leak\" (fun _ => 1)\n"),
        (
            "dbgTraceIfShared",
            "disallowed identifier",
            "def f (x : Nat) : Nat := dbgTraceIfShared \"leak\" x\n",
        ),
        ("dbgStackTrace", "disallowed identifier", "def f : Nat := dbgStackTrace (fun _ => 1)\n"),
        ("loadDynlib", "disallowed identifier", "def f : Nat → Nat := loadDynlib\n"),
        (
            "init_system_ident",
            "disallowed reference",
            "def f := Init.System.FilePath.mk \".\"\n",
        ),
        ("std_internal_uv_ident", "disallowed reference", "def f := Std.Internal.UV.Loop.mk\n"),
        (
            "open_std_internal_uv",
            "disallowed reference UV.Loop.mk",
            "open Std.Internal in\ndef f := UV.Loop.mk\n",
        ),
    ] {
        let mut f = Fixture::new(PROOF);
        f.set(
            "Spec",
            TargetRole::Specification,
            &format!(
                "prelude\nimport Model\n{body}\
                 def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"
            ),
        );
        let mut checker = f.cargo_checker();
        let err = checker.run_target(&f.request).unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(err.message.contains(expected_msg), "{label}: {err}");
    }

    for (label, imp) in [
        ("import_init_system_io", "import Init.System.IO\n"),
        ("import_std_internal_uv", "import Std.Internal.UV\n"),
        ("import_std_internal_uv_tcp", "import Std.Internal.UV.TCP\n"),
    ] {
        let mut f = Fixture::new(PROOF);
        f.set(
            "Spec",
            TargetRole::Specification,
            &format!(
                "prelude\nimport Model\n{imp}\
                 def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"
            ),
        );
        let mut checker = f.cargo_checker();
        let err = checker.run_target(&f.request).unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "headers", "{label}: {err}");
        assert!(err.message.contains("disallowed sysroot import"), "{label}: {err}");
    }

    // `"target-audit"` enforces the transitive spec ban across helpers
    // declared in `Model` (which `"spec-preflight"` does not inspect).
    let model_base = "prelude\nimport Init.Data.BitVec.Basic\n\
        namespace Trusted.MirSemantics\n\
        structure Crate where\n  \
          program : BitVec 8\n  \
          specs : BitVec 8 → Prop\n\
        def UnitTheorem (c : Crate) : Prop := \
          c.program.toNat = 7 ∧ c.specs c.program\n";
    let mut f_trans = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim :=\n  \
           And.intro rfl (And.intro BitVec.and_self rfl)\n",
    );
    f_trans.set(
        "Model",
        TargetRole::Model,
        &format!(
            "{model_base}\
             def Model.dbgLeak (n : Nat) : Nat := dbgTrace \"leak\" (fun _ => n)\n"
        ),
    );
    f_trans.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs (p : BitVec 8) : Prop :=\n  \
           BitVec.and p p = p ∧ Trusted.MirSemantics.Model.dbgLeak p.toNat = p.toNat\n",
    );
    f_trans.reject_audit("specification transitively references disallowed constant");

    // `"target-audit"` also applies the transitive spec ban across duplicate
    // alternate theorem bodies in `.specification` (`pendingSourceAlternates`).
    let mut f_alt_trans = Fixture::new(PROOF);
    f_alt_trans.set(
        "Model",
        TargetRole::Model,
        &format!(
            "{model_base}\
             def Model.dbgLeak (n : Nat) : Nat := dbgTrace \"leak\" (fun _ => n)\n"
        ),
    );
    f_alt_trans.set(
        "SpecAlt",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         theorem SharedSpec.altDup : True :=\n  \
           (fun _ : Nat => True.intro) (Trusted.MirSemantics.Model.dbgLeak 0)\n",
    );
    f_alt_trans.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         theorem SharedSpec.altDup : True := True.intro\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    f_alt_trans.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_alt_trans.reject_audit("specification transitively references disallowed constant");
}

/// Neither `"target-export"` nor `"target-audit"` executes `[init]` module
/// initializers (`loadExts := false`), and `"target-audit"` still catches
/// authored `[init]` hooks and non-proof `.source` `@[csimp]` overrides from
/// the serialized extension entries of each module's artifact parts.
#[test]
fn target_export_and_audit_do_not_execute_init_and_catch_source_csimp_overrides() {
    // 1. `[init]` blocks inside `Proof` (imported in `"target-export"`) and
    //    `ModelAux` (non-proof module imported in `"target-audit"`) that throw
    //    an uncaught IO error if executed must never execute during
    //    `"target-export"` or `"target-audit"`. Omit `prelude` (unpinned mode)
    //    so `IO` and `IO.userError` are in scope without executing `ModelAux`
    //    during downstream target compilation.
    for (label, use_proof_init, expected_err) in [
        ("proof", true, "unchecked compiler init override on proofInitVal"),
        ("model-aux", false, "unchecked compiler init override on modelInitVal"),
    ] {
        let proof_src = if use_proof_init {
            "import Expected\n\
             def proofInit : IO Unit := throw (IO.userError \"PROOF_INIT_EXECUTED\")\n\
             @[init proofInit] def proofInitVal : Unit := ()\n\
             theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n"
        } else {
            "import Expected\n\
             theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n"
        };
        let mut f = Fixture::new(proof_src);
        if !use_proof_init {
            f.set(
                "ModelAux",
                TargetRole::Model,
                "def modelInit : IO Unit := throw (IO.userError \"MODEL_INIT_EXECUTED\")\n\
                 @[init modelInit] def modelInitVal : Unit := ()\n",
            );
        }
        let mut checker = f.cargo_checker();
        checker.set_allow_unpinned_lean(true);
        let err = checker.run_target(&f.request).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected_err), "{label}: {err}");
        assert!(
            !err.message.contains("PROOF_INIT_EXECUTED")
                && !err.message.contains("MODEL_INIT_EXECUTED"),
            "{label} executed [init] initializer: {err}"
        );
    }

    // 2. Non-proof `.source` `@[csimp]` override targeting a logically reached
    //    helper is caught in `"target-audit"` from serialized extension
    //    entries without requiring a separate `fixedMetadata` environment.
    let mut f_csimp = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl (And.intro rfl BitVec.and_self)\n",
    );
    f_csimp.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         def modelSlow (n : Nat) : Nat := n\n\
         def modelFast (n : Nat) : Nat := n\n\
         @[csimp] theorem modelSlow_eq : @modelSlow = @modelFast := rfl\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\n",
    );
    f_csimp.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs (p : BitVec 8) : Prop := modelSlow p.toNat = p.toNat ∧ BitVec.and p p = p\n",
    );
    f_csimp.reject_audit("authored compiler replacement on logical dependency modelSlow");
}

/// `"target-audit"` seeds `phase2Roots` with dependencies of the selected
/// `stored` proof body when an unreached realized theorem differs across
/// proof modules, so `checkAlternateProofs` replays both without missing
/// `unknown constant` errors.
#[test]
fn target_audit_replays_alternate_proof_with_unreached_stored_dependencies() {
    let mut f = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem SharedAlt.check : (fun x : Nat => x = x) 0 := rfl\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "ModelAux",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         def unreachedStoredOnlyAux : Nat := 1\n\
         theorem SharedAlt.check : (fun x : Nat => x = x) 0 :=\n  \
           (fun _ : Nat => rfl) unreachedStoredOnlyAux\n",
    );
    let mut checker = f.cargo_checker();
    let report = checker.run_target(&f.request).unwrap();
    assert_eq!(report["replay"], true, "{report}");
    assert_eq!(report["exactType"], true, "{report}");
}

/// Profile v2 canonical roots (`UnitTheoremV2` and `CrateTheoremV2`) bind to
/// `CrateV2.mk`, reject mismatched v1/forged claims, and reject unapproved
/// model-origin roots.
#[test]
fn accepts_profile_v2_unit_and_crate_theorems_and_rejects_forged_v2_claims() {
    let model_v2 = "\
prelude
import Init.Data.BitVec.Basic
namespace Trusted.MirSemantics
structure Crate where
  program : BitVec 8
  specs : BitVec 8 → Prop
structure CrateV2 where
  program : BitVec 8
  specs : BitVec 8 → Prop
def UnitTheorem (c : Crate) : Prop := (1 : Nat) = 1 ∧ c.program.toNat = 7 ∧ c.specs c.program
def UnitTheoremV2 (c : CrateV2) : Prop := c.program.toNat = 7 ∧ c.specs c.program
def CrateTheoremV2 (c : CrateV2) : Prop := c.program.toNat = 7 ∧ c.specs c.program
def BogusTheorem (_ : Crate) : Prop := True
end Trusted.MirSemantics
";
    let proof_ok = "\
prelude
import Expected
import Init.Data.BitVec.Lemmas
theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self
";

    for root in [
        "Trusted.MirSemantics.UnitTheoremV2",
        "Trusted.MirSemantics.CrateTheoremV2",
    ] {
        let mut f = Fixture::new(proof_ok);
        f.set("Model", TargetRole::Model, model_v2);
        f.request.canonical_root = root.into();
        f.set(
            "Expected",
            TargetRole::Expected,
            &format!(
                "prelude\nimport Captured\nimport Spec\n\
                 def Expected.claim : Prop := {root} \
                 (Trusted.MirSemantics.CrateV2.mk Captured.program Spec.specs)\n"
            ),
        );
        let report = f.run().unwrap();
        assert_eq!(report["replay"], true, "{root}: {report}");
        assert_eq!(report["exactType"], true, "{root}: {report}");
    }

    // Reject forged v2 claim whose Expected.claim targets v1 UnitTheorem.
    let mut f_mismatch = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl (And.intro rfl BitVec.and_self)\n",
    );
    f_mismatch.set("Model", TargetRole::Model, model_v2);
    f_mismatch.request.canonical_root = "Trusted.MirSemantics.UnitTheoremV2".into();
    f_mismatch.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
         (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_mismatch.reject_audit("Expected");

    // Reject forged Proof.verify weakening UnitTheoremV2's proposition.
    let mut f_forged_proof = Fixture::new(
        "prelude\nimport Expected\n\
         def Spec.alt (_ : BitVec 8) : Prop := True\n\
         theorem Proof.verify : Trusted.MirSemantics.UnitTheoremV2 \
         (Trusted.MirSemantics.CrateV2.mk Captured.program Spec.alt) := \
         And.intro rfl True.intro\n",
    );
    f_forged_proof.set("Model", TargetRole::Model, model_v2);
    f_forged_proof.request.canonical_root = "Trusted.MirSemantics.UnitTheoremV2".into();
    f_forged_proof.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop := Trusted.MirSemantics.UnitTheoremV2 \
         (Trusted.MirSemantics.CrateV2.mk Captured.program Spec.specs)\n",
    );
    f_forged_proof.reject_audit("target theorem type differs from Expected");

    // Reject an unapproved model-origin canonical root.
    let mut f_bogus = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := True.intro\n",
    );
    f_bogus.set("Model", TargetRole::Model, model_v2);
    f_bogus.request.canonical_root = "Trusted.MirSemantics.BogusTheorem".into();
    f_bogus.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop := Trusted.MirSemantics.BogusTheorem \
         (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_bogus.reject_audit("unexpected canonical root Trusted.MirSemantics.BogusTheorem");
}

/// `SpecPreflight`'s module index runs over real compiled target artifacts on
/// the pinned toolchain: it attributes compiler-generated constants (structure
/// constructors/projections and anonymous instances) to their defining
/// module, never lists `Proof` constants, reports no compiler overrides for
/// override-free modules, and refuses a mismatched `isModule` expectation
/// before importing. The sysroot index attributes `Init` constants to their
/// modules.
#[test]
fn spec_preflight_module_index_attributes_generated_target_constants() {
    let mut f = Fixture::new(
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nnamespace Contract\nstructure Box where\n  n : Nat\n\
         instance : Inhabited Box := ⟨⟨0⟩⟩\nend Contract\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let (roles, is_module) = with_spec_preflight(&f);
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    checker.run_target(&f.request).unwrap();

    let (origins, overrides) = checker.inspect_target_consts(&roles, &is_module).unwrap();
    for (name, module) in [
        ("Spec.specs", "Spec"),
        ("Contract.Box", "Spec"),
        ("Contract.Box.mk", "Spec"),
        ("Contract.Box.n", "Spec"),
        ("Contract.instInhabitedBox", "Spec"),
        ("Captured.program", "Captured"),
        ("Expected.claim", "Expected"),
        ("Trusted.MirSemantics.UnitTheorem", "Model"),
        ("Trusted.MirSemantics.Crate.mk", "Model"),
    ] {
        assert_eq!(origins.get(name).map(|(m, _)| m.as_str()), Some(module), "{name}: {origins:?}");
    }
    assert!(!origins.keys().any(|n| n.starts_with("Proof")), "{origins:?}");
    assert!(overrides.is_empty(), "{overrides:?}");

    let sysroot = checker.inspect_sysroot_consts().unwrap();
    assert_eq!(sysroot.get("Nat.add").map(String::as_str), Some("Init.Prelude"));
    assert!(!sysroot.contains_key("Spec.specs"));

    let mut wrong = is_module.clone();
    wrong.insert("Spec".to_owned(), true);
    let err = checker.inspect_target_consts(&roles, &wrong).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert!(err.message.contains("non-module artifact mismatch in Spec"), "{err}");
}

/// The module index fails closed on an `unsafe` constant in a non-`Proof`
/// target module and on a non-realized constant that two target modules
/// both declare (Lean's import keeps one module's proof under the other
/// module's index for equal theorem headers).
#[test]
fn spec_preflight_module_index_rejects_unsafe_and_colliding_target_constants() {
    let proof =
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n";

    let mut unsafe_f = Fixture::new(proof);
    unsafe_f.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\nunsafe def Captured.evil : Nat := 0\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
    );
    let (roles, is_module) = with_spec_preflight(&unsafe_f);
    let mut checker = cargo_anneal::Checker::new(&unsafe_f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    let _ = checker.run_target(&unsafe_f.request);
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert!(err.message.contains("declares unsafe constant Captured.evil"), "{err}");

    let mut dup_f = Fixture::new(proof);
    for name in ["SpecA", "SpecB"] {
        dup_f.set(
            name,
            TargetRole::Specification,
            "prelude\nimport Model\ntheorem Contract.t : True := True.intro\n",
        );
    }
    dup_f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nimport SpecA\nimport SpecB\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let (roles, is_module) = with_spec_preflight(&dup_f);
    let mut checker = cargo_anneal::Checker::new(&dup_f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    let _ = checker.run_target(&dup_f.request);
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert!(err.message.contains("constant Contract.t declared by"), "{err}");

    // Lean's import keeps the later of two equal-header theorems under the
    // earlier module's index, even for an equation-style name; differing
    // proofs fail closed instead of erasing one module's dependencies.
    let mut realized_f = Fixture::new(proof);
    for (name, value) in [("SpecA", "True.intro"), ("SpecB", "(fun _ : Nat => True.intro) 0")] {
        realized_f.set(
            name,
            TargetRole::Specification,
            &format!("prelude\nimport Model\ntheorem Contract.foo.eq_1 : True := {value}\n"),
        );
    }
    realized_f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nimport SpecA\nimport SpecB\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let (roles, is_module) = with_spec_preflight(&realized_f);
    let mut checker = cargo_anneal::Checker::new(&realized_f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    let _ = checker.run_target(&realized_f.request);
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert!(err.message.contains("Contract.foo.eq_1"), "{err}");
}

/// The module index reports a non-`Proof` target module's
/// `@[implemented_by]`, `@[extern]`, `@[csimp]`, and scoped `@[csimp]`
/// subjects, which the comparator rejects whenever a verified cone reaches
/// them.
#[test]
fn spec_preflight_module_index_reports_target_compiler_overrides() {
    let mut f = Fixture::new(
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\nnamespace Captured\n\
         def fImpl (n : Nat) : Nat := n\n\
         @[implemented_by fImpl] def f (n : Nat) : Nat := n\n\
         @[extern \"anneal_g\"] def g (n : Nat) : Nat := n\n\
         def h (n : Nat) : Nat := n\ndef hFast (n : Nat) : Nat := n\n\
         @[csimp] theorem h_eq : @h = @hFast := rfl\n\
         def k (n : Nat) : Nat := n\ndef kFast (n : Nat) : Nat := n\n\
         @[scoped csimp] theorem k_eq : @k = @kFast := rfl\n\
         def program : BitVec 8 := BitVec.ofNat 8 7\nend Captured\n",
    );
    let (roles, is_module) = with_spec_preflight(&f);
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    let _ = checker.run_target(&f.request);
    let (origins, overrides) = checker.inspect_target_consts(&roles, &is_module).unwrap();
    assert_eq!(origins.get("Captured.f").map(|(m, _)| m.as_str()), Some("Captured"));
    let expected: BTreeSet<String> =
        ["Captured.f", "Captured.g", "Captured.h", "Captured.k"].map(str::to_owned).into();
    assert_eq!(overrides, expected);
}

/// `SpecPreflight` `"target-consts"` enforces `Lean.aliasExtension` export
/// rules across target roles, admitting allowlisted `.foundation` exports
/// (`System.Platform.getNumBits`, `Nat.add`) while rejecting unapproved
/// axioms, `unsafe` exports, `Trusted`-root aliases, and reserved-root
/// aliases.
#[test]
fn spec_preflight_module_index_enforces_alias_exports_and_admits_foundation_exports() {
    let proof =
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n";

    // Positive control: allowlisted `.foundation` exports (including
    // `Quot.sound` from `Init.Prelude`) in `Spec` pass.
    let mut ok_f = Fixture::new(proof);
    ok_f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nnamespace MySpec\n\
         export System.Platform (getNumBits)\nexport Nat (add)\nexport Quot (sound)\nend MySpec\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let (roles, is_module) = with_spec_preflight(&ok_f);
    let mut checker = cargo_anneal::Checker::new(&ok_f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    checker.run_target(&ok_f.request).unwrap();
    checker.inspect_target_consts(&roles, &is_module).unwrap();

    // Negative case: `Spec` exporting an unapproved axiom declared in `Model`.
    let mut ax_f = Fixture::new(proof);
    ax_f.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace BadAx\naxiom unapprovedAx : Prop\nend BadAx\n\
         namespace Trusted.MirSemantics\nstructure Crate where\n  program : BitVec 8\n  \
         specs : BitVec 8 → Prop\ndef UnitTheorem (c : Crate) : Prop := \
         c.program.toNat = 7 ∧ c.specs c.program\n",
    );
    ax_f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nexport BadAx (unapprovedAx)\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let (ax_roles, ax_is_module) = with_spec_preflight(&ax_f);
    let mut ax_checker = cargo_anneal::Checker::new(&ax_f.root, None).unwrap();
    ax_checker.set_allow_unpinned_lean(true);
    let _ = ax_checker.run_target(&ax_f.request);
    let ax_err = ax_checker.inspect_target_consts(&ax_roles, &ax_is_module).unwrap_err();
    assert_eq!(ax_err.code, 1, "Spec unapprovedAx: {ax_err}");
    assert!(
        ax_err.message.contains("references unapproved axiom BadAx.unapprovedAx"),
        "Spec unapprovedAx: {ax_err}"
    );

    // Negative matrix across `Specification` and `Capture` alias exports.
    for (mod_name, role, src, expected_msg) in [
        (
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Init.Data.Array.Basic\nimport Model\n\
             namespace MySpec\nexport Array (modifyMUnsafe)\nend MySpec\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "references unsafe declaration Array.modifyMUnsafe",
        ),
        (
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\nnamespace Trusted\nexport Nat (add)\nend Trusted\n\
             def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
            "cannot export alias Trusted.add in Trusted namespace",
        ),
        (
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\nnamespace Expected\nexport Nat (add)\nend Expected\n\
             def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
            "cannot export alias Expected.add in reserved kernel namespace Expected",
        ),
    ] {
        let mut f = Fixture::new(proof);
        f.set(mod_name, role, src);
        let (roles, is_module) = with_spec_preflight(&f);
        let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
        checker.set_allow_unpinned_lean(true);
        let _ = checker.run_target(&f.request);
        let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
        assert_eq!(err.code, 1, "{mod_name}: {err}");
        assert!(err.message.contains(expected_msg), "{mod_name}: {err}");
    }
}

/// Both `SpecPreflight` `"target-consts"` and pinned `TrustedBoundary`
/// `"target-audit"` inspect Lean 4 `module`-mode targets across all `.olean`,
/// `.olean.server`, and `.olean.private` parts and across repeated
/// `(extName, entries)` pairs in `ModuleData.entries`:
/// - inventories `private` declarations and reports both public (deduplicated)
///   and `private` compiler overrides while admitting allowlisted `.foundation`
///   exports;
/// - catches `Lean.aliasExtension` exports and `@[extern]` overrides placed
///   only in `.olean` (part 0), only in `.olean.server` (part 1), or in an
///   earlier duplicate `ModuleData.entries` pair shadowed by a trailing `#[]`;
/// - rejects forged `unsafe`, duplicate, or uninventoried companion-part
///   constants and companion `isModule` flag mismatches on both routes.
#[test]
fn spec_preflight_module_index_scans_all_module_parts_and_duplicate_entries() {
    let mut f = Fixture::new(
        "module\nprelude\npublic import Expected\n\
         import Init.Data.BitVec.Lemmas\n\
         private theorem helper_ok : BitVec.and (BitVec.ofNat 8 7) (BitVec.ofNat 8 7) = BitVec.ofNat 8 7 := by exact BitVec.and_self\n\
         public theorem Proof.verify : Expected.claim := And.intro rfl helper_ok\n",
    );
    f.set(
        "Model",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
         @[expose] public section\n\
         namespace BadAx\naxiom unapprovedAx : Prop\nend BadAx\n\
         def Model.extFn (n : Nat) : Nat := n\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\nend\n",
    );
    f.set(
        "Captured",
        TargetRole::Capture,
        "module\nprelude\npublic import Model\n\
         private def Captured.privImpl (n : Nat) : Nat := n\n\
         @[implemented_by Captured.privImpl] private def Captured.privBy (n : Nat) : Nat := n\n\
         @[extern \"anneal_priv_ext\"] private def Captured.privExt (n : Nat) : Nat := n\n\
         public section\n\
         def Captured.recHelper : Nat → Nat\n  | 0 => 0\n  | k + 1 => Captured.recHelper k\n\
         end\n\
         @[expose] public section\n\
         @[extern \"anneal_pub_ext\"] def Captured.pubExt (n : Nat) : Nat := n\n\
         def Captured.part0Target (n : Nat) : Nat := n\n\
         def Captured.dupTarget (n : Nat) : Nat := n\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\nend\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "module\nprelude\npublic import Model\n\
         private def Spec.privHelper (n : Nat) : Nat := n\n\
         public section\n\
         def Spec.recHelper : Nat → Nat\n  | 0 => 0\n  | k + 1 => Spec.recHelper k\n\
         end\n\
         @[expose] public section\n\
         namespace MySpec\n\
         export System.Platform (getNumBits)\n\
         export Nat (add)\n\
         export Quot (sound)\n\
         end MySpec\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\nend\n",
    );
    f.set(
        "Expected",
        TargetRole::Expected,
        "module\nprelude\npublic import Model\npublic import Captured\npublic import Spec\n\
         @[expose] public section\n\
         def Expected.claim : Prop :=\n\
           Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
         end\n",
    );

    let (roles, mut is_module) = with_spec_preflight(&f);
    for v in is_module.values_mut() {
        *v = true;
    }
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    checker.run_target(&f.request).unwrap();

    for name in ["Model", "Captured", "Spec", "Expected", "Proof"] {
        let arts = &checker.admitted().unwrap().artifacts[name];
        assert_eq!(arts.olean_parts.len(), 3, "expected 3 parts for {name}: {:?}", arts.olean_parts);
    }

    // 1. Positive control: private constants, non-`@[expose]` recursive public
    //    definitions (`Spec.recHelper._unsafe_rec` and
    //    `Captured.recHelper._unsafe_rec`, which erase to
    //    `.axiomInfo { isUnsafe := true }` in `.olean` / `.olean.server` while
    //    remaining `.defnInfo { safety := .partial }` in `.olean.private`),
    //    public/private overrides, and allowlisted `.foundation` exports in
    //    3-part `module`-mode targets.
    let (origins, overrides) = checker.inspect_target_consts(&roles, &is_module).unwrap();
    assert!(
        origins.keys().any(|k| k.ends_with("Spec.privHelper")),
        "missing private Spec constant in module-mode inventory: {origins:?}"
    );
    assert_eq!(
        origins.get("Spec.recHelper._unsafe_rec").map(|(m, p)| (m.as_str(), *p)),
        Some(("Spec", true)),
        "expected paired Spec.recHelper._unsafe_rec in module-mode inventory: {origins:?}"
    );
    assert_eq!(
        origins.get("Captured.recHelper._unsafe_rec").map(|(m, p)| (m.as_str(), *p)),
        Some(("Captured", true)),
        "expected paired Captured.recHelper._unsafe_rec in module-mode inventory: {origins:?}"
    );
    assert!(overrides.contains("Captured.pubExt"), "missing public override: {overrides:?}");
    assert!(
        overrides.iter().any(|k| k.ends_with("Captured.privExt")),
        "missing private @[extern] override: {overrides:?}"
    );
    assert!(
        overrides.iter().any(|k| k.ends_with("Captured.privBy")),
        "missing private @[implemented_by] override: {overrides:?}"
    );

    let part_paths = |stage: &Path, stem: &str| -> [PathBuf; 3] {
        [
            stage.join(format!("lib/{stem}.olean")),
            stage.join(format!("lib/{stem}.olean.server")),
            stage.join(format!("lib/{stem}.olean.private")),
        ]
    };
    let stage = checker.stage().to_path_buf();
    let backup_parts = |stem: &str| -> [Vec<u8>; 3] {
        let [p0, p1, p2] = part_paths(&stage, stem);
        [fs::read(p0).unwrap(), fs::read(p1).unwrap(), fs::read(p2).unwrap()]
    };
    let restore_parts = |stem: &str, saved: &[Vec<u8>; 3]| {
        let [p0, p1, p2] = part_paths(&stage, stem);
        fs::write(p0, &saved[0]).unwrap();
        fs::write(p1, &saved[1]).unwrap();
        fs::write(p2, &saved[2]).unwrap();
    };
    let rewrite_parts =
        |checker: &mut cargo_anneal::Checker, label: &str, stem: &str, lean_body: &str| {
            let [p0, p1, p2] = part_paths(&stage, stem);
            let [t0, t1, t2] = [
                stage.join(format!("lib/{stem}.tmp.olean")),
                stage.join(format!("lib/{stem}.tmp.olean.server")),
                stage.join(format!("lib/{stem}.tmp.olean.private")),
            ];
            let script = stage.join(format!("Forge_{label}.lean"));
            let src = format!(
                "import Lean\n\
                 open Lean in\n\
                 def main : IO Unit := do\n  \
                   let parts ← readModuleDataParts #[System.FilePath.mk {:?}, \
                     System.FilePath.mk {:?}, System.FilePath.mk {:?}]\n  \
                   let #[(d0, _), (d1, _), (d2, _)] := parts\n    \
                     | throw <| IO.userError \"expected 3 parts\"\n  \
                   {lean_body}\n  \
                   saveModuleDataParts `{stem} #[\n    \
                     (System.FilePath.mk {:?}, d0'),\n    \
                     (System.FilePath.mk {:?}, d1'),\n    \
                     (System.FilePath.mk {:?}, d2')]\n",
                p0.to_string_lossy(),
                p1.to_string_lossy(),
                p2.to_string_lossy(),
                t0.to_string_lossy(),
                t1.to_string_lossy(),
                t2.to_string_lossy(),
            );
            fs::write(&script, src).unwrap();
            checker
                .process(
                    label,
                    &[
                        "-j1".into(),
                        "-M4096".into(),
                        "--run".into(),
                        script.to_string_lossy().into(),
                    ],
                )
                .unwrap();
            fs::rename(&t0, &p0).unwrap();
            fs::rename(&t1, &p1).unwrap();
            fs::rename(&t2, &p2).unwrap();
        };

    let spec_orig = backup_parts("Spec");
    let cap_orig = backup_parts("Captured");
    let model_orig = backup_parts("Model");

    // 2. Alias placed only in `.olean` (part 0) of `Spec`, with `.olean.server`
    //    and `.olean.private` clean.
    rewrite_parts(
        &mut checker,
        "spec_part0_alias",
        "Spec",
        "let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`MySpec.unapprovedAx, `BadAx.unapprovedAx)] : Array (Name × Name))\n  \
         let d0' := { d0 with entries := d0.entries.push (Lean.aliasExtension.name, e) }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 alias: {err}");
    assert!(
        err.message.contains("references unapproved axiom BadAx.unapprovedAx"),
        "spec part0 alias: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!((ta_err.code, ta_err.phase.as_str()), (1, "target-audit"), "ta part0 alias: {ta_err}");
    assert!(
        ta_err.message.contains("references unapproved axiom BadAx.unapprovedAx"),
        "ta part0 alias: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    // 3. Alias placed only in `.olean.server` (part 1) of `Captured`, with
    //    `.olean` and `.olean.private` clean.
    rewrite_parts(
        &mut checker,
        "cap_part1_alias",
        "Captured",
        "let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`Trusted.add, `Nat.add)] : Array (Name × Name))\n  \
         let d0' := d0\n  \
         let d1' := { d1 with entries := d1.entries.push (Lean.aliasExtension.name, e) }\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "cap part1 alias: {err}");
    assert!(
        err.message.contains("cannot export alias Trusted.add in Trusted namespace"),
        "cap part1 alias: {err}"
    );
    restore_parts("Captured", &cap_orig);

    // 4. `@[extern]` override placed only in `.olean` (part 0) of `Captured`.
    rewrite_parts(
        &mut checker,
        "cap_part0_extern",
        "Captured",
        "let ext : ExternAttrData := { entries := [.standard `all \"anneal_part0\"] }\n  \
         let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`Captured.part0Target, ext)] : Array (Name × ExternAttrData))\n  \
         let d0' := { d0 with entries := d0.entries.push (externAttr.ext.name, e) }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let (_, part0_overrides) = checker.inspect_target_consts(&roles, &is_module).unwrap();
    assert!(
        part0_overrides.contains("Captured.part0Target"),
        "missing part-0 @[extern] override: {part0_overrides:?}"
    );
    restore_parts("Captured", &cap_orig);

    // 5a. Duplicate `Lean.aliasExtension` entries in `.olean.private`: earlier
    //     unapproved axiom entry shadowed by a trailing empty `#[]` pair.
    rewrite_parts(
        &mut checker,
        "spec_dup_alias",
        "Spec",
        "let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`MySpec.dupAx, `BadAx.unapprovedAx)] : Array (Name × Name))\n  \
         let ents := (d2.entries.push (Lean.aliasExtension.name, e)).push \
           (Lean.aliasExtension.name, #[])\n  \
         let d0' := d0\n  \
         let d1' := d1\n  \
         let d2' := { d2 with entries := ents }",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec dup alias: {err}");
    assert!(
        err.message.contains("references unapproved axiom BadAx.unapprovedAx"),
        "spec dup alias: {err}"
    );
    restore_parts("Spec", &spec_orig);

    // 5b. Duplicate `externAttr` entries in `.olean.private` of `Captured`
    //     shadowed by a trailing empty `#[]` pair.
    rewrite_parts(
        &mut checker,
        "cap_dup_extern",
        "Captured",
        "let ext : ExternAttrData := { entries := [.standard `all \"anneal_dup\"] }\n  \
         let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`Captured.dupTarget, ext)] : Array (Name × ExternAttrData))\n  \
         let ents := (d2.entries.push (externAttr.ext.name, e)).push \
           (externAttr.ext.name, #[])\n  \
         let d0' := d0\n  \
         let d1' := d1\n  \
         let d2' := { d2 with entries := ents }",
    );
    let (_, dup_overrides) = checker.inspect_target_consts(&roles, &is_module).unwrap();
    assert!(
        dup_overrides.contains("Captured.dupTarget"),
        "missing earlier duplicate @[extern] override: {dup_overrides:?}"
    );
    restore_parts("Captured", &cap_orig);

    // 5c. Specification alias targeting a `Model` declaration whose `@[extern]`
    //     lives in `.olean` (part 0) behind a trailing duplicate empty pair.
    rewrite_parts(
        &mut checker,
        "model_part0_dup_extern",
        "Model",
        "let ext : ExternAttrData := { entries := [.standard `all \"anneal_model_ext\"] }\n  \
         let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`Model.extFn, ext)] : Array (Name × ExternAttrData))\n  \
         let ents := (d0.entries.push (externAttr.ext.name, e)).push \
           (externAttr.ext.name, #[])\n  \
         let d0' := { d0 with entries := ents }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    rewrite_parts(
        &mut checker,
        "spec_part0_model_ext_alias",
        "Spec",
        "let e : Array EnvExtensionEntry := unsafe unsafeCast \
           (#[(`MySpec.extFn, `Model.extFn)] : Array (Name × Name))\n  \
         let d0' := { d0 with entries := d0.entries.push (Lean.aliasExtension.name, e) }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec alias to part0 dup extern: {err}");
    assert!(
        err.message.contains("references compiler override declaration Model.extFn"),
        "spec alias to part0 dup extern: {err}"
    );
    restore_parts("Spec", &spec_orig);
    restore_parts("Model", &model_orig);

    // 6a. Extra constant injected only into `.olean` (part 0) of `Spec`,
    //     absent from `.olean.private`, rejected by both `"target-consts"` and
    //     pinned `"target-audit"`.
    rewrite_parts(
        &mut checker,
        "spec_part0_extra_const",
        "Spec",
        "let extra : ConstantInfo := .defnInfo { name := `Spec.ghost, levelParams := [], \
           type := .const `Nat [], value := .lit (.natVal 0), hints := .abbrev, \
           safety := .safe, all := [`Spec.ghost] }\n  \
         let cn := d0.constNames.push `Spec.ghost\n  \
         let cs := d0.constants.push extra\n  \
         let d0' := { d0 with constNames := cn, constants := cs }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 extra const: {err}");
    assert!(
        err.message.contains("target companion constant Spec.ghost missing from private inventory"),
        "spec part0 extra const: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part0 extra const: {ta_err}"
    );
    assert!(
        ta_err.message.contains("target companion constant Spec.ghost missing from private inventory"),
        "ta part0 extra const: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    // 6b. `unsafe` constant injected only into `.olean` (part 0) of `Spec`,
    //     rejected by both `"target-consts"` and pinned `"target-audit"`.
    rewrite_parts(
        &mut checker,
        "spec_part0_unsafe_const",
        "Spec",
        "let bad : ConstantInfo := .defnInfo { name := `Spec.evilPart0, levelParams := [], \
           type := .const `Nat [], value := .lit (.natVal 0), hints := .abbrev, \
           safety := .unsafe, all := [`Spec.evilPart0] }\n  \
         let cn := d0.constNames.push `Spec.evilPart0\n  \
         let cs := d0.constants.push bad\n  \
         let d0' := { d0 with constNames := cn, constants := cs }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 unsafe const: {err}");
    assert!(
        err.message.contains("declares unsafe constant Spec.evilPart0"),
        "spec part0 unsafe const: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part0 unsafe const: {ta_err}"
    );
    assert!(
        ta_err.message.contains("declares unsafe constant Spec.evilPart0"),
        "ta part0 unsafe const: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    // 6b-2. Forged `.axiomInfo { isUnsafe := true }` in `.olean` (part 0) for
    //       a safe non-`partial` `.defnInfo` (`Spec.specs`) in `.olean.private`
    //       is still rejected as unsafe by both `"target-consts"` and pinned
    //       `"target-audit"`.
    rewrite_parts(
        &mut checker,
        "spec_part0_unsafe_axiom_for_safe_def",
        "Spec",
        "let cs := d0.constants.map fun ci =>\n  \
           if ci.name == `Spec.specs then\n    \
             .axiomInfo { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := true }\n  \
           else ci\n  \
         let d0' := { d0 with constants := cs }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 unsafe axiom for safe def: {err}");
    assert!(
        err.message.contains("declares unsafe constant Spec.specs"),
        "spec part0 unsafe axiom for safe def: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part0 unsafe axiom for safe def: {ta_err}"
    );
    assert!(
        ta_err.message.contains("declares unsafe constant Spec.specs"),
        "ta part0 unsafe axiom for safe def: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    // 6c. Mismatched `constNames` in `.olean` (part 0) of `Spec`, rejected by
    //     both `"target-consts"` and pinned `"target-audit"`.
    rewrite_parts(
        &mut checker,
        "spec_part0_bad_const_names",
        "Spec",
        "let cn := d0.constNames.push `Spec.bogusKey\n  \
         let d0' := { d0 with constNames := cn }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 bad constNames: {err}");
    assert!(
        err.message.contains("invalid target inventory Spec"),
        "spec part0 bad constNames: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part0 bad constNames: {ta_err}"
    );
    assert!(
        ta_err.message.contains("invalid target inventory Spec"),
        "ta part0 bad constNames: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    // 7. Companion `.olean.server` `isModule = false` mismatch.
    rewrite_parts(
        &mut checker,
        "spec_part1_is_module_mismatch",
        "Spec",
        "let d0' := d0\n  \
         let d1' := { d1 with isModule := false }\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part1 isModule mismatch: {err}");
    assert!(
        err.message.contains("mismatched olean companion isModule flag in Spec"),
        "spec part1 isModule mismatch: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part1 isModule mismatch: {ta_err}"
    );
    assert!(
        ta_err.message.contains("mismatched olean companion isModule flag in Spec"),
        "ta part1 isModule mismatch: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    // 8. Companion `.olean` constant payload mismatch (`Spec.specs` body
    //    mutated in part 0 while `.olean.private` stays intact), companion
    //    `imports` mismatch, `_root_`-prefixed alias keys, `Specification`
    //    forbidden alias names (`optParam`, `Anneal.bad`), and alias role-edge
    //    violation (`Spec` -> `Captured.program`) — all rejected on both
    //    `"target-consts"` and pinned `"target-audit"`.
    rewrite_parts(
        &mut checker,
        "spec_part0_const_payload_mismatch",
        "Spec",
        "let cs := d0.constants.map fun ci =>\n    \
           if ci.name == `Spec.specs then\n      \
             match ci with\n      \
             | .defnInfo dv => .defnInfo { dv with value := .const `Nat.zero [] }\n      \
             | other => other\n    \
           else ci\n  \
         let d0' := { d0 with constants := cs }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 payload mismatch: {err}");
    assert!(
        err.message.contains("mismatched target companion constant Spec.specs in Spec"),
        "spec part0 payload mismatch: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part0 payload mismatch: {ta_err}"
    );
    assert!(
        ta_err.message.contains("mismatched target companion constant Spec.specs in Spec"),
        "ta part0 payload mismatch: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    rewrite_parts(
        &mut checker,
        "spec_part0_imports_mismatch",
        "Spec",
        "let d0' := { d0 with imports := #[] }\n  \
         let d1' := d1\n  \
         let d2' := d2",
    );
    let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
    assert_eq!(err.code, 1, "spec part0 imports mismatch: {err}");
    assert!(
        err.message.contains("mismatched target companion imports in Spec"),
        "spec part0 imports mismatch: {err}"
    );
    let ta_err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(
        (ta_err.code, ta_err.phase.as_str()),
        (1, "target-audit"),
        "ta part0 imports mismatch: {ta_err}"
    );
    assert!(
        ta_err.message.contains("mismatched target companion imports in Spec"),
        "ta part0 imports mismatch: {ta_err}"
    );
    restore_parts("Spec", &spec_orig);

    for (label, stem, alias_pair, expected_sub) in [
        (
            "cap_root_prefixed_trusted_alias",
            "Captured",
            "(`_root_.Trusted.spoof, `Nat.add)",
            "cannot export alias _root_.Trusted.spoof in Trusted namespace",
        ),
        (
            "spec_root_prefixed_expected_alias",
            "Spec",
            "(`_root_.Expected.claim, `Nat.add)",
            "cannot export alias _root_.Expected.claim in reserved kernel namespace Expected",
        ),
        (
            "spec_alias_opt_param",
            "Spec",
            "(`optParam, `Nat.add)",
            "specification module Spec cannot export alias optParam",
        ),
        (
            "spec_alias_anneal_root",
            "Spec",
            "(`Anneal.spoof, `Nat.add)",
            "specification module Spec cannot export alias Anneal.spoof",
        ),
        (
            "spec_alias_role_edge_capture",
            "Spec",
            "(`MySpec.capRef, `Captured.program)",
            "authority violation",
        ),
    ] {
        rewrite_parts(
            &mut checker,
            label,
            stem,
            &format!(
                "let e : Array EnvExtensionEntry := unsafe unsafeCast \
                   (#[{alias_pair}] : Array (Name × Name))\n  \
                 let d0' := {{ d0 with entries := d0.entries.push (Lean.aliasExtension.name, e) }}\n  \
                 let d1' := d1\n  \
                 let d2' := d2"
            ),
        );
        let err = checker.inspect_target_consts(&roles, &is_module).unwrap_err();
        assert_eq!(err.code, 1, "tc {label}: {err}");
        assert!(err.message.contains(expected_sub), "tc {label}: {err}");
        let ta_err = checker.inspect_target(&f.request).unwrap_err();
        assert_eq!(
            (ta_err.code, ta_err.phase.as_str()),
            (1, "target-audit"),
            "ta {label}: {ta_err}"
        );
        assert!(ta_err.message.contains(expected_sub), "ta {label}: {ta_err}");
        if stem == "Captured" {
            restore_parts("Captured", &cap_orig);
        } else {
            restore_parts("Spec", &spec_orig);
        }
    }
}

/// `SpecPreflight.isPairedUnsafeRec` classifies a `partial` `p._unsafe_rec`
/// auxiliary as paired only when `p` is a safe total `.defnInfo` in the same
/// module and both `type` and `levelParams` match (`sameUnsafeRecHeader`), so
/// forged type- or universe-mismatched auxiliaries stay in the checked
/// specification inventory rather than being excluded by the comparator.
#[test]
fn spec_preflight_paired_unsafe_rec_checks_header_parity() {
    let f = Fixture::new(
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let (roles, is_module) = with_spec_preflight(&f);
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    checker.run_target(&f.request).unwrap();

    let spec_olean = checker.stage().join("lib/Spec.olean");
    let script = checker.stage().join("ForgeSpecPreflightUnsafeRec.lean");
    fs::write(
        &script,
        format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let mkDef (n : Name) (lvls : List Name) (ty val : Expr) \
                 (safety : DefinitionSafety) : ConstantInfo := .defnInfo {{\n    \
                 name := n, levelParams := lvls, type := ty, value := val,\n    \
                 hints := .abbrev, safety := safety, all := [n] }}\n  \
               let good := mkDef `Spec.good [] (.const `Nat []) (.lit (.natVal 0)) .safe\n  \
               let goodRec := mkDef `Spec.good._unsafe_rec [] \
                 (.const `Nat []) (.lit (.natVal 1)) .partial\n  \
               let badType := mkDef `Spec.badType [] (.const `Nat []) (.lit (.natVal 0)) .safe\n  \
               let badTypeRec := mkDef `Spec.badType._unsafe_rec [] \
                 (.const `Bool []) (.const `Bool.true []) .partial\n  \
               let badUniv := mkDef `Spec.badUniv [`u] (.const `Nat []) (.lit (.natVal 0)) .safe\n  \
               let badUnivRec := mkDef `Spec.badUniv._unsafe_rec [`u, `v] \
                 (.const `Nat []) (.lit (.natVal 0)) .partial\n  \
               let added := #[good, goodRec, badType, badTypeRec, badUniv, badUnivRec]\n  \
               saveModuleData p `Spec {{ data with\n    \
                 constNames := data.constNames ++ added.map ConstantInfo.name,\n    \
                 constants := data.constants ++ added }}\n",
            spec_olean.to_string_lossy()
        ),
    )
    .unwrap();
    checker
        .process(
            "forge-spec-preflight-unsafe-rec",
            &["-j1".into(), "-M4096".into(), "--run".into(), script.to_string_lossy().into()],
        )
        .unwrap();
    let (origins, _) = checker.inspect_target_consts(&roles, &is_module).unwrap();
    assert_eq!(origins.get("Spec.good._unsafe_rec").map(|(m, p)| (m.as_str(), *p)), Some(("Spec", true)));
    assert_eq!(
        origins.get("Spec.badType._unsafe_rec").map(|(m, p)| (m.as_str(), *p)),
        Some(("Spec", false)),
        "type-mismatched p._unsafe_rec must not be paired: {origins:?}"
    );
    assert_eq!(
        origins.get("Spec.badUniv._unsafe_rec").map(|(m, p)| (m.as_str(), *p)),
        Some(("Spec", false)),
        "levelParams-mismatched p._unsafe_rec must not be paired: {origins:?}"
    );
}
