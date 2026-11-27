// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `.olean` companion handling and `module`-mode targets.

use super::*;

/// Craft header-chained 88-byte synthetic `.olean.server` and `.olean.private`
/// companions for `primary_path` under `stage_dir/lib/{stem}.olean.*`. The
/// companions satisfy the v2 header prefix and 64 KiB base-address chaining
/// checks in `validateTargetArtifactPreImport`, but abort inside
/// `CompactedRegion.read` (exit code 2) if `importEnv` mmaps them without a
/// pre-import policy rejection.
fn craft_chained_olean_companions(
    stage_dir: &Path,
    primary_path: &str,
    stem: &str,
) -> (String, String) {
    let raw = fs::read(primary_path).unwrap();
    assert!(raw.len() >= 88);
    let base0 = u64::from_le_bytes(raw[80..88].try_into().unwrap());
    let align64k = |n: u64| (n + 0xffff) & !0xffff;
    let base1 = align64k(base0 + raw.len() as u64);
    let mut srv = Vec::with_capacity(88);
    srv.extend_from_slice(&raw[..80]);
    srv.extend_from_slice(&base1.to_le_bytes());
    let base2 = align64k(base1 + srv.len() as u64);
    let mut prv = Vec::with_capacity(88);
    prv.extend_from_slice(&raw[..80]);
    prv.extend_from_slice(&base2.to_le_bytes());
    let srv_path = stage_dir.join(format!("lib/{stem}.olean.server"));
    let prv_path = stage_dir.join(format!("lib/{stem}.olean.private"));
    fs::write(&srv_path, srv).unwrap();
    fs::write(&prv_path, prv).unwrap();
    (
        srv_path.to_string_lossy().into_owned(),
        prv_path.to_string_lossy().into_owned(),
    )
}

/// `"target-export"` and `"target-audit"` must validate `.olean*` companion
/// headers, 64 KiB base-address chaining, and primary-part `isModule` policy
/// *before* `importEnv` mmaps `.olean.server` / `.olean.private` regions:
/// - swapped `.olean.server` or `.olean.private` on `Trusted.*` (`Model`) or
///   `Anneal.*` (`Proof`) fails closed with a policy error (zero `SIGSEGV`);
/// - non-`module` `Trusted.*` or `Anneal.*` paired with companion parts (even
///   with matching header prefix and chained 64 KiB base addresses) fails
///   closed with `"companion artifact parts unsupported"` before `importEnv`.
#[test]
fn target_export_and_audit_reject_swapped_companions_and_non_module_bundled_companions() {
    use anneal_audit::ModuleArtifacts;
    use std::collections::BTreeMap;

    let mut f = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         import Anneal.HelperA\nimport Anneal.HelperB\nimport Anneal.NonMod\n\
         theorem Proof.verify : Expected.claim :=\n\
         (fun _ _ _ => And.intro rfl BitVec.and_self) Anneal.HelperA.ok Anneal.HelperB.ok Anneal.NonMod.ok\n",
    );
    f.request.modules.retain(|m| m.module != "Model");
    f.set(
        "Trusted.ModA",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
         @[expose] public section\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\n\
         end\n",
    );
    f.set(
        "Trusted.ModB",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Core\n\
         @[expose] public section\n\
         def Trusted.ModB.val : Nat := 99\n\
         end\n",
    );
    f.set(
        "Trusted.NonMod",
        TargetRole::Model,
        "prelude\nimport Init.Core\ndef Trusted.NonMod.val : Nat := 1\n",
    );
    f.set(
        "Anneal.HelperA",
        TargetRole::Proof,
        "module\nprelude\npublic import Init.Core\n\
         public section\ntheorem Anneal.HelperA.ok : True := True.intro\nend\n",
    );
    f.set(
        "Anneal.HelperB",
        TargetRole::Proof,
        "module\nprelude\npublic import Init.Core\n\
         public section\ntheorem Anneal.HelperB.ok : True := True.intro\nend\n",
    );
    f.set(
        "Anneal.NonMod",
        TargetRole::Proof,
        "prelude\nimport Init.Core\ntheorem Anneal.NonMod.ok : True := True.intro\n",
    );
    f.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Trusted.ModA\nimport Trusted.ModB\nimport Trusted.NonMod\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Trusted.ModA\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );

    let mut checker = f.cargo_checker();
    let baseline = checker.run_target(&f.request).unwrap();
    assert_eq!(baseline["replay"], true);
    assert_eq!(baseline["exactType"], true);

    let orig_artifacts = checker.admitted().unwrap().artifacts.clone();
    let get_parts = |name: &str| -> Vec<String> {
        orig_artifacts
            .get(name)
            .unwrap_or_else(|| panic!("missing artifacts for {name}"))
            .olean_parts
            .clone()
    };

    let mod_a = get_parts("Trusted.ModA");
    let mod_b = get_parts("Trusted.ModB");
    let helper_a = get_parts("Anneal.HelperA");
    let helper_b = get_parts("Anneal.HelperB");
    assert_eq!(mod_a.len(), 3, "expected 3-part module for Trusted.ModA");
    assert_eq!(mod_b.len(), 3, "expected 3-part module for Trusted.ModB");
    assert_eq!(helper_a.len(), 3, "expected 3-part module for Anneal.HelperA");
    assert_eq!(helper_b.len(), 3, "expected 3-part module for Anneal.HelperB");

    let build_arts = |p0: &str, p1: &str, p2: &str| -> ModuleArtifacts {
        let mut avail = BTreeMap::new();
        avail.insert("olean", p0.to_owned());
        avail.insert("olean.server", p1.to_owned());
        avail.insert("olean.private", p2.to_owned());
        ModuleArtifacts::from_available(&avail, "fixture", || "missing".into()).unwrap()
    };

    // 1. Swapped `.olean.server` on `Trusted.ModA` (Model) fails closed before
    //    `importEnv` without SIGSEGV.
    checker.admitted_mut().unwrap().artifacts = orig_artifacts.clone();
    checker
        .admitted_mut()
        .unwrap()
        .artifacts
        .insert("Trusted.ModA".into(), build_arts(&mod_a[0], &mod_b[1], &mod_a[2]));
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert!(
        err.message
            .contains("mismatched olean companion base address in Trusted.ModA"),
        "{err}"
    );

    // 2. Swapped `.olean.server` on `Anneal.HelperA` (Proof) fails closed in
    //    `"target-export"`.
    checker.admitted_mut().unwrap().artifacts = orig_artifacts.clone();
    checker.admitted_mut().unwrap().artifacts.insert(
        "Anneal.HelperA".into(),
        build_arts(&helper_a[0], &helper_b[1], &helper_a[2]),
    );
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "target-audit", "{err}");
    assert!(
        err.message
            .contains("mismatched olean companion base address in Anneal.HelperA"),
        "{err}"
    );

    // 3. Swapped `.olean.private` on `Anneal.HelperA` (Proof) fails closed in
    //    `"target-export"` without SIGSEGV.
    checker.admitted_mut().unwrap().artifacts = orig_artifacts.clone();
    checker.admitted_mut().unwrap().artifacts.insert(
        "Anneal.HelperA".into(),
        build_arts(&helper_a[0], &helper_a[1], &helper_b[2]),
    );
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "target-audit", "{err}");
    assert!(
        err.message
            .contains("mismatched olean companion base address in Anneal.HelperA"),
        "{err}"
    );

    let stage_dir = checker.stage().to_path_buf();

    // 4. Non-`module` `Trusted.NonMod` (`Model`, `expectedIsModule = false`)
    //    paired with header-chained 3-part companions fails closed pre-import
    //    on part count (`validateTargetArtifactParts`) before `importEnv`.
    let non_mod_model = get_parts("Trusted.NonMod");
    let (nm_srv, nm_prv) =
        craft_chained_olean_companions(&stage_dir, &non_mod_model[0], "Trusted/NonMod");
    checker.admitted_mut().unwrap().artifacts = orig_artifacts.clone();
    checker.admitted_mut().unwrap().artifacts.insert(
        "Trusted.NonMod".into(),
        build_arts(&non_mod_model[0], &nm_srv, &nm_prv),
    );
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert!(
        err.message
            .contains("companion artifact parts unsupported in Trusted.NonMod"),
        "{err}"
    );

    // 5. Non-`module` `Anneal.NonMod` (`Proof`, `expectedIsModule = false`)
    //    paired with header-chained 3-part companions fails closed pre-import
    //    in `"target-export"` on part count before `importEnv`.
    let non_mod_proof = get_parts("Anneal.NonMod");
    let (ap_srv, ap_prv) =
        craft_chained_olean_companions(&stage_dir, &non_mod_proof[0], "Anneal/NonMod");
    checker.admitted_mut().unwrap().artifacts = orig_artifacts;
    checker.admitted_mut().unwrap().artifacts.insert(
        "Anneal.NonMod".into(),
        build_arts(&non_mod_proof[0], &ap_srv, &ap_prv),
    );
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "target-audit", "{err}");
    assert!(
        err.message
            .contains("companion artifact parts unsupported in Anneal.NonMod"),
        "{err}"
    );
}

/// Lean 4 `module`-mode target units (`Model`, `Capture`, `Specification`,
/// `Expected`, and authored `Proof`) pass end-to-end verification, enforce
/// boundary invariants, and maintain legacy non-`module` interoperability:
/// - full `module`-mode pipeline compiles and audits with 3-part `.olean*`;
/// - legacy non-`module` `Spec` + `Expected` + `Proof` compose cleanly with
///   `module`-mode `Model` + `Captured`;
/// - `import all` in `Proof` (`module` mode) is rejected by `"headers"`;
/// - private `import Proof` in `Spec` (`module` mode) fails closed;
/// - omitting `public` on `Proof.verify` in `module` mode fails
///   `"target-audit"`;
/// - forged `isModule = false` `.olean` on a `module` target fails pre-import
///   `"target-audit"` when `"isModule"` expectation is `true`; and
/// - raw `"target-export"` / `"target-audit"` requests omitting `"isModule"`
///   fail closed;
/// - a `module` Proof regenerating an identical lazy equation helper
///   (`Option.map.eq_1`) passes `"target-audit"`; and
/// - duplicate non-helper declarations across Proof modules (`Shared.dup`)
///   fail closed in `"target-audit"` (forged helper copies are covered in
///   `headers_rejects_module_system_modifiers_and_lean_lake_and_allows_no_prelude`).
#[test]
fn module_mode_targets_verify_and_enforce_boundary_invariants() {
    use std::collections::BTreeMap;

    use anneal_audit::ModuleArtifacts;

    let make_module_fixture = |spec_src: &str, proof_src: &str| -> Fixture {
        let mut f = Fixture::new(proof_src);
        f.set(
            "Model",
            TargetRole::Model,
            "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
             @[expose] public section\n\
             namespace Trusted.MirSemantics\n\
             structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
             def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
             end Trusted.MirSemantics\nend\n",
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            "module\nprelude\npublic import Model\n\
             @[expose] public section\n\
             def Captured.program : BitVec 8 := BitVec.ofNat 8 7\nend\n",
        );
        f.set("Spec", TargetRole::Specification, spec_src);
        f.set(
            "Expected",
            TargetRole::Expected,
            "module\nprelude\npublic import Model\npublic import Captured\npublic import Spec\n\
             @[expose] public section\n\
             def Expected.claim : Prop :=\n\
               Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
             end\n",
        );
        f
    };

    let clean_spec = "module\nprelude\npublic import Model\n\
        @[expose] public section\n\
        def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n\
        end\n";
    let clean_proof = "module\nprelude\npublic import Expected\n\
        import Init.Data.BitVec.Lemmas\n\
        private theorem helper_ok : BitVec.and (BitVec.ofNat 8 7) (BitVec.ofNat 8 7) = BitVec.ofNat 8 7 := by exact BitVec.and_self\n\
        public theorem Proof.verify : Expected.claim := And.intro rfl helper_ok\n";

    // 1. Full `module`-mode pipeline compiles and passes `"target-audit"`.
    let mod_f = make_module_fixture(clean_spec, clean_proof);
    let mut checker = mod_f.cargo_checker();
    let report = checker.run_target(&mod_f.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(report["sorryDeclarations"], serde_json::json!([]));
    for name in ["Model", "Captured", "Spec", "Expected", "Proof"] {
        let arts = &checker.admitted().unwrap().artifacts[name];
        assert!(
            arts.olean_parts.len() == 3
                && arts.olean_parts[1].ends_with(".olean.server")
                && arts.olean_parts[2].ends_with(".olean.private"),
            "expected 3-part module artifacts for {name}, got {:?}",
            arts.olean_parts
        );
    }

    // 2. Mixed backward compatibility: `module` Model and Captured with
    //    non-`module` Spec, Expected, and Proof pass cleanly.
    let mut mixed_f = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    mixed_f.set(
        "Model",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
         @[expose] public section\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\nend\n",
    );
    mixed_f.set(
        "Captured",
        TargetRole::Capture,
        "module\nprelude\npublic import Model\n\
         @[expose] public section\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\nend\n",
    );
    let mixed_report = mixed_f.run().unwrap();
    assert_eq!(mixed_report["replay"], true);
    assert_eq!(mixed_report["exactType"], true);

    // 3. `Proof` (`module`) using `import all` is rejected in `"headers"`.
    let bad_proof_all = make_module_fixture(
        clean_spec,
        "module\nprelude\nimport all Expected\n\
         public theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let err = bad_proof_all.run().unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "headers"), "{err}");
    assert!(err.message.contains("import modifiers"), "{err}");

    // 4. `Spec` (`module`) importing a `Proof` module (`Helper`) privately
    //    is rejected fail-closed without relying on cycle detection.
    let mut bad_spec_imp_proof = make_module_fixture(
        "module\nprelude\npublic import Model\nimport Helper\n\
         @[expose] public section\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\nend\n",
        clean_proof,
    );
    bad_spec_imp_proof.set(
        "Helper",
        TargetRole::Proof,
        "module\nprelude\npublic import Init.Core\npublic theorem Helper.ok : True := True.intro\n",
    );
    let err = bad_spec_imp_proof.run().unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-role"), "{err}");
    assert!(err.message.contains("Spec cannot import Helper"), "{err}");

    // 5. Omitting `public` on `Proof.verify` in `module` mode fails
    //    `"target-audit"`.
    let private_verify_proof = make_module_fixture(
        clean_spec,
        "module\nprelude\npublic import Expected\n\
         import Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let err = private_verify_proof.run().unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(err.message.contains("missing target dependency Proof.verify"), "{err}");

    // 6. Forged `isModule = false` `.olean` when `"isModule": true` is expected
    //    fails pre-import `"target-audit"` with
    //    `"non-module artifact mismatch"`.
    //    6a pairs the forged non-module `Spec.olean` with header-chained
    //    88-byte synthetic `.olean.server` & `.olean.private` companions so
    //    disabling the pre-import `expected && !actual` check in
    //    `validateTargetArtifactPreImport` either falls through to part-count
    //    rejection or aborts in `CompactedRegion.read` (exit code 2) rather
    //    than matching the post-import message; 6b also checks the 1-part case.
    let mut forged_checker = mod_f.cargo_checker();
    forged_checker.run_target(&mod_f.request).unwrap();
    let nonmod_spec_src = "prelude\nimport Model\n\
        def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    let nonmod_spec_path = forged_checker.stage().join("NonModSpec.lean");
    fs::write(&nonmod_spec_path, nonmod_spec_src).unwrap();
    let hdr_json =
        forged_checker.inspect_headers(&[("Spec".into(), nonmod_spec_path.clone())]).unwrap();
    let hdrs: cargo_anneal::PreflightResult = serde_json::from_value(hdr_json).unwrap();
    forged_checker
        .compile_lean_module(
            "Spec",
            &nonmod_spec_path,
            hdrs.headers[0].imports.clone(),
            false,
            "lib",
            false,
            true,
        )
        .unwrap();
    let nonmod_olean = forged_checker
        .stage()
        .join("lib/Spec.olean")
        .to_string_lossy()
        .into_owned();
    let (forged_srv, forged_prv) =
        craft_chained_olean_companions(forged_checker.stage(), &nonmod_olean, "NonModSpec");
    let mut nonmod_chained = BTreeMap::new();
    nonmod_chained.insert("olean", nonmod_olean.clone());
    nonmod_chained.insert("olean.server", forged_srv);
    nonmod_chained.insert("olean.private", forged_prv);
    forged_checker.admitted_mut().unwrap().artifacts.insert(
        "Spec".into(),
        ModuleArtifacts::from_available(&nonmod_chained, "fixture", || "missing".into()).unwrap(),
    );
    let err = forged_checker.inspect_target(&mod_f.request).unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(err.message.contains("non-module artifact mismatch in Spec"), "{err}");

    let mut nonmod_avail = BTreeMap::new();
    nonmod_avail.insert("olean", nonmod_olean);
    forged_checker.admitted_mut().unwrap().artifacts.insert(
        "Spec".into(),
        ModuleArtifacts::from_available(&nonmod_avail, "fixture", || "missing".into()).unwrap(),
    );
    let err = forged_checker.inspect_target(&mod_f.request).unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(err.message.contains("non-module artifact mismatch in Spec"), "{err}");

    // 7. Missing `"isModule"` expectation on raw `"target-export"` request
    //    fails closed.
    let mut raw_modes = BTreeMap::new();
    for m in &mod_f.request.modules {
        if m.module != "Spec" {
            raw_modes.insert(m.module.clone(), true);
        }
    }
    let err = checker.inspect_target_with_modes(&mod_f.request, &raw_modes).unwrap_err();
    assert_eq!(err.phase, "target-audit", "{err}");
    assert!(err.message.contains("missing isModule expectation for Spec"), "{err}");

    // 8. A `module` Proof that regenerates an identical lazy equation helper
    //    passes `"target-audit"`: `Model` privately imports
    //    `Init.Control.Lawful.Instances`, so `Option.map.eq_1` is already
    //    admitted, while `Proof` imports only `Init.Data.Option.Lemmas` and
    //    regenerates `Option.map.eq_1`.
    let opt_proof = "module\nprelude\npublic import Expected\n\
        import Init.Data.BitVec.Lemmas\nimport Init.Data.Option.Lemmas\n\
        private theorem opt_eq : Option.map Nat.succ (some 1) = some 2 := by simp [Option.map]\n\
        private theorem bv_ok : BitVec.and (BitVec.ofNat 8 7) (BitVec.ofNat 8 7) = BitVec.ofNat 8 7 := by exact BitVec.and_self\n\
        public theorem Proof.verify : Expected.claim := (fun _ => And.intro rfl bv_ok) opt_eq\n";
    let mut opt_f = make_module_fixture(clean_spec, opt_proof);
    opt_f.set(
        "Model",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Data.BitVec.Basic\nimport Init.Control.Lawful.Instances\n\
         @[expose] public section\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\nend\n",
    );
    let opt_report = opt_f.run().unwrap();
    assert_eq!(opt_report["replay"], true);
    assert_eq!(opt_report["exactType"], true);

    // 9. Non-helper duplicate public declarations (`HelperB` privately imported
    //    by `HelperA` vs `Proof`) still fail closed before `"target-audit"`
    //    returns a verdict (direct `"target-audit"` forged-export deduplication
    //    is pinned by `forged_dup_export` in `headers_rejects_...`).
    let mut dup_nonhelper = make_module_fixture(
        clean_spec,
        "module\nprelude\npublic import Expected\nimport HelperA\n\
         import Init.Data.BitVec.Lemmas\n\
         public def Shared.dup : Nat := 2\n\
         public theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    dup_nonhelper.set(
        "HelperB",
        TargetRole::Proof,
        "module\nprelude\npublic import Init.Core\npublic def Shared.dup : Nat := 1\n",
    );
    dup_nonhelper.set(
        "HelperA",
        TargetRole::Proof,
        "module\nprelude\npublic import Init.Core\nimport HelperB\n",
    );
    let err = dup_nonhelper.run().unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (2, "target-audit"), "{err}");
    assert!(err.message.contains("already contains 'Shared.dup'"), "{err}");

    // 10. Private imports between `module` targets pass `"target-export"` and
    //     `"target-audit"`: `Spec` privately imports a `module` `SpecHelper`,
    //     and `Proof` privately imports a `module` `ExpectedClean`. Neither
    //     helper is imported publicly anywhere, so a `level := .server`
    //     re-import rooted at `Proof` or `Spec` would need their missing `.ir`.
    let mut private_imports = make_module_fixture(
        "module\nprelude\npublic import Model\nimport SpecHelper\n\
         @[expose] public section\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n\
         end\n",
        "module\nprelude\npublic import Expected\n\
         import ExpectedClean\nimport Init.Data.BitVec.Lemmas\n\
         public theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    private_imports.set(
        "SpecHelper",
        TargetRole::Specification,
        "module\nprelude\npublic import Model\n\
         public def SpecHelper.same (p : BitVec 8) : BitVec 8 := p\n",
    );
    private_imports.set(
        "ExpectedClean",
        TargetRole::Expected,
        "module\nprelude\npublic import Init.Core\n\
         public theorem ExpectedClean.ok : True := True.intro\n",
    );
    let private_report = private_imports.run().unwrap();
    assert_eq!(private_report["replay"], true);
    assert_eq!(private_report["exactType"], true);
}
