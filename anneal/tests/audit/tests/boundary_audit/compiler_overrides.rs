// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Repository and proof compiler override entries.

use super::*;

/// Verifies that compiled repository `.olean` checks in Pass 1 `"audit"`,
/// Pass 2 `"correspondence-audit"`, and `"target-export"` <-> `"target-audit"`
/// fail closed on authored compiler overrides (`@[implemented_by]`,
/// `@[extern]`, `@[csimp]`, `@[export]`, `@[init]`, `@[builtin_init]`,
/// `@[cpass]`, `ConstantFold.folderExt`, and `postponedCompileDeclsExt`),
/// including `module`-mode `.olean.private`, `.olean` (`.exported`), and
/// `.olean.server` companion parts.
#[test]
fn rejects_repo_and_proof_compiler_override_entries() {
    #[cfg(unix)]
    use std::os::unix::fs::PermissionsExt;

    use anneal_audit::{TargetAuditRequest, TargetBindings, TargetModule, TargetRole};

    let checkout = repo_root();
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let theory_lib = stage.join("theory-lib");
    let src_dir = stage.join("src/override-neg");
    fs::create_dir_all(&theory_lib).unwrap();

    // 1. Pass 1 `"audit"`: forged `.repo .theory` modules bypassing preflight
    //    with `@[implemented_by]`, `@[export]`, `@[extern]`, `@[csimp]`, or
    //    `postponedCompileDeclsExt`.
    for (module, body, expected) in [
        (
            "Anneal.BadImplBy",
            "prelude\nimport Init.Core\ndef goodImpl (n : Nat) : Nat := n + 1\n\
             @[implemented_by goodImpl] def badImpl (n : Nat) : Nat := n\n",
            "unchecked compiler implemented_by override on badImpl in Anneal.BadImplBy",
        ),
        (
            "Anneal.BadExport",
            "prelude\nimport Init.Core\n@[export anneal_repo_export] def badExport (n : Nat) : Nat := n\n",
            "unchecked compiler export override on badExport in Anneal.BadExport",
        ),
        (
            "Anneal.BadExtern",
            "prelude\nimport Init.Core\n@[extern \"anneal_repo_extern\"] def badExtern (n : Nat) : Nat := n\n",
            "unchecked compiler extern override on badExtern in Anneal.BadExtern",
        ),
        (
            "Anneal.BadCsimp",
            "prelude\nimport Init.Core\ndef slow (n : Nat) : Nat := n\ndef fast (n : Nat) : Nat := n\n\
             @[csimp] theorem eq_sf : @slow = @fast := rfl\n",
            "authored compiler csimp replacement on slow in Anneal.BadCsimp",
        ),
    ] {
        compile_forged_module(&mut checker, &src_dir, &theory_lib, &[], module, body);
        let err = checker
            .inspect(InspectorRequest::Audit {
                trusted: vec!["Trusted".to_string()],
                theory: vec![module.to_string()],
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "audit"), "{module}: {err}");
        assert!(err.message.contains(expected), "{module}: {err}");
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove(module);
        adm.graph.remove(module);
    }

    let postponed_olean = theory_lib.join("Anneal/BadPostponed.olean");
    fs::create_dir_all(postponed_olean.parent().unwrap()).unwrap();
    let lean_prefix = checker.admitted().unwrap().prefix.clone();
    run_lean_script(
        &mut checker,
        "gen-bad-postponed",
        &stage.join("gen_bad_postponed.lean"),
        &format!(
            "import Lean.Compiler.LCNF.Main\n\
             import Lean.Elab.Import\n\
             open Lean\n\
             def main : IO Unit := do\n\
               searchPathRef.set (← getBuiltinSearchPath (System.FilePath.mk {:?}))\n\
               let env ← importModules #[{{ module := `Init.Core }}] {{}} 0\n\
               let env := env.setMainModule `Anneal.BadPostponed\n\
               let env := Compiler.LCNF.postponedCompileDeclsExt.addEntry env (\n\
                 {{ declNames := #[`Anneal.BadPostponed.secret], options := {{}} }})\n\
               writeModule env {:?}\n",
            lean_prefix.to_string_lossy(),
            postponed_olean.to_string_lossy()
        ),
    );
    let postponed_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let postponed_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", postponed_olean.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    checker
        .admitted_mut()
        .unwrap()
        .artifacts
        .insert("Anneal.BadPostponed".to_string(), postponed_arts);
    checker.admitted_mut().unwrap().graph.insert("Anneal.BadPostponed".to_string(), postponed_edge);
    let err_post = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal.BadPostponed".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!((err_post.code, err_post.phase.as_str()), (1, "audit"), "{err_post}");
    assert!(
        err_post
            .message
            .contains("unchecked postponed compilation entry for Anneal.BadPostponed.secret in Anneal.BadPostponed"),
        "{err_post}"
    );
    let adm = checker.admitted_mut().unwrap();
    adm.artifacts.remove("Anneal.BadPostponed");
    adm.graph.remove("Anneal.BadPostponed");

    // 2. Pass 2 `"correspondence-audit"`: forged `.repo .theory` modules
    //    importing sysroot `Init.System.IO` / `Lean.Compiler.LCNF.*` with
    //    `@[init]`, `@[builtin_init]`, `@[cpass]`, or
    //    `ConstantFold.registerFolder`.
    let compile_corr_theory = |chk: &mut Checker, module: &str, body: &str| {
        let rel = module.replace('.', "/");
        let src = src_dir.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let out = theory_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        chk.process_with_path(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                src_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
            None,
        )
        .unwrap();
    };
    for (module, body, expected) in [
        (
            "Anneal.CorrBadInit",
            "prelude\nimport Init.Core\nimport Init.System.IO\n\
             @[init] def badInit : IO Unit := pure ()\n",
            "unchecked compiler init override on badInit in Anneal.CorrBadInit",
        ),
        (
            "Anneal.CorrBadBuiltinInit",
            "prelude\nimport Init.Core\nimport Init.System.IO\n\
             @[builtin_init] def badBuiltinInit : IO Unit := pure ()\n",
            "unchecked compiler builtin_init override on badBuiltinInit in Anneal.CorrBadBuiltinInit",
        ),
        (
            "Anneal.CorrBadCpass",
            "import Lean.Compiler.LCNF.Passes\nopen Lean\n\
             meta def badPassInstaller : Compiler.LCNF.PassInstaller :=\n\
               { phase := .base, install := fun pm => pure pm }\n\
             attribute [cpass] badPassInstaller\n",
            "unchecked compiler cpass override badPassInstaller in Anneal.CorrBadCpass",
        ),
        (
            "Anneal.CorrBadFold",
            "import Lean.Compiler.LCNF.Simp.ConstantFold\nimport Lean.Elab.Command\nopen Lean\n\
             meta def badFolder : Compiler.LCNF.Simp.ConstantFold.Folder := fun _ => return none\n\
             run_cmd Elab.Command.liftCoreM <|\n\
               Compiler.LCNF.Simp.ConstantFold.registerFolder `Nat.add `badFolder\n",
            "unchecked compiler constant_fold override on Nat.add in Anneal.CorrBadFold",
        ),
    ] {
        compile_corr_theory(&mut checker, module, body);
        let err = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: vec![stage.join("lib"), theory_lib.clone()],
                trusted: vec!["Trusted".to_string()],
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: vec![module.to_string()],
                vendor_miri: Vec::new(),
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "correspondence-audit"), "{module}: {err}");
        assert!(err.message.contains(expected), "{module}: {err}");
    }

    // 3. `"target-export"` <-> `"target-audit"`: spliced `passManagerExt`,
    //    `folderExt`, and `postponedCompileDeclsExt` entries on `Proof.olean`
    //    and non-`Proof` `Spec.olean` fail closed with policy exit code `1`.
    let target_dir = stage.join("target-splice-root");
    for rel in [
        "trusted/audit/TrustedBoundary.lean",
        "trusted/audit/library-lock.json",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
    ] {
        fs::create_dir_all(target_dir.join(rel).parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), target_dir.join(rel)).unwrap();
    }
    fs::create_dir_all(target_dir.join("trusted/lean")).unwrap();
    fs::write(target_dir.join("trusted/lean/Trusted.lean"), HEADER).unwrap();
    let inputs = target_dir.join("inputs");
    fs::create_dir_all(&inputs).unwrap();
    let h = sha256_bytes(b"target splice fixture");
    let mut modules = Vec::new();
    for (name, role, src) in [
        (
            "Model",
            TargetRole::Model,
            "prelude\nimport Init.Data.BitVec.Basic\nnamespace Trusted.MirSemantics\n\
             structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
             def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n",
        ),
        (
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
        ),
        (
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Captured\nimport Spec\ndef Expected.claim : Prop := \
             Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        ),
        (
            "Proof",
            TargetRole::Proof,
            "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
        ),
    ] {
        let p = inputs.join(format!("{name}.lean"));
        fs::write(&p, src).unwrap();
        modules.push(TargetModule {
            module: name.into(),
            source: p,
            expected_sha256: sha256_bytes(src.as_bytes()),
            role,
        });
    }
    let request = TargetAuditRequest {
        modules,
        theorem_module: "Proof".into(),
        theorem_name: "Proof.verify".into(),
        expected_module: "Expected".into(),
        expected_declaration: "Expected.claim".into(),
        canonical_root: "Trusted.MirSemantics.UnitTheorem".into(),
        subject_declaration: "Captured.program".into(),
        specification_declaration: "Spec.specs".into(),
        allow_sorry_in_proof: false,
        bindings: TargetBindings {
            request_sha256: h.clone(),
            capture_sha256: h.clone(),
            model_manifest_sha256: h.clone(),
            specification_manifest_sha256: h,
        },
    };
    let mut tgt_chk = cargo_anneal::Checker::new(&target_dir, None).unwrap();
    tgt_chk.run_target(&request).unwrap();

    let tstage = tgt_chk.stage().to_path_buf();
    let proof_olean = tstage.join("lib/Proof.olean");
    let spec_olean = tstage.join("lib/Spec.olean");
    let clean_proof = tstage.join("CleanProof.olean");
    let clean_spec = tstage.join("CleanSpec.olean");
    fs::copy(&proof_olean, &clean_proof).unwrap();
    fs::copy(&spec_olean, &clean_spec).unwrap();
    let cpass_olean = theory_lib.join("Anneal/CorrBadCpass.olean");
    let fold_olean = theory_lib.join("Anneal/CorrBadFold.olean");

    let splice_cases = [
        (
            "cpass",
            "unchecked compiler cpass override badPassInstaller",
            cpass_olean.clone(),
            "Compiler.LCNF.passManagerExt.name",
        ),
        (
            "constant-fold",
            "unchecked compiler constant_fold override on Nat.add",
            fold_olean.clone(),
            "Compiler.LCNF.Simp.ConstantFold.folderExt.name",
        ),
        (
            "postponed-compile",
            "unchecked postponed compilation entry for Anneal.BadPostponed.secret",
            postponed_olean.clone(),
            "Compiler.LCNF.postponedCompileDeclsExt.name",
        ),
    ];
    let mut gen_src = String::from(
        "import Lean.Compiler.LCNF.Main\n\
         import Lean.Compiler.LCNF.Passes\n\
         import Lean.Compiler.LCNF.Simp.ConstantFold\n\
         import Lean.Elab.Import\n\
         open Lean\n\
         def main : IO Unit := do\n\
           let (proofMd, _) ← readModuleData ",
    );
    gen_src.push_str(&format!(
        "{:?}\n  let (specMd, _) ← readModuleData {:?}\n",
        clean_proof.to_string_lossy(),
        clean_spec.to_string_lossy()
    ));
    for (idx, (_, _, donor_path, ext_name)) in splice_cases.iter().enumerate() {
        let out_p = tstage.join(format!("SplicedProof_{idx}.olean"));
        let out_s = tstage.join(format!("SplicedSpec_{idx}.olean"));
        gen_src.push_str(&format!(
            "  let (d{idx}, _) ← readModuleData {:?}\n\
               let e{idx} := d{idx}.entries.filter (fun (n, _) => n == {ext_name})\n\
               saveModuleData {:?} `Proof {{ proofMd with entries := proofMd.entries ++ e{idx} }}\n\
               saveModuleData {:?} `Spec {{ specMd with entries := specMd.entries ++ e{idx} }}\n",
            donor_path.to_string_lossy(),
            out_p.to_string_lossy(),
            out_s.to_string_lossy()
        ));
    }
    run_lean_script(
        &mut checker,
        "gen-spliced-target-oleans",
        &stage.join("gen_spliced_target.lean"),
        &gen_src,
    );

    let replace_artifact =
        |chk: &mut cargo_anneal::Checker, mod_name: &str, dest: &Path, src: &Path| {
            #[cfg(unix)]
            if dest.exists() {
                let _ = fs::set_permissions(dest, fs::Permissions::from_mode(0o600));
            }
            fs::copy(src, dest).unwrap();
            let avail = BTreeMap::from([("olean", dest.to_string_lossy().into_owned())]);
            let arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
            chk.admitted_mut().unwrap().artifacts.insert(mod_name.into(), arts);
        };

    for (idx, (label, expected, _, _)) in splice_cases.iter().enumerate() {
        let sp_proof = tstage.join(format!("SplicedProof_{idx}.olean"));
        replace_artifact(&mut tgt_chk, "Proof", &proof_olean, &sp_proof);
        let err_p = tgt_chk.inspect_target(&request).unwrap_err();
        assert_eq!(
            (err_p.code, err_p.phase.as_str()),
            (1, "target-audit"),
            "proof-{label}: {err_p}"
        );
        assert!(err_p.message.contains(expected), "proof-{label}: {err_p}");
        replace_artifact(&mut tgt_chk, "Proof", &proof_olean, &clean_proof);

        let sp_spec = tstage.join(format!("SplicedSpec_{idx}.olean"));
        replace_artifact(&mut tgt_chk, "Spec", &spec_olean, &sp_spec);
        let err_s = tgt_chk.inspect_target(&request).unwrap_err();
        assert_eq!(
            (err_s.code, err_s.phase.as_str()),
            (1, "target-audit"),
            "spec-{label}: {err_s}"
        );
        let expected_spec = format!("{expected} in Spec");
        assert!(err_s.message.contains(&expected_spec), "spec-{label}: {err_s}");
        replace_artifact(&mut tgt_chk, "Spec", &spec_olean, &clean_spec);
    }

    // 4. Multi-part Lean 4 `module` companion coverage:
    //    (a) `private @[export]` inside a compiled 3-part `module` goes only
    //        into `.olean.private`, and `"audit"` still rejects it;
    //    (b) forging an override strictly into `.olean` (`.exported`) or
    //        `.olean.server` (`.server`) while `.olean.private` stays clean
    //        fails closed in Pass 1 `"audit"`, Pass 2
    //        `"correspondence-audit"`, and `"target-export"` <->
    //        `"target-audit"`;
    //    (c) a clean `.olean.private` whose `isModule` flag is `false` under
    //        a `module` `.olean` that carries an override fails closed in both
    //        repository passes, which no longer choose parts by that flag;
    //    (d) a `module` `.repo` module privately importing a `module`
    //        `.vendorMiri` module without `.ir` parts passes the Pass 2
    //        override scan instead of failing to import.
    //    (e) a hook stored only in `.ir` or only in `.ir.sig` fails closed in
    //        Pass 2 `"correspondence-audit"`.
    let init_core_edge = ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    };
    let compile_module_3part = |chk: &mut Checker, module: &str, body: &str, edges: Vec<ImportEdge>| {
        let rel = module.replace('.', "/");
        let src = src_dir.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let olean = theory_lib.join(format!("{rel}.olean"));
        let srv = theory_lib.join(format!("{rel}.olean.server"));
        let prv = theory_lib.join(format!("{rel}.olean.private"));
        fs::create_dir_all(olean.parent().unwrap()).unwrap();
        let base_setup = chk.write_setup_json(module, &edges).unwrap();
        let mut setup_json: Json =
            serde_json::from_str(&fs::read_to_string(&base_setup).unwrap()).unwrap();
        setup_json["isModule"] = json!(true);
        let mod_setup = stage.join(format!("{module}.mod.setup.json"));
        fs::write(&mod_setup, serde_json::to_string_pretty(&setup_json).unwrap()).unwrap();
        chk.process(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                mod_setup.to_string_lossy().into_owned(),
                "-o".to_string(),
                olean.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
        assert!(srv.exists(), "{module} missing .olean.server");
        assert!(prv.exists(), "{module} missing .olean.private");
        let arts = ModuleArtifacts::from_available(
            &BTreeMap::from([
                ("olean", olean.to_string_lossy().into_owned()),
                ("olean.server", srv.to_string_lossy().into_owned()),
                ("olean.private", prv.to_string_lossy().into_owned()),
            ]),
            "test",
            String::new,
        )
        .unwrap();
        let adm = chk.admitted_mut().unwrap();
        adm.artifacts.insert(module.to_string(), arts);
        adm.graph.insert(module.to_string(), edges);
    };

    compile_module_3part(
        &mut checker,
        "Anneal.BadModPrivExport",
        "module\nprelude\npublic import Init.Core\n\
         @[export anneal_repo_priv_export] private def privExport (n : Nat) : Nat := n\n",
        vec![init_core_edge.clone()],
    );
    let err_priv = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal.BadModPrivExport".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!((err_priv.code, err_priv.phase.as_str()), (1, "audit"), "{err_priv}");
    assert!(
        err_priv.message.contains("unchecked compiler export override on ")
            && err_priv.message.contains("privExport in Anneal.BadModPrivExport"),
        "{err_priv}"
    );
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove("Anneal.BadModPrivExport");
        adm.graph.remove("Anneal.BadModPrivExport");
    }

    compile_module_3part(
        &mut checker,
        "Anneal.CleanMod",
        "module\nprelude\npublic import Init.Core\n\
         @[expose] public section\n\
         def cleanVal : Nat := 1\n\
         end\n",
        vec![init_core_edge.clone()],
    );
    let clean_mod_o = theory_lib.join("Anneal/CleanMod.olean");
    let clean_mod_s = theory_lib.join("Anneal/CleanMod.olean.server");
    let clean_mod_p = theory_lib.join("Anneal/CleanMod.olean.private");
    let mod_edges = vec![init_core_edge.clone()];

    let exp_dir = theory_lib.join("Anneal/CleanModExpOnly");
    let srv_dir = theory_lib.join("Anneal/CleanModSrvOnly");
    let prv_nonmod_dir = theory_lib.join("Anneal/CleanModPrivNonMod");
    for dir in [&exp_dir, &srv_dir, &prv_nonmod_dir] {
        fs::create_dir_all(dir.join("Anneal")).unwrap();
    }
    let splice_mod_script = format!(
        "import Lean.Compiler.LCNF.Passes\n\
         import Lean.Elab.Import\n\
         open Lean\n\
         def main : IO Unit := do\n\
           let parts ← readModuleDataParts #[{:?}, {:?}, {:?}]\n\
           let (d, _) ← readModuleData {:?}\n\
           let e := d.entries.filter (fun (n, _) => n == Compiler.LCNF.passManagerExt.name)\n\
           let #[(md0, _), (md1, _), (md2, _)] := parts | throw <| IO.userError \"expected 3 parts\"\n\
           saveModuleDataParts `Anneal.CleanMod #[\n\
             ({:?}, {{ md0 with entries := md0.entries ++ e }}),\n\
             ({:?}, md1),\n\
             ({:?}, md2)]\n\
           saveModuleDataParts `Anneal.CleanMod #[\n\
             ({:?}, md0),\n\
             ({:?}, {{ md1 with entries := md1.entries ++ e }}),\n\
             ({:?}, md2)]\n\
           saveModuleDataParts `Anneal.CleanMod #[\n\
             ({:?}, {{ md0 with entries := md0.entries ++ e }}),\n\
             ({:?}, md1),\n\
             ({:?}, {{ md2 with isModule := false }})]\n",
        clean_mod_o.to_string_lossy(),
        clean_mod_s.to_string_lossy(),
        clean_mod_p.to_string_lossy(),
        cpass_olean.to_string_lossy(),
        exp_dir.join("Anneal/CleanMod.olean").to_string_lossy(),
        exp_dir.join("Anneal/CleanMod.olean.server").to_string_lossy(),
        exp_dir.join("Anneal/CleanMod.olean.private").to_string_lossy(),
        srv_dir.join("Anneal/CleanMod.olean").to_string_lossy(),
        srv_dir.join("Anneal/CleanMod.olean.server").to_string_lossy(),
        srv_dir.join("Anneal/CleanMod.olean.private").to_string_lossy(),
        prv_nonmod_dir.join("Anneal/CleanMod.olean").to_string_lossy(),
        prv_nonmod_dir.join("Anneal/CleanMod.olean.server").to_string_lossy(),
        prv_nonmod_dir.join("Anneal/CleanMod.olean.private").to_string_lossy(),
    );
    run_lean_script(
        &mut checker,
        "gen-spliced-module-parts",
        &stage.join("gen_spliced_module_parts.lean"),
        &splice_mod_script,
    );

    let cpass_clean_mod = "unchecked compiler cpass override badPassInstaller in Anneal.CleanMod";
    let part_cases = [
        ("exported-only", &exp_dir, cpass_clean_mod),
        ("server-only", &srv_dir, cpass_clean_mod),
        (
            "private-non-module",
            &prv_nonmod_dir,
            "mismatched olean companion isModule flag in Anneal.CleanMod",
        ),
    ];
    for (label, dir, expected) in part_cases {
        let arts = ModuleArtifacts::from_available(
            &BTreeMap::from([
                ("olean", dir.join("Anneal/CleanMod.olean").to_string_lossy().into_owned()),
                (
                    "olean.server",
                    dir.join("Anneal/CleanMod.olean.server").to_string_lossy().into_owned(),
                ),
                (
                    "olean.private",
                    dir.join("Anneal/CleanMod.olean.private").to_string_lossy().into_owned(),
                ),
            ]),
            "test",
            String::new,
        )
        .unwrap();
        {
            let adm = checker.admitted_mut().unwrap();
            adm.artifacts.insert("Anneal.CleanMod".to_string(), arts);
            adm.graph.insert("Anneal.CleanMod".to_string(), mod_edges.clone());
        }
        let err_part = checker
            .inspect(InspectorRequest::Audit {
                trusted: vec!["Trusted".to_string()],
                theory: vec!["Anneal.CleanMod".to_string()],
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!(
            (err_part.code, err_part.phase.as_str()),
            (1, "audit"),
            "{label}: {err_part}"
        );
        assert!(err_part.message.contains(expected), "{label}: {err_part}");
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove("Anneal.CleanMod");
        adm.graph.remove("Anneal.CleanMod");
    }
    for (label, dir, expected) in part_cases {
        let err_corr = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: vec![stage.join("lib"), dir.clone()],
                trusted: vec!["Trusted".to_string()],
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: vec!["Anneal.CleanMod".to_string()],
                vendor_miri: Vec::new(),
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!(
            (err_corr.code, err_corr.phase.as_str()),
            (1, "correspondence-audit"),
            "corr-{label}: {err_corr}"
        );
        assert!(err_corr.message.contains(expected), "corr-{label}: {err_corr}");
    }

    compile_module_3part(
        &mut checker,
        "Miri.ModVendor",
        "module\nprelude\npublic import Init.Core\n\
         public def Miri.ModVendor.v : Nat := 1\n",
        vec![init_core_edge.clone()],
    );
    for ext in ["ir", "ir.sig"] {
        let _ = fs::remove_file(theory_lib.join(format!("Miri/ModVendor.{ext}")));
    }
    compile_module_3part(
        &mut checker,
        "Anneal.RepoUsesVendor",
        "module\nprelude\npublic import Init.Core\nimport Miri.ModVendor\n\
         public def Anneal.RepoUsesVendor.r : Nat := 2\n",
        vec![
            init_core_edge.clone(),
            ImportEdge {
                module: "Miri.ModVendor".to_string(),
                import_all: false,
                is_exported: false,
                is_meta: false,
            },
        ],
    );
    let err_vendor = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![stage.join("lib"), theory_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.RepoUsesVendor".to_string()],
            vendor_miri: vec!["Miri.ModVendor".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        (err_vendor.code, err_vendor.phase.as_str()),
        (1, "correspondence-audit"),
        "{err_vendor}"
    );
    // The request gets past the override scan and fails later, on the
    // `Miri.Interpreter.ExecutionMachine` module that this fixture omits.
    assert!(
        err_vendor
            .message
            .contains("unknown declaration origin: Miri.Interpreter.ExecutionMachine.step"),
        "{err_vendor}"
    );

    // 4(e). A hook stored only in `.ir` or only in `.ir.sig`, beside clean
    //       `.olean*` parts, fails closed in Pass 2 `"correspondence-audit"`,
    //       which reads `.ir*` parts through the search path. The Pass 1
    //       artifact map that `cargo-anneal` stages holds only `.olean*`
    //       parts, and `"target-audit"` rejects target `.ir` parts.
    let ir_only_dir = theory_lib.join("Anneal/CleanModIrOnly");
    let ir_sig_only_dir = theory_lib.join("Anneal/CleanModIrSigOnly");
    for dir in [&ir_only_dir, &ir_sig_only_dir] {
        fs::create_dir_all(dir.join("Anneal")).unwrap();
        for (src, ext) in [
            (&clean_mod_o, "olean"),
            (&clean_mod_s, "olean.server"),
            (&clean_mod_p, "olean.private"),
        ] {
            fs::copy(src, dir.join(format!("Anneal/CleanMod.{ext}"))).unwrap();
        }
    }
    let splice_ir_script = format!(
        "import Lean.Compiler.LCNF.Passes\n\
         import Lean.Elab.Import\n\
         open Lean\n\
         def main : IO Unit := do\n\
           let parts ← readModuleDataParts #[{:?}, {:?}, {:?}]\n\
           let (d, _) ← readModuleData {:?}\n\
           let e := d.entries.filter (fun (n, _) => n == Compiler.LCNF.passManagerExt.name)\n\
           let #[_, _, (md2, _)] := parts | throw <| IO.userError \"expected 3 parts\"\n\
           let ir : ModuleData := {{ md2 with constNames := #[], constants := #[], entries := #[] }}\n\
           saveModuleDataParts `Anneal.CleanMod.ir #[\n\
             ({:?}, default),\n\
             ({:?}, {{ ir with entries := e }})]\n\
           saveModuleDataParts `Anneal.CleanMod.ir #[\n\
             ({:?}, {{ (default : ModuleData) with entries := e }}),\n\
             ({:?}, ir)]\n",
        clean_mod_o.to_string_lossy(),
        clean_mod_s.to_string_lossy(),
        clean_mod_p.to_string_lossy(),
        cpass_olean.to_string_lossy(),
        ir_only_dir.join("Anneal/CleanMod.ir.sig").to_string_lossy(),
        ir_only_dir.join("Anneal/CleanMod.ir").to_string_lossy(),
        ir_sig_only_dir.join("Anneal/CleanMod.ir.sig").to_string_lossy(),
        ir_sig_only_dir.join("Anneal/CleanMod.ir").to_string_lossy(),
    );
    run_lean_script(
        &mut checker,
        "gen-spliced-module-ir-parts",
        &stage.join("gen_spliced_module_ir_parts.lean"),
        &splice_ir_script,
    );
    for (label, dir) in [("ir-only", &ir_only_dir), ("ir-sig-only", &ir_sig_only_dir)] {
        let err_ir_corr = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: vec![stage.join("lib"), dir.clone()],
                trusted: vec!["Trusted".to_string()],
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: vec!["Anneal.CleanMod".to_string()],
                vendor_miri: Vec::new(),
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!(
            (err_ir_corr.code, err_ir_corr.phase.as_str()),
            (1, "correspondence-audit"),
            "corr-{label}: {err_ir_corr}"
        );
        assert!(err_ir_corr.message.contains(cpass_clean_mod), "corr-{label}: {err_ir_corr}");
    }

    // Also verify 3-part `module` companion tampering in `"target-export"` <->
    // `"target-audit"` on bundled `Anneal.*` (`Proof`) and `Trusted.*`
    // (`Model`).
    let mod_h = sha256_bytes(b"target 3-part module splice fixture");
    let mut mod_tgt_modules = Vec::new();
    for (name, role, src) in [
        (
            "Trusted.ModBase",
            TargetRole::Model,
            "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
             @[expose] public section\n\
             namespace Trusted.MirSemantics\n\
             structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
             def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
             end Trusted.MirSemantics\n\
             end\n",
        ),
        (
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Trusted.ModBase\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
        ),
        (
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Trusted.ModBase\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Captured\nimport Spec\ndef Expected.claim : Prop := \
             Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        ),
        (
            "Anneal.HelperMod",
            TargetRole::Proof,
            "module\nprelude\npublic import Init.Core\n\
             public section\ntheorem Anneal.HelperMod.ok : True := True.intro\nend\n",
        ),
        (
            "Proof",
            TargetRole::Proof,
            "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\nimport Anneal.HelperMod\n\
             theorem Proof.verify : Expected.claim :=\n\
             (fun _ => And.intro rfl BitVec.and_self) Anneal.HelperMod.ok\n",
        ),
    ] {
        let p = inputs.join(format!("{name}.lean"));
        fs::write(&p, src).unwrap();
        mod_tgt_modules.push(TargetModule {
            module: name.into(),
            source: p,
            expected_sha256: sha256_bytes(src.as_bytes()),
            role,
        });
    }
    let mod_req = TargetAuditRequest {
        modules: mod_tgt_modules,
        theorem_module: "Proof".into(),
        theorem_name: "Proof.verify".into(),
        expected_module: "Expected".into(),
        expected_declaration: "Expected.claim".into(),
        canonical_root: "Trusted.MirSemantics.UnitTheorem".into(),
        subject_declaration: "Captured.program".into(),
        specification_declaration: "Spec.specs".into(),
        allow_sorry_in_proof: false,
        bindings: TargetBindings {
            request_sha256: mod_h.clone(),
            capture_sha256: mod_h.clone(),
            model_manifest_sha256: mod_h.clone(),
            specification_manifest_sha256: mod_h,
        },
    };
    let mut mod_tgt_chk = cargo_anneal::Checker::new(&target_dir, None).unwrap();
    mod_tgt_chk.run_target(&mod_req).unwrap();
    let orig_mod_arts = mod_tgt_chk.admitted().unwrap().artifacts.clone();
    let mod_stage = mod_tgt_chk.stage().to_path_buf();
    let base_parts = orig_mod_arts["Trusted.ModBase"].olean_parts.clone();
    let helper_parts = orig_mod_arts["Anneal.HelperMod"].olean_parts.clone();
    assert_eq!(base_parts.len(), 3);
    assert_eq!(helper_parts.len(), 3);
    fs::create_dir_all(mod_stage.join("spliced-mod-base")).unwrap();
    fs::create_dir_all(mod_stage.join("spliced-helper-mod")).unwrap();
    fs::create_dir_all(mod_stage.join("spliced-helper-mod-srv")).unwrap();
    let splice_tgt_3part = format!(
        "import Lean.Compiler.LCNF.Passes\n\
         import Lean.Elab.Import\n\
         open Lean\n\
         def main : IO Unit := do\n\
           let (d, _) ← readModuleData {:?}\n\
           let e := d.entries.filter (fun (n, _) => n == Compiler.LCNF.passManagerExt.name)\n\
           let #[(bp0, _), (bp1, _), (bp2, _)] ← readModuleDataParts #[{:?}, {:?}, {:?}]\n\
             | throw <| IO.userError \"expected 3 base parts\"\n\
           saveModuleDataParts `Trusted.ModBase #[\n\
             ({:?}, bp0),\n\
             ({:?}, {{ bp1 with entries := bp1.entries ++ e }}),\n\
             ({:?}, bp2)]\n\
           let #[(hp0, _), (hp1, _), (hp2, _)] ← readModuleDataParts #[{:?}, {:?}, {:?}]\n\
             | throw <| IO.userError \"expected 3 helper parts\"\n\
           saveModuleDataParts `Anneal.HelperMod #[\n\
             ({:?}, {{ hp0 with entries := hp0.entries ++ e }}),\n\
             ({:?}, hp1),\n\
             ({:?}, hp2)]\n\
           saveModuleDataParts `Anneal.HelperMod #[\n\
             ({:?}, hp0),\n\
             ({:?}, {{ hp1 with entries := hp1.entries ++ e }}),\n\
             ({:?}, hp2)]\n",
        cpass_olean.to_string_lossy(),
        base_parts[0],
        base_parts[1],
        base_parts[2],
        mod_stage.join("spliced-mod-base/ModBase.olean").to_string_lossy(),
        mod_stage.join("spliced-mod-base/ModBase.olean.server").to_string_lossy(),
        mod_stage.join("spliced-mod-base/ModBase.olean.private").to_string_lossy(),
        helper_parts[0],
        helper_parts[1],
        helper_parts[2],
        mod_stage.join("spliced-helper-mod/HelperMod.olean").to_string_lossy(),
        mod_stage.join("spliced-helper-mod/HelperMod.olean.server").to_string_lossy(),
        mod_stage.join("spliced-helper-mod/HelperMod.olean.private").to_string_lossy(),
        mod_stage.join("spliced-helper-mod-srv/HelperMod.olean").to_string_lossy(),
        mod_stage.join("spliced-helper-mod-srv/HelperMod.olean.server").to_string_lossy(),
        mod_stage.join("spliced-helper-mod-srv/HelperMod.olean.private").to_string_lossy(),
    );
    run_lean_script(
        &mut checker,
        "gen-spliced-target-3part",
        &stage.join("gen_spliced_target_3part.lean"),
        &splice_tgt_3part,
    );
    fs::create_dir_all(mod_stage.join("clean-mod-base")).unwrap();
    for (idx, ext) in ["olean", "olean.server", "olean.private"].iter().enumerate() {
        fs::copy(&base_parts[idx], mod_stage.join(format!("clean-mod-base/ModBase.{ext}"))).unwrap();
    }
    for (mod_name, stem, dir, label) in [
        ("Trusted.ModBase", "Trusted/ModBase", mod_stage.join("spliced-mod-base"), "target-model-server"),
        ("Anneal.HelperMod", "Anneal/HelperMod", mod_stage.join("spliced-helper-mod"), "target-proof-exported"),
        ("Anneal.HelperMod", "Anneal/HelperMod", mod_stage.join("spliced-helper-mod-srv"), "target-proof-server"),
    ] {
        let leaf = if mod_name == "Trusted.ModBase" { "ModBase" } else { "HelperMod" };
        let mut avail = BTreeMap::new();
        for ext in ["olean", "olean.server", "olean.private"] {
            let dest = mod_stage.join(format!("lib/{stem}.{ext}"));
            #[cfg(unix)]
            if dest.exists() {
                let _ = fs::set_permissions(&dest, fs::Permissions::from_mode(0o600));
            }
            fs::copy(dir.join(format!("{leaf}.{ext}")), &dest).unwrap();
            avail.insert(ext, dest.to_string_lossy().into_owned());
        }
        let arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
        mod_tgt_chk.admitted_mut().unwrap().artifacts = orig_mod_arts.clone();
        mod_tgt_chk.admitted_mut().unwrap().artifacts.insert(mod_name.into(), arts);
        let err_m = mod_tgt_chk.inspect_target(&mod_req).unwrap_err();
        assert_eq!((err_m.code, err_m.phase.as_str()), (1, "target-audit"), "{label}: {err_m}");
        assert!(
            err_m.message.contains("unchecked compiler cpass override badPassInstaller"),
            "{label}: {err_m}"
        );
        if mod_name == "Trusted.ModBase" {
            for ext in ["olean", "olean.server", "olean.private"] {
                let dest = mod_stage.join(format!("lib/Trusted/ModBase.{ext}"));
                #[cfg(unix)]
                let _ = fs::set_permissions(&dest, fs::Permissions::from_mode(0o600));
                fs::copy(mod_stage.join(format!("clean-mod-base/ModBase.{ext}")), &dest).unwrap();
            }
        }
    }
}
