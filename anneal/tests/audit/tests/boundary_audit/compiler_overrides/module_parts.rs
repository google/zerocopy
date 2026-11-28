// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Section 4: overrides hidden in individual parts of 3-part Lean 4
//! `module` artifacts in the repository passes.

use super::*;

/// Runs section 4, including 4(e), and returns the checker.
pub(super) fn repo_passes_reject_overrides_in_module_parts(
    mut checker: Checker,
    stage: PathBuf,
    theory_lib: PathBuf,
    src_dir: PathBuf,
    cpass_olean: PathBuf,
) -> Checker {
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
    checker
}
