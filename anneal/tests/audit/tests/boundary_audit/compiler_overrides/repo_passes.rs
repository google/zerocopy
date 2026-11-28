// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Sections 1 and 2: forged repository modules with compiler overrides in
//! Pass 1 `"audit"` and Pass 2 `"correspondence-audit"`.

use super::*;

/// Runs section 1 and returns the checker together with the forged
/// `Anneal/BadPostponed.olean`, which section 3 splices into target modules.
pub(super) fn audit_rejects_forged_overrides(
    mut checker: Checker,
    stage: PathBuf,
    theory_lib: PathBuf,
    src_dir: PathBuf,
) -> (Checker, PathBuf) {
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
    (checker, postponed_olean)
}

/// Runs section 2, which also compiles the `Anneal.CorrBadCpass` and
/// `Anneal.CorrBadFold` donor modules that sections 3 through 5 reuse.
pub(super) fn correspondence_audit_rejects_forged_overrides(
    mut checker: Checker,
    stage: PathBuf,
    theory_lib: PathBuf,
    src_dir: PathBuf,
) -> Checker {
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
    checker
}
