// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Section 5: overrides hidden in individual parts of 3-part Lean 4
//! `module` artifacts in the target passes.

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use anneal_audit::{TargetAuditRequest, TargetBindings, TargetModule, TargetRole};

use super::*;

/// Runs section 5.
pub(super) fn target_audit_rejects_overrides_in_module_parts(
    mut checker: Checker,
    stage: PathBuf,
    target_dir: PathBuf,
    inputs: PathBuf,
    cpass_olean: PathBuf,
) {
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
