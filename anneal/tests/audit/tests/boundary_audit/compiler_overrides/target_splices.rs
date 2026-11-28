// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Section 3: compiler-override entries spliced into target `Proof` and
//! `Spec` modules.

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use anneal_audit::{TargetAuditRequest, TargetBindings, TargetModule, TargetRole};

use super::*;

/// Runs section 3 and returns the checker together with the target root, its
/// `inputs` directory, and the `Anneal/CorrBadCpass.olean` donor, which
/// section 5 reuses.
pub(super) fn target_audit_rejects_spliced_overrides(
    mut checker: Checker,
    checkout: PathBuf,
    stage: PathBuf,
    theory_lib: PathBuf,
    postponed_olean: PathBuf,
) -> (Checker, PathBuf, PathBuf, PathBuf) {
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
    (checker, target_dir, inputs, cpass_olean)
}
