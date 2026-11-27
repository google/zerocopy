// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Target roots, canonical inputs, source binding, and the authority
//! separation between reviewed roles.

use super::*;

/// Authored tactic source and BitVec dependencies are checked from private
/// copies. Adjacent caller artifacts and read-only source files are untouched.
#[test]
fn accepts_authored_proof_and_preserves_read_only_sources() {
    let f = Fixture::new(PROOF);
    let bytes: Vec<_> = f
        .request
        .modules
        .iter()
        .map(|m| fs::read(&m.source).unwrap())
        .collect();
    for m in &f.request.modules {
        let mut p = fs::metadata(&m.source).unwrap().permissions();
        p.set_readonly(true);
        fs::set_permissions(&m.source, p).unwrap();
        fs::write(m.source.with_extension("olean"), b"stale artifact").unwrap();
    }
    let report = f.run().unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert!(report["replayedDeclarations"].as_u64().unwrap() > 5);
    for (m, original) in f.request.modules.iter().zip(bytes) {
        assert_eq!(fs::read(&m.source).unwrap(), original);
        assert_eq!(
            fs::read(m.source.with_extension("olean")).unwrap(),
            b"stale artifact"
        );
    }
}

/// The dotted spelling of name pool entry `id` of a proof export.
fn export_name(export: &Json, id: usize) -> String {
    let entry = export["names"][id].as_array().unwrap();
    match entry[0].as_str().unwrap() {
        "a" => String::new(),
        "s" => {
            let pre = export_name(export, entry[1].as_u64().unwrap() as usize);
            let seg = entry[2].as_str().unwrap();
            if pre.is_empty() { seg.to_owned() } else { format!("{pre}.{seg}") }
        }
        tag => panic!("unexpected name tag {tag}"),
    }
}

/// The type and value expression pool indices of definition `name` in a
/// proof export.
fn export_defn_ids(export: &Json, name: &str) -> (u64, u64) {
    for module in export["modules"].as_array().unwrap() {
        for constant in module["constants"].as_array().unwrap() {
            let c = constant.as_array().unwrap();
            if c[0] == "defn" && export_name(export, c[1].as_u64().unwrap() as usize) == name {
                return (c[3].as_u64().unwrap(), c[4].as_u64().unwrap());
            }
        }
    }
    panic!("no definition {name} in proof export");
}

/// `"target-export"` interns by strict structure: the same term in two proof
/// modules (separate `.olean` objects, so distinct heap objects) shares one
/// expression entry, and two types that differ only in a binder's info (the
/// binder names `h` and `x` match) keep distinct entries, so the decoded
/// declarations are exactly the compiled ones.
#[test]
fn target_export_interns_by_strict_structure() {
    let mut f = Fixture::new(
        "prelude\nimport Expected\nimport ProofAux\nimport Init.Data.BitVec.Lemmas\n\
         def Proof.shareB (a b : Nat) : Nat := a + b * a + (b + a) * (a + b)\n\
         def Proof.explicitArg (h : ∀ (x : Nat), x = x) : 0 = 0 := h 0\n\
         def Proof.implicitArg (h : ∀ {x : Nat}, x = x) : 0 = 0 := @h 0\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "ProofAux",
        TargetRole::Proof,
        "prelude\nimport Init.Data.BitVec.Lemmas\n\
         def ProofAux.shareA (a b : Nat) : Nat := a + b * a + (b + a) * (a + b)\n",
    );
    let mut checker = f.cargo_checker();
    checker.run_target(&f.request).unwrap();
    let export = checker.inspect_target_export(&f.request).unwrap();
    let ids = |name| export_defn_ids(&export, name);
    assert_eq!(ids("ProofAux.shareA").1, ids("Proof.shareB").1);
    assert_ne!(ids("Proof.explicitArg").0, ids("Proof.implicitArg").0);
}

/// Claim identities include a library used only through the selected subject,
/// without turning proof helpers or unused Capture modules into meaning roots.
#[test]
fn reports_subject_only_library_identities_without_proof_dependencies() {
    const LIBRARY: &str = "Init.Data.Nat.Gcd";
    const PROOF_LIBRARY: &str = "Init.Data.BitVec.Lemmas";
    let mut fixture = Fixture::new(PROOF);
    fixture.set(
        "CapturedHelper",
        TargetRole::Capture,
        "prelude\nimport Model\nimport Init.Data.Nat.Gcd\ndef CapturedHelper.value : Nat := Nat.gcd 0 7\n",
    );
    fixture.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\nimport CapturedHelper\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 CapturedHelper.value\n",
    );
    fixture.set(
        "UnusedCapture",
        TargetRole::Capture,
        "prelude\nimport Model\ndef UnusedCapture.value : BitVec 8 := BitVec.ofNat 8 99\n",
    );
    let mut checker = fixture.checker();
    let report = checker.run_target(&fixture.request).unwrap();
    assert_eq!(report["exactType"], true);
    assert_eq!(report["replay"], true);
    let identity = &report["moduleIdentities"][LIBRARY];
    assert!(identity.is_object(), "missing subject library identity");
    let admitted = checker.admitted().unwrap();
    assert!(admitted.library_modules.contains(LIBRARY));
    assert_eq!(
        identity["sourceSha256"],
        sha256_bytes(&fs::read(admitted.prefix.join("src/lean/Init/Data/Nat/Gcd.lean")).unwrap())
    );
    let expected_artifacts: Vec<_> = admitted.artifacts[LIBRARY]
        .to_wire()
        .iter()
        .flat_map(|parts| parts.iter())
        .map(|path| {
            serde_json::json!({
                "part": Path::new(path).file_name().unwrap().to_str().unwrap(),
                "sha256": sha256_bytes(&fs::read(path).unwrap())
            })
        })
        .collect();
    assert_eq!(identity["artifacts"], serde_json::json!(expected_artifacts));
    let subject = report["subjectClosure"].as_array().unwrap();
    assert!(subject.iter().any(|row| row["name"] == "Nat.gcd"));
    assert!(subject.iter().any(|row| row["module"] == "CapturedHelper"));
    for key in ["modelClosure", "specificationClosure"] {
        assert!(
            report[key]
                .as_array()
                .unwrap()
                .iter()
                .all(|row| row["module"] != LIBRARY),
            "subject-only library entered {key}"
        );
    }
    assert!(admitted.library_modules.contains(PROOF_LIBRARY));
    for module in [PROOF_LIBRARY, "Proof", "UnusedCapture"] {
        assert!(subject.iter().all(|row| row["module"] != module));
        assert!(report["moduleIdentities"].get(module).is_none());
    }
    assert!(
        report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .any(|source| source["module"] == "UnusedCapture")
    );
    assert_eq!(
        report["bindings"],
        serde_json::to_value(&fixture.request.bindings).unwrap()
    );
}

/// Original source paths are native filesystem inputs. Only their admitted
/// private copies and hashes belong in the inspector protocol.
#[cfg(unix)]
#[test]
fn accepts_native_source_paths_without_json_path_encoding() {
    use std::{ffi::OsString, os::unix::ffi::OsStringExt};

    let mut fixture = Fixture::new(PROOF);
    let module = fixture
        .request
        .modules
        .iter_mut()
        .find(|module| module.module == "Proof")
        .unwrap();
    let native = fixture
        .root
        .join("inputs")
        .join(OsString::from_vec(b"proof-\xff.lean".to_vec()));
    fs::rename(&module.source, &native).unwrap();
    module.source = native.clone();
    let original = fs::read(&native).unwrap();
    let mut permissions = fs::metadata(&native).unwrap().permissions();
    permissions.set_readonly(true);
    fs::set_permissions(&native, permissions).unwrap();
    fs::write(
        native.with_extension("olean"),
        b"untrusted adjacent artifact",
    )
    .unwrap();

    // Serializing the public host-side request as JSON is intentionally not
    // required. The inspector's narrower data must still audit this input.
    assert!(serde_json::to_value(&fixture.request).is_err());
    let report = fixture.run().unwrap();
    assert_eq!(report["exactType"], true);
    assert_eq!(report["replay"], true);
    assert_eq!(
        report["bindings"],
        serde_json::to_value(&fixture.request.bindings).unwrap()
    );
    let proof = report["sources"]
        .as_array()
        .unwrap()
        .iter()
        .find(|source| source["module"] == "Proof")
        .unwrap();
    assert_eq!(proof["sourceSha256"], sha256_bytes(&original));
    assert_eq!(fs::read(&native).unwrap(), original);
    assert!(fs::metadata(&native).unwrap().permissions().readonly());
    assert_eq!(
        fs::read(native.with_extension("olean")).unwrap(),
        b"untrusted adjacent artifact"
    );
}

/// The current selected labels are an explicit ASCII wire profile. That
/// restriction does not constrain names used by ordinary Lean proof helpers.
#[test]
fn accepts_unicode_and_apostrophe_helpers_behind_ascii_root() {
    let mut fixture = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         namespace Proof\n\
         theorem helper' : Expected.claim := by exact And.intro rfl BitVec.and_self\n\
         theorem θεώρημα : Expected.claim := helper'\n\
         theorem verify : Expected.claim := θεώρημα\n\
         end Proof\n",
    );
    let report = fixture.run().unwrap();
    assert_eq!(report["exactType"], true);
    assert_eq!(report["replay"], true);
    for name in ["Proof.helper'", "Proof.θεώρημα"] {
        fixture.request.theorem_name = name.into();
        let failure = fixture.run().unwrap_err();
        assert_eq!(failure.code, 1, "{failure}");
        assert_eq!(failure.phase, "target-input", "{failure}");
        assert!(failure.message.contains(name), "{failure}");
    }
}

#[test]
fn rejects_wrong_root_and_added_hypothesis() {
    Fixture::new("prelude\nimport Expected\ntheorem Proof.verify : True := True.intro\n")
        .reject("type differs");
    Fixture::new("prelude\nimport Expected\ntheorem Proof.verify (h : False) : Expected.claim := False.elim h\n").reject("type differs");
}

/// The root and Expected preconditions run before replay and before either
/// canonical comparison, so the extra declarations selected below need no
/// proof of the claim. Each request violates exactly one precondition.
#[test]
fn rejects_root_and_expected_kind_universe_and_sort_gates() {
    let mut f = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := by exact And.intro rfl BitVec.and_self\n\
         def Proof.definition : Expected.claim := Proof.verify\n\
         theorem Proof.polymorphic.{u} (_ : PUnit.{u}) : Expected.claim := Proof.verify\n",
    );
    f.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
         inductive Expected.inductiveClaim : Prop\n  | intro\n\
         def Expected.polymorphicClaim.{u} : Prop := PUnit.{u} → Expected.claim\n\
         def Expected.predicateClaim (_ : True) : Prop := Expected.claim\n",
    );
    let mut checker = f.accepted_checker();
    for (theorem, expected, text) in [
        (
            "Proof.definition",
            "Expected.claim",
            "target root must be a theorem",
        ),
        (
            "Proof.verify",
            "Expected.inductiveClaim",
            "Expected must be a definition",
        ),
        (
            "Proof.polymorphic",
            "Expected.claim",
            "target and Expected must have no universe parameters",
        ),
        (
            "Proof.verify",
            "Expected.polymorphicClaim",
            "target and Expected must have no universe parameters",
        ),
        (
            "Proof.verify",
            "Expected.predicateClaim",
            "Expected must have type Prop",
        ),
    ] {
        let mut request = f.request.clone();
        request.theorem_name = theorem.into();
        request.expected_declaration = expected.into();
        reject_inspected(&mut checker, request, text);
    }
}

/// Each canonical input must come from its own reviewed source role and have
/// no universe parameters. A request cannot select another role's declaration
/// or an installed one in its place.
#[test]
fn rejects_canonical_inputs_from_other_origins_or_with_universes() {
    let mut f = Fixture::new(PROOF);
    f.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 7\n\
         def Captured.polymorphic.{u} (_ : PUnit.{u}) : BitVec 8 := BitVec.ofNat 8 7\n",
    );
    let mut checker = f.accepted_checker();
    let edited = |edit: fn(&mut TargetAuditRequest)| {
        let mut request = f.request.clone();
        edit(&mut request);
        request
    };
    reject_inspected(
        &mut checker,
        edited(|r| r.canonical_root = "Expected.claim".into()),
        "incorrect canonical input origin Expected.claim",
    );
    reject_inspected(
        &mut checker,
        edited(|r| r.subject_declaration = "Spec.specs".into()),
        "incorrect canonical input origin Spec.specs",
    );
    reject_inspected(
        &mut checker,
        edited(|r| r.specification_declaration = "Captured.program".into()),
        "incorrect canonical input origin Captured.program",
    );
    // Foundation declarations have no target source role at all.
    reject_inspected(
        &mut checker,
        edited(|r| r.subject_declaration = "Nat.zero".into()),
        "incorrect canonical input origin Nat.zero",
    );
    reject_inspected(
        &mut checker,
        edited(|r| r.subject_declaration = "Captured.polymorphic".into()),
        "canonical input has universe parameters Captured.polymorphic",
    );
}

/// The inspector fixes the crate constructor instead of reading it from the
/// request, and neither a specification nor another non-model module can
/// supply it.
#[test]
fn rejects_crate_constructor_outside_model() {
    let mut f = Fixture::new(
        "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := True.intro\n",
    );
    f.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\ndef Trusted.MirSemantics.UnitTheorem (_ : Nat) : Prop := True\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nstructure Trusted.MirSemantics.Crate where\n  program : BitVec 8\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    f.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\ndef Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem 7\n",
    );
    // Specification preflight refuses declarations in reserved `Trusted`
    // before the run reaches `"target-audit"`.
    let e = f.run().unwrap_err();
    assert_eq!(e.code, 1, "{e}");
    assert_eq!(e.phase, "spec-preflight", "{e}");
    assert!(
        e.message
            .contains("cannot declare in reserved namespace Trusted in specification"),
        "{e}",
    );

    // Non-model modules outside `Specification` (such as `Expected`) still hit
    // the inspector's namespace-isolation guard in `"target-audit"` before
    // canonical-input origin validation.
    let mut f_expected = Fixture::new(
        "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := True.intro\n",
    );
    f_expected.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\ndef Trusted.MirSemantics.UnitTheorem (_ : Nat) : Prop := True\n",
    );
    f_expected.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\nstructure Trusted.MirSemantics.Crate where\n  program : BitVec 8\n\
         def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem 7\n",
    );
    f_expected.reject_audit(
        "non-model target module Expected cannot declare constant Trusted.MirSemantics.Crate",
    );
}

#[test]
fn rejects_specification_import_of_proof_helper() {
    let mut f = Fixture::new(PROOF);
    f.set(
        "Helper",
        TargetRole::Proof,
        "prelude\nimport Model\ndef Helper.spec (_ : BitVec 8) : Prop := True\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nimport Helper\ndef Spec.specs := Helper.spec\n",
    );
    f.reject("cannot import Helper");
}

#[test]
fn rejects_changed_source_and_authority_assignment() {
    let mut f = Fixture::new(PROOF);
    fs::write(&f.request.modules[0].source, "prelude\n").unwrap();
    f.reject("source digest differs");
    f = Fixture::new(PROOF);
    f.request
        .modules
        .iter_mut()
        .find(|m| m.module == "Expected")
        .unwrap()
        .role = TargetRole::Proof;
    f.reject("authority roles");
}

/// A source-role check also runs on compiled definition edges, independently
/// from Rust's import admission. A forged, axiom-free dependency with an
/// ill-typed body is then rejected by fresh kernel replay.
#[test]
fn rejects_compiled_role_violation_and_forged_dependency() {
    use anneal_audit::InspectorRequest;
    use serde_json::json;
    let mut f = Fixture::new(PROOF);
    f.set(
        "Helper",
        TargetRole::Specification,
        "prelude\nimport Model\ndef Helper.intent (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nimport Helper\ndef Spec.specs := Helper.intent\n",
    );
    let mut checker = f.checker();
    checker.run_target(&f.request).unwrap();
    let mut changed_roles = f.request.clone();
    changed_roles
        .modules
        .iter_mut()
        .find(|m| m.module == "Helper")
        .unwrap()
        .role = TargetRole::Proof;
    let failure = checker
        .inspect(InspectorRequest::TargetAudit {
            request: changed_roles,
        })
        .unwrap_err();
    assert_eq!(failure.code, 1, "{failure}");
    assert!(failure.message.contains("authority violation"), "{failure}");
    let adm = checker.admitted().unwrap();
    let artifacts: Vec<_> = adm
        .artifacts
        .iter()
        .map(|(n, a)| json!([n, a.to_wire()]))
        .collect();
    let output = adm.artifacts["Proof"].to_wire()[0][0].clone();
    let request_path = checker.stage().join("forged-dependency-input.json");
    fs::write(
        &request_path,
        serde_json::to_vec(&json!({
            "sysroot": adm.prefix, "artifacts": artifacts
        }))
        .unwrap(),
    )
    .unwrap();
    let script = checker.stage().join("ForgeDependency.lean");
    // This trusted test producer deliberately bypasses kernel insertion checks.
    // Its emitted module imports only the ordinary narrow proof dependencies;
    // Lean metaprogram libraries do not enter the audit's admitted environment.
    fs::write(&script, r#"
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let [input, output] := args | throw <| IO.userError "expected paths"
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let sysroot ← IO.ofExcept <| j.getObjValAs? String "sysroot"
  initSearchPath sysroot
  let entries ← IO.ofExcept <| j.getObjValAs?
    (Array (String × Array (Array String))) "artifacts"
  let arts := entries.foldl (init := ({} : NameMap ImportArtifacts)) fun acc (n,parts) =>
    acc.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  let env ← importModules #[{module := `Expected}, {module := `Init.Data.BitVec.Lemmas}] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let env := env.setMainModule `Proof |>.setExporting false
  let helper := Declaration.thmDecl { name := `Proof.forgedHelper, levelParams := [], type := mkConst `False, value := mkConst `True.intro }
  let env ← match env.addDeclCore 0 0 helper none false with
    | .ok next => pure next
    | .error _ => throw <| IO.userError "could not add forged helper"
  let proof := mkApp2 (mkConst `False.elim [Level.zero])
    (mkConst `Expected.claim) (mkConst `Proof.forgedHelper)
  let root := Declaration.thmDecl { name := `Proof.verify, levelParams := [], type := mkConst `Expected.claim, value := proof }
  let env ← match env.addDeclCore 0 0 root none false with
    | .ok next => pure next
    | .error _ => throw <| IO.userError "could not add forged root"
  writeModule env output false
"#).unwrap();
    checker
        .process(
            "forge-fixture",
            &[
                "--run".into(),
                script.to_string_lossy().into_owned(),
                request_path.to_string_lossy().into_owned(),
                output,
            ],
        )
        .unwrap();
    let failure = checker
        .inspect(InspectorRequest::TargetAudit {
            request: f.request.clone(),
        })
        .unwrap_err();
    // Kernel exceptions remain refusals and are reported conservatively as
    // operational, even for this deliberately invalid serialized proof.
    // The explicit role-policy violation above remains code 1.
    assert_eq!(failure.code, 2, "{failure}");
    assert!(
        failure.message.contains("kernel replay rejected"),
        "{failure}"
    );
    assert!(failure.message.contains("Proof.forgedHelper"), "{failure}");
}

/// Compiled role edges from every reviewed source role are rechecked after
/// Rust's import admission. Each helper compiles with its importer's role; one
/// inspection at a time relabels a single helper to a role its importer may
/// not depend on.
#[test]
fn rejects_compiled_edges_from_each_reviewed_role() {
    let mut f = Fixture::new(PROOF);
    f.set(
        "ModelHelper",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\ndef ModelHelper.seven : Nat := 7\n",
    );
    f.set("Model", TargetRole::Model, "prelude\nimport Init.Data.BitVec.Basic\nimport ModelHelper\nnamespace Trusted.MirSemantics\nstructure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\ndef UnitTheorem (c : Crate) : Prop := c.program.toNat = ModelHelper.seven ∧ c.specs c.program\n");
    f.set(
        "CaptureHelper",
        TargetRole::Capture,
        "prelude\nimport Model\ndef CaptureHelper.value : Nat := 7\n",
    );
    f.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\nimport CaptureHelper\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 CaptureHelper.value\n",
    );
    f.set(
        "SpecHelper",
        TargetRole::Specification,
        "prelude\nimport Model\ndef SpecHelper.intent (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\nimport SpecHelper\ndef Spec.specs := SpecHelper.intent\n",
    );
    f.set("ExpectedHelper", TargetRole::Expected, "prelude\nimport Captured\nimport Spec\ndef ExpectedHelper.claim : Prop := Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n");
    f.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport ExpectedHelper\ndef Expected.claim : Prop := ExpectedHelper.claim\n",
    );
    let mut checker = f.accepted_checker();
    for (helper, role, edge) in [
        (
            "ModelHelper",
            TargetRole::Capture,
            "Trusted.MirSemantics.UnitTheorem references ModelHelper.seven",
        ),
        (
            "CaptureHelper",
            TargetRole::Specification,
            "Captured.program references CaptureHelper.value",
        ),
        (
            "SpecHelper",
            TargetRole::Capture,
            "Spec.specs references SpecHelper.intent",
        ),
        (
            "ExpectedHelper",
            TargetRole::Proof,
            "Expected.claim references ExpectedHelper.claim",
        ),
    ] {
        let mut request = f.request.clone();
        request
            .modules
            .iter_mut()
            .find(|m| m.module == helper)
            .unwrap()
            .role = role;
        reject_inspected(
            &mut checker,
            request,
            &format!("target authority violation {edge}"),
        );
    }
}
