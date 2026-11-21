// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact target-root, source binding and authority separation regressions.

use std::{
    fs,
    path::{Path, PathBuf},
};

use anneal_audit::{
    Checker, Failure, Json, TargetAuditRequest, TargetBindings, TargetModule, TargetRole,
    sha256_bytes,
};

struct Fixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
    request: TargetAuditRequest,
}
impl Fixture {
    fn new(proof: &str) -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().to_path_buf();
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        for rel in [
            "trusted/audit/TrustedBoundary.lean",
            "trusted/audit/library-lock.json",
            "trusted/lean/foundation-lock.json",
            "trusted/lean/lean-toolchain",
        ] {
            fs::create_dir_all(root.join(rel).parent().unwrap()).unwrap();
            fs::copy(repo.join(rel), root.join(rel)).unwrap();
        }
        fs::write(
            root.join("trusted/lean/Trusted.lean"),
            "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\n",
        )
        .unwrap();
        let h = sha256_bytes(b"fixture compilation");
        let mut f = Self {
            _dir: dir,
            root,
            request: TargetAuditRequest {
                modules: vec![],
                theorem_module: "Proof".into(),
                theorem_name: "Proof.verify".into(),
                expected_module: "Expected".into(),
                expected_declaration: "Expected.claim".into(),
                canonical_root: "Trusted.MirSemantics.UnitTheorem".into(),
                subject_declaration: "Captured.program".into(),
                specification_declaration: "Spec.specs".into(),
                bindings: TargetBindings {
                    request_sha256: h.clone(),
                    capture_sha256: h.clone(),
                    model_manifest_sha256: h.clone(),
                    specification_manifest_sha256: h,
                },
            },
        };
        f.set("Model", TargetRole::Model, "prelude\nimport Init.Data.BitVec.Basic\nnamespace Trusted.MirSemantics\nstructure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\ndef UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n");
        f.set(
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
        );
        f.set(
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        );
        f.set("Expected", TargetRole::Expected, "prelude\nimport Captured\nimport Spec\ndef Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n");
        f.set("Proof", TargetRole::Proof, proof);
        f
    }
    fn set(&mut self, name: &str, role: TargetRole, source: &str) {
        let path = self.root.join("inputs").join(format!("{name}.lean"));
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, source).unwrap();
        self.request.modules.retain(|m| m.module != name);
        self.request.modules.push(TargetModule {
            module: name.into(),
            source: path,
            expected_sha256: sha256_bytes(source.as_bytes()),
            role,
        });
    }
    fn run(&self) -> Result<Json, Failure> {
        Checker::new(&self.root, None)
            .unwrap()
            .run_target(&self.request)
    }
    fn reject(&self, text: &str) {
        let e = self.run().unwrap_err();
        assert_eq!(e.code, 1, "{e}");
        assert!(e.message.contains(text), "{e}");
    }
    /// Assert a policy refusal from the inspector rather than from compilation.
    fn reject_audit(&self, text: &str) {
        let e = self.run().unwrap_err();
        assert_eq!(e.code, 1, "{e}");
        assert_eq!(e.phase, "target-audit", "{e}");
        assert!(e.message.contains(text), "{e}");
    }
    /// Compile and accept this fixture's own request. Later inspections of
    /// edited requests reuse the returned checker's compiled artifacts.
    fn accepted_checker(&self) -> Checker {
        let mut checker = Checker::new(&self.root, None).unwrap();
        checker.run_target(&self.request).unwrap();
        checker
    }
}

/// Inspect already compiled artifacts with an edited request and assert a
/// policy refusal from the inspector.
fn reject_inspected(checker: &mut Checker, request: TargetAuditRequest, text: &str) {
    use anneal_audit::InspectorRequest;
    let failure = checker
        .inspect(InspectorRequest::TargetAudit { request })
        .unwrap_err();
    assert_eq!(failure.code, 1, "{failure}");
    assert_eq!(failure.phase, "target-audit", "{failure}");
    assert!(failure.message.contains(text), "{failure}");
}
const PROOF: &str = "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\nmacro \"audit_finish\" : tactic => `(tactic| exact And.intro rfl BitVec.and_self)\ntheorem Proof.verify : Expected.claim := by audit_finish\n";

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
    let mut checker = Checker::new(&fixture.root, None).unwrap();
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
/// request, and a reviewed specification cannot supply it.
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
    // Non-model modules cannot declare constants in the `Trusted` namespace at
    // all, so defining `Trusted.MirSemantics.Crate` in `Spec` is refused by
    // the namespace-isolation guard before canonical-input origin validation.
    f.reject_audit(
        "non-model target module Spec cannot declare constant Trusted.MirSemantics.Crate",
    );
}

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
    let mut checker = Checker::new(&f.root, None).unwrap();
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

/// Exercise actual pinned compiler failure reporting through target
/// compilation. These authored sources deliberately use target elaboration's
/// intact-host assumption; repository preflight would refuse them before
/// compilation.
#[test]
fn classifies_native_failures_and_resource_limits_as_operational() {
    for body in [
        "#eval (Array.replicate (2^128) (0 : UInt8)).size",
        "def wrong : Nat := \"bad\"\n#eval (Array.replicate (2^128) (0 : UInt8)).size",
        "set_option maxHeartbeats 1 in\nexample : (List.range 10000).foldl Nat.add 0 = 49995000 := by decide",
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
        if body.contains("Array.replicate") {
            assert!(
                failure.message.contains("INTERNAL PANIC: out of memory"),
                "{failure}"
            );
        } else {
            assert!(
                failure.message.contains("runtime.maxHeartbeats"),
                "{failure}"
            );
        }
        if body.starts_with("def wrong") {
            assert!(failure.message.contains("Type mismatch"), "{failure}");
        }
    }
}

/// Exercise the inspector's final gate with serialized library artifacts.
/// The fixture deliberately bypasses hash admission after a successful public
/// run; it establishes inventory policy, not a public-input false-claim
/// exploit.
fn target_library_inventory_case(module: &str, mode: &str, rejection: Option<&str>) {
    use std::collections::BTreeMap;

    use anneal_audit::{ImportEdge, InspectorRequest, ModuleArtifacts, PARTS};
    use serde_json::json;

    let f = Fixture::new(PROOF);
    let mut checker = Checker::new(&f.root, None).unwrap();
    checker.run_target(&f.request).unwrap();
    let adm = checker.admitted().unwrap();
    let foundation: Vec<_> = adm
        .foundation_modules()
        .into_iter()
        .map(str::to_string)
        .collect();
    let artifacts: Vec<_> = adm
        .artifacts
        .iter()
        .map(|(n, a)| json!([n, a.to_wire()]))
        .collect();
    let proof_output = adm.artifacts["Proof"].to_wire()[0][0].clone();
    let input = checker.stage().join("library-inventory-input.json");
    fs::write(
        &input,
        serde_json::to_vec(&json!({
            "sysroot": adm.prefix, "foundation": foundation, "artifacts": artifacts,
        }))
        .unwrap(),
    )
    .unwrap();
    let output = checker.stage().join(format!("{module}.olean"));
    let producer = checker.stage().join("ForgeTargetLibrary.lean");
    fs::write(&producer, r#"
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let [input, output, proofOutput, moduleText, mode] := args
    | throw <| IO.userError "expected fixture paths and mode"
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let sysroot ← IO.ofExcept <| j.getObjValAs? String "sysroot"
  initSearchPath sysroot
  let names ← IO.ofExcept <| j.getObjValAs? (Array String) "foundation"
  let roots := names.map fun n => { module := n.toName : Import }
  let entries ← IO.ofExcept <| j.getObjValAs?
    (Array (String × Array (Array String))) "artifacts"
  let arts := entries.foldl (init := ({} : NameMap ImportArtifacts)) fun acc (n, parts) =>
    acc.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  let privateEnv ← importModules (roots.push {module := `Proof}) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let some (.thmInfo original) := privateEnv.checked.get.find? `List.drop.eq_def
    | throw <| IO.userError "missing genuine pinned theorem"
  let some (.thmInfo root) := privateEnv.checked.get.find? `Proof.verify
    | throw <| IO.userError "missing genuine target theorem"
  let module := moduleText.toName
  let publicEnv ← importModules roots {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .exported) (arts := arts)
  let publicEnv := publicEnv.setMainModule module |>.setExporting false
  if mode == "missing" || mode == "foundation-extra" then
    -- A new name gets its origin from the earlier IR-only module while its
    -- valid kernel declaration comes from a later module. Existing foundation
    -- names instead keep their prior origin and are an accepted control.
    let extraName := if mode == "missing" then `TargetInventoryWitness.logical else
      `List.drop.eq_def
    if publicEnv.header.isModule then
      let levels : Array OLeanLevel := #[.exported, .server, .private]
      let parts ← levels.mapM fun level => do
        let data ← mkModuleData publicEnv level
        let data := if level == .private then
          { data with extraConstNames := #[extraName] } else data
        pure (level.adjustFileName output, data)
      saveModuleDataParts module parts
    else
      let data ← mkModuleData publicEnv
      saveModuleData output module { data with extraConstNames := #[extraName] }
    if mode == "missing" then
      let provider := publicEnv.setMainModule `ZZZZInventoryProvider
      let declaration := Declaration.thmDecl {name := extraName, levelParams := [], type := mkConst `True, value := mkConst `True.intro}
      let provider ← match provider.addDeclCore 0 0 declaration none true with
        | .ok next => pure next
        | .error _ => throw <| IO.userError "valid inventory provider was rejected"
      writeModule provider ((System.FilePath.mk output).parent.get! / "ZZZZInventoryProvider.olean") false
  else
    let helper := if mode == "source-edge" then `Proof.verify else
      Name.str module "onlyAlternate"
    let helperType := if mode == "source-edge" then root.type else
      if mode == "extra-axiom" then mkConst `False else mkConst `True
    let helperDecl := if mode == "extra-axiom" then
      Declaration.axiomDecl {name := helper, levelParams := [], type := helperType, isUnsafe := false}
    else
      Declaration.thmDecl {name := helper, levelParams := [], type := helperType, value := mkConst `True.intro}
    let publicEnv ← if mode == "source-edge" then pure publicEnv else
      match publicEnv.addDeclCore 0 0 helperDecl none false with
      | .ok next => pure next
      | .error _ => throw <| IO.userError "could not add alternate-only helper"
    let metadataOnly := mode == "metadata-all" || mode == "metadata-levels"
    let value := if metadataOnly then original.value else
      if mode == "bad" then mkConst `True.intro else
        Expr.letE `_alternate helperType (mkConst helper) original.value false
    let all := if mode == "metadata-all" then original.all ++ [helper] else original.all
    let levelParams := if mode == "metadata-levels" then
      original.levelParams ++ [`metadataUnused] else original.levelParams
    let declaration := Declaration.thmDecl { original with value, all, levelParams }
    let publicEnv ← match publicEnv.addDeclCore 0 0 declaration none false with
      | .ok next => pure next
      | .error _ => throw <| IO.userError "could not add library inventory theorem"
    writeModule publicEnv output false
  -- Retain a genuine logical reference in the stored target proof. The body
  -- stays valid, but a mere unused import cannot make this regression pass.
  let levels := if mode == "missing" then [] else
    original.levelParams.map fun _ => Level.zero
  let referenceName := if mode == "missing" then `TargetInventoryWitness.logical else original.name
  let referenceType := if mode == "missing" then mkConst `True else
    original.type.instantiateLevelParams original.levelParams levels
  let proof := Expr.letE `_pinned referenceType (mkConst referenceName levels) root.value false
  let proofEnv ← importModules #[{module := `Expected}, {module := `Init.Data.BitVec.Lemmas}] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let proofEnv := proofEnv.setMainModule `Proof |>.setExporting false
  let proofEnv ← match proofEnv.addDeclCore 0 0 (.thmDecl {root with value := proof}) none false with
    | .ok next => pure next
    | .error _ => throw <| IO.userError "could not retain the logical library reference"
  writeModule proofEnv proofOutput false
"#).unwrap();
    checker
        .process(
            "library-inventory-fixture",
            &[
                "--run".into(),
                producer.to_string_lossy().into_owned(),
                input.to_string_lossy().into_owned(),
                output.to_string_lossy().into_owned(),
                proof_output,
                module.into(),
                mode.into(),
            ],
        )
        .unwrap();
    let libraries = if mode == "missing" {
        vec![module, "ZZZZInventoryProvider"]
    } else {
        vec![module]
    };
    for library in libraries {
        let mut available = BTreeMap::new();
        for part in PARTS {
            let path = output.parent().unwrap().join(format!("{library}.{part}"));
            if path.exists() {
                available.insert(part, path.to_string_lossy().into_owned());
            }
        }
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.insert(
            library.into(),
            ModuleArtifacts::from_available(&available, "fixture", || {
                "missing forged library artifact".into()
            })
            .unwrap(),
        );
        adm.library_modules.insert(library.into());
        adm.graph.insert(
            library.into(),
            foundation
                .iter()
                .cloned()
                .map(|module| ImportEdge {
                    module,
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                })
                .collect(),
        );
    }
    let result = checker.inspect(InspectorRequest::TargetAudit {
        request: f.request.clone(),
    });
    // Optional evidence retention lets another inspector replay the exact
    // serialized input. Ordinary tests retain nothing; requested fixtures stay
    // in the caller's temporary area until that caller removes them.
    if let Some(directory) = std::env::var_os("ANNEAL_AUDIT_RETAIN_FIXTURES") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(
            directory.join(format!("{module}-{mode}.json")),
            serde_json::to_vec_pretty(&json!({
                "stage": checker.stage(), "fixture": f.root,
                "result": result.as_ref().ok(),
                "failure": result.as_ref().err().map(ToString::to_string),
            }))
            .unwrap(),
        )
        .unwrap();
        std::mem::forget(checker);
        std::mem::forget(f);
    }
    match rejection {
        Some(message) => {
            let failure = result.unwrap_err();
            // Metadata-only conflicts fail in the pinned importer; bad proof
            // values fail in kernel checking. Both exception paths remain
            // operational, while explicit axiom/source-edge policy stays 1.
            let expected_code = if mode.starts_with("metadata-") || mode == "bad" {
                2
            } else {
                1
            };
            assert_eq!(failure.code, expected_code, "{failure}");
            assert!(failure.message.contains(message), "{failure}");
        }
        None => {
            let report = result.unwrap();
            assert_eq!(report["exactType"], true);
            if mode != "foundation-extra" {
                assert!(report["checkedAlternateProofs"].as_u64().unwrap() >= 2);
            }
        }
    }
}

#[test]
fn rejects_reached_library_name_missing_from_inventory() {
    target_library_inventory_case(
        "AAAAMissingInventory",
        "missing",
        Some("uninventoried target library dependency TargetInventoryWitness.logical"),
    );
}

#[test]
fn rejects_discarded_and_selected_library_proof_bodies() {
    for module in ["AAAAAlternate", "ZZZZAlternate"] {
        target_library_inventory_case(
            module,
            "bad",
            Some("alternate pinned theorem proof check List.drop.eq_def"),
        );
    }
}

#[test]
fn checks_alternate_only_dependencies_and_accepts_valid_proofs() {
    target_library_inventory_case("AAAAAlternate", "extra-axiom", Some("unapproved axiom"));
    target_library_inventory_case(
        "AAAAAlternate",
        "source-edge",
        Some("installed library List.drop.eq_def references target source Proof.verify"),
    );
    target_library_inventory_case("AAAAAlternate", "valid", None);
}

/// An IR-only reexport cannot replace the earlier foundation origin. Rejecting
/// this control would mistake harmless metadata for a missing library body.
#[test]
fn accepts_ir_extra_name_for_existing_foundation_declaration() {
    target_library_inventory_case("ZZZZFoundationExtra", "foundation-extra", None);
}

/// The importer rejects conflicting duplicate metadata before inventory policy
/// runs. Probe the actual staged helper directly so that prerequisite cannot
/// mask an early-return regression. Appending a unit probe leaves the inspected
/// implementation intact and adds no inspector mode or production API.
#[test]
fn reconciles_equal_theorem_bodies_before_discarding_inventory_metadata() {
    let fixture = Fixture::new(PROOF);
    let mut checker = Checker::new(&fixture.root, None).unwrap();
    let inspector = checker.tool_admission().unwrap().inspector.clone();
    let mut source = fs::read_to_string(inspector).unwrap();
    source.push_str(
        r#"

#eval do
  let original : Lean.TheoremVal := {
    name := `MetadataWitness, levelParams := [], type := Lean.mkConst `True,
    value := Lean.mkConst `True.intro, all := [`MetadataWitness] }
  let stored := Lean.ConstantInfo.thmInfo original
  let unchanged ← TrustedBoundary.inventoryAlternates stored stored true
  unless unchanged.isEmpty do throw <| IO.userError "identical theorem produced alternates"
  let changedProof := Lean.Expr.letE `h original.type original.value (.bvar 0) false
  let alternate := Lean.ConstantInfo.thmInfo { original with value := changedProof }
  let proofs ← TrustedBoundary.inventoryAlternates stored alternate true
  unless proofs.size == 2 && proofs[0]!.value? true == stored.value? true &&
      proofs[1]!.value? true == alternate.value? true do
    throw <| IO.userError "different pinned proofs were not both retained"
  let deps ← TrustedBoundary.declarationEdges (.thmInfo {
    original with all := original.all ++ [`UnapprovedMetadataDependency] })
  unless deps.contains `UnapprovedMetadataDependency do
    throw <| IO.userError "metadata witness does not add a dependency edge"
  let mut accepted : Array String := #[]
  for (label, changed) in #[
      ("all", { original with all := original.all ++ [`UnapprovedMetadataDependency] }),
      ("levelParams", { original with levelParams := [`u] })] do
    let ci := Lean.ConstantInfo.thmInfo changed
    unless stored.type == ci.type && stored.value? true == ci.value? true do
      throw <| IO.userError "metadata fixture also changed the theorem expression"
    for (a, b) in #[(stored, ci), (ci, stored)] do
      let rejected ← try
        let _ ← TrustedBoundary.inventoryAlternates a b true
        pure false
      catch error =>
        unless error.toString.startsWith "policy:inconsistent pinned theorem metadata" do
          throw error
        pure true
      unless rejected do accepted := accepted.push label
  unless accepted.isEmpty do
    throw <| IO.userError s!"equal-body metadata was accepted: {accepted}"
"#,
    );
    let probe = checker.stage().join("TheoremMetadata.lean");
    fs::write(&probe, source).unwrap();
    checker
        .process(
            "theorem-metadata-unit",
            &[probe.to_string_lossy().into_owned()],
        )
        .unwrap();
}

/// This is an importer-refusal control, not an importer-reachable false-proof
/// exploit. The direct helper regression above tests Anneal's own invariant.
#[test]
fn pinned_importer_rejects_equal_body_metadata_conflicts() {
    for mode in ["metadata-all", "metadata-levels"] {
        target_library_inventory_case(
            "AAAAAlternate",
            mode,
            Some("environment already contains 'List.drop.eq_def'"),
        );
    }
}

/// Exercise typed result handling without a resource race or large allocation.
/// Existing invalid-proof fixtures separately exercise actual kernel/replay
/// exceptions through the inspector protocol.
#[test]
fn kernel_result_channels_preserve_success_mismatch_and_operational_error() {
    let fixture = Fixture::new(PROOF);
    let mut checker = Checker::new(&fixture.root, None).unwrap();
    let inspector = checker.tool_admission().unwrap().inspector.clone();
    let mut source = fs::read_to_string(inspector).unwrap();
    source.push_str(
        r#"

#eval do
  TrustedBoundary.requireKernelEquality "success" "mismatch" (.ok true)
  let policy ← try
    TrustedBoundary.requireKernelEquality "false" "mismatch" (.ok false)
    pure false
  catch error => pure (error.toString == "policy:mismatch")
  unless policy do throw <| IO.userError "completed false equality lost policy status"
  let operational ← try
    TrustedBoundary.requireKernelEquality "resource" "mismatch" (.error .excessiveMemory)
    pure false
  catch error => pure (error.toString.startsWith "kernel operation failed (resource):")
  unless operational do throw <| IO.userError "kernel exception lost operational status"
  let value ← TrustedBoundary.kernelResult "value" (α := Nat) (.ok 7)
  unless value == 7 do throw <| IO.userError "kernel success value changed"
"#,
    );
    let probe = checker.stage().join("KernelResultChannels.lean");
    fs::write(&probe, source).unwrap();
    checker
        .process(
            "kernel-result-channels",
            &[probe.to_string_lossy().into_owned()],
        )
        .unwrap();
}
