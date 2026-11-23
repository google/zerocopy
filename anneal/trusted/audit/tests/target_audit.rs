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
                allow_sorry_in_proof: false,
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
        "def wrong : Nat := \"bad\"\nset_option maxHeartbeats 1 in\nexample : (List.range 10000).foldl Nat.add 0 = 49995000 := by decide",
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
            // Lean 4.34.1 elaborates commands on a worker task while the main
            // thread drains JSON diagnostics in `SnapshotTree.runAndReport`.
            // Under CPU contention, the native OOM's `std::exit(1)` can
            // terminate the process before the main thread buffers the earlier
            // `Type mismatch` JSON on stdout; classification remains code 2
            // either way, and `stage::process_tests` deterministically covers
            // combined stdout JSON + stderr `INTERNAL PANIC`.
        } else {
            assert!(
                failure.message.contains("runtime.maxHeartbeats"),
                "{failure}"
            );
            if body.starts_with("def wrong") {
                assert!(failure.message.contains("Type mismatch"), "{failure}");
            }
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
    let output = checker.stage().join("lib").join(format!("{module}.olean"));
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

/// `"headers"` rejects Lean 4 module-system headers (`module`), import
/// modifiers (`import all`, `public import`, `meta import`), and
/// `Lean.*`/`Lake.*` imports with exit code 1, while accepting omitted
/// `prelude` (synthetic non-meta + meta `Init` pair) in unpinned mode.
#[test]
fn headers_rejects_module_system_modifiers_and_lean_lake_and_allows_no_prelude() {
    for (label, header, expected) in [
        (
            "module",
            "module\nprelude\nimport Model\n",
            "module system header",
        ),
        (
            "import-all",
            "prelude\nimport all Model\n",
            "header parser error",
        ),
        (
            "public-import",
            "prelude\npublic import Model\n",
            "header parser error",
        ),
        (
            "meta-import",
            "prelude\nmeta import Model\n",
            "header parser error",
        ),
        (
            "lean-import",
            "prelude\nimport Lean.Elab\nimport Model\n",
            "disallowed sysroot import",
        ),
        (
            "lake-import",
            "prelude\nimport Lake.Build\nimport Model\n",
            "disallowed sysroot import",
        ),
    ] {
        let mut f = Fixture::new(PROOF);
        f.set(
            "Spec",
            TargetRole::Specification,
            &format!("{header}def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"),
        );
        let err = f.run().unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "headers", "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }

    // Direct unit probe of `validateTargetImports` confirming importAll,
    // !isExported, unpaired meta Init, meta non-Init, and Lean/Lake rejections
    // as well as acceptance of the synthetic `!hasPrelude` Init pair.
    let probe_fixture = Fixture::new(PROOF);
    let mut probe_checker = Checker::new(&probe_fixture.root, None).unwrap();
    let inspector = probe_checker.tool_admission().unwrap().inspector.clone();
    let mut probe_src = fs::read_to_string(inspector).unwrap();
    probe_src.push_str(
        r#"

#eval do
  let okPair : Array Lean.Import := #[
    { module := `Init, importAll := false, isExported := true, isMeta := false },
    { module := `Init, importAll := false, isExported := true, isMeta := true }
  ]
  TrustedBoundary.validateTargetImports "Spec" okPair
  let badCases : Array (String × Array Lean.Import × String) := #[
    ("importAll", #[{ module := `Init, importAll := true, isExported := true, isMeta := false }], "import modifiers"),
    ("private", #[{ module := `Init, importAll := false, isExported := false, isMeta := false }], "import modifiers"),
    ("unpairedMetaInit", #[{ module := `Init, importAll := false, isExported := true, isMeta := true }], "meta import Init"),
    ("metaNonInit", #[{ module := `Init, importAll := false, isExported := true, isMeta := false }, { module := `Model, importAll := false, isExported := true, isMeta := true }], "meta import Model"),
    ("lean", #[{ module := `Lean.Elab, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("lake", #[{ module := `Lake, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import")
  ]
  for (label, imps, want) in badCases do
    let ok ← try
      TrustedBoundary.validateTargetImports "Spec" imps
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{label}: unexpected error {msg}"
      pure true
    unless ok do
      throw <| IO.userError s!"{label}: unexpectedly accepted"
"#,
    );
    let probe_path = probe_checker.stage().join("ValidateTargetImports.lean");
    fs::write(&probe_path, probe_src).unwrap();
    probe_checker
        .process(
            "validate-target-imports-unit",
            &[probe_path.to_string_lossy().into_owned()],
        )
        .unwrap();

    // Unpinned mode: omitting `prelude` produces Lean 4's synthetic
    // `Init(isMeta = false)` + `Init(isMeta = true)` pair and must pass
    // `"headers"`, `"spec-preflight"`, and `"target-audit"` end-to-end.
    let mut f = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "import Model\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    let report = checker.run_target(&f.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(report["sorryDeclarations"], serde_json::json!([]));
}

/// Live parse-tree round-trip verification against the pinned Lean parser plus
/// comprehensive negative tests for `"spec-preflight"` covering commands,
/// modifiers, lexical scopes, attributes, deriving, `set_option`, tactics, and
/// term/quotation guards.
#[test]
fn spec_preflight_parse_tree_round_trip_and_negative_guards() {
    // 1. Live parse-tree round-trip probe + exhaustive 62-vector negative
    //    check against the real `TrustedBoundary.parseAndInspectSpecCommands`
    //    on one loaded `Init` + `Std` parser environment (fast in CI).
    let spec_base = "def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    let vectors: &[(&str, &str, &str)] = &[
        ("eval-cmd", "#eval 1\n", "unsupported command"),
        (
            "axiom-decl",
            "axiom badAx : True\n",
            "unsupported declaration kind",
        ),
        (
            "opaque-decl",
            "opaque badOp : Nat := 0\n",
            "unsupported declaration kind",
        ),
        (
            "example-decl",
            "example : True := trivial\n",
            "unsupported declaration kind",
        ),
        (
            "macro-cmd",
            "macro \"m\" : term => `(0)\n",
            "unsupported command",
        ),
        (
            "syntax-cmd",
            "syntax \"mykw\" : term\n",
            "unsupported command",
        ),
        ("init-cmd", "initialize pure ()\n", "unsupported command"),
        (
            "notation-cmd",
            "notation \"x99\" => 1\n",
            "unsupported command",
        ),
        (
            "in-bad-lhs",
            "namespace N in def f : Nat := 0\n",
            "unsupported command on LHS of `in`",
        ),
        (
            "in-bad-rhs",
            "open Nat in namespace N\n",
            "unsupported command inside `in`",
        ),
        (
            "mutual-nested-sec",
            "mutual\nsection S\nend S\nend\n",
            "unsupported mutual-block shape",
        ),
        (
            "partial-def",
            "partial def p (n : Nat) : Nat := p n\n",
            "unsupported declaration modifier",
        ),
        (
            "unsafe-def",
            "unsafe def u : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "meta-def",
            "meta def m : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "public-def",
            "public def pub : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "term-unsafe",
            "def u2 : Nat := unsafe 0\n",
            "disallowed modifier",
        ),
        (
            "public-section",
            "public section S\nend S\n",
            "unsupported section/namespace modifier",
        ),
        (
            "meta-section",
            "meta section S\nend S\n",
            "unsupported section/namespace modifier",
        ),
        (
            "partial-fixpoint",
            "def pf (n : Nat) : Nat := pf n\npartial_fixpoint\n",
            "disallowed modifier",
        ),
        (
            "unsafe-rec-ident",
            "def foo._unsafe_rec : Nat := 0\n",
            "_unsafe_rec",
        ),
        ("open-io", "open IO\n", "forbidden namespace IO"),
        ("open-lean", "open Lean\n", "forbidden namespace Lean"),
        ("open-lake", "open Lake\n", "forbidden namespace Lake"),
        ("open-system", "open System\n", "forbidden namespace System"),
        (
            "open-platform-all",
            "open System.Platform\n",
            "forbidden namespace System.Platform",
        ),
        (
            "open-platform-target",
            "open System.Platform (target)\n",
            "disallowed open item System.Platform.target",
        ),
        (
            "open-platform-hiding",
            "open System.Platform hiding target\n",
            "forbidden namespace System.Platform",
        ),
        (
            "open-scoped-io",
            "open scoped IO\n",
            "forbidden namespace IO",
        ),
        ("ns-io", "namespace IO\nend IO\n", "disallowed reference IO"),
        (
            "term-open-io",
            "def x : Nat := open IO in 0\n",
            "forbidden namespace IO",
        ),
        (
            "export-platform-target",
            "export System.Platform (target)\n",
            "disallowed export item System.Platform.target",
        ),
        (
            "ref-io",
            "def x := IO.println\n",
            "disallowed reference IO.println",
        ),
        (
            "ref-platform-target",
            "def x := System.Platform.target\n",
            "disallowed reference System.Platform.target",
        ),
        (
            "attr-impl-by",
            "@[implemented_by Nat.add] def f := Nat.add\n",
            "unsupported attribute implemented_by",
        ),
        (
            "attr-extern",
            "@[extern \"c_fn\"] def f (x : Nat) : Nat := x\n",
            "unsupported attribute kind",
        ),
        (
            "attr-csimp",
            "@[csimp] theorem t : Nat.add = Nat.add := rfl\n",
            "unsupported attribute csimp",
        ),
        (
            "attr-scoped-simp",
            "@[scoped simp] theorem t : True := trivial\n",
            "only global or local attributes",
        ),
        (
            "attr-erase-extern",
            "attribute [-extern] Nat.add\n",
            "unsupported attribute removal extern",
        ),
        (
            "deriving-unknown",
            "structure S where\n  x : Nat\nderiving UnknownClass\n",
            "unsupported deriving class",
        ),
        (
            "opt-skip-kernel",
            "set_option debug.skipKernelTC true\n",
            "unsupported option debug.skipKernelTC",
        ),
        (
            "opt-non-num",
            "set_option maxHeartbeats true\n",
            "requires a numeric literal",
        ),
        (
            "opt-non-bool",
            "set_option linter.unusedVariables 1\n",
            "requires a boolean literal",
        ),
        (
            "term-opt-bad",
            "def x : Nat := set_option debug.skipKernelTC true in 0\n",
            "unsupported option debug.skipKernelTC",
        ),
        (
            "tactic-sorry",
            "theorem t : True := by sorry\n",
            "unsupported tactic",
        ),
        (
            "tactic-admit",
            "theorem t : True := by admit\n",
            "unsupported tactic",
        ),
        (
            "tactic-native-decide",
            "theorem t : 1 = 1 := by native_decide\n",
            "unsupported tactic",
        ),
        (
            "tactic-decide-native",
            "theorem t : 1 = 1 := by decide +native\n",
            "unsupported decide config option native",
        ),
        (
            "tactic-decide-valcfg",
            "theorem t : 1 = 1 := by decide (config := { native := true })\n",
            "unsupported decide config",
        ),
        (
            "tactic-bv-decide",
            "theorem t : true = true := by bv_decide\n",
            "unsupported tactic",
        ),
        (
            "tactic-grind",
            "theorem t : 1 = 1 := by grind\n",
            "unsupported tactic",
        ),
        (
            "tactic-rfl-prime",
            "theorem t : 1 = 1 := by rfl'\n",
            "unsupported tactic",
        ),
        (
            "tactic-run-tac",
            "theorem t : True := by run_tac pure ()\n",
            "unsupported tactic",
        ),
        (
            "tactic-open",
            "theorem t : True := by open Nat in trivial\n",
            "unsupported tactic",
        ),
        (
            "tactic-set-option",
            "theorem t : True := by set_option maxHeartbeats 1 in trivial\n",
            "unsupported tactic",
        ),
        (
            "tactic-conv",
            "theorem t : 1 = 1 := by conv => rfl\n",
            "unsupported tactic",
        ),
        (
            "term-include-str",
            "def s := include_str \"foo\"\n",
            "disallowed syntax Lean.includeStr",
        ),
        (
            "term-by-elab",
            "def e : Nat := by_elab return 0\n",
            "disallowed syntax Lean.byElab",
        ),
        (
            "term-sorry",
            "def s : Nat := sorry\n",
            "disallowed syntax Lean.Parser.Term.sorry",
        ),
        (
            "term-dbg-trace",
            "def d : Nat := dbg_trace \"hi\"; 0\n",
            "disallowed syntax Lean.Parser.Term.dbgTrace",
        ),
        (
            "term-decl-name",
            "def f := decl_name%\n",
            "disallowed syntax Lean.Parser.Term.declName",
        ),
        (
            "term-quot",
            "def q := `(1 + 2)\n",
            "disallowed syntax Lean.Parser.Term.quot",
        ),
        (
            "term-dyn-quot",
            "def dq := `(term| 1 + 2)\n",
            "disallowed syntax Lean.Parser.Term.dynamicQuot",
        ),
        (
            "auto-param-exploit",
            "universe u\n\
             def idAt {α : Sort u} (_f : α → Prop) (a : α) : α := a\n\
             def myTac := idAt (fun s => autoParam True s)\n\
               (.node .none `Lean.Parser.Tactic.tacticSeq #[\n\
                 .node .none `Lean.Parser.Tactic.tacticSeq1Indented #[\n\
                   .node .none `null #[\n\
                     .node .none `Lean.Parser.Tactic.tacticSorry #[.atom .none \"sorry\"]]]])\n\
             theorem evil (h : autoParam False myTac) : False := h\n",
            "disallowed identifier autoParam",
        ),
        (
            "quoted-name",
            "def qn := `foo\n",
            "disallowed syntax Lean.Parser.Term.quotedName",
        ),
        (
            "double-quoted-name",
            "def dqn := ``Nat.add\n",
            "disallowed syntax Lean.Parser.Term.doubleQuotedName",
        ),
        (
            "binder-tactic",
            "def half (n : Nat) (h : n > 0 := by omega) : Nat := n / 2\n",
            "disallowed syntax Lean.Parser.Term.binderTactic",
        ),
        (
            "scoped-instance",
            "namespace N\nscoped instance : Inhabited Unit := ⟨()⟩\nend N\n",
            "disallowed modifier Lean.Parser.Term.scoped",
        ),
        (
            "term-mod-cast",
            "theorem mc (n : Nat) : (n : Int) = (n : Int) := mod_cast (rfl : n = n)\n",
            "disallowed syntax Lean.modCast",
        ),
        (
            "term-panic",
            "def p : Nat := panic! \"boom\"\n",
            "disallowed syntax Lean.Parser.Term.panic",
        ),
        (
            "term-unreachable",
            "def u : Nat := unreachable!\n",
            "disallowed syntax Lean.Parser.Term.unreachable",
        ),
        (
            "term-assert",
            "def a : Nat := assert! true; 0\n",
            "disallowed syntax Lean.Parser.Term.assert",
        ),
        (
            "term-debug-assert",
            "def da : Nat := debug_assert! true; 0\n",
            "disallowed syntax Lean.Parser.Term.debugAssert",
        ),
        (
            "direct-panic-core",
            "def pc : Nat := panicCore \"boom\"\n",
            "disallowed identifier panicCore",
        ),
        (
            "contract-decl-val",
            "def contracted (n : Nat) : Nat\n\
             requires True\n\
             ensures _ => True\n\
             := n\n",
            "disallowed syntax Lean.Parser.Command.contractDeclVal",
        ),
        (
            "term-qed-try",
            "theorem t : True := ∎\n",
            "disallowed syntax «term∎»",
        ),
    ];

    // 1. Live parse-tree round-trip probe + exhaustive check of all negative
    //    vectors against `TrustedBoundary.parseAndInspectSpecCommands` in one
    //    loaded `Init` + `Std` parser environment (~3 s total).
    let fixture = Fixture::new(PROOF);
    let mut checker = Checker::new(&fixture.root, None).unwrap();
    let adm = checker.tool_admission().unwrap().clone();
    let vectors_json_path = checker.stage().join("spec_preflight_vectors.json");
    let vectors_json: Vec<Json> = vectors
        .iter()
        .map(|(label, snippet, expected)| {
            serde_json::json!([label, format!("{snippet}{spec_base}"), expected])
        })
        .collect();
    fs::write(
        &vectors_json_path,
        serde_json::to_vec(&vectors_json).unwrap(),
    )
    .unwrap();
    let mut source = fs::read_to_string(&adm.inspector).unwrap();
    source.push_str(&format!(
        r#"

#eval do
  Lean.initSearchPath (System.FilePath.mk {:?})
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules #[{{ module := `Init }}, {{ module := `Std }}] {{}}
    (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
  let (cmdKinds, tacKinds) ← TrustedBoundary.collectSpecParserSets env
  unless cmdKinds.contains ``Lean.Parser.Command.eval &&
      cmdKinds.contains ``Lean.Parser.Command.initialize &&
      !cmdKinds.contains ``Lean.Parser.Command.declModifiers do
    throw <| IO.userError "unexpected commandLikeKinds partition"
  unless tacKinds.contains `Lean.Parser.Tactic.bvDecide &&
      tacKinds.contains `Lean.Parser.Tactic.nativeDecide &&
      tacKinds.contains `Lean.Parser.Tactic.grind &&
      tacKinds.contains `Lean.Parser.Tactic.runTac &&
      tacKinds.contains `Lean.Parser.Tactic.Conv.conv do
    throw <| IO.userError "unexpected tacticLikeKinds partition"
  let parseHasKind (src : String) (want : Lean.Name) : IO Unit := do
    let ctx := Lean.Parser.mkInputContext src "<rt>"
    let (stx, st, msgs) := Lean.Parser.parseCommand ctx {{ env := env, options := {{}} }} {{}} {{}}
    if msgs.hasErrors || st.recovering then
      throw <| IO.userError s!"parse failed for: {{src}}"
    let rec hasKind : Lean.Syntax → Bool
      | .node _ k args => k == want || args.any hasKind
      | _ => false
    unless hasKind stx do
      throw <| IO.userError s!"expected syntax kind {{want}} in: {{src}}"
  parseHasKind "def s := include_str \"foo\"" ``Lean.includeStr
  parseHasKind "def e : Nat := by_elab return 0" ``Lean.byElab
  parseHasKind "noncomputable section S" ``Lean.Parser.Command.sectionHeader
  parseHasKind "attribute [local simp] Nat.add_zero" ``Lean.Parser.Term.attrInstance
  parseHasKind "deriving instance BEq for Nat" ``Lean.Parser.Command.derivingClass
  parseHasKind "set_option maxHeartbeats 100 in def f := 1" ``Lean.Parser.Command.set_option
  parseHasKind "def f := set_option maxHeartbeats 100 in 1" ``Lean.Parser.Term.set_option
  parseHasKind "theorem t : 1 = 1 := by decide +native" `Lean.Parser.Tactic.decide
  parseHasKind "def q := `(1 + 2)" `Lean.Parser.Term.quot
  parseHasKind "def dq := `(term| 1 + 2)" `Lean.Parser.Term.dynamicQuot
  let raw ← IO.FS.readFile (System.FilePath.mk {:?})
  let j ← IO.ofExcept (Lean.Json.parse raw)
  let cases ← IO.ofExcept (Lean.fromJson? (α := Array (Array String)) j)
  let rootScope : TrustedBoundary.ParseScope :=
    {{ header := "", currNamespace := .anonymous, openDecls := [] }}
  for row in cases do
    let #[label, body, want] := row
      | throw <| IO.userError "malformed test vector row"
    let ctx := Lean.Parser.mkInputContext body label
    let ok ← try
      TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
        [rootScope] `Spec {{}} {{}}
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: expected {{want}} in {{msg}}"
      pure true
    unless ok do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
"#,
        adm.prefix.to_string_lossy(),
        vectors_json_path.to_string_lossy()
    ));
    let probe = checker.stage().join("SpecPreflightRoundTrip.lean");
    fs::write(&probe, source).unwrap();
    checker
        .process(
            "spec-preflight-roundtrip",
            &[probe.to_string_lossy().into_owned()],
        )
        .unwrap();

    // 2. End-to-end `run_target` and sandboxed wire-protocol
    //    `inspect_spec_preflight` checks proving `"spec-preflight"` halts with
    //    exit code 1 inside `ExecSeal` BEFORE any target compilation.
    for (label, snippet, expected) in [
        ("e2e-eval", "#eval 1\n", "unsupported command"),
        (
            "e2e-include-str",
            "def s := include_str \"foo\"\n",
            "disallowed syntax Lean.includeStr",
        ),
    ] {
        let mut e2e_f = Fixture::new(
            "import Expected\n\
             theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
        );
        e2e_f.set(
            "Spec",
            TargetRole::Specification,
            &format!("import Model\n{snippet}{spec_base}"),
        );
        let mut c = cargo_anneal::Checker::new(&e2e_f.root, None).unwrap();
        c.set_allow_unpinned_lean(true);
        let err = c.run_target(&e2e_f.request).unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }

    let mut base_fixture = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let mut unpinned = cargo_anneal::Checker::new(&base_fixture.root, None).unwrap();
    unpinned.set_allow_unpinned_lean(true);
    base_fixture.set(
        "Spec",
        TargetRole::Specification,
        &format!("import Model\n{spec_base}"),
    );
    unpinned.run_target(&base_fixture.request).unwrap();

    let wire_samples = [
        "axiom-decl",
        "partial-def",
        "unsafe-rec-ident",
        "open-platform-target",
        "attr-impl-by",
        "deriving-unknown",
        "tactic-decide-native",
        "term-quot",
        "auto-param-exploit",
        "scoped-instance",
    ];
    for (idx, (label, snippet, expected)) in vectors
        .iter()
        .filter(|(label, _, _)| wire_samples.contains(label))
        .enumerate()
    {
        let path = base_fixture.root.join(format!("neg_spec_{idx:03}.lean"));
        fs::write(&path, format!("import Model\n{snippet}{spec_base}")).unwrap();
        let err = unpinned
            .inspect_spec_preflight(&[("Spec".to_owned(), path)])
            .unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(
            err.message.contains(expected),
            "{label}: expected {expected:?} in {err}"
        );
    }
}

/// Positive end-to-end check confirming rich pure specifications—including
/// `noncomputable section`, `@[local simp]`, `@[reducible, inline]`,
/// `deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable`,
/// `set_option maxHeartbeats` / `linter.*`, `decide +kernel`, `decide +revert`,
/// `omega`, `open System.Platform (numBits)`, and well-founded recursion
/// (`termination_by`/`decreasing_by`, which generates paired
/// `wfRec._unsafe_rec`)—pass `"spec-preflight"` and `"target-audit"` cleanly.
#[test]
fn spec_preflight_and_target_audit_accept_rich_pure_specs_and_wf_recursion() {
    let mut f = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        r#"import Model
set_option linter.unusedVariables false
open System.Platform (numBits)
noncomputable section SpecRich
structure Tag where
  val : Nat
deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable
@[reducible, inline] def hostBits : Nat := numBits + System.Platform.numBits
@[local simp] theorem hostBits_pos : 0 < hostBits := by
  have h := System.Platform.numBits_eq
  rcases h with h32 | h64
  · simp [hostBits, h32]
  · simp [hostBits, h64]
set_option maxHeartbeats 200000 in
theorem dec_kernel_ok : 2 + 2 = 4 := by decide +kernel
theorem dec_revert_ok (b : Bool) : (b || !b) = true := by decide +revert
theorem omega_ok (n : Nat) : n + 1 > n := by omega
def wfHalf (n : Nat) : Nat :=
  if h : n = 0 then 0 else wfHalf (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
section
open BitVec
def bvLit (x : Nat) (h : x < 2^8) : BitVec 8 := x#'h
end
section
open BitVec hiding ofNat
def bvLitHide (x : Nat) (h : x < 2^8) : BitVec 8 := x#'h
end
section
open Int
def negSuccVal (n : Nat) : Int := -[n+1]
end
end SpecRich
def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p
"#,
    );
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    let report = checker.run_target(&f.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(report["sorryDeclarations"], serde_json::json!([]));
}

/// Unified `"target-audit"` Phase 1 enforces whole-specification invariants
/// even on declarations unreferenced by `Spec.specs` (rejecting `opaque`,
/// `sorryAx` even when `allow_sorry_in_proof = true`, transitive `IO`,
/// `dbgTrace`, or `System.Platform.target`, forged unpaired `._unsafe_rec`, and
/// forged `Proof` references to a paired `._unsafe_rec`, plus companion
/// artifact parts).
#[test]
fn target_audit_phase1_enforces_whole_spec_opaque_effects_and_unsafe_rec_invariants() {
    use anneal_audit::ModuleArtifacts;
    use std::collections::BTreeMap;

    // Helper: compile ONE valid unpinned baseline via `run_target` (which
    // admits the full `Init` closure into `checker.admitted()`), then overwrite
    // and recompile `Spec` (and `Expected`/`Proof`) directly into `stage/lib`
    // to exercise `"target-audit"` Phase 1 directly without `"spec-preflight"`.
    let mut f = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "import Model\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
    checker.set_allow_unpinned_lean(true);
    checker.run_target(&f.request).unwrap();

    let mut audit_bypassing_preflight = |spec_src: &str,
                                         proof_src: &str,
                                         allow_sorry: bool,
                                         forge_companion: bool|
     -> Result<Json, Failure> {
        f.set("Spec", TargetRole::Specification, spec_src);
        f.set("Proof", TargetRole::Proof, proof_src);
        f.request.allow_sorry_in_proof = allow_sorry;
        for name in ["Spec", "Expected", "Proof"] {
            let m = f.request.modules.iter().find(|x| x.module == name).unwrap();
            let staged_src = checker.stage().join("ro").join(format!("{name}.lean"));
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let _ = fs::set_permissions(&staged_src, fs::Permissions::from_mode(0o600));
            }
            fs::copy(&m.source, &staged_src).unwrap();
            let hdr_json = checker
                .inspect_headers(&[(name.to_string(), staged_src.clone())])
                .unwrap();
            let hdrs: cargo_anneal::PreflightResult = serde_json::from_value(hdr_json).unwrap();
            let header = hdrs.headers.into_iter().next().unwrap();
            let dest_olean = checker.stage().join("lib").join(format!("{name}.olean"));
            if dest_olean.exists() {
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let _ = fs::set_permissions(&dest_olean, fs::Permissions::from_mode(0o600));
                }
            }
            checker
                .compile_lean_module(
                    name,
                    &staged_src,
                    header.imports,
                    header.is_module,
                    "lib",
                    false,
                    true,
                )
                .unwrap();
        }
        if forge_companion {
            let spec_olean = checker.stage().join("lib/Spec.olean");
            let fake_priv = checker.stage().join("lib/Spec.olean.private");
            fs::copy(&spec_olean, &fake_priv).unwrap();
            let mut avail = BTreeMap::new();
            avail.insert("olean", spec_olean.to_string_lossy().into_owned());
            avail.insert("olean.private", fake_priv.to_string_lossy().into_owned());
            let adm = checker.admitted_mut().unwrap();
            adm.artifacts.insert(
                "Spec".into(),
                ModuleArtifacts::from_available(&avail, "fixture", || "missing".into()).unwrap(),
            );
        }
        checker.inspect_target(&f.request)
    };

    let clean_proof = "import Expected\n\
        theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n";

    // 1. Unused `opaque` in `Spec` rejected in Phase 1.
    let err = audit_bypassing_preflight(
        "import Model\nopaque Spec.unusedOp : Nat := 0\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("opaque declaration Spec.unusedOp"),
        "{err}"
    );

    // 2. Unused `sorry` in `Spec` rejected in Phase 1 EVEN WITH
    //    `allow_sorry_in_proof = true`.
    let err = audit_bypassing_preflight(
        "import Model\ntheorem Spec.unusedSorry : True := sorry\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        true,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(err.message.contains("unapproved axiom sorryAx"), "{err}");

    // 3. Unused `Spec` declaration transitively referencing `IO`, `dbgTrace`,
    //    or `System.Platform.target` rejected in Phase 1.
    for (label, decl, expected) in [
        (
            "io",
            "def Spec.unusedIo : IO Unit := pure ()\n",
            "disallowed constant IO",
        ),
        (
            "dbg-trace",
            "def Spec.unusedDbg : Nat := dbgTrace \"x\" (fun _ => 0)\n",
            "disallowed constant dbgTrace",
        ),
        (
            "platform-target",
            "def Spec.unusedTarget : String := System.Platform.target\n",
            "disallowed constant System.Platform.target",
        ),
    ] {
        let err = audit_bypassing_preflight(
            &format!(
                "import Model\n{decl}def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"
            ),
            clean_proof,
            false,
            false,
        )
        .unwrap_err();
        assert_eq!(
            (err.code, err.phase.as_str()),
            (1, "target-audit"),
            "{label}: {err}"
        );
        assert!(err.message.contains(expected), "{label}: {err}");
    }

    // 4. Unpaired `partial def Spec.orphan._unsafe_rec` rejected in Phase 1.
    let err = audit_bypassing_preflight(
        "import Model\npartial def Spec.orphan._unsafe_rec (n : Nat) : Nat := \
         Spec.orphan._unsafe_rec n\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message
            .contains("opaque declaration Spec.orphan._unsafe_rec")
            || err.message.contains("unsafe/partial"),
        "{err}"
    );

    // 5a. Safe Proof referencing a legitimately paired
    //     `Spec.wfHalf._unsafe_rec` is already rejected by Lean's kernel during
    //     `compile-Proof`; an `unsafe def` in `Spec` referencing
    //     `Spec.wfHalf._unsafe_rec` (or an `unsafe def Spec.foo._unsafe_rec`
    //     paired by name with total `Spec.foo`) compiles cleanly and is
    //     rejected by `"target-audit"` Phase 1.
    let wf_spec = r#"import Model
def Spec.wfHalf (n : Nat) : Nat :=
  if h : n = 0 then 0 else Spec.wfHalf (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p
"#;
    let err = audit_bypassing_preflight(
        &format!("{wf_spec}unsafe def Spec.sneak (n : Nat) : Nat := Spec.wfHalf._unsafe_rec n\n"),
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("unsafe/partial") || err.message.contains("paired _unsafe_rec"),
        "{err}"
    );

    // 5b. `unsafe def Spec.foo._unsafe_rec` next to total `def Spec.foo` fails
    //     the `!ci.isUnsafe` pairing guard and is rejected by `"target-audit"`.
    let err = audit_bypassing_preflight(
        "import Model\ndef Spec.foo (n : Nat) : Nat := n\n\
         unsafe def Spec.foo._unsafe_rec (n : Nat) : Nat := n\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message
            .contains("unsafe/partial logical dependency Spec.foo._unsafe_rec"),
        "{err}"
    );

    // 6. Companion artifact part (`.olean.private`) on a target source module
    //    rejected by `"target-audit"`.
    let err = audit_bypassing_preflight(
        "import Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        true,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("companion artifact parts unsupported"),
        "{err}"
    );

    // 7. Forged `isModule = true` `.olean` on a target source module rejected
    //    by `"target-audit"`.
    let clean_spec = "import Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    let _ = audit_bypassing_preflight(clean_spec, clean_proof, false, false).unwrap();
    let spec_olean = checker.stage().join("lib/Spec.olean");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = fs::set_permissions(&spec_olean, fs::Permissions::from_mode(0o600));
    }
    let forge_script = checker.stage().join("ForgeIsModule.lean");
    fs::write(
        &forge_script,
        format!(
            r#"import Lean
open Lean in
def main : IO Unit := do
  let p := System.FilePath.mk {:?}
  let (data, _) ← readModuleData p
  saveModuleData p `Spec {{ data with isModule := true }}
"#,
            spec_olean.to_string_lossy()
        ),
    )
    .unwrap();
    checker
        .process(
            "forge-is-module",
            &[
                "--run".to_string(),
                forge_script.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let mut avail_single = BTreeMap::new();
    avail_single.insert("olean", spec_olean.to_string_lossy().into_owned());
    checker.admitted_mut().unwrap().artifacts.insert(
        "Spec".into(),
        ModuleArtifacts::from_available(&avail_single, "fixture", || "missing".into()).unwrap(),
    );
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!(err.phase.as_str(), "target-audit", "{err}");
    assert!(
        (err.code == 1 && err.message.contains("module-system artifact unsupported"))
            || (err.code == 2 && err.message.contains("missing data file for module Spec")),
        "expected fail-closed rejection of forged isModule .olean: {err}"
    );
}

/// Phase 2 `"target-audit"` with `allow_sorry_in_proof`:
/// - rejects proof `sorry` when `allow_sorry_in_proof = false`;
/// - admits proof-only `sorry` when `allow_sorry_in_proof = true` and records
///   ALL proof declarations that reference `sorryAx` (verifying per-edge
///   admission before `visited` short-circuiting);
/// - emits `"sorryDeclarations": []` without `"sorryAx"` in `"axioms"` when a
///   proof under `allow_sorry_in_proof = true` uses zero `sorry`s; and
/// - rejects `sorry` in `Model`, `Capture`, or `Expected` even when
///   `allow_sorry_in_proof = true`.
#[test]
fn target_audit_phase2_allow_sorry_in_proof_tracks_multiple_helpers_and_isolates_phase1() {
    let multi_sorry_proof = "prelude\nimport Expected\n\
        theorem Proof.helperA : Captured.program.toNat = 7 := sorry\n\
        theorem Proof.helperB : Spec.specs Captured.program := sorry\n\
        theorem Proof.verify : Expected.claim := And.intro Proof.helperA Proof.helperB\n";

    // 1. Default (`allow_sorry_in_proof = false`) rejects proof `sorry`.
    let f_strict = Fixture::new(multi_sorry_proof);
    f_strict.reject_audit("unapproved axiom sorryAx from Init.Prelude");

    // 2. `allow_sorry_in_proof = true` admits BOTH proof helpers and reports
    //    both in sorted `sorryDeclarations`.
    let mut f_allow = Fixture::new(multi_sorry_proof);
    f_allow.request.allow_sorry_in_proof = true;
    let report = f_allow.run().unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(
        report["sorryDeclarations"],
        serde_json::json!(["Proof.helperA", "Proof.helperB"])
    );
    assert!(
        report["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .any(|a| a == "sorryAx"),
        "expected sorryAx in axioms: {report}"
    );

    // 3. Clean proof under `allow_sorry_in_proof = true` has empty
    //    `sorryDeclarations` and omits `sorryAx` from `axioms`.
    let mut f_clean = Fixture::new(PROOF);
    f_clean.request.allow_sorry_in_proof = true;
    let clean_report = f_clean.run().unwrap();
    assert_eq!(clean_report["sorryDeclarations"], serde_json::json!([]));
    assert!(
        clean_report["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .all(|a| a != "sorryAx"),
        "unexpected sorryAx in clean axioms: {clean_report}"
    );

    // 4. `sorry` in `Capture`, `Model`, or `Expected` (Phase 1) is rejected
    //    EVEN WITH `allow_sorry_in_proof = true`.
    let mut f_bad_capture = Fixture::new(multi_sorry_proof);
    f_bad_capture.request.allow_sorry_in_proof = true;
    f_bad_capture.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\ndef Captured.program : BitVec 8 := sorry\n",
    );
    f_bad_capture.reject_audit("unapproved axiom sorryAx from Init.Prelude");

    let mut f_bad_model = Fixture::new(multi_sorry_proof);
    f_bad_model.request.allow_sorry_in_proof = true;
    f_bad_model.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Prelude\nimport Init.Core\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         theorem modelHelper : True := sorry\n\
         def UnitTheorem (c : Crate) : Prop := (fun _ : True => c.program.toNat = 7 ∧ c.specs c.program) modelHelper\n\
         end Trusted.MirSemantics\n",
    );
    f_bad_model.reject_audit("unapproved axiom sorryAx from Init.Prelude");

    let mut f_bad_expected = Fixture::new(multi_sorry_proof);
    f_bad_expected.request.allow_sorry_in_proof = true;
    f_bad_expected.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         theorem Expected.helper : True := sorry\n\
         def Expected.claim : Prop := (fun _ : True => Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)) Expected.helper\n",
    );
    f_bad_expected.reject_audit("unapproved axiom sorryAx from Init.Prelude");
}

#[test]
fn target_audit_reports_empty_and_unused_binding_spec_warnings() {
    let f_clean = Fixture::new(PROOF);
    let clean_report = f_clean.run().unwrap();
    assert_eq!(clean_report["specWarnings"], serde_json::json!([]));

    let mut f_unused = Fixture::new(PROOF);
    f_unused.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.helper (unusedParam : Nat) (p : BitVec 8) : Prop := p &&& p = p\n\
         def Spec.specs (p : BitVec 8) : Prop := Spec.helper 0 p\n",
    );
    let unused_report = f_unused.run().unwrap();
    assert_eq!(unused_report["replay"], true);
    assert_eq!(
        unused_report["specWarnings"],
        serde_json::json!([{
            "code": "unused_spec_binding",
            "declaration": "Spec.helper",
            "message": "unused argument binding(s) in `Spec.helper`: unusedParam"
        }])
    );
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

    let mut checker = cargo_anneal::Checker::new(&f.root, None).unwrap();
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

    // Helper: craft header-chained synthetic `.olean.server` & `.olean.private`
    // for a non-`module` `.olean` so ONLY the primary-part `data.isModule`
    // pre-import check (not the base-address check) can reject it before
    // `CompactedRegion.read` would crash on the 88-byte synthetic bodies.
    let stage_dir = checker.stage().to_path_buf();
    let craft_chained_companions = |primary_path: &str, stem: &str| -> (String, String) {
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
    };

    // 4. Non-`module` `Trusted.NonMod` (`Model`) paired with header-chained
    //    3-part companions fails closed before `importEnv` via `data.isModule`.
    let non_mod_model = get_parts("Trusted.NonMod");
    let (nm_srv, nm_prv) = craft_chained_companions(&non_mod_model[0], "Trusted/NonMod");
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

    // 5. Non-`module` `Anneal.NonMod` (`Proof`) paired with header-chained
    //    3-part companions fails closed in `"target-export"` before `importEnv`.
    let non_mod_proof = get_parts("Anneal.NonMod");
    let (ap_srv, ap_prv) = craft_chained_companions(&non_mod_proof[0], "Anneal/NonMod");
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
