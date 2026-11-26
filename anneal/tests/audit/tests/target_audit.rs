// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact target-root, source binding and authority separation regressions.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use anneal_audit::{
    Checker, Failure, Json, TargetAuditRequest, TargetBindings, TargetModule, TargetRole,
    sha256_bytes,
};
use anneal_testkit::{LeanAuditFixture, OleanCachePolicy};

struct Fixture {
    inner: LeanAuditFixture,
    root: PathBuf,
    request: TargetAuditRequest,
}
impl Fixture {
    fn new(proof: &str) -> Self {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let inner = LeanAuditFixture::with_cache_policy(
            &repo,
            "anneal-target-test-",
            None,
            true,
            OleanCachePolicy::Shared,
        )
        .unwrap();
        let root = inner.root().to_path_buf();
        let h = sha256_bytes(b"fixture compilation");
        let mut f = Self {
            inner,
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
        let (path, expected_sha256) = self.inner.write_input_lean(name, source).unwrap();
        self.request.modules.retain(|m| m.module != name);
        self.request.modules.push(TargetModule {
            module: name.into(),
            source: path,
            expected_sha256,
            role,
        });
    }
    fn checker(&self) -> Checker {
        let env = self.inner.checker_env().unwrap();
        Checker::new_with_env(&self.root, None, env).unwrap()
    }
    fn cargo_checker(&self) -> cargo_anneal::Checker {
        let env = self.inner.checker_env().unwrap();
        cargo_anneal::Checker::new_with_env(&self.root, None, env).unwrap()
    }
    fn run(&self) -> Result<Json, Failure> {
        self.checker().run_target(&self.request)
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
        let mut checker = self.checker();
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

/// Authored `@[export]`, `@[init]`, and `@[builtin_init]` hooks in `Proof` or
/// non-`Proof` target modules are refused even when logically unreached, while
/// legitimate baseline `Init` `@[init]`/`@[export]` entries remain accepted.
#[test]
fn rejects_authored_export_init_and_builtin_init_metadata() {
    // 1. Pinned `Fixture`: unreached `@[export]` in `Proof` fails closed
    //    through `"target-export"` -> `"target-audit"`.
    Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         @[export anneal_audit_export_helper] def exportHelper (n : Nat) : Nat := n\n\
         theorem Proof.verify : Expected.claim := by exact And.intro rfl BitVec.and_self\n",
    )
    .reject_audit("unchecked compiler export override on exportHelper");

    // 2. Unpinned target mode: baseline `Init.Data.Random` (`@[init]` on
    //    `IO.stdGenRef`, plus `Init.Prelude` `@[export]`) stays accepted,
    //    while authored `@[init]` and `@[builtin_init]` in unreached `Proof`
    //    or non-`Proof` target modules (`Spec`/`Captured`) fail closed.
    let mut f_ok = Fixture::new(
        "import Expected\nimport Init.Data.Random\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let clean_spec = "import Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    f_ok.set("Spec", TargetRole::Specification, clean_spec);
    let mut chk = cargo_anneal::Checker::new(&f_ok.root, None).unwrap();
    chk.set_allow_unpinned_lean(true);
    let report = chk.run_target(&f_ok.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);

    let recompile_and_inspect = |chk: &mut cargo_anneal::Checker,
                                 f: &mut Fixture,
                                 role: TargetRole,
                                 mod_name: &str,
                                 src: &str|
     -> Failure {
        f.set(mod_name, role, src);
        let m = f.request.modules.iter().find(|x| x.module == mod_name).unwrap();
        let staged_src = chk.stage().join("ro").join(format!("{mod_name}.lean"));
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = fs::set_permissions(&staged_src, fs::Permissions::from_mode(0o600));
        }
        fs::copy(&m.source, &staged_src).unwrap();
        let hdr_json = chk.inspect_headers(&[(mod_name.to_string(), staged_src.clone())]).unwrap();
        let hdrs: cargo_anneal::PreflightResult = serde_json::from_value(hdr_json).unwrap();
        let header = hdrs.headers.into_iter().next().unwrap();
        let dest_olean = chk.stage().join("lib").join(format!("{mod_name}.olean"));
        if dest_olean.exists() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let _ = fs::set_permissions(&dest_olean, fs::Permissions::from_mode(0o600));
            }
        }
        chk.compile_lean_module(
            mod_name,
            &staged_src,
            header.imports,
            header.is_module,
            "lib",
            false,
            true,
        )
        .unwrap();
        chk.inspect_target(&f.request).unwrap_err()
    };

    for (label, proof_decl, expected) in [
        (
            "proof-init",
            "@[init] def initHelper : IO Unit := pure ()\n",
            "unchecked compiler init override on initHelper",
        ),
        (
            "proof-builtin-init",
            "@[builtin_init] def builtinInitHelper : IO Unit := pure ()\n",
            "unchecked compiler builtin_init override on builtinInitHelper",
        ),
    ] {
        let proof_src = format!(
            "import Expected\n{proof_decl}\
             theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n"
        );
        let err =
            recompile_and_inspect(&mut chk, &mut f_ok, TargetRole::Proof, "Proof", &proof_src);
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }
    // Restore clean `Proof` (and re-run headers-matched `Spec` / `Captured`)
    // before testing non-`Proof` target modules.
    f_ok.set(
        "Proof",
        TargetRole::Proof,
        "import Expected\ntheorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    chk.set_allow_unpinned_lean(true);
    chk.run_target(&f_ok.request).unwrap();

    // 3. Direct non-`Proof` target module check (`Spec` for `@[export]`,
    //    `Captured` for `@[init]` / `@[builtin_init]`) bypassing preflight.
    let err_spec_export = recompile_and_inspect(
        &mut chk,
        &mut f_ok,
        TargetRole::Specification,
        "Spec",
        "import Model\n\
         @[export anneal_spec_export] def Spec.badExport (n : Nat) : Nat := n\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    assert_eq!(
        (err_spec_export.code, err_spec_export.phase.as_str()),
        (1, "target-audit"),
        "spec-export: {err_spec_export}"
    );
    assert!(
        err_spec_export
            .message
            .contains("unchecked compiler export override on Spec.badExport in Spec"),
        "spec-export: {err_spec_export}"
    );
    f_ok.set("Spec", TargetRole::Specification, clean_spec);
    chk.run_target(&f_ok.request).unwrap();

    for (label, decl, expected) in [
        (
            "capture-init",
            "@[init] def Captured.badInit : IO Unit := pure ()\n",
            "unchecked compiler init override on Captured.badInit in Captured",
        ),
        (
            "capture-builtin-init",
            "@[builtin_init] def Captured.badBuiltinInit : IO Unit := pure ()\n",
            "unchecked compiler builtin_init override on Captured.badBuiltinInit in Captured",
        ),
    ] {
        let cap_src =
            format!("import Model\n{decl}def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n");
        let err =
            recompile_and_inspect(&mut chk, &mut f_ok, TargetRole::Capture, "Captured", &cap_src);
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
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
    let mut checker = f.checker();
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
    let mut checker = fixture.checker();
    let inspector = checker.tool_admission().unwrap().inspector.clone();
    let mut source = fs::read_to_string(inspector).unwrap();
    source.push_str(
        r#"

#eval do
  let original : Lean.TheoremVal := {
    name := `MetadataWitness, levelParams := [], type := Lean.mkConst `True,
    value := Lean.mkConst `True.intro, all := [`MetadataWitness] }
  let stored := Lean.ConstantInfo.thmInfo original
  let unchanged ← TrustedBoundary.inventoryAlternates stored stored
  unless unchanged.isEmpty do throw <| IO.userError "identical theorem produced alternates"
  let changedProof := Lean.Expr.letE `h original.type original.value (.bvar 0) false
  let alternate := Lean.ConstantInfo.thmInfo { original with value := changedProof }
  let proofs ← TrustedBoundary.inventoryAlternates stored alternate
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
        let _ ← TrustedBoundary.inventoryAlternates a b
        pure false
      catch error =>
        unless error.toString.startsWith "policy:inconsistent theorem metadata" do
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
    let mut checker = fixture.checker();
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

/// `"headers"` admits Lean 4 module-system headers (`module`, `public import`)
/// while rejecting `import all`, `meta import`, non-module import modifiers,
/// and `Lean.*`/`Lake.*` imports with exit code 1, and accepts omitted
/// `prelude` (synthetic non-meta + meta `Init` pair) in unpinned mode.
#[test]
fn headers_rejects_module_system_modifiers_and_lean_lake_and_allows_no_prelude() {
    for (label, header, expected) in [
        ("module-import-all", "module\nprelude\nimport all Model\n", "import modifiers"),
        (
            "module-meta-import",
            "module\nprelude\nmeta import Model\n",
            "unsupported syntax kind Lean.Parser.Module.meta",
        ),
        (
            "module-lean-import",
            "module\nprelude\npublic import Lean.Elab\nimport Model\n",
            "disallowed sysroot import",
        ),
        ("import-all", "prelude\nimport all Model\n", "header parser error"),
        ("public-import", "prelude\npublic import Model\n", "header parser error"),
        ("meta-import", "prelude\nmeta import Model\n", "header parser error"),
        ("lean-import", "prelude\nimport Lean.Elab\nimport Model\n", "disallowed sysroot import"),
        ("lake-import", "prelude\nimport Lake.Build\nimport Model\n", "disallowed sysroot import"),
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

    // Direct unit probe of `validateTargetImports` confirming both legacy
    // non-`module` and Lean 4 `module`-system import rules as well as
    // acceptance of the synthetic `!hasPrelude` Init pair and the bundled
    // `Anneal.*` `Init.Data.Nat.Bitwise.Basic` exception.
    let probe_fixture = Fixture::new(PROOF);
    let mut probe_checker = probe_fixture.checker();
    let empty_proof_export = probe_checker.stage().join("proof_export_empty.json");
    fs::write(
        &empty_proof_export,
        r#"{"schemaVersion":1,"names":[],"levels":[],"exprs":[],"modules":[],"compilerOverrides":{"implementedBy":[],"extern":[],"csimp":[],"export":[],"init":[],"builtinInit":[],"cpass":[],"constantFold":[],"postponedCompile":[]}}"#,
    )
    .unwrap();
    let empty_proof_export_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-export",
            "sysroot": "",
            "artifacts": [],
            "foundation": [],
            "libraries": [],
            "proofExportPath": empty_proof_export.to_string_lossy(),
            "target": {
                "modules": [{"module": "Spec", "expectedSha256": "0", "role": "specification"}],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let forged_eq_export = probe_checker.stage().join("proof_export_forged_eq.json");
    fs::write(
        &forged_eq_export,
        serde_json::to_string(&serde_json::json!({
            "schemaVersion": 1,
            "names": [
                ["a"],
                ["s", 0, "Option"],
                ["s", 1, "map"],
                ["s", 2, "eq_1"],
                ["s", 0, "True"],
                ["s", 4, "intro"]
            ],
            "levels": [],
            "exprs": [
                ["c", 4, []],
                ["c", 5, []]
            ],
            "modules": [{
                "module": "Proof",
                "isModule": true,
                "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                "constNames": [3],
                "constants": [["thm", 3, [], 0, 1, [3]]]
            }],
            "compilerOverrides": {
                "implementedBy": [], "extern": [], "csimp": [],
                "export": [], "init": [], "builtinInit": [],
                "cpass": [], "constantFold": [], "postponedCompile": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let forged_eq_req_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-audit",
            "sysroot": "",
            "artifacts": [],
            "graph": {
                "Proof": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}]
            },
            "foundation": ["Init.Control.Lawful.Instances", "Init.Core"],
            "libraries": [],
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"]
            ],
            "proofExportPath": forged_eq_export.to_string_lossy(),
            "target": {
                "modules": [{"module": "Proof", "expectedSha256": "0", "role": "proof", "isModule": true}],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let forged_dup_export = probe_checker.stage().join("proof_export_forged_dup.json");
    fs::write(
        &forged_dup_export,
        serde_json::to_string(&serde_json::json!({
            "schemaVersion": 1,
            "names": [
                ["a"],
                ["s", 0, "Shared"],
                ["s", 1, "dup"],
                ["s", 0, "True"],
                ["s", 3, "intro"],
                ["s", 0, "False"]
            ],
            "levels": [],
            "exprs": [
                ["c", 3, []],
                ["c", 4, []],
                ["c", 5, []]
            ],
            "modules": [
                {
                    "module": "HelperA",
                    "isModule": true,
                    "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                    "constNames": [2],
                    "constants": [["thm", 2, [], 0, 1, [2]]]
                },
                {
                    "module": "Proof",
                    "isModule": true,
                    "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                    "constNames": [2],
                    "constants": [["thm", 2, [], 2, 1, [2]]]
                }
            ],
            "compilerOverrides": {
                "implementedBy": [], "extern": [], "csimp": [],
                "export": [], "init": [], "builtinInit": [],
                "cpass": [], "constantFold": [], "postponedCompile": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let forged_dup_req_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-audit",
            "sysroot": "",
            "artifacts": [],
            "graph": {},
            "foundation": ["Init.Control.Lawful.Instances", "Init.Core"],
            "libraries": [],
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"]
            ],
            "proofExportPath": forged_dup_export.to_string_lossy(),
            "target": {
                "modules": [
                    {"module": "HelperA", "expectedSha256": "0", "role": "proof", "isModule": true},
                    {"module": "Proof", "expectedSha256": "0", "role": "proof", "isModule": true}
                ],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let forged_anon_export = probe_checker.stage().join("proof_export_forged_anon.json");
    fs::write(
        &forged_anon_export,
        serde_json::to_string(&serde_json::json!({
            "schemaVersion": 1,
            "names": [
                ["a"],
                ["s", 0, "True"],
                ["s", 1, "intro"]
            ],
            "levels": [],
            "exprs": [
                ["c", 1, []],
                ["c", 2, []]
            ],
            "modules": [{
                "module": "Proof",
                "isModule": true,
                "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                "constNames": [0],
                "constants": [["thm", 0, [], 0, 1, [0]]]
            }],
            "compilerOverrides": {
                "implementedBy": [], "extern": [], "csimp": [],
                "export": [], "init": [], "builtinInit": [],
                "cpass": [], "constantFold": [], "postponedCompile": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let forged_anon_req_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-audit",
            "sysroot": "",
            "artifacts": [],
            "graph": {},
            "foundation": ["Init.Control.Lawful.Instances", "Init.Core"],
            "libraries": [],
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"]
            ],
            "proofExportPath": forged_anon_export.to_string_lossy(),
            "target": {
                "modules": [{"module": "Proof", "expectedSha256": "0", "role": "proof", "isModule": true}],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
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
  let okModuleImps : Array Lean.Import := #[
    { module := `Init, importAll := false, isExported := false, isMeta := false },
    { module := `Init, importAll := false, isExported := false, isMeta := true },
    { module := `Model, importAll := false, isExported := true, isMeta := false },
    { module := `Helper, importAll := false, isExported := false, isMeta := false }
  ]
  TrustedBoundary.validateTargetImports "Spec" okModuleImps (allowModule := true)
  TrustedBoundary.validateTargetImports "Anneal.NatBitwise"
    #[{ module := `Init.Data.Nat.Bitwise.Basic, importAll := true, isExported := false, isMeta := false }]
    (allowModule := true) (allowTheoryImportAll := true)
  let badCases : Array (String × Bool × Bool × Array Lean.Import × String) := #[
    ("importAll", false, false, #[{ module := `Init, importAll := true, isExported := true, isMeta := false }], "import modifiers"),
    ("private", false, false, #[{ module := `Init, importAll := false, isExported := false, isMeta := false }], "import modifiers"),
    ("unpairedMetaInit", false, false, #[{ module := `Init, importAll := false, isExported := true, isMeta := true }], "meta import Init"),
    ("metaNonInit", false, false, #[{ module := `Init, importAll := false, isExported := true, isMeta := false }, { module := `Model, importAll := false, isExported := true, isMeta := true }], "meta import Model"),
    ("lean", false, false, #[{ module := `Lean.Elab, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("lake", false, false, #[{ module := `Lake, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("modImportAll", true, false, #[{ module := `Model, importAll := true, isExported := false, isMeta := false }], "import modifiers"),
    ("modTheoryNonBitwiseImportAll", true, true, #[{ module := `Model, importAll := true, isExported := false, isMeta := false }], "import modifiers"),
    ("modMetaNonInit", true, false, #[{ module := `Model, importAll := false, isExported := false, isMeta := true }], "meta import Model"),
    ("modLean", true, false, #[{ module := `Lean.Elab, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("modLake", true, false, #[{ module := `Lake, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import")
  ]
  for (label, allowMod, allowBitwiseAll, imps, want) in badCases do
    let ok ← try
      TrustedBoundary.validateTargetImports "Spec" imps
        (allowModule := allowMod) (allowTheoryImportAll := allowBitwiseAll)
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
    probe_src.push_str(&format!(
        r#"
  -- Realized theorem and generated-helper guards used by `"target-audit"`.
  let forgedEqBase ← IO.ofExcept <| Lean.Json.parse {forged_eq_req_lit}
  let initEnv : Lean.Environment ← TrustedBoundary.importEnv forgedEqBase #[`Init.Control.Lawful.Instances, `Init.Core]
  let helperName := `Option.map.eq_1
  let mkThm (lps : List Lean.Name) (ty val : Lean.Expr) : Lean.ConstantInfo :=
    .thmInfo {{ name := helperName, levelParams := lps, type := ty, value := val, all := [helperName] }}
  let base := mkThm [`u] (Lean.mkConst `True) (Lean.mkConst `True.intro)
  let altProof := mkThm [`u] (Lean.mkConst `True) (Lean.mkConst `trivial)
  unless TrustedBoundary.sameRealizedThmHeader base altProof do
    throw <| IO.userError "realized-thm: differing proof body rejected"
  let defnCopy : Lean.ConstantInfo :=
    .defnInfo {{ name := helperName, levelParams := [`u], type := Lean.mkConst `True, value := Lean.mkConst `True.intro, hints := .opaque, safety := .safe, all := [helperName] }}
  for (label, other) in #[
      ("levelParams", mkThm [`v] (Lean.mkConst `True) (Lean.mkConst `True.intro)),
      ("type", mkThm [`u] (Lean.mkConst `False) (Lean.mkConst `True.intro)),
      ("kind", defnCopy)
    ] do
    if TrustedBoundary.sameRealizedThmHeader base other then
      throw <| IO.userError s!"realized-thm: {{label}} difference accepted"
  unless TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (· == `Option.map) base
      (allowUnimportedProofSparse := true) do
    throw <| IO.userError "lazy-helper: helper of admitted parent rejected"
  if TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (fun _ => false) base
      (allowUnimportedProofSparse := true) then
    throw <| IO.userError "lazy-helper: helper of unknown parent accepted"
  let unknownEq : Lean.ConstantInfo :=
    .thmInfo {{ name := `X.f.eq_1, levelParams := [`u], type := Lean.mkConst `True, value := Lean.mkConst `True.intro, all := [`X.f.eq_1] }}
  if TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (· == `X.f) unknownEq
      (allowUnimportedProofSparse := true) then
    throw <| IO.userError "lazy-helper: unreserved parent accepted"
  let nonHelper : Lean.ConstantInfo :=
    .thmInfo {{ name := `Option.map.dup, levelParams := [`u], type := Lean.mkConst `True, value := Lean.mkConst `True.intro, all := [`Option.map.dup] }}
  if TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (· == `Option.map) nonHelper
      (allowUnimportedProofSparse := true) then
    throw <| IO.userError "lazy-helper: non-helper suffix accepted"
  let mut gEntries : List (String × Lean.Json) :=
    (initEnv.header.modules.zip initEnv.header.moduleData).toList.map fun ((m : Lean.EffectiveImport), (d : Lean.ModuleData)) =>
      (m.module.toString, Lean.toJson d.imports)
  gEntries := ("Proof", Lean.toJson #[({{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }} : Lean.Import)]) :: gEntries
  let found := initEnv.header.modules.map (fun (m : Lean.EffectiveImport) => m.module)
  let forgedEqReq := forgedEqBase.setObjVal! "graph" (Lean.Json.mkObj gEntries)
  let forgedRejected ← try
    let _ ← TrustedBoundary.targetAudit forgedEqReq found
    pure false
  catch e =>
    let msg := e.toString
    unless (msg.splitOn "duplicate target declaration Option.map.eq_1").length > 1 do
      throw <| IO.userError s!"forged-wrong-type-lazy-helper: unexpected error {{msg}}"
    pure true
  unless forgedRejected do
    throw <| IO.userError "forged-wrong-type-lazy-helper: unexpectedly accepted"
  let forgedDupBase ← IO.ofExcept <| Lean.Json.parse {forged_dup_req_lit}
  let mut dupGEntries : List (String × Lean.Json) :=
    (initEnv.header.modules.zip initEnv.header.moduleData).toList.map fun ((m : Lean.EffectiveImport), (d : Lean.ModuleData)) =>
      (m.module.toString, Lean.toJson d.imports)
  let coreImp := Lean.toJson #[({{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }} : Lean.Import)]
  dupGEntries := ("HelperA", coreImp) :: ("Proof", coreImp) :: dupGEntries
  let forgedDupReq := forgedDupBase.setObjVal! "graph" (Lean.Json.mkObj dupGEntries)
  let dupRejected ← try
    let _ ← TrustedBoundary.targetAudit forgedDupReq found
    pure false
  catch e =>
    let msg := e.toString
    unless (msg.splitOn "duplicate target declaration Shared.dup").length > 1 do
      throw <| IO.userError s!"forged-proof-dup: unexpected error {{msg}}"
    pure true
  unless dupRejected do
    throw <| IO.userError "forged-proof-dup: unexpectedly accepted"
  let forgedAnonBase ← IO.ofExcept <| Lean.Json.parse {forged_anon_req_lit}
  let forgedAnonReq := forgedAnonBase.setObjVal! "graph" (Lean.Json.mkObj gEntries)
  let assertPolicyErr (label want : String) (act : IO Unit) : IO Unit := do
    let rejected ← try
      act
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: unexpected error {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
  assertPolicyErr "forged-proof-anon" "anonymous declaration in target inventory Proof" do
    discard <| TrustedBoundary.targetAudit forgedAnonReq found
  assertPolicyErr "replay-map-key" "replay map key MismatchKey differs from Option.map.eq_1" do
    TrustedBoundary.validateReplayMap initEnv.toKernelEnv
      (({{}} : Std.HashMap Lean.Name Lean.ConstantInfo).insert `MismatchKey base) "probe"
  let some trueCi := initEnv.checked.get.find? `True
    | throw <| IO.userError "missing True in initEnv"
  assertPolicyErr "replay-base-shadow" "declaration True shadows base environment" do
    TrustedBoundary.validateReplayMap initEnv.toKernelEnv
      (({{}} : Std.HashMap Lean.Name Lean.ConstantInfo).insert `True trueCi) "probe"
  let omittedPartial : Lean.ConstantInfo := .defnInfo {{
    name := `OmittedPartial, levelParams := [], type := Lean.mkConst `True,
    value := Lean.mkConst `True.intro, hints := .opaque, safety := .partial,
    all := [`OmittedPartial] }}
  assertPolicyErr "replay-omitted" "declaration OmittedPartial omitted after kernel replay" do
    discard <| TrustedBoundary.replayKernelEnv initEnv.toKernelEnv
      (({{}} : Std.HashMap Lean.Name Lean.ConstantInfo).insert `OmittedPartial omittedPartial)
      "probe"
  let missingIsModReq ← IO.ofExcept <| Lean.Json.parse {empty_proof_export_lit}
  for (fnLabel, runner) in #[
      ("targetExport-missing-isModule", TrustedBoundary.targetExport missingIsModReq #[]),
      ("targetAudit-missing-isModule", TrustedBoundary.targetAudit missingIsModReq #[])
    ] do
    let rejected ← try
      let _ ← runner
      pure false
    catch e =>
      let msg := e.toString
      unless msg == "Bool expected" do
        throw <| IO.userError s!"{{fnLabel}}: unexpected error {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{fnLabel}}: unexpectedly accepted"
"#,
    ));
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
    let mut checker = f.cargo_checker();
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
    // 1. Live parse-tree round-trip probe + exhaustive negative-vector
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
        (
            "opt-auto-implicit-true",
            "set_option autoImplicit true\n",
            "unsupported option autoImplicit",
        ),
        (
            "opt-auto-implicit-false",
            "set_option autoImplicit false\n",
            "unsupported option autoImplicit",
        ),
        (
            "opt-relaxed-auto-implicit-true",
            "set_option relaxedAutoImplicit true\n",
            "unsupported option relaxedAutoImplicit",
        ),
        (
            "term-opt-auto-implicit-true",
            "def x : Nat := set_option autoImplicit true in 0\n",
            "unsupported option autoImplicit",
        ),
        (
            "cmd-in-opt-auto-implicit-true",
            "set_option autoImplicit true in\ndef x (n : Nat) : pre_ok → True := fun _ => trivial\n",
            "unsupported option autoImplicit",
        ),
        (
            "term-get-elem-bang",
            "def x : Nat := (#[] : Array Nat)[0]!\n",
            "disallowed syntax «term__[_]_!»",
        ),
        (
            "ident-list-head-bang",
            "def x : Nat := ([] : List Nat).head!\n",
            "disallowed identifier head!",
        ),
        (
            "ident-option-get-bang",
            "def x : Nat := (none : Option Nat).get!\n",
            "disallowed identifier get!",
        ),
        (
            "ident-get-elem-bang-qual",
            "def x : Nat := GetElem?.getElem! (#[] : Array Nat) 0\n",
            "disallowed identifier GetElem?.getElem!",
        ),
        (
            "ident-out-of-bounds",
            "def x : Nat := outOfBounds\n",
            "disallowed identifier outOfBounds",
        ),
        (
            "ident-pos-slice-or-panic",
            "def x := @String.Pos.sliceOrPanic\n",
            "disallowed identifier String.Pos.sliceOrPanic",
        ),
        (
            "ident-slice-pos-slice-or-panic",
            "def x := @String.Slice.Pos.sliceOrPanic\n",
            "disallowed identifier String.Slice.Pos.sliceOrPanic",
        ),
        (
            "proj-slice-or-panic",
            "def x (s : String) (pos : s.Pos) (h : pos ≤ pos) := pos.sliceOrPanic pos pos (h := h)\n",
            "disallowed identifier pos.sliceOrPanic",
        ),
        (
            "open-only-head-bang",
            "open List (head!)\n",
            "invalid open item head!",
        ),
        (
            "export-head-bang",
            "export List (head!)\n",
            "invalid export item head!",
        ),
        (
            "open-renaming-head-bang",
            "open List renaming head! -> safeHead\n",
            "invalid open renaming item head! -> safeHead",
        ),
        (
            "open-renaming-slice-or-panic",
            "open String.Slice renaming Pos.sliceOrPanic -> safeSlice\n",
            "invalid open renaming item Pos.sliceOrPanic -> safeSlice",
        ),
        (
            "do-while",
            "def x : Nat := Id.run do\n  let mut i := 5\n  while i > 0 do\n    i := i - 1\n  return i\n",
            "disallowed syntax Lean.Parser.Term.doWhile",
        ),
        (
            "do-repeat",
            "def x : Nat := Id.run do\n  repeat\n    break\n  return 0\n",
            "disallowed syntax Lean.Parser.Term.doRepeat",
        ),
        (
            "do-repeat-until",
            "def x : Nat := Id.run do\n  let mut i := 0\n  repeat\n    i := i + 1\n  until i > 0\n  return i\n",
            "disallowed syntax Lean.Parser.Term.doRepeatUntil",
        ),
        (
            "ident-repeat-m",
            "def x := repeatM\n",
            "disallowed identifier repeatM",
        ),
        // Declaration-namespace guards: entering or declaring under the
        // `Trusted`/`Anneal`/`Proof` roots, every `reservedKernelRoots` root
        // (including `Init` and `Std`), and the `forbiddenSysUvPrefixes`
        // sub-scopes (which an earlier reference guard may reject first),
        // with `_root_` stripped.
        (
            "ns-trusted",
            "namespace Trusted\nend Trusted\n",
            "cannot enter reserved namespace Trusted",
        ),
        (
            "ns-anneal",
            "namespace Anneal\nend Anneal\n",
            "cannot enter reserved namespace Anneal",
        ),
        (
            "ns-proof",
            "namespace Proof\nend Proof\n",
            "cannot enter reserved namespace Proof",
        ),
        (
            "ns-nat",
            "namespace Nat\nend Nat\n",
            "cannot enter reserved namespace Nat",
        ),
        (
            "ns-init",
            "namespace Init\nend Init\n",
            "cannot enter reserved namespace Init",
        ),
        (
            "ns-std",
            "namespace Std\nend Std\n",
            "cannot enter reserved namespace Std",
        ),
        (
            "ns-internal-uv",
            "namespace Internal.UV\nend Internal.UV\n",
            "Internal.UV",
        ),
        (
            "ns-dynlib",
            "namespace Dynlib\nend Dynlib\n",
            "Dynlib",
        ),
        (
            "ns-root-trusted",
            "namespace _root_.Trusted\nend _root_.Trusted\n",
            "_root_.Trusted",
        ),
        (
            "decl-bare-nat",
            "def Nat : Nat := 0\n",
            "cannot declare reserved namespace Nat",
        ),
        (
            "decl-in-std",
            "def Std.evil : Nat := 0\n",
            "cannot declare in reserved namespace Std",
        ),
        (
            "decl-in-internal-uv",
            "def Internal.UV.evil : Nat := 0\n",
            "Internal.UV",
        ),
    ];

    // 1. Live parse-tree round-trip probe + exhaustive check of all negative
    //    vectors against `TrustedBoundary.parseAndInspectSpecCommands` in one
    //    loaded `Init` + `Std` parser environment (~3 s total).
    let fixture = Fixture::new(PROOF);
    let mut checker = fixture.checker();
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
  parseHasKind "def x := (#[] : Array Nat)[0]!" `«term__[_]_!»
  parseHasKind "def x : Nat := Id.run do\n  let mut i := 1\n  while i > 0 do i := i - 1\n  return i" `Lean.Parser.Term.doWhile
  parseHasKind "def x : Nat := Id.run do\n  repeat break\n  return 0" `Lean.Parser.Term.doRepeat
  parseHasKind "def x : Nat := Id.run do\n  let mut i := 0\n  repeat i := i + 1 until i > 0\n  return i" `Lean.Parser.Term.doRepeatUntil
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
  -- Non-`module` specs reject `@[expose]` attributes and section modifiers.
  for (label, body, want) in #[
      ("nonmod-expose-def", "@[expose] def Spec.e : Nat := 0\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n", "unsupported attribute"),
      ("nonmod-expose-sec", "@[expose] section S\nend S\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n", "unsupported section/namespace modifier")
    ] do
    let ctx := Lean.Parser.mkInputContext body label
    let rejected ← try
      TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
        [rootScope] `Spec {{}} {{}} false
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: expected {{want}} in {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
  -- `module`-mode (`isModule := true`) admits `public`, `@[expose]`,
  -- `@[expose] public section`, and `public noncomputable section`, while
  -- rejecting `meta`, `@[local expose]`, and `attribute [-expose]`.
  let modOk := #[
    "@[expose] public section\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\nend\n",
    "public noncomputable section S\ndef Spec.ncHelper : Nat := 0\nend S\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    "@[expose] public def Spec.helper (n : Nat) : Nat := n\npublic theorem Spec.thm : True := trivial\nprivate theorem Spec.privThm : True := trivial\npublic section\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\nend\n"
  ]
  for body in modOk do
    let ctx := Lean.Parser.mkInputContext body "mod-ok"
    TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
      [rootScope] `Spec {{}} {{}} true
  for (label, body, want) in #[
      ("mod-meta-sec", "meta section S\nend S\n", "unsupported section/namespace modifier"),
      ("mod-public-meta-sec", "public meta section S\nend S\n", "unsupported section/namespace modifier"),
      ("mod-meta-def", "meta def Spec.m : Nat := 0\n", "unsupported declaration modifier"),
      ("mod-public-meta-def", "public meta def Spec.m : Nat := 0\n", "unsupported declaration modifier"),
      ("mod-local-expose", "@[local expose] public def f : Nat := 0\n", "unsupported attribute"),
      ("mod-erase-expose", "attribute [-expose] Nat.add\n", "unsupported attribute removal")
    ] do
    let ctx := Lean.Parser.mkInputContext body label
    let rejected ← try
      TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
        [rootScope] `Spec {{}} {{}} true
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: expected {{want}} in {{msg}}"
      pure true
    unless rejected do
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
        let mut c = e2e_f.cargo_checker();
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
    let mut unpinned = base_fixture.cargo_checker();
    unpinned.set_allow_unpinned_lean(true);
    base_fixture.set(
        "Spec",
        TargetRole::Specification,
        &format!("import Model\n{spec_base}"),
    );
    unpinned.run_target(&base_fixture.request).unwrap();

    let wire_samples = [
        "ns-init",
        "ns-internal-uv",
        "decl-bare-nat",
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
        "cmd-in-opt-auto-implicit-true",
        "term-get-elem-bang",
        "ident-list-head-bang",
        "ident-option-get-bang",
        "do-while",
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

    // 3. `SpecPreflight.lean`'s `"spec-preflight"`, which serves the NDJSON
    //    comparator route, admits the base specification during `run_target`
    //    and rejects every wire sample with the same reason on the pinned
    //    toolchain.
    with_spec_preflight(&base_fixture);
    let mut via_sp = base_fixture.cargo_checker();
    via_sp.set_allow_unpinned_lean(true);
    via_sp.set_spec_preflight_mode_via_spec_preflight(true);
    via_sp.run_target(&base_fixture.request).unwrap();
    assert!(
        via_sp.stage().join("control/SpecPreflight.olean").is_file(),
        "`\"spec-preflight\"` did not run SpecPreflight.lean"
    );
    for (idx, (label, snippet, expected)) in
        vectors.iter().filter(|(label, _, _)| wire_samples.contains(label)).enumerate()
    {
        let path = base_fixture.root.join(format!("neg_spec_sp_{idx:03}.lean"));
        fs::write(&path, format!("import Model\n{snippet}{spec_base}")).unwrap();
        let err = via_sp.inspect_spec_preflight(&[("Spec".to_owned(), path)]).unwrap_err();
        assert_eq!(err.code, 1, "SpecPreflight {label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "SpecPreflight {label}: {err}");
        assert!(
            err.message.contains(expected),
            "SpecPreflight {label}: expected {expected:?} in {err}"
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
def optElem : Option Nat := [1, 2][0]?
def optHead : Option Nat := [1, 2].head?
def sumFor : Nat := Id.run do
  let mut acc := 0
  for x in [1, 2, 3] do
    acc := acc + x
  return acc
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
    let mut checker = f.cargo_checker();
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
    let mut checker = f.cargo_checker();
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
        (
            "get-elem-bang",
            "def Spec.unusedGetElemBang : Nat := (#[] : Array Nat)[0]!\n",
            "cannot reference GetElem?.getElem!",
        ),
        (
            "list-head-bang",
            "def Spec.unusedHeadBang : Nat := ([] : List Nat).head!\n",
            "cannot reference List.head!",
        ),
        (
            "option-get-bang",
            "def Spec.unusedGetBang : Nat := (none : Option Nat).get!\n",
            "cannot reference Option.get!",
        ),
        (
            "do-while-loop",
            "def Spec.unusedWhile : Nat := Id.run do\n  let mut x := 5\n  while x > 0 do\n    x := x - 1\n  return x\n",
            "disallowed constant Lean.Loop",
        ),
        (
            "out-of-bounds",
            "def Spec.unusedOob : Nat := outOfBounds\n",
            "cannot reference outOfBounds",
        ),
        (
            "pos-slice-or-panic",
            "def Spec.unusedPosSliceOrPanic := @String.Pos.sliceOrPanic\n",
            "cannot reference String.Pos.sliceOrPanic",
        ),
        (
            "slice-pos-slice-or-panic",
            "def Spec.unusedSlicePosSliceOrPanic := @String.Slice.Pos.sliceOrPanic\n",
            "cannot reference String.Slice.Pos.sliceOrPanic",
        ),
        (
            "repeat-m",
            "def Spec.unusedRepeatM : Nat := Id.run (repeatM (fun _ => pure (Sum.inr 0)) ())\n",
            "disallowed constant repeatM",
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
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("module-system artifact unsupported in Spec"),
        "expected pre-import isModule mismatch rejection: {err}"
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

#[test]
fn target_audit_rejects_wrong_program_arity_fail_closed() {
    let make_fixture = |extra_field_decl: &str, extra_field_val: &str| {
        let mut f = Fixture::new(
            "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := And.intro True.intro rfl\n",
        );
        f.set(
            "Model",
            TargetRole::Model,
            &format!(
                "prelude\nimport Init.Prelude\nimport Init.Core\n\
                 namespace Trusted.MirAst\n\
                 structure Program where\n\
                   bodies : List Nat\n\
                   entryDefId : Nat\n\
                   pointerWidthBits : Nat\n\
                   mirProfileVersion : Nat\n\
                   scope : Nat\n\
                   overflowChecks : Bool\n\
                   panicStrategy : Nat\n\
                 {extra_field_decl}\
                 end Trusted.MirAst\n\
                 namespace Trusted.MirSemantics\n\
                 structure Specs where\n\
                   safety : String → List Nat → Prop\n\
                   property : Trusted.MirAst.Program → Prop\n\
                 structure Crate where\n\
                   program : Trusted.MirAst.Program\n\
                   specs : Specs\n\
                 def UnitTheorem (c : Crate) : Prop :=\n\
                   c.specs.safety \"\" List.nil ∧ c.specs.property c.program\n\
                 end Trusted.MirSemantics\n"
            ),
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            &format!(
                "prelude\nimport Model\n\
                 def Captured.program : Trusted.MirAst.Program :=\n\
                   Trusted.MirAst.Program.mk List.nil 0 64 1 0 false 0{extra_field_val}\n"
            ),
        );
        f.set(
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\n\
             def Spec.specs : Trusted.MirSemantics.Specs :=\n\
               Trusted.MirSemantics.Specs.mk (fun _ _ => True) (fun p => p.pointerWidthBits = 64)\n",
        );
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Model\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n\
               Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f
    };

    // A 7-field `Program` (wrong arity) must fail closed, never silently skip
    // linting.
    let f_wrong_arity = make_fixture("", "");
    f_wrong_arity.reject_audit("unexpected Program arity");

    // Control: 8-field `Program` (expected arity) passes cleanly.
    let f_ok = make_fixture("hasLocalPanicHandler : Bool\n", " true");
    let ok_report = f_ok.run().unwrap();
    assert_eq!(ok_report["replay"], true);
}

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

/// Compiling a `TargetRole::Specification` module passes `-DautoImplicit=false`
/// and `-DrelaxedAutoImplicit=false`, rejecting undeclared multi-letter and
/// single-letter typo identifiers at `compile-Spec` while leaving
/// `TargetRole::Proof` auto-implicits unaffected; `set_option autoImplicit true`
/// inside a specification is also rejected fail-closed in `"spec-preflight"`.
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

/// Stage `trusted/audit/SpecPreflight.lean` into `f` so its `"sysroot-consts"`
/// and `"target-consts"` modes (which only it implements) run on the pinned
/// Lean binary (with unpinned `Init` admission, as the non-`prelude` fixture
/// proof needs), and return the roles and staged-header `isModule` flags of the
/// fixture's modules.
fn with_spec_preflight(f: &Fixture) -> (BTreeMap<String, TargetRole>, BTreeMap<String, bool>) {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let rel = "trusted/audit/SpecPreflight.lean";
    fs::copy(repo.join(rel), f.root.join(rel)).unwrap();
    let roles = f.request.modules.iter().map(|m| (m.module.clone(), m.role)).collect();
    let is_module = f.request.modules.iter().map(|m| (m.module.clone(), false)).collect();
    (roles, is_module)
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

/// Writes `source` to `script` and executes it via `lean --run`.
fn run_lean_script(checker: &mut Checker, label: &str, script: &Path, source: &str) {
    fs::write(script, source).unwrap();
    checker
        .process(
            label,
            &["-j1".into(), "-M4096".into(), "--run".into(), script.to_string_lossy().into()],
        )
        .unwrap();
}

/// Verifies `lean4#16677` defense-in-depth hardening in `TrustedBoundary.lean`:
/// - mismatched `constNames` vs `ConstantInfo.name` in `.olean` inventories;
/// - intra-module duplicate names in `.library` `.olean` inventories; and
/// - `TargetRole::Specification` `p._unsafe_rec` with mismatched type.
#[test]
fn target_audit_rejects_key_mismatch_dup_library_and_unsafe_rec_type_mismatch() {
    use std::collections::BTreeMap;

    use anneal_audit::{ImportEdge, ModuleArtifacts};

    // 1. Mismatched `constNames` key (`Captured.wrongKey` vs `Captured.aux`).
    let mut f_key = Fixture::new(PROOF);
    f_key.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.aux : Nat := 1\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
    );
    let mut c_key = f_key.accepted_checker();
    let cap_olean = c_key.stage().join("lib/Captured.olean");
    let key_script = c_key.stage().join("ForgeKeyMismatch.lean");
    run_lean_script(
        &mut c_key,
        "forge-key-mismatch",
        &key_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let patched := data.constNames.map (fun n =>\n    \
                 if n == `Captured.aux then `Captured.wrongKey else n)\n  \
               saveModuleData p `Captured {{ data with constNames := patched }}\n",
            cap_olean.to_string_lossy()
        ),
    );
    reject_inspected(&mut c_key, f_key.request.clone(), "mismatched checked environment key");

    // 2. Intra-module duplicate declaration in a `.library` module must fail
    //    closed rather than collapsing silently via `NameSet.ofList`.
    let f_dup = Fixture::new(PROOF);
    let mut c_dup = f_dup.accepted_checker();
    let adm = c_dup.admitted().unwrap();
    let dep = adm.foundation_modules().into_iter().next().unwrap().to_owned();
    let dup_lib_olean = c_dup.stage().join("lib/DupLib.olean");
    let dup_script = c_dup.stage().join("ForgeDupLib.lean");
    run_lean_script(
        &mut c_dup,
        "forge-dup-lib",
        &dup_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `DupLib.t\n    \
                 levelParams := []\n    \
                 type := .const `True []\n    \
                 value := .const `True.intro []\n    \
                 all := [`DupLib.t]\n  \
               }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false\n    \
                 imports := #[{{ module := `{dep} }}]\n    \
                 constNames := #[`DupLib.t, `DupLib.t]\n    \
                 constants := #[ci, ci]\n    \
                 extraConstNames := #[]\n    \
                 entries := #[]\n  \
               }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `DupLib md\n",
            dup_lib_olean.to_string_lossy()
        ),
    );
    let dup_avail = BTreeMap::from([("olean", dup_lib_olean.to_string_lossy().into_owned())]);
    let dup_arts = ModuleArtifacts::from_available(&dup_avail, "fixture", String::new).unwrap();
    let adm_mut = c_dup.admitted_mut().unwrap();
    adm_mut.artifacts.insert("DupLib".into(), dup_arts);
    adm_mut.library_modules.insert("DupLib".into());
    adm_mut.graph.insert(
        "DupLib".into(),
        vec![ImportEdge {
            module: dep,
            import_all: false,
            is_exported: true,
            is_meta: false,
        }],
    );
    reject_inspected(
        &mut c_dup,
        f_dup.request.clone(),
        "duplicate target library declaration DupLib.t",
    );

    // 3. `TargetRole::Specification` `p._unsafe_rec` with mismatched type fails
    //    `pairedSpecUnsafeRecParent?` and is rejected as unreplayable partial.
    let f_rec = Fixture::new(PROOF);
    let mut c_rec = f_rec.accepted_checker();
    let spec_olean = c_rec.stage().join("lib/Spec.olean");
    let rec_script = c_rec.stage().join("ForgeBadUnsafeRec.lean");
    run_lean_script(
        &mut c_rec,
        "forge-bad-unsafe-rec",
        &rec_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let parentCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Spec.foo\n    \
                 levelParams := []\n    \
                 type := .const `Nat []\n    \
                 value := .lit (.natVal 0)\n    \
                 hints := .abbrev\n    \
                 safety := .safe\n    \
                 all := [`Spec.foo]\n  \
               }}\n  \
               let badRecCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Spec.foo._unsafe_rec\n    \
                 levelParams := []\n    \
                 type := .const `Bool []\n    \
                 value := .const `Bool.true []\n    \
                 hints := .abbrev\n    \
                 safety := .partial\n    \
                 all := [`Spec.foo._unsafe_rec]\n  \
               }}\n  \
               let newNames := data.constNames ++ #[`Spec.foo, `Spec.foo._unsafe_rec]\n  \
               let newConsts := data.constants ++ #[parentCi, badRecCi]\n  \
               saveModuleData p `Spec \
                 {{ data with constNames := newNames, constants := newConsts }}\n",
            spec_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_rec,
        f_rec.request.clone(),
        "unsafe/partial logical dependency Spec.foo._unsafe_rec",
    );

    // 4. Duplicate constant inside a `.foundation` `.olean` is rejected by
    //    `verifyModuleHeaderInventory` in `targetAudit`'s `.foundation` arm.
    let f_found = Fixture::new(PROOF);
    let mut c_found = f_found.accepted_checker();
    let orig_core = c_found.admitted().unwrap().artifacts["Init.Core"].clone();
    let orig_core_path = orig_core
        .olean_parts
        .first()
        .expect("Init.Core olean");
    let forged_core = c_found.stage().join("lib/ForgedInitCore.olean");
    let found_script = c_found.stage().join("ForgeInitCore.lean");
    let found_src = format!(
        "import Lean\n\
         open Lean in\n\
         def main : IO Unit := do\n  \
           let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
           let extra := data.constants[0]!\n  \
           let md : ModuleData := {{ data with\n    \
             isModule := false,\n    \
             constNames := data.constNames.push extra.name,\n    \
             constants := data.constants.push extra }}\n  \
           saveModuleData (System.FilePath.mk {:?}) `Init.Core md\n",
        orig_core_path.as_str(),
        forged_core.to_string_lossy()
    );
    run_lean_script(&mut c_found, "forge-foundation-dup", &found_script, &found_src);
    let forged_avail = BTreeMap::from([("olean", forged_core.to_string_lossy().into_owned())]);
    let forged_arts = ModuleArtifacts::from_available(&forged_avail, "fixture", String::new).unwrap();
    c_found.admitted_mut().unwrap().artifacts.insert("Init.Core".into(), forged_arts);
    reject_inspected(
        &mut c_found,
        f_found.request.clone(),
        "duplicate target declaration",
    );

    // 5. `Model` `.olean` re-declaring `propext` as a theorem overwrites
    //    `stored` via Lean `subsumesInfo`, exercising `targetAudit`'s
    //    `.foundation` reconciliation (`sameConstantShape stored ci`).
    let f_hijack = Fixture::new(PROOF);
    let mut c_model_hijack = f_hijack.accepted_checker();
    let hijack_model = c_model_hijack.stage().join("lib/Model.olean");
    let hijack_prefix = c_model_hijack.admitted().unwrap().prefix.clone();
    let hijack_script = c_model_hijack.stage().join("ForgeModelPropextHijack.lean");
    let hijack_src = format!(
        "import Lean\n\
         open Lean in\n\
         def main : IO Unit := do\n  \
           initSearchPath (System.FilePath.mk {:?})\n  \
           let env ← importModules #[{{ module := `Init.Core }}] {{}} \
             (trustLevel := 0) (plugins := #[]) (loadExts := false) \
             (level := .private)\n  \
           let some px := env.checked.get.find? `propext \
             | throw (IO.userError \"missing propext\")\n  \
           let p := System.FilePath.mk {:?}\n  \
           let (data, _) ← readModuleData p\n  \
           let body := Expr.const `True []\n  \
           let fakeThm : ConstantInfo := .thmInfo {{\n    \
             name := `propext, levelParams := px.levelParams,\n    \
             type := px.type, value := body, all := [`propext] }}\n  \
           let newNames := data.constNames.push `propext\n  \
           let newConsts := data.constants.push fakeThm\n  \
           saveModuleData p `Model \
             {{ data with constNames := newNames, constants := newConsts }}\n",
        hijack_prefix.to_string_lossy(),
        hijack_model.to_string_lossy()
    );
    run_lean_script(&mut c_model_hijack, "forge-model-propext-hijack", &hijack_script, &hijack_src);
    reject_inspected(
        &mut c_model_hijack,
        f_hijack.request.clone(),
        "stored target declaration differs propext",
    );

    // 6. A `.library` `.olean` overriding a `.foundation` theorem (`Iff.refl`)
    //    via `subsumesInfo` with a proof body referencing a `.source` constant
    //    (`Proof.verify`) is rejected by `pendingSourceAlternates` checking
    //    both `stored` and `ci` even when `Proof.verify` never references
    //    `Iff.refl`.
    let f_lib_sub = Fixture::new(PROOF);
    let mut c_lib_sub = f_lib_sub.accepted_checker();
    let lib_sub_prefix = c_lib_sub.admitted().unwrap().prefix.clone();
    let proof_olean_path = c_lib_sub.admitted().unwrap().artifacts["Proof"]
        .olean_parts
        .first()
        .expect("Proof olean")
        .clone();
    let lib_sub_olean = c_lib_sub.stage().join("lib/ZZZZSubsumesLib.olean");
    let lib_sub_script = c_lib_sub.stage().join("ForgeLibSubsumesFoundation.lean");
    run_lean_script(
        &mut c_lib_sub,
        "forge-lib-subsumes-foundation",
        &lib_sub_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo iffTv) := env.checked.get.find? `Iff.refl \
                 | throw (IO.userError \"missing Iff.refl\")\n  \
               let (proofData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let some rootCi := proofData.constants.find? (·.name == `Proof.verify) \
                 | throw (IO.userError \"missing Proof.verify\")\n  \
               let wrapped := Expr.letE `_src rootCi.type \
                 (.const `Proof.verify []) iffTv.value false\n  \
               let forged : ConstantInfo := .thmInfo {{ iffTv with value := wrapped }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Iff.refl],\n    \
                 constants := #[forged],\n    \
                 extraConstNames := #[],\n    \
                 entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `ZZZZSubsumesLib md\n",
            lib_sub_prefix.to_string_lossy(),
            proof_olean_path.as_str(),
            lib_sub_olean.to_string_lossy()
        ),
    );
    let lib_sub_avail =
        BTreeMap::from([("olean", lib_sub_olean.to_string_lossy().into_owned())]);
    let lib_sub_arts =
        ModuleArtifacts::from_available(&lib_sub_avail, "fixture", String::new).unwrap();
    {
        let adm_mut = c_lib_sub.admitted_mut().unwrap();
        adm_mut.artifacts.insert("ZZZZSubsumesLib".into(), lib_sub_arts);
        adm_mut.library_modules.insert("ZZZZSubsumesLib".into());
        adm_mut.graph.insert(
            "ZZZZSubsumesLib".into(),
            vec![ImportEdge {
                module: "Init.Core".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
    }
    reject_inspected(
        &mut c_lib_sub,
        f_lib_sub.request.clone(),
        "installed library Iff.refl references target source Proof.verify",
    );

    // 7. Realizing a `.foundation` theorem (`flip.eq_1`) inside a `.source`
    //    `.olean` via `subsumesInfo` derives `storedOrigin` from the actual
    //    defining module (`storedRoleMap`): `Expected` referencing
    //    `Spec.specs` (`TargetRole::Specification`, allowed for `Expected`)
    //    succeeds and kernel-checks both alternates, whereas `Model`
    //    referencing `Spec.specs` (`TargetRole::Model` cannot depend on
    //    `Specification`) fails closed with `"target authority violation"`.
    let forge_flip_sub = |checker: &mut anneal_audit::Checker,
                          label: &str,
                          target_mod: &str,
                          target_olean: &std::path::Path| {
        let prefix = checker.admitted().unwrap().prefix.clone();
        let spec_olean = checker.stage().join("lib/Spec.olean");
        let script = checker.stage().join(format!("{label}.lean"));
        run_lean_script(
            checker,
            label,
            &script,
            &format!(
                "import Lean\n\
                 open Lean in\n\
                 def main : IO Unit := do\n  \
                   initSearchPath (System.FilePath.mk {:?})\n  \
                   let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                     (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                     (level := .private)\n  \
                   let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                     | throw (IO.userError \"missing flip.eq_1\")\n  \
                   let (specData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
                   let some specCi := specData.constants.find? (·.name == `Spec.specs) \
                     | throw (IO.userError \"missing Spec.specs\")\n  \
                   let p := System.FilePath.mk {:?}\n  \
                   let (modData, _) ← readModuleData p\n  \
                   let wrapped := Expr.letE `_spec specCi.type \
                     (.const `Spec.specs []) flipTv.value false\n  \
                   let forged : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
                   saveModuleData p `{target_mod} {{ modData with\n    \
                     constNames := modData.constNames.push `flip.eq_1,\n    \
                     constants := modData.constants.push forged }}\n",
                prefix.to_string_lossy(),
                spec_olean.to_string_lossy(),
                target_olean.to_string_lossy()
            ),
        );
    };
    let f_src_sub = Fixture::new(PROOF);
    let mut c_src_sub = f_src_sub.accepted_checker();
    let expected_olean = c_src_sub.stage().join("lib/Expected.olean");
    forge_flip_sub(
        &mut c_src_sub,
        "forge-expected-subsumes-foundation",
        "Expected",
        &expected_olean,
    );
    let src_sub_ok = c_src_sub
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_src_sub.request.clone(),
        })
        .unwrap();
    assert_eq!(src_sub_ok["replay"], true, "{src_sub_ok}");
    assert_eq!(src_sub_ok["exactType"], true, "{src_sub_ok}");
    assert!(
        src_sub_ok["checkedAlternateProofs"].as_u64().unwrap_or(0) >= 2,
        "expected alternate proof checks for realized flip.eq_1: {src_sub_ok}"
    );

    let f_model_sub = Fixture::new(PROOF);
    let mut c_model_sub = f_model_sub.accepted_checker();
    let model_olean_for_sub = c_model_sub.stage().join("lib/Model.olean");
    forge_flip_sub(
        &mut c_model_sub,
        "forge-model-subsumes-foundation",
        "Model",
        &model_olean_for_sub,
    );
    reject_inspected(
        &mut c_model_sub,
        f_model_sub.request.clone(),
        "target authority violation flip.eq_1 references Spec.specs",
    );

    // 7c. A `.library` `.olean` exporting the exact same `ConstantInfo` body
    //     for `flip.eq_1` as a later `.source` `.olean` (`Expected`) must still
    //     be rejected via `isLibraryStored` even though `storedOrigin` resolves
    //     to `.source .expected`.
    let f_lib_dup_sub = Fixture::new(PROOF);
    let mut c_lib_dup_sub = f_lib_dup_sub.accepted_checker();
    let lib_dup_prefix = c_lib_dup_sub.admitted().unwrap().prefix.clone();
    let lib_dup_spec = c_lib_dup_sub.stage().join("lib/Spec.olean");
    let lib_dup_exp = c_lib_dup_sub.stage().join("lib/Expected.olean");
    let lib_dup_mod = c_lib_dup_sub.stage().join("lib/ZZZZDupLib.olean");
    let lib_dup_script = c_lib_dup_sub.stage().join("ForgeLibAndExpectedDup.lean");
    run_lean_script(
        &mut c_lib_dup_sub,
        "forge-lib-and-expected-dup",
        &lib_dup_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (specData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let some specCi := specData.constants.find? (·.name == `Spec.specs) \
                 | throw (IO.userError \"missing Spec.specs\")\n  \
               let wrapped := Expr.letE `_spec specCi.type \
                 (.const `Spec.specs []) flipTv.value false\n  \
               let forged : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
               let pExp := System.FilePath.mk {:?}\n  \
               let (expData, _) ← readModuleData pExp\n  \
               saveModuleData pExp `Expected {{ expData with\n    \
                 constNames := expData.constNames.push `flip.eq_1,\n    \
                 constants := expData.constants.push forged }}\n  \
               let libMd : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`flip.eq_1],\n    \
                 constants := #[forged],\n    \
                 extraConstNames := #[],\n    \
                 entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `ZZZZDupLib libMd\n",
            lib_dup_prefix.to_string_lossy(),
            lib_dup_spec.to_string_lossy(),
            lib_dup_exp.to_string_lossy(),
            lib_dup_mod.to_string_lossy()
        ),
    );
    let lib_dup_avail =
        BTreeMap::from([("olean", lib_dup_mod.to_string_lossy().into_owned())]);
    let lib_dup_arts =
        ModuleArtifacts::from_available(&lib_dup_avail, "fixture", String::new).unwrap();
    {
        let adm_mut = c_lib_dup_sub.admitted_mut().unwrap();
        adm_mut.artifacts.insert("ZZZZDupLib".into(), lib_dup_arts);
        adm_mut.library_modules.insert("ZZZZDupLib".into());
        adm_mut.graph.insert(
            "ZZZZDupLib".into(),
            vec![ImportEdge {
                module: "Init.Core".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
    }
    reject_inspected(
        &mut c_lib_dup_sub,
        f_lib_dup_sub.request.clone(),
        "installed library flip.eq_1 references target source Spec.specs",
    );

    // 7d. A first-exporter `.source` module (`Model`) declaring a theorem
    //     (`Model.badRealized`) referencing `Spec.specs` cannot hide behind a
    //     later `Expected` module exporting a byte-identical copy.
    let f_model_dup = Fixture::new(PROOF);
    let mut c_model_dup = f_model_dup.accepted_checker();
    let model_dup_spec = c_model_dup.stage().join("lib/Spec.olean");
    let model_dup_model = c_model_dup.stage().join("lib/Model.olean");
    let model_dup_exp = c_model_dup.stage().join("lib/Expected.olean");
    let model_dup_script = c_model_dup.stage().join("ForgeModelAndExpectedDup.lean");
    run_lean_script(
        &mut c_model_dup,
        "forge-model-and-expected-dup",
        &model_dup_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let (specData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let some specCi := specData.constants.find? (·.name == `Spec.specs) \
                 | throw (IO.userError \"missing Spec.specs\")\n  \
               let badThm : ConstantInfo := .thmInfo {{\n    \
                 name := `Model.badRealized, levelParams := [],\n    \
                 type := .const `True [],\n    \
                 value := Expr.letE `_spec specCi.type (.const `Spec.specs []) \
                   (.const `True.intro []) false,\n    \
                 all := [`Model.badRealized] }}\n  \
               for (modName, pathStr) in [(`Model, {:?}), (`Expected, {:?})] do\n    \
                 let p := System.FilePath.mk pathStr\n    \
                 let (d, _) ← readModuleData p\n    \
                 saveModuleData p modName {{ d with\n      \
                   constNames := d.constNames.push `Model.badRealized,\n      \
                   constants := d.constants.push badThm }}\n",
            model_dup_spec.to_string_lossy(),
            model_dup_model.to_string_lossy(),
            model_dup_exp.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_model_dup,
        f_model_dup.request.clone(),
        "target authority violation Model.badRealized references Spec.specs",
    );

    // 8. A non-proof `.source` `.olean` (`Model`) injecting a `.thmInfo` under
    //    an `Init.Prelude` `extraConstNames` IR-helper name (`mixHash._boxed`)
    //    is rejected by `targetAudit`'s `.foundation` `extraConstNames` check.
    let f_extra_src = Fixture::new(PROOF);
    let mut c_extra_src = f_extra_src.accepted_checker();
    let model_extra_olean = c_extra_src.stage().join("lib/Model.olean");
    let extra_src_script = c_extra_src.stage().join("ForgeModelExtraCollide.lean");
    run_lean_script(
        &mut c_extra_src,
        "forge-model-extra-collide",
        &extra_src_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let badThm : ConstantInfo := .thmInfo {{\n    \
                 name := `mixHash._boxed, levelParams := [],\n    \
                 type := .const `False [], value := .const `True.intro [],\n    \
                 all := [`mixHash._boxed] }}\n  \
               saveModuleData p `Model {{ data with\n    \
                 constNames := data.constNames.push `mixHash._boxed,\n    \
                 constants := data.constants.push badThm }}\n",
            model_extra_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_extra_src,
        f_extra_src.request.clone(),
        "uninventoried kernel compiler helper mixHash._boxed",
    );

    // 9. An exported `Proof` module declaring a constant under an
    //    `Init.Prelude` `extraConstNames` IR-helper name (`mixHash._boxed`) is
    //    rejected before `originOf` can misclassify it as `.foundation`.
    let f_extra_prf = Fixture::new(PROOF);
    let mut c_extra_prf = f_extra_prf.accepted_checker();
    let proof_extra_olean = c_extra_prf.stage().join("lib/Proof.olean");
    let extra_prf_script = c_extra_prf.stage().join("ForgeProofExtraCollide.lean");
    run_lean_script(
        &mut c_extra_prf,
        "forge-proof-extra-collide",
        &extra_prf_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let badThm : ConstantInfo := .thmInfo {{\n    \
                 name := `mixHash._boxed, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`mixHash._boxed] }}\n  \
               saveModuleData p `Proof {{ data with\n    \
                 constNames := data.constNames.push `mixHash._boxed,\n    \
                 constants := data.constants.push badThm }}\n",
            proof_extra_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_extra_prf,
        f_extra_prf.request.clone(),
        "target declaration mixHash._boxed collides with imported IR helper",
    );
}

/// Verifies `targetAudit` identical-copy role tracking:
/// 1. A `.foundation` module exporting a theorem (`Target.Alt`) referencing
///    `.library` (`ZZZZLibMod.secret`) cannot mask the violation behind a
///    byte-identical copy in a later `.source` module (`Expected`), either
///    directly or after an earlier `.foundation` declaration (`ZZZZF0`).
/// 2. Conversely, a valid `.library` theorem referencing another `.library`
///    declaration also exported identically in `Expected` continues to pass.
#[test]
fn target_audit_rejects_foundation_identical_copy_with_later_source() {
    use anneal_audit::{ImportEdge, InspectorRequest, ModuleArtifacts};

    // Case A & B: `.foundation` `ZZZZFBad` exports `Target.Alt` referencing
    // `.library` `ZZZZLibMod.secret` alongside an identical copy in `Expected`
    // (both direct first-export `use_f0 = false` and post-`ZZZZF0` realization
    // `use_f0 = true`).
    for use_f0 in [false, true] {
        let f = Fixture::new(PROOF);
        let mut c = f.accepted_checker();
        let dep_core = "Init.Core".to_string();
        let f0_olean = c.stage().join("lib/ZZZZF0.olean");
        let lib_olean = c.stage().join("lib/ZZZZLibMod.olean");
        let fbad_olean = c.stage().join("lib/ZZZZFBad.olean");
        let exp_olean = c.stage().join("lib/Expected.olean");
        let script = c.stage().join(if use_f0 {
            "ForgeFoundationLibCopyAfterF0.lean"
        } else {
            "ForgeFoundationLibCopy.lean"
        });
        run_lean_script(
            &mut c,
            if use_f0 {
                "forge-foundation-lib-copy-f0"
            } else {
                "forge-foundation-lib-copy"
            },
            &script,
            &format!(
                "import Lean\n\
                 open Lean in\n\
                 def main : IO Unit := do\n  \
                   let secretThm : ConstantInfo := .thmInfo {{\n    \
                     name := `ZZZZLibMod.secret, levelParams := [],\n    \
                     type := .const `True [], value := .const `True.intro [],\n    \
                     all := [`ZZZZLibMod.secret] }}\n  \
                   saveModuleData (System.FilePath.mk {:?}) `ZZZZLibMod {{\n    \
                     isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                     constNames := #[`ZZZZLibMod.secret], constants := #[secretThm],\n    \
                     extraConstNames := #[], entries := #[] }}\n  \
                   if {use_f0} then\n    \
                     let baseThm : ConstantInfo := .thmInfo {{\n      \
                       name := `Target.Alt, levelParams := [],\n      \
                       type := .const `True [], value := .const `True.intro [],\n      \
                       all := [`Target.Alt] }}\n    \
                     saveModuleData (System.FilePath.mk {:?}) `ZZZZF0 {{\n      \
                       isModule := false, imports := #[{{ module := `Init.Core }}],\n      \
                       constNames := #[`Target.Alt], constants := #[baseThm],\n      \
                       extraConstNames := #[], entries := #[] }}\n  \
                   let badVal := Expr.letE `_sec (.const `True [])\n    \
                     (.const `ZZZZLibMod.secret []) (.const `True.intro []) false\n  \
                   let badThm : ConstantInfo := .thmInfo {{\n    \
                     name := `Target.Alt, levelParams := [],\n    \
                     type := .const `True [], value := badVal,\n    \
                     all := [`Target.Alt] }}\n  \
                   let fbadImports := if {use_f0} then\n    \
                     #[{{ module := `Init.Core }}, {{ module := `ZZZZLibMod }}, {{ module := `ZZZZF0 }}]\n  \
                     else #[{{ module := `Init.Core }}, {{ module := `ZZZZLibMod }}]\n  \
                   saveModuleData (System.FilePath.mk {:?}) `ZZZZFBad {{\n    \
                     isModule := false, imports := fbadImports,\n    \
                     constNames := #[`Target.Alt], constants := #[badThm],\n    \
                     extraConstNames := #[], entries := #[] }}\n  \
                   let expPath := System.FilePath.mk {:?}\n  \
                   let (expData, _) ← readModuleData expPath\n  \
                   saveModuleData expPath `Expected {{ expData with\n    \
                     constNames := expData.constNames.push `Target.Alt,\n    \
                     constants := expData.constants.push badThm }}\n",
                lib_olean.to_string_lossy(),
                f0_olean.to_string_lossy(),
                fbad_olean.to_string_lossy(),
                exp_olean.to_string_lossy(),
            ),
        );
        let mk_edge = |m: &str| ImportEdge {
            module: m.to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        };
        let lib_arts = ModuleArtifacts::from_available(
            &BTreeMap::from([("olean", lib_olean.to_string_lossy().into_owned())]),
            "fixture",
            String::new,
        )
        .unwrap();
        let fbad_arts = ModuleArtifacts::from_available(
            &BTreeMap::from([("olean", fbad_olean.to_string_lossy().into_owned())]),
            "fixture",
            String::new,
        )
        .unwrap();
        let adm = c.admitted_mut().unwrap();
        adm.artifacts.insert("ZZZZLibMod".into(), lib_arts);
        adm.library_modules.insert("ZZZZLibMod".into());
        adm.graph.insert("ZZZZLibMod".into(), vec![mk_edge(&dep_core)]);
        let mut fbad_edges = vec![mk_edge(&dep_core), mk_edge("ZZZZLibMod")];
        if use_f0 {
            let f0_arts = ModuleArtifacts::from_available(
                &BTreeMap::from([("olean", f0_olean.to_string_lossy().into_owned())]),
                "fixture",
                String::new,
            )
            .unwrap();
            adm.artifacts.insert("ZZZZF0".into(), f0_arts);
            adm.foundation_graph
                .insert("ZZZZF0".into(), vec![mk_edge(&dep_core)]);
            adm.graph.insert("ZZZZF0".into(), vec![mk_edge(&dep_core)]);
            fbad_edges.push(mk_edge("ZZZZF0"));
        }
        adm.artifacts.insert("ZZZZFBad".into(), fbad_arts);
        adm.foundation_graph
            .insert("ZZZZFBad".into(), fbad_edges.clone());
        adm.graph.insert("ZZZZFBad".into(), fbad_edges);
        reject_inspected(
            &mut c,
            f.request.clone(),
            "target authority violation Target.Alt references ZZZZLibMod.secret",
        );
    }

    // Case C: Legitimate `.library` theorem referencing another `.library`
    // declaration (`ZZZZLibGood.helper`) with a byte-identical copy in
    // `Expected` must continue to be accepted (no `.foundation` confusion).
    let f_ok = Fixture::new(PROOF);
    let mut c_ok = f_ok.accepted_checker();
    let lib_ok_olean = c_ok.stage().join("lib/ZZZZLibGood.olean");
    let exp_ok_olean = c_ok.stage().join("lib/Expected.olean");
    let ok_script = c_ok.stage().join("ForgeLibOkCopy.lean");
    run_lean_script(
        &mut c_ok,
        "forge-lib-ok-copy",
        &ok_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let helperThm : ConstantInfo := .thmInfo {{\n    \
                 name := `ZZZZLibGood.helper, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`ZZZZLibGood.helper] }}\n  \
               let sharedVal := Expr.letE `_hlp (.const `True [])\n    \
                 (.const `ZZZZLibGood.helper []) (.const `True.intro []) false\n  \
               let sharedThm : ConstantInfo := .thmInfo {{\n    \
                 name := `Target.LibShared, levelParams := [],\n    \
                 type := .const `True [], value := sharedVal,\n    \
                 all := [`Target.LibShared] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `ZZZZLibGood {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`ZZZZLibGood.helper, `Target.LibShared],\n    \
                 constants := #[helperThm, sharedThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let expPath := System.FilePath.mk {:?}\n  \
               let (expData, _) ← readModuleData expPath\n  \
               saveModuleData expPath `Expected {{ expData with\n    \
                 constNames := expData.constNames.push `Target.LibShared,\n    \
                 constants := expData.constants.push sharedThm }}\n",
            lib_ok_olean.to_string_lossy(),
            exp_ok_olean.to_string_lossy(),
        ),
    );
    let lib_ok_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", lib_ok_olean.to_string_lossy().into_owned())]),
        "fixture",
        String::new,
    )
    .unwrap();
    let adm_ok = c_ok.admitted_mut().unwrap();
    adm_ok.artifacts.insert("ZZZZLibGood".into(), lib_ok_arts);
    adm_ok.library_modules.insert("ZZZZLibGood".into());
    adm_ok.graph.insert(
        "ZZZZLibGood".into(),
        vec![ImportEdge {
            module: "Init.Core".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        }],
    );
    let ok_rep = c_ok
        .inspect(InspectorRequest::TargetAudit {
            request: f_ok.request.clone(),
        })
        .unwrap();
    assert_eq!(ok_rep["replay"], true, "{ok_rep}");
}

/// Verifies `targetAudit` admission guards on uninventoried library and
/// source `extraConstNames` declarations using never-reached theorems so
/// downstream reach-time checks cannot mask regressions.
#[test]
fn target_audit_rejects_uninventoried_library_and_source_extra_helpers() {
    use std::collections::BTreeMap;

    use anneal_audit::{ImportEdge, ModuleArtifacts};

    let f_src = Fixture::new(PROOF);
    let mut c_src = f_src.accepted_checker();
    let adm_src = c_src.admitted().unwrap();
    let dep_src = adm_src.foundation_modules().into_iter().next().unwrap().to_owned();
    let lib_src_olean = c_src.stage().join("lib/LibSrc.olean");
    let cap_src_olean = c_src.stage().join("lib/Captured.olean");
    let forge_src = c_src.stage().join("ForgeSourceUninventoriedLib.lean");
    run_lean_script(
        &mut c_src,
        "forge-source-uninventoried-lib",
        &forge_src,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let libMd : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `{dep_src} }}],\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[`LibSrc.uninv], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `LibSrc libMd\n  \
               let capPath := System.FilePath.mk {:?}\n  \
               let (capData, _) ← readModuleData capPath\n  \
               let uninvThm : ConstantInfo := .thmInfo {{\n    \
                 name := `LibSrc.uninv, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`LibSrc.uninv] }}\n  \
               saveModuleData capPath `Captured {{ capData with\n    \
                 imports := capData.imports.push {{ module := `LibSrc }},\n    \
                 constNames := capData.constNames.push `LibSrc.uninv,\n    \
                 constants := capData.constants.push uninvThm }}\n",
            lib_src_olean.to_string_lossy(),
            cap_src_olean.to_string_lossy(),
        ),
    );
    let lib_src_avail = BTreeMap::from([("olean", lib_src_olean.to_string_lossy().into_owned())]);
    let lib_src_arts = ModuleArtifacts::from_available(&lib_src_avail, "fixture", String::new).unwrap();
    let adm_src_mut = c_src.admitted_mut().unwrap();
    adm_src_mut.artifacts.insert("LibSrc".into(), lib_src_arts);
    adm_src_mut.library_modules.insert("LibSrc".into());
    let dep_edge = ImportEdge {
        module: dep_src,
        import_all: false,
        is_exported: true,
        is_meta: false,
    };
    adm_src_mut.graph.insert("LibSrc".into(), vec![dep_edge]);
    adm_src_mut.graph.get_mut("Captured").unwrap().push(ImportEdge {
        module: "LibSrc".into(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    });
    reject_inspected(
        &mut c_src,
        f_src.request.clone(),
        "uninventoried target library dependency LibSrc.uninv",
    );

    let f_prf = Fixture::new(PROOF);
    let mut c_prf = f_prf.accepted_checker();
    let adm_prf = c_prf.admitted().unwrap();
    let dep_prf = adm_prf.foundation_modules().into_iter().next().unwrap().to_owned();
    let lib1_olean = c_prf.stage().join("lib/LibPrf1.olean");
    let lib2_olean = c_prf.stage().join("lib/LibPrf2.olean");
    let prf_olean = c_prf.stage().join("lib/Proof.olean");
    let forge_prf = c_prf.stage().join("ForgeProofUninventoriedLib.lean");
    run_lean_script(
        &mut c_prf,
        "forge-proof-uninventoried-lib",
        &forge_prf,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let uninvThm : ConstantInfo := .thmInfo {{\n    \
                 name := `LibPrf1.uninv, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`LibPrf1.uninv] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `LibPrf1 {{\n    \
                 isModule := false, imports := #[{{ module := `{dep_prf} }}],\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[`LibPrf1.uninv], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `LibPrf2 {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `{dep_prf} }}, {{ module := `LibPrf1 }}],\n    \
                 constNames := #[`LibPrf1.uninv], constants := #[uninvThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let prfPath := System.FilePath.mk {:?}\n  \
               let (prfData, _) ← readModuleData prfPath\n  \
               saveModuleData prfPath `Proof {{ prfData with\n    \
                 constNames := prfData.constNames.push `LibPrf1.uninv,\n    \
                 constants := prfData.constants.push uninvThm }}\n",
            lib1_olean.to_string_lossy(),
            lib2_olean.to_string_lossy(),
            prf_olean.to_string_lossy(),
        ),
    );
    let lib1_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", lib1_olean.to_string_lossy().into_owned())]),
        "fixture",
        String::new,
    )
    .unwrap();
    let lib2_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", lib2_olean.to_string_lossy().into_owned())]),
        "fixture",
        String::new,
    )
    .unwrap();
    let adm_prf_mut = c_prf.admitted_mut().unwrap();
    adm_prf_mut.artifacts.insert("LibPrf1".into(), lib1_arts);
    adm_prf_mut.artifacts.insert("LibPrf2".into(), lib2_arts);
    adm_prf_mut.library_modules.insert("LibPrf1".into());
    adm_prf_mut.library_modules.insert("LibPrf2".into());
    let dep_prf_edge = ImportEdge {
        module: dep_prf,
        import_all: false,
        is_exported: true,
        is_meta: false,
    };
    adm_prf_mut.graph.insert("LibPrf1".into(), vec![dep_prf_edge.clone()]);
    adm_prf_mut.graph.insert(
        "LibPrf2".into(),
        vec![
            dep_prf_edge,
            ImportEdge {
                module: "LibPrf1".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            },
        ],
    );
    reject_inspected(
        &mut c_prf,
        f_prf.request.clone(),
        "uninventoried target library dependency LibPrf1.uninv",
    );

    let f_extra = Fixture::new(PROOF);
    let mut c_extra = f_extra.accepted_checker();
    let cap_extra_olean = c_extra.stage().join("lib/Captured.olean");
    let exp_extra_olean = c_extra.stage().join("lib/Expected.olean");
    let forge_extra = c_extra.stage().join("ForgeSourceExtraConst.lean");
    run_lean_script(
        &mut c_extra,
        "forge-source-extra-const",
        &forge_extra,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let capPath := System.FilePath.mk {:?}\n  \
               let (capData, _) ← readModuleData capPath\n  \
               saveModuleData capPath `Captured {{ capData with\n    \
                 extraConstNames := capData.extraConstNames.push `Captured.irHelper }}\n  \
               let expPath := System.FilePath.mk {:?}\n  \
               let (expData, _) ← readModuleData expPath\n  \
               let helperThm : ConstantInfo := .thmInfo {{\n    \
                 name := `Captured.irHelper, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`Captured.irHelper] }}\n  \
               saveModuleData expPath `Expected {{ expData with\n    \
                 constNames := expData.constNames.push `Captured.irHelper,\n    \
                 constants := expData.constants.push helperThm }}\n",
            cap_extra_olean.to_string_lossy(),
            exp_extra_olean.to_string_lossy(),
        ),
    );
    reject_inspected(
        &mut c_extra,
        f_extra.request.clone(),
        "uninventoried kernel compiler helper Captured.irHelper",
    );

    // Reversed extra-name collisions: when an already-declared foundation,
    // source, or library name appears in a later `.source` module's
    // `extraConstNames` (absent from `modConsts`), `const2ModIdx` preserves the
    // earlier owner, so `auditTarget` must still reject the checked-env
    // collision regardless of `actualOrig`.
    for (owner_kind, helper_sym, err_sub) in [
        ("foundation", "True.intro", "uninventoried kernel compiler helper True.intro"),
        ("source", "Captured.srcHelper", "uninventoried kernel compiler helper Captured.srcHelper"),
        ("library", "LibSrc2.libHelper", "uninventoried kernel compiler helper LibSrc2.libHelper"),
    ] {
        let f_rev = Fixture::new(PROOF);
        let mut c_rev = f_rev.accepted_checker();
        let dep_rev = c_rev.admitted().unwrap().foundation_modules().into_iter().next().unwrap().to_owned();
        let lib2_rev_olean = c_rev.stage().join("lib/LibSrc2.olean");
        let cap_rev_olean = c_rev.stage().join("lib/Captured.olean");
        let exp_rev_olean = c_rev.stage().join("lib/Expected.olean");
        let forge_rev = c_rev.stage().join(format!("ForgeRevExtra_{owner_kind}.lean"));
        run_lean_script(
            &mut c_rev,
            &format!("forge-rev-extra-{owner_kind}"),
            &forge_rev,
            &format!(
                "import Lean\n\
                 open Lean in\n\
                 def main : IO Unit := do\n  \
                   let helperName := `{helper_sym}\n  \
                   let helperThm : ConstantInfo := .thmInfo {{\n    \
                     name := helperName, levelParams := [],\n    \
                     type := .const `True [], value := .const `True.intro [],\n    \
                     all := [helperName] }}\n  \
                   let capPath := System.FilePath.mk {:?}\n  \
                   let (capData, _) ← readModuleData capPath\n  \
                   let expPath := System.FilePath.mk {:?}\n  \
                   let (expData, _) ← readModuleData expPath\n  \
                   if {:?} == \"foundation\" then\n    \
                     saveModuleData expPath `Expected {{ expData with\n      \
                       extraConstNames := expData.extraConstNames.push helperName }}\n  \
                   else if {:?} == \"source\" then\n    \
                     saveModuleData capPath `Captured {{ capData with\n      \
                       constNames := capData.constNames.push helperName,\n      \
                       constants := capData.constants.push helperThm }}\n    \
                     saveModuleData expPath `Expected {{ expData with\n      \
                       extraConstNames := expData.extraConstNames.push helperName }}\n  \
                   else\n    \
                     saveModuleData (System.FilePath.mk {:?}) `LibSrc2 {{\n      \
                       isModule := false, imports := #[{{ module := `{dep_rev} }}],\n      \
                       constNames := #[helperName], constants := #[helperThm],\n      \
                       extraConstNames := #[], entries := #[] }}\n    \
                     saveModuleData capPath `Captured {{ capData with\n      \
                       imports := capData.imports.push {{ module := `LibSrc2 }},\n      \
                       extraConstNames := capData.extraConstNames.push helperName }}\n",
                cap_rev_olean.to_string_lossy(),
                exp_rev_olean.to_string_lossy(),
                owner_kind,
                owner_kind,
                lib2_rev_olean.to_string_lossy(),
            ),
        );
        if owner_kind == "library" {
            let lib2_arts = ModuleArtifacts::from_available(
                &BTreeMap::from([("olean", lib2_rev_olean.to_string_lossy().into_owned())]),
                "fixture",
                String::new,
            )
            .unwrap();
            let adm_rev = c_rev.admitted_mut().unwrap();
            adm_rev.artifacts.insert("LibSrc2".into(), lib2_arts);
            adm_rev.library_modules.insert("LibSrc2".into());
            adm_rev.graph.insert(
                "LibSrc2".into(),
                vec![ImportEdge {
                    module: dep_rev,
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                }],
            );
            adm_rev.graph.get_mut("Captured").unwrap().push(ImportEdge {
                module: "LibSrc2".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            });
        }
        reject_inspected(&mut c_rev, f_rev.request.clone(), err_sub);
    }
}

/// Under `--allow-sorry-in-proof`, a `.source .proof` alternate body
/// referencing `sorryAx`:
/// 1. still enqueues non-`sorryAx` dependencies into `phase2Roots` (rejecting
///    unapproved axioms and tampered helpers fail-closed);
/// 2. still undergoes fresh kernel typechecking via `checkAlternateProofs`
///    (and `phase2Roots` replay when `idx == 0` across two `Proof` modules),
///    rejecting ill-typed `sorryAx`-bearing alternate proof bodies fail-closed;
/// 3. passes when the `sorryAx`-bearing alternate proof body is well-typed,
///    recording the theorem in `sorryDeclarations`.
#[test]
fn target_audit_allow_sorry_alternate_keeps_non_sorry_deps_in_phase2() {
    let mut f_sorry_alt_ax = Fixture::new(PROOF);
    f_sorry_alt_ax.request.allow_sorry_in_proof = true;
    let mut c_sorry_alt_ax = f_sorry_alt_ax.accepted_checker();
    let sorry_alt_prefix = c_sorry_alt_ax.admitted().unwrap().prefix.clone();
    let proof_sorry_ax_olean = c_sorry_alt_ax.stage().join("lib/Proof.olean");
    let sorry_ax_script = c_sorry_alt_ax.stage().join("ForgeProofSorryAltAxiom.lean");
    run_lean_script(
        &mut c_sorry_alt_ax,
        "forge-proof-sorry-alt-axiom",
        &sorry_ax_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let badAx : ConstantInfo := .axiomInfo {{\n    \
                 name := `Proof.badAxiom, levelParams := [],\n    \
                 type := .const `True [], isUnsafe := false }}\n  \
               let sorryTerm := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let wrapped := Expr.letE `_s (.const `True []) sorryTerm\n    \
                 (Expr.letE `_a (.const `True []) (.const `Proof.badAxiom []) \
                   flipTv.value false) false\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := (data.constNames.push `Proof.badAxiom).push `flip.eq_1,\n    \
                 constants := (data.constants.push badAx).push forgedFlip }}\n",
            sorry_alt_prefix.to_string_lossy(),
            proof_sorry_ax_olean.to_string_lossy(),
            proof_sorry_ax_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_sorry_alt_ax,
        f_sorry_alt_ax.request.clone(),
        "unapproved axiom Proof.badAxiom from Proof",
    );

    let mut f_sorry_alt_bad = Fixture::new(PROOF);
    f_sorry_alt_bad.request.allow_sorry_in_proof = true;
    let mut c_sorry_alt_bad = f_sorry_alt_bad.accepted_checker();
    let sorry_bad_prefix = c_sorry_alt_bad.admitted().unwrap().prefix.clone();
    let proof_sorry_bad_olean = c_sorry_alt_bad.stage().join("lib/Proof.olean");
    let sorry_bad_script = c_sorry_alt_bad.stage().join("ForgeProofSorryAltBadHelper.lean");
    run_lean_script(
        &mut c_sorry_alt_bad,
        "forge-proof-sorry-alt-bad-helper",
        &sorry_bad_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let badHelper : ConstantInfo := .thmInfo {{\n    \
                 name := `Proof.badHelper, levelParams := [],\n    \
                 type := .const `True [], value := .const `Bool.true [],\n    \
                 all := [`Proof.badHelper] }}\n  \
               let sorryTerm := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let wrapped := Expr.letE `_s (.const `True []) sorryTerm\n    \
                 (Expr.letE `_h (.const `True []) (.const `Proof.badHelper []) \
                   flipTv.value false) false\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := (data.constNames.push `Proof.badHelper).push `flip.eq_1,\n    \
                 constants := (data.constants.push badHelper).push forgedFlip }}\n",
            sorry_bad_prefix.to_string_lossy(),
            proof_sorry_bad_olean.to_string_lossy(),
            proof_sorry_bad_olean.to_string_lossy()
        ),
    );
    let replay_err = c_sorry_alt_bad
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_sorry_alt_bad.request.clone(),
        })
        .unwrap_err();
    assert_eq!(replay_err.code, 2, "{replay_err}");
    assert!(
        replay_err
            .message
            .contains("kernel replay rejected target dependency")
            && replay_err.message.contains("Proof.badHelper"),
        "expected kernel replay rejection on Proof.badHelper, got: {replay_err}"
    );

    // 3. Under `--allow-sorry-in-proof`, an ill-typed `sorryAx`-bearing
    //    `.source .proof` alternate (`idx == 1` overriding `.foundation`
    //    `flip.eq_1`) MUST still undergo fresh kernel typechecking via
    //    `checkAlternateProofs` and fail closed.
    let mut f_sorry_ill = Fixture::new(PROOF);
    f_sorry_ill.request.allow_sorry_in_proof = true;
    let mut c_sorry_ill = f_sorry_ill.accepted_checker();
    let sorry_ill_prefix = c_sorry_ill.admitted().unwrap().prefix.clone();
    let proof_sorry_ill_olean = c_sorry_ill.stage().join("lib/Proof.olean");
    let sorry_ill_script = c_sorry_ill.stage().join("ForgeProofSorryAltIllTyped.lean");
    run_lean_script(
        &mut c_sorry_ill,
        "forge-proof-sorry-alt-ill-typed",
        &sorry_ill_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let sorryTerm := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let illBody := Expr.letE `_s (.const `True []) sorryTerm \
                 (.const `Bool.true []) false\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := illBody }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := data.constNames.push `flip.eq_1,\n    \
                 constants := data.constants.push forgedFlip }}\n",
            sorry_ill_prefix.to_string_lossy(),
            proof_sorry_ill_olean.to_string_lossy(),
            proof_sorry_ill_olean.to_string_lossy()
        ),
    );
    let ill_err = c_sorry_ill
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_sorry_ill.request.clone(),
        })
        .unwrap_err();
    assert_eq!(ill_err.code, 2, "{ill_err}");
    assert!(
        ill_err
            .message
            .contains("kernel operation failed (alternate pinned theorem proof check flip.eq_1)")
            && ill_err.message.contains("declaration type mismatch"),
        "expected checkAlternateProofs rejection on ill-typed sorryAx alternate flip.eq_1, got: {ill_err}"
    );

    // 4. Across two `.source .proof` modules (`ProofHelper` `idx == 0` and
    //    `Proof` `idx == 1`), when `Proof.verify` never references
    //    `ProofHelper.unused` and both exports carry `sorryAx`-bearing
    //    alternate bodies (`ProofHelper` ill-typed), `target-audit` enqueues
    //    `idx == 0` into `phase2Roots` and both into `sourceAlternateProofs`,
    //    rejecting fail-closed.
    let mut f_two_proof = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\nimport ProofHelper\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f_two_proof.set(
        "ProofHelper",
        TargetRole::Proof,
        "prelude\nimport Expected\ntheorem ProofHelper.unused : True := sorry\n",
    );
    f_two_proof.request.allow_sorry_in_proof = true;
    let mut c_two_proof = f_two_proof.accepted_checker();
    let helper_olean = c_two_proof.stage().join("lib/ProofHelper.olean");
    let main_proof_olean = c_two_proof.stage().join("lib/Proof.olean");
    let two_proof_script = c_two_proof.stage().join("ForgeTwoProofSorryAltIllTyped.lean");
    run_lean_script(
        &mut c_two_proof,
        "forge-two-proof-sorry-alt-ill-typed",
        &two_proof_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let helperPath := System.FilePath.mk {:?}\n  \
               let (helperData, _) ← readModuleData helperPath\n  \
               let sorryTrue := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let illBody := Expr.letE `_s (.const `True []) sorryTrue \
                 (.const `Bool.true []) false\n  \
               let helperAlt : ConstantInfo := .thmInfo {{\n    \
                 name := `ProofHelper.unused, levelParams := [],\n    \
                 type := .const `True [], value := illBody,\n    \
                 all := [`ProofHelper.unused] }}\n  \
               saveModuleData helperPath `ProofHelper {{ helperData with\n    \
                 constants := helperData.constants.map fun ci =>\n      \
                   if ci.name == `ProofHelper.unused then helperAlt else ci }}\n  \
               let mainPath := System.FilePath.mk {:?}\n  \
               let (mainData, _) ← readModuleData mainPath\n  \
               let otherSorry := Expr.letE `_t (.const `True []) sorryTrue \
                 (.const `True.intro []) false\n  \
               let mainAlt : ConstantInfo := .thmInfo {{\n    \
                 name := `ProofHelper.unused, levelParams := [],\n    \
                 type := .const `True [], value := otherSorry,\n    \
                 all := [`ProofHelper.unused] }}\n  \
               saveModuleData mainPath `Proof {{ mainData with\n    \
                 constNames := mainData.constNames.push `ProofHelper.unused,\n    \
                 constants := mainData.constants.push mainAlt }}\n",
            helper_olean.to_string_lossy(),
            main_proof_olean.to_string_lossy()
        ),
    );
    let two_err = c_two_proof
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_two_proof.request.clone(),
        })
        .unwrap_err();
    assert_eq!(two_err.code, 2, "{two_err}");
    assert!(
        two_err
            .message
            .contains("kernel replay rejected target dependency")
            && two_err.message.contains("ProofHelper.unused"),
        "expected kernel replay rejection on idx == 0 ill-typed sorryAx alternate ProofHelper.unused, got: {two_err}"
    );

    // 5. Positive control: a well-typed `sorryAx`-bearing `.source .proof`
    //    alternate overriding `.foundation` `flip.eq_1` passes fresh kernel
    //    typechecking in `checkAlternateProofs` and records `flip.eq_1` in
    //    `sorryDeclarations`.
    let mut f_sorry_ok = Fixture::new(PROOF);
    f_sorry_ok.request.allow_sorry_in_proof = true;
    let mut c_sorry_ok = f_sorry_ok.accepted_checker();
    let sorry_ok_prefix = c_sorry_ok.admitted().unwrap().prefix.clone();
    let proof_sorry_ok_olean = c_sorry_ok.stage().join("lib/Proof.olean");
    let sorry_ok_script = c_sorry_ok.stage().join("ForgeProofSorryAltWellTyped.lean");
    run_lean_script(
        &mut c_sorry_ok,
        "forge-proof-sorry-alt-well-typed",
        &sorry_ok_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let sorryFlip := mkApp2 (.const `sorryAx [.zero]) \
                 flipTv.type (.const `Bool.false [])\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := sorryFlip }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := data.constNames.push `flip.eq_1,\n    \
                 constants := data.constants.push forgedFlip }}\n",
            sorry_ok_prefix.to_string_lossy(),
            proof_sorry_ok_olean.to_string_lossy(),
            proof_sorry_ok_olean.to_string_lossy()
        ),
    );
    let ok_rep = c_sorry_ok
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_sorry_ok.request.clone(),
        })
        .unwrap();
    assert_eq!(ok_rep["replay"], true);
    assert_eq!(ok_rep["exactType"], true);
    assert!(
        ok_rep["sorryDeclarations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n == "flip.eq_1"),
        "expected flip.eq_1 in sorryDeclarations: {ok_rep}"
    );

    // 6. When a Phase-1 stored constant (`flip.eq_1` used by `Spec.specs`)
    //    is sorry-free, a well-typed `sorryAx`-bearing `.source .proof`
    //    alternate in `Proof.olean` enters `altSorryDecls` and must be rejected
    //    by `TrustedBoundary.lean`'s post-Phase-1 check.
    let mut f_sorry_phase1_alt = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f_sorry_phase1_alt.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs (p : BitVec 8) : Prop :=\n  \
           (fun (_ : flip Nat.add 0 1 = Nat.add 1 0) => BitVec.and p p = p)\n    \
             (@flip.eq_1 Nat Nat Nat Nat.add 1 0)\n",
    );
    f_sorry_phase1_alt.request.allow_sorry_in_proof = true;
    let mut c_sorry_phase1_alt = f_sorry_phase1_alt.accepted_checker();
    let p1_alt_prefix = c_sorry_phase1_alt.admitted().unwrap().prefix.clone();
    let proof_p1_alt_olean = c_sorry_phase1_alt.stage().join("lib/Proof.olean");
    let p1_alt_script = c_sorry_phase1_alt.stage().join("ForgeProofSorryPhase1Alt.lean");
    run_lean_script(
        &mut c_sorry_phase1_alt,
        "forge-proof-sorry-phase1-alt",
        &p1_alt_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let sorryFlip := mkApp2 (.const `sorryAx [.zero]) \
                 flipTv.type (.const `Bool.false [])\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := sorryFlip }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := data.constNames.push `flip.eq_1,\n    \
                 constants := data.constants.push forgedFlip }}\n",
            p1_alt_prefix.to_string_lossy(),
            proof_p1_alt_olean.to_string_lossy(),
            proof_p1_alt_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_sorry_phase1_alt,
        f_sorry_phase1_alt.request.clone(),
        "unapproved axiom sorryAx from Init.Prelude",
    );
}

/// Verifies `inspectSpecVacuity` handles `BitVec`, `Option`, `Exists`, `Nat.le`
/// and `BitVec` inequalities/disjunctions while avoiding false positives on
/// uninhabited `Fin 0` and custom opaque orderings, and surfaces truncation on
/// opaque or over-long captured programs.
#[test]
fn inspect_spec_vacuity_handles_bitvec_option_exists_le_and_fin0() {
    let make_specs_fixture = |spec_expr: &str| {
        let mut f = Fixture::new(
            "prelude\nimport Expected\n\
             theorem Proof.verify : Expected.claim := ⟨rfl, .inr trivial, .inr trivial⟩\n",
        );
        f.set(
            "Model",
            TargetRole::Model,
            "prelude\nimport Init.Data.BitVec.Basic\n\
             namespace Trusted.MirAst\n\
             structure Program where\n  \
               bodies : List Nat\n  \
               pointerWidthBits : Nat\n  \
               mirProfileVersion : Nat\n  \
               entryDefId : Nat\n  \
               scope : Nat\n  \
               overflowChecks : Bool\n  \
               panicStrategy : Nat\n  \
               hasLocalPanicHandler : Bool\n\
             opaque customLe : Nat → Nat → Prop\n\
             end Trusted.MirAst\n\
             namespace Trusted.MirSemantics\n\
             structure Val where\n  raw : Nat\n\
             structure Specs where\n  \
               safety : String → List Val → Prop\n  \
               property : Trusted.MirAst.Program → Prop\n\
             structure Crate where\n  \
               program : Trusted.MirAst.Program\n  \
               specs : Specs\n\
             def UnitTheorem (c : Crate) : Prop :=\n  \
               c.program.bodies = [] ∧ (c.specs.safety \"\" [] ∨ True) ∧ \
                 (c.specs.property c.program ∨ True)\n\
             end Trusted.MirSemantics\n",
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\n\
             def Captured.program : Trusted.MirAst.Program := ⟨[], 64, 1, 0, 0, false, 0, false⟩\n",
        );
        f.set("Spec", TargetRole::Specification, spec_expr);
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Model\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n  \
               Trusted.MirSemantics.UnitTheorem\n    \
                 (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f
    };

    let rep_bv = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => (∀ _x : BitVec 64, False) ∨ (∀ _o : Option Nat, 1 ≤ 0) ∨ \
             BitVec.ofNat 64 0 = BitVec.ofNat 64 1,\n   \
            fun _p => ∃ _b : BitVec 64, True⟩\n",
    )
    .run()
    .unwrap();
    assert!(
        rep_bv["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety"),
        "expected BitVec/Option/Nat.le unsatisfiable_safety: {rep_bv}"
    );
    assert!(
        rep_bv["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "trivial_property"),
        "expected Exists BitVec trivial_property: {rep_bv}"
    );

    // 2. Uninhabited `Fin 0`, modulo-wrapping `(256 : BitVec 8) = 0`, and
    //    custom opaque `LE Nat` must NOT emit `unsatisfiable_safety`.
    let rep_non_vacuous = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => (∀ _x : Fin 0, False) ∧\n      \
              (256 : BitVec 8) = (0 : BitVec 8) ∧\n      \
              (letI : LE Nat := ⟨Trusted.MirAst.customLe⟩; (1 : Nat) ≤ (0 : Nat)),\n   \
            fun p => p.bodies = []⟩\n",
    )
    .run()
    .unwrap();
    assert_eq!(
        rep_non_vacuous["specWarnings"],
        serde_json::json!([]),
        "unexpected vacuity warning on Fin 0 / wrapping BitVec / custom LE: {rep_non_vacuous}"
    );

    // 3. Inhabited `Fin 1` in `∀ _ : Fin 1, False` triggers
    //    `unsatisfiable_safety`, while `(256 : BitVec 8) = 0` in `property`
    //    triggers `trivial_property`.
    let rep_fin1 = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => ∀ _x : Fin 1, False,\n   \
            fun _p => (256 : BitVec 8) = (0 : BitVec 8)⟩\n",
    )
    .run()
    .unwrap();
    let fin1_warnings = rep_fin1["specWarnings"].as_array().unwrap();
    assert!(
        fin1_warnings.iter().any(|w| w["code"] == "unsatisfiable_safety"),
        "expected Fin 1 unsatisfiable_safety: {rep_fin1}"
    );
    assert!(
        fin1_warnings.iter().any(|w| w["code"] == "trivial_property"),
        "expected trivial_property on (256 : BitVec 8) = 0: {rep_fin1}"
    );

    // 4. `Trusted.MirSemantics.Val` is recognized as an inhabited domain.
    let rep_val = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => ∀ _v : Trusted.MirSemantics.Val, False, fun p => p.bodies = []⟩\n",
    )
    .run()
    .unwrap();
    assert!(
        rep_val["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety"),
        "expected Trusted.MirSemantics.Val unsatisfiable_safety: {rep_val}"
    );
}

/// Verifies `inspectSpecVacuity` reduces concrete `BitVec` strict inequalities
/// into `Nat.le` and emits `vacuity_check_truncated` for opaque or >256-body
/// captured programs.
#[test]
fn inspect_spec_vacuity_checks_bitvec_lt_and_truncation() {
    let mut f_bv_lt = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_bv_lt.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Program where\n  \
           bodies : List Nat\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : Nat\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure Specs where\n  \
           safety : String → List Val → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : Specs\n\
         def UnitTheorem (c : Crate) : Prop :=\n  \
           (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_bv_lt.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program := ⟨[], 64, 1, 0, 0, false, 0, false⟩\n",
    );
    f_bv_lt.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => (1 : BitVec 8) < (0 : BitVec 8), fun p => p.bodies = []⟩\n",
    );
    f_bv_lt.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_bv_lt.set(
        "Proof",
        TargetRole::Proof,
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    let rep_bv_lt = f_bv_lt.run().unwrap();
    assert!(
        rep_bv_lt["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety"),
        "expected (1 : BitVec 8) < 0 unsatisfiable_safety: {rep_bv_lt}"
    );

    // 2. Non-reducible `Captured.program.bodies` list emits
    //    `vacuity_check_truncated` rather than dropping `Specs.safety`
    //    per-body checks silently, while an opaque outer `Captured.program`
    //    fails closed with `unexpected Program constructor`.
    let make_trunc_prog_fixture = |extra_decl: &str, prog_expr: &str| {
        let mut f = Fixture::new(
            "prelude\nimport Expected\n\
             theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
        );
        f.set(
            "Model",
            TargetRole::Model,
            &format!(
                "prelude\nimport Init.Data.BitVec.Basic\n\
                 namespace Trusted.MirAst\n\
                 structure Program where\n  \
                   bodies : List Nat\n  \
                   pointerWidthBits : Nat\n  \
                   mirProfileVersion : Nat\n  \
                   entryDefId : Nat\n  \
                   scope : Nat\n  \
                   overflowChecks : Bool\n  \
                   panicStrategy : Nat\n  \
                   hasLocalPanicHandler : Bool\n\
                 {extra_decl}\
                 end Trusted.MirAst\n\
                 namespace Trusted.MirSemantics\n\
                 structure Val where\n  raw : Nat\n\
                 structure Specs where\n  \
                   safety : String → List Val → Prop\n  \
                   property : Trusted.MirAst.Program → Prop\n\
                 structure Crate where\n  \
                   program : Trusted.MirAst.Program\n  \
                   specs : Specs\n\
                 def UnitTheorem (c : Crate) : Prop :=\n  \
                   (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
                 end Trusted.MirSemantics\n"
            ),
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            &format!("prelude\nimport Model\ndef Captured.program : Trusted.MirAst.Program := {prog_expr}\n"),
        );
        f.set(
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\n\
             def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
               ⟨fun _ _ => True, fun p => p.bodies = []⟩\n",
        );
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Model\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n  \
               Trusted.MirSemantics.UnitTheorem\n    \
                 (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f.set(
            "Proof",
            TargetRole::Proof,
            "prelude\nimport Expected\n\
             theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
        );
        f
    };
    let f_trunc = make_trunc_prog_fixture(
        "opaque opaqueBodies : List Nat := []\n",
        "⟨Trusted.MirAst.opaqueBodies, 64, 1, 0, 0, false, 0, false⟩",
    );
    let rep_trunc = f_trunc.run().unwrap();
    assert!(
        rep_trunc["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| {
                w["code"] == "vacuity_check_truncated"
                    && w["message"]
                        .as_str()
                        .unwrap_or("")
                        .contains("unreducible Captured.program.bodies list")
            }),
        "expected unreducible Captured.program.bodies vacuity_check_truncated: {rep_trunc}"
    );
    let f_opaque_prog = make_trunc_prog_fixture(
        "opaque opaqueProg : Program := ⟨[], 64, 1, 0, 0, false, 0, false⟩\n",
        "Trusted.MirAst.opaqueProg",
    );
    f_opaque_prog.reject_audit("unexpected Program constructor");

    // 3. Captured program exceeding 256 bodies emits explicit
    //    `vacuity_check_truncated` ("after 256 captured bodies").
    let mut f_257 = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_257.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Body where\n  \
           argumentCount : Nat\n  \
           locals : List Nat\n  \
           basicBlocks : List Nat\n  \
           isUnsafe : Bool\n  \
           identity : String\n\
         structure Program where\n  \
           bodies : List Body\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : String\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         def app : List Body → List Body → List Body\n  \
           | [], ys => ys\n  \
           | x :: xs, ys => x :: app xs ys\n\
         def sampleBody : Body := ⟨0, [], [], true, \"fn\"⟩\n\
         def b1 : List Body := [sampleBody]\n\
         def b2 : List Body := app b1 b1\n\
         def b4 : List Body := app b2 b2\n\
         def b8 : List Body := app b4 b4\n\
         def b16 : List Body := app b8 b8\n\
         def b32 : List Body := app b16 b16\n\
         def b64 : List Body := app b32 b32\n\
         def b128 : List Body := app b64 b64\n\
         def b257 : List Body := sampleBody :: app b128 b128\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure Specs where\n  \
           safety : String → List Val → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : Specs\n\
         def UnitTheorem (c : Crate) : Prop :=\n  \
           (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_257.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program :=\n  \
           ⟨Trusted.MirAst.b257, 64, 1, 0, \"\", false, 0, false⟩\n",
    );
    f_257.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => True, fun p => p.bodies = []⟩\n",
    );
    f_257.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_257.set(
        "Proof",
        TargetRole::Proof,
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    let rep_257 = f_257.run().unwrap();
    assert!(
        rep_257["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| {
                w["code"] == "vacuity_check_truncated"
                    && w["message"]
                        .as_str()
                        .unwrap_or("")
                        .contains("after 256 captured bodies")
            }),
        "expected after-256 vacuity_check_truncated: {rep_257}"
    );

    // 4. Unsafe bodies with empty `identity` (`""`) fall back to `body#<idx>`
    //    across both `unsatisfiable_safety` and wide-body
    //    `vacuity_check_truncated` (>32 args) so `validate_target_audit_report`
    //    never rejects an empty `"body"` string operationally.
    let mut f_empty_id = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_empty_id.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Body where\n  \
           argumentCount : Nat\n  \
           locals : List Nat\n  \
           basicBlocks : List Nat\n  \
           isUnsafe : Bool\n  \
           identity : String\n\
         structure Program where\n  \
           bodies : List Body\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : String\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure Specs where\n  \
           safety : String → List Val → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : Specs\n\
         def UnitTheorem (c : Crate) : Prop :=\n  \
           (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_empty_id.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program :=\n  \
           ⟨[⟨0, [], [], true, \"\"⟩, ⟨33, [], [], true, \"\"⟩], 64, 1, 0, \"\", false, 0, false⟩\n",
    );
    f_empty_id.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun id _ => if id == \"\" then False else True, fun p => p.bodies = []⟩\n",
    );
    f_empty_id.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    let rep_empty_id = f_empty_id.run().unwrap();
    let empty_id_warnings = rep_empty_id["specWarnings"].as_array().unwrap();
    assert!(
        empty_id_warnings
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety" && w["body"] == "body#0"),
        "expected body#0 fallback on empty-identity unsatisfiable_safety: {rep_empty_id}"
    );
    assert!(
        empty_id_warnings
            .iter()
            .any(|w| w["code"] == "vacuity_check_truncated" && w["body"] == "body#1"),
        "expected body#1 fallback on empty-identity vacuity_check_truncated: {rep_empty_id}"
    );

    // 5. `SpecsV2` (`UnitTheoremV2` / `CrateV2` / `Query`) also emits
    //    `vacuity_check_truncated` with `SpecsV2.safety` prefix when an unsafe
    //    body exceeds `maxCheckedArgs` (`32`).
    let mut f_v2_trunc = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_v2_trunc.request.canonical_root = "Trusted.MirSemantics.UnitTheoremV2".into();
    f_v2_trunc.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Body where\n  \
           argumentCount : Nat\n  \
           locals : List Nat\n  \
           basicBlocks : List Nat\n  \
           isUnsafe : Bool\n  \
           identity : String\n\
         structure Program where\n  \
           bodies : List Body\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : String\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure CallerMemory where\n  raw : Nat\n\
         structure Query where\n  \
           args : List Val\n  \
           callerMem : CallerMemory\n\
         structure SpecsV2 where\n  \
           safety : String → Query → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : SpecsV2\n\
         structure CrateV2 where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : SpecsV2\n\
         def UnitTheoremV2 (c : CrateV2) : Prop :=\n  \
           (c.specs.safety \"\" ⟨[], ⟨0⟩⟩ ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_v2_trunc.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program :=\n  \
           ⟨[⟨33, [], [], true, \"wide_v2_fn\"⟩], 64, 2, 0, \"\", false, 0, false⟩\n",
    );
    f_v2_trunc.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.SpecsV2 :=\n  \
           ⟨fun _ _ => True, fun p => p.bodies = []⟩\n",
    );
    f_v2_trunc.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheoremV2\n    \
             (Trusted.MirSemantics.CrateV2.mk Captured.program Spec.specs)\n",
    );
    let rep_v2_trunc = f_v2_trunc.run().unwrap();
    assert!(
        rep_v2_trunc["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| {
                w["code"] == "vacuity_check_truncated"
                    && w["body"] == "wide_v2_fn"
                    && w["message"]
                        .as_str()
                        .unwrap_or("")
                        .contains("SpecsV2.safety per-body lint skipped unsafe body")
            }),
        "expected SpecsV2 vacuity_check_truncated: {rep_v2_trunc}"
    );
}
