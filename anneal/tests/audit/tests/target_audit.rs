// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact target-root, source binding and authority separation regressions.
//!
//! The tests live in domain submodules under `tests/target_audit/`, which
//! share this file's fixture, helpers, and imports through `use super::*`.
//! They stay in this one test target so that the slow-test overrides in
//! `.config/nextest.toml`, which select the `target_audit` binary, keep
//! applying to them.

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

#[path = "target_audit/axiom_metadata_and_failure_gates.rs"]
mod axiom_metadata_and_failure_gates;
#[path = "target_audit/companions_and_module_mode.rs"]
mod companions_and_module_mode;
#[path = "target_audit/forged_library_replay.rs"]
mod forged_library_replay;
#[path = "target_audit/library_inventory.rs"]
mod library_inventory;
#[path = "target_audit/module_headers.rs"]
mod module_headers;
#[path = "target_audit/role_and_origin_gates.rs"]
mod role_and_origin_gates;
#[path = "target_audit/spec_and_phase_gates.rs"]
mod spec_and_phase_gates;
#[path = "target_audit/spec_effects_and_module_index.rs"]
mod spec_effects_and_module_index;
#[path = "target_audit/spec_g4_vacuity.rs"]
mod spec_g4_vacuity;
#[path = "target_audit/spec_preflight_parse_tree.rs"]
mod spec_preflight_parse_tree;
#[path = "target_audit/spec_vacuity.rs"]
mod spec_vacuity;
#[path = "target_audit/uninventoried_and_alternate_replay.rs"]
mod uninventoried_and_alternate_replay;
