// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Kernel-checked `TrustedBoundary` and `Trusted.Framework.Bridge` audit
//! tests for structured `MirEnvelopeSpec` roots, `specificationUserDecls`
//! extraction, `specificationEnvelope` summaries, `inspectSpecVacuity` §2
//! envelope lint, and negative kernel safety/vacuity/law/stub checks.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

use anneal_audit::{
    Checker, Json, TargetAuditRequest, TargetBindings, TargetModule, TargetRole, sha256_bytes,
};
use anneal_testkit::{LeanAuditFixture, OleanCachePolicy};
use serde_json::json;

fn anneal_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn collect_lean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()))
        .map(|entry| entry.expect("dir entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_lean_files(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
            out.push(path);
        }
    }
}

fn stage_real_model_and_theory(fix: &LeanAuditFixture, include_theory: bool) -> Vec<TargetModule> {
    let repo = anneal_root();
    let trusted_dir = repo.join("trusted/lean");
    let mut modules = Vec::new();

    let mut trusted_files = Vec::new();
    collect_lean_files(&trusted_dir, &mut trusted_files);
    for path in trusted_files {
        let rel_under_trusted = path.strip_prefix(&trusted_dir).unwrap();
        let rel = Path::new("trusted/lean").join(rel_under_trusted);
        let module = rel_under_trusted
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(".");
        let bytes = fs::read(&path).unwrap();
        let staged = fix.write_rel(&rel, &bytes).unwrap();
        modules.push(TargetModule {
            module,
            source: staged,
            expected_sha256: sha256_bytes(&bytes),
            role: TargetRole::Model,
        });
    }

    if include_theory {
        let manifest: Json =
            serde_json::from_slice(&fs::read(repo.join("theory/bundle-manifest.json")).unwrap())
                .unwrap();
        for entry in manifest["modules"].as_array().unwrap() {
            let rel_str = entry["path"].as_str().unwrap();
            let rel = Path::new(rel_str);
            let rel_under_theory = rel.strip_prefix("theory").unwrap();
            let module = rel_under_theory
                .with_extension("")
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(".");
            let bytes = fs::read(repo.join(rel)).unwrap();
            let staged = fix.write_rel(rel, &bytes).unwrap();
            modules.push(TargetModule {
                module,
                source: staged,
                expected_sha256: sha256_bytes(&bytes),
                role: TargetRole::Proof,
            });
        }
    }

    modules
}

struct EnvelopeAuditCase {
    fix: LeanAuditFixture,
    modules: Vec<TargetModule>,
    canonical_root: String,
}

impl EnvelopeAuditCase {
    fn new(canonical_root: &str, scope_lean: &str, spec_lean: &str, proof_lean: &str) -> Self {
        let fix = LeanAuditFixture::with_cache_policy(
            &anneal_root(),
            "anneal-spec-env-",
            None,
            false,
            OleanCachePolicy::Shared,
        )
        .unwrap();
        let mut modules = stage_real_model_and_theory(&fix, true);

        let captured_src = format!(
            "\
prelude
import Init.NotationExtra
import Trusted.MirAst
namespace Captured
open Trusted.MirAst
def body0 : Body := {{
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{{ statements := [], terminator := .return_ }}]
  isUnsafe := false
  identity := \"demo::zero\"
}}
def program : Program := {{
  scope := {scope_lean}
  pointerWidthBits := 64
  mirProfileVersion := {}
  bodies := [body0]
}}
end Captured
",
            if canonical_root.ends_with("V2") { 2 } else { 1 }
        );
        let expected_src = format!(
            "\
prelude
import Captured
import Spec
import Trusted.Framework.Bridge
def Expected.claim : Prop :=
  {canonical_root} (Trusted.Framework.MirEnvelope.mk Captured.program Spec.specs)
"
        );

        for (rel, module, src, role) in [
            ("case/Captured.lean", "Captured", captured_src.as_str(), TargetRole::Capture),
            ("case/Spec.lean", "Spec", spec_lean, TargetRole::Specification),
            ("case/Expected.lean", "Expected", expected_src.as_str(), TargetRole::Expected),
            ("case/Proof.lean", "Proof", proof_lean, TargetRole::Proof),
        ] {
            let bytes = src.as_bytes();
            let path = fix.write_rel(Path::new(rel), bytes).unwrap();
            modules.push(TargetModule {
                module: module.to_owned(),
                source: path,
                expected_sha256: sha256_bytes(bytes),
                role,
            });
        }

        Self { fix, modules, canonical_root: canonical_root.to_owned() }
    }

    fn with_spec_module(mut self, module: &str, src: &str) -> Self {
        let rel = format!("case/{module}.lean");
        let bytes = src.as_bytes();
        let path = self.fix.write_rel(Path::new(&rel), bytes).unwrap();
        self.modules.push(TargetModule {
            module: module.to_owned(),
            source: path,
            expected_sha256: sha256_bytes(bytes),
            role: TargetRole::Specification,
        });
        self
    }

    fn request(&self) -> TargetAuditRequest {
        TargetAuditRequest {
            modules: self.modules.clone(),
            theorem_module: "Proof".to_owned(),
            theorem_name: "Proof.verify".to_owned(),
            expected_module: "Expected".to_owned(),
            expected_declaration: "Expected.claim".to_owned(),
            canonical_root: self.canonical_root.clone(),
            subject_declaration: "Captured.program".to_owned(),
            specification_declaration: "Spec.specs".to_owned(),
            allow_sorry_in_proof: false,
            bindings: TargetBindings {
                request_sha256: "a".repeat(64),
                capture_sha256: "b".repeat(64),
                model_manifest_sha256: "c".repeat(64),
                specification_manifest_sha256: "d".repeat(64),
            },
        }
    }

    fn run(&self) -> Result<Json, anneal_audit::Failure> {
        let env = self.fix.checker_env().unwrap();
        let mut checker = Checker::new_with_env(self.fix.root(), None, env).unwrap();
        checker.run_target(&self.request())
    }
}

const V1_CRATE_PROOF: &str = "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.Framework
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework Anneal.MirWp Anneal.Framework
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, (fun h => by cases h),
      ⟨⟨?_, rfl, ?_, rfl, fun h => Bool.noConfusion h,
          nonEmpty_oracle_id, ?_, fun _ h => h⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      ⟨Spec.userLawProof, True.intro⟩, ⟨True.intro, True.intro⟩⟩
  · exact ne_string_of_len_beq_false rfl
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    refine ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body0, rfl, rfl, rfl, rfl, absurd_mem_nil, ?_, ?_, ?_⟩
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            exact (spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 1)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg rfl)).1
          | cons _ _ => exact Bool.noConfusion hDom.1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            have hSpec := spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 1)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg rfl)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              injection hMap with hR hM
              subst hR hM
              exact ⟨⟨rfl, rfl⟩, rfl⟩
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
          | cons _ _ => exact Bool.noConfusion hDom.1
      · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [] }, ⟨rfl, rfl⟩,
          ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
";

const V1_UNIT_PROOF: &str = "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.Framework
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework Anneal.MirWp Anneal.Framework
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, fun _ => List.Mem.head _,
      ⟨⟨?_, rfl, ?_, rfl, fun _ => List.Mem.head _,
          nonEmpty_oracle_id, ?_, fun _ h => List.Mem.tail _ h⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      ⟨Spec.userLawProof, True.intro⟩, True.intro⟩
  · exact ne_string_of_len_beq_false rfl
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    refine ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body0, rfl, rfl, rfl, rfl, absurd_mem_nil, ?_, ?_, ?_⟩
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            exact (spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 1)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg rfl)).1
          | cons _ _ => exact Bool.noConfusion hDom.1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            have hSpec := spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 1)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg rfl)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              injection hMap with hR hM
              subst hR hM
              exact ⟨⟨rfl, rfl⟩, rfl⟩
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
          | cons _ _ => exact Bool.noConfusion hDom.1
      · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [] }, ⟨rfl, rfl⟩,
          ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
";

const V2_ENVELOPE_PROOF_BODY: &str = "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Anneal.Framework
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework Anneal.MirWp Anneal.Framework
private theorem exec_zero (callerMem : CallerMemory)
    (hValCm : validCallerMemory callerMem = true) :
    execProgV2 (entryProgForBody Captured.program 0) 1
      { args := [], callerMem := callerMem }
      (fun o => o = .returned ⟨.unit, callerMem⟩) := by
  have hInit :
      initStateV2 (entryProgForBody Captured.program 0)
        { args := [], callerMem := callerMem } =
      Except.ok {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [LocalSlot.immediate (some .unit)]
        }]
        callerMem := callerMem
        mem := entryMemoryWithCaller callerMem
      } := by
    unfold initStateV2 entryProgForBody
    dsimp only [Captured.program, Query.callerMem, Program.pointerWidthBits,
      Program.mirProfileVersion]
    rw [hValCm]
    rfl
  have hRet :
      evalStepV2 (entryProgForBody Captured.program 0) {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [LocalSlot.immediate (some .unit)]
        }]
        callerMem := callerMem
        mem := entryMemoryWithCaller callerMem
      } = StepResult.done (TerminalOut.returned ⟨.unit, callerMem⟩) := by
    have hExt := extractCallerMemory_entryMemoryWithCaller callerMem hValCm
    change StepResult.done (TerminalOut.returned ⟨.unit,
      extractCallerMemory callerMem (entryMemoryWithCaller callerMem)⟩) =
      StepResult.done (TerminalOut.returned ⟨.unit, callerMem⟩)
    rw [hExt]
  unfold execProgV2
  rw [hInit]
  change
    match evalStepV2 (entryProgForBody Captured.program 0) {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 0
        locals := [LocalSlot.immediate (some .unit)]
      }]
      callerMem := callerMem
      mem := entryMemoryWithCaller callerMem
    } with
    | StepResult.step _ => False
    | StepResult.done out => out = .returned ⟨.unit, callerMem⟩
    | StepResult.fault _ => False
  rw [hRet]
";

fn v2_crate_proof() -> String {
    format!(
        "{V2_ENVELOPE_PROOF_BODY}\
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, (fun h => by cases h),
      ⟨⟨nonEmpty_profile_v2_id, rfl, ?_, rfl,
          fun h => Bool.noConfusion h, ⟨rfl, List.Mem.head _⟩, ?_,
          fun g hg => List.Mem.tail _ (List.Mem.tail _ hg)⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      True.intro, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body0, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · intro g hg
        have hEq : g = .callerMemoryThreadIsolation \"mir_profile_v2\" := by
          cases hg with
          | head => rfl
          | tail _ hNil => cases hNil
        subst hEq
        exact List.Mem.tail _ (List.Mem.head _)
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          have hValCm : validCallerMemory callerMem = true := hDom.1
          cases args with
          | nil => exact (spec_and_behaviorV2_of_exec_eq (exec_zero callerMem hValCm)).1
          | cons _ _ => exact Bool.noConfusion hDom.2.1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          have hValCm : validCallerMemory callerMem = true := hDom.1
          cases args with
          | nil =>
            have hSpec := spec_and_behaviorV2_of_exec_eq (exec_zero callerMem hValCm)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              injection hMap with hR hM
              subst hR hM
              exact ⟨⟨rfl, hValCm, rfl, rfl, rfl⟩, rfl⟩
            · intro m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              cases hMap
            · intro m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              cases hMap
          | cons _ _ => exact Bool.noConfusion hDom.2.1
      · exact Or.inl ⟨rfl, Or.inl ⟨{{ args := [], callerMem := ⟨[]⟩ }},
          ⟨rfl, rfl, rfl, rfl⟩, ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
"
    )
}

fn v2_unit_proof() -> String {
    format!(
        "{V2_ENVELOPE_PROOF_BODY}\
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, fun _ => List.Mem.head _,
      ⟨⟨nonEmpty_profile_v2_id, rfl, ?_, rfl,
          fun _ => List.Mem.head _, ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩, ?_,
          fun g hg => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hg))⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      True.intro, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body0, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · intro g hg
        have hEq : g = .callerMemoryThreadIsolation \"mir_profile_v2\" := by
          cases hg with
          | head => rfl
          | tail _ hNil => cases hNil
        subst hEq
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          have hValCm : validCallerMemory callerMem = true := hDom.1
          cases args with
          | nil => exact (spec_and_behaviorV2_of_exec_eq (exec_zero callerMem hValCm)).1
          | cons _ _ => exact Bool.noConfusion hDom.2.1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          have hValCm : validCallerMemory callerMem = true := hDom.1
          cases args with
          | nil =>
            have hSpec := spec_and_behaviorV2_of_exec_eq (exec_zero callerMem hValCm)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              injection hMap with hR hM
              subst hR hM
              exact ⟨⟨rfl, hValCm, rfl, rfl, rfl⟩, rfl⟩
            · intro m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              cases hMap
            · intro m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              cases hMap
          | cons _ _ => exact Bool.noConfusion hDom.2.1
      · exact Or.inl ⟨rfl, Or.inl ⟨{{ args := [], callerMem := ⟨[]⟩ }},
          ⟨rfl, rfl, rfl, rfl⟩, ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
"
    )
}

#[test]
fn positive_v1_v2_envelope_roots_extract_user_decls_and_summary() {
    let spec_v1_crate = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
abbrev MyNat := Nat
inductive Flag where
  | a
  | b
structure PairBox where
  x : Nat
class HasTag (α : Type) where
  tag : α → Nat
instance : HasTag PairBox where
  tag p := p.x
def recAdd : Nat → Nat → Nat
  | 0, y => y
  | .succ x, y => .succ (recAdd x y)
private theorem privHelper : (0 : Nat) = 0 := rfl
def userLawProp : Prop := recAdd 1 2 = 3 ∧ privHelper = privHelper
theorem userLawProof : userLawProp := ⟨rfl, rfl⟩
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := [userLawProp]
  stepBounds := fun _ => [True]
}
end Spec
";

    let case_v1_crate = EnvelopeAuditCase::new(
        "Trusted.Framework.CrateMirEnvelopeTheoremV1",
        ".crate",
        spec_v1_crate,
        V1_CRATE_PROOF,
    );
    let rep = case_v1_crate.run().expect("CrateMirEnvelopeTheoremV1 audit succeeds");
    assert_eq!(rep["replay"], json!(true));
    assert_eq!(rep["exactType"], json!(true));
    assert_eq!(rep["canonicalRoot"], json!("Trusted.Framework.CrateMirEnvelopeTheoremV1"));
    let axioms: BTreeSet<&str> =
        rep["axioms"].as_array().unwrap().iter().map(|v| v.as_str().unwrap()).collect();
    assert!(axioms.is_subset(&BTreeSet::from(["propext"])), "{axioms:?}");

    let user_decls = rep["specificationUserDecls"].as_array().unwrap();
    let seen: BTreeSet<(&str, &str)> = user_decls
        .iter()
        .map(|d| (d["name"].as_str().unwrap(), d["kind"].as_str().unwrap()))
        .collect();
    for expected in [
        ("Spec.MyNat", "abbrev"),
        ("Spec.Flag", "inductive"),
        ("Spec.PairBox", "structure"),
        ("Spec.HasTag", "classInductive"),
        ("Spec.instHasTagPairBox", "instance"),
        ("Spec.recAdd", "def"),
        ("_private.Spec.0.Spec.privHelper", "theorem"),
        ("Spec.userLawProp", "def"),
        ("Spec.userLawProof", "theorem"),
        ("Spec.specs", "def"),
    ] {
        assert!(seen.contains(&expected), "missing user decl {expected:?} in {seen:?}");
    }
    for banned_suffix in [".inj", ".injEq", ".eq_1", ".eq_def", "._sizeOf_1", "._sizeOf_inst"] {
        assert!(
            !seen.iter().any(|(name, _)| name.ends_with(banned_suffix)),
            "compiler-generated decl leaked with suffix {banned_suffix}: {seen:?}"
        );
    }

    assert_eq!(
        rep["specificationEnvelope"],
        json!({
            "entries": [{
                "identity": "demo::zero",
                "is_unsafe": false,
                "terminates": true,
                "no_unwind": true,
                "no_abort": true,
                "require_inhabited": true
            }],
            "stubs": [],
            "refutations": [],
            "claim_shapes": ["forallSafety", "termination"],
            "gaps": [
                "unverifiedDownstream(rustc_mir_opt)",
                "unverifiedDownstream(llvm_codegen)",
                "unverifiedDownstream(linker)",
                "unverifiedDownstream(microarch_timing)"
            ],
            "law_heads": [{ "head": "And", "target_const": "" }],
            "has_step_bounds": true
        })
    );

    // Selected-unit V1 positive case.
    let spec_v1_unit = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def userLawProp : Prop := (1 : Nat) = 1
theorem userLawProof : userLawProp := rfl
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := .selectedUnitScope :: defaultMirDownstreamGaps
  laws := [userLawProp]
}
end Spec
";
    let case_v1_unit = EnvelopeAuditCase::new(
        "Trusted.Framework.UnitMirEnvelopeTheoremV1",
        ".unit",
        spec_v1_unit,
        V1_UNIT_PROOF,
    );
    let rep_unit = case_v1_unit.run().expect("UnitMirEnvelopeTheoremV1 audit succeeds");
    assert_eq!(rep_unit["replay"], json!(true));
    assert_eq!(rep_unit["specificationEnvelope"]["has_step_bounds"], json!(false));

    // Profile v2 Crate + Unit positive cases.
    let spec_v2_crate = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := .unbridgedSemantics \"mir_profile_v2\" ::
          .callerMemoryThreadIsolation \"mir_profile_v2\" ::
          defaultMirDownstreamGaps
  laws := []
}
end Spec
";
    let v2_crate_proof = v2_crate_proof();
    let case_v2_crate = EnvelopeAuditCase::new(
        "Trusted.Framework.CrateMirEnvelopeTheoremV2",
        ".crate",
        spec_v2_crate,
        &v2_crate_proof,
    );
    let rep_v2_crate = case_v2_crate.run().expect("CrateMirEnvelopeTheoremV2 audit succeeds");
    assert_eq!(rep_v2_crate["replay"], json!(true));

    let spec_v2_unit = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := .selectedUnitScope ::
          .unbridgedSemantics \"mir_profile_v2\" ::
          .callerMemoryThreadIsolation \"mir_profile_v2\" ::
          defaultMirDownstreamGaps
  laws := []
}
end Spec
";
    let v2_unit_proof = v2_unit_proof();
    let case_v2_unit = EnvelopeAuditCase::new(
        "Trusted.Framework.UnitMirEnvelopeTheoremV2",
        ".unit",
        spec_v2_unit,
        &v2_unit_proof,
    );
    let rep_v2_unit = case_v2_unit.run().expect("UnitMirEnvelopeTheoremV2 audit succeeds");
    assert_eq!(rep_v2_unit["replay"], json!(true));
}

#[test]
fn inspect_spec_vacuity_flags_envelope_unsatisfiable_safety_and_truncation() {
    let spec_unsat_safety = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def userLawProp : Prop := True
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::unsafe_fn\"
    sig := { isUnsafe := true, abi := .rust, params := [], ret := .unit }
    contract := {
      safetyPre := fun _ => False
      effects := { terminates := false, noUnwind := false, noAbort := false }
    }
    requireInhabited := false
  }]
  claimShapes := [.forallSafety]
  gaps := []
  laws := [userLawProp]
}
end Spec
";
    let mut unsat_case = EnvelopeAuditCase::new(
        "Trusted.Framework.CrateMirEnvelopeTheoremV1",
        ".crate",
        spec_unsat_safety,
        V1_CRATE_PROOF,
    );
    // Replace Proof with `sorry` allowed so `inspectSpecVacuity` runs even
    // though `Captured.body0` doesn't match `"demo::unsafe_fn"`.
    for m in &mut unsat_case.modules {
        if m.module == "Proof" {
            let p_src =
                "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := sorry\n";
            let p_path =
                unsat_case.fix.write_rel(Path::new("case/Proof.lean"), p_src.as_bytes()).unwrap();
            m.source = p_path;
            m.expected_sha256 = sha256_bytes(p_src.as_bytes());
        }
    }
    let mut req = unsat_case.request();
    req.allow_sorry_in_proof = true;
    let env = unsat_case.fix.checker_env().unwrap();
    let mut checker = Checker::new_with_env(unsat_case.fix.root(), None, env).unwrap();
    let rep_unsat = checker.run_target(&req).expect("allow_sorry reaches spec vacuity");
    let warnings = rep_unsat["specWarnings"].as_array().unwrap();
    assert!(
        warnings
            .iter()
            .any(|w| { w["code"] == "unsatisfiable_safety" && w["body"] == "demo::unsafe_fn" }),
        "expected unsatisfiable_safety warning: {warnings:?}"
    );

    // >256 entries triggers `vacuity_check_truncated`.
    let spec_trunc = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def mkList : Nat → List MirVerifiedEntry
  | 0 => []
  | .succ n => {
      identity := \"demo::zero\"
      sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
      contract := { effects := { terminates := true, noUnwind := true, noAbort := true } }
    } :: mkList n
def specs : MirEnvelopeSpec := {
  entries := mkList 260
  claimShapes := [.forallSafety, .termination]
  gaps := []
  laws := []
}
end Spec
";
    let mut trunc_case = EnvelopeAuditCase::new(
        "Trusted.Framework.CrateMirEnvelopeTheoremV1",
        ".crate",
        spec_trunc,
        V1_CRATE_PROOF,
    );
    for m in &mut trunc_case.modules {
        if m.module == "Proof" {
            let p_src =
                "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := sorry\n";
            let p_path =
                trunc_case.fix.write_rel(Path::new("case/Proof.lean"), p_src.as_bytes()).unwrap();
            m.source = p_path;
            m.expected_sha256 = sha256_bytes(p_src.as_bytes());
        }
    }
    let mut req_trunc = trunc_case.request();
    req_trunc.allow_sorry_in_proof = true;
    let env_t = trunc_case.fix.checker_env().unwrap();
    let mut checker_t = Checker::new_with_env(trunc_case.fix.root(), None, env_t).unwrap();
    let rep_trunc = checker_t.run_target(&req_trunc).expect("260 entries triggers lint truncation");
    let w_trunc = rep_trunc["specWarnings"].as_array().unwrap();
    assert!(
        w_trunc.iter().any(|w| w["code"] == "vacuity_check_truncated"),
        "expected vacuity_check_truncated: {w_trunc:?}"
    );
}

#[test]
fn negative_kernel_tests_reject_dup_id_vacuous_pre_false_law_and_stub_ban() {
    let cases = [
        (
            "duplicate_identity_nodupstrings",
            "Trusted.Framework.CrateMirEnvelopeTheoremV1",
            ".crate",
            "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def userLawProp : Prop := True
def specs : MirEnvelopeSpec := {
  entries := [
    { identity := \"demo::zero\", sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit },
      contract := { effects := { terminates := true, noUnwind := true, noAbort := true } } },
    { identity := \"demo::zero\", sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit },
      contract := { effects := { terminates := true, noUnwind := true, noAbort := true } } }
  ]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := [userLawProp]
}
end Spec
",
            "\
prelude
import Init.NotationExtra
import Expected
theorem Proof.verify : ¬ Expected.claim := fun h =>
  h.2.2.1.2.2.1.2.1 \"demo::zero\" (List.Mem.head _) rfl
",
        ),
        (
            "uninhabited_behavior_pre_without_waiver",
            "Trusted.Framework.CrateMirEnvelopeTheoremV1",
            ".crate",
            "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def userLawProp : Prop := True
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      behaviorPre := fun _ => False
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
    requireInhabited := true
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := [userLawProp]
}
end Spec
",
            "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
theorem Proof.verify : ¬ Expected.claim := fun h => by
  have hSatAll := h.2.2.1.2.2.2.1 _ (List.Mem.head _)
  cases hSatAll with
  | intro defId h1 =>
    cases h1 with
    | intro body h2 =>
      cases h2 with
      | intro hAt hSat =>
        cases defId with
        | zero =>
          injection hAt with hEq
          subst hEq
          cases hSat.2.2.2.2.2.2 with
          | inl hL =>
            cases hL.2 with
            | inl hWit =>
              cases hWit with
              | intro _ hQ => exact hQ.2.2
            | inr hUninh =>
              exact hUninh { args := [], callerMem := ⟨[]⟩ }
                ⟨by
                  dsimp [Trusted.MirSemantics.ValidEntryArgs,
                    Trusted.MirSemantics.checkArgsMatch, Captured.body0,
                    List.drop, List.take], rfl⟩
          | inr hR => exact Bool.noConfusion hR.1
        | succ _ =>
          dsimp [Captured.program, Trusted.Framework.MirProfileV1,
            Trusted.MirSemantics.getElem?] at hAt
          cases hAt
",
        ),
        (
            "false_model_law_v1",
            "Trusted.Framework.CrateMirEnvelopeTheoremV1",
            ".crate",
            "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := [(1 : Nat) = 2]
}
end Spec
",
            "\
prelude
import Init.NotationExtra
import Expected
theorem Proof.verify : ¬ Expected.claim := fun h => by
  cases h.2.2.2.1.1
",
        ),
        (
            "false_model_law_v2",
            "Trusted.Framework.UnitMirEnvelopeTheoremV2",
            ".unit",
            "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := .selectedUnitScope ::
          .unbridgedSemantics \"mir_profile_v2\" ::
          .callerMemoryThreadIsolation \"mir_profile_v2\" ::
          defaultMirDownstreamGaps
  laws := [False]
}
end Spec
",
            "\
prelude
import Init.NotationExtra
import Expected
theorem Proof.verify : ¬ Expected.claim := fun h =>
  h.2.2.2.1.1
",
        ),
        (
            "local_body_in_stubs",
            "Trusted.Framework.CrateMirEnvelopeTheoremV1",
            ".crate",
            "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def userLawProp : Prop := True
def specs : MirEnvelopeSpec := {
  entries := []
  stubs := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ _ _ => False
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety]
  gaps := .assumedExternalCallee \"demo::zero\" :: defaultMirDownstreamGaps
  laws := [userLawProp]
}
end Spec
",
            "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
theorem Proof.verify : ¬ Expected.claim := fun h => by
  have hStubAll := h.2.2.1.2.2.2.2.1 _ (List.Mem.head _)
  cases hStubAll with
  | intro defId h1 =>
    cases h1 with
    | intro body h2 =>
      cases h2 with
      | intro hAt hStub =>
        cases defId with
        | zero =>
          injection hAt with hEq
          subst hEq
          exact Bool.noConfusion (P := False) hStub.1
        | succ _ =>
          dsimp [Captured.program, Trusted.Framework.MirProfileV1,
            Trusted.MirSemantics.getElem?] at hAt
          cases hAt
",
        ),
    ];

    let sorry_proof = "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := sorry\n";
    for (label, root, scope, spec, refute_proof) in cases {
        assert!(!refute_proof.contains("sorry"), "{label}: refutation must be sorry-free");
        let refute = EnvelopeAuditCase::new(root, scope, spec, refute_proof);
        let refute_err =
            refute.run().expect_err(&format!("case {label} refutation must reject type"));
        assert_eq!(refute_err.code, 1, "{label}: {refute_err}");
        assert!(
            refute_err.message.contains("target theorem type differs from Expected"),
            "{label}: expected kernel refutation type mismatch, got: {refute_err}"
        );

        let sorry_case = EnvelopeAuditCase::new(root, scope, spec, sorry_proof);
        let sorry_err =
            sorry_case.run().expect_err(&format!("case {label} sorry must fail target-audit"));
        assert_eq!(sorry_err.code, 1, "{label}: {sorry_err}");
        assert_eq!(sorry_err.phase, "target-audit", "{label}: {sorry_err}");
    }
}

#[test]
fn spec_closure_surfaces_cross_module_compiler_thm_spoofs() {
    let spec_base = "\
prelude
inductive BareCross where
  | mk
  | alt
def crossBase : BareCross := .mk
";
    let spec_main = "\
prelude
import Init.NotationExtra
import SpecBase
import Trusted.Framework.Bridge
theorem BareCross.ofNat_ctorIdx : True := trivial
theorem BareCross.mk.inj : True := trivial
theorem BareCross.mk.sizeOf_spec : True := trivial
theorem BareCross._sizeOf_1_eq : True := trivial
theorem crossBase.proof_1 : True := trivial
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def userLawProp : Prop := (1 : Nat) = 1
theorem userLawProof : userLawProp := rfl
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"demo::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := [userLawProp]
  stepBounds := fun _ => [True]
}
end Spec
";
    let case = EnvelopeAuditCase::new(
        "Trusted.Framework.CrateMirEnvelopeTheoremV1",
        ".crate",
        spec_main,
        V1_CRATE_PROOF,
    )
    .with_spec_module("SpecBase", spec_base);

    let rep = case.run().expect("cross-module SpecBase + Spec audit succeeds");
    let user_decls = rep["specificationUserDecls"].as_array().unwrap();
    let seen: BTreeSet<(&str, &str, &str)> = user_decls
        .iter()
        .map(|d| {
            (
                d["module"].as_str().unwrap(),
                d["name"].as_str().unwrap(),
                d["kind"].as_str().unwrap(),
            )
        })
        .collect();
    for expected in [
        ("SpecBase", "BareCross", "inductive"),
        ("SpecBase", "crossBase", "def"),
        ("Spec", "BareCross.ofNat_ctorIdx", "theorem"),
        ("Spec", "BareCross.mk.inj", "theorem"),
        ("Spec", "BareCross.mk.sizeOf_spec", "theorem"),
        ("Spec", "BareCross._sizeOf_1_eq", "theorem"),
        ("Spec", "crossBase.proof_1", "theorem"),
    ] {
        assert!(seen.contains(&expected), "missing spoof {expected:?} in {seen:?}");
    }
}
