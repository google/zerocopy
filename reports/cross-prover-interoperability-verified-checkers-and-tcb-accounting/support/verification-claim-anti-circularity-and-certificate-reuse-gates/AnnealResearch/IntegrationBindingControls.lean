import AnnealResearch.IntegrationBinding

set_option Elab.async false

/-!
Negative controls and partition completeness for `R-ADEV-06`
(`AnnealResearch.IntegrationBindingControls`).

This module proves that omitting any of the essential semantic bindings or producer-status
checks from `AnnealResearch.IntegrationBinding` permits stale or unsound endorsement of
concrete specimens from `experiments/configured-admission` and `experiments/cleanup-binding`
(plus the labeled counterfactual single-variable perturbations), whereas entry-scoped
essential binding avoids both false acceptance (`b1-mir`, `alt_impl`, `b0`, macro drift)
and false verification blockers on unmonomorphized dead generic mentions (`unused_b1-mir`)
or incidental MIR/path renumbering (`cleanup_binding.mir`).
-/

namespace AnnealResearch.IntegrationBindingControls

open IntegrationBinding

/-- Control 1 loader: checks only physical file presence (`art.2.2.1`) and primary
source file SHA-256 (`art.2.2.2.2.2.1.1`), omitting `producerExitZero` (`art.2.1`) and
configured instance identity. -/
noncomputable def filePresenceLoader (cert : VerifiedClaimCert) (art : CaptureArtifact) : Bool :=
  art.2.2.1 &&
  decide (art.2.2.2.2.2.1.1 = cert.1.1)

/-- Control 2 loader: checks `producerExitZero`, `artifactPresent`, `sourceHash`, and the
top-level owner symbol (`entry`), while omitting `cfgFlags` and `resolvedCalleeInstance`. -/
noncomputable def sourceAndOwnerLoader (cert : VerifiedClaimCert) (art : CaptureArtifact) : Bool :=
  art.2.1 &&
  art.2.2.1 &&
  decide (art.2.2.2.2.2.1.1 = cert.1.1) &&
  decide (art.2.2.2.2.2.1.2.2.2.2.1 = cert.1.2.2.2.2.1)

/-- Control 3 loader: checks `producerExitZero`, `artifactPresent`, unexpanded `sourceHash`,
`cfgFlags`, `targetTriple`, and `ownerSymbol`, while omitting `expandedInputHash` and the
post-expansion `resolvedCalleeInstance` / `evaluatedConstChecksPassed`. -/
noncomputable def unexpandedSourceLoader (cert : VerifiedClaimCert) (art : CaptureArtifact) :
    Bool :=
  art.2.1 &&
  art.2.2.1 &&
  decide (art.2.2.2.2.2.1.1 = cert.1.1) &&
  decide (art.2.2.2.2.2.1.2.2.1 = cert.1.2.2.1) &&
  decide (art.2.2.2.2.2.1.2.2.2.1 = cert.1.2.2.2.1) &&
  decide (art.2.2.2.2.2.1.2.2.2.2.1 = cert.1.2.2.2.2.1)

/-- Control 4a over-approximating loader: requires `AdmissibleBinding` plus the absence of
any uninstantiated generic false-bound mention (`art.2.2.2.2.2.2.2.2.2 = 0`) in the MIR file. -/
noncomputable def syntacticAllMentionsLoader (cert : VerifiedClaimCert) (art : CaptureArtifact) :
    Bool :=
  AdmissibleBinding cert art &&
  decide (art.2.2.2.2.2.2.2.2.2 = 0)

/-- Control 4b under-approximating loader: checks `artifactPresent` and static
source/cfg/owner/callee identity fields while ignoring `producerExitZero` and
`evaluatedConstChecksPassed`. -/
noncomputable def constCheckIgnoringLoader (cert : VerifiedClaimCert) (art : CaptureArtifact) :
    Bool :=
  art.2.2.1 &&
  decide (art.2.2.2.2.2.1.1 = cert.1.1) &&
  decide (art.2.2.2.2.2.1.2.1 = cert.1.2.1) &&
  decide (art.2.2.2.2.2.1.2.2.1 = cert.1.2.2.1) &&
  decide (art.2.2.2.2.2.1.2.2.2.1 = cert.1.2.2.2.1) &&
  decide (art.2.2.2.2.2.1.2.2.2.2.1 = cert.1.2.2.2.2.1) &&
  decide (art.2.2.2.2.2.1.2.2.2.2.2.1 = cert.1.2.2.2.2.2.1)

/-- Theorem 1 (`file_presence_only_loader_control`):
On `captureB1Mir` (`observations/b1-mir/probe.mir`, SHA-256 `f01001b9...`, `1,846` bytes),
`rustc` exited `1` on `E0080` (`1 <= 0` in `checked::<B, 1>::{constant#0}`) after writing
the MIR file to disk. `filePresenceLoader` (under `certA0`) and `constCheckIgnoringLoader`
(under the `B1` static config certificate) falsely accept `captureB1Mir`, whereas
`AdmissibleBinding` rejects it (`false`, status `2` = `rejectedProducerFailure`) and
executing `captureB1Mir` violates `Execution.NoUB`. -/
theorem file_presence_only_loader_control :
    let certB1Unchecked : VerifiedClaimCert :=
      ((0, 0, 3, 0, 0, 3, 1, false), (1, 1, 0, 0), 0xB0)
    let bad : (Nat × Nat) → Prop := fun s => s.1 = 2 ∨ s.1 = 3
    captureB1Mir.2.2.1 = true ∧
    captureB1Mir.2.1 = false ∧
    filePresenceLoader certA0 captureB1Mir = true ∧
    constCheckIgnoringLoader certB1Unchecked captureB1Mir = true ∧
    AdmissibleBinding certA0 captureB1Mir = false ∧
    AdmissibleBinding certB1Unchecked captureB1Mir = false ∧
    classifyIntegrationChange certA0 captureB1Mir = 2 ∧
    ¬ Execution.NoUB (runSelectedCallee captureB1Mir) bad (0, 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   Execution.bad_prefix_not_noUB (Bad := fun s => s.1 = 2 ∨ s.1 = 3)
     (Execution.Reach.tail (Execution.Reach.refl (0, 0)) ⟨rfl, rfl⟩)
     (Or.inl rfl)⟩

/-- Theorem 2 (`source_and_symbol_name_only_loader_control`):
`sourceAndOwnerLoader` checks `producerExitZero`, `artifactPresent`, `sourceHash`
(`probe.rs` `3ada61...`), and `ownerSymbol` (`entry`), while omitting `cfgFlags` and
`resolvedCalleeInstance`. Under `certA0` (`claimedReturn = 0xA1`), it falsely accepts both
`captureA1Mir` (`--cfg=alt_impl`, stepping to `(1, 0xA2)`) and `captureB0Mir`
(`--cfg probe_case="b0"`, stepping to `(1, 0xB0)`). -/
theorem source_and_symbol_name_only_loader_control :
    sourceAndOwnerLoader certA0 captureA1Mir = true ∧
    sourceAndOwnerLoader certA0 captureB0Mir = true ∧
    AdmissibleBinding certA0 captureA1Mir = false ∧
    AdmissibleBinding certA0 captureB0Mir = false ∧
    classifyIntegrationChange certA0 captureA1Mir = 4 ∧
    classifyIntegrationChange certA0 captureB0Mir = 4 ∧
    runSelectedCallee captureA1Mir (0, 0) (1, 0xA2) ∧
    runSelectedCallee captureB0Mir (0, 0) (1, 0xB0) ∧
    (0xA2 : Nat) ≠ certA0.2.2 ∧
    (0xB0 : Nat) ≠ certA0.2.2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    fun hEq => Bool.noConfusion (congrArg (fun n => decide (n = 0xA2)) hEq),
    fun hEq => Bool.noConfusion (congrArg (fun n => decide (n = 0xB0)) hEq)⟩

/-- Theorem 3 (`unexpanded_macro_token_loader_control`):
On `captureMacroStaleMir`, the unexpanded source digest (`probe.rs` `3ada61...`),
`cfgFlags`, `targetTriple`, and `ownerSymbol` match `certA0`, but an external
`include!`/build-script generated constant changed `expandedInputHash` and switched the
post-expansion callee to a faulting path. `unexpandedSourceLoader` falsely accepts
`captureMacroStaleMir`, whereas `AdmissibleBinding` rejects it with status `3`
(`rejectedStaleSourceOrExpansion`) and `runSelectedCallee captureMacroStaleMir` violates
`Execution.NoUB`. -/
theorem unexpanded_macro_token_loader_control :
    let bad : (Nat × Nat) → Prop := fun s => s.1 = 2 ∨ s.1 = 3
    captureMacroStaleMir.2.2.2.2.2.1.1 = certA0.1.1 ∧
    captureMacroStaleMir.2.2.2.2.2.1.2.1 ≠ certA0.1.2.1 ∧
    unexpandedSourceLoader certA0 captureMacroStaleMir = true ∧
    AdmissibleBinding certA0 captureMacroStaleMir = false ∧
    classifyIntegrationChange certA0 captureMacroStaleMir = 3 ∧
    ¬ Execution.NoUB (runSelectedCallee captureMacroStaleMir) bad (0, 0) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl,
    Execution.bad_prefix_not_noUB (Bad := fun s => s.1 = 2 ∨ s.1 = 3)
      (Execution.Reach.tail (Execution.Reach.refl (0, 0)) ⟨rfl, rfl⟩)
      (Or.inr rfl)⟩
  intro (hEq : 2 = 0)
  exact Nat.noConfusion hEq

/-- Theorem 4 (`unused_generic_mention_not_monomorphized_control`):
In `obsUnusedB1Mir` (`observations/unused_b1-mir/probe.mir`, `5ed88e...`), the private
generic function `never_instantiated<U>() -> checked::<B, 1>()` appears in MIR
(`uninstantiatedGenericMention = 1`) while the public entry `entry` resolves to
`checked::<B, 0>()` (and `unused_b1-llvm-ir` has the exact same digest `8da133...` as
`b0-llvm-ir`). Entry-scoped `AdmissibleBinding` admits `obsUnusedB1Mir` for the `unused_b1`
entry certificate (with `Execution.NoUB` and return state `(1, 0xB0)`) and rejects
`captureB1Mir`; over-approximating via `syntacticAllMentionsLoader` creates a false
blocker on `obsUnusedB1Mir`, while under-approximating via `constCheckIgnoringLoader`
falsely admits `captureB1Mir`. -/
theorem unused_generic_mention_not_monomorphized_control :
    let certUnusedB1Entry : VerifiedClaimCert :=
      ((0, 0, 4, 0, 0, 2, 0, true), (1, 1, 0, 0), 0xB0)
    let certB1Unchecked : VerifiedClaimCert :=
      ((0, 0, 3, 0, 0, 3, 1, false), (1, 1, 0, 0), 0xB0)
    let bad : (Nat × Nat) → Prop := fun s => s.1 = 2 ∨ s.1 = 3
    obsUnusedB1Mir.2.2.2.2.2.2.2.2.2 = 1 ∧
    AdmissibleBinding certUnusedB1Entry obsUnusedB1Mir = true ∧
    classifyIntegrationChange certUnusedB1Entry obsUnusedB1Mir = 1 ∧
    Execution.NoUB (runSelectedCallee obsUnusedB1Mir) bad (0, 0) ∧
    runSelectedCallee obsUnusedB1Mir (0, 0) (1, 0xB0) ∧
    syntacticAllMentionsLoader certUnusedB1Entry obsUnusedB1Mir = false ∧
    constCheckIgnoringLoader certB1Unchecked captureB1Mir = true ∧
    AdmissibleBinding certB1Unchecked captureB1Mir = false ∧
    ¬ Execution.NoUB (runSelectedCallee captureB1Mir) bad (0, 0) := by
  have hVer :
      Execution.Verified (runSelectedCallee obsUnusedB1Mir)
        (fun s => s.1 = 2 ∨ s.1 = 3) (fun s => s.1 = 1) (0, 0) := by
    apply Execution.invariant_verified
      (Invariant := fun s => s = (0, 0) ∨ s = (1, 0xB0)) (Or.inl rfl)
    · intro s t _ hStep
      exact Or.inr hStep.2
    · intro s hInv
      rcases hInv with rfl | rfl
      · exact fun h => Or.elim h
          (fun (h2 : 0 = 2) => Nat.noConfusion h2)
          (fun (h3 : 0 = 3) => Nat.noConfusion h3)
      · exact fun h => Or.elim h
          (fun (h2 : 1 = 2) => Nat.noConfusion h2 Nat.noConfusion)
          (fun (h3 : 1 = 3) => Nat.noConfusion h3 Nat.noConfusion)
    · intro s hInv
      rcases hInv with rfl | rfl
      · exact Or.inr ⟨(1, 0xB0), ⟨rfl, rfl⟩⟩
      · exact Or.inl rfl
  exact ⟨rfl, rfl, rfl, hVer.1, ⟨rfl, rfl⟩, rfl, rfl, rfl,
    Execution.bad_prefix_not_noUB (Bad := fun s => s.1 = 2 ∨ s.1 = 3)
      (Execution.Reach.tail (Execution.Reach.refl (0, 0)) ⟨rfl, rfl⟩)
      (Or.inl rfl)⟩

/-- Theorem 5 (`essential_vs_incidental_partition_complete`):
Complete bidirectional partition theorem and matrix audit across the historical
`configured-admission` captures (`captureA0Mir`, `captureA0Llvm`, `captureB0Mir`,
`captureB1Mir`, `obsUnusedB1Mir`), the `cleanup-binding` relative/absolute path captures,
and the counterfactual single-variable perturbations (`captureA1Mir`, `captureMacroStaleMir`). -/
theorem essential_vs_incidental_partition_complete :
    (∀ cert art,
      (AdmissibleBinding cert art = true ↔
        (art.2.1 = true ∧ art.2.2.1 = true ∧
         art.2.2.2.2.2.1.2.2.2.2.2.2.2 = true ∧ art.2.2.2.2.2.1 = cert.1)) ∧
      (AdmissibleBinding cert art = true ↔
        (classifyIntegrationChange cert art = 0 ∨ classifyIntegrationChange cert art = 1))) ∧
    (∀ (cert : VerifiedClaimCert) (art : CaptureArtifact)
       (ph' bytes' dig' : Nat) (inc' : IncidentalAdapterMetadata),
      let art' : CaptureArtifact :=
        (ph', art.2.1, art.2.2.1, bytes', dig', art.2.2.2.2.2.1, inc')
      AdmissibleBinding cert art' = AdmissibleBinding cert art ∧
      runSelectedCallee art' = runSelectedCallee art) ∧
    classifyIntegrationChange certA0 captureA0Mir = 0 ∧
    classifyIntegrationChange certA0 captureA0Llvm = 0 ∧
    classifyIntegrationChange certA0 captureA1Mir = 4 ∧
    classifyIntegrationChange certA0 captureB0Mir = 4 ∧
    classifyIntegrationChange certA0 captureB1Mir = 2 ∧
    classifyIntegrationChange certA0 captureMacroStaleMir = 3 :=
  ⟨admissible_iff_reused_or_incidental_refresh,
   fun _ _ _ _ _ _ => ⟨rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms file_presence_only_loader_control
#print axioms source_and_symbol_name_only_loader_control
#print axioms unexpanded_macro_token_loader_control
#print axioms unused_generic_mention_not_monomorphized_control
#print axioms essential_vs_incidental_partition_complete

end AnnealResearch.IntegrationBindingControls
