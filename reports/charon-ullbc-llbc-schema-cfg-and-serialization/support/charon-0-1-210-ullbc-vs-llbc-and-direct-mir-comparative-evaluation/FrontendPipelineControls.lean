import AnnealResearch.FrontendPipelineTrust

set_option Elab.async false

/-!
Wave A negative controls and discriminator suite for FE-01 and FE-02 from
live Issue #45 (`<!-- anneal-frontend-evaluation-program-2026-10-16 -->`).

Memory discipline for the Linux `x86_64` `-M768` envelope:
- `set_option Elab.async false`
- Imports only `AnnealResearch.FrontendPipelineTrust`
- Zero `deriving Repr` and zero `deriving DecidableEq`
- Value definitions marked `noncomputable def` to skip LCNF compilation
-/

namespace AnnealResearch.FrontendPipelineControls

open AnnealResearch.FrontendPipelineTrust

/-- Output-only observer that checks only `scalarReturn` while ignoring call target,
    memory write footprint, unwind behavior, and intermediate UB. -/
noncomputable def scalarReturnOnlyObserver (p : ProbeSpec) (expectedRet : Nat) : Bool :=
  p.scalarReturn == expectedRet

/-- Mutant 1: switches `calleeId` from `1` (`ImplA::marker`) to `2` (`ImplB::marker`)
    while preserving `scalarReturn = 7`. -/
noncomputable def wrongCalleeMutant : ProbeSpec :=
  { intendedProbe with calleeId := 2 }

/-- 1. Negative control: `scalarReturnOnlyObserver` accepts `wrongCalleeMutant`,
    whereas `FullFrontendClaim` rejects it. -/
theorem wrong_callee_same_scalar_return_control :
    scalarReturnOnlyObserver wrongCalleeMutant 7 = true ∧
    wrongCalleeMutant.scalarReturn = intendedProbe.scalarReturn ∧
    wrongCalleeMutant.calleeId = 2 ∧
    ¬ FullFrontendClaim wrongCalleeMutant 1 1 42 7 true := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h.2.1

/-- Mutant 2: writes to memory location `99` instead of `1` while preserving
    `scalarReturn = 7`. -/
noncomputable def wrongFootprintMutant : ProbeSpec :=
  { intendedProbe with writtenLoc := 99 }

/-- 2. Negative control: `scalarReturnOnlyObserver` accepts `wrongFootprintMutant`,
    whereas `FullFrontendClaim` rejects the altered memory footprint. -/
theorem wrong_written_location_same_return_control :
    scalarReturnOnlyObserver wrongFootprintMutant 7 = true ∧
    wrongFootprintMutant.scalarReturn = intendedProbe.scalarReturn ∧
    wrongFootprintMutant.writtenLoc = 99 ∧
    ¬ FullFrontendClaim wrongFootprintMutant 1 1 42 7 true := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h.2.2.1

/-- Mutant 3a: drops the unwind cleanup edge (`unwindsOnErr = false`) while
    preserving `scalarReturn = 7`. -/
noncomputable def unwindCleanupMutant : ProbeSpec :=
  { intendedProbe with unwindsOnErr := false }

/-- Mutant 3b: contains an intermediate UB/cleanup fault on its unwind path
    while retaining `scalarReturn = 7` on the normal return path. -/
noncomputable def unwindFaultMutant : ProbeSpec :=
  { intendedProbe with hasIntermediateFault := true }

/-- Transformation modeling pinned Aeneas ignoring `on_unwind` blocks during
    call/assert interpretation (`03-prototype-author-limitations.md` §3.8). -/
noncomputable def ignoreOnUnwindPass (p : ProbeSpec) : ProbeSpec :=
  { p with unwindsOnErr := false, hasIntermediateFault := false }

/-- 3. Negative control: `ignoreOnUnwindPass` preserves `scalarReturn = 7` and makes
    the lowered model appear UB-free (`Execution.NoUB`), while the actual subject
    `unwindFaultMutant` reaches `faultState` (`¬ Execution.NoUB`). -/
theorem erased_unwind_edge_hides_exceptional_effect_control :
    scalarReturnOnlyObserver unwindCleanupMutant 7 = true ∧
    (ignoreOnUnwindPass unwindFaultMutant).scalarReturn = intendedProbe.scalarReturn ∧
    Execution.NoUB
      (probeSys (ignoreOnUnwindPass unwindFaultMutant)).1
      (probeSys (ignoreOnUnwindPass unwindFaultMutant)).2
      initProbeState ∧
    ¬ Execution.NoUB
      (probeSys unwindFaultMutant).1
      (probeSys unwindFaultMutant).2
      initProbeState ∧
    ¬ FullFrontendClaim unwindCleanupMutant 1 1 42 7 true := by
  refine ⟨rfl, rfl,
    noUB_of_no_intermediate_fault (ignoreOnUnwindPass unwindFaultMutant) rfl,
    Execution.bad_prefix_not_noUB
      (Execution.Reach.tail (Execution.Reach.refl initProbeState) (Or.inl ⟨rfl, rfl, rfl⟩))
      rfl,
    ?_⟩
  intro h
  cases h.2.2.2.2.1

/-- Object representation `(logicalFieldVal, paddingInitialized)` for the
    `Aeneas #1405` typed-copy padding discriminator. -/
abbrev PaddingObject : Type := Nat × Bool

noncomputable def initializedPaddedObj : PaddingObject := (42, true)

/-- Functional value-only copy (`Aeneas #1405`) preserves the logical field value
    while forgetting padding-byte initialization. -/
noncomputable def logicalValueCopyOnly (obj : PaddingObject) : PaddingObject :=
  (obj.1, false)

def logicalOnlyStep (_ : PaddingObject) (s t : ProbeState) : Prop :=
  s = initProbeState ∧ t = normalExitState

def intoBytesPhysicalStep (obj : PaddingObject) (s t : ProbeState) : Prop :=
  (s = initProbeState ∧ obj.2 = false ∧ t = faultState) ∨
  (s = initProbeState ∧ obj.2 = true ∧ t = normalExitState)

/-- 4. Negative control (`Aeneas #1405`): `logicalValueCopyOnly` preserves the
    logical field value (`42`) and passes `Execution.NoUB` under `logicalOnlyStep`,
    but loses padding initialization (`false`) so an unsafe `into_bytes` physical
    read reaches `faultState` (`¬ Execution.NoUB`). -/
theorem typed_copy_padding_loss_control :
    (logicalValueCopyOnly initializedPaddedObj).1 = initializedPaddedObj.1 ∧
    (logicalValueCopyOnly initializedPaddedObj).2 = false ∧
    Execution.NoUB
      (logicalOnlyStep (logicalValueCopyOnly initializedPaddedObj))
      probeBad
      initProbeState ∧
    ¬ Execution.NoUB
      (intoBytesPhysicalStep (logicalValueCopyOnly initializedPaddedObj))
      probeBad
      initProbeState := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · apply Execution.invariant_noUB (Invariant := fun s => s ≠ faultState)
    · intro h; cases h
    · intro s t _ hstep
      rcases hstep with ⟨_, ht⟩
      subst ht
      intro h; cases h
    · intro s hinv hbad
      exact hinv hbad
  · exact Execution.bad_prefix_not_noUB
      (Execution.Reach.tail (Execution.Reach.refl initProbeState) (Or.inl ⟨rfl, rfl, rfl⟩))
      rfl

noncomputable def directTrustedDirAudit (directDeclsHaveAxiomOrSorry : Bool) : Bool :=
  !directDeclsHaveAxiomOrSorry

noncomputable def transitiveClosureAudit
    (directDeclsHaveAxiomOrSorry transitiveImportWeakensClaim : Bool) : Bool :=
  (!directDeclsHaveAxiomOrSorry) && (!transitiveImportWeakensClaim)

/-- Helper predicate outside `trusted/` that weakens the safety obligation to `True`
    without declaring any Lean `axiom` or `sorry`. -/
def WeakenedImportedClaim (_ : ProbeSpec) : Prop :=
  True

/-- 5. Negative control: a non-transitive `trusted/` check passes when `trusted/`
    contains no direct `axiom`/`sorry`, yet an untracked imported definition outside
    `trusted/` (`WeakenedImportedClaim`) trivially admits `unwindFaultMutant`. -/
theorem untracked_trusted_import_dependency_control :
    directTrustedDirAudit false = true ∧
    transitiveClosureAudit false true = false ∧
    WeakenedImportedClaim unwindFaultMutant ∧
    ¬ Execution.NoUB
      (probeSys unwindFaultMutant).1
      (probeSys unwindFaultMutant).2
      initProbeState :=
  ⟨rfl, rfl, True.intro,
    Execution.bad_prefix_not_noUB
      (Execution.Reach.tail (Execution.Reach.refl initProbeState) (Or.inl ⟨rfl, rfl, rfl⟩))
      rfl⟩

/-- 6. Complete FE-01/FE-02 discriminator summary combining positive route preservation
    with all five negative controls. -/
theorem fe01_fe02_complete_discriminator_summary :
    FullFrontendClaim (mirPostCleanupTrace intendedProbe) 1 1 42 7 true ∧
    FullFrontendClaim (ullbcRetainedTrace intendedProbe) 1 1 42 7 true ∧
    ¬ FullFrontendClaim wrongCalleeMutant 1 1 42 7 true ∧
    ¬ FullFrontendClaim wrongFootprintMutant 1 1 42 7 true ∧
    ¬ Execution.NoUB (probeSys unwindFaultMutant).1 (probeSys unwindFaultMutant).2 initProbeState ∧
    ¬ Execution.NoUB
      (intoBytesPhysicalStep (logicalValueCopyOnly initializedPaddedObj))
      probeBad
      initProbeState ∧
    transitiveClosureAudit false true = false :=
  ⟨positive_probe_preserved_across_faithful_routes.1,
    positive_probe_preserved_across_faithful_routes.2.1,
    wrong_callee_same_scalar_return_control.2.2.2,
    wrong_written_location_same_return_control.2.2.2,
    erased_unwind_edge_hides_exceptional_effect_control.2.2.2.1,
    typed_copy_padding_loss_control.2.2.2,
    rfl⟩

#print axioms AnnealResearch.FrontendPipelineControls.wrong_callee_same_scalar_return_control
#print axioms AnnealResearch.FrontendPipelineControls.wrong_written_location_same_return_control
#print axioms AnnealResearch.FrontendPipelineControls.erased_unwind_edge_hides_exceptional_effect_control
#print axioms AnnealResearch.FrontendPipelineControls.typed_copy_padding_loss_control
#print axioms AnnealResearch.FrontendPipelineControls.untracked_trusted_import_dependency_control
#print axioms AnnealResearch.FrontendPipelineControls.fe01_fe02_complete_discriminator_summary

end AnnealResearch.FrontendPipelineControls
