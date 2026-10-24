import AnnealResearch.FrontendIncrementalFrontiers

set_option Elab.async false

namespace AnnealResearch.FrontendIncrementalControls

open AnnealResearch.Execution
open AnnealResearch.FrontendIncrementalFrontiers

/-- Torn subject produced by an interrupted update combining old `bodyHash = 10`
with newly mutated `selectedInstanceHash = 11` at generation `2`. -/
noncomputable def tornSubj : SubjectFingerprint := (10, 11, 20, 20, 30, 30, 2)

/-- Interrupted capture transaction (`atomicCommitComplete = false`, `readerObservedGen = 1`). -/
noncomputable def tornTx : CaptureTransaction :=
  ((10, 10, 20, 20, 30, 30, 1), true, false, false, 1, true)

/-- Naive lockless/generation-blind reader that checks only `bodyHash` and `proofChecked`. -/
noncomputable def naiveTornReaderAccepts
    (subj : SubjectFingerprint) (tx : CaptureTransaction) : Bool :=
  (subj.1 == tx.1.1) && tx.2.2.2.2.2

/-- Faulting subject inspected during an incomplete interactive tactic session. -/
noncomputable def unprovedFaultSubj : SubjectFingerprint := (40, 41, 20, 20, 30, 30, 5)

/-- Provisional tactic-state transaction (`captureComplete = false`, `proofChecked = false`)
carrying the current document's `generationId = 5`. -/
noncomputable def tacticQueryTx : CaptureTransaction :=
  (unprovedFaultSubj, false, false, true, 5, false)

/-- Flawed editor rule that relabels any non-canceled response at the current
document generation as a verified endorsement. -/
noncomputable def naiveRevisionRelabelAccepts
    (subj : SubjectFingerprint) (tx : CaptureTransaction) : Bool :=
  (tx.2.2.2.2.1 == subj.2.2.2.2.2.2) && (!tx.2.2.1)

/-- Projection of three extension-frontier observables (storage padding/provenance,
atomic ordering, and inline-asm clobbers) under a route's `FrontierPreservationProfile`. -/
noncomputable def eraseFrontierObservables
    (p : FrontierPreservationProfile)
    (paddingInitOk atomicAcqRelOk asmClobberOk : Bool) : Bool × Bool × Bool :=
  (if p.1 then paddingInitOk else true,
   if p.2.2.1 then atomicAcqRelOk else true,
   if p.2.2.2.1 then asmClobberOk else true)

/-- Step relation for a mutant violating storage padding, atomic ordering,
and inline-asm clobber obligations while returning the same scalar payload. -/
def frontierMutantStep (s s' : IncState) : Prop :=
  s = initIncState ∧ s' = (1, false, false)

/-- Async coroutine transition step where completed `Poll::Ready` execution
reaches `(3, true, true)` safely, but ordinary cancellation at `SuspendedAtAwait1`
(`(1, false, true)`) faults in destructor cleanup (`(2, false, false)`). -/
def asyncCancelledFaultStep (s s' : IncState) : Prop :=
  (s = initIncState ∧ s' = (1, false, true)) ∨
  (s = (1, false, true) ∧ s' = (2, false, false)) ∨
  (s = (1, false, true) ∧ s' = (3, true, true))

/-- Version-pinned semantic authority renewal check (`FE-14`). -/
noncomputable def versionPinnedRenewalAccepts
    (certVer currentVer : Nat) (proofChecked : Bool) : Bool :=
  (certVer == currentVer) && proofChecked

/-- Step relation under strengthened operational semantics (`semanticModelVer = 2`)
for a specimen that only satisfied `semanticModelVer = 1`. -/
def semanticV2StrengthenedStep (s s' : IncState) : Prop :=
  s = initIncState ∧ s' = (1, false, false)

/-- Negative Control 1 (`FE-13`): A concurrent reader that ignores atomic commit
and generation barriers accepts a torn `(bodyHash, selectedInstanceHash)` pair
that violates `Execution.NoUB`, whereas `CurrentEndorsementValid` rejects it. -/
theorem torn_write_concurrent_reader_race_control :
    naiveTornReaderAccepts tornSubj tornTx = true ∧
      CurrentEndorsementValid tornSubj tornTx = false ∧
      classifyTransaction tornSubj tornTx = 3 ∧
      SubjectWellFormed tornSubj = false ∧
      ¬ NoUB (incrementalSubjStep tornSubj) IncBadState initIncState := by
  have hStep : incrementalSubjStep tornSubj initIncState (1, false, false) :=
    ⟨rfl, rfl⟩
  have hReach : Reach (incrementalSubjStep tornSubj) initIncState (1, false, false) :=
    Reach.tail (Reach.refl initIncState) hStep
  have hBad : IncBadState (1, false, false) := rfl
  have hNotNoUB : ¬ NoUB (incrementalSubjStep tornSubj) IncBadState initIncState :=
    bad_prefix_not_noUB (Bad := IncBadState) hReach hBad
  exact ⟨rfl, rfl, rfl, rfl, hNotNoUB⟩

#print axioms torn_write_concurrent_reader_race_control

/-- Negative Control 2 (`FE-13`): Relabeling a provisional tactic-state response
with the current document generation as a verified endorsement admits an unproved
faulting subject (`¬ Execution.NoUB`), whereas `classifyTransaction` isolates it
as `provisionalTacticOrPartial` (`1`). -/
theorem provisional_tactic_state_relabeled_as_endorsement_control :
    naiveRevisionRelabelAccepts unprovedFaultSubj tacticQueryTx = true ∧
      CurrentEndorsementValid unprovedFaultSubj tacticQueryTx = false ∧
      classifyTransaction unprovedFaultSubj tacticQueryTx = 1 ∧
      ¬ NoUB (incrementalSubjStep unprovedFaultSubj) IncBadState initIncState := by
  have hStep : incrementalSubjStep unprovedFaultSubj initIncState (1, false, false) :=
    ⟨rfl, rfl⟩
  have hReach :
      Reach (incrementalSubjStep unprovedFaultSubj) initIncState (1, false, false) :=
    Reach.tail (Reach.refl initIncState) hStep
  have hBad : IncBadState (1, false, false) := rfl
  have hNotNoUB : ¬ NoUB (incrementalSubjStep unprovedFaultSubj) IncBadState initIncState :=
    bad_prefix_not_noUB (Bad := IncBadState) hReach hBad
  exact ⟨rfl, rfl, rfl, hNotNoUB⟩

#print axioms provisional_tactic_state_relabeled_as_endorsement_control

/-- Negative Control 3 (`FE-14`): A frontend route that erases storage padding,
atomic orderings, and inline-asm clobbers (`valuePureLoweringProfile`) collapses
a safe specimen and a frontier UB mutant to identical projections, whereas
`directMirProfile` distinguishes them and the mutant violates `Execution.NoUB`. -/
theorem irretrievable_frontier_erasure_blocks_extension_control :
    eraseFrontierObservables valuePureLoweringProfile true true true =
      eraseFrontierObservables valuePureLoweringProfile false false false ∧
    eraseFrontierObservables directMirProfile true true true ≠
      eraseFrontierObservables directMirProfile false false false ∧
    ¬ NoUB frontierMutantStep IncBadState initIncState := by
  have hNe :
      eraseFrontierObservables directMirProfile true true true ≠
        eraseFrontierObservables directMirProfile false false false := by
    intro hEq
    cases hEq
  have hStep : frontierMutantStep initIncState (1, false, false) := ⟨rfl, rfl⟩
  have hReach : Reach frontierMutantStep initIncState (1, false, false) :=
    Reach.tail (Reach.refl initIncState) hStep
  have hBad : IncBadState (1, false, false) := rfl
  have hNotNoUB : ¬ NoUB frontierMutantStep IncBadState initIncState :=
    bad_prefix_not_noUB (Bad := IncBadState) hReach hBad
  exact ⟨rfl, hNe, hNotNoUB⟩

#print axioms irretrievable_frontier_erasure_blocks_extension_control

/-- Negative Control 4 (`FE-14`): An async frontend model that checks only the
completed `Poll::Ready` branch (`(3, true, true)`) while omitting the drop path
of a suspended coroutine at `SuspendedAtAwait1` misses a cancellation UB fault. -/
theorem cancelled_async_future_missing_suspended_drop_control :
    Reach asyncCancelledFaultStep initIncState (3, true, true) ∧
      ¬ IncBadState (3, true, true) ∧
      ¬ NoUB asyncCancelledFaultStep IncBadState initIncState := by
  have hStep1 : asyncCancelledFaultStep initIncState (1, false, true) :=
    Or.inl ⟨rfl, rfl⟩
  have hStepReady : asyncCancelledFaultStep (1, false, true) (3, true, true) :=
    Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hReachReady : Reach asyncCancelledFaultStep initIncState (3, true, true) :=
    Reach.tail (Reach.tail (Reach.refl initIncState) hStep1) hStepReady
  have hReadyOk : ¬ IncBadState (3, true, true) := by
    intro hBad
    cases hBad
  have hStepCancel : asyncCancelledFaultStep (1, false, true) (2, false, false) :=
    Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hReachCancel :
      Reach asyncCancelledFaultStep initIncState (2, false, false) :=
    Reach.tail (Reach.tail (Reach.refl initIncState) hStep1) hStepCancel
  have hBadCancel : IncBadState (2, false, false) := rfl
  have hNotNoUB : ¬ NoUB asyncCancelledFaultStep IncBadState initIncState :=
    bad_prefix_not_noUB (Bad := IncBadState) hReachCancel hBadCancel
  exact ⟨hReachReady, hReadyOk, hNotNoUB⟩

#print axioms cancelled_async_future_missing_suspended_drop_control

/-- Negative Control 5 (`FE-14`): Renewing a `semanticModelVer = 1` proof under
`semanticModelVer = 2` without checking `versionPinnedRenewalAccepts` falsely
certifies a specimen that violates `Execution.NoUB` under v2 semantics. -/
theorem silent_semantic_authority_migration_control :
    versionPinnedRenewalAccepts 1 1 true = true ∧
      versionPinnedRenewalAccepts 1 2 true = false ∧
      ¬ NoUB semanticV2StrengthenedStep IncBadState initIncState := by
  have hStep : semanticV2StrengthenedStep initIncState (1, false, false) :=
    ⟨rfl, rfl⟩
  have hReach : Reach semanticV2StrengthenedStep initIncState (1, false, false) :=
    Reach.tail (Reach.refl initIncState) hStep
  have hBad : IncBadState (1, false, false) := rfl
  have hNotNoUB : ¬ NoUB semanticV2StrengthenedStep IncBadState initIncState :=
    bad_prefix_not_noUB (Bad := IncBadState) hReach hBad
  exact ⟨rfl, rfl, hNotNoUB⟩

#print axioms silent_semantic_authority_migration_control

end AnnealResearch.FrontendIncrementalControls
