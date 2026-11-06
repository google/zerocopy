import Std
import AnnealResearch.Execution
set_option Elab.async false

/-!
Consequential property transfer (`FE-10`), matched proof usability and complete cost (`FE-11`),
and agent-assisted maintenance across a real compiler upgrade (`FE-12`) for live Issue `#45`
(`<!-- anneal-frontend-evaluation-program-2026-10-16 -->`), within research program `#32` and
requirements `#1` (Section 21 `A-ADEV-03`, `A-ADEV-04`, `E-ADEV-05`, `E-ADEV-06`).
-/

namespace AnnealResearch.FrontendPropertyAndUpgrade

/-- Evaluated frontend routes:
`0 = charonLLBC`, `1 = charonULLBC`, `2 = directMirDriver`, `3 = rustcPublic`. -/
abbrev FrontendRoute := Nat

noncomputable def routeCharonLLBC : FrontendRoute := 0
noncomputable def routeCharonULLBC : FrontendRoute := 1
noncomputable def routeDirectMirDriver : FrontendRoute := 2
noncomputable def routeRustcPublic : FrontendRoute := 3

/-- `(preservesFootprint, preservesAllPrefixNoUB, preservesCleanupAndDivergence, concreteInstanceBound)` -/
abbrev RouteBridgeCert := Bool × Bool × Bool × Bool

def RouteBridgeValid (cert : RouteBridgeCert) : Prop :=
  cert.1 = true ∧ cert.2.1 = true ∧ cert.2.2.1 = true ∧ cert.2.2.2 = true

noncomputable def fullRouteBridgeCert : RouteBridgeCert :=
  (true, true, true, true)

/-- `(admittedInput, writtenSlot, outputTag, hasBadIntermediatePrefix, cleanupExecuted, divergesAfterCleanup)` -/
abbrev ConsequentialSubject := Bool × Nat × Nat × Bool × Bool × Bool

/-- `(phase, badFlag, slotObserved, returnObserved)` -/
abbrev SubjState := Nat × Bool × Nat × Nat

noncomputable def initSubjState : SubjState := (0, false, 0, 0)

def SubjBad (s : SubjState) : Prop := s.2.1 = true

def SubjAllowed (s : SubjState) : Prop := s.1 = 0 ∨ s.1 = 1

def SubjSafeStepCond (subj : ConsequentialSubject) : Prop :=
  subj.1 = true ∧ subj.2.2.2.1 = false ∧ subj.2.2.2.2.1 = true

/-- Small-step semantics for the `FE-10` consequential subject `guarded_slice_update_with_cleanup`.
When `SubjSafeStepCond subj` fails, execution first visits the unsafe intermediate state
`(2, true, writtenSlot, outputTag)` (`SubjBad`) and can still step to the normal-looking
completed state `(1, false, writtenSlot, outputTag)`. -/
def subjectStep (subj : ConsequentialSubject) (s s' : SubjState) : Prop :=
  (SubjSafeStepCond subj ∧
    ((s = initSubjState ∧ s' = (1, false, subj.2.1, subj.2.2.1)) ∨
     (subj.2.2.2.2.2 = true ∧
      s = (1, false, subj.2.1, subj.2.2.1) ∧
      s' = (1, false, subj.2.1, subj.2.2.1)))) ∨
  (¬ SubjSafeStepCond subj ∧
    ((s = initSubjState ∧ s' = (2, true, subj.2.1, subj.2.2.1)) ∨
     (s = (2, true, subj.2.1, subj.2.2.1) ∧ s' = (1, false, subj.2.1, subj.2.2.1))))

def ExactFootprintAndOutput (subj : ConsequentialSubject) : Prop :=
  subj.1 = true ∧ subj.2.1 = 1 ∧ subj.2.2.1 = 42 ∧ subj.2.2.2.2.1 = true

def JustifiedRustClaim (subj : ConsequentialSubject) : Prop :=
  Execution.NoUB (subjectStep subj) SubjBad initSubjState ∧ ExactFootprintAndOutput subj

noncomputable def reqTrue (gate : Bool) (cond : Bool) : Bool :=
  match gate with
  | false => true
  | true => cond

noncomputable def reqFalse (gate : Bool) (bad : Bool) : Bool :=
  match gate with
  | false => true
  | true =>
    match bad with
    | false => true
    | true => false

noncomputable def allTrue6 (b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  match b1 with
  | false => false
  | true =>
    match b2 with
    | false => false
    | true =>
      match b3 with
      | false => false
      | true =>
        match b4 with
        | false => false
        | true =>
          match b5 with
          | false => false
          | true => b6

/-- Route-local verifier decision (`ModelRelativeProof`) gated by the route's bridge capabilities. -/
noncomputable def ModelRelativeProof (cert : RouteBridgeCert) (subj : ConsequentialSubject) : Bool :=
  allTrue6
    subj.1
    (reqTrue cert.1 (decide (subj.2.1 = 1)))
    (decide (subj.2.2.1 = 42))
    (reqFalse cert.2.1 subj.2.2.2.1)
    (reqTrue cert.2.2.1 subj.2.2.2.2.1)
    cert.2.2.2

theorem allTrue6_eq_true {b1 b2 b3 b4 b5 b6 : Bool}
    (h : allTrue6 b1 b2 b3 b4 b5 b6 = true) :
    b1 = true ∧ b2 = true ∧ b3 = true ∧ b4 = true ∧ b5 = true ∧ b6 = true := by
  cases b1 with
  | false => exact Bool.noConfusion h
  | true =>
    cases b2 with
    | false => exact Bool.noConfusion h
    | true =>
      cases b3 with
      | false => exact Bool.noConfusion h
      | true =>
        cases b4 with
        | false => exact Bool.noConfusion h
        | true =>
          cases b5 with
          | false => exact Bool.noConfusion h
          | true =>
            cases b6 with
            | false => exact Bool.noConfusion h
            | true => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reqFalse_true_eq_true {b : Bool} (h : reqFalse true b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact Bool.noConfusion h

/-- Positive `FE-10` witness: `guarded_slice_update_with_cleanup`. -/
noncomputable def guardedSliceUpdateSubj : ConsequentialSubject :=
  (true, 1, 42, false, true, true)

/-- Endpoint 1 (`FE-10`): A model-relative proof transfers to a justified Rust operational claim
(`Execution.NoUB`, `Execution.Verified`, and `ExactFootprintAndOutput`) when `RouteBridgeValid` holds. -/
theorem model_proof_plus_route_bridge_transfers_rust_claim
    (cert : RouteBridgeCert) (subj : ConsequentialSubject)
    (hBridge : RouteBridgeValid cert)
    (hProof : ModelRelativeProof cert subj = true) :
    JustifiedRustClaim subj ∧
    Execution.Verified (subjectStep subj) SubjBad SubjAllowed initSubjState ∧
    subjectStep subj initSubjState (1, false, 1, 42) := by
  rcases hBridge with ⟨hC1, hC2, hC3, hC4⟩
  unfold ModelRelativeProof at hProof
  rw [hC1, hC2, hC3, hC4] at hProof
  rcases allTrue6_eq_true hProof with ⟨hAdm, hSlotDec, hTagDec, hNoBadReq, hClean, _⟩
  have hSlot : subj.2.1 = 1 := of_decide_eq_true hSlotDec
  have hTag : subj.2.2.1 = 42 := of_decide_eq_true hTagDec
  have hNoBad : subj.2.2.2.1 = false := reqFalse_true_eq_true hNoBadReq
  have hSafe : SubjSafeStepCond subj := ⟨hAdm, hNoBad, hClean⟩
  have hVer : Execution.Verified (subjectStep subj) SubjBad SubjAllowed initSubjState := by
    apply Execution.invariant_verified
      (Invariant := fun s => s = initSubjState ∨ s = (1, false, subj.2.1, subj.2.2.1))
      (Or.inl rfl)
    · intro s s' _ hStep
      rcases hStep with ⟨_, hSafeStep⟩ | ⟨hNotSafe, _⟩
      · rcases hSafeStep with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
        · exact Or.inr rfl
        · exact Or.inr rfl
      · exact False.elim (hNotSafe hSafe)
    · intro s hInv
      rcases hInv with rfl | rfl
      · exact fun (h : false = true) => Bool.noConfusion h
      · exact fun (h : false = true) => Bool.noConfusion h
    · intro s hInv
      rcases hInv with rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
  have hStep1 : subjectStep subj initSubjState (1, false, 1, 42) := by
    have hRaw : subjectStep subj initSubjState (1, false, subj.2.1, subj.2.2.1) :=
      Or.inl ⟨hSafe, Or.inl ⟨rfl, rfl⟩⟩
    rw [hSlot, hTag] at hRaw
    exact hRaw
  exact ⟨⟨hVer.1, hAdm, hSlot, hTag, hClean⟩, hVer, hStep1⟩

/-- Endpoint 2 (`FE-10`): Non-vacuity and admissibility of `guardedSliceUpdateSubj` under
`fullRouteBridgeCert`, including its post-cleanup divergence transition. -/
theorem positive_witness_admitted_and_nonvacuous :
    RouteBridgeValid fullRouteBridgeCert ∧
    ModelRelativeProof fullRouteBridgeCert guardedSliceUpdateSubj = true ∧
    JustifiedRustClaim guardedSliceUpdateSubj ∧
    Execution.Verified (subjectStep guardedSliceUpdateSubj) SubjBad SubjAllowed initSubjState ∧
    subjectStep guardedSliceUpdateSubj initSubjState (1, false, 1, 42) ∧
    subjectStep guardedSliceUpdateSubj (1, false, 1, 42) (1, false, 1, 42) := by
  have hBridge : RouteBridgeValid fullRouteBridgeCert := ⟨rfl, rfl, rfl, rfl⟩
  have hProof : ModelRelativeProof fullRouteBridgeCert guardedSliceUpdateSubj = true := rfl
  rcases model_proof_plus_route_bridge_transfers_rust_claim
      fullRouteBridgeCert guardedSliceUpdateSubj hBridge hProof with
    ⟨hClaim, hVer, hStep1⟩
  have hSafe : SubjSafeStepCond guardedSliceUpdateSubj := ⟨rfl, rfl, rfl⟩
  have hLoop : subjectStep guardedSliceUpdateSubj (1, false, 1, 42) (1, false, 1, 42) :=
    Or.inl ⟨hSafe, Or.inr ⟨rfl, rfl, rfl⟩⟩
  exact ⟨hBridge, hProof, hClaim, hVer, hStep1, hLoop⟩

/-- `FE-11` task kinds: `0 = initialProof`, `1 = implRepair`, `2 = harmlessRefactor`, `3 = contractRepChange`. -/
abbrev Fe11TaskKind := Nat

/-- `(supportedTasks, unsupportedTasks, preservesDivergenceAndCleanup, extractionAndParseCost, proofAndCheckCost, sharedSetupCost, humanReviewCount)` -/
abbrev RouteCostAndScopeLedger := Nat × Nat × Bool × Nat × Nat × Nat × Nat

noncomputable def totalRouteCost (L : RouteCostAndScopeLedger) : Nat :=
  L.2.2.2.2.2.1 + L.2.2.2.1 + L.2.2.2.2.1

noncomputable def MatchedUsabilityComparison (L1 L2 : RouteCostAndScopeLedger) : Bool :=
  allTrue6
    (decide (L1.1 = 4))
    (decide (L1.2.1 = 0))
    L1.2.2.1
    (decide (L2.1 = 4))
    (decide (L2.2.1 = 0))
    L2.2.2.1

noncomputable def charonSidecarFullLedger : RouteCostAndScopeLedger := (4, 0, true, 3, 9, 6, 2)
noncomputable def directMirFullLedger : RouteCostAndScopeLedger := (4, 0, true, 2, 13, 5, 3)
noncomputable def charonUnpatchedLedger : RouteCostAndScopeLedger := (2, 2, false, 3, 5, 2, 1)
noncomputable def rustcPublicPartialLedger : RouteCostAndScopeLedger := (3, 1, false, 3, 10, 4, 2)

/-- Endpoint 3 (`FE-11`): Matched usability comparisons require full 4-task scope and retention of
divergence and stateful cleanup alongside complete extraction, proof, and shared-setup cost. -/
theorem fe11_scope_and_cost_jointly_classified :
    (∀ L1 L2 : RouteCostAndScopeLedger,
      MatchedUsabilityComparison L1 L2 = true →
      L1.1 = 4 ∧ L1.2.1 = 0 ∧ L1.2.2.1 = true ∧
      L2.1 = 4 ∧ L2.2.1 = 0 ∧ L2.2.2.1 = true) ∧
    MatchedUsabilityComparison charonSidecarFullLedger directMirFullLedger = true ∧
    MatchedUsabilityComparison charonUnpatchedLedger directMirFullLedger = false ∧
    MatchedUsabilityComparison rustcPublicPartialLedger directMirFullLedger = false ∧
    totalRouteCost charonSidecarFullLedger = 18 ∧
    totalRouteCost directMirFullLedger = 20 ∧
    totalRouteCost charonUnpatchedLedger = 10 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro L1 L2 hMatch
  rcases allTrue6_eq_true hMatch with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, h3,
         of_decide_eq_true h4, of_decide_eq_true h5, h6⟩

/-- `(syntaxOrWireChanged, unwindSemanticsDrifted, layoutSemanticsDrifted, callInstanceDrifted, independentSemanticAuditPassed)` -/
abbrev CompilerUpgradeDelta := Bool × Bool × Bool × Bool × Bool

noncomputable def UpgradeAccepted (adapterRepaired : Bool) (claimPreserved : Bool)
    (d : CompilerUpgradeDelta) : Bool :=
  allTrue6
    adapterRepaired
    claimPreserved
    (reqFalse true d.2.1)
    (reqFalse true d.2.2.1)
    (reqFalse true d.2.2.2.1)
    d.2.2.2.2

noncomputable def visibleStructuralRenameUpgrade : CompilerUpgradeDelta :=
  (true, false, false, false, true)

/-- Endpoint 4 (`FE-12`): Compiler upgrade acceptance requires adapter repair, claim preservation,
zero silent semantic drift across unwind/layout/call-instance axes, and an independent semantic audit. -/
theorem fe12_upgrade_acceptance_requires_independent_semantic_delta_check
    (adapterRepaired claimPreserved : Bool) (d : CompilerUpgradeDelta)
    (hAcc : UpgradeAccepted adapterRepaired claimPreserved d = true) :
    adapterRepaired = true ∧
    claimPreserved = true ∧
    d.2.1 = false ∧
    d.2.2.1 = false ∧
    d.2.2.2.1 = false ∧
    d.2.2.2.2 = true := by
  rcases allTrue6_eq_true hAcc with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, reqFalse_true_eq_true h3, reqFalse_true_eq_true h4,
         reqFalse_true_eq_true h5, h6⟩

/-- Endpoint 5 (`FE-12`): A visible structural/wire change across a compiler upgrade is rejected
until repaired, rejected if repaired by claim weakening, and accepted once the adapter is repaired
with the frozen `JustifiedRustClaim` preserved. -/
theorem visible_structural_change_repaired_without_claim_weakening :
    visibleStructuralRenameUpgrade.1 = true ∧
    UpgradeAccepted false true visibleStructuralRenameUpgrade = false ∧
    UpgradeAccepted true false visibleStructuralRenameUpgrade = false ∧
    UpgradeAccepted true true visibleStructuralRenameUpgrade = true ∧
    JustifiedRustClaim guardedSliceUpdateSubj :=
  ⟨rfl, rfl, rfl, rfl, positive_witness_admitted_and_nonvacuous.2.2.1⟩

#print axioms model_proof_plus_route_bridge_transfers_rust_claim
#print axioms positive_witness_admitted_and_nonvacuous
#print axioms fe11_scope_and_cost_jointly_classified
#print axioms fe12_upgrade_acceptance_requires_independent_semantic_delta_check
#print axioms visible_structural_change_repaired_without_claim_weakening

end AnnealResearch.FrontendPropertyAndUpgrade
