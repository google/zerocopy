import ToyCoalesce.Examples

/-!
# Further tightness counterexamples
-/

namespace Toy.Coalesce

/-! ## The `MoveSem.deinit` characterization -/

/-- `x := 1; x := copy x` (body index 2; left side equal to the read place); out x. -/
def pSelf : Prog where
  sizes := [1]
  body := [.storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 1], .assign ⟨0, 0, 1⟩ [.copy ⟨0, 0, 1⟩],
    .out (.copy ⟨0, 0, 1⟩)]
  dtors := []
  fns := []

/-- Dropping the left-side disjointness of an upgrade site breaks the characterization: on
`pSelf` (`x := copy x` upgraded to `x := move x`) the source run on `A0` is neither undefined nor
excluded, the outcomes are equal, and the no-read-before-re-initialization condition fails. -/
theorem cex_upgrade_deinit_iff_lhs_overlap :
    pSelf.body[2]? = some (.assign qx [.copy qx]) ∧ ¬ WindowsDisjoint qx qx ∧
    outcome semD pSelf A0 = .done [.vals [.int 1]] ∧
    outcome semD (pSelf.upgradeAt 2) A0 = outcome semD pSelf A0 ∧
    ¬ NoReadBeforeReinit (run semD pSelf A0).log 2 true qx := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  simp [pSelf, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]; decide

/-- `pReuse` with a destructor that reads a non-existent local (undefined behaviour). -/
def pReuseUB : Prog := { pReuse with dtors := [.out (.copy ⟨5, 0, 1⟩)] }

/-- Dropping "the source run is not undefined" breaks the characterization: on `pReuseUB` (site
at body index 3) both outcomes are undefined behaviour, hence equal, while the condition fails. -/
theorem cex_upgrade_deinit_iff_source_ub :
    UpgradeSite pReuseUB 3 qx ∧ outcome semD pReuseUB A0 = .ub ∧
    outcome semD (pReuseUB.upgradeAt 3) A0 = outcome semD pReuseUB A0 ∧
    ¬ NoReadBeforeReinit (run semD pReuseUB A0).log 3 true qx := by
  refine ⟨Or.inl ⟨⟨1, 0, 1⟩, by decide, by decide⟩, by decide, ?_, by decide⟩
  simp [pReuseUB, pReuse, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]; decide

/-- Dropping "the source run is not excluded" breaks the characterization: on `pReuse` with the
layout that puts every local at address `0`, both runs are excluded (equal outcomes) while the
condition fails. -/
theorem cex_upgrade_deinit_iff_bad_layout :
    UpgradeSite pReuse 3 qx ∧ outcome semD pReuse (fun _ => 0) = .badLayout ∧
    outcome semD (pReuse.upgradeAt 3) (fun _ => 0) = outcome semD pReuse (fun _ => 0) ∧
    ¬ NoReadBeforeReinit (run semD pReuse (fun _ => 0)).log 3 true qx := by
  refine ⟨Or.inl ⟨⟨1, 0, 1⟩, by decide, by decide⟩, by decide, ?_, by decide⟩
  rw [pReuse_upgradeAt]; decide

/-- Non-vacuity of the characterization: `pNoDtor` at body index 5 on `A0` satisfies every
hypothesis (and both sides hold). -/
theorem nonvacuous_upgrade_moveDeinit_iff :
    UpgradeSite pNoDtor 5 qx ∧ outcome semD pNoDtor A0 ≠ .ub ∧
    outcome semD pNoDtor A0 ≠ .badLayout ∧
    NoReadBeforeReinit (run semD pNoDtor A0).log 5 true qx :=
  ⟨Or.inl ⟨⟨2, 0, 1⟩, by decide, by decide⟩, by decide, by decide, by decide⟩

/-- Non-vacuity of the sufficient `MoveSem.deinit` condition: on `pNoDtor` (site 5) the condition holds
on every layout whose source run is neither undefined nor excluded. -/
theorem nonvacuous_upgrade_moveDeinit_refines :
    UpgradeSite pNoDtor 5 qx ∧
    ∀ A, outcome semD pNoDtor A ≠ .ub → outcome semD pNoDtor A ≠ .badLayout →
      NoReadBeforeReinit (run semD pNoDtor A).log 5 true qx := by
  refine ⟨Or.inl ⟨⟨2, 0, 1⟩, by decide, by decide⟩, ?_⟩
  intro A _ _; simp only [pNoDtor, pDtor, qx]; log_eval

/-- The non-call restriction of `upgrade_outcome_eq_moveInPlaceCall_of_not_call` is needed: at the
call site of `pIPStore` the outcomes on `A0` differ under `MoveSem.inPlaceCall`. -/
theorem cex_upgrade_inPlaceCall_call_site :
    pIPStore.body[4]? = some (.call 0 (.copy qx)) ∧
    outcome semI (pIPStore.upgradeAt 4) A0 ≠ outcome semI pIPStore A0 := by
  refine ⟨by decide, ?_⟩
  simp only [pIPStore, pCall_upgradeAt]; decide

/-- Non-vacuity of the in-place theorem: `pIPOk` (the callee reads its parameter and does nothing
else) satisfies the site, (a), (b) and (c). -/
theorem nonvacuous_upgrade_moveInPlaceCall :
    CallSite pIPOk 4 0 qx ∧
    (∀ A, outcome semI pIPOk A ≠ .ub → outcome semI pIPOk A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPOk A).log 4 false qx) ∧
    (∀ A, outcome semI pIPOk A ≠ .ub → outcome semI pIPOk A ≠ .badLayout →
      CalleeAvoids (run semI pIPOk A).log 4 qx) ∧
    ¬ AddrTaken pIPOk (pIPOk.fn 0).prm := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, by decide⟩
  · intro A _ _; simp only [pIPOk, pCall, qx]; log_eval
  · intro A _ _; simp only [pIPOk, pCall, qx]; log_eval

/-! ## Certificate soundness -/

/-- The certificate hypothesis is needed: the all-false mask is not a certificate for `pReuse`,
it does not contain `x` at tick 4, and with it the no-read conclusion at body index 3 fails. -/
theorem cex_noRead_needs_obsCert :
    ¬ ObsCert pReuse (fun _ _ => false) ∧ (fun _ _ => false : ObsMask) (3 + 1) qx.base = false ∧
    ¬ NoReadBeforeReinit (run semD pReuse A0).log 3 false qx := by
  refine ⟨?_, rfl, by decide⟩
  unfold ObsCert; decide

/-- The hypothesis `q.base ∉ O (k+1)` is needed: the computed certificate for `pReuse` contains
`x` at tick 4, and the conclusion fails. -/
theorem cex_noRead_needs_not_in_mask :
    ObsCert pReuse (obsAnalysis pReuse) ∧ obsAnalysis pReuse 4 0 = true ∧
    ¬ NoReadBeforeReinit (run semD pReuse A0).log 3 false qx := by
  refine ⟨?_, by decide, by decide⟩
  unfold ObsCert; decide

/-- The certificate hypothesis of the licensed-upgrade theorem is needed: the all-false mask
licenses the `MoveSem.deinit` upgrade at body index 5 of `pDtor`, which is not a refinement. -/
theorem cex_licensed_needs_obsCert :
    UpgradeSite pDtor 5 qx ∧
    ¬ ObsCert pDtor (fun _ _ => false) ∧ Licensed .deinit pDtor (fun _ _ => false) 5 qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := by
  refine ⟨ex_upgradeSite_pos, ?_, ⟨rfl, ?_⟩, cex_upgrade_moveDeinit_dtorLoad.2.2.2.2⟩
  · unfold ObsCert; decide
  · intro fn h; simp [pDtor] at h

/-- The licensing hypothesis is needed: the computed certificate for `pDtor` does not license the
upgrade at body index 5, which is not a refinement. -/
theorem cex_licensed_needs_licensing :
    UpgradeSite pDtor 5 qx ∧
    ObsCert pDtor (obsAnalysis pDtor) ∧ ¬ Licensed .deinit pDtor (obsAnalysis pDtor) 5 qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor :=
  ⟨ex_upgradeSite_pos, ex_obsCert_pos, ex_licensed_neg, cex_upgrade_moveDeinit_dtorLoad.2.2.2.2⟩

/-! ## Staging -/

/-- A callee that swaps the fields of its two-cell parameter with an aggregate. -/
def pCalleeSwap : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .call 0 (.copy ⟨0, 0, 2⟩)]
  dtors := []
  fns := [⟨1, [.assign ⟨1, 0, 2⟩ [.copy ⟨1, 1, 1⟩, .copy ⟨1, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩)]⟩]

/-- The callee restriction of the staging theorems is needed: `pCalleeSwap` mentions only
existing locals and its callee parameter exists, it has a callee assignment that needs staging,
staging leaves callees unchanged, and the staged program under in-order writes does not refine
(hence does not have the same behaviours as) the source under atomic assignment. -/
theorem cex_stage_needs_calleesNoStaging :
    LocalsInRange pCalleeSwap ∧ ParamsInRange pCalleeSwap ∧ ¬ CalleesNoStaging pCalleeSwap ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage pCalleeSwap) ⟨.deinit, .atomic⟩ pCalleeSwap ∧
    ¬ BehEq ⟨.deinit, .inOrder⟩ (stage pCalleeSwap) ⟨.deinit, .atomic⟩ pCalleeSwap := by
  have hnr : ¬ Refines ⟨.deinit, .inOrder⟩ (stage pCalleeSwap) ⟨.deinit, .atomic⟩ pCalleeSwap := by
    refine not_refines_of_witness A0 [.vals [.int 2, .int 1]] ?_ (by decide) (by decide)
    intro A; simp only [pCalleeSwap]; run_eval
  refine ⟨by decide, by decide, by decide, hnr, fun hb => hnr fun o ho => Or.inr ((hb o).1 ho)⟩

/-- The coalesced `pSwap` followed by statements that use local `2` (the index `stage` gives its
fresh temporary). -/
def pTmpClash : Prog :=
  { coalesce (single 1 0 0) pSwap with
    body := (coalesce (single 1 0 0) pSwap).body ++
      [.storageLive 2, .assign ⟨2, 0, 2⟩ [.lit 3, .lit 4], .out (.copy ⟨2, 0, 2⟩)] }

/-- The locals-in-range hypothesis of the behavioural-equivalence form is needed: `pTmpClash`
mentions local `2`, which does not exist in it (every run is undefined) but is the staging
temporary of `stage pTmpClash`, which completes. The refinement form still holds there. -/
theorem cex_stage_behEq_needs_localsInRange :
    CalleesNoStaging pTmpClash ∧ ¬ LocalsInRange pTmpClash ∧
    ¬ BehEq ⟨.deinit, .inOrder⟩ (stage pTmpClash) ⟨.deinit, .atomic⟩ pTmpClash := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hT : Beh ⟨.deinit, .inOrder⟩ (stage pTmpClash)
      (.done [.vals [.int 2, .int 1], .vals [.int 3, .int 4]]) := ⟨A0, by decide, by decide⟩
  obtain ⟨A, hA, _⟩ := (h _).1 hT
  have hS : outcome ⟨.deinit, .atomic⟩ pTmpClash A = .ub ∨
      outcome ⟨.deinit, .atomic⟩ pTmpClash A = .badLayout := by
    simp only [pTmpClash, pSwap]; coalesce_simp; run_eval
  rcases hS with h1 | h1 <;> rw [h1] at hA <;> cases hA

/-- A source with an overlapping aggregate assignment: `y := (1, 2); y := (y.1, y.0); out y`. -/
def pOverlapSrc : Prog where
  sizes := [2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2],
    .assign ⟨0, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨0, 0, 2⟩)]
  dtors := []
  fns := []

/-- The source restriction of the pipeline theorem is needed: with the empty forest, the staged
`pOverlapSrc` prints `(2, 1)` while the source under in-order writes prints `(2, 2)`. -/
theorem cex_pipeline_needs_noStagingNeeded :
    ForestWF pOverlapSrc [] ∧ NoValueClobberStmt .deinit [] pOverlapSrc ∧
    ClassAddrDisjoint pOverlapSrc [] ∧ CalleesNoStaging (coalesce [] pOverlapSrc) ∧
    ParamsInRange pOverlapSrc ∧ ¬ NoStagingNeeded pOverlapSrc ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce [] pOverlapSrc)) ⟨.deinit, .inOrder⟩ pOverlapSrc := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, ?_⟩
  · intro A _ _; simp only [pOverlapSrc]; log_eval
  · refine not_refines_of_witness A0 [.vals [.int 2, .int 2]] ?_ (by decide) (by decide)
    intro A; simp only [pOverlapSrc]; run_eval

/-! ## Backward transfer -/

/-- Backward transfer of an address-free postcondition needs `NoValueClobberStmt`: on `pClobber` the coalesced
program satisfies "the erased trace is `[9], [9, 5]`", the source has no undefined behaviour but
does not satisfy it. -/
theorem cex_vc_backward_needs_noValueClobber :
    ForestWF pClobber (single 0 1 0) ∧ ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    UBFree semD pClobber ∧ AddrFree (erasedIs [.vals [.int 9], .vals [.int 9, .int 5]]) ∧
    Valid semD (coalesce (single 0 1 0) pClobber) (erasedIs [.vals [.int 9], .vals [.int 9, .int 5]]) ∧
    ¬ Valid semD pClobber (erasedIs [.vals [.int 9], .vals [.int 9, .int 5]]) := by
  refine ⟨by decide, (cex_coalesce_single_valueClobber .deinit).2.2.2.1, ?_, erasedIs_addrFree _,
    ?_, ?_⟩
  · intro ⟨A, hA, _⟩
    rcases pClobber_outcome .deinit A with h | h <;> rw [h] at hA <;> cases hA
  · intro o ⟨A, hA, hb⟩
    have hT : outcome semD (coalesce (single 0 1 0) pClobber) A =
        .done [.vals [.int 9], .vals [.int 9, .int 5]] ∨
        outcome semD (coalesce (single 0 1 0) pClobber) A = .badLayout := by
      simp only [pClobber]; coalesce_simp; run_eval
    rcases hT with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, hp⟩ := hv _ ⟨A0, rfl, by decide⟩
    have h2 : outcome semD pClobber A0 = .done [.vals [.int 7], .vals [.int 9, .int 5]] := by decide
    rw [h2] at ht; cases ht; revert hp; decide

/-- The postcondition "some pointer comparison returned `true`" (address-mentioning). -/
def someCmpTrue (t : List Event) : Prop := t.any (fun e => e == .cmp true) = true

instance : DecidablePred someCmpTrue := fun t => by unfold someCmpTrue; infer_instance

/-- Backward transfer needs address-freedom: on `p3`, `NoValueClobberStmt` holds, the source has no undefined
behaviour, the coalesced program satisfies `someCmpTrue`, the source does not. -/
theorem cex_vc_backward_addrPost :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    UBFree semD p3 ∧ ¬ AddrFree someCmpTrue ∧
    Valid semD (coalesce (single 0 1 0) p3) someCmpTrue ∧ ¬ Valid semD p3 someCmpTrue := by
  refine ⟨by decide, (cex_coalesce_single_addrTaken_lexOverlap .deinit).2.1, ?_, ?_, ?_, ?_⟩
  · intro ⟨A, hA, _⟩
    rcases p3_outcome .deinit A with h | h <;> rw [h] at hA <;> cases hA
  · intro h
    have := (h [.cmp true] [.cmp false] rfl).1 (by decide)
    revert this; decide
  · intro o ⟨A, hA, hb⟩
    have hT : outcome semD (coalesce (single 0 1 0) p3) A =
        .done [.vals [.int 7], .cmp true, .vals [.int 9, .int 5]] ∨
        outcome semD (coalesce (single 0 1 0) p3) A = .badLayout := by
      simp only [p3]; coalesce_simp; run_eval
    rcases hT with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, hp⟩ := hv _ ⟨A0, rfl, by decide⟩
    have h2 : outcome semD p3 A0 = .done [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]] := by
      decide
    rw [h2] at ht; cases ht; revert hp; decide

/-! ## Pipeline tightness under in-order writes -/

/-- The no-staging hypothesis of `outcome_inOrder_eq_atomic_of_noStagingNeeded` is needed: the
coalesced `pSwap` needs staging and its in-order and atomic outcomes on `A0` differ. -/
theorem cex_inOrder_eq_atomic_needs_noStaging :
    ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) ∧
    outcome ⟨.deinit, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A0 ≠
      outcome ⟨.deinit, .atomic⟩ (coalesce (single 1 0 0) pSwap) A0 := by decide

theorem p3_outcome_inOrder (A : Layout) :
    outcome ⟨.deinit, .inOrder⟩ p3 A = .done [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]] ∨
      outcome ⟨.deinit, .inOrder⟩ p3 A = .badLayout := by
  simp only [p3]; run_eval

theorem pClobber_outcome_inOrder (A : Layout) :
    outcome ⟨.deinit, .inOrder⟩ pClobber A = .done [.vals [.int 7], .vals [.int 9, .int 5]] ∨
      outcome ⟨.deinit, .inOrder⟩ pClobber A = .badLayout := by
  simp only [pClobber]; run_eval

/-- Tightness of the root-level address check for both pipeline theorems, under in-order writes
(`p3`, merge `x ↦ y.0`): every other hypothesis of either form holds, and neither the staged nor
the unstaged coalesced program refines the source. -/
theorem cex_pipeline_needs_classAddrDisjoint :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    NoStagingNeeded p3 ∧ CalleesNoStaging (coalesce (single 0 1 0) p3) ∧ ParamsInRange p3 ∧
    NoStagingNeeded (coalesce (single 0 1 0) p3) ∧
    ¬ ClassAddrDisjoint p3 (single 0 1 0) ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce (single 0 1 0) p3)) ⟨.deinit, .inOrder⟩ p3 ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (coalesce (single 0 1 0) p3) ⟨.deinit, .inOrder⟩ p3 := by
  refine ⟨by decide, (cex_coalesce_single_addrTaken_lexOverlap .deinit).2.1, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_⟩
  · exact not_refines_of_witness A0 _ p3_outcome_inOrder (by decide) (by decide)
  · exact not_refines_of_witness A0 _ p3_outcome_inOrder (by decide) (by decide)

/-- Tightness of `NoValueClobberStmt` for both pipeline theorems, under in-order writes
(`pClobber`, merge `x ↦ y.0`): every other hypothesis of either form holds, and neither the staged
nor the unstaged coalesced program refines the source. -/
theorem cex_pipeline_needs_noValueClobber :
    ForestWF pClobber (single 0 1 0) ∧ ClassAddrDisjoint pClobber (single 0 1 0) ∧
    NoStagingNeeded pClobber ∧ CalleesNoStaging (coalesce (single 0 1 0) pClobber) ∧
    ParamsInRange pClobber ∧ NoStagingNeeded (coalesce (single 0 1 0) pClobber) ∧
    ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce (single 0 1 0) pClobber)) ⟨.deinit, .inOrder⟩
      pClobber ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (coalesce (single 0 1 0) pClobber) ⟨.deinit, .inOrder⟩ pClobber := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (cex_coalesce_single_valueClobber .deinit).2.2.2.1, ?_, ?_⟩
  · exact not_refines_of_witness A0 _ pClobber_outcome_inOrder (by decide) (by decide)
  · exact not_refines_of_witness A0 _ pClobber_outcome_inOrder (by decide) (by decide)

/-! ## Copy-to-move upgrades: further witnesses -/

/-- Non-vacuity of the non-call in-place theorem: body index 3 of `pReuse` is not a call. -/
theorem nonvacuous_upgrade_outcome_eq_moveInPlaceCall_of_not_call :
    ∀ fn a, pReuse.body[3]? ≠ some (.call fn a) := by
  intro fn a h; simp [pReuse] at h

/-- The upgrade-site hypothesis of the `MoveSem.deinit` refinement form is needed: on `pReuse`,
`UpgradeSite pReuse 3 y` fails for the place `y` (local 1), which is not the upgraded place; the
no-read condition holds for `y` on every layout whose source run is neither undefined nor
excluded; and the upgrade at body index 3 (of `copy x`) is not a refinement. -/
theorem cex_upgrade_deinit_refines_needs_site :
    ¬ UpgradeSite pReuse 3 ⟨1, 0, 1⟩ ∧
    (∀ A, outcome semD pReuse A ≠ .ub → outcome semD pReuse A ≠ .badLayout →
      NoReadBeforeReinit (run semD pReuse A).log 3 true ⟨1, 0, 1⟩) ∧
    ¬ Refines semD (pReuse.upgradeAt 3) semD pReuse := by
  refine ⟨by simp [UpgradeSite, pReuse], ?_, moveDeinit_moveInPlaceCall_upgrades_incomparable.2.2⟩
  intro A _ _; simp only [pReuse]; log_eval

/-- Non-vacuity of the licensed-upgrade theorem under `MoveSem.inPlaceCall`: the full analysis is
a certificate for `pIPOk` and licenses the call-argument upgrade at body index 4. -/
theorem nonvacuous_upgrade_refines_of_obsCert_licensed_inPlaceCall :
    UpgradeSite pIPOk 4 qx ∧ ObsCert pIPOk (obsAnalysis pIPOk) ∧
    Licensed .inPlaceCall pIPOk (obsAnalysis pIPOk) 4 qx := by
  refine ⟨Or.inr (Or.inl ⟨0, by decide, by decide⟩), ?_, ex_licensed_inPlaceCall_pos⟩
  unfold ObsCert; decide

/-- Licensing is incomplete: on `pLoadOther`, no certificate licenses the `MoveSem.deinit`
upgrade at body index 8 (the later `load` through `p` counts as a possible read of the
address-taken `x`, although `p` then points to `z`), yet the upgrade is a refinement. -/
theorem cex_licensed_incomplete :
    UpgradeSite pLoadOther 8 qx ∧
    (∀ O, ObsCert pLoadOther O → ¬ Licensed .deinit pLoadOther O 8 qx) ∧
    Refines semD (pLoadOther.upgradeAt 8) semD pLoadOther := by
  refine ⟨Or.inl ⟨⟨2, 0, 1⟩, by decide, by decide⟩, ?_, ?_⟩
  · intro O hO hl
    have h9 := (hO 9 (by decide) 0 (by decide)).1 (by decide)
    have h0 : O 9 0 = false := hl.1
    rw [h0] at h9; cases h9
  · refine refines_of_single_trace [.vals [.int 3], .vals [.int 7]] A0 ?_ (by decide)
    intro A
    simp only [pLoadOther, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]
    run_eval

/-! ## Coalescing: well-formedness witnesses -/

theorem pSmallParent_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ pSmallParent A = .done [.vals [.int 1, .int 2]] ∨
    outcome ⟨ms, .atomic⟩ pSmallParent A = .badLayout := by
  cases ms <;> simp only [pSmallParent] <;> run_eval

/-- Tightness of the well-formedness hypothesis of the coalescing and forward-transfer theorems
(fit clause): on `pSmallParent` the merge of the two-cell local 1 into the one-cell local 0 is not
well formed, while `NoValueClobberStmt`, the lexical address condition, `ClassAddrDisjoint` and
the lexical policy check hold and the source is valid for the trivial postcondition; the
coalesced program has undefined behaviour on `A0`, does not refine the source, and is not valid. -/
theorem cex_coalesce_needs_forestWF (ms : MoveSem) :
    ¬ ForestWF pSmallParent (single 1 0 0) ∧
    NoValueClobberStmt ms (single 1 0 0) pSmallParent ∧
    (AddrTaken pSmallParent 1 → AddrTaken pSmallParent 0 → ¬ LexOverlap pSmallParent 1 0) ∧
    ClassAddrDisjoint pSmallParent (single 1 0 0) ∧
    PolicyCheck (fun _ => .lexical) pSmallParent (single 1 0 0) ∧
    AddrFree (fun _ => True) ∧ Valid ⟨ms, .atomic⟩ pSmallParent (fun _ => True) ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSmallParent) A0 = .ub ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSmallParent) ⟨ms, .atomic⟩ pSmallParent ∧
    ¬ Valid ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSmallParent) (fun _ => True) := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, fun _ _ _ => Iff.rfl, ?_,
    by cases ms <;> decide, ?_, ?_⟩
  · intro A _ _; cases ms <;> simp only [pSmallParent] <;> log_eval
  · intro o ⟨A, hA, hb⟩
    rcases pSmallParent_outcome ms A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, trivial⟩
    · exact absurd hA.symm hb
  · exact not_refines_of_witness A0 _ (pSmallParent_outcome ms) (by cases ms <;> decide)
      (by cases ms <;> decide)
  · intro hv
    obtain ⟨t, ht, _⟩ := hv .ub ⟨A0, by cases ms <;> decide, by decide⟩
    cases ht

theorem pOobCall_outcome (sem : Sem) (A : Layout) :
    outcome sem pOobCall A = .done [.vals [.int 7]] ∨ outcome sem pOobCall A = .badLayout := by
  rcases sem with ⟨ms, am⟩
  cases ms <;> cases am <;> simp only [pOobCall] <;> run_eval

/-- Tightness of the well-formedness hypothesis (call clause `CallsInBounds`): `pOobCall` calls an
absent callee, which the semantics runs with parameter local `0`. The merge `1 ↦ 0.0` satisfies
`NoValueClobberStmt`, the lexical address condition, `ClassAddrDisjoint`, every policy check, the
staging conditions and `ParamsInRange`, and the source is valid for the trivial postcondition;
but `ForestWF` fails (`CallsInBounds` fails), the coalesced program allocates local `0` at entry,
the call then has undefined behaviour, and coalescing (staged or not, under either assignment
order) is not a refinement and not valid. -/
theorem cex_coalesce_needs_callsInBounds (ms : MoveSem) :
    ¬ CallsInBounds pOobCall ∧ ¬ ForestWF pOobCall (single 1 0 0) ∧
    NoValueClobberStmt ms (single 1 0 0) pOobCall ∧
    (AddrTaken pOobCall 1 → AddrTaken pOobCall 0 → ¬ LexOverlap pOobCall 1 0) ∧
    ClassAddrDisjoint pOobCall (single 1 0 0) ∧
    (∀ pol : Policy, PolicyCheck pol pOobCall (single 1 0 0)) ∧
    NoStagingNeeded pOobCall ∧ NoStagingNeeded (coalesce (single 1 0 0) pOobCall) ∧
    CalleesNoStaging (coalesce (single 1 0 0) pOobCall) ∧ ParamsInRange pOobCall ∧
    Valid ⟨ms, .atomic⟩ pOobCall (fun _ => True) ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) A0 = .ub ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) ⟨ms, .atomic⟩ pOobCall ∧
    ¬ Refines ⟨ms, .inOrder⟩ (stage (coalesce (single 1 0 0) pOobCall)) ⟨ms, .inOrder⟩ pOobCall ∧
    ¬ Refines ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pOobCall) ⟨ms, .inOrder⟩ pOobCall ∧
    ¬ Valid ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) (fun _ => True) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_, by decide, by decide, by decide,
    by decide, ?_, by cases ms <;> decide, ?_, ?_, ?_, ?_⟩
  · intro A _ _; cases ms <;> simp only [pOobCall] <;> log_eval
  · intro pol u hu v hv hne _ _
    have hu' : u = 0 ∨ u = 1 := by simp [Prog.nloc, pOobCall] at hu; omega
    have hv' : v = 0 ∨ v = 1 := by simp [Prog.nloc, pOobCall] at hv; omega
    have h0 : decide (AddrTaken pOobCall 0) = false := by decide
    have h1 : decide (AddrTaken pOobCall 1) = false := by decide
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact absurd rfl hne
    · rw [h0, h1]; cases pol false <;> decide
    · rw [h1, h0]; cases pol false <;> decide
    · exact absurd rfl hne
  · intro o ⟨A, hA, hb⟩
    rcases pOobCall_outcome ⟨ms, .atomic⟩ A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, trivial⟩
    · exact absurd hA.symm hb
  · exact not_refines_of_witness A0 _ (pOobCall_outcome ⟨ms, .atomic⟩) (by cases ms <;> decide)
      (by cases ms <;> decide)
  · exact not_refines_of_witness A0 _ (pOobCall_outcome ⟨ms, .inOrder⟩) (by cases ms <;> decide)
      (by cases ms <;> decide)
  · exact not_refines_of_witness A0 _ (pOobCall_outcome ⟨ms, .inOrder⟩) (by cases ms <;> decide)
      (by cases ms <;> decide)
  · intro hv
    obtain ⟨t, ht, _⟩ := hv .ub ⟨A0, by cases ms <;> decide, by decide⟩
    cases ht

/-- Non-vacuity for the union–find characterization (`pChainOk`, forest `x ↦ y.1`, `y ↦ z.1`):
the forest is well formed and both sides of the equivalence hold. -/
theorem nonvacuous_ufCheck :
    ForestWF pChainOk μChain ∧ ufCheck pChainOk μChain = true ∧
    ClassAddrDisjointW pChainOk μChain := by decide

/-- Tightness of `ForestWF` for the union–find characterization: on the two-cycle
`0 ↦ 1.0`, `1 ↦ 0.0` over `pPreciseOk` (no address-taken locals) the window-insensitive check
holds vacuously while `ufCheck` rejects the cycle, so the equivalence fails. -/
theorem cex_ufCheck_needs_forestWF :
    ¬ ForestWF pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] ∧
    ClassAddrDisjointW pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] ∧
    ufCheck pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] = false ∧
    ¬ (ufCheck pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] = true ↔
      ClassAddrDisjointW pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩]) := by decide

theorem pCalleeReorder_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ pCalleeReorder A = .done [.vals [.int 1], .vals [.int 99]] ∨
    outcome ⟨ms, .atomic⟩ pCalleeReorder A = .badLayout := by
  cases ms <;> simp only [pCalleeReorder] <;> run_eval

/-- The callee-reordering hazard for precise liveness: on `pCalleeReorder` (merge `x ↦ y.0`, no
address-taken local) the callee writes `y` and then reads `x`; the coalesced program prints `99`
for `x` on `A0` and does not refine the source; `NoValueClobberStmt` fails, and the mixed policy
(lexical for address-taken locals, precise otherwise) rejects the merge, because the call marks
both half-statement points for every local its callee touches. -/
theorem cex_callee_reorder_rejected_by_policy (ms : MoveSem) :
    ForestWF pCalleeReorder (single 0 1 0) ∧
    ¬ AddrTaken pCalleeReorder 0 ∧ ¬ AddrTaken pCalleeReorder 1 ∧
    ¬ PolicyCheck (fun b => if b then .lexical else .precise) pCalleeReorder (single 0 1 0) ∧
    ¬ NoValueClobberStmt ms (single 0 1 0) pCalleeReorder ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 0 1 0) pCalleeReorder) A0 =
      .done [.vals [.int 99], .vals [.int 99]] ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) pCalleeReorder) ⟨ms, .atomic⟩ pCalleeReorder := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by cases ms <;> decide, ?_⟩
  · intro h
    have h0 := h A0 (by cases ms <;> decide) (by cases ms <;> decide)
    revert h0; cases ms <;> decide
  · exact not_refines_of_witness A0 _ (pCalleeReorder_outcome ms) (by cases ms <;> decide)
      (by cases ms <;> decide)

/-! ## Staging and the pipeline: further witnesses -/

/-- Non-vacuity for the staging theorems: `pSwap` needs no staging; the coalesced `pSwap` has an
assignment that needs staging, no callee assignment that does, every callee parameter exists and
every mentioned local exists. -/
theorem nonvacuous_staging :
    NoStagingNeeded pSwap ∧ ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) ∧
    CalleesNoStaging (coalesce (single 1 0 0) pSwap) ∧
    ParamsInRange (coalesce (single 1 0 0) pSwap) ∧
    LocalsInRange (coalesce (single 1 0 0) pSwap) := by decide

/-- Non-vacuity for the non-staging pipeline theorem (`p3x`, merge `x ↦ y.0`). -/
theorem nonvacuous_coalesce_refines_inOrder_of_noStagingNeeded (ms : MoveSem) :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3x ∧
    ClassAddrDisjoint p3x (single 0 1 0) ∧ NoStagingNeeded (coalesce (single 0 1 0) p3x) :=
  ⟨by decide, (nonvacuous_coalesce_single ms).2.1, by decide, by decide⟩

theorem pCalleeCoalSwap_outcome (A : Layout) :
    outcome ⟨.deinit, .inOrder⟩ pCalleeCoalSwap A = .done [.vals [.int 2, .int 1]] ∨
    outcome ⟨.deinit, .inOrder⟩ pCalleeCoalSwap A = .badLayout := by
  simp only [pCalleeCoalSwap]; run_eval

/-- Tightness of the callee condition of the staged pipeline: on `pCalleeCoalSwap` (merge
`y' ↦ y.0` creating an overlapping assignment inside the callee) every other hypothesis holds,
the coalesced callee needs staging, and the staged coalesced program does not refine the source
under in-order writes (`MoveSem.deinit`). -/
theorem cex_pipeline_needs_calleesNoStaging :
    ForestWF pCalleeCoalSwap (single 1 0 0) ∧
    NoValueClobberStmt .deinit (single 1 0 0) pCalleeCoalSwap ∧
    ClassAddrDisjoint pCalleeCoalSwap (single 1 0 0) ∧ NoStagingNeeded pCalleeCoalSwap ∧
    ParamsInRange pCalleeCoalSwap ∧
    ¬ CalleesNoStaging (coalesce (single 1 0 0) pCalleeCoalSwap) ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce (single 1 0 0) pCalleeCoalSwap))
      ⟨.deinit, .inOrder⟩ pCalleeCoalSwap := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, ?_⟩
  · intro A _ _; simp only [pCalleeCoalSwap]; log_eval
  · exact not_refines_of_witness A0 [.vals [.int 2, .int 1]] pCalleeCoalSwap_outcome
      (by decide) (by decide)

theorem pStageOobPrm_outcome (A : Layout) :
    outcome ⟨.inPlaceCall, .atomic⟩ pStageOobPrm A = .done [] ∨
    outcome ⟨.inPlaceCall, .atomic⟩ pStageOobPrm A = .badLayout := by
  simp only [pStageOobPrm]; run_eval

/-- Tightness of `ParamsInRange` for the staging refinement: in `pStageOobPrm` no callee
assignment needs staging, but the callee parameter (local 1) does not exist; staging appends a
two-cell temporary with index 1; the in-place call passing a width-0 place then has undefined
behaviour in the staged program (`MoveSem.inPlaceCall`), so it does not refine the source. -/
theorem cex_stage_refines_needs_paramsInRange :
    CalleesNoStaging pStageOobPrm ∧ ¬ ParamsInRange pStageOobPrm ∧
    outcome ⟨.inPlaceCall, .inOrder⟩ (stage pStageOobPrm) A0 = .ub ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage pStageOobPrm) ⟨.inPlaceCall, .atomic⟩ pStageOobPrm := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact not_refines_of_witness A0 [] pStageOobPrm_outcome (by decide) (by decide)

theorem pSwapPrm_outcome (A : Layout) :
    outcome ⟨.inPlaceCall, .inOrder⟩ pSwapPrm A = .done [.vals [.int 2, .int 1]] ∨
    outcome ⟨.inPlaceCall, .inOrder⟩ pSwapPrm A = .badLayout := by
  simp only [pSwapPrm]; run_eval

/-- Tightness of `ParamsInRange` for the staged pipeline (`pSwapPrm`, merge `y' ↦ y.0`,
`MoveSem.inPlaceCall`): every other hypothesis holds; the callee parameter (local 2) does not
exist, staging gives that index to a two-cell temporary, and the final in-place call of a width-0
place has undefined behaviour in the staged coalesced program. -/
theorem cex_pipeline_needs_paramsInRange :
    ForestWF pSwapPrm (single 1 0 0) ∧
    NoValueClobberStmt .inPlaceCall (single 1 0 0) pSwapPrm ∧
    ClassAddrDisjoint pSwapPrm (single 1 0 0) ∧ NoStagingNeeded pSwapPrm ∧
    CalleesNoStaging (coalesce (single 1 0 0) pSwapPrm) ∧ ¬ ParamsInRange pSwapPrm ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage (coalesce (single 1 0 0) pSwapPrm))
      ⟨.inPlaceCall, .inOrder⟩ pSwapPrm := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, ?_⟩
  · intro A _ _; simp only [pSwapPrm]; log_eval
  · exact not_refines_of_witness A0 _ pSwapPrm_outcome (by decide) (by decide)

/-! ## Verification-condition transfer: joint non-vacuity -/

/-- Non-vacuity for the three transfer theorems (`p3x`, merge `x ↦ y.0`, the address-free
postcondition "the erased trace is `[7], [address], [9, 5]`"): the forest is well formed,
`NoValueClobberStmt`, `ClassAddrDisjoint` and `UBFree` hold, the postcondition is address-free,
and it is valid for both the source and the coalesced program. -/
theorem nonvacuous_vc_p3x :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3x ∧
    ClassAddrDisjoint p3x (single 0 1 0) ∧ UBFree semD p3x ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) ∧
    Valid semD p3x (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) ∧
    Valid semD (coalesce (single 0 1 0) p3x)
      (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) := by
  refine ⟨by decide, (nonvacuous_coalesce_single .deinit).2.1, by decide,
    nonvacuous_vc_backward.2.2.1, erasedIs_addrFree _, ?_, ?_⟩
  · intro o ⟨A, hA, hb⟩
    have : outcome semD p3x A =
        .done [.vals [.int 7], .vals [.addr (A 0)], .vals [.int 9, .int 5]] ∨
        outcome semD p3x A = .badLayout := by simp only [p3x]; run_eval
    rcases this with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by simp [erasedIs, Event.erase]⟩
    · exact absurd hA.symm hb
  · intro o ⟨A, hA, hb⟩
    have : outcome semD (coalesce (single 0 1 0) p3x) A =
        .done [.vals [.int 7], .vals [.addr (A 1)], .vals [.int 9, .int 5]] ∨
        outcome semD (coalesce (single 0 1 0) p3x) A = .badLayout := by
      simp only [p3x]; coalesce_simp; run_eval
    rcases this with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by simp [erasedIs, Event.erase]⟩
    · exact absurd hA.symm hb

/-- The validity hypothesis of the transfer theorems is needed (`p3x`, merge `x ↦ y.0`, the
unsatisfiable postcondition): every other hypothesis of the three transfer theorems holds, and the
postcondition is valid for neither the source nor the coalesced program. -/
theorem cex_vc_needs_valid :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3x ∧
    ClassAddrDisjoint p3x (single 0 1 0) ∧ UBFree semD p3x ∧ AddrFree (fun _ => False) ∧
    ¬ Valid semD p3x (fun _ => False) ∧ ¬ Valid semD (coalesce (single 0 1 0) p3x) (fun _ => False) := by
  refine ⟨by decide, (nonvacuous_coalesce_single .deinit).2.1, by decide,
    nonvacuous_vc_backward.2.2.1, fun _ _ _ => Iff.rfl, ?_, ?_⟩
  · intro hv
    obtain ⟨t, _, hf⟩ := hv _ ⟨A0, rfl, by decide⟩
    exact hf
  · intro hv
    obtain ⟨t, _, hf⟩ := hv _ ⟨A0, rfl, by decide⟩
    exact hf

end Toy.Coalesce
