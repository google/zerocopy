import ToyCoalesce.Programs

/-!
# Counterexamples, positive controls and non-vacuity: copy-to-move upgrades and the analysis
-/

namespace Toy.Coalesce

/-- Semantics abbreviations (atomic assignments). -/
abbrev semC : Sem := ⟨.asCopy, .atomic⟩
abbrev semD : Sem := ⟨.deinit, .atomic⟩
abbrev semI : Sem := ⟨.inPlaceCall, .atomic⟩

/-- If every non-excluded run of `S` completes with trace `t`, and `T` has a non-excluded run
with a different outcome, then `T` does not refine `S`. -/
theorem not_refines_of_witness {semT semS : Sem} {T S : Prog} (A' : Layout) (t : List Event)
    (hS : ∀ A, outcome semS S A = .done t ∨ outcome semS S A = .badLayout)
    (hT : outcome semT T A' ≠ .badLayout) (hne : outcome semT T A' ≠ .done t) :
    ¬ Refines semT T semS S := by
  intro h
  rcases h (outcome semT T A') ⟨A', rfl, hT⟩ with ⟨A, hA, _⟩ | ⟨A, hA, hb⟩
  · rcases hS A with h1 | h1 <;> rw [h1] at hA <;> cases hA
  · rcases hS A with h1 | h1 <;> rw [h1] at hA
    · exact hne hA.symm
    · exact hb hA.symm

/-- If every non-excluded run of `T` completes with trace `t` and some run of `S` completes with
trace `t`, then `T` refines `S`. -/
theorem refines_of_single_trace {semT semS : Sem} {T S : Prog} (t : List Event) (A1 : Layout)
    (hT : ∀ A, outcome semT T A = .done t ∨ outcome semT T A = .badLayout)
    (hS : outcome semS S A1 = .done t) : Refines semT T semS S := by
  intro o ⟨A, hA, hb⟩
  rcases hT A with h | h <;> rw [h] at hA
  · subst hA; exact Or.inr ⟨A1, hS, by simp⟩
  · exact absurd hA.symm hb

/-! ## Source runs of the concrete programs -/

theorem pDtor_outcome (A : Layout) :
    outcome semD pDtor A = .done [.vals [.int 7], .vals [.int 7]] ∨
      outcome semD pDtor A = .badLayout := by
  simp only [pDtor]; run_eval

theorem pIPStore_outcome (A : Layout) :
    outcome semI pIPStore A = .done [.vals [.int 1]] ∨ outcome semI pIPStore A = .badLayout := by
  simp only [pIPStore, pCall]; run_eval

theorem pIPLoad_outcome (sem : Sem) (h : sem = semI ∨ sem = semD) (A : Layout) :
    outcome sem pIPLoad A = .done [.vals [.int 1]] ∨ outcome sem pIPLoad A = .badLayout := by
  rcases h with rfl | rfl <;> simp only [pIPLoad, pCall] <;> run_eval

theorem pIPAddr_outcome (A : Layout) :
    outcome semI pIPAddr A = .done [.cmp false] ∨ outcome semI pIPAddr A = .badLayout := by
  simp only [pIPAddr, pCall]; run_eval

theorem pIPAfter_outcome (A : Layout) :
    outcome semI pIPAfter A = .done [.vals [.int 1]] ∨ outcome semI pIPAfter A = .badLayout := by
  simp only [pIPAfter, pCall]; run_eval

theorem pReuse_outcome (A : Layout) :
    outcome semD pReuse A = .done [.vals [.int 1]] ∨ outcome semD pReuse A = .badLayout := by
  simp only [pReuse]; run_eval

/-! ## Copy-to-move upgrades -/

/-- The destructor-load counterexample under `MoveSem.deinit`: `pDtor` at body index 5 is an upgrade
site; on layout `A0` the source completes with `[7, 7]` and the upgraded program has undefined
behaviour (the destructor reads `x` after the move); the no-read-before-re-initialization condition
fails; and the upgrade is not a refinement. -/
theorem cex_upgrade_moveDeinit_dtorLoad :
    UpgradeSite pDtor 5 qx ∧
    outcome semD pDtor A0 = .done [.vals [.int 7], .vals [.int 7]] ∧
    outcome semD (pDtor.upgradeAt 5) A0 = .ub ∧
    ¬ NoReadBeforeReinit (run semD pDtor A0).log 5 true qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := by
  refine ⟨Or.inl ⟨⟨2, 0, 1⟩, by decide, by decide⟩, by decide, ?_, by decide, ?_⟩
  · rw [pDtor_upgradeAt]; decide
  · refine not_refines_of_witness A0 _ pDtor_outcome ?_ ?_ <;> rw [pDtor_upgradeAt] <;> decide

/-- Positive control for the destructor-load counterexample: without the destructor block the same
upgrade is a refinement under `MoveSem.deinit`. -/
theorem pNoDtor_upgrade_refines : Refines semD (pNoDtor.upgradeAt 5) semD pNoDtor := by
  refine refines_of_single_trace [.vals [.int 7]] A0 ?_ (by decide)
  intro A
  rw [pNoDtor_upgradeAt]; simp only [pDtor, pDtorMv]; run_eval

/-- Tightness of (b) for the in-place theorem, in canonical form (`pIPStore`: the callee stores
through the escaped pointer to `x`, then reads its parameter): the site, (a) and (c) hold on every
layout, (b) fails, and the upgrade is not a refinement under `MoveSem.inPlaceCall`. -/
theorem cex_upgrade_moveInPlaceCall_calleeAvoids :
    CallSite pIPStore 4 0 qx ∧
    (∀ A, outcome semI pIPStore A ≠ .ub → outcome semI pIPStore A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPStore A).log 4 false qx) ∧
    ¬ AddrTaken pIPStore (pIPStore.fn 0).prm ∧
    ¬ CalleeAvoids (run semI pIPStore A0).log 4 qx ∧
    ¬ Refines semI (pIPStore.upgradeAt 4) semI pIPStore := by
  refine ⟨⟨by decide, by decide⟩, ?_, by decide, by decide, ?_⟩
  · intro A _ _
    simp only [pIPStore, pCall, qx]
    log_eval
  · refine not_refines_of_witness A0 _ pIPStore_outcome ?_ ?_ <;>
      simp only [pIPStore, pCall_upgradeAt] <;> decide

/-- Tightness of (c) (`pIPAddr`: the callee compares the address of its parameter with the
escaped pointer to `x`): the site, (a) and (b) hold on every layout, (c) fails (the parameter
local is address-taken, inside the callee), and the upgrade is not a refinement under
`MoveSem.inPlaceCall` (the source comparison is `false` on every non-excluded layout; the
upgraded one is `true` on `A0`). -/
theorem cex_upgrade_moveInPlaceCall_noParamAddr :
    CallSite pIPAddr 4 0 qx ∧
    (∀ A, outcome semI pIPAddr A ≠ .ub → outcome semI pIPAddr A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPAddr A).log 4 false qx) ∧
    (∀ A, outcome semI pIPAddr A ≠ .ub → outcome semI pIPAddr A ≠ .badLayout →
      CalleeAvoids (run semI pIPAddr A).log 4 qx) ∧
    AddrTaken pIPAddr (pIPAddr.fn 0).prm ∧
    ¬ Refines semI (pIPAddr.upgradeAt 4) semI pIPAddr := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, by decide, ?_⟩
  · intro A _ _
    simp only [pIPAddr, pCall, qx]
    log_eval
  · intro A _ _
    simp only [pIPAddr, pCall, qx]
    log_eval
  · refine not_refines_of_witness A0 _ pIPAddr_outcome ?_ ?_ <;>
      simp only [pIPAddr, pCall_upgradeAt] <;> decide

/-- Tightness of (a) (`pIPAfter`: the callee writes its parameter and the caller reads `x` after
the call): the site, (b) and (c) hold on every layout, (a) fails, and the upgrade is not a
refinement under `MoveSem.inPlaceCall`. -/
theorem cex_upgrade_moveInPlaceCall_noReadAfterCall :
    CallSite pIPAfter 4 0 qx ∧
    (∀ A, outcome semI pIPAfter A ≠ .ub → outcome semI pIPAfter A ≠ .badLayout →
      CalleeAvoids (run semI pIPAfter A).log 4 qx) ∧
    ¬ AddrTaken pIPAfter (pIPAfter.fn 0).prm ∧
    ¬ NoReadBeforeReinit (run semI pIPAfter A0).log 4 false qx ∧
    ¬ Refines semI (pIPAfter.upgradeAt 4) semI pIPAfter := by
  refine ⟨⟨by decide, by decide⟩, ?_, by decide, by decide, ?_⟩
  · intro A _ _
    simp only [pIPAfter, pCall, qx]
    log_eval
  · refine not_refines_of_witness A0 _ pIPAfter_outcome ?_ ?_ <;>
      simp only [pIPAfter, pCall_upgradeAt] <;> decide

/-- The in-place scenario with a load (`pIPLoad`: the callee writes its parameter, then loads
through the escaped pointer to `x`): the upgrade is not a refinement under `MoveSem.inPlaceCall`
(the callee sees the new value) nor under `MoveSem.deinit` (the load reads `x` after the move);
this program violates (b) and also the `MoveSem.deinit` condition, so it is not a canonical
tightness witness for (b) alone. -/
theorem cex_upgrade_callee_load_escaped :
    ¬ CalleeAvoids (run semI pIPLoad A0).log 4 qx ∧
    ¬ NoReadBeforeReinit (run semD pIPLoad A0).log 4 true qx ∧
    outcome semI (pIPLoad.upgradeAt 4) A0 = .done [.vals [.int 2]] ∧
    ¬ Refines semI (pIPLoad.upgradeAt 4) semI pIPLoad ∧
    ¬ Refines semD (pIPLoad.upgradeAt 4) semD pIPLoad := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · simp only [pIPLoad, pCall_upgradeAt]; decide
  · refine not_refines_of_witness A0 _ (pIPLoad_outcome semI (Or.inl rfl)) ?_ ?_ <;>
      simp only [pIPLoad, pCall_upgradeAt] <;> decide
  · refine not_refines_of_witness A0 _ (pIPLoad_outcome semD (Or.inr rfl)) ?_ ?_ <;>
      simp only [pIPLoad, pCall_upgradeAt] <;> decide

/-- Under atomic assignments, `MoveSem.deinit` and `MoveSem.inPlaceCall` admit incomparable sets
of refining upgrades: on `pIPStore` the call-argument upgrade is a refinement under
`MoveSem.deinit` but not under `MoveSem.inPlaceCall`; on `pReuse` the assignment upgrade is a
refinement under `MoveSem.inPlaceCall` but not under `MoveSem.deinit`. -/
theorem moveDeinit_moveInPlaceCall_upgrades_incomparable :
    (Refines semD (pIPStore.upgradeAt 4) semD pIPStore ∧
      ¬ Refines semI (pIPStore.upgradeAt 4) semI pIPStore) ∧
    (Refines semI (pReuse.upgradeAt 3) semI pReuse ∧
      ¬ Refines semD (pReuse.upgradeAt 3) semD pReuse) := by
  refine ⟨⟨?_, cex_upgrade_moveInPlaceCall_calleeAvoids.2.2.2.2⟩, ?_, ?_⟩
  · refine refines_of_single_trace [.vals [.int 1]] A0 ?_ (by decide)
    intro A
    simp only [pIPStore, pCall_upgradeAt, pCallMv]
    run_eval
  · refine refines_of_single_trace [.vals [.int 1]] A0 ?_ (by decide)
    intro A
    rw [pReuse_upgradeAt]
    simp only [pReuseMv, pReuse]
    run_eval
  · refine not_refines_of_witness A0 _ pReuse_outcome ?_ ?_ <;> rw [pReuse_upgradeAt] <;> decide

/-! ## The backward analysis -/

/-- The destructor-blind analysis: the backward scan over the body, ignoring the destructor block. -/
def obsBodyOnly (P : Prog) : ObsMask := fun t u => obsFrom P u (P.body.drop t)

/-- The destructor-blind analysis admits the destructor-load counterexample: its mask satisfies
the certificate conditions over the body and licenses the `MoveSem.deinit` upgrade at body index 5 of
`pDtor`, which is not a refinement. -/
theorem cex_obsCertBodyOnly_licenses_dtorLoad :
    ObsCertBodyOnly pDtor (obsBodyOnly pDtor) ∧ Licensed .deinit pDtor (obsBodyOnly pDtor) 5 qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := by
  refine ⟨?_, ⟨by decide, ?_⟩, cex_upgrade_moveDeinit_dtorLoad.2.2.2.2⟩
  · unfold ObsCertBodyOnly; decide
  · intro fn h; simp [pDtor] at h

/-- Positive control: the full analysis (body and destructors) is a certificate for `pDtor` and
does not license that upgrade. -/
theorem obsAnalysis_rejects_dtorLoad :
    checkObs pDtor (obsAnalysis pDtor) = true ∧ ¬ Licensed .deinit pDtor (obsAnalysis pDtor) 5 qx := by
  refine ⟨by decide, ?_⟩
  intro h; exact absurd h.1 (by decide)

/-- Non-vacuity for the licensed-upgrade theorem under `MoveSem.deinit`: the full analysis is a
certificate for `pNoDtor` and licenses the upgrade at body index 5. -/
theorem nonvacuous_upgrade_refines_of_obsCert_licensed :
    UpgradeSite pNoDtor 5 qx ∧ ObsCert pNoDtor (obsAnalysis pNoDtor) ∧
    Licensed .deinit pNoDtor (obsAnalysis pNoDtor) 5 qx := by
  refine ⟨Or.inl ⟨⟨2, 0, 1⟩, by decide, by decide⟩, ?_, by decide, ?_⟩
  · unfold ObsCert; decide
  · intro fn h; simp [pNoDtor, pDtor] at h

end Toy.Coalesce
