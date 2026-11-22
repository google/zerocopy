import ToyLoanFlow.Facts
import ToyLoanFlow.Soundness
import ToyLoanFlow.Inclusion

/-!
# Main results

Every result, counterexample, non-vacuity witness and positive control in this file is fully
proved. Soundness of the location-sensitive checker is proved in `Soundness.lean` and the
inclusion of the location-insensitive checker in it in `Inclusion.lean`.
-/

namespace Toy.LoanFlow

variable {n m : Nat}

/-- `Acyclic p`: no node reaches itself by a walk of one or more steps (along `p.succ`). -/
def Acyclic (p : Prog n m) : Prop := ∀ q q' : Fin n, q' ∈ p.succ q → ¬ Reach p.succ q' q

/-- Certificate for `Acyclic`: a reachability over-approximation in which no edge closes a
cycle. -/
theorem acyclic_of_cert {p : Prog n m} (R : List (Fin n × Fin n))
    (hR : reachClosed p.succ R = true)
    (h : ((List.finRange n).all fun q => (p.succ q).all fun q' => !R.contains (q', q)) = true) :
    Acyclic p := by
  intro q q' hq hr
  have := List.all_eq_true.1 (List.all_eq_true.1 h q (List.mem_finRange q)) q' hq
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this (mem_of_reach hR hr)

theorem pc3_acyclic : Acyclic pc3 := acyclic_of_cert (reachAll pc3) (by decide) (by decide)

theorem pUntypedStore_acyclic : Acyclic pUntypedStore :=
  acyclic_of_cert (reachAll pUntypedStore) (by decide) (by decide)

theorem pCopyThenUse_acyclic : Acyclic pCopyThenUse :=
  acyclic_of_cert (reachAll pCopyThenUse) (by decide) (by decide)

theorem pc3Loop_not_acyclic : ¬ Acyclic pc3Loop :=
  fun h => h 0 1 (by decide) (.step (v := 3) (by decide) (.step (v := 0) (by decide) (.refl _)))

/-! ## Result 1: soundness of both checkers -/

/-- **Result 1c.** Every program that is well typed at every node and accepted by the
location-sensitive checker is safe: no walk of `p.succ` from `p.entry`, executed by `run` with
`exec` from `RState.init`, reaches UB (any CFG, including cycles). -/
theorem safe_of_wellTyped_of_lsAccepts (p : Prog n m) (hwt : WellTyped p)
    (hacc : LSAccepts p) : Safe p := by
  intro π hw hh
  cases π with
  | nil => exact hw.elim
  | cons x t =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    exact Sound.run_not_ub hwt hacc t p.entry RState.init hw (Sound.inv_init p)

/-- **Result 2.** For every variance mode `vm`, every program that is well typed at every node
and accepted by the location-insensitive checker `NLL.Accepts vm` is accepted by the
location-sensitive checker with kills at overwrites `LS.Accepts .overwrite vm`. -/
theorem lsAccepts_of_wellTyped_of_nllAccepts (vm : VarMode) (p : Prog n m) (hwt : WellTyped p)
    (h : NLL.Accepts vm p) : LS.Accepts .overwrite vm p :=
  (lsAccepts_overwrite_iff_liveAccepts vm p).2 (liveAccepts_of_wellTyped_of_nllAccepts vm p hwt h)

/-- **Result 1a.** Every program that is well typed at every node and accepted by the
location-insensitive checker is safe: no walk of `p.succ` from `p.entry`, executed by `run` with
`exec` from `RState.init`, reaches UB. -/
theorem safe_of_wellTyped_of_nllAccepts (p : Prog n m) (hwt : WellTyped p)
    (hacc : NLLAccepts p) : Safe p :=
  safe_of_wellTyped_of_lsAccepts p hwt (lsAccepts_of_wellTyped_of_nllAccepts .inv p hwt hacc)

/-- Counterexample for `hwt` in Result 1a: an ill-typed program that the location-insensitive
checker accepts and that reaches UB. -/
theorem nllAccepts_not_safe_without_wellTyped :
    ¬ WellTyped pUntypedHolder ∧ NLLAccepts pUntypedHolder ∧ ¬ Safe pUntypedHolder :=
  ⟨pUntypedHolder_not_wellTyped, pUntypedHolder_nllAccepts, pUntypedHolder_not_safe⟩

/-- Counterexample for `hwt` in Result 1c: an ill-typed program with an acyclic CFG that the
location-sensitive checker accepts and that reaches UB. -/
theorem lsAccepts_not_safe_without_wellTyped :
    ¬ WellTyped pUntypedStore ∧ Acyclic pUntypedStore ∧ LSAccepts pUntypedStore ∧
      ¬ Safe pUntypedStore :=
  ⟨pUntypedStore_not_wellTyped, pUntypedStore_acyclic, pUntypedStore_lsAccepts,
    pUntypedStore_not_safe⟩

/-- Counterexample for the acceptance hypothesis of Results 1a and 1c: a well-typed program
with an acyclic CFG that reaches UB (both checkers reject it). -/
theorem wellTyped_acyclic_not_safe :
    WellTyped pCopyThenUse ∧ Acyclic pCopyThenUse ∧ ¬ Safe pCopyThenUse :=
  ⟨pCopyThenUse_wellTyped, pCopyThenUse_acyclic, pCopyThenUse_not_safe⟩

/-- Non-vacuity of Result 1a, including a witness with non-empty generated constraints. -/
theorem safe_of_wellTyped_of_nllAccepts_nonvacuous :
    (WellTyped pReassign ∧ NLLAccepts pReassign) ∧
      (WellTyped pStoreSafe ∧ NLLAccepts pStoreSafe ∧ gen .inv pStoreSafe 3 ≠ []) :=
  ⟨⟨pReassign_wellTyped, pReassign_nllAccepts⟩,
    ⟨pStoreSafe_wellTyped, pStoreSafe_nllAccepts, by decide⟩⟩

/-- Non-vacuity of Result 1c, with a cyclic CFG and with non-empty generated constraints. -/
theorem safe_of_wellTyped_of_lsAccepts_nonvacuous :
    (WellTyped pc3Loop ∧ ¬ Acyclic pc3Loop ∧ LSAccepts pc3Loop) ∧
      (WellTyped pStoreSafe ∧ LSAccepts pStoreSafe ∧ gen .inv pStoreSafe 3 ≠ []) :=
  ⟨⟨pc3Loop_wellTyped, pc3Loop_not_acyclic, pc3Loop_lsAccepts⟩,
    ⟨pStoreSafe_wellTyped, pStoreSafe_lsAccepts, by decide⟩⟩

/-- Counterexample for `hwt` in Result 2 (at `vm = .inv`). -/
theorem lsAccepts_of_nllAccepts_fails_without_wellTyped :
    ¬ WellTyped pUntypedHolder ∧ NLLAccepts pUntypedHolder ∧ ¬ LSAccepts pUntypedHolder :=
  ⟨pUntypedHolder_not_wellTyped, pUntypedHolder_nllAccepts, pUntypedHolder_not_lsAccepts⟩

/-- Result 2 fails when well-typedness is required only at the nodes reachable from the entry
node: `pUnreachUntyped` is well typed at every reachable node and accepted by the
location-insensitive checker, and the location-sensitive checker rejects it. -/
theorem lsAccepts_of_reachWellTyped_of_nllAccepts_fails :
    (∀ q, Reach pUnreachUntyped.succ pUnreachUntyped.entry q →
      StmtWellTyped pUnreachUntyped (pUnreachUntyped.stmt q)) ∧
      NLLAccepts pUnreachUntyped ∧ ¬ LSAccepts pUnreachUntyped :=
  ⟨pUnreachUntyped_reach_wellTyped, pUnreachUntyped_nllAccepts, pUnreachUntyped_not_lsAccepts⟩

/-- Counterexample for `h` in Result 2: a well-typed program that the location-sensitive
checker rejects. -/
theorem wellTyped_not_lsAccepts : WellTyped pCopyThenUse ∧ ¬ LSAccepts pCopyThenUse :=
  ⟨pCopyThenUse_wellTyped, pCopyThenUse_not_lsAccepts⟩

/-- Non-vacuity of Result 2, for both variance modes and with non-empty generated
constraints. -/
theorem lsAccepts_of_wellTyped_of_nllAccepts_nonvacuous :
    (WellTyped pReassign ∧ NLLAccepts pReassign) ∧
      (WellTyped pVariance ∧ NLL.Accepts .cov pVariance) ∧
      (WellTyped pStoreSafe ∧ NLLAccepts pStoreSafe ∧ gen .inv pStoreSafe 3 ≠ []) :=
  ⟨⟨pReassign_wellTyped, pReassign_nllAccepts⟩, ⟨pVariance_wellTyped, pVariance_nllCov_accepts⟩,
    ⟨pStoreSafe_wellTyped, pStoreSafe_nllAccepts, by decide⟩⟩

/-! ## Result 3: strictness on problem case #3 -/

/-- **Result 3a.** `pc3` is well typed and safe, the location-sensitive checker accepts it,
and the location-insensitive checker rejects it. -/
theorem pc3_wellTyped_safe_lsAccepts_not_nllAccepts :
    WellTyped pc3 ∧ Safe pc3 ∧ LSAccepts pc3 ∧ ¬ NLLAccepts pc3 :=
  ⟨pc3_wellTyped, pc3_safe, pc3_lsAccepts, pc3_not_nllAccepts⟩

/-- **Result 3b.** The loop variant `pc3Loop` is well typed and safe, the location-sensitive
checker accepts it, and the location-insensitive checker rejects it. -/
theorem pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts :
    WellTyped pc3Loop ∧ Safe pc3Loop ∧ LSAccepts pc3Loop ∧ ¬ NLLAccepts pc3Loop :=
  ⟨pc3Loop_wellTyped, pc3Loop_safe, pc3Loop_lsAccepts, pc3Loop_not_nllAccepts⟩

/-- **Result 3c** (the mechanism). In `pc3` the write at node `3` conflicts with the loan
created at node `0`; the outermost origin of the returned local `r` contains every node; that
loan is in scope at node `3` for the location-insensitive checker and not live there for the
location-sensitive checker. -/
theorem pc3_loan0_at_insertion :
    Conflicts pc3 0 3 ∧ (∀ q : Fin 6, NLL.InRegion .inv pc3 (1, 0) q) ∧
      NLL.InScope .inv pc3 0 3 ∧ ¬ LS.LoanLive .overwrite .inv pc3 0 3 :=
  ⟨by decide, pc3_r_region_universal, pc3_nll_loan0_inScope_at_3, pc3_ls_loan0_not_live_at_3⟩

/-- Reference point for Result 3c: when the first loan of problem case #3 is used instead of
returned (`pc3NoReturn`), both checkers accept the program. -/
theorem pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts :
    WellTyped pc3NoReturn ∧ Safe pc3NoReturn ∧ NLLAccepts pc3NoReturn ∧ LSAccepts pc3NoReturn :=
  ⟨pc3NoReturn_wellTyped, pc3NoReturn_safe, pc3NoReturn_nllAccepts, pc3NoReturn_lsAccepts⟩

/-! ## Result 4: kills -/

/-- **Result 4a.** `pReassign` is well typed and safe and both checkers of the package accept
it, while the location-sensitive checker without kills (`LS.Accepts .none`, whose propagation
along edges is limited neither by kills nor by liveness) rejects it. -/
theorem pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts :
    WellTyped pReassign ∧ Safe pReassign ∧ NLLAccepts pReassign ∧ LSAccepts pReassign ∧
      ¬ LS.Accepts .none .inv pReassign :=
  ⟨pReassign_wellTyped, pReassign_safe, pReassign_nllAccepts, pReassign_lsAccepts,
    pReassign_not_lsNoKill_accepts⟩

/-- Result 2 fails for the location-sensitive checker without kills (canonical form). -/
theorem lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails :
    ¬ ∀ p : Prog 5 3, WellTyped p → NLLAccepts p → LS.Accepts .none .inv p :=
  fun h => pReassign_not_lsNoKill_accepts (h _ pReassign_wellTyped pReassign_nllAccepts)

/-- **Result 4b.** Adding kills at the source of a copy makes the location-sensitive checker
accept an unsafe well-typed program, `pCopyThenUse`; the checker with kills at overwrites
alone rejects it (positive control). -/
theorem pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe :
    WellTyped pCopyThenUse ∧ LS.Accepts .overwriteAndCopySrc .inv pCopyThenUse ∧
      ¬ Safe pCopyThenUse ∧ ¬ LSAccepts pCopyThenUse :=
  ⟨pCopyThenUse_wellTyped, pCopyThenUse_lsCopySrcKill_accepts, pCopyThenUse_not_safe,
    pCopyThenUse_not_lsAccepts⟩

/-- The shared-reference counterpart of Result 4b, with `pCopyThenUseShr` copying `&D`. -/
theorem pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe :
    WellTyped pCopyThenUseShr ∧ LS.Accepts .overwriteAndCopySrc .inv pCopyThenUseShr ∧
      ¬ Safe pCopyThenUseShr ∧ ¬ LSAccepts pCopyThenUseShr :=
  ⟨pCopyThenUseShr_wellTyped, pCopyThenUseShr_lsCopySrcKill_accepts, pCopyThenUseShr_not_safe,
    pCopyThenUseShr_not_lsAccepts⟩

/-- Result 1c fails with kills at copy sources (canonical form). -/
theorem safe_of_wellTyped_of_lsCopySrcKillAccepts_fails :
    ¬ ∀ p : Prog 4 3, WellTyped p → LS.Accepts .overwriteAndCopySrc .inv p → Safe p :=
  fun h => pCopyThenUse_not_safe (h _ pCopyThenUse_wellTyped pCopyThenUse_lsCopySrcKill_accepts)

/-- Non-vacuity of Result 4c: `pReassign` is accepted by both sides of the equivalence and
`pCopyThenUse` by neither. -/
theorem lsAccepts_overwrite_iff_liveAccepts_nonvacuous :
    (LSAccepts pReassign ∧ LS.LiveAccepts .inv pReassign) ∧
      (¬ LSAccepts pCopyThenUse ∧ ¬ LS.LiveAccepts .inv pCopyThenUse) :=
  ⟨⟨pReassign_lsAccepts, (lsAccepts_overwrite_iff_liveAccepts .inv pReassign).1
      pReassign_lsAccepts⟩,
    ⟨pCopyThenUse_not_lsAccepts, fun h => pCopyThenUse_not_lsAccepts
      ((lsAccepts_overwrite_iff_liveAccepts .inv pCopyThenUse).2 h)⟩⟩

/-- The statement "Result 2 needs kills in the location-sensitive checker" is false: the
liveness-gated variant without kills `LS.LiveAccepts` satisfies the inclusion of Result 2 for
every variance mode and accepts `pReassign`, which the variant with neither kills nor liveness
gating (`LS.Accepts .none`) rejects. -/
theorem refuted_result2_needs_kills :
    (∀ {n m : Nat} (vm : VarMode) (p : Prog n m), WellTyped p → NLL.Accepts vm p →
      LS.LiveAccepts vm p) ∧
      LS.LiveAccepts .inv pReassign ∧ ¬ LS.Accepts .none .inv pReassign :=
  ⟨fun vm p hwt h => liveAccepts_of_wellTyped_of_nllAccepts vm p hwt h,
    (lsAccepts_overwrite_iff_liveAccepts .inv pReassign).1 pReassign_lsAccepts,
    pReassign_not_lsNoKill_accepts⟩

/-! ## Result 5: invariance of `&mut T` in `T` -/

/-- **Result 5.** With `&mut T` treated as covariant in `T`, both checkers accept the unsafe
well-typed program `pVariance`; with the invariant rule both reject it (positive control). -/
theorem pVariance_wellTyped_covAccepts_not_safe :
    WellTyped pVariance ∧ LS.Accepts .overwrite .cov pVariance ∧ NLL.Accepts .cov pVariance ∧
      ¬ Safe pVariance ∧ ¬ LSAccepts pVariance ∧ ¬ NLLAccepts pVariance :=
  ⟨pVariance_wellTyped, pVariance_lsCov_accepts, pVariance_nllCov_accepts, pVariance_not_safe,
    pVariance_not_lsAccepts, pVariance_not_nllAccepts⟩

/-- Result 1c fails with covariant `&mut` (canonical form). -/
theorem safe_of_wellTyped_of_lsCovAccepts_fails :
    ¬ ∀ p : Prog 6 5, WellTyped p → LS.Accepts .overwrite .cov p → Safe p :=
  fun h => pVariance_not_safe (h _ pVariance_wellTyped pVariance_lsCov_accepts)

/-- Result 1a fails with covariant `&mut` (canonical form). -/
theorem safe_of_wellTyped_of_nllCovAccepts_fails :
    ¬ ∀ p : Prog 6 5, WellTyped p → NLL.Accepts .cov p → Safe p :=
  fun h => pVariance_not_safe (h _ pVariance_wellTyped pVariance_nllCov_accepts)

end Toy.LoanFlow
