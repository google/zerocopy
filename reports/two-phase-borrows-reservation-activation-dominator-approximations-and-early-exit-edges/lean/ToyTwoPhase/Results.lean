import ToyTwoPhase.DefExamples
import ToyTwoPhase.Lemmas

/-!
# Main results

Statements and proofs of the main results, counterexamples in canonical form (all other
hypotheses hold and the conclusion fails), non-vacuity witnesses (all hypotheses hold) and
positive controls. Concrete facts are proved by `decide` or from proved lemmas.

These are statements about the toy model; they neither establish nor refute the corresponding
claims about rustc's borrow checker. Model–system relation: none proved.
-/

namespace Toy.TwoPhase

variable {n : Nat}

/-! ## Supporting lemma -/

/-- If, at every read of `x` under a live loan, phase test `ph₁` implies phase test `ph₂`, then
every program accepted with `ph₂` is accepted with `ph₁`. -/
theorem accepts_of_phase_imp {p : Prog n} {ph₁ ph₂ : Fin n → Prop}
    (himp : ∀ L, (p.op L).isRead = true → LoanLive p L → ph₁ L → ph₂ L)
    (h : Accepts p ph₂) : Accepts p ph₁ := by
  intro L hf
  apply h L
  rcases hf with h1 | ⟨hr, hl, hp⟩ | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨hr, hl, himp L hr hl hp⟩)
  · exact Or.inr (Or.inr h3)

/-! ## R1a. The forward may-analysis computes `MaybeActive` -/

/-- **R1a.** If `A` is reachable from the entry, then at every node `L` the forward may-analysis
(generate at `A`, kill at `R` and `endLoan`, join by disjunction over all edges, `n` rounds from
all-`false`) yields `true` exactly when `MaybeActive p L` holds (both are in-facts: they describe
the point just before `L` executes). -/
theorem dfMaybeActive_iff_maybeActive_of_activation_reachable (p : Prog n)
    (hreach : PathVia p.edges (fun _ => true) p.entry p.A) (L : Fin n) :
    dfMaybeActive p L = true ↔ MaybeActive p L := by
  rw [dfMaybeActive_iff_genReach]
  exact ⟨fun h => (maybeActive_iff p L).2 ⟨hreach, h⟩, fun h => ((maybeActive_iff p L).1 h).2⟩

/-- R1a, tightness of `hreach`: with `A` unreachable, the analysis reports a fact that no walk
from the entry supports. -/
theorem dfMaybeActive_ne_maybeActive_pUnreachA :
    ¬ PathVia pUnreachA.edges (fun _ => true) pUnreachA.entry pUnreachA.A ∧
      dfMaybeActive pUnreachA 4 = true ∧ ¬ MaybeActive pUnreachA 4 := by
  decide

/-- R1a, non-vacuity: `A` is reachable in `pBreak`, and the analysis agrees with `MaybeActive`
at every node there. -/
theorem dfMaybeActive_hypotheses_hold_pBreak :
    PathVia pBreak.edges (fun _ => true) pBreak.entry pBreak.A ∧
      ∀ L : Fin 8, (dfMaybeActive pBreak L = true ↔ MaybeActive pBreak L) := by
  decide

/-! ## R1b. The exact-phase checker is sound -/

/-- **R1b.** Every program accepted by the exact-phase checker (phase test `MaybeActive`) is safe
in the reference semantics. -/
theorem exactPhaseAccepts_safe (p : Prog n) (h : ExactPhaseAccepts p) : Safe p := by
  intro π hw hh
  cases π with
  | nil => exact absurd hw (fun h => h)
  | cons x t =>
    simp at hh; subst hh
    exact run_ne_ub_of_runInv h t p.entry RState.init hw (runInv_init p)

/-- R1b, tightness of `h`: `pBreak` is rejected by the exact-phase checker and is unsafe. -/
theorem exactPhaseAccepts_tight_pBreak : ¬ ExactPhaseAccepts pBreak ∧ ¬ Safe pBreak :=
  ⟨by decide, safe_neg⟩

/-- R1b, non-vacuity: `v.push(v.len())` (a read during the reservation) is accepted. -/
theorem exactPhaseAccepts_hypotheses_hold_pPush : ExactPhaseAccepts pPush := by decide

/-! ## R1c. The iterative dataflow checker is sound -/

/-- **R1c (inclusion).** Every program accepted by the iterative dataflow checker (phase test
`dfMaybeActive`) is accepted by the exact-phase checker. -/
theorem iterDataflowAccepts_exactPhaseAccepts (p : Prog n) (h : IterDataflowAccepts p) :
    ExactPhaseAccepts p :=
  accepts_of_phase_imp (fun _ _ _ hL => dfMaybeActive_of_maybeActive hL) h

/-- **R1c (soundness).** Every program accepted by the iterative dataflow checker is safe. -/
theorem iterDataflowAccepts_safe (p : Prog n) (h : IterDataflowAccepts p) : Safe p :=
  exactPhaseAccepts_safe p (iterDataflowAccepts_exactPhaseAccepts p h)

/-- R1c, tightness of `h`: `pBreak` is rejected by the iterative and exact-phase checkers and is
unsafe. -/
theorem iterDataflowAccepts_tight_pBreak :
    ¬ IterDataflowAccepts pBreak ∧ ¬ ExactPhaseAccepts pBreak ∧ ¬ Safe pBreak :=
  ⟨by decide, by decide, safe_neg⟩

/-- R1c, non-vacuity: `pPush` is accepted by the iterative dataflow checker. -/
theorem iterDataflowAccepts_hypotheses_hold_pPush : IterDataflowAccepts pPush := by decide

/-! ## R1d. With `A` reachable, the two checkers coincide -/

/-- **R1d.** If `A` is reachable from the entry, the iterative dataflow checker and the
exact-phase checker accept the same programs. -/
theorem iterDataflowAccepts_iff_exactPhaseAccepts_of_activation_reachable (p : Prog n)
    (hreach : PathVia p.edges (fun _ => true) p.entry p.A) :
    IterDataflowAccepts p ↔ ExactPhaseAccepts p :=
  ⟨iterDataflowAccepts_exactPhaseAccepts p,
    accepts_of_phase_imp (fun L _ _ hL =>
      (dfMaybeActive_iff_maybeActive_of_activation_reachable p hreach L).1 hL)⟩

/-- R1d, tightness of `hreach`: in `pUnreachMerge` (`A` unreachable) the exact-phase checker
accepts and the iterative dataflow checker rejects; the program is safe. -/
theorem exactPhaseAccepts_not_iterDataflowAccepts_pUnreachMerge :
    ¬ PathVia pUnreachMerge.edges (fun _ => true) pUnreachMerge.entry pUnreachMerge.A ∧
      ExactPhaseAccepts pUnreachMerge ∧ ¬ IterDataflowAccepts pUnreachMerge ∧
      Safe pUnreachMerge :=
  ⟨by decide, by decide, by decide,
    safe_of_cert (explore pUnreachMerge 12 [(pUnreachMerge.entry, RState.init)]) (by decide)
      (by decide)⟩

/-- R1d, non-vacuity: `A` is reachable in `pPush`. -/
theorem iterDataflowAccepts_iff_hypotheses_hold_pPush :
    PathVia pPush.edges (fun _ => true) pPush.entry pPush.A := by decide

/-! ## R2. Dominance and post-dominance of the activation do not suffice in looping CFGs -/

/-- **R2 (counterexample).** In `pLoopBack`, `R` dominates `A`, `A` post-dominates `R` (normal
edges), there are no unwinding edges, and every walk from `A` back to `A` passes `R`; yet at the
read `4` the loan is live and may be active while the dominator test calls it reserved, the
dominator checker accepts, and a run reaches UB. -/
theorem rdomA_apdomR_noUnwind_reentryFree_insufficient_pLoopBack :
    Dom pLoopBack.edges pLoopBack.entry pLoopBack.R pLoopBack.A ∧
      PDom pLoopBack.succ pLoopBack.A pLoopBack.R ∧ NoUnwind pLoopBack ∧
      ReentryFree pLoopBack ∧
      LoanLive pLoopBack 4 ∧ MaybeActive pLoopBack 4 ∧ ¬ IsActiveDom pLoopBack 4 ∧
      DominatorAccepts pLoopBack ∧ ReachesUB pLoopBack [0, 1, 2, 3, 4, 5] := by
  decide

/-- R2, second counterexample: in `pLoop1` the same CFG facts hold except `ReentryFree`, and
also `ActivationStaysReachable` holds; `A` re-enters the reserved region without passing `R`. -/
theorem rdomA_apdomR_noUnwind_insufficient_pLoop1 :
    Dom pLoop1.edges pLoop1.entry pLoop1.R pLoop1.A ∧ PDom pLoop1.succ pLoop1.A pLoop1.R ∧
      NoUnwind pLoop1 ∧ ActivationStaysReachable pLoop1 ∧ ¬ ReentryFree pLoop1 ∧
      LoanLive pLoop1 2 ∧ MaybeActive pLoop1 2 ∧ ¬ IsActiveDom pLoop1 2 ∧
      DominatorAccepts pLoop1 ∧ ReachesUB pLoop1 [0, 1, 2, 3, 2, 3] := by
  decide

/-- R2, third counterexample: in `pDiverge` the `break` target enters a cycle from which `A` is
unreachable; `A` still post-dominates `R`. -/
theorem rdomA_apdomR_noUnwind_reentryFree_insufficient_pDiverge :
    Dom pDiverge.edges pDiverge.entry pDiverge.R pDiverge.A ∧
      PDom pDiverge.succ pDiverge.A pDiverge.R ∧ NoUnwind pDiverge ∧ ReentryFree pDiverge ∧
      ¬ ActivationStaysReachable pDiverge ∧
      LoanLive pDiverge 4 ∧ MaybeActive pDiverge 4 ∧ ¬ IsActiveDom pDiverge 4 ∧
      DominatorAccepts pDiverge ∧ ReachesUB pDiverge [0, 1, 2, 3, 4, 5] := by
  decide

/-- R2, positive control: a looping program satisfying `DomGuard` that the dominator checker
accepts and that is safe. -/
theorem dominatorAccepts_safe_pLoopOK : DomGuard pLoopOK ∧ DominatorAccepts pLoopOK ∧ Safe pLoopOK :=
  ⟨by decide, by decide,
    safe_of_cert (explore pLoopOK 12 [(pLoopOK.entry, RState.init)]) (by decide) (by decide)⟩

/-! ## Shared counterexamples for the hypotheses of R2b, R2c, R7a and R7c -/

/-- `pLoop1` violates `ReentryFree` and satisfies every other hypothesis of R2b, R2c, R7a and
R7c (at node `2`); the conclusions of all four fail. -/
theorem reentryFree_tight_pLoop1 :
    (¬ ReentryFree pLoop1 ∧ ActivationStaysReachable pLoop1 ∧ NoUnwind pLoop1 ∧
      ¬ IsCleanup pLoop1 2 ∧ CleanupReadsUnderDeadLoan pLoop1 ∧ MaybeActive pLoop1 2 ∧
      ¬ IsActiveDom pLoop1 2 ∧ DominatorAccepts pLoop1) ∧ ¬ Safe pLoop1 :=
  ⟨by decide, not_safe_of_reachesUB (π := [0, 1, 2, 3, 2, 3]) (by decide)⟩

/-- `pLoopBack` violates `ActivationStaysReachable` and satisfies every other hypothesis of R2b,
R2c, R7a and R7c (at node `4`); the conclusions of all four fail. -/
theorem activationStaysReachable_tight_pLoopBack :
    (ReentryFree pLoopBack ∧ ¬ ActivationStaysReachable pLoopBack ∧ NoUnwind pLoopBack ∧
      ¬ IsCleanup pLoopBack 4 ∧ CleanupReadsUnderDeadLoan pLoopBack ∧ MaybeActive pLoopBack 4 ∧
      ¬ IsActiveDom pLoopBack 4 ∧ DominatorAccepts pLoopBack) ∧ ¬ Safe pLoopBack :=
  ⟨by decide, not_safe_of_reachesUB (π := [0, 1, 2, 3, 4, 5]) (by decide)⟩

/-- `pCleanup` has unwinding edges into a cleanup block that reads `x` while `r` is live; it
violates `NoUnwind` (R2a, R2b, R2c), `¬ IsCleanup p 6` (R7a) and `CleanupReadsUnderDeadLoan`
(R7c), and satisfies every other hypothesis of those results (at node `6`); their conclusions
fail. -/
theorem unwinding_tight_pCleanup :
    (Acyclic pCleanup.succ ∧ PDom pCleanup.succ pCleanup.A pCleanup.R ∧
      ReentryFree pCleanup ∧ ActivationStaysReachable pCleanup ∧ ¬ NoUnwind pCleanup ∧
      IsCleanup pCleanup 6 ∧ ¬ CleanupReadsUnderDeadLoan pCleanup ∧ MaybeActive pCleanup 6 ∧
      ¬ IsActiveDom pCleanup 6 ∧ DominatorAccepts pCleanup) ∧ ¬ Safe pCleanup :=
  ⟨by decide, not_safe_of_reachesUB (π := [0, 1, 2, 3, 4, 6, 7]) (by decide)⟩

/-- `pWriteDuringRes` satisfies every CFG hypothesis of R2c and R7c, is rejected by the dominator
checker, and is unsafe. -/
theorem dominatorAccepts_tight_pWriteDuringRes :
    (ReentryFree pWriteDuringRes ∧ ActivationStaysReachable pWriteDuringRes ∧
      NoUnwind pWriteDuringRes ∧ CleanupReadsUnderDeadLoan pWriteDuringRes ∧
      ¬ DominatorAccepts pWriteDuringRes) ∧ ¬ Safe pWriteDuringRes :=
  ⟨by decide, not_safe_of_reachesUB (π := [0, 1, 2, 3]) (by decide)⟩

/-! ## R2a. Acyclic CFGs: post-dominance suffices -/

/-- **R2a.** If the normal-edge CFG is acyclic, `A` post-dominates `R` (normal edges), and there
are no unwinding edges, then at every node where the loan may be active the dominator test
calls it active. -/
theorem isActiveDom_of_maybeActive_of_acyclic_pdom_noUnwind (p : Prog n)
    (hac : Acyclic p.succ) (hpd : PDom p.succ p.A p.R) (hnu : NoUnwind p)
    (L : Fin n) (hL : MaybeActive p L) : IsActiveDom p L :=
  isActiveDom_of_maybeActive_of_succWalks p (reentryFree_of_acyclic hac)
    (activationStaysReachable_of_acyclic_pdom hac hpd) L
    (fun π hw => by rwa [edges_eq_succ_of_noUnwind hnu] at hw) hL

/-- R2a, tightness of `hac`: `pLoop1`. -/
theorem acyclic_tight_pLoop1 :
    ¬ Acyclic pLoop1.succ ∧ PDom pLoop1.succ pLoop1.A pLoop1.R ∧ NoUnwind pLoop1 ∧
      MaybeActive pLoop1 2 ∧ ¬ IsActiveDom pLoop1 2 := by
  decide

/-- R2a, tightness of `hpd`: `pBreak` (an acyclic early exit). -/
theorem pdom_tight_pBreak :
    Acyclic pBreak.succ ∧ ¬ PDom pBreak.succ pBreak.A pBreak.R ∧ NoUnwind pBreak ∧
      MaybeActive pBreak 4 ∧ ¬ IsActiveDom pBreak 4 := by
  decide

/-- R2a, tightness of `hL`: in `pPush` at node `2` (between `R` and `A`). -/
theorem maybeActive_tight_pPush :
    Acyclic pPush.succ ∧ PDom pPush.succ pPush.A pPush.R ∧ NoUnwind pPush ∧
      ¬ MaybeActive pPush 2 ∧ ¬ IsActiveDom pPush 2 := by
  decide

/-- R2a, non-vacuity: `pPush` satisfies all hypotheses, at node `4`. -/
theorem acyclic_pdom_hypotheses_hold_pPush :
    Acyclic pPush.succ ∧ PDom pPush.succ pPush.A pPush.R ∧ NoUnwind pPush ∧
      MaybeActive pPush 4 := by
  decide

/-! ## R2b. Looping CFGs: re-entry freedom and a reachable activation suffice -/

/-- **R2b.** If every normal walk from `A` back to `A` passes `R` (`ReentryFree`), every node
`x ≠ R` reached from a normal successor `y ≠ R` of `R` along normal edges without passing `A` or
`R` before `x` can still reach `A` without passing `R` (`ActivationStaysReachable`), and there
are no unwinding edges, then at every node where the loan may be active the dominator test
calls it active. -/
theorem isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_noUnwind
    (p : Prog n) (hre : ReentryFree p) (hasr : ActivationStaysReachable p) (hnu : NoUnwind p)
    (L : Fin n) (hL : MaybeActive p L) : IsActiveDom p L :=
  isActiveDom_of_maybeActive_of_succWalks p hre hasr L
    (fun π hw => by rwa [edges_eq_succ_of_noUnwind hnu] at hw) hL

/-- R2b, tightness of `hL`: in `pLoopOK` at node `2`. -/
theorem maybeActive_tight_pLoopOK :
    ReentryFree pLoopOK ∧ ActivationStaysReachable pLoopOK ∧ NoUnwind pLoopOK ∧
      ¬ MaybeActive pLoopOK 2 ∧ ¬ IsActiveDom pLoopOK 2 := by
  decide

/-- R2b, non-vacuity: `pArgLoop` (a loop between `R` and `A`) satisfies all hypotheses, at
node `4`; its normal CFG is cyclic. -/
theorem reentryFree_activationStaysReachable_hypotheses_hold_pArgLoop :
    ReentryFree pArgLoop ∧ ActivationStaysReachable pArgLoop ∧ NoUnwind pArgLoop ∧
      ¬ Acyclic pArgLoop.succ ∧ MaybeActive pArgLoop 4 := by
  decide

/-- R2b with a `continue` back to `R` (`pContinue`): all hypotheses hold at node `4`, and the
program satisfies `DomGuard`, is accepted by the dominator checker and by repairs (b) and (c),
and is safe. -/
theorem reentryFree_activationStaysReachable_hypotheses_hold_pContinue :
    ReentryFree pContinue ∧ ActivationStaysReachable pContinue ∧ NoUnwind pContinue ∧
      MaybeActive pContinue 4 ∧ DomGuard pContinue ∧ DominatorAccepts pContinue ∧
      RepairBAccepts pContinue ∧ RepairCAccepts pContinue ∧ Safe pContinue :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    safe_of_cert (explore pContinue 12 [(pContinue.entry, RState.init)]) (by decide) (by decide)⟩

/-- R2b variant with `ActivationStaysReachable` weakened to `DomRegionReachesA` (region nodes
dominated by `R` along normal edges): if `ReentryFree`, `DomRegionReachesA` and no unwinding
edges hold, then at every node where the loan may be active the dominator test calls it
active. -/
theorem isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind
    (p : Prog n) (hre : ReentryFree p) (hdr : DomRegionReachesA p) (hnu : NoUnwind p)
    (L : Fin n) (hL : MaybeActive p L) : IsActiveDom p L :=
  isActiveDom_of_maybeActive_of_domRegion p hre hdr hnu L hL

/-- `DomRegionReachesA` is strictly weaker than `ActivationStaysReachable`: `pJoin` satisfies
every hypothesis of `isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind` (at
node `6`) and violates `ActivationStaysReachable`. -/
theorem pJoin_separates_domRegionReachesA :
    (ReentryFree pJoin ∧ DomRegionReachesA pJoin ∧ NoUnwind pJoin ∧ MaybeActive pJoin 6) ∧
      ¬ ActivationStaysReachable pJoin := by
  decide

/-! ## R2c. The dominator checker is sound under the R2b conditions -/

/-- **R2c.** Under `ReentryFree`, `ActivationStaysReachable` and no unwinding edges, every program
accepted by the dominator checker is safe. -/
theorem dominatorAccepts_safe_of_reentryFree_activationStaysReachable_noUnwind (p : Prog n)
    (hre : ReentryFree p) (hasr : ActivationStaysReachable p) (hnu : NoUnwind p)
    (h : DominatorAccepts p) : Safe p :=
  exactPhaseAccepts_safe p (accepts_of_phase_imp
    (fun L _ _ hL =>
      isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_noUnwind p hre hasr hnu
        L hL)
    h)

/-! ## R3. Early exit: the dominator checker accepts an unsafe program -/

/-- **R3 (counterexample; toy rendering of the reproducer of rust-lang/rust#160598).** In
`pBreak` (acyclic, no unwinding edges, `R` dominates `A`, every walk from `A` to `A` passes
`R`), the `break` edge `2 → 4` makes `A` fail to post-dominate `R`. At the join `4`, `R`
strictly dominates `4`, `A` does not dominate `4`, so the dominator test calls the loan
reserved, although it is live and may be active. The dominator checker accepts, the exact-phase
checker rejects, and the fall-through walk `0,1,2,3,4,5,6` (which does not take the edge
`2 → 4`) reaches UB; the walk that takes the `break` halts safely at the write through `r`. -/
theorem pBreak_dominatorAccepts_unsafe :
    Acyclic pBreak.succ ∧ NoUnwind pBreak ∧ ReentryFree pBreak ∧
      Dom pBreak.edges pBreak.entry pBreak.R pBreak.A ∧
      ¬ PDom pBreak.succ pBreak.A pBreak.R ∧
      (pBreak.R ≠ 4 ∧ Dom pBreak.edges pBreak.entry pBreak.R 4) ∧
      ¬ Dom pBreak.edges pBreak.entry pBreak.A 4 ∧ ¬ IsActiveDom pBreak 4 ∧
      LoanLive pBreak 4 ∧ MaybeActive pBreak 4 ∧
      DominatorAccepts pBreak ∧ ¬ ExactPhaseAccepts pBreak ∧
      ReachesUB pBreak [0, 1, 2, 3, 4, 5, 6] ∧
      run pBreak RState.init [0, 1, 2, 4, 5, 6] = .halt := by
  decide

/-- R3, positive control 1: with the `break` hoisted above the reservation, `A` post-dominates
`R`, `DomGuard` holds, and the exact-phase and dominator checkers reject (a run would reach UB).
-/
theorem pBreakHoisted_rejected :
    PDom pBreakHoisted.succ pBreakHoisted.A pBreakHoisted.R ∧ DomGuard pBreakHoisted ∧
      ¬ DominatorAccepts pBreakHoisted ∧ ¬ ExactPhaseAccepts pBreakHoisted ∧
      ReachesUB pBreakHoisted [0, 1, 2, 3, 4, 5, 6] := by
  decide

/-- R3, positive control 2: with a write at the join, the exact-phase and dominator checkers
reject (writes are flagged under a live loan regardless of phase). -/
theorem pBreakWrite_rejected :
    ¬ DominatorAccepts pBreakWrite ∧ ¬ ExactPhaseAccepts pBreakWrite := by
  decide

/-! ## R4. The dominator test is also incomplete -/

/-- **R4 (counterexample).** `pJoin` (`R` dominates `A`) is safe and accepted by the exact-phase
checker but rejected by the dominator checker: the join `5` is reached from a path without `R`
(no loan) and from the reserved region (loan reserved, not active), so `R` does not strictly
dominate `5`. The write `6` executes with `r` active on the walk through `A`; on the two walks
that reach `6` without `A`, the write halts. -/
theorem pJoin_safe_exactPhaseAccepts_not_dominatorAccepts :
    Dom pJoin.edges pJoin.entry pJoin.R pJoin.A ∧ ¬ MaybeActive pJoin 5 ∧ IsActiveDom pJoin 5 ∧
      LoanLive pJoin 5 ∧ ExactPhaseAccepts pJoin ∧ ¬ DominatorAccepts pJoin ∧
      run pJoin RState.init [0, 1, 2, 3] = .ok ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ ∧
      run pJoin RState.init [0, 1, 2, 3, 6] = .ok ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ ∧
      run pJoin RState.init [0, 1, 5, 6] = .halt ∧
      run pJoin RState.init [0, 1, 2, 5, 6] = .halt ∧ Safe pJoin :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide,
    safe_of_cert (explore pJoin 12 [(pJoin.entry, RState.init)]) (by decide) (by decide)⟩

/-- R4 positive control (and R6 positive control): `pPush` (a read between `R` and `A`) is safe
and accepted by the exact-phase and dominator checkers. -/
theorem pPush_safe_accepted : Safe pPush ∧ ExactPhaseAccepts pPush ∧ DominatorAccepts pPush :=
  ⟨safe_pos, by decide, by decide⟩

/-! ## R5. Repairs compared by accepted sets -/

/-- **R5a (inclusion).** Every program accepted by repair (b) is accepted by the exact-phase
checker. -/
theorem repairBAccepts_exactPhaseAccepts (p : Prog n) (h : RepairBAccepts p) :
    ExactPhaseAccepts p := by
  apply accepts_of_phase_imp _ h
  intro L _ _ hL
  unfold guardedDomPhase
  split
  · next hg =>
    exact isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_noUnwind p
      hg.1 hg.2.1 hg.2.2 L hL
  · trivial

/-- **R5a (soundness).** Every program accepted by repair (b) is safe. -/
theorem repairBAccepts_safe (p : Prog n) (h : RepairBAccepts p) : Safe p :=
  exactPhaseAccepts_safe p (repairBAccepts_exactPhaseAccepts p h)

/-- R5a, tightness of `h`: `pBreak` is rejected by repair (b) and by the exact-phase checker, and
is unsafe. -/
theorem repairBAccepts_tight_pBreak :
    ¬ RepairBAccepts pBreak ∧ ¬ ExactPhaseAccepts pBreak ∧ ¬ Safe pBreak :=
  ⟨by decide, by decide, safe_neg⟩

/-- **R5c (inclusion, by construction).** Every program accepted by repair (c) is accepted by
repair (b): both use the same guard `DomGuard`. -/
theorem repairCAccepts_repairBAccepts (p : Prog n) (h : RepairCAccepts p) :
    RepairBAccepts p := by
  obtain ⟨hg, hd⟩ := h
  unfold RepairBAccepts
  have : guardedDomPhase p = IsActiveDom p := by
    funext L; unfold guardedDomPhase; simp [hg]
  rw [this]; exact hd

/-- R5c, tightness of `h` in `repairCAccepts_repairBAccepts`: `pJoin` is rejected by repair (c)
and by repair (b); it violates `ActivationStaysReachable` (the edge `2 → 5` leaves the reserved
region towards an exit), so `DomGuard` fails. -/
theorem repairCAccepts_tight_pJoin :
    ¬ RepairCAccepts pJoin ∧ ¬ RepairBAccepts pJoin ∧ ¬ ActivationStaysReachable pJoin ∧
      ¬ DomGuard pJoin := by
  decide

/-- **R5c (strictness).** Both inclusions repair (c) ⊆ repair (b) ⊆ exact-phase checker are
strict: `pJoin` is safe and accepted by the exact-phase checker but not by repair (b); the
`break`-in-argument program `pBreakDead`, in which `r` is dead at the join, is safe and accepted
by the exact-phase checker and by repair (b) but not by repair (c). -/
theorem repairs_strict :
    (Safe pJoin ∧ ExactPhaseAccepts pJoin ∧ ¬ RepairBAccepts pJoin) ∧
      (Safe pBreakDead ∧ ¬ LoanLive pBreakDead 4 ∧ ExactPhaseAccepts pBreakDead ∧
        RepairBAccepts pBreakDead ∧ ¬ RepairCAccepts pBreakDead) :=
  ⟨⟨pJoin_safe_exactPhaseAccepts_not_dominatorAccepts.2.2.2.2.2.2.2.2.2.2,
      pJoin_safe_exactPhaseAccepts_not_dominatorAccepts.2.2.2.2.1, by decide⟩,
    ⟨safe_of_cert (explore pBreakDead 12 [(pBreakDead.entry, RState.init)]) (by decide)
        (by decide), by decide, by decide, by decide, by decide⟩⟩

/-- **R5d (counterexample).** The literal repair (b), guarded by `A` post-dominating `R` (normal
edges) alone, accepts the unsafe `pLoopBack`. -/
theorem literalRepairB_unsound_pLoopBack :
    PDom pLoopBack.succ pLoopBack.A pLoopBack.R ∧ LiteralRepairBAccepts pLoopBack ∧
      ReachesUB pLoopBack [0, 1, 2, 3, 4, 5] := by
  decide

/-- R5d, positive control: the literal repair (b) rejects the early-exit program `pBreak`
(its guard fails there, so every loan counts as active). -/
theorem literalRepairB_rejects_pBreak :
    ¬ PDom pBreak.succ pBreak.A pBreak.R ∧ ¬ LiteralRepairBAccepts pBreak := by
  decide

/-! ## R6. Writes and shared reborrows during a reservation -/

/-- **R6b (counterexample).** In `pWriteDuringRes`, a write to `x` during the reservation is
followed by the activation; the walk `0, 1, 2, 3` reaches UB at the activation. The exact-phase
and dominator checkers flag the write, although neither phase test calls the loan active there.
-/
theorem pWriteDuringRes_ub_rejected :
    ¬ MaybeActive pWriteDuringRes 2 ∧ ¬ IsActiveDom pWriteDuringRes 2 ∧
      ReachesUB pWriteDuringRes [0, 1, 2, 3] ∧
      Flagged pWriteDuringRes (MaybeActive pWriteDuringRes) 2 ∧
      Flagged pWriteDuringRes (IsActiveDom pWriteDuringRes) 2 := by
  decide

/-- **R6c (counterexample).** In `pSharedDuringRes`, a shared reference created during the
reservation is used after the activation; the walk `0, 1, 2, 3, 4` reaches UB at the use. The
exact-phase and dominator checkers reject, and for each of them the flagged nodes are exactly
`A` (the activation check). -/
theorem pSharedDuringRes_ub_rejected :
    ¬ MaybeActive pSharedDuringRes 2 ∧ ReachesUB pSharedDuringRes [0, 1, 2, 3, 4] ∧
      (∀ L : Fin 5, Flagged pSharedDuringRes (MaybeActive pSharedDuringRes) L ↔
        L = pSharedDuringRes.A) ∧
      (∀ L : Fin 5, Flagged pSharedDuringRes (IsActiveDom pSharedDuringRes) L ↔
        L = pSharedDuringRes.A) := by
  decide

/-! ## R7. Unwinding edges -/

/-- **R7a.** With unwinding edges allowed: if `ReentryFree` and `ActivationStaysReachable` hold
(normal edges), then at every node `L` that is not a cleanup node and where the loan may be
active, the dominator test (dominance over all edges) calls the loan active. -/
theorem isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_not_isCleanup
    (p : Prog n) (hre : ReentryFree p) (hasr : ActivationStaysReachable p) (L : Fin n)
    (hnc : ¬ IsCleanup p L) (hL : MaybeActive p L) : IsActiveDom p L :=
  isActiveDom_of_maybeActive_of_succWalks p hre hasr L (isWalk_succ_of_not_isCleanup hnc) hL

/-- R7a, tightness of `hL`: `pCleanupRead` (with unwinding edges) at node `2`. -/
theorem maybeActive_tight_pCleanupRead :
    ¬ NoUnwind pCleanupRead ∧ ReentryFree pCleanupRead ∧ ActivationStaysReachable pCleanupRead ∧
      ¬ IsCleanup pCleanupRead 2 ∧ ¬ MaybeActive pCleanupRead 2 ∧
      ¬ IsActiveDom pCleanupRead 2 := by
  decide

/-- R7a, non-vacuity: `pCleanupRead` has unwinding edges and satisfies all hypotheses at node
`4`. -/
theorem notCleanup_hypotheses_hold_pCleanupRead :
    ¬ NoUnwind pCleanupRead ∧ ReentryFree pCleanupRead ∧ ActivationStaysReachable pCleanupRead ∧
      ¬ IsCleanup pCleanupRead 4 ∧ MaybeActive pCleanupRead 4 := by
  decide

/-- **R7b (counterexample).** `pCleanup` satisfies `ReentryFree` and `ActivationStaysReachable`
but its cleanup block reads `x` while `r` is live; there the dominator test calls the loan
reserved, the dominator checker accepts, and a run reaches UB. -/
theorem pCleanup_dominatorAccepts_unsafe :
    ReentryFree pCleanup ∧ ActivationStaysReachable pCleanup ∧
      ¬ CleanupReadsUnderDeadLoan pCleanup ∧ (pCleanup.op 6).isRead = true ∧
      LoanLive pCleanup 6 ∧ MaybeActive pCleanup 6 ∧ ¬ IsActiveDom pCleanup 6 ∧
      DominatorAccepts pCleanup ∧ ReachesUB pCleanup [0, 1, 2, 3, 4, 6, 7] := by
  decide

/-- R7b positive control (and R7c non-vacuity): `pCleanupRead` has unwinding edges, satisfies
`ReentryFree`, `ActivationStaysReachable` and `CleanupReadsUnderDeadLoan`, is accepted by the
dominator checker (including its read during the reservation at node `2`), and is safe. -/
theorem pCleanupRead_hypotheses_hold_safe :
    ¬ NoUnwind pCleanupRead ∧ ReentryFree pCleanupRead ∧ ActivationStaysReachable pCleanupRead ∧
      CleanupReadsUnderDeadLoan pCleanupRead ∧ DominatorAccepts pCleanupRead ∧
      LoanLive pCleanupRead 2 ∧ Safe pCleanupRead :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    safe_of_cert (explore pCleanupRead 12 [(pCleanupRead.entry, RState.init)]) (by decide)
      (by decide)⟩

/-- **R7c.** With unwinding edges allowed: under `ReentryFree` and `ActivationStaysReachable`
(normal edges), if no cleanup node reads `x` while `r` is live, every program accepted by the
dominator checker is safe. -/
theorem dominatorAccepts_safe_of_reentryFree_activationStaysReachable_cleanupReadsUnderDeadLoan
    (p : Prog n) (hre : ReentryFree p) (hasr : ActivationStaysReachable p)
    (hcl : CleanupReadsUnderDeadLoan p) (h : DominatorAccepts p) : Safe p :=
  exactPhaseAccepts_safe p (accepts_of_phase_imp
    (fun L hr hl hL =>
      isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_not_isCleanup
        p hre hasr L (not_isCleanup_of_cleanupReadsUnderDeadLoan hcl hr hl) hL) h)

end Toy.TwoPhase
