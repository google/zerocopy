import ToyTwoPhase.Programs

/-!
# Definition examples (positive and negative), all proved by `decide` or `rfl`
-/

namespace Toy.TwoPhase

/-! ### Degenerate sizes -/
/-- There is no program with zero nodes (`entry : Fin 0`). -/
theorem prog_zero_uninhabited (p : Prog 0) : False := p.entry.elim0
/-- There is no program with one node (`R ≠ A` needs two nodes). -/
theorem prog_one_uninhabited (p : Prog 1) : False :=
  p.hRA (Fin.ext (by have := p.R.isLt; have := p.A.isLt; omega))

/-! ### Walks and `PathVia` -/
theorem isWalk_pos : IsWalk pPush.edges [0, 1, 2, 3, 4] := by decide
theorem isWalk_neg : ¬ IsWalk pPush.edges [0, 2] := by decide
theorem pathVia_pos : PathVia pBreak.edges (fun x => x != 3) 0 4 := by decide
theorem pathVia_neg : ¬ PathVia pPush.edges (fun x => x != 3) 0 4 := by decide

/-! ### Dominance, post-dominance, acyclicity -/
/-- `R` dominates `A` in `pBreak`. -/
theorem dom_pos : Dom pBreak.edges pBreak.entry pBreak.R pBreak.A := by decide
/-- `A` does not dominate the join `4` in `pBreak` (the `break` walk `0,1,2,4`). -/
theorem dom_neg : ¬ Dom pBreak.edges pBreak.entry pBreak.A 4 := by decide
/-- Unreachable nodes are dominated by every node (here node `4` of `pJoin`). -/
theorem dom_unreachable : Dom pJoin.edges pJoin.entry 6 4 := by decide
theorem pdom_pos : PDom pPush.succ pPush.A pPush.R := by decide
/-- `A` does not post-dominate `R` in `pBreak` (the walk `1,2,4,5,6,7`). -/
theorem pdom_neg : ¬ PDom pBreak.succ pBreak.A pBreak.R := by decide
theorem acyclic_pos : Acyclic pBreak.succ := by decide
theorem acyclic_neg : ¬ Acyclic pLoop1.succ := by decide

/-! ### Phase and liveness -/
/-- At the join of `pBreak` the loan may be active (walk `0,1,2,3,4`). -/
theorem maybeActive_pos : MaybeActive pBreak 4 := by decide
/-- Between `R` and `A` in `pPush` the loan is never active. -/
theorem maybeActive_neg : ¬ MaybeActive pPush 2 := by decide
/-- After `endLoan` the loan is not active (`pEndThenRead`, node `4`). -/
theorem maybeActive_neg_endLoan : ¬ MaybeActive pEndThenRead 4 := by decide
/-- `MaybeActive` is a path fact, not a semantic one: in the straight-line `pEndBeforeA` it holds
at node `4`, while running the walk `0, 1, 2, 3` (the program is a single path) ends in the
initial state, whose permission is `none`. -/
theorem maybeActive_pEndBeforeA_run_init :
    MaybeActive pEndBeforeA 4 ∧ run pEndBeforeA RState.init [0, 1, 2, 3] = .ok RState.init := by
  decide
/-- `MaybeActive` is an in-fact: in `pLoopOK` it holds at `R` (reached from `A` through `4`) and
fails at `A` (every walk from `A` back to `A` passes the kill `R`). -/
theorem maybeActive_in_fact_pLoopOK :
    MaybeActive pLoopOK pLoopOK.R ∧ ¬ MaybeActive pLoopOK pLoopOK.A := by
  decide
theorem loanLive_pos : LoanLive pBreak 4 := by decide
/-- After the last use of `r` the loan is dead. -/
theorem loanLive_neg : ¬ LoanLive pBreak 7 := by decide
/-- `R` itself is never a live point: passing `R` ends the previous loan. -/
theorem loanLive_neg_at_R : ¬ LoanLive pLoopOK pLoopOK.R := by decide
theorem sharedLive_pos : SharedLive pSharedDuringRes .s0 pSharedDuringRes.A := by decide
/-- In `pBreak`, `s0` is re-created after `A` before its uses, so it is not live at `A`. -/
theorem sharedLive_neg : ¬ SharedLive pBreak .s0 pBreak.A := by decide
theorem isActiveDom_pos : IsActiveDom pPush 4 := by decide
theorem isActiveDom_neg : ¬ IsActiveDom pPush 2 := by decide

/-! ### CFG conditions -/
theorem noUnwind_pos : NoUnwind pBreak := by decide
theorem noUnwind_neg : ¬ NoUnwind pCleanup := by decide
theorem reentryFree_pos : ReentryFree pLoopOK := by decide
theorem reentryFree_neg : ¬ ReentryFree pLoop1 := by decide
theorem activationStaysReachable_pos : ActivationStaysReachable pLoopOK := by decide
/-- A loop between `R` and `A` from which `A` stays reachable is admitted. -/
theorem activationStaysReachable_pos_argLoop : ActivationStaysReachable pArgLoop := by decide
/-- A `continue` back to `R` from a region node that can also reach `A` without passing `R` is
admitted. -/
theorem activationStaysReachable_pos_continue : ActivationStaysReachable pContinue := by decide
/-- Early exit to an exit node. -/
theorem activationStaysReachable_neg_exit : ¬ ActivationStaysReachable pBreak := by decide
/-- Early exit to a node whose every normal walk to `A` passes `R` (node `4` of `pLoopBack`). -/
theorem activationStaysReachable_neg_loopBack : ¬ ActivationStaysReachable pLoopBack := by
  decide
/-- Early exit into a cycle from which `A` is unreachable. -/
theorem activationStaysReachable_neg_diverge : ¬ ActivationStaysReachable pDiverge := by decide
/-- `pJoin`: the join `5`, reached from `R` and not dominated by `R`, is ignored. -/
theorem domRegionReachesA_pos : DomRegionReachesA pJoin := by decide
/-- `pBreak`: the join `4` is reached from `R`, is dominated by `R`, and cannot reach `A`. -/
theorem domRegionReachesA_neg : ¬ DomRegionReachesA pBreak := by decide
theorem isCleanup_pos : IsCleanup pCleanup 6 := by decide
theorem isCleanup_neg : ¬ IsCleanup pCleanup 5 := by decide
theorem cleanupReadsUnderDeadLoan_pos : CleanupReadsUnderDeadLoan pCleanupRead := by decide
theorem cleanupReadsUnderDeadLoan_neg : ¬ CleanupReadsUnderDeadLoan pCleanup := by decide
theorem domGuard_pos : DomGuard pLoopOK := by decide
theorem domGuard_pos_argLoop : DomGuard pArgLoop := by decide
theorem domGuard_pos_continue : DomGuard pContinue := by decide
theorem domGuard_neg : ¬ DomGuard pBreak := by decide

/-! ### Reference semantics -/
theorem safe_pos : Safe pPush :=
  safe_of_cert (explore pPush 12 [(pPush.entry, RState.init)]) (by decide) (by decide)
theorem safe_neg : ¬ Safe pBreak :=
  not_safe_of_reachesUB (π := [0, 1, 2, 3, 4, 5, 6]) (by decide)
/-- A write through a reserved (not yet activated) `r` halts safely. -/
theorem run_halt_reserved_writeThrough : run pBreak RState.init [0, 1, 2, 4, 5, 6] = .halt := by
  decide
/-- The activation marks a created shared reference dirty: in `pSharedDuringRes`, after `R`,
`borrowShared s0` and `A`, the state has `r` active and `s0` dirty. -/
theorem run_activate_marks_shared_dirty :
    run pSharedDuringRes RState.init [0, 1, 2, 3] = .ok ⟨.active, ⟨true, true⟩, ⟨false, false⟩⟩ := by
  decide

/-- Property of `exec`: while `r` is reserved, foreign reads (`readX`, creating a shared
reference, using a clean shared reference) cause no UB and leave `r` reserved. -/
theorem exec_foreignRead_of_reserved (σ : RState) (h : σ.perm = .reserved) :
    exec .readX σ = .ok σ ∧
      (∀ s, exec (.borrowShared s) σ = .ok (σ.setSh s ⟨true, false⟩)) ∧
      (∀ s, (σ.sh s).dirty = false → exec (.useShared s) σ = .ok σ) := by
  obtain ⟨perm, sh0, sh1⟩ := σ
  simp only at h
  subst h
  refine ⟨rfl, ?_, ?_⟩
  · intro s; cases s <;> rfl
  · intro s hs; cases s <;> simp_all [exec, RState.sh, foreignRead]

/-- `exec_foreignRead_of_reserved`, non-vacuity: running `pPush` through `R` (walk `0, 1`)
reaches a state in which `r` is reserved. -/
theorem exec_foreignRead_of_reserved_hypotheses_hold_pPush :
    ∃ σ : RState, run pPush RState.init [0, 1] = .ok σ ∧ σ.perm = .reserved :=
  ⟨⟨.reserved, ⟨false, false⟩, ⟨false, false⟩⟩, by decide, rfl⟩

/-- `exec_foreignRead_of_reserved`, tightness of `h`: in an `active` state a direct read freezes
`r` (the state changes). -/
theorem exec_readX_active_freezes :
    (⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ : RState).perm ≠ .reserved ∧
    exec .readX ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ =
      .ok ⟨.frozen, ⟨false, false⟩, ⟨false, false⟩⟩ ∧
    exec .readX ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ ≠
      .ok ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ := by
  decide

/-! ### Checkers and the analysis -/
theorem dominatorAccepts_pos : DominatorAccepts pPush := by decide
theorem dominatorAccepts_neg : ¬ DominatorAccepts pBreakHoisted := by decide
theorem exactPhaseAccepts_pos : ExactPhaseAccepts pPush := by decide
theorem exactPhaseAccepts_neg : ¬ ExactPhaseAccepts pBreak := by decide
theorem iterDataflowAccepts_pos : IterDataflowAccepts pPush := by decide
theorem iterDataflowAccepts_neg : ¬ IterDataflowAccepts pBreak := by decide
/-- With two-phase treatment removed, `pBreakDead` (no read under a live loan) is still
accepted. -/
theorem alwaysActiveAccepts_pos : AlwaysActiveAccepts pBreakDead := by decide
/-- Without two-phase borrows, `v.push(v.len())` is rejected. -/
theorem alwaysActiveAccepts_neg : ¬ AlwaysActiveAccepts pPush := by decide
theorem dfMaybeActive_pos : dfMaybeActive pBreak 4 = true := by decide
theorem dfMaybeActive_neg : dfMaybeActive pBreak 2 = false := by decide
theorem repairBAccepts_pos : RepairBAccepts pLoopOK := by decide
/-- Repair (b) falls back to "always active" when `DomGuard` fails; `pBreakDead` is still
accepted. -/
theorem repairBAccepts_pos_noGuard : ¬ DomGuard pBreakDead ∧ RepairBAccepts pBreakDead := by
  decide
theorem repairBAccepts_neg : ¬ RepairBAccepts pBreak := by decide
theorem repairCAccepts_pos : RepairCAccepts pLoopOK := by decide
theorem repairCAccepts_pos_argLoop : RepairCAccepts pArgLoop := by decide
theorem repairCAccepts_neg : ¬ RepairCAccepts pBreakDead := by decide

end Toy.TwoPhase
