import ToyLoanFlow.Results

/-!
# Positive and negative examples for the definitions
-/

namespace Toy.LoanFlow

/-! ## `Conflicts` -/

/-- The write to `x` at node `3` of `pc3` conflicts with the mutable loan of `x` created at
node `0`. -/
example : Conflicts pc3 0 3 := by decide
/-- Returning `r` (node `2`) reads `r`, not `x`: no conflict with the loan of `x`. -/
example : ¬ Conflicts pc3 0 2 := by decide
/-- Node `2` of `pc3` creates no loan, so nothing conflicts with it. -/
example : ¬ Conflicts pc3 2 3 := by decide
/-- The write to `y` at node `4` of `pVariance` conflicts with the shared loan of `y` created at
node `2`. -/
example : Conflicts pVariance 2 4 := by decide

/-! ## `LiveAt` -/

/-- `r` is live at the branch of `pc3` (it may be returned). -/
example : LiveAt pc3 1 1 := .step (q' := 2) (by decide) (by decide) (.use (by decide))
/-- `r` is dead at the insertion of `pc3`. -/
example : ¬ LiveAt pc3 1 3 := fun h => by
  have := mem_of_liveAt (L := liveList pc3) (by decide) h
  revert this; decide
/-- `r` is dead on entry to the node of `pReassign` that overwrites it. -/
example : ¬ LiveAt pReassign 2 2 := fun h => by
  have := mem_of_liveAt (L := liveList pReassign) (by decide) h
  revert this; decide

/-! ## `killsAt` -/

example : killsAt .overwrite pReassign 2 2 = true := by decide
/-- The checker's kill rule does not drop the source of a copy. -/
example : killsAt .overwrite pCopyThenUse 1 1 = false := by decide
/-- The unsound ablation drops the source of a copy. -/
example : killsAt .overwriteAndCopySrc pCopyThenUse 1 1 = true := by decide
example : killsAt .none pReassign 2 2 = false := by decide

/-! ## `invariantAt` and `gen` -/

example : invariantAt .inv [.mut, .shr] 1 = true := by decide
example : invariantAt .inv [.shr, .shr] 1 = false := by decide
example : invariantAt .inv [.mut, .shr] 0 = false := by decide
example : invariantAt .cov [.mut, .shr] 1 = false := by decide
/-- `pp := &mut c` with `c : &D` relates `c`'s origin and `pp`'s inner origin both ways. -/
example : gen .inv pVariance 1 = [((2, 0), (3, 1)), ((3, 1), (2, 0))] := by decide
/-- The covariant ablation keeps one direction. -/
example : gen .cov pVariance 1 = [((2, 0), (3, 1))] := by decide
/-- `*pp := s` lets `s`'s loans flow into `pp`'s inner origin. -/
example : gen .inv pVariance 3 = [((4, 0), (3, 1))] := by decide
/-- A borrow of plain data generates no constraint. -/
example : gen .inv pc3 0 = [] := by decide

/-! ## `LS.Holds`, `LS.SubAt` and `LS.LoanLive` -/

/-- The loan of `pc3` created at node `0` may be in `r`'s origin after the branch (node `1`),
whose successors include the insertion (node `3`) … -/
example : LS.Holds .overwrite .inv pc3 0 (1, 0) 1 :=
  .carry (q := 0) (.intro rfl) (by decide) (by decide)
/-- … but it is not live there. -/
example : ¬ LS.LoanLive .overwrite .inv pc3 0 3 := pc3_ls_loan0_not_live_at_3
/-- The kill at node `2` of `pReassign` drops the first loan from `r`'s origin. -/
example : ¬ LS.Holds .overwrite .inv pReassign 0 (2, 0) 2 := fun h => by
  have := mem_of_holds (L := liveList pReassign) (T := subList .inv pReassign)
    (S := lsList .overwrite .inv pReassign) (by decide) (by decide) (by decide) h
  revert this; decide
/-- Without kills it stays. -/
example : LS.Holds .none .inv pReassign 0 (2, 0) 2 :=
  .carry (q := 1) (.carry (q := 0) (.intro rfl) (by decide) rfl) (by decide) rfl
/-- A loan copied into `s` stays live through `r` while `r` is used later. -/
example : LS.LoanLive .overwrite .inv pCopyThenUse 0 2 :=
  ⟨(1, 0), 1, .carry (q := 0) (.intro rfl) (by decide) (by decide), by decide,
    .step (q' := 3) (by decide) (by decide) (.use (by decide))⟩
/-- `pp := &mut c` relates `c`'s origin and `pp`'s inner origin while both are live. -/
example : LS.SubAt .inv pVariance (3, 1) (2, 0) 1 := .base (by decide)
/-- In `pVariance`, `pp` is dead after the store, so the relation does not persist to node `4`. -/
example : ¬ LS.SubAt .inv pVariance (3, 1) (2, 0) 4 := fun h => by
  have := mem_of_subAt (L := liveList pVariance) (T := subList .inv pVariance)
    (by decide) (by decide) h
  revert this; decide

/-! ## `LS.LiveHolds`, `LS.LiveLoanLive` and `LS.LiveAccepts` -/

/-- In the liveness-gated variant the first loan of `pReassign` may be in `r`'s origin after
node `1`, where `r` is live … -/
example : LS.LiveHolds .inv pReassign 0 (2, 0) 1 :=
  .carry (q := 0) (.intro rfl) (by decide) (.use (by decide))
/-- … and it is not carried into node `2`, where `r` is dead. -/
example : ¬ LS.LiveHolds .inv pReassign 0 (2, 0) 2 := fun h => by
  have := mem_of_holds (L := liveList pReassign) (T := subList .inv pReassign)
    (S := lsList .overwrite .inv pReassign) (by decide) (by decide) (by decide)
    (Incl.holds_of_liveHolds h)
  revert this; decide
/-- The loan copied into `s` in `pCopyThenUse` is live at the write to `x`. -/
example : LS.LiveLoanLive .inv pCopyThenUse 0 2 :=
  (lsLoanLive_overwrite_iff_liveLoanLive .inv pCopyThenUse 0 2).1
    ⟨(1, 0), 1, .carry (q := 0) (.intro rfl) (by decide) (by decide), by decide,
      .step (q' := 3) (by decide) (by decide) (.use (by decide))⟩
example : LS.LiveAccepts .inv pReassign :=
  (lsAccepts_overwrite_iff_liveAccepts .inv pReassign).1 pReassign_lsAccepts
example : ¬ LS.LiveAccepts .inv pCopyThenUse := fun h =>
  pCopyThenUse_not_lsAccepts ((lsAccepts_overwrite_iff_liveAccepts .inv pCopyThenUse).2 h)

/-! ## `NLL.InRegion` and `NLL.InScope` -/

/-- The returned local's origin contains every node. -/
example : NLL.InRegion .inv pc3 (1, 0) 3 := .universal (b := 2) rfl
/-- `r`'s region in `pReassign` omits the node that overwrites `r`. -/
example : ¬ NLL.InRegion .inv pReassign (2, 0) 2 := fun h => by
  have := mem_of_inRegion (L := liveList pReassign) (G := regionList .inv pReassign)
    (by decide) (by decide) h
  revert this; decide
example : NLL.InScope .inv pc3 0 3 := pc3_nll_loan0_inScope_at_3
/-- The first loan of `pReassign` leaves scope at the gap in `r`'s region. -/
example : ¬ NLL.InScope .inv pReassign 0 3 := fun h => by
  have := mem_of_inScope (L := liveList pReassign) (G := regionList .inv pReassign)
    (W := scopeList .inv pReassign) (by decide) (by decide) (by decide) h
  revert this; decide

/-! ## `Acyclic`, `WellTyped`, `Safe`, and the two checkers -/

example : Acyclic pc3 := pc3_acyclic
example : ¬ Acyclic pc3Loop := pc3Loop_not_acyclic
example : WellTyped pVariance := pVariance_wellTyped
example : ¬ WellTyped pUntypedStore := pUntypedStore_not_wellTyped
example : Safe pc3Loop := pc3Loop_safe
example : ¬ Safe pVariance := pVariance_not_safe
example : LSAccepts pc3 := pc3_lsAccepts
example : ¬ LSAccepts pCopyThenUse := pCopyThenUse_not_lsAccepts
example : NLLAccepts pReassign := pReassign_nllAccepts
example : ¬ NLLAccepts pc3 := pc3_not_nllAccepts

end Toy.LoanFlow
