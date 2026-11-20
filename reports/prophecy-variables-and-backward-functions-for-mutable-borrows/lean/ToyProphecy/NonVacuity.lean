import ToyProphecy.Examples

/-!
# Non-vacuity witnesses for the main statements

`richProg` exercises every construct of the language: a borrow selected at run
time, two levels of nested reborrows, a call returning a reborrow two levels below
its argument, writes after a reborrow has ended, and a read of the lender after
the end. It obeys every part of the discipline.
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-- `r0 = if x2 ≠ 0 { &mut x0 } else { &mut x1 }; r1 = &mut *r0; *r1 = *r1 + 1;
r2 = &mut *r1; *r2 = *r2 + 10; end r2; end r1; r3 = deep(&mut *r0);
*r3 = *r3 + 100; end r3; *r0 = *r0 + 1000; end r0; x2 = x0`. -/
def richProg : Prog :=
  [op (borrowSel 0 (var 2) 0 1), op (reborrow 1 0), op (write 1 (add (deref 1) (lit 1))),
   op (reborrow 2 1), op (write 2 (add (deref 2) (lit 10))), op (endBorrow 2), op (endBorrow 1),
   call 3 deepCallee 0, op (write 3 (add (deref 3) (lit 100))), op (endBorrow 3),
   op (write 0 (add (deref 0) (lit 1000))), op (endBorrow 0), op (assign 2 (var 0))]

/-- **Non-vacuity of the main statements.** `richProg` satisfies all five parts
of the discipline; from the store `x ↦ x` (so `x2 = 2` selects `x0`) the
reference semantics and the backward-function translation both end with
`(x0, x1, x2) = (1116, 1, 1116)`, and the prophecy translation admits a store with
these values. -/
theorem richProg_nonvacuous :
    NoLentAccess richProg ∧ NoFrozenAccess richProg ∧ NoUseAfterEnd richProg ∧
    FreshBindings richProg ∧ AllEndedAtExit richProg ∧
    (refSem richProg idStore).map (fun σ => (σ 0, σ 1, σ 2)) = some (1116, 1, 1116) ∧
    (backSem richProg idStore).map (fun σ => (σ 0, σ 1, σ 2)) = some (1116, 1, 1116) ∧
    ∃ σ', ProphOutcome richProg idStore σ' ∧ σ' 0 = 1116 ∧ σ' 1 = 1 ∧ σ' 2 = 1116 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   _, ⟨phiOf [1116, 11, 11, 116, 13, 116, 116], _, rfl, by decide, rfl⟩, rfl, rfl, rfl⟩

/-- The same program from the zero store (so `x2 = 0` selects `x1`). -/
theorem richProg_nonvacuous_other_branch :
    (refSem richProg zeroStore).map (fun σ => (σ 0, σ 1, σ 2)) = some (0, 1116, 0) ∧
    (backSem richProg zeroStore).map (fun σ => (σ 0, σ 1, σ 2)) = some (0, 1116, 0) := by
  decide

/-- **Non-vacuity of the inclusion statement, within and beyond the full
discipline.** `richProg` satisfies the four hypotheses of
`prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`
(and `AllEndedAtExit`); `cxUnended` (a borrow never ended) satisfies the four
hypotheses but not `AllEndedAtExit`. For both, the reference semantics produces a
store and the prophecy translation admits it. -/
theorem inclusion_nonvacuous :
    (NoLentAccess richProg ∧ NoFrozenAccess richProg ∧ NoUseAfterEnd richProg ∧
      FreshBindings richProg ∧ AllEndedAtExit richProg ∧
      ∃ σ', refSem richProg idStore = some σ' ∧ ProphOutcome richProg idStore σ') ∧
    (NoLentAccess cxUnended ∧ NoFrozenAccess cxUnended ∧ NoUseAfterEnd cxUnended ∧
      FreshBindings cxUnended ∧ ¬ AllEndedAtExit cxUnended ∧
      ∃ σ', refSem cxUnended zeroStore = some σ' ∧ ProphOutcome cxUnended zeroStore σ') := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩⟩
  · refine ⟨_, rfl, phiOf [1116, 11, 11, 116, 13, 116, 116], _, rfl, by decide, ?_⟩
    funext y
    rcases y with _ | _ | _ | y
    · decide
    · decide
    · decide
    · rfl
  · refine ⟨_, rfl, phiOf [5], _, rfl, by decide, ?_⟩
    funext y
    rcases y with _ | y
    · decide
    · rfl

/-- **Non-vacuity of the omission statement, within and beyond the full
discipline.** With `r = 0`: `writeThenRead` satisfies the four hypotheses of
`prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`
(and `AllEndedAtExit`), and `cxUnended` satisfies them but not
`AllEndedAtExit`; for both, the real outcome is admitted when the resolution of
`r0` is omitted. -/
theorem omission_keeps_real_nonvacuous :
    (NoLentAccess writeThenRead ∧ NoFrozenAccess writeThenRead ∧ NoUseAfterEnd writeThenRead ∧
      FreshBindings writeThenRead ∧ AllEndedAtExit writeThenRead ∧
      ∃ σ', refSem writeThenRead zeroStore = some σ' ∧
        ProphOutcomeWith (ResPolicy.omitAtEnd 0) writeThenRead zeroStore σ') ∧
    (NoLentAccess cxUnended ∧ NoFrozenAccess cxUnended ∧ NoUseAfterEnd cxUnended ∧
      FreshBindings cxUnended ∧ ¬ AllEndedAtExit cxUnended ∧
      ∃ σ', refSem cxUnended zeroStore = some σ' ∧
        ProphOutcomeWith (ResPolicy.omitAtEnd 0) cxUnended zeroStore σ') := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide,
      _, refSem_writeThenRead, omitting_resolution_keeps_real_store_writeThenRead⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩⟩
  refine ⟨_, rfl, phiOf [5], _, rfl, by decide, ?_⟩
  funext y
  rcases y with _ | y
  · decide
  · rfl

/-- Outside the hypotheses of the inclusion statement: `cxRebind`
(`r0 = &mut x0; *r0 = 5; r0 = &mut x1; end r0`, which leaks the first borrow of
`r0`) violates only `FreshBindings`, and its real outcome is still admitted (its
leaked prophecy is free). This is an example, not a general claim. -/
theorem cxRebind_real_outcome_admitted :
    violations cxRebind = [.rebind] ∧
    ∃ σ', refSem cxRebind zeroStore = some σ' ∧ ProphOutcome cxRebind zeroStore σ' := by
  refine ⟨by decide, _, rfl, phiOf [5, 0], _, rfl, by decide, ?_⟩
  funext y
  rcases y with _ | _ | y
  · decide
  · decide
  · rfl

end Toy.Prophecy
