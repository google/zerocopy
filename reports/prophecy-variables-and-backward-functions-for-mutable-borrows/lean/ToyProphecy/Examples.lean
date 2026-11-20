import ToyProphecy.Selection

/-!
# Positive and negative examples for the definitions

Each core definition gets at least one intended instance it admits and one it
rejects (or one behaviour it must exhibit and one it must not). Further examples
live next to the results: `prophOutcome_writeThenRead_iff`,
`omitting_resolution_admits_unproducible_store`, `deepCallee_nonvacuous`, the
`cx*_violations` facts, and `selIncr_*`.
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-! ## Stores and point updates -/

/-- `Store.set` writes the named local. -/
theorem store_set_pos : (zeroStore.set 0 5) 0 = 5 := by decide
/-- `Store.set` leaves every other local unchanged. -/
theorem store_set_neg : (zeroStore.set 0 5) 1 = 0 := by decide
/-- `fupd` updates the named entry. -/
theorem fupd_pos : fupd (fun _ => (0 : Int)) 3 7 3 = 7 := by decide
/-- `fupd` leaves other entries unchanged. -/
theorem fupd_neg : fupd (fun _ => (0 : Int)) 3 7 4 = 0 := by decide

/-! ## Reference semantics -/

/-- Writes through nested reborrows reach the lender (`0 + 1 + 10 + 100`). -/
theorem refSem_pos_nested : (refSem nestedReborrows zeroStore).map (· 0) = some 111 := by decide
/-- Writes through a borrow update the lender immediately, before the borrow ends
(lifetimes are erased at run time). -/
theorem refSem_pos_in_place :
    (refSem [op (borrow 0 0), op (write 0 (lit 5))] zeroStore).map (· 0) = some 5 := by decide
/-- Using a never-bound reference variable is stuck. -/
theorem refSem_neg_unbound : refSem [op (write 0 (lit 1))] zeroStore = none := by decide
/-- A local operation inside a callee body is stuck. -/
theorem refSem_neg_callee_local :
    refSem [op (borrow 0 0), call 1 cxCalleeLocal 0] zeroStore = none := by decide

/-! ## Backward-function translation -/

/-- Backward functions compose through nested reborrows. -/
theorem backSem_pos_nested : (backSem nestedReborrows zeroStore).map (· 0) = some 111 := by decide
/-- Backward summaries compose across a call returning a reborrow. -/
theorem backSem_pos_call :
    (backSem callDeep idStore).map (fun σ => (σ 0, σ 1)) = some (15, 15) := by decide
/-- The lender is not updated before the borrow ends (contrast `refSem_pos_in_place`). -/
theorem backSem_neg_not_in_place :
    (backSem [op (borrow 0 0), op (write 0 (lit 5))] zeroStore).map (· 0) = some 0 := by decide
/-- Using a never-bound reference variable is stuck. -/
theorem backSem_neg_unbound : backSem [op (write 0 (lit 1))] zeroStore = none := by decide

/-- `applyBack` performs a local assignment. -/
theorem applyBack_pos :
    (applyBack (BState.init zeroStore) [(.loc 0, 5)]).map (·.store 0) = some 5 := by decide
/-- `applyBack` is stuck when the target borrow is unbound. -/
theorem applyBack_neg :
    (applyBack (BState.init zeroStore) [(.ref 3, 5)]).map (·.store 0) = none := by decide

/-- `selBack` gives the final value to the chosen lender, also in the degenerate
case `x = y` (the chosen lender is written last). -/
theorem selBack_pos_degenerate :
    (applyBack (BState.init idStore) (selBack true 0 0 0 0 5)).map (·.store 0) = some 5 := by decide
/-- `selBack false` does not give the final value to `x`. -/
theorem selBack_neg :
    (applyBack (BState.init idStore) (selBack false 0 1 0 1 5)).map (fun s => (s.store 0, s.store 1))
      = some (0, 5) := by decide

/-- Forward value of `incCallee` at argument `4`. -/
theorem calleeFwd_pos : calleeFwd incCallee 4 = some 5 := by decide
/-- A stuck callee has no forward value. -/
theorem calleeFwd_neg : calleeFwd cxCalleeLocal 4 = none := by decide
/-- The backward function of `deepCallee` returns the returned borrow's final value. -/
theorem calleeBack_pos : calleeBack deepCallee 4 20 = 20 := by decide
/-- The partial backward function of a callee whose parent chain is a cycle is undefined. -/
theorem calleeBack_neg : calleeBack? cxCalleeRebind 0 5 = none := by decide

/-! ## Prophecy translation -/

theorem sat_pos : Sat [(1, 1), (2, 2)] := by decide
theorem sat_neg : ¬ Sat [(1, 1), (1, 2)] := by decide

/-- The standard policy emits one resolution for `writeOnce`. -/
theorem std_pos :
    (runP ResPolicy.std (phiOf [5]) 0 (PState.init zeroStore) writeOnce).map (·.cs) =
      some [(5, 5)] := by decide
/-- Omitting `r0`'s resolution emits none for `writeOnce`. -/
theorem omitAtEnd_pos :
    (runP (ResPolicy.omitAtEnd 0) (phiOf [5]) 0 (PState.init zeroStore) writeOnce).map (·.cs) =
      some [] := by decide
/-- Omitting the resolution of a different name changes nothing for `writeOnce`. -/
theorem omitAtEnd_neg :
    (runP (ResPolicy.omitAtEnd 1) (phiOf [5]) 0 (PState.init zeroStore) writeOnce).map (·.cs) =
      some [(5, 5)] := by decide
/-- Resolving after statement `0` uses the current value at that point. -/
theorem resolveAfter_pos :
    (runP (ResPolicy.resolveAfter 0 0) (phiOf [5]) 0 (PState.init zeroStore) writeOnce).map (·.cs) =
      some [(0, 5)] := by decide
/-- Resolving after statement `1` uses the value after the write. -/
theorem resolveAfter_neg :
    (runP (ResPolicy.resolveAfter 1 0) (phiOf [5]) 0 (PState.init zeroStore) writeOnce).map (·.cs) =
      some [(5, 5)] := by decide
/-- Callee-exit resolution: `deepCallee` emits one constraint inside its body and
two at exit (parameter and intermediate reborrow; the ended reborrow is not
resolved again, the returned one is left to the caller). -/
theorem calleeExit_pos :
    (calleeRunP true (phiOf [6, 20, 20]) deepCallee 4 20 0).map (·.cs) =
      some [(6, 6), (20, 20), (20, 20)] := by decide
/-- Without callee-exit resolution only the in-body constraint remains. -/
theorem calleeExit_neg :
    (calleeRunP false (phiOf [6, 20, 20]) deepCallee 4 20 0).map (·.cs) = some [(6, 6)] := by
  decide

/-- `ProphOutcome` admits the program's outcome. -/
theorem prophOutcome_pos : ProphOutcome writeThenRead zeroStore writeThenReadOut :=
  (prophOutcome_writeThenRead_iff _).2 refSem_writeThenRead
/-- `ProphOutcome` rejects a store the program does not produce. -/
theorem prophOutcome_neg : ¬ ProphOutcome writeThenRead zeroStore zeroStore := by
  intro h
  have := (prophOutcome_writeThenRead_iff _).1 h
  rw [refSem_writeThenRead] at this
  have h0 := congrArg (Option.map (· 0)) this
  revert h0
  decide

/-- `ProphContract` of `incCallee`: current `5` from argument `4`, argument
prophecy equal to the returned borrow's prophecy. -/
theorem prophContract_pos : ProphContract incCallee 4 5 9 9 :=
  ⟨phiOf [], _, rfl, by decide, _, rfl, rfl, rfl⟩
/-- `ProphContract` of `incCallee` rejects a returned prophecy different from the
argument's. -/
theorem prophContract_neg : ¬ ProphContract incCallee 4 5 9 8 := by
  rintro ⟨φ, s, hrun, -, q, hq, -, hfin⟩
  simp [incCallee, calleeRunP, runOpsP, stepOpP, evalP, calleeInitP, fupd, Callee.param] at hrun
  subst hrun
  simp [fupd, incCallee] at hq
  subst hq
  simp at hfin

/-! ## Discipline -/

/-- `nestedReborrows` and `callDeep` obey every part of the discipline. -/
theorem discipline_pos : violations nestedReborrows = [] ∧ violations callDeep = [] ∧
    violations selIncr = [] := by decide
/-- The check is static and conservative: a run-time selected borrow lends both
candidates, so assigning `x1` while `r0` is live is a violation even when the
condition chose `x0`. -/
theorem borrowSel_lends_both :
    violations [op (borrowSel 0 (lit 1) 0 1), op (assign 1 (lit 3)), op (endBorrow 0)] =
      [.lentAccess] := by decide
/-- Ending a borrow while it is reborrowed is a frozen access. -/
theorem end_parent_first_neg :
    violations [op (borrow 0 0), op (reborrow 1 0), op (endBorrow 0), op (endBorrow 1)] =
      [.frozenAccess] := by decide
/-- Rebinding an *ended* name is still a rebinding. -/
theorem rebind_ended_neg :
    violations [op (borrow 0 0), op (endBorrow 0), op (borrow 0 1), op (endBorrow 0)] =
      [.rebind] := by decide
/-- `r0 = &mut x0; *r0 = 5; end r0; r0 = &mut x1; *r0 = 9; end r0` reuses the name
of an ended borrow. -/
def rebindEnded : Prog :=
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (borrow 0 1), op (write 0 (lit 9)),
   op (endBorrow 0)]

/-- Reusing the name of an *ended* borrow is a `rebind` violation, yet harmless:
for `rebindEnded` both translations agree with the reference semantics (outcome
`x0 = 5`, `x1 = 9`). `FreshBindings` is therefore stricter than what either
translation needs on this program. -/
theorem rebindEnded_harmless :
    violations rebindEnded = [.rebind] ∧
    backSem rebindEnded zeroStore = refSem rebindEnded zeroStore ∧
    ∀ σ', ProphOutcome rebindEnded zeroStore σ' ↔ refSem rebindEnded zeroStore = some σ' := by
  have hr : refSem rebindEnded zeroStore = some ((zeroStore.set 0 5).set 1 9) := by
    apply eq_some_of_forall_map
    intro y
    rcases y with _ | _ | y
    · decide
    · decide
    · rfl
  have hb : backSem rebindEnded zeroStore = some ((zeroStore.set 0 5).set 1 9) := by
    apply eq_some_of_forall_map
    intro y
    rcases y with _ | _ | y
    · decide
    · decide
    · rfl
  refine ⟨by decide, by rw [hb, hr], fun σ' => ?_⟩
  rw [hr]
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    simp [rebindEnded, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
      fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    obtain ⟨h0, h1⟩ := hsat
    show some ((zeroStore.set 0 5).set 1 9) = some ((zeroStore.set 0 (φ 0)).set 1 (φ 1))
    rw [← h0, ← h1]
  · intro h
    cases h
    exact ⟨phiOf [5, 9], _, rfl, by decide, rfl⟩

/-- `r0 = &mut x0; r1 = &mut *r0; r0 = &mut x1; r2 = &mut *r0; end r1; x2 = *r0;
*r2 = 9; end r2; end r0`: rebinds the reborrowed name `r0`, then reads the new
`r0` while it is reborrowed by `r2`. -/
def rebindThenFrozenRead : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (borrow 0 1), op (reborrow 2 0), op (endBorrow 1),
   op (assign 2 (deref 0)), op (write 2 (lit 9)), op (endBorrow 2), op (endBorrow 0)]

/-- Rebinding does not hide later frozen accesses: ending `r1` (a reborrow of the
leaked first borrow of `r0`) does not unfreeze the new borrow held in `r0`, so the
read `x2 = *r0` while `r2` is live is reported as a frozen access. -/
theorem rebindThenFrozenRead_violations :
    violations rebindThenFrozenRead = [.rebind, .frozenAccess] := by decide

/-- Why the frozen access in `rebindThenFrozenRead` must be rejected: its
reference outcome has `x2 = 0` (the read happens before `*r2 = 9`), while every
store admitted by the prophecy translation has `x2 = 9` (the read sees `r2`'s
prophecy). -/
theorem rebindThenFrozenRead_real_excluded :
    (refSem rebindThenFrozenRead zeroStore).map (· 2) = some 0 ∧
    ∀ σ', ProphOutcome rebindThenFrozenRead zeroStore σ' → σ' 2 = 9 := by
  refine ⟨by decide, ?_⟩
  rintro σ' ⟨φ, s, hrun, hsat, rfl⟩
  simp [rebindThenFrozenRead, runP, stepP, stepOpP, evalP, PState.init, earlyCs,
    ResPolicy.std, fupd] at hrun
  subst hrun
  simp [Sat] at hsat
  simp [Store.set]
  omega

/-- Two further programs that rebind the reborrowed name `r0` and then use the
new `r0` while its reborrow `r2` is live (a write, then an end; or a read): the
uses are reported as frozen accesses. -/
theorem rebindThenFrozenUse_violations :
    violations [op (borrow 0 0), op (reborrow 1 0), op (borrow 0 1), op (reborrow 2 0),
      op (endBorrow 1), op (write 0 (lit 99)), op (write 2 (lit 5)), op (endBorrow 0),
      op (endBorrow 2)] = [.rebind, .frozenAccess, .frozenAccess] ∧
    violations [op (borrow 0 0), op (reborrow 1 0), op (borrow 0 1), op (reborrow 2 0),
      op (endBorrow 1), op (write 2 (add (deref 0) (lit 1))), op (endBorrow 2),
      op (endBorrow 0)] = [.rebind, .frozenAccess] := by decide

/-- Scoping errors are not violations: the checker stops (on this program the
reference semantics and the backward-function translation are stuck as well:
`refSem_neg_unbound`, `backSem_neg_unbound`). -/
theorem unbound_not_violation : violations [op (write 0 (lit 1))] = [] := by decide

/-- `deepCallee` passes the callee check; `cxCalleeFrozen` does not. -/
theorem calleeAvoids_pos_neg :
    CalleeAvoids .frozenAccess deepCallee ∧ ¬ CalleeAvoids .frozenAccess cxCalleeFrozen := by
  decide
/-- The three callee discipline properties: `deepCallee` satisfies all three, and
`cxCalleeFrozen`, `cxCalleeAfterEnd`, `cxCalleeRebind` each violate the
corresponding one. -/
theorem calleeDiscipline_pos_neg :
    (CalleeNoFrozenAccess deepCallee ∧ CalleeNoUseAfterEnd deepCallee ∧
      CalleeFreshBindings deepCallee) ∧
    ¬ CalleeNoFrozenAccess cxCalleeFrozen ∧ ¬ CalleeNoUseAfterEnd cxCalleeAfterEnd ∧
    ¬ CalleeFreshBindings cxCalleeRebind := by
  decide
/-- `incCallee` is scoped; `cxCalleeLocal` is not. -/
theorem calleeScoped_pos_neg : CalleeScoped incCallee ∧ ¬ CalleeScoped cxCalleeLocal := by decide

/-! ## Specification shapes for run-time selection -/

theorem selLenders_pos : selLenders true 1 2 9 = (9, 2) := by decide
theorem selLenders_neg : selLenders false 1 2 9 = (1, 9) := by decide
theorem selBackSpec_pos : SelBackSpec true 1 2 1 (selLenders true 1 2) :=
  ⟨rfl, fun _ => rfl⟩
theorem selBackSpec_neg : ¬ SelBackSpec true 1 2 1 (selLenders false 1 2) := by
  rintro ⟨-, h⟩
  have := h 5
  simp [selLenders] at this
theorem selProphSpec_pos : SelProphSpec true 1 2 1 9 9 2 := ⟨rfl, rfl⟩
/-- `backLenders01` reads off the lenders after a run-time selected borrow's
backward function. -/
theorem backLenders01_pos :
    backLenders01 idStore { cur := 0, back := selBack true 0 1 0 1 } 5 = (5, 1) := by decide
/-- `backLenders01` defaults to `(0, 0)` when the backward function writes to a
borrow (stuck in a state without borrows). -/
theorem backLenders01_neg :
    backLenders01 idStore { cur := 0, back := fun v => [(.ref 3, v)] } 5 = (0, 0) := by decide
/-- The lender must hold the prophecy, not its old value. -/
theorem selProphSpec_neg : ¬ SelProphSpec true 1 2 1 9 1 2 := by
  rintro ⟨-, h⟩
  simp [selLenders] at h

/-! ## Callee checks: which violation kinds can occur in a callee -/

theorem checkExpr_callee_no_lent_unended (e : Expr) (c0 : CState)
    (h1 : ∀ x, c0.lent x = false)
    (h2 : Violation.lentAccess ∉ c0.viol) (h3 : Violation.unendedAtExit ∉ c0.viol) :
    (∀ x, (checkExpr false c0 e).lent x = false) ∧
    Violation.lentAccess ∉ (checkExpr false c0 e).viol ∧
    Violation.unendedAtExit ∉ (checkExpr false c0 e).viol := by
  induction e generalizing c0 with
  | lit _ => exact ⟨h1, h2, h3⟩
  | var _ => simp [checkExpr, CState.setStuck, h1, h2, h3]
  | deref q =>
      simp only [checkExpr, CState.useRef]
      split <;> simp [CState.setStuck, CState.addV, h1, h2, h3]
  | add a b iha ihb =>
      obtain ⟨h1', h2', h3'⟩ := iha c0 h1 h2 h3
      exact ihb _ h1' h2' h3'

theorem checkOp_callee_no_lent_unended (c : CState) (o : Op)
    (hl : ∀ x, c.lent x = false)
    (hv : Violation.lentAccess ∉ c.viol ∧ Violation.unendedAtExit ∉ c.viol) :
    (∀ x, (checkOp false c o).lent x = false) ∧
    Violation.lentAccess ∉ (checkOp false c o).viol ∧
    Violation.unendedAtExit ∉ (checkOp false c o).viol := by
  by_cases hs : c.stuck
  · simp [checkOp, hs, hl, hv]
  · have hu : ∀ r, (∀ x, (c.useRef r).lent x = false) ∧
        Violation.lentAccess ∉ (c.useRef r).viol ∧
        Violation.unendedAtExit ∉ (c.useRef r).viol := by
      intro r
      simp only [CState.useRef]
      split <;> simp [CState.setStuck, CState.addV, hl, hv]
    cases o with
    | assign x e => simp [checkOp, hs, CState.setStuck, hl, hv]
    | borrow r x => simp [checkOp, hs, CState.setStuck, hl, hv]
    | borrowSel r e x y => simp [checkOp, hs, CState.setStuck, hl, hv]
    | reborrow t r =>
        simp only [checkOp, hs, Bool.false_eq_true, ↓reduceIte]
        split
        · exact hu r
        · simp only [CState.bindRef]
          split <;> simp [CState.addV, hu r]
    | write r e =>
        simp only [checkOp, hs, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨h1, h2, h3⟩ := checkExpr_callee_no_lent_unended e c hl hv.1 hv.2
        split
        · exact ⟨h1, h2, h3⟩
        · simp only [CState.useRef]
          split <;> simp [CState.setStuck, CState.addV, h1, h2, h3]
    | endBorrow r =>
        simp only [checkOp, hs, Bool.false_eq_true, ↓reduceIte]
        split
        · exact hu r
        · split
          · exact hu r
          · simp only [CState.release]
            cases (c.useRef r).lender r with
            | none => simp [hu r]
            | some l =>
                cases l with
                | loc x => simp [CState.upd, hu r]
                | sel x z => simp [CState.upd, hu r]
                | ref q =>
                    by_cases hq : (c.useRef r).status q = .frozen <;> simp [hq, hu r]

theorem checkOps_callee_no_lent_unended :
    ∀ (os : List Op) (c : CState),
      (∀ x, c.lent x = false) →
      Violation.lentAccess ∉ c.viol → Violation.unendedAtExit ∉ c.viol →
      Violation.lentAccess ∉ (checkOps false c os).viol ∧
      Violation.unendedAtExit ∉ (checkOps false c os).viol
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | o :: os, c, hl, h1, h2 => by
      obtain ⟨hl', h1', h2'⟩ := checkOp_callee_no_lent_unended c o hl ⟨h1, h2⟩
      exact checkOps_callee_no_lent_unended os (checkOp false c o) hl' h1' h2'

/-- In a callee only `.frozenAccess`, `.useAfterEnd` and `.rebind` can be
reported: `CalleeAvoids .lentAccess f` and `CalleeAvoids .unendedAtExit f` hold
for every callee `f`. -/
theorem calleeAvoids_lentAccess_unendedAtExit (f : Callee) :
    CalleeAvoids .lentAccess f ∧ CalleeAvoids .unendedAtExit f := by
  simp only [CalleeAvoids, calleeViolations, checkCallee]
  have ⟨h1, h2⟩ := checkOps_callee_no_lent_unended f.body CState.calleeInit
    (fun _ => rfl) (by decide) (by decide)
  split
  · exact ⟨h1, h2⟩
  · simp only [CState.useRef]
    split <;> simp [CState.setStuck, CState.addV, h1, h2]

end Toy.Prophecy
