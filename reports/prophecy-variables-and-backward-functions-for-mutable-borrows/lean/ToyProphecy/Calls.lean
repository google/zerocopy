import ToyProphecy.Resolution

/-!
# Calls returning a borrow: non-vacuity and tightness

Counterexample callees for the two callee-level statements, and a callee that
satisfies all their hypotheses.
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-- Writes the parameter while it is reborrowed, returns the reborrow:
`fn(p) { let q = &mut *p; *p = 5; *q = 6; q }`. -/
def cxCalleeFrozen : Callee := { body := [reborrow 1 0, write 0 (lit 5), write 1 (lit 6)], ret := 1 }

/-- Reborrows an ended borrow and returns it:
`fn(p) { let q = &mut *p; end q; let s = &mut *q; s }`. -/
def cxCalleeAfterEnd : Callee := { body := [reborrow 1 0, endBorrow 1, reborrow 2 1], ret := 2 }

/-- Rebinds a live borrow name, closing a cycle of parents:
`fn(p) { let q = &mut *p; let s = &mut *q; q = &mut *s; q }`. -/
def cxCalleeRebind : Callee := { body := [reborrow 1 0, reborrow 2 1, reborrow 1 2], ret := 1 }

/-- Uses a local (callee frames have none), so it is stuck:
`fn(p) { x0 = 1; p }`. -/
def cxCalleeLocal : Callee := { body := [assign 0 (lit 1)], ret := 0 }

theorem cxCalleeFrozen_violations : calleeViolations cxCalleeFrozen = [.frozenAccess] := by decide
theorem cxCalleeAfterEnd_violations : calleeViolations cxCalleeAfterEnd = [.useAfterEnd] := by decide
theorem cxCalleeRebind_violations : calleeViolations cxCalleeRebind = [.rebind] := by decide
theorem cxCalleeLocal_not_scoped : ¬ CalleeScoped cxCalleeLocal := by decide
theorem cxCalleeLocal_violations : calleeViolations cxCalleeLocal = [] := by decide

/-! ## Non-vacuity -/

/-- `deepCallee` satisfies every hypothesis of both callee-level statements, and
its prophecy contract and backward summary relate argument `4`, returned current
value `9`, and final value `20`. -/
theorem deepCallee_nonvacuous :
    CalleeScoped deepCallee ∧ CalleeNoFrozenAccess deepCallee ∧
    CalleeNoUseAfterEnd deepCallee ∧ CalleeFreshBindings deepCallee ∧
    ProphContract deepCallee 4 9 20 20 ∧ calleeFwd deepCallee 4 = some 9 ∧
    calleeBack deepCallee 4 20 = 20 :=
  ⟨by decide, by decide, by decide, by decide,
   ⟨phiOf [6, 20, 20], _, rfl, by decide, _, rfl, rfl, rfl⟩, by decide, by decide⟩

/-! ## Tightness: callee summaries agree -/

/-- `CalleeNoFrozenAccess` is necessary for
`prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings`: the contract of
`cxCalleeFrozen` admits argument prophecy `5` with returned final value `8`,
whereas the backward summary forces them equal. -/
theorem prophContract_iff_tight_frozenAccess :
    ¬ CalleeNoFrozenAccess cxCalleeFrozen ∧ CalleeNoUseAfterEnd cxCalleeFrozen ∧
    CalleeFreshBindings cxCalleeFrozen ∧
    ¬ ∀ a c pf rf, ProphContract cxCalleeFrozen a c pf rf ↔
        (calleeFwd cxCalleeFrozen a = some c ∧ pf = calleeBack cxCalleeFrozen a rf) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have hc : ProphContract cxCalleeFrozen 0 6 5 8 :=
    ⟨phiOf [8], _, rfl, by decide, _, rfl, rfl, rfl⟩
  have := ((h 0 6 5 8).1 hc).2
  revert this
  decide

/-- `CalleeNoUseAfterEnd` is necessary for
`prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings`: the contract of
`cxCalleeAfterEnd` admits argument prophecy `0` with returned final value `1`. -/
theorem prophContract_iff_tight_useAfterEnd :
    CalleeNoFrozenAccess cxCalleeAfterEnd ∧ ¬ CalleeNoUseAfterEnd cxCalleeAfterEnd ∧
    CalleeFreshBindings cxCalleeAfterEnd ∧
    ¬ ∀ a c pf rf, ProphContract cxCalleeAfterEnd a c pf rf ↔
        (calleeFwd cxCalleeAfterEnd a = some c ∧ pf = calleeBack cxCalleeAfterEnd a rf) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have hc : ProphContract cxCalleeAfterEnd 0 0 0 1 :=
    ⟨phiOf [0, 1], _, rfl, by decide, _, rfl, rfl, rfl⟩
  have := ((h 0 0 0 1).1 hc).2
  revert this
  decide

/-- `CalleeFreshBindings` is necessary for
`prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings`: the contract of
`cxCalleeRebind` admits argument prophecy `1` with returned final value `2`. -/
theorem prophContract_iff_tight_rebind :
    CalleeNoFrozenAccess cxCalleeRebind ∧ CalleeNoUseAfterEnd cxCalleeRebind ∧
    ¬ CalleeFreshBindings cxCalleeRebind ∧
    ¬ ∀ a c pf rf, ProphContract cxCalleeRebind a c pf rf ↔
        (calleeFwd cxCalleeRebind a = some c ∧ pf = calleeBack cxCalleeRebind a rf) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have hc : ProphContract cxCalleeRebind 0 0 1 2 :=
    ⟨phiOf [1, 2, 2], _, rfl, by decide, _, rfl, rfl, rfl⟩
  have := ((h 0 0 1 2).1 hc).2
  revert this
  decide

/-! ## Tightness: backward functions are projections -/

/-- `CalleeScoped` is necessary for `calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings`:
`cxCalleeLocal` binds nothing twice but is stuck, and its total backward function
is the default `0`. -/
theorem calleeBack_eq_final_tight_scoped :
    ¬ CalleeScoped cxCalleeLocal ∧ CalleeFreshBindings cxCalleeLocal ∧
    ¬ ∀ a v, calleeBack cxCalleeLocal a v = v := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 0 1
  revert this
  decide

/-- `CalleeFreshBindings` is necessary for
`calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings`: in `cxCalleeRebind` the chain of
parents from the returned borrow is a cycle and never reaches the parameter. -/
theorem calleeBack_eq_final_tight_rebind :
    CalleeScoped cxCalleeRebind ∧ ¬ CalleeFreshBindings cxCalleeRebind ∧
    ¬ ∀ a v, calleeBack cxCalleeRebind a v = v := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 0 5
  revert this
  decide

/-- Ends a reborrowed borrow (a frozen access) and then reuses its name, closing a
cycle of parents: `fn(p) { let q = &mut *p; let s = &mut *q; end q; q = &mut *s; q }`. -/
def cxCalleeEndedRebind : Callee :=
  { body := [reborrow 1 0, reborrow 2 1, endBorrow 1, reborrow 1 2], ret := 1 }

/-- Why `CalleeFreshBindings` also rejects reusing the name of an *ended* borrow: in a
callee that may have frozen accesses (which `calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings`
allows), reusing an ended name can make the chain of parents a cycle, so the
backward summary is undefined. The checker reports both the frozen access and the
reuse of the name. -/
theorem cxCalleeEndedRebind_cycle :
    calleeViolations cxCalleeEndedRebind = [.frozenAccess, .rebind] ∧
    CalleeScoped cxCalleeEndedRebind ∧ calleeBack? cxCalleeEndedRebind 0 5 = none := by
  decide

end Toy.Prophecy
