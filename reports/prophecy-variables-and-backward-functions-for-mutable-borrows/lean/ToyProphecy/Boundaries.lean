import ToyProphecy.NonVacuity

/-!
# Boundary examples

Concrete, fully proved facts that delimit what the definitions say:

* the discipline checker stops at the first scoping error, so a program or callee
  with a scoping error satisfies every discipline property that the part before
  the error satisfies;
* `CalleeScoped` also requires the returned reference variable to be bound;
* `CalleeFreshBindings` rejects reusing the name of an ended borrow even on a
  callee where that reuse is harmless;
* `calleeBack` totalizes the partial `calleeBack?` with the default `0`;
* `ResPolicy.omitAtEnd r` leaves callee frames resolved, even when `r` is also the
  name of a callee's parameter;
* degenerate edge cases (empty program, empty callee, a selection between a local
  and itself).
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-! ## Scoping of a callee includes its returned reference variable -/

/-- `fn(p) { r1 }`: an empty body returning the never-bound name `1`. -/
def emptyBodyUnboundRet : Callee := { body := [], ret := 1 }

/-- `emptyBodyUnboundRet` has an empty body and binds no name twice, but it
returns a name that is never bound, so it is not scoped, and its total backward
function is the default `0` rather than the projection. -/
theorem emptyBody_unboundRet_not_scoped :
    emptyBodyUnboundRet.body = [] ∧ CalleeFreshBindings emptyBodyUnboundRet ∧
    ¬ CalleeScoped emptyBodyUnboundRet ∧ calleeBack emptyBodyUnboundRet 0 5 = 0 :=
  ⟨rfl, by decide, by decide, by decide⟩

/-! ## The checker stops at the first scoping error -/

/-- Once the checker is stuck, checking further operations changes nothing. -/
theorem checkOps_of_stuck (L : Bool) (c : CState) (h : c.stuck = true) :
    ∀ os, checkOps L c os = c
  | [] => rfl
  | o :: os => by
    have hc : checkOp L c o = c := by simp [checkOp, h]
    simp only [checkOps, hc]
    exact checkOps_of_stuck L c h os

/-- Once the checker is stuck, checking further statements changes nothing: no
violation after the first scoping error is recorded. -/
theorem checkStmts_of_stuck (c : CState) (h : c.stuck = true) :
    ∀ P, checkStmts c P = c
  | [] => rfl
  | s :: ss => by
    have hc : checkStmt c s = c := by
      cases s with
      | op o => simp [checkStmt, checkOp, h]
      | call t f r => simp [checkStmt, h]
    simp only [checkStmts, hc]
    exact checkStmts_of_stuck c h ss

/-- `r0 = &mut x0; *r99 = 1; x1 = x0; r1 = &mut *r0; *r0 = 2; end r0; end r0;
r0 = &mut x1`: a scoping error (`r99` is never bound) followed by a lent access,
frozen accesses, a use after end, a rebinding, and borrows left live. -/
def stuckProgWithViolations : Prog :=
  [ op (borrow 0 0),
    op (write 99 (lit 1)),
    op (assign 1 (var 0)),
    op (reborrow 1 0),
    op (write 0 (lit 2)),
    op (endBorrow 0),
    op (endBorrow 0),
    op (borrow 0 1) ]

/-- The checker records nothing after the first scoping error and does not report
live borrows of a stuck program, so `stuckProgWithViolations` satisfies all five
discipline properties; every semantics is stuck on it (no final store; the
prophecy run is stuck for every prophecy assignment, so no store is admitted). -/
theorem stuckProg_satisfies_all_avoids :
    NoLentAccess stuckProgWithViolations ∧
    NoFrozenAccess stuckProgWithViolations ∧
    NoUseAfterEnd stuckProgWithViolations ∧
    FreshBindings stuckProgWithViolations ∧
    AllEndedAtExit stuckProgWithViolations ∧
    refSem stuckProgWithViolations zeroStore = none ∧
    backSem stuckProgWithViolations zeroStore = none ∧
    (∀ φ, runP ResPolicy.std φ 0 (PState.init zeroStore) stuckProgWithViolations = none) ∧
    (∀ σ', ¬ ProphOutcome stuckProgWithViolations zeroStore σ') := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun φ => rfl, ?_⟩
  rintro σ' ⟨φ, s, hrun, -, -⟩
  simp [stuckProgWithViolations, runP, stepP, stepOpP, evalP, PState.init, earlyCs,
    ResPolicy.std, fupd] at hrun

/-- `fn(p) { x0 = 1; let q = &mut *p; *p = 5; end q; *q = 6; q = &mut *p; q }`: a
scoping error (a local operation in a callee) followed by a frozen access, a use
after end, and a rebinding. -/
def stuckCalleeWithViolations : Callee :=
  { body := [assign 0 (lit 1), reborrow 1 0, write 0 (lit 5), endBorrow 1,
             write 1 (lit 6), reborrow 1 0]
    ret := 1 }

/-- Likewise for callees: `stuckCalleeWithViolations` is not scoped but satisfies
all three callee discipline properties. -/
theorem stuckCallee_satisfies_all_avoids :
    ¬ CalleeScoped stuckCalleeWithViolations ∧
    CalleeNoFrozenAccess stuckCalleeWithViolations ∧
    CalleeNoUseAfterEnd stuckCalleeWithViolations ∧
    CalleeFreshBindings stuckCalleeWithViolations :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The callee `cxCalleeLocal` (`fn(p) { x0 = 1; p }`, stuck on its local
operation) satisfies all three callee discipline properties, has no forward value
(`calleeFwd_neg`), and its prophecy contract never holds. -/
theorem cxCalleeLocal_avoids_all_no_contract :
    CalleeNoFrozenAccess cxCalleeLocal ∧ CalleeNoUseAfterEnd cxCalleeLocal ∧
    CalleeFreshBindings cxCalleeLocal ∧ (∀ a, calleeFwd cxCalleeLocal a = none) ∧
    ∀ a c pf rf, ¬ ProphContract cxCalleeLocal a c pf rf := by
  refine ⟨by decide, by decide, by decide, fun a => rfl, ?_⟩
  rintro a c pf rf ⟨φ, s, hrun, -⟩
  have h : calleeRunP true φ cxCalleeLocal a pf 0 = none := rfl
  rw [h] at hrun
  cases hrun

/-! ## Reusing an ended name in a callee -/

/-- `fn(p) { let q = &mut *p; *q = *q + 2; end q; *p = *p + 3; q = &mut *p; q }`:
reuses the name of the ended borrow `q`. -/
def reuseEndedCallee : Callee :=
  { body := [ reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
              write 0 (add (deref 0) (lit 3)), reborrow 1 0 ]
    ret := 1 }

/-- On `reuseEndedCallee` the reuse of an ended name is harmless: the callee
violates `CalleeFreshBindings` only, is scoped, has the projection as backward
function, and its prophecy contract agrees with its backward summary. -/
theorem reuseEndedCallee_harmless :
    CalleeScoped reuseEndedCallee ∧
    CalleeNoFrozenAccess reuseEndedCallee ∧
    CalleeNoUseAfterEnd reuseEndedCallee ∧
    ¬ CalleeFreshBindings reuseEndedCallee ∧
    (∀ a v, calleeBack reuseEndedCallee a v = v) ∧
    (∀ a c pf rf, ProphContract reuseEndedCallee a c pf rf ↔
      (calleeFwd reuseEndedCallee a = some c ∧ pf = calleeBack reuseEndedCallee a rf)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro a v
    simp [calleeBack, calleeBack?, reuseEndedCallee, calleeRunB, runOpsB, stepOpB, evalB,
      applyBack, calleeInitB, unwindB, Callee.param, fupd]
  · intro a c pf rf
    have hfwd : calleeFwd reuseEndedCallee a = some (a + 5) := by
      simp [calleeFwd, reuseEndedCallee, calleeRunB, runOpsB, stepOpB, evalB, applyBack,
        calleeInitB, fupd, Callee.param]
      omega
    have hback : calleeBack reuseEndedCallee a rf = rf := by
      simp [calleeBack, calleeBack?, reuseEndedCallee, calleeRunB, runOpsB, stepOpB, evalB,
        applyBack, calleeInitB, unwindB, Callee.param, fupd]
    rw [hfwd, hback]
    constructor
    · rintro ⟨φ, s, hrun, hsat, q, hq, hqc, hqf⟩
      have hm : (calleeRunP true φ reuseEndedCallee a pf 0).map
          (fun s => (s.cs, s.refs reuseEndedCallee.ret)) =
          some ([(a + 2, φ 0), (φ 1, pf)], some { cur := φ 0 + 3, fin := φ 1, done := false }) := rfl
      rw [hrun] at hm
      injection hm with hm
      injection hm with hcs hret
      rw [hq] at hret
      injection hret with hret
      subst hret
      rw [hcs] at hsat
      simp only [Sat, List.mem_cons, List.not_mem_nil, or_false] at hsat
      have h1 := hsat (a + 2, φ 0) (Or.inl rfl)
      have h2 := hsat (φ 1, pf) (Or.inr rfl)
      dsimp only at h1 h2 hqc hqf
      exact ⟨congrArg some (by omega), by omega⟩
    · rintro ⟨h1, hpf⟩
      cases h1
      subst hpf
      refine ⟨phiOf [a + 2, pf], _, rfl, ?_, _, rfl, ?_, rfl⟩
      · change Sat [(a + 2, phiOf [a + 2, pf] 0), (phiOf [a + 2, pf] 1, pf)]
        have hp0 : phiOf [a + 2, pf] 0 = a + 2 := rfl
        have hp1 : phiOf [a + 2, pf] 1 = pf := rfl
        rw [hp0, hp1]
        intro c hc
        simp at hc
        rcases hc with rfl | rfl <;> rfl
      · change (phiOf [a + 2, pf] 0 + 3 : Int) = a + 5
        have hp0 : phiOf [a + 2, pf] 0 = a + 2 := rfl
        rw [hp0]
        omega

/-! ## `calleeBack` is a totalization -/

/-- `calleeBack` maps the undefined case of `calleeBack?` (here a cycle of
parents) to `0`, which coincides with a legitimate result `0`. -/
theorem calleeBack_masks_none_at_zero :
    calleeBack? cxCalleeRebind 0 0 = none ∧ calleeBack cxCalleeRebind 0 0 = 0 :=
  ⟨by decide, by decide⟩

/-- Away from `0` the totalization loses nothing: `calleeBack f a v = v` with
`v ≠ 0` implies that the partial backward function is defined and equals `v`. -/
theorem calleeBackOpt_eq_some_of_calleeBack_eq_of_ne_zero (f : Callee) (a v : Int)
    (h : calleeBack f a v = v) (hv : v ≠ 0) : calleeBack? f a v = some v := by
  unfold calleeBack at h
  cases hc : calleeBack? f a v with
  | none =>
    rw [hc] at h
    exact absurd h.symm hv
  | some w =>
    rw [hc] at h
    simp only [Option.getD_some] at h
    rw [h]

/-! ## Omission at the end of a main-program name leaves callee frames resolved -/

/-- Under `ResPolicy.omitAtEnd 0` on `callDeep`, the callee `deepCallee` still
resolves its parameter (also named `0`) and its intermediate borrows at callee
exit; only the main program's `end r0` is unresolved. So every admitted store
still has `x1 = 15`. -/
theorem callDeep_omitAtEnd0_callee_still_resolved :
    ∀ σ', ProphOutcomeWith (ResPolicy.omitAtEnd 0) callDeep idStore σ' → σ' 1 = 15 := by
  rintro σ' ⟨φ, s, hrun, hsat, rfl⟩
  have hm : (runP (ResPolicy.omitAtEnd 0) φ 0 (PState.init idStore) callDeep).map
      (fun s => (s.cs, s.store 1)) =
      some ([(2, φ 2), (φ 3, φ 1), (φ 4, φ 3), (φ 2 + 3 + 10, φ 4)], φ 1) := rfl
  rw [hrun] at hm
  injection hm with hm
  injection hm with hcs hs1
  rw [hcs] at hsat
  simp only [Sat, List.mem_cons, List.not_mem_nil, or_false] at hsat
  have c1 := hsat (2, φ 2) (Or.inl rfl)
  have c2 := hsat (φ 3, φ 1) (Or.inr (Or.inl rfl))
  have c3 := hsat (φ 4, φ 3) (Or.inr (Or.inr (Or.inl rfl)))
  have c4 := hsat (φ 2 + 3 + 10, φ 4) (Or.inr (Or.inr (Or.inr rfl)))
  dsimp only at c1 c2 c3 c4
  rw [hs1]
  omega

/-- Under the standard policy no admitted store of `callDeep` from `x ↦ x` has
`x0 = x1 = 7` (a consequence of `callDeep_prophOutcome_iff`). -/
theorem callDeep_std_excludes_spurious :
    ¬ ∃ σ', ProphOutcome callDeep idStore σ' ∧ σ' 0 = 7 ∧ σ' 1 = 7 := by
  rintro ⟨σ', h, h0, -⟩
  have hr := (callDeep_prophOutcome_iff σ').1 h
  rw [refSem_callDeep] at hr
  injection hr with hr
  have := congrFun hr 0
  simp [callDeepOut, Store.set, h0] at this

/-! ## Edge cases -/

/-- The empty program satisfies all five discipline properties, and the three
semantics agree on it for every initial store. -/
theorem emptyProg_edge_case (σ : Store) :
    NoLentAccess [] ∧ NoFrozenAccess [] ∧ NoUseAfterEnd [] ∧
    FreshBindings [] ∧ AllEndedAtExit [] ∧
    backSem [] σ = refSem [] σ ∧
    (∀ σ', ProphOutcome [] σ σ' ↔ backSem [] σ = some σ') := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, fun σ' => ?_⟩
  constructor
  · rintro ⟨φ, s, hrun, -, rfl⟩
    simp [runP, PState.init] at hrun
    subst hrun
    rfl
  · intro h
    simp [backSem, runB, BState.init] at h
    subst h
    exact ⟨fun _ => 0, _, rfl, by simp [Sat, PState.init], rfl⟩

/-- `fn(p) { p }`. -/
def emptyCallee : Callee := { body := [], ret := 0 }

/-- The empty callee satisfies every callee hypothesis, its backward function is
the projection, and its prophecy contract agrees with its backward summary. -/
theorem emptyCallee_edge_case :
    CalleeScoped emptyCallee ∧
    CalleeNoFrozenAccess emptyCallee ∧
    CalleeNoUseAfterEnd emptyCallee ∧
    CalleeFreshBindings emptyCallee ∧
    (∀ a v, calleeBack emptyCallee a v = v) ∧
    (∀ a c pf rf, ProphContract emptyCallee a c pf rf ↔
      (calleeFwd emptyCallee a = some c ∧ pf = calleeBack emptyCallee a rf)) := by
  refine ⟨by decide, by decide, by decide, by decide, fun a v => rfl, fun a c pf rf => ?_⟩
  constructor
  · rintro ⟨φ, s, hrun, -, q, hq, hqc, hqf⟩
    simp [emptyCallee, calleeRunP, runOpsP, calleeInitP, calleeExitCs, Callee.refNames,
      Callee.param] at hrun
    subst hrun
    simp [emptyCallee, fupd] at hq
    subst hq
    simp [calleeFwd, calleeBack, calleeBack?, emptyCallee, calleeRunB, runOpsB,
      calleeInitB, unwindB, fupd, Callee.param]
    exact ⟨hqc, hqf⟩
  · rintro ⟨hfwd, hpf⟩
    simp [calleeFwd, calleeBack, calleeBack?, emptyCallee, calleeRunB, runOpsB,
      calleeInitB, unwindB, fupd, Callee.param] at hfwd hpf
    subst hfwd; subst hpf
    refine ⟨fun _ => 0, _, rfl, ?_, _, rfl, rfl, rfl⟩
    simp [Sat, calleeInitP, calleeExitCs, emptyCallee, Callee.refNames, Callee.param]

/-- `r0 = if x2 ≠ 0 { &mut x0 } else { &mut x0 }; *r0 = *r0 + 1; end r0`: a run-time
selection between a local and itself. -/
def selSameLocal : Prog :=
  [op (borrowSel 0 (var 2) 0 0), op (write 0 (add (deref 0) (lit 1))), op (endBorrow 0)]

/-- `selSameLocal` satisfies all five discipline properties, and the three
semantics agree on it for every initial store. -/
theorem selSameLocal_edge_case (σ : Store) :
    NoLentAccess selSameLocal ∧ NoFrozenAccess selSameLocal ∧ NoUseAfterEnd selSameLocal ∧
    FreshBindings selSameLocal ∧ AllEndedAtExit selSameLocal ∧
    backSem selSameLocal σ = refSem selSameLocal σ ∧
    (∀ σ', ProphOutcome selSameLocal σ σ' ↔ refSem selSameLocal σ = some σ') := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · by_cases h : σ 2 = 0 <;>
    · simp [backSem, refSem, selSameLocal, runB, runR, stepB, stepR, stepOpB, stepOpR,
        evalB, evalR, BState.init, RState.init, selBack, applyBack, fupd, h]
      funext y
      by_cases hy : y = 0 <;> simp [Store.set, hy]
  · intro σ'
    have hr : refSem selSameLocal σ = some (σ.set 0 (σ 0 + 1)) := by
      by_cases h : σ 2 = 0 <;>
        simp [refSem, selSameLocal, runR, stepR, stepOpR, evalR, RState.init, fupd, h]
    rw [hr]
    constructor
    · rintro ⟨φ, s, hrun, hsat, rfl⟩
      by_cases h : σ 2 = 0 <;>
      · simp [selSameLocal, runP, stepP, stepOpP, evalP, PState.init, earlyCs,
          ResPolicy.std, fupd, h] at hrun
        subst hrun
        simp [Sat] at hsat
        congr 1
        funext y
        by_cases hy : y = 0 <;> simp_all [Store.set]
    · intro hs
      cases hs
      by_cases h : σ 2 = 0 <;>
      · refine ⟨phiOf [σ 0 + 1], ?_⟩
        simp [selSameLocal, runP, stepP, stepOpP, evalP, PState.init, earlyCs,
          ResPolicy.std, fupd, h, Sat, phiOf]

end Toy.Prophecy
