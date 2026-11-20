import ToyProphecy.Counterexamples

/-!
# Where resolution constraints go: omission, premature resolution, early
resolution of a reborrowed parent, and callee-exit resolution

All results in this file are about concrete programs and are fully proved.
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-- `r0 = &mut x0; *r0 = 5; end r0` -/
def writeOnce : Prog := [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0)]

/-- `r0 = &mut x0; r1 = &mut *r0; *r1 = 7; end r1; end r0` -/
def reborrowOnce : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (endBorrow 1), op (endBorrow 0)]

/-! ## Omitting one resolution -/

/-- The only outcome of `writeThenRead` from the zero store: `x0 = x1 = 5`. -/
def writeThenReadOut : Store := (zeroStore.set 0 5).set 1 5

theorem refSem_writeThenRead : refSem writeThenRead zeroStore = some writeThenReadOut := by
  simp only [refSem, writeThenRead, runR, stepR, stepOpR, evalR, RState.init,
    writeThenReadOut]
  rfl

/-- Positive control: under the standard policy the prophecy translation of
`writeThenRead` admits exactly the program's outcome. -/
theorem prophOutcome_writeThenRead_iff (σ' : Store) :
    ProphOutcome writeThenRead zeroStore σ' ↔ refSem writeThenRead zeroStore = some σ' := by
  rw [refSem_writeThenRead]
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    simp [writeThenRead, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
      fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    congr 1
    funext y
    simp only [writeThenReadOut, Store.set, zeroStore]
    split <;> simp_all
  · intro h
    cases h
    refine ⟨phiOf [5], _, rfl, by decide, ?_⟩
    funext y
    simp only [writeThenReadOut, Store.set, zeroStore, phiOf]
    split <;> rfl

/-- **Resolution is necessary for precision.** `writeThenRead`
(`r0 = &mut x0; *r0 = 5; end r0; x1 = x0`) obeys every part of the borrow
discipline, yet when the resolution of `r0` at its end is omitted, the prophecy
translation admits a final store with `x0 = x1 = 7`, which the program cannot
produce (its only outcome has `x0 = x1 = 5`). The read of the lender after the
end observes the unresolved prophecy. -/
theorem omitting_resolution_admits_unproducible_store :
    NoLentAccess writeThenRead ∧ NoFrozenAccess writeThenRead ∧ NoUseAfterEnd writeThenRead ∧
    FreshBindings writeThenRead ∧ AllEndedAtExit writeThenRead ∧
    ∃ σ', ProphOutcomeWith (ResPolicy.omitAtEnd 0) writeThenRead zeroStore σ' ∧
      σ' 0 = 7 ∧ σ' 1 = 7 ∧ refSem writeThenRead zeroStore ≠ some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨_, ⟨phiOf [7], _, rfl, by decide, rfl⟩, rfl, rfl, ?_⟩
  intro h
  have := congrArg (Option.map (· 0)) h
  revert this
  decide

/-- With the resolution of `r0` omitted, the real outcome of `writeThenRead` is
still admitted: omission adds stores, it does not remove the real one. -/
theorem omitting_resolution_keeps_real_store_writeThenRead :
    ProphOutcomeWith (ResPolicy.omitAtEnd 0) writeThenRead zeroStore writeThenReadOut := by
  refine ⟨phiOf [5], _, rfl, by decide, ?_⟩
  funext y
  simp only [writeThenReadOut, Store.set, zeroStore, phiOf]
  split <;> rfl

/-! ## Resolving too early -/

/-- **Premature resolution is unsound.** Resolving `r0` of `writeOnce`
(`r0 = &mut x0; *r0 = 5; end r0`) right after its creation (statement `0`),
before the write through it, makes every admitted final store have `x0 = 0`,
while the program's only outcome has `x0 = 5`; the admitted set is non-empty, so
a verifier that quantifies over admitted stores would accept the false
postcondition `x0 = 0`. The program obeys every part of the discipline. -/
theorem premature_resolution_excludes_real_store :
    NoLentAccess writeOnce ∧ NoFrozenAccess writeOnce ∧ NoUseAfterEnd writeOnce ∧
    FreshBindings writeOnce ∧ AllEndedAtExit writeOnce ∧
    (∀ σ', ProphOutcomeWith (ResPolicy.resolveAfter 0 0) writeOnce zeroStore σ' → σ' 0 = 0) ∧
    (∃ σ', ProphOutcomeWith (ResPolicy.resolveAfter 0 0) writeOnce zeroStore σ') ∧
    (refSem writeOnce zeroStore).map (· 0) = some 5 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, by decide⟩
  · rintro σ' ⟨φ, s, hrun, hsat, rfl⟩
    simp [writeOnce, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.resolveAfter,
      fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    simp only [Store.set, ite_true]
    exact hsat.symm
  · exact ⟨_, phiOf [0], _, rfl, by decide, rfl⟩

/-- Positive control: resolving `r0` of `writeOnce` right after its last write
(statement `1`) instead of at its end admits exactly the program's outcome. -/
theorem resolution_after_last_write_exact (σ' : Store) :
    ProphOutcomeWith (ResPolicy.resolveAfter 1 0) writeOnce zeroStore σ' ↔
      refSem writeOnce zeroStore = some σ' := by
  have hr : refSem writeOnce zeroStore = some (zeroStore.set 0 5) := by
    simp only [refSem, writeOnce, runR, stepR, stepOpR, evalR, RState.init]
    rfl
  rw [hr]
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    simp [writeOnce, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.resolveAfter,
      fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    congr 1
    funext y
    simp only [Store.set, zeroStore]
    split <;> simp_all
  · intro h
    cases h
    refine ⟨phiOf [5], _, rfl, by decide, ?_⟩
    funext y
    simp only [Store.set, zeroStore, phiOf]
    split <;> rfl

/-- **A reborrowed parent may be resolved while its reborrow is live.** In
`reborrowOnce` (`r0 = &mut x0; r1 = &mut *r0; *r1 = 7; end r1; end r0`),
resolving `r0` right after the reborrow (statement `1`), while `r1` is still live
and before `r1`'s write, admits exactly the program's outcome: after the reborrow,
`r0`'s current value is `r1`'s prophecy, so the early constraint links the two
prophecies instead of fixing a stale value. -/
theorem parent_resolution_while_reborrow_live_exact (σ' : Store) :
    ProphOutcomeWith (ResPolicy.resolveAfter 1 0) reborrowOnce zeroStore σ' ↔
      refSem reborrowOnce zeroStore = some σ' := by
  have hr : refSem reborrowOnce zeroStore = some (zeroStore.set 0 7) := by
    simp only [refSem, reborrowOnce, runR, stepR, stepOpR, evalR, RState.init]
    rfl
  rw [hr]
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    simp [reborrowOnce, runP, stepP, stepOpP, evalP, PState.init, earlyCs,
      ResPolicy.resolveAfter, fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    congr 1
    funext y
    simp only [Store.set, zeroStore]
    split <;> simp_all
  · intro h
    cases h
    refine ⟨phiOf [7, 7], _, rfl, by decide, ?_⟩
    funext y
    simp only [Store.set, zeroStore, phiOf]
    split <;> rfl

/-! ## Resolution at callee exit -/

/-- **Callee-exit resolution is necessary for precision.** `callDeep` (a call of
`deepCallee`, which returns a reborrow two levels below its parameter) obeys
every part of the discipline and, from the store `x ↦ x`, produces `x0 = x1 = 15`.
Without the resolutions emitted at callee exit, the prophecy translation admits a
final store with `x0 = x1 = 7`, which is not the program's outcome: the
argument's prophecy is no longer linked to the returned borrow's. -/
theorem omitting_callee_exit_resolution_admits_unproducible_store :
    NoLentAccess callDeep ∧ NoFrozenAccess callDeep ∧ NoUseAfterEnd callDeep ∧
    FreshBindings callDeep ∧ AllEndedAtExit callDeep ∧
    (refSem callDeep idStore).map (fun σ => (σ 0, σ 1)) = some (15, 15) ∧
    ∃ σ', ProphOutcomeWith ResPolicy.omitAtCalleeExit callDeep idStore σ' ∧
      σ' 0 = 7 ∧ σ' 1 = 7 ∧ refSem callDeep idStore ≠ some σ' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨_, ⟨phiOf [7, 7, 2, 0, 15], _, rfl, by decide, rfl⟩, rfl, rfl, ?_⟩
  intro h
  have := congrArg (Option.map (· 0)) h
  revert this
  decide

/-- The only outcome of `callDeep` from the store `x ↦ x`: `x0 = x1 = 15`, every
other local unchanged. -/
def callDeepOut : Store := (idStore.set 0 15).set 1 15

/-- A partial store is `some τ` as soon as it agrees with `τ` at every local. -/
theorem eq_some_of_forall_map {o : Option Store} {τ : Store}
    (h : ∀ y, o.map (· y) = some (τ y)) : o = some τ := by
  cases o with
  | none => exact absurd (h 0) (by simp)
  | some σ =>
    congr 1
    funext y
    simpa using h y

theorem refSem_callDeep : refSem callDeep idStore = some callDeepOut := by
  apply eq_some_of_forall_map
  intro y
  rcases y with _ | _ | y
  · decide
  · decide
  · rfl

/-- Positive control: under the standard policy (callee-exit resolution
included), the stores admitted for `callDeep` from `x ↦ x` are exactly the
program's outcome; in particular the spurious store with `x0 = x1 = 7` is
excluded. -/
theorem callDeep_prophOutcome_iff (σ' : Store) :
    ProphOutcome callDeep idStore σ' ↔ refSem callDeep idStore = some σ' := by
  rw [refSem_callDeep]
  have hfilt : (deepCallee.refNames.filter fun j => decide (j ≠ deepCallee.ret)) = [0, 1, 2] := by
    decide
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    simp only [callDeep, runP, stepP, calleeRunP, earlyCs, ResPolicy.std, List.filterMap_nil,
      List.append_nil, calleeExitCs, hfilt] at hrun
    simp [deepCallee, runOpsP, stepOpP, evalP, PState.init, calleeInitP, fupd,
      Callee.param, List.filterMap_cons] at hrun
    subst hrun
    simp [Sat, idStore] at hsat
    obtain ⟨h2, h31, h43, h4, h10⟩ := hsat
    have e1 : φ 1 = 15 := by omega
    have e0 : φ 0 = 15 := by omega
    show some callDeepOut = some ((idStore.set 0 (φ 0)).set 1 (φ 1))
    rw [e0, e1]
    rfl
  · intro h
    cases h
    exact ⟨phiOf [15, 15, 2, 15, 15], _, rfl, by decide, rfl⟩

/-- Without callee-exit resolution the real outcome of `callDeep` is still
admitted (omission adds the spurious store, it does not remove the real one). -/
theorem callDeep_omitAtCalleeExit_admits_real :
    ProphOutcomeWith ResPolicy.omitAtCalleeExit callDeep idStore callDeepOut :=
  ⟨phiOf [15, 15, 2, 15, 15], _, rfl, by decide, rfl⟩

/-! ## Ending a reborrowed parent before its reborrow -/

/-- `r0 = &mut x0; r1 = &mut *r0; *r1 = 7; end r0; end r1` (ends the parent while
it is reborrowed: a frozen access). -/
def endParentFirst : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (endBorrow 0), op (endBorrow 1)]

/-- **Ending a parent before its reborrow: exact for prophecies, lossy for
backward functions.** `endParentFirst` has a single violation (frozen access, at
`end r0`). The reference semantics ends with `x0 = 7`. The backward-function
translation ends with `x0 = 0`: ending `r0` writes back `r0`'s stale current
value, and the later write-back of `r1` goes to the already-ended `r0`. The
prophecy translation admits exactly the program's outcome: `r0`'s current value
is `r1`'s prophecy, which `r1`'s own resolution later fixes. -/
theorem endParentFirst_prophecy_exact_backward_lossy :
    violations endParentFirst = [.frozenAccess] ∧
    (refSem endParentFirst zeroStore).map (· 0) = some 7 ∧
    (backSem endParentFirst zeroStore).map (· 0) = some 0 ∧
    ∀ σ', ProphOutcome endParentFirst zeroStore σ' ↔ refSem endParentFirst zeroStore = some σ' := by
  refine ⟨by decide, by decide, by decide, fun σ' => ?_⟩
  have hr : refSem endParentFirst zeroStore = some (zeroStore.set 0 7) := by
    apply eq_some_of_forall_map
    intro y
    rcases y with _ | y
    · decide
    · rfl
  rw [hr]
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    simp [endParentFirst, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std,
      fupd] at hrun
    subst hrun
    simp [Sat] at hsat
    congr 1
    funext y
    simp only [Store.set, zeroStore]
    split <;> simp_all
  · intro h
    cases h
    refine ⟨phiOf [7, 7], _, rfl, by decide, ?_⟩
    funext y
    simp only [Store.set, zeroStore, phiOf]
    split <;> rfl

/-- `r0 = &mut x0; r1 = &mut *r0; *r1 = 7; end r0` (the reborrow never ends). -/
def endParentFirstChildUnended : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (endBorrow 0)]

/-- Ending the parent first is exact for the prophecy translation only because
the reborrow is resolved later: if `r1` never ends, the program still produces
`x0 = 7`, but a store with `x0 = 8` is also admitted. -/
theorem endParentFirstChildUnended_imprecise :
    violations endParentFirstChildUnended = [.frozenAccess, .unendedAtExit] ∧
    (refSem endParentFirstChildUnended zeroStore).map (· 0) = some 7 ∧
    (∃ σ', ProphOutcome endParentFirstChildUnended zeroStore σ' ∧ σ' 0 = 7) ∧
    (∃ σ', ProphOutcome endParentFirstChildUnended zeroStore σ' ∧ σ' 0 = 8) :=
  ⟨by decide, by decide, ⟨_, ⟨phiOf [7, 7], _, rfl, by decide, rfl⟩, rfl⟩,
    ⟨_, ⟨phiOf [8, 8], _, rfl, by decide, rfl⟩, rfl⟩⟩

end Toy.Prophecy
