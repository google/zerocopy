import ToyBackward.Programs

/-!
# Positive and negative examples for every core definition

Each definition is exercised on an instance it is meant to admit (positive) and one it is meant
to reject (negative). Observations containing functions are compared through finitely many
projections.
-/

namespace Toy.Backward

/-! ## `heapSem` -/

/-- Positive: a write then a read through one reference updates memory and is observed. -/
theorem heapSem_example_writeThenRead :
    (heapSem (writeThenRead 5) zeroHeap).map (fun o => (o.heap 0, o.vars 0)) = some (5, 5) := by
  decide

/-- Positive: the heap semantics has no aliasing rules: a reference observes a raw write made while
it is in use. -/
theorem heapSem_example_alias_visible :
    (heapSem rawWriteDuringBorrow zeroHeap).map (fun o => o.vars 0) = some 7 := by
  decide

/-- Negative: using a reference that was never created is stuck. -/
theorem heapSem_example_danglingUse : heapSem danglingUse zeroHeap = none := by
  rfl

/-- Negative: using a reference before the statement that creates it is stuck. -/
theorem heapSem_example_useBeforeCreation : heapSem useBeforeCreation zeroHeap = none := by
  rfl

/-! ## `isRegion` -/

/-- Positive and negative: index 0 of `writeOnce` is an `asMut` (a region); index 1 (a write) and
index 5 (out of range) are not. -/
theorem isRegion_examples :
    isRegion writeOnce 0 = true ∧ isRegion writeOnce 1 = false ∧ isRegion writeOnce 5 = false := by
  decide

/-! ## `translate` and `effSem` -/

/-- Positive: the effectful translation inserts the backward call where the placement says. -/
theorem translate_example_writeThenRead :
    translate (writeThenRead 5) (endAt 3) =
      [.fwd 0 0, .lwrite 0 (.lit 5), .lread 0 0, .back 0] := by
  decide

/-- Negative: no backward call is inserted for an index that is not a region. -/
theorem translate_example_no_back_for_nonregion :
    translate danglingUse (endAt 0) = [.lread 0 0] := by
  decide

/-- Positive: with the region ended at the end of the program, the write reaches the heap model. -/
theorem effSem_example_writeThenRead :
    (effSem (writeThenRead 5) (endAt 3) zeroHeap).map (fun o => (o.heap 0, o.vars 0)) =
      some (5, 5) := by
  decide

/-- Positive: before its region ends, a write through the reference is not yet in the heap model:
a raw read placed after the write but before the backward call sees the old value (the unchecked
copy-in/copy-out behaviour). -/
theorem effSem_example_write_back_deferred :
    (effSem [.asMut 0, .write 0 (.lit 5), .rawRead 1 0] (endAt 3) zeroHeap).map
      (fun o => (o.vars 1, o.heap 0)) = some (0, 5) := by
  decide

/-- Positive: the region's local value stays writable after its backward call; such a write is
silently lost rather than stuck (the unchecked behaviour). -/
theorem effSem_example_write_after_back_lost :
    (effSem writeOnce (endAt 1) zeroHeap).map (fun o => o.heap 0) = some 0 := by
  decide

/-- Negative: a backward call scheduled before its forward call is stuck. -/
theorem effSem_example_end_before_creation : effSem (writeThenRead 5) (endAt 0) zeroHeap = none := by
  rfl

/-! ## `lockSem` -/

/-- Positive: with the region ended at the end of the program, the borrow-locking translation
writes back and is observed. -/
theorem lockSem_example_writeThenRead :
    (lockSem (writeThenRead 5) (endAt 3) zeroHeap).map (fun o => (o.heap 0, o.vars 0)) =
      some (5, 5) := by
  decide

/-- Positive: two loans of the same cell in sequence, the first returned before the second. -/
theorem lockSem_example_reborrowAfterWrite :
    (lockSem (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) zeroHeap).map
      (fun o => (o.heap 0, o.vars 0, o.vars 1)) = some (5, 0, 5) := by
  decide

/-- Negative: an owner access to a lent cell is stuck (instead of reading a stale heap model). -/
theorem lockSem_example_owner_access_while_lent :
    lockSem [.asMut 0, .write 0 (.lit 5), .rawRead 1 0] (endAt 3) zeroHeap = none := by
  rfl

/-- Negative: a use of the region after its backward call is stuck (instead of being lost). -/
theorem lockSem_example_use_after_back :
    lockSem writeOnce (endAt 1) zeroHeap = none := by
  rfl

/-- Negative: a second loan of a cell that is still lent is stuck. -/
theorem lockSem_example_second_loan :
    lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = none := by
  rfl

/-- Negative: a run ending with a cell still lent is stuck. -/
theorem lockSem_example_never_returned :
    lockSem writeOnce (endAt 3) zeroHeap = none := by
  rfl

/-! ## `pureBackSem` -/

/-- Positive: local reads see local writes, but nothing is ever written back to the heap model. -/
theorem pureBackSem_example_writeThenRead :
    (pureBackSem (writeThenRead 5) zeroHeap).map (fun o => (o.heap 0, o.vars 0)) = some (0, 5) := by
  decide

/-- Negative: using a reference that was never created is stuck. -/
theorem pureBackSem_example_danglingUse : pureBackSem danglingUse zeroHeap = none := by
  rfl

/-! ## `statelessSem` -/

/-- Positive: the forward call of `as_mut p` returns `F p`; backward calls that succeed change
nothing. -/
theorem statelessSem_example_forward :
    (statelessSem (fun _ => some 3) (fun _ _ => true) [.asMut 0, .write 0 (.lit 4), .read 0 0]
      (endAt 2)).map (fun ρ => ρ 0) = some 4 := by
  decide

/-- Negative: a failing forward model makes the run fail. -/
theorem statelessSem_example_forward_fails :
    statelessSem (fun _ => none) (fun _ _ => true) [.asMut 0, .read 0 0] (endAt 2) = none := by
  rfl

/-- Negative: a failing backward model makes the run fail at the backward call. -/
theorem statelessSem_example_backward_fails :
    statelessSem (fun _ => some 3) (fun _ _ => false) [.asMut 0, .read 0 0] (endAt 2) = none := by
  rfl

/-- Negative: a stateless model cannot let a raw write influence a later raw read. -/
theorem statelessSem_example_rawWrite_invisible :
    (statelessSem (fun _ => some 3) (fun _ _ => true) [.rawWrite 0 (.lit 9), .rawRead 0 0]
      (endAt 2)).map (fun ρ => ρ 0) = some 3 := by
  decide

/-! ## `prophSem` and `ProphOutcome` -/

/-- Positive: prophesying the true final value satisfies the resolution, and the owner ends up
holding it. -/
theorem prophSem_example_correct_prophecy :
    (prophSem writeOnce (endAt 2) zeroHeap (fun _ => 5)).map (fun r => (r.1.heap 0, r.2)) =
      some (5, true) := by
  decide

/-- Negative: a wrong prophecy violates the resolution assumption. -/
theorem prophSem_example_wrong_prophecy :
    (prophSem writeOnce (endAt 2) zeroHeap (fun _ => 4)).map (fun r => r.2) = some false := by
  decide

/-- Positive: hence the true final state is a prophecy outcome. -/
theorem prophOutcome_example :
    ∃ o, ProphOutcome writeOnce (endAt 2) zeroHeap o ∧ o.heap 0 = 5 :=
  ⟨_, ⟨fun _ => 5, rfl⟩, rfl⟩

/-- Negative: no prophecy assignment satisfying the resolution assumption produces a final cell
other than the written value `5`, so every outcome with a different cell is rejected. -/
theorem prophOutcome_example_neg (o : Obs) (ho : ProphOutcome writeOnce (endAt 2) zeroHeap o) :
    o.heap 0 = 5 := by
  obtain ⟨φ, hφ⟩ := ho
  have e : prophSem writeOnce (endAt 2) zeroHeap φ =
      some (⟨upd zeroHeap 0 (φ 0), fun _ => 0⟩, true && decide ((5 : Int) = φ 0)) := rfl
  rw [e] at hφ
  simp only [Option.some.injEq, Prod.mk.injEq, Bool.true_and, decide_eq_true_eq] at hφ
  obtain ⟨h1, h2⟩ := hφ
  subst h1
  simp [upd, h2]

/-! ## `AliasingDiscipline` -/

/-- Positive: two `as_mut` calls on one pointer, with the first reference dead before the second
is created (`aliasingDiscipline_reborrowAfterWrite`, in `ToyBackward.Programs`). -/
example : AliasingDiscipline (reborrowAfterWrite 7) := aliasingDiscipline_reborrowAfterWrite 7

/-- Negative: a raw write while the reference is still used. -/
theorem not_aliasingDiscipline_rawWriteDuringBorrow : ¬ AliasingDiscipline rawWriteDuringBorrow := by
  decide

/-- Negative: a raw write between a write and a read through the same reference. -/
theorem not_aliasingDiscipline_readAfterRawWrite : ¬ AliasingDiscipline readAfterRawWrite := by
  decide

/-- Negative: an owner read before a write through the reference. -/
theorem not_aliasingDiscipline_ownerReadThenWriteBack :
    ¬ AliasingDiscipline ownerReadThenWriteBack := by
  decide

/-- Scope of the definition (documented limitation): the aliasing discipline does not check
reference scoping. Ill-scoped programs satisfy it and admit liveness-respecting placements, and
they are stuck in the heap semantics and in the unchecked write-back translation; `danglingUse` is
also stuck in the borrow-locking translation (for `useBeforeCreation`, see
`lockSem_none_of_ill_scoped_respectsLiveness`). -/
theorem aliasingDiscipline_admits_ill_scoped :
    (AliasingDiscipline danglingUse ∧ RespectsLiveness danglingUse (endAt 0) ∧
      heapSem danglingUse zeroHeap = none ∧ effSem danglingUse (endAt 0) zeroHeap = none ∧
      lockSem danglingUse (endAt 0) zeroHeap = none) ∧
    (AliasingDiscipline useBeforeCreation ∧
      RespectsLiveness useBeforeCreation (lazyPlacement useBeforeCreation) ∧
      heapSem useBeforeCreation zeroHeap = none ∧
      effSem useBeforeCreation (lazyPlacement useBeforeCreation) zeroHeap = none) :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl⟩, ⟨by decide, by decide, rfl, rfl⟩⟩

/-! ## Placement conditions -/

/-- Positive: the lazy placement of `reborrowAfterWrite` respects all four conditions. -/
theorem respectsLiveness_example :
    RespectsLiveness (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) := by
  decide

/-- Negative: ending region 0 before its write is not liveness-respecting. -/
theorem respectsLiveness_example_neg :
    ¬ RespectsLiveness (reborrowAfterWrite 5) endBeforeWrite := by
  decide

/-- Positive and negative for `EndsAfterCreation`: ending the unused region of `unusedRegion`
before statement 1 is after its creation; ending it before statement 0 is not. -/
theorem endsAfterCreation_examples :
    EndsAfterCreation unusedRegion (endAt 1) ∧ ¬ EndsAfterCreation unusedRegion (endAt 0) := by
  decide

/-- `EndsAfterLastUse` says nothing about unused regions: it holds for `unusedRegion` even with
the region ended before its creation (which `EndsAfterCreation` rejects). -/
theorem endsAfterLastUse_example_unused :
    EndsAfterLastUse unusedRegion (endAt 0) := by
  decide

/-- Negative: ending region 0 before its write violates `EndsAfterLastUse`. -/
theorem endsAfterLastUse_example_neg : ¬ EndsAfterLastUse (reborrowAfterWrite 5) endBeforeWrite := by
  decide

/-- Positive: ending between the last write and a later read satisfies `EndsAfterLastWrite`
(but not `EndsAfterLastUse`). -/
theorem endsAfterLastWrite_example_pos :
    EndsAfterLastWrite (writeThenRead 5) (endAt 2) ∧ ¬ EndsAfterLastUse (writeThenRead 5) (endAt 2) := by
  decide

/-- Negative: ending before the write violates `EndsAfterLastWrite`. -/
theorem endsAfterLastWrite_example_neg : ¬ EndsAfterLastWrite (reborrowAfterWrite 5) endBeforeWrite := by
  decide

/-- Positive and negative for `EndsByNextOwnerAccess`: ending region 0 at the second `asMut` of
the same pointer is allowed; ending it after that `asMut` is not. -/
theorem endsByNextOwnerAccess_examples :
    EndsByNextOwnerAccess (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) ∧
    ¬ EndsByNextOwnerAccess (reborrowAfterWrite 5) endAfterReborrow := by
  decide

/-- Positive and negative for `EndsByProgramEnd`: ending at the program end is allowed, ending
beyond it (never) is not. -/
theorem endsByProgramEnd_examples :
    EndsByProgramEnd writeOnce (endAt 2) ∧ ¬ EndsByProgramEnd writeOnce (endAt 3) := by
  decide

/-! ## Canonical placements -/

/-- Positive: the lazy placement ends region 0 of `reborrowAfterWrite` at the second `asMut`
(index 3) and region 3 at the end of the program; negative: not at index 2. -/
theorem lazyPlacement_example :
    lazyPlacement (reborrowAfterWrite 5) 0 = 3 ∧ lazyPlacement (reborrowAfterWrite 5) 3 = 5 ∧
      lazyPlacement (reborrowAfterWrite 5) 0 ≠ 2 := by
  decide

/-- Positive: the eager placement ends region 0 right after its last use; it differs from the lazy
placement when the owner's next access comes later. -/
theorem eagerPlacement_example :
    eagerPlacement writeThenOtherThenRawRead 0 = 2 ∧ lazyPlacement writeThenOtherThenRawRead 0 = 3 := by
  decide

/-- Negative: the eager placement does not wait for the owner's next access (it does not end
region 0 of `writeThenOtherThenRawRead` before index 3), and a use that precedes the creation does
not pull the end before the creation (region 1 of `useBeforeCreation` ends at 2, not at 1). -/
theorem eagerPlacement_example_neg :
    eagerPlacement writeThenOtherThenRawRead 0 ≠ 3 ∧ eagerPlacement useBeforeCreation 1 = 2 ∧
      eagerPlacement useBeforeCreation 1 ≠ 1 := by
  decide

/-- Positive: pure backward functions coincide with never ending any region. -/
theorem neverEndPlacement_example :
    translate (writeThenRead 5) (neverEndPlacement (writeThenRead 5)) = translatePureBack 0 (writeThenRead 5) :=
  translate_neverEndPlacement _

/-- Negative: the never-ending placement is not a placement that ends regions by the program end,
and it differs from ending the region at the program end. -/
theorem neverEndPlacement_example_neg :
    ¬ EndsByProgramEnd writeOnce (neverEndPlacement writeOnce) ∧
    translate writeOnce (neverEndPlacement writeOnce) ≠ translate writeOnce (endAt 2) := by
  decide

/-! ## Search helpers -/

theorem firstBelow_examples :
    firstBelow (fun j => j == 3) 5 = 3 ∧ firstBelow (fun _ => false) 5 = 5 := by
  decide

theorem lastBelow_examples :
    lastBelow (fun j => j == 3 || j == 1) 7 5 = 3 ∧ lastBelow (fun _ => false) 7 5 = 7 := by
  decide

end Toy.Backward
