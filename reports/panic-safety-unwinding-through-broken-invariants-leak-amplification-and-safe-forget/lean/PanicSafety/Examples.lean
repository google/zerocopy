import PanicSafety.Logical

/-!
# Positive and negative examples for the definitions
-/

namespace Toy.PanicSafety

/-! ## `toks`, `OwnsUniquely`, `Inv` -/

theorem toks_example : toks [some 1, none, some 2] = [1, 2] := by decide

theorem ownsUniquely_pos : OwnsUniquely [] [some 0, some 1] := by decide
theorem ownsUniquely_neg_duplicate : ¬ OwnsUniquely [] [some 0, some 0] := by decide
theorem ownsUniquely_neg_dropped : ¬ OwnsUniquely [0] [some 0] := by decide
theorem ownsUniquely_neg_uninit : ¬ OwnsUniquely [] [none] := by decide

theorem inv_pos : Inv ⟨[some 0, some 1], 2, [], 0, 0⟩ := by decide
/-- Stale bits beyond `len` (here a copy of value `0`) do not matter. -/
theorem inv_pos_staleTail : Inv ⟨[some 0, some 0], 1, [], 0, 0⟩ := by decide
/-- `Inv` ignores the counters. -/
theorem inv_pos_countersDisagree : Inv ⟨[], 0, [], 1, 0⟩ := by decide
theorem inv_neg_lenPastBuffer : ¬ Inv ⟨[some 0], 2, [], 0, 0⟩ := by decide
theorem inv_neg_duplicate : ¬ Inv ⟨[some 0, some 0], 2, [], 0, 0⟩ := by decide
theorem inv_neg_dropped : ¬ Inv ⟨[some 0, some 1], 2, [0], 0, 0⟩ := by decide
theorem inv_neg_uninit : ¬ Inv ⟨[none], 1, [], 0, 0⟩ := by decide

/-! ## Destructor tables -/

theorem noPanickingDtors_pos : NoPanickingDtors noPanicDtors := fun _ => rfl
theorem noPanickingDtors_neg : ¬ NoPanickingDtors dtPanicsOn0 := fun h => absurd (h 0) (by decide)

/-! ## Guards, unwinding, the owner's drop -/

/-- A back-shift guard with `processed = 1`, `deleted = 1`, `original_len = 3` moves cells
`[1, 3)` down by one and sets `len := 2`. -/
theorem backshift_example :
    (backshift 1 1 3).fix [some 9, some 1, some 2] 3 = ([some 1, some 2, some 2], 2) := by decide

theorem unwindEntries_example :
    unwindEntries noPanicDtors [.value 5, .guard (backshift 1 1 2)] ⟨[some 0, some 1], 2, [0], 0, 0⟩ =
      .ok ⟨[some 1, some 1], 1, [5, 0], 0, 0⟩ := by decide

theorem unwindEntries_example_abort :
    unwindEntries dtPanicsOn0 [.value 0] ⟨[], 0, [], 0, 0⟩ = .abort := by decide

theorem containerDrop_pos : containerDrop noPanicDtors ceMem2 = .ok [1, 0] := by decide
theorem containerDrop_neg_doubleDrop :
    containerDrop noPanicDtors ⟨[some 0, some 1], 2, [0], 0, 0⟩ = .ub := by decide
theorem containerDrop_neg_lenPastBuffer :
    containerDrop noPanicDtors ⟨[some 0], 2, [], 0, 0⟩ = .ub := by decide

/-- The two adequacy characterizations `inv_iff_containerDrop_noPanic_ne_ub` and
`unwindEntries_noPanic_ok_inv_iff_dropSafe` fix non-panicking destructors; with the table
`dtPanicsOn0` both fail. A state violating `Inv` whose drop glue aborts (a panicking
destructor) before reaching UB; and a `DropSafe` frame whose unwinding aborts. -/
theorem dropSafety_adequacy_fails_with_panickingDtors :
    (¬ Inv dupMem ∧ containerDrop dtPanicsOn0 dupMem = .abort) ∧
    (DropSafe [.value 0] ⟨[], 0, [], 0, 0⟩ ∧
      unwindEntries dtPanicsOn0 [.value 0] ⟨[], 0, [], 0, 0⟩ = .abort) := by
  decide

/-- Owner's drop with a panicking destructor while a panic is in flight (a double panic):
under the guard, removing value `0`, keeping value `1` and panicking on element `2` unwinds to
the repaired container `[1, 2]` (the guard moved value `2` down); when the owner then drops
it, value `1`'s destructor panics and the run aborts (`containerDrop` maps a destructor panic
to `.abort`; no UB). -/
theorem guardRetain_ownerDrop_doublePanic_aborts_example :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic (dtOf [false, true]) guardRetain ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    Inv ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemoveKeepPanic (dtOf [false, true]) guardRetain ceMem3 = .aborted := by
  decide

/-! ## `DropSafe` -/

/-- A guard can make a frame drop-safe although the container's own fields are broken. -/
theorem dropSafe_pos_guardRepairs :
    ¬ Inv ⟨[some 0, some 1], 2, [0], 0, 0⟩ ∧
    DropSafe [.guard (backshift 1 1 2)] ⟨[some 0, some 1], 2, [0], 0, 0⟩ := by decide

/-- A live local that duplicates a value still owned by the container is not drop-safe. -/
theorem dropSafe_neg_localDuplicates : ¬ DropSafe [.value 0] ceMem1 := by decide

/-- `DropSafe` includes the length bound: with `len` past the buffer, the uniqueness conjunct
holds on the truncated prefix, yet `DropSafe` fails. -/
theorem dropSafe_neg_lenPastBuffer :
    OwnsUniquely [] ((valueToks []).map some ++
      (applyGuards [] ([some 0], 2)).1.take (applyGuards [] ([some 0], 2)).2) ∧
    ¬ DropSafe [] ⟨[some 0], 2, [], 0, 0⟩ := by decide

/-! ## Panic-safety predicates -/

theorem panicSafe_pos : PanicSafe .unwind truncateThenCall := truncateThenCall_panicSafe .unwind

theorem panicSafe_neg : ¬ PanicSafe .unwind truncateLate := truncateLate_counterexample.2.2.2

theorem panicSafe_neg_rawRetain : ¬ PanicSafe .unwind rawRetain := by
  intro h
  have := h ceCbRemoveThenPanic noPanicDtors ceMem2 (by decide)
  revert this
  decide

theorem panicSafeAssumingNoDtorPanic_pos :
    PanicSafeAssumingNoDtorPanic .unwind truncateLate := truncateLate_panicSafeAssumingNoDtorPanic

theorem panicSafeAssumingNoDtorPanic_neg : ¬ PanicSafeAssumingNoDtorPanic .unwind rawRetain := by
  intro h
  have := h ceCbRemoveThenPanic noPanicDtors ceMem2 (fun _ => rfl) (by decide)
  revert this
  decide

theorem callSitesDropSafe_pos : CallSitesDropSafe truncateThenCall :=
  truncateThenCall_callSitesDropSafe

theorem callSitesDropSafe_neg : ¬ CallSitesDropSafe rawRetain := rawRetain_not_callSitesDropSafe

theorem callbackSitesDropSafe_pos : CallbackSitesDropSafe truncateLate :=
  truncateLate_callbackSitesDropSafe

theorem callbackSitesDropSafe_neg : ¬ CallbackSitesDropSafe rawRetain := by
  intro h
  have := h ceCbRemoveThenPanic noPanicDtors ceMem2 (by decide)
  revert this
  decide

/-! ## Abstract retain and the exact specifications -/

theorem specRetain_example :
    specRetain ceCbRemoveKeepPanic noPanicDtors [0, 1, 2] = ⟨[1], [0], [2], .callbackPanic⟩ := by
  decide

theorem specRetain_example_dtorPanic :
    specRetain ceCbRemove dtPanicsOn0 [0, 1] = ⟨[], [0], [1], .dtorPanic⟩ := by decide

theorem retainReturns_pos :
    RetainReturns ⟨[1], [0], [], .finished⟩ ceMem2 ⟨[some 1, some 1], 1, [0], 0, 0⟩ := by decide
theorem retainReturns_neg_wrongDropLog :
    ¬ RetainReturns ⟨[1], [0], [], .finished⟩ ceMem2 ⟨[some 1, some 1], 1, [], 0, 0⟩ := by decide

theorem leakFree_pos : LeakFree ceMem2 ⟨[some 1], 1, [0], 0, 0⟩ := by decide
theorem leakFree_neg : ¬ LeakFree ceMem2 ⟨[some 1], 0, [0], 0, 0⟩ := by decide

/-- The exact specifications are not trivially true: off `Inv` they fail
(`rawRetain_abort_exact_needs_inv`, `leakRetain_unwind_exact_needs_inv`,
`guardRetain_unwind_exact_needs_inv`). On an `Inv` state they hold. Panic branch (remove `0`,
keep `1`, panic on element `2`): -/
theorem rawAbortExact_pos :
    Inv ceMem3 ∧ run .abort ceCbRemoveKeepPanic noPanicDtors rawRetain ceMem3 = .abort ∧
    RawAbortExact ceCbRemoveKeepPanic noPanicDtors ceMem3 := by decide
theorem leakUnwindExact_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors leakRetain ceMem3 =
      .unwound ⟨[some 1, some 1, some 2], 0, [0], 0, 0⟩ ∧
    LeakUnwindExact ceCbRemoveKeepPanic noPanicDtors ceMem3 := by decide
theorem guardUnwindExact_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors guardRetain ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    GuardUnwindExact ceCbRemoveKeepPanic noPanicDtors ceMem3 := by decide

/-- Remove element `0`, keep the rest (no panic). -/
def ceCbRemoveFirst : Callback := tableOf [.ret false, .ret true, .ret true]

/-- Normal-return branch of the exact specifications: removing `0` and keeping `1, 2` returns
the container `[1, 2]` with `0` dropped, for all three implementations. -/
theorem rawAbortExact_return_pos :
    Inv ceMem3 ∧
    run .abort ceCbRemoveFirst noPanicDtors rawRetain ceMem3 =
      .ret ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    RawAbortExact ceCbRemoveFirst noPanicDtors ceMem3 := by decide
theorem leakUnwindExact_return_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveFirst noPanicDtors leakRetain ceMem3 =
      .ret ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    LeakUnwindExact ceCbRemoveFirst noPanicDtors ceMem3 := by decide
theorem guardUnwindExact_return_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveFirst noPanicDtors guardRetain ceMem3 =
      .ret ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    GuardUnwindExact ceCbRemoveFirst noPanicDtors ceMem3 := by decide

/-! ## Logical invariant -/

theorem countersAgree_pos : CountersAgree ⟨[], 0, [], 2, 2⟩ := by decide
theorem countersAgree_neg : ¬ CountersAgree ⟨[], 0, [], 1, 0⟩ := by decide

/-! ## Client language -/

theorem clientRun_rejected_example : clientRun .leakAmplified [.next] ceMem1 = .rejected := by
  decide

theorem clientRun_drainTwice_rejected :
    clientRun .destructorReliant [.drain, .drain] ceMem1 = .rejected := by decide

end Toy.PanicSafety
