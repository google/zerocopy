import PanicSafety.Forget

/-!
# Panic safety (memory) does not imply preservation of a logical invariant on unwind

A purely logical invariant (two counters that should agree) can be broken by a panic in an
operation that is panic-safe under `unwind` (memory safety), with no UB. In contrast, the
memory-safety invariant `Inv` must hold on every unwound state handed to the owner when no
destructor panics (`inv_iff_containerDrop_noPanic_ne_ub`: an unwound state violating `Inv`
makes the owner's drop glue reach UB).

`catch_unwind` and the `UnwindSafe` marker are not modelled.
-/

namespace Toy.PanicSafety

/-- Increment `ctrA`, call user code, increment `ctrB`. -/
def bumpBoth : Prog := .bumpA (.call fun _ => .bumpB .done)

/-- The logical invariant: the two counters agree. -/
def CountersAgree (m : Mem) : Prop := m.ctrA = m.ctrB

instance (m : Mem) : Decidable (CountersAgree m) := by unfold CountersAgree; infer_instance

/-- Separation: `bumpBoth` is panic-safe under `unwind` (memory safety), yet some run from
a state satisfying `Inv` and `CountersAgree` unwinds to a state violating `CountersAgree`. -/
theorem panicSafe_unwind_but_countersAgree_broken :
    PanicSafe .unwind bumpBoth ∧
    ∃ (cb : Callback) (dt : DtorTable) (m m' : Mem),
      Inv m ∧ CountersAgree m ∧ run .unwind cb dt bumpBoth m = .unwound m' ∧
      ¬ CountersAgree m' := by
  refine ⟨?_, tableOf [.panic], noPanicDtors, ceMem1, ⟨[some 0], 1, [], 1, 0⟩, by decide⟩
  intro cb dt m hm
  unfold run
  simp only [exec, bumpBoth]
  cases cb 0 <;> simp [panicFrom, unwindEntries, ResOk] <;>
    exact ⟨hm.1, hm.2⟩

/-- Non-vacuity witness for the separation: a panicking callback on the one-element
container. -/
theorem bumpBoth_unwind_example :
    Inv ceMem1 ∧ CountersAgree ceMem1 ∧
    run .unwind (tableOf [.panic]) noPanicDtors bumpBoth ceMem1 =
      .unwound ⟨[some 0], 1, [], 1, 0⟩ ∧
    Inv ⟨[some 0], 1, [], 1, 0⟩ ∧ ¬ CountersAgree ⟨[some 0], 1, [], 1, 0⟩ := by
  decide

/-- Counterexample (the entry `Inv` inside `PanicSafe .unwind bumpBoth` cannot be dropped):
from `dupMem`, which violates `Inv`, a run that returns normally returns a state violating
`Inv`. -/
theorem bumpBoth_needs_inv :
    ¬ Inv dupMem ∧ ¬ ResOk (run .unwind (tableOf []) noPanicDtors bumpBoth dupMem) := by
  decide

/-! ## Bounded check of the call-site characterization on sample programs -/

/-- The finite family used by `characterization_bounded_samples`: sizes `0..2`, entry
states `testMems n`, callback tables determined by the first `n + 1` invocations, destructor
tables determined by tokens `0..n-1`. -/
def charFamily : List (Callback × DtorTable × Mem) :=
  [0, 1, 2].flatMap fun n => (testMems n).flatMap fun m =>
    (allBehs (n + 1)).flatMap fun bs => (allBools n).map fun ds => (tableOf bs, dtOf ds, m)

/-- `PanicSafe` restricted to `charFamily`. -/
def BoundedPanicSafe (mode : Mode) (p : Prog) : Prop :=
  ∀ x ∈ charFamily, ResOk (run mode x.1 x.2.1 p x.2.2)

instance (mode : Mode) (p : Prog) : Decidable (BoundedPanicSafe mode p) := by
  unfold BoundedPanicSafe; infer_instance

/-- `CallSitesDropSafe` restricted to `charFamily`. -/
def BoundedCallSitesDropSafe (p : Prog) : Prop :=
  ∀ x ∈ charFamily, ∀ s ∈ sites x.1 x.2.1 p x.2.2, DropSafe s.entries s.mem

instance (p : Prog) : Decidable (BoundedCallSitesDropSafe p) := by
  unfold BoundedCallSitesDropSafe; infer_instance

/-- The sample programs of this package. -/
def samplePrograms : List Prog :=
  [rawRetain, leakRetain, guardRetain, guardRetainLate, drainWith, truncateLate,
   truncateThenCall, badSetLen, bumpBoth]

set_option maxRecDepth 100000 in
/-- Bounded check: on every sample program, the restriction of both sides of
`panicSafe_unwind_iff_abort_and_callSitesDropSafe` to `charFamily` agree. -/
theorem characterization_bounded_samples :
    ∀ p ∈ samplePrograms,
      (BoundedPanicSafe .unwind p ↔ BoundedPanicSafe .abort p ∧ BoundedCallSitesDropSafe p) := by
  decide

set_option maxRecDepth 100000 in
/-- The bounded check is not vacuous: `rawRetain` passes the `abort` side but fails the site
side; `badSetLen` fails the `abort` side but passes the site side; `guardRetain` passes the
site side and is panic-safe under `unwind` on the family. -/
theorem characterization_bounded_samples_nontrivial :
    BoundedPanicSafe .abort rawRetain ∧ ¬ BoundedCallSitesDropSafe rawRetain ∧
    ¬ BoundedPanicSafe .abort badSetLen ∧ BoundedCallSitesDropSafe badSetLen ∧
    BoundedPanicSafe .unwind guardRetain ∧ BoundedCallSitesDropSafe guardRetain := by
  decide

end Toy.PanicSafety
