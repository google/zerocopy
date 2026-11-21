import MonoShim.MissingEdges

/-!
# Clone ladder: examples and counterexamples
-/

namespace Toy.MonoShim

/-- A ladder without cleanup: clone the fields left to right and nothing else. -/
def ladderNoCleanup : List Ty → Stmt
  | [] => .skip
  | t :: ts => .seq (.clone t) (ladderNoCleanup ts)

/-- `base 0` clones by emitting 1 and drops by emitting 2; `base 1` panics when cloned.
`main` clones a `pair (base 0) (base 1)`. -/
def P3 : Program where
  fns := [⟨false, .clone (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .emit 2)]
  cloneImpls := [(0, .emit 1), (1, .panic)]
  assoc := []

/-- As `P3`, but the destructor of `base 0` panics as well. -/
def P3abort : Program where
  fns := [⟨false, .clone (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .panic)]
  cloneImpls := [(0, .emit 1), (1, .panic)]
  assoc := []

/-- Non-vacuity of the ladder theorem's interesting branches: when the second field's clone
panics, both the ladder and the aggregate drop the first clone (event 2) and keep unwinding;
when that drop panics too, both abort. -/
theorem ladder_cloneAgg_unwind_and_abort_examples :
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (ladder [.base 0, .base 1]) [] st0
      = (.unwind, [], ⟨[1, 2], 0⟩) ∧
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (.cloneAgg [.base 0, .base 1]) [] st0
      = (.unwind, [], ⟨[1, 2], 0⟩) ∧
    execS P3abort.sig (runKey P3abort.sig (srcDef P3abort) 5) (ladder [.base 0, .base 1]) [] st0
      = (.abort, [], ⟨[1], 0⟩) ∧
    execS P3abort.sig (runKey P3abort.sig (srcDef P3abort) 5) (.cloneAgg [.base 0, .base 1]) [] st0
      = (.abort, [], ⟨[1], 0⟩) := by
  decide

/-- Clones of `base 0`, `base 1` emit 1, 2 and the clone of `base 2` panics; the destructors of
`base 0`, `base 1` emit 10, 20. -/
def P3three : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := [(0, .emit 10), (1, .emit 20)]
  cloneImpls := [(0, .emit 1), (1, .emit 2), (2, .panic)]
  assoc := []

/-- A three-field witness for the cleanup order: when the third clone panics, the ladder and the
aggregate clone both drop the clones of fields 1 and 0 in that order (events 20, 10), i.e. in
reverse order of creation. -/
theorem ladder_cloneAgg_three_fields_reverse_cleanup_example :
    execS P3three.sig (runKey P3three.sig (srcDef P3three) 5) (ladder [.base 0, .base 1, .base 2]) []
      st0 = (.unwind, [], ⟨[1, 2, 20, 10], 0⟩) ∧
    execS P3three.sig (runKey P3three.sig (srcDef P3three) 5) (.cloneAgg [.base 0, .base 1, .base 2])
      [] st0 = (.unwind, [], ⟨[1, 2, 20, 10], 0⟩) := by
  decide

/-- **Counterexample 1: a ladder without cleanup is observably different** (a skipped destructor
event, i.e. a leak): it differs from the source aggregate clone on `P3`. -/
theorem ladderNoCleanup_ne_cloneAgg :
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (ladderNoCleanup [.base 0, .base 1]) [] st0
      = (.unwind, [], ⟨[1], 0⟩) ∧
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (ladderNoCleanup [.base 0, .base 1]) [] st0 ≠
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (.cloneAgg [.base 0, .base 1]) [] st0 := by
  decide

/-- **Counterexample 2: a shim whose reference set omits a field type's drop glue can yield a
non-closed target.** With the cleanup-blind edge function, the collected target for `P3` lacks
the drop glue of `base 0`, and the run from `main` calls it. -/
def cfg3 : MonoCfg := ⟨refsNoCleanup P3.sig, synthStd P3⟩
def T3 : List Key := [.userClone 1, .userClone 0, .cloneShim (.pair (.base 0) (.base 1)), .inst 0 []]

theorem ladder_drop_refs_missing_break_closure :
    collect (edgesM P3 cfg3) fifo [.inst 0 []] 10 = some T3 ∧
    ¬ Closed P3.sig (tableM P3 cfg3 T3) T3 ∧
    runM P3 cfg3 T3 4 (.inst 0 []) st0 = (.link (.dropGlue (.base 0)), ⟨[1], 0⟩) ∧
    runS P3 4 (.inst 0 []) st0 = (.unwind, ⟨[1, 2], 0⟩) := by
  decide

end Toy.MonoShim
