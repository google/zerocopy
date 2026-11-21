/-!
# Observations of the real Lean printer and elaborator

This module records, as build-checked observations, how the pinned Lean toolchain
prints and elaborates the statements used as running examples in `Toy.Render`.
Each `#guard_msgs` block fails the build if the printed output changes. These are
observations of one toolchain on these inputs, under default options except where a
`set_option` line names an option, not theorems about Lean; they neither establish
nor refute claims about other inputs, options or versions, and nothing in `Toy.Render`
is claimed to model Lean's printer or elaborator.
-/

/-! ## Numeral types are elided by default -/

/-- info: 2 - 3 = 0 : Prop -/
#guard_msgs in
#check ((2 : Int) - 3 = 0)

/-- info: 2 - 3 = 0 : Prop -/
#guard_msgs in
#check ((2 : Nat) - 3 = 0)

-- The two statements above have different truth values.
example : (2 : Nat) - 3 = 0 := by decide
example : ¬ ((2 : Int) - 3 = 0) := by decide

/-- info: (2 : Int) - (3 : Int) = (0 : Int) : Prop -/
#guard_msgs in
set_option pp.numericTypes true in
#check ((2 : Int) - 3 = 0)

/-! ## Coercions are shown (as `↑`) by default -/

/-- info: fun a b => ↑(a - b) = ↑a - ↑b : Nat → Nat → Prop -/
#guard_msgs in
#check fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)

/-- info: fun a b => (a - b).cast = a.cast - b.cast : Nat → Nat → Prop -/
#guard_msgs in
set_option pp.coercions false in
#check fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)

/-! ## The elaborator places coercions at the leaves of an arithmetic tree -/

/-- info: fun a b z => ↑a - ↑b = z : Nat → Nat → Int → Prop -/
#guard_msgs in
#check fun (a b : Nat) (z : Int) => a - b = z

example (a b : Nat) : ((a - b : Int)) = (a : Int) - (b : Int) := rfl

/-! ## `pp.analyze` adds an annotation it deems needed for re-elaboration -/

/-- info: fun a b => ↑(a - b) = HSub.hSub (α := Int) ↑a ↑b : Nat → Nat → Prop -/
#guard_msgs in
set_option pp.analyze true in
#check fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)

/-! ## `pp.analyze` does not always add the annotation that separates a collision

With `pp.analyze` enabled, the `Int` statement of the numeral collision above still
prints without any numeral type, exactly like the `Nat` statement. (The option's
documentation in `TopDownAnalyze.lean` states that the analysis is "neither sound
nor complete".) -/

/-- info: 2 - 3 = 0 : Prop -/
#guard_msgs in
set_option pp.analyze true in
#check ((2 : Int) - 3 = 0)
