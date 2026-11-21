import PanicSafety.Facts

/-!
# Bounded-check infrastructure

Enumerations used by fully proved, explicitly bounded checks (`*_upTo*` theorems). A
bounded check covers the listed container sizes, the listed entry states, and every
callback/destructor table that is determined by its values on the first few invocations
(later callback invocations return `true`, tokens beyond the list have non-panicking
destructors). A bounded check establishes the stated property on the listed finite family;
it neither establishes nor refutes the corresponding unbounded statement.
-/

namespace Toy.PanicSafety

/-- All behaviour lists of length `k`. -/
def allBehs : Nat → List (List Beh)
  | 0 => [[]]
  | k + 1 => (allBehs k).flatMap fun l => [Beh.ret true :: l, Beh.ret false :: l, Beh.panic :: l]

/-- All boolean lists of length `k`. -/
def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBools k).flatMap fun l => [true :: l, false :: l]

/-- The callback table that follows `bs` and then returns `true`. -/
def tableOf (bs : List Beh) : Callback := fun j => bs.getD j (.ret true)

/-- The destructor table that follows `ds` on tokens `0, 1, …` and is non-panicking beyond. -/
def dtOf (ds : List Bool) : DtorTable := fun t => ds.getD t false

/-- Entry states of size `n` used by bounded checks: tokens `0, …, n-1` in order, exact
capacity and empty drop log; and the same with one extra stale cell holding an
already-dropped value `99` beyond `len`. -/
def testMems (n : Nat) : List Mem :=
  [⟨(List.range n).map some, n, [], 0, 0⟩,
   ⟨(List.range n).map some ++ [some 99], n, [99], 0, 0⟩]

theorem testMems_inv : ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, Inv m := by decide

end Toy.PanicSafety
