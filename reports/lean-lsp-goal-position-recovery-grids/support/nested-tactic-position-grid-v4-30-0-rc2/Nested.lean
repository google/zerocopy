import Lean

theorem nested (n : Nat) (h : n = 0) : n + 0 = 0 := by
  have hz : n + 0 = 0 := by
    simpa using h
  first
  | trace "🧪"; exact hz
  | exact h

theorem branches (n : Nat) : True ∧ n = n := by
  constructor
  · trivial
  · rfl

theorem term (n : Nat) : n = n := by
  exact Eq.refl n
