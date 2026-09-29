import Lean
theorem checked (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
