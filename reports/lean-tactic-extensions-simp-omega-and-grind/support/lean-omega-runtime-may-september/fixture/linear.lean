import Lean.Elab.Tactic.Omega

example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by omega
example (a b : Int) (h : a + 3 = b) : b - a = 3 := by omega
example (a b : Nat) (h : a = b) : a ≠ b + 1 := by omega
example (a : Nat) (h : 3 ∣ a) : a % 3 = 0 := by omega
example (a b : Nat) : a - b ≤ a := by omega
example (a b : Int) : min a b ≤ a := by omega
example (a : Int) : 0 ≤ Int.natAbs a := by omega

-- The same nonlinear expression can be an opaque atom in a linear relation.
example (a b : Nat) (h : a * b ≤ 5) : a * b ≤ 6 := by omega
