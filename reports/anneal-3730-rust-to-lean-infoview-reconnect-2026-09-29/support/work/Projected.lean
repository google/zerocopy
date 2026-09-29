import Lean

def helper (n : Nat) : Nat := n + 1
theorem demo (n : Nat) (h : n = 7) : (/- café 🦀 -/ helper n) = 8 := by
  exact ?_
