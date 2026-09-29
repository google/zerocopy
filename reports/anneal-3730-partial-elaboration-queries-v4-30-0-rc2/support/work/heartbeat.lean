import Lean

theorem before : True := by
  trivial
#print axioms before

set_option maxHeartbeats 1 in
theorem broken (n : Nat) : n + 1 = n + 1 := by
  omega

theorem after : True := by
  trivial
#print axioms after
