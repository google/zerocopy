import Lean

theorem nested (n : Nat) (h : n = 0) : n + 0 = 0 := by
  have hz : n + 0 = 0 := by
    this_is_not_a_tactic
  exact hz

theorem tail : True := by
  trivial
