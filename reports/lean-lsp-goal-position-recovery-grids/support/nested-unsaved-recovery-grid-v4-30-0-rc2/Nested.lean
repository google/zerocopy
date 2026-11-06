import Lean

theorem nested (n : Nat) (h : n = 0) : n + 0 = 0 := by
  have hz : n + 0 = 0 := by
    simpa using h
  exact hz

theorem tail : True := by
  trivial
