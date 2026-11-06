import Lean

theorem left : True := by
  simp

theorem right : True := by
  simp

theorem combined : True ∧ True := by
  constructor
  · simp
  · trivial
