import Lean

theorem left : True := by
  trivial

theorem right : True := by
  trivial

theorem combined : True ∧ True := by
  constructor
  · trivial
  · trivial
