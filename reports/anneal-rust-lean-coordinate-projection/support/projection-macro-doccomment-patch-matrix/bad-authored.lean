import Lean

theorem left : True := by
  missingProof

theorem right : True := by
  missingProof

theorem combined : True ∧ True := by
  constructor
  · trivial
  · trivial
