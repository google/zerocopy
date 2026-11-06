import Lean

theorem before : True := by
  trivial
#print axioms before

theorem broken : True := by
  tactic_that_does_not_exist

theorem after : True := by
  trivial
#print axioms after
