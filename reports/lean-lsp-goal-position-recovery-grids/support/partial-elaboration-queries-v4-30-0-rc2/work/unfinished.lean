import Lean

theorem before : True := by
  trivial
#print axioms before

theorem broken : True := by
  exact ?_

theorem after : True := by
  trivial
#print axioms after
