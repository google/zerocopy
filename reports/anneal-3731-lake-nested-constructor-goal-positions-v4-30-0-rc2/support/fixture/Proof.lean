import Dep

theorem nested (h : depValue = 7) : (depValue = 7) ∧ True := by
  constructor
  · have hz : depValue = 7 := by
      exact h
    exact hz
  · trivial
#print axioms nested
#eval depValue
