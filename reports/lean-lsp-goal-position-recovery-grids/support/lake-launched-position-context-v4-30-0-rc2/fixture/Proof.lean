import Dep

theorem positioned (n : Nat) (h : n = depValue) : n + 0 = depValue := by
  have hz : n + 0 = depValue := by
    simpa using h
  exact hz
#print axioms positioned
#eval depValue
