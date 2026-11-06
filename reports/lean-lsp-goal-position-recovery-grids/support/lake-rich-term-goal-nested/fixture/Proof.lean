import Dep

theorem nested_term : depValue = depValue := by
  exact Eq.trans (Eq.refl depValue) (Eq.refl depValue)
#print axioms nested_term
#eval depValue
