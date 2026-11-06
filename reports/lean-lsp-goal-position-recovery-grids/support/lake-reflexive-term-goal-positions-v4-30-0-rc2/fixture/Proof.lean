import Dep

theorem term_proof : depValue = depValue := by
  exact Eq.refl depValue
#print axioms term_proof
#eval depValue
