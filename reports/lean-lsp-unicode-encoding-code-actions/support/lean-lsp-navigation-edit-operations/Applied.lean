theorem renamed_demo (α : Nat) (hα : α = 0) : α = 0 := by
  exact hα

#check renamed_demo

theorem completion_demo (β : Nat) (hβ : β = 0) : β = 0 := by
  exact hβ
