import Model
theorem helper (n : Nat) (h : n = modelValue) : n + 1 = 8 := by
  rw [h]; rfl
