def modelValue : Nat := 7
theorem helper (n : Nat) (h : n = modelValue) : n + 1 = 8 := by
  rw [h]; rfl
