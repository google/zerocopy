import Generated
theorem claim (n : Nat) (h : n = modelValue) : n + 2 = 7 := by
  rw [h]; rfl
-- concurrent harmless note
