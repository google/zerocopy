import Model
theorem helper (n : Nat) (h : n = modelValue) : n + 1 = 8 := by
  rw [h]; rfl
theorem claimOne (n : Nat) (h : n = modelValue) : n + 1 = 8 := by
  exact ?_
theorem claimTwo (n : Nat) (h : n = modelValue) : n + 1 = 8 := by
  exact helper n h
