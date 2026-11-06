import AnnOne
theorem claimTwo (n : Nat) (h : n = modelValue) : n + 1 = 8 := by
  exact claimOne n h
