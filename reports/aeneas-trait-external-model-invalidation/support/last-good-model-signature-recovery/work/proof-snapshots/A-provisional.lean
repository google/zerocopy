import Current
example : recovery_probe.inc 0#u32 = .ok 1#u32 := by
  have h : recovery_probe.inc 0#u32 = .ok 1#u32 := by rfl
  exact h
