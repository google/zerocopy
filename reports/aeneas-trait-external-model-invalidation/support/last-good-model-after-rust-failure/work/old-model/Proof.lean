import Current
example : last_good_probe.inc 0#u32 = .ok 1#u32 := by
  have h : last_good_probe.inc 0#u32 = .ok 1#u32 := rfl
  simpa using h
