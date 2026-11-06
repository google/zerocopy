import Current
theorem nav_inc : bundle_golden.inc 0#u32 = .ok 1#u32 := by
  trace_state
  rfl
theorem nav_twice : bundle_golden.twice 0#u32 = .ok 2#u32 := by
  trace_state
  rfl
theorem nav_choose : bundle_golden.choose 0#u32 = .ok 3#u32 := by
  trace_state
  rfl
