import Current
theorem obl_left_step : nav_ambig.left.step 0#u32 = .ok 1#u32 := by
  trace_state
  rfl
theorem obl_right_step : nav_ambig.right.step 0#u32 = .ok 2#u32 := by
  trace_state
  rfl
theorem obl_both : nav_ambig.both 0#u32 = .ok 3#u32 := by
  trace_state
  rfl
