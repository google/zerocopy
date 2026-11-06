import Current
theorem goal_inc : pipeline_workload.inc 0#u32 = .ok 1#u32 := by
  trace_state
  rfl
#print axioms goal_inc
