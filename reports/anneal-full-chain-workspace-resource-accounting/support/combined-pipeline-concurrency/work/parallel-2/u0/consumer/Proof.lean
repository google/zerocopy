import Current
theorem obl_inc : pipeline_workload.inc 0#u32 = .ok 1#u32 := by rfl
#print axioms obl_inc
theorem obl_twice : pipeline_workload.twice 0#u32 = .ok 2#u32 := by rfl
#print axioms obl_twice
theorem obl_choose : pipeline_workload.choose 0#u32 = .ok 3#u32 := by rfl
#print axioms obl_choose
