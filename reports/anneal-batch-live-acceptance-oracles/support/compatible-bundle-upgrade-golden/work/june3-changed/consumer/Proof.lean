import Current
theorem obl_inc : bundle_golden.inc 0#u32 = .ok 2#u32 := by rfl
#print axioms obl_inc
theorem obl_twice : bundle_golden.twice 0#u32 = .ok 4#u32 := by rfl
#print axioms obl_twice
theorem obl_choose : bundle_golden.choose 0#u32 = .ok 5#u32 := by rfl
#print axioms obl_choose
