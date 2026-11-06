import Current
theorem obl_inc : golden_vertical.inc 0#u32 = .ok 2#u32 := by rfl
#print axioms obl_inc
theorem obl_twice : golden_vertical.twice 0#u32 = .ok 4#u32 := by rfl
#print axioms obl_twice
theorem obl_choose : golden_vertical.choose 0#u32 = .ok 5#u32 := by rfl
#print axioms obl_choose
