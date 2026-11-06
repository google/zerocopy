import Source
theorem obl_inc : comparator_probe.inc 0#u32 = .ok 2#u32 := by rfl
#check obl_inc
#print axioms obl_inc
theorem obl_twice : comparator_probe.twice 0#u32 = .ok 4#u32 := by rfl
#check obl_twice
#print axioms obl_twice
theorem obl_choose : comparator_probe.choose 0#u32 = .ok 5#u32 := by rfl
#check obl_choose
#print axioms obl_choose
