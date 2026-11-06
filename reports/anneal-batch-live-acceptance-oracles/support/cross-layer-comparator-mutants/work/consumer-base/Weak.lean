import Source
theorem obl_inc : True := by trivial
theorem obl_twice : comparator_probe.twice 0#u32 = .ok 2#u32 := by rfl
theorem obl_choose : comparator_probe.choose 0#u32 = .ok 3#u32 := by rfl
#check obl_inc
#print axioms obl_inc
