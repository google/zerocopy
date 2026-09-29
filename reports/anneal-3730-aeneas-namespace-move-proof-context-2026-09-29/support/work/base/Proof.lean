import Fixture
theorem caller : move_probe.caller 1#u32 = .ok 2#u32 := by rfl
theorem helper : move_probe.core.use_step 1#u32 = .ok 2#u32 := by rfl
#print axioms caller
#print axioms helper
