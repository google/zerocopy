import Fixture
theorem caller : trait_reuse.core.use_step 1#u32 = .ok 2#u32 := by rfl
theorem combined : trait_reuse.combine 1#u32 = .ok 13#u32 := by rfl
theorem side : trait_reuse.side.untouched 1#u32 = .ok 11#u32 := by rfl
#print axioms caller
#print axioms combined
#print axioms side
