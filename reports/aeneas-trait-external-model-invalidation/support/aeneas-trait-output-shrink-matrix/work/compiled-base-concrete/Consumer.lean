import TraitProbe
#print axioms trait_probe.external_call
example : trait_probe.external_call 1#u32 = .ok 2#u32 := by rfl
