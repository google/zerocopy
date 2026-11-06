import TraitProbe
#check trait_probe.use_step
example : trait_probe.use_step 1#u32 = .ok 2#u32 := by rfl
#check trait_probe.old
#check trait_probe.external_call
