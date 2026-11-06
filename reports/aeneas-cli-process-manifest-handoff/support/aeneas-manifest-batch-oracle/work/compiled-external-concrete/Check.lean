import External
#eval oracle_probe.call 1#u32
#print axioms oracle_probe.call
example : oracle_probe.call 1#u32 = .ok 2#u32 := by rfl
