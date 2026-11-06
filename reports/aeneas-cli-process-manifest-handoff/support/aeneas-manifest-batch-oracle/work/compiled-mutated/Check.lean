import Mutated
#eval oracle_probe.inc 0#u32
#eval oracle_probe.twice 0#u32
example : oracle_probe.inc 0#u32 = .ok 2#u32 := by rfl
example : oracle_probe.twice 0#u32 = .ok 4#u32 := by rfl
#print axioms oracle_probe.inc
