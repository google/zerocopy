/-
Assumption-recording probe, downstream file: imports the compiled
`Probe.Base` module (.olean) and re-queries the imported declarations.
-/
import Probe.Base

#print axioms A
#print axioms B
#print axioms C
#print axioms D
#print axioms E2
#print axioms E3
#print axioms F

-- H: a new theorem in the downstream file that depends on F.
theorem H : twoPow20Mod7 = 4 := F.1
#print axioms H
