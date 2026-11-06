import Heap
open FiniteHeap
def candidate : Cert 3 := (.update ⟨#v[(some 7),(some 11),(some 99)],#v[(some 7),(some 12),(some 99)],#v[none,(some 11),none],#v[(some 7),none,(some 99)],1,11,12⟩)
def acceptDecision : Bool := check candidate && writesOnly 1 candidate && decide (input candidate = meaning before ∧ output candidate = meaning after)
theorem observed : acceptDecision = true := by decide
#print axioms observed
#eval acceptDecision
theorem consumer_frame : Unchanged (meaning before) (meaning after) 1 := by
  have core := certificate_frame candidate 1 (by decide) (by decide)
  have i : input candidate = meaning before := by decide
  have o : output candidate = meaning after := by decide
  simpa only [i,o] using core
#print axioms consumer_frame
