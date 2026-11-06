import Heap
open FiniteHeap
def candidate : Cert 3 := (.update ⟨#v[(some 7),(some 11),(some 0)],#v[(some 7),(some 12),(some 0)],#v[none,(some 11),none],#v[(some 7),none,(some 0)],1,11,12⟩)
def acceptDecision : Bool := check candidate && writesOnly 1 candidate && decide (input candidate = meaning before ∧ output candidate = meaning after)
theorem observed : acceptDecision = false := by decide
#print axioms observed
#eval acceptDecision
