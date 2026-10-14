import Lean
theorem ordinary : 1 + 1 = 2 := by decide
theorem localHyp (h : False) : False := h
axiom assumedFalse : False
private def concealedFalse : False := assumedFalse
theorem viaHelper : False := concealedFalse
#print axioms ordinary
#print axioms localHyp
#print axioms viaHelper
