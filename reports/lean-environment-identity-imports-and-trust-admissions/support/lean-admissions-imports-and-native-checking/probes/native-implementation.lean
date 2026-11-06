import Lean
def nativeTrue : Bool := true
@[implemented_by nativeTrue]
def logicalFalse : Bool := false
theorem logicalResult : logicalFalse = false := rfl
theorem nativeResult : logicalFalse = true := by native_decide
#print axioms logicalResult
#print axioms nativeResult
