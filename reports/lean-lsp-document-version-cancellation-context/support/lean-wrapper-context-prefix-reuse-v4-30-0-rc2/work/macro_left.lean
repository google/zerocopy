namespace N
syntax "claim" : term
macro_rules | `(claim) => `(0 = 0)
theorem proof : claim := by rfl
#print N.proof
#print axioms N.proof
end N
