import Proof
example (n : Nat) (h : n = modelValue) : n + 2 = 7 := claim n h
#print axioms claim
