/-
Assumption-recording probe, upstream module.
Each theorem depends on a different kind of unchecked or checked evidence;
`#print axioms` is run on each one at the end of this file.
-/

-- A: native evaluation (compiled code decides the proposition).
theorem A : 2 ^ 20 % 7 = 4 := by native_decide

-- B: the same proposition decided by kernel reduction.
theorem B : 2 ^ 20 % 7 = 4 := by decide

-- C: an incomplete proof.
theorem C : 1 + 1 = 3 := sorry

-- D: a user axiom.
axiom myAx : 2 + 2 = 5
theorem D : 2 + 2 = 5 := myAx

-- E: a definition whose compiled implementation disagrees with its logical body.
def flagImpl (_ : Nat) : Bool := true
@[implemented_by flagImpl] def flag (_ : Nat) : Bool := false
-- E1: kernel reduction sees the logical body.
theorem E1 : flag 0 = false := rfl
-- E2: native evaluation runs the implementation instead.
theorem E2 : flag 0 = true := by native_decide
-- E3: the two together give False.
theorem E3 : False := by
  have h1 := E1
  have h2 := E2
  rw [h1] at h2
  exact Bool.false_ne_true h2

-- F: depends on A transitively through an ordinary definition and theorem.
def twoPow20Mod7 : Nat := 2 ^ 20 % 7
theorem F0 : twoPow20Mod7 = 4 := A
theorem F : twoPow20Mod7 = 4 ∧ True := ⟨F0, trivial⟩

-- G: classical reasoning, for the standard-axiom baseline.
theorem G (p : Prop) : p ∨ ¬ p := Classical.em p

#print axioms A
#print axioms B
#print axioms C
#print axioms D
#print axioms E1
#print axioms E2
#print axioms E3
#print axioms F
#print axioms G
