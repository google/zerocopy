/-
Direct use of the in-kernel native-reduction axiom `Lean.ofReduceBool`
(deprecated since 2026-02-01 in v4.29.x; absent in later releases).
-/
set_option linter.deprecated false

def k : Bool := 2 ^ 20 % 7 == 4
theorem R : k = true := Lean.ofReduceBool k true rfl

def flagImpl (_ : Nat) : Bool := true
@[implemented_by flagImpl] def flag (_ : Nat) : Bool := false
def kFlag : Bool := flag 0
-- kernel reduction of the logical body
theorem RE1 : kFlag = false := rfl
-- in-kernel native reduction runs the implementation instead
theorem RE2 : kFlag = true := Lean.ofReduceBool kFlag true rfl
theorem RE3 : False := by
  have h1 := RE1
  have h2 := RE2
  rw [h1] at h2
  exact Bool.false_ne_true h2

-- the tactic path on the same toolchain
theorem N : 2 ^ 20 % 7 = 4 := by native_decide

#print axioms R
#print axioms RE3
#print axioms N
#print axioms Lean.ofReduceBool
