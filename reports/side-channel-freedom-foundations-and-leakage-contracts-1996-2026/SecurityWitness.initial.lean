import Lean

namespace SecurityWitness

-- A secret Boolean input; no public input. The output is always zero.
def safeModel (_secret : Bool) : Nat × List Bool := (0, [])
def leakySource (secret : Bool) : Nat × List Bool := (0, [secret])
def ValueEq (p q : Bool → Nat × List Bool) : Prop := ∀ s, (p s).1 = (q s).1
def ConstantTime (p : Bool → Nat × List Bool) : Prop := ∀ a b, (p a).2 = (p b).2
def TraceEq (p q : Bool → Nat × List Bool) : Prop := ∀ s, (p s).2 = (q s).2

theorem values_agree : ValueEq leakySource safeModel := by intro s; rfl
theorem model_constant_time : ConstantTime safeModel := by intros; rfl
theorem source_not_constant_time : ¬ ConstantTime leakySource := by
  intro h
  have bad := h false true
  simp [leakySource] at bad

theorem value_equality_does_not_reflect_security :
    ¬ (∀ p q, ValueEq p q → ConstantTime q → ConstantTime p) := by
  intro h
  exact source_not_constant_time (h leakySource safeModel values_agree model_constant_time)

theorem trace_equality_reflects_security (p q : Bool → Nat × List Bool)
    (h : TraceEq p q) (hq : ConstantTime q) : ConstantTime p := by
  intro a b
  exact (h a).trans ((hq a b).trans (h b).symm)

-- The opposite transfer is equally justified only because this specimen has exact
-- per-input trace equality. A one-direction may-refinement is a different proposition.
theorem trace_equality_preserves_security (p q : Bool → Nat × List Bool)
    (h : TraceEq p q) (hp : ConstantTime p) : ConstantTime q := by
  intro a b
  exact (h a).symm.trans ((hp a b).trans (h b))

#print axioms values_agree
#print axioms source_not_constant_time
#print axioms value_equality_does_not_reflect_security
#print axioms trace_equality_reflects_security
#print axioms trace_equality_preserves_security
end SecurityWitness
