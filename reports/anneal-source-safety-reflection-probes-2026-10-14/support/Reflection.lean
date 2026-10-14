import Std

namespace AnnealReflectionProbe

inductive Outcome where
  | returned (value : Nat)
  | ub
  | diverged
  deriving DecidableEq, Repr

abbrev Program := Bool → Outcome

def Safe (p : Program) : Prop := ∀ input, p input ≠ .ub

-- An intentionally explicit ordinary defined-execution preservation contract.
def DefinedPreservation (source model : Program) : Prop :=
  ∀ input, source input ≠ .ub → model input = source input

def FailureReflection (source model : Program) : Prop :=
  ∀ input, source input = .ub → model input = .ub

def brokenSource (input : Bool) : Outcome :=
  if input then .ub else .returned 7

def constantModel (_ : Bool) : Outcome := .returned 7

theorem constant_model_safe : Safe constantModel := by
  intro input
  simp [constantModel]

theorem broken_source_unsafe : ¬ Safe brokenSource := by
  intro h
  have := h true
  simp [brokenSource] at this

theorem ordinary_preservation_holds :
    DefinedPreservation brokenSource constantModel := by
  intro input h
  cases input <;> simp_all [brokenSource, constantModel]

theorem ordinary_preservation_does_not_reflect_safety :
    ¬ (∀ source model : Program,
      DefinedPreservation source model → Safe model → Safe source) := by
  intro h
  exact broken_source_unsafe
    (h brokenSource constantModel ordinary_preservation_holds constant_model_safe)

theorem failure_reflection_transfers_safety {source model : Program}
    (h : FailureReflection source model) (modelSafe : Safe model) : Safe source := by
  intro input sourceBad
  exact modelSafe input (h input sourceBad)

theorem failure_reflection_composes {a b c : Program}
    (hab : FailureReflection a b) (hbc : FailureReflection b c) :
    FailureReflection a c := by
  intro input badA
  exact hbc input (hab input badA)

theorem erased_failure_rejected :
    ¬ FailureReflection brokenSource constantModel := by
  intro h
  have bad := h true (by simp [brokenSource])
  simp [constantModel] at bad

-- Restricting the input domain can make a conditional claim true, but that
-- domain restriction does not justify the unconditional safe-API claim.
def SafeOn (domain : Bool → Prop) (p : Program) : Prop :=
  ∀ input, domain input → p input ≠ .ub

theorem narrowed_domain_is_safe : SafeOn (fun input => input = false) brokenSource := by
  intro input allowed
  subst input
  simp [brokenSource]

#print axioms ordinary_preservation_does_not_reflect_safety
#print axioms failure_reflection_transfers_safety
#print axioms failure_reflection_composes
#print axioms erased_failure_rejected
#print axioms narrowed_domain_is_safe

end AnnealReflectionProbe
