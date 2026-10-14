import Std
namespace EnumCoherence
-- MiniRust's Known discriminator ignores tag bytes. Both payload types are
-- empty tuples with one padding byte, so both payload decoders return unit.
def payloadEncode : List (Option Nat) := [none]
def tagEncode (d : Nat) : List (Option Nat) := [some d]
def knownZeroDecode (_ : List (Option Nat)) : Option (Nat × Unit) := some (0, ())
def valueEncode (v : Nat × Unit) := tagEncode v.1
def branchChecks : Prop :=
  (1 < 256) ∧ (1 = 1) ∧ (1 ≤ 1) ∧ (0 + 1 ≤ 1) ∧ (0 < 2)
theorem checker_conditions : branchChecks := by unfold branchChecks; decide
theorem known_discriminator_breaks_roundtrip :
    knownZeroDecode (valueEncode (1, ())) ≠ some (1, ()) := by decide
#print axioms checker_conditions
#print axioms known_discriminator_breaks_roundtrip
end EnumCoherence
