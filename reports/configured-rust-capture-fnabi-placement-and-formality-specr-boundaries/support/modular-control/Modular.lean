import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace Modular
abbrev Byte := Fin 256
structure Dictionary where
  modulus : Nat
  bias : Nat
  deriving DecidableEq, Repr
-- Target/associated-type implementation chooses executable arithmetic, not a tag.
def callee (d : Dictionary) (x : Byte) : Nat := (x.val + d.bias) % d.modulus
def caller (d : Dictionary) (x : Byte) : Nat := callee d x + 3
def expected (x : Byte) : Nat := (x.val + 1) % 256
inductive Contract where | exact | narrowed | weakened deriving DecidableEq, Repr
def pre : Contract → Byte → Prop
  | .narrowed, x => x.val < 255
  | _, _ => True
def post : Contract → Byte → Nat → Prop
  | .weakened, _, _ => True
  | _, x, y => y = expected x
instance (c : Contract) (x : Byte) : Decidable (pre c x) := by cases c <;> unfold pre <;> infer_instance
instance (c : Contract) (x : Byte) (y : Nat) : Decidable (post c x y) := by cases c <;> unfold post <;> infer_instance
structure CalleeCertificate (d : Dictionary) (c : Contract) : Prop where
  holds : ∀ x, pre c x → post c x (callee d x)
def Covered (c : Contract) : Prop := ∀ x, pre c x
-- Independent caller obligation, not generated from the proposed contract.
def Adequate (c : Contract) : Prop := ∀ x y, post c x y → y = expected x
theorem compose (d : Dictionary) (c : Contract) (certificate : CalleeCertificate d c)
    (coverage : Covered c) (adequacy : Adequate c) :
    ∀ x, caller d x = expected x + 3 := by
  intro x
  unfold caller
  rw [adequacy x _ (certificate.holds x (coverage x))]
def good : Dictionary := ⟨256,1⟩
def changedImplementation : Dictionary := ⟨256,2⟩
def target16 : Dictionary := ⟨65536,1⟩
def associatedNibble : Dictionary := ⟨16,1⟩
def foreignVtable : Dictionary := ⟨256,0⟩
theorem good_certificate : CalleeCertificate good .exact := ⟨by intro x _; rfl⟩
theorem exact_coverage : Covered .exact := by intro x; trivial
theorem exact_adequacy : Adequate .exact := by intro x y h; exact h
theorem accepted_composition : ∀ x, caller good x = expected x + 3 :=
  compose good .exact good_certificate exact_coverage exact_adequacy
theorem changed_implementation_fails : caller changedImplementation 0 ≠ expected 0 + 3 := by decide
theorem target_substitution_fails : caller target16 255 ≠ expected 255 + 3 := by decide
theorem associated_type_substitution_fails : caller associatedNibble 15 ≠ expected 15 + 3 := by decide
theorem dynamic_substitution_fails : caller foreignVtable 0 ≠ expected 0 + 3 := by decide
theorem narrowed_certificate : CalleeCertificate good .narrowed := ⟨by intro x _; rfl⟩
theorem narrowed_coverage_fails : ¬ Covered .narrowed := by
  intro h
  exact (by decide : ¬ pre .narrowed (255 : Byte)) (h 255)
theorem weakened_certificate : CalleeCertificate changedImplementation .weakened := ⟨by intro x _; trivial⟩
theorem weakened_adequacy_fails : ¬ Adequate .weakened := by
  intro h
  have bad := h 0 999 (by trivial)
  contradiction
-- New evidence for a changed body can legitimately establish a changed claim.
def updatedExpected (x : Byte) := (x.val+2)%256
theorem legitimate_relink : ∀ x, caller changedImplementation x = updatedExpected x + 3 := by intro x; rfl
#print axioms compose
#print axioms accepted_composition
#print axioms changed_implementation_fails
#print axioms target_substitution_fails
#print axioms associated_type_substitution_fails
#print axioms dynamic_substitution_fails
#print axioms narrowed_coverage_fails
#print axioms weakened_adequacy_fails
#print axioms legitimate_relink
end Modular
