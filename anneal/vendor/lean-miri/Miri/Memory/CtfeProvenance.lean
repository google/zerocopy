import Miri.Memory.Pointer

/-!
CTFE's packed provenance from pinned rustc `mir/interpret/pointer.rs`.
The representation is decoded into the same allocation ID and two flags;
the constructor enforces the source's 62-bit ID and immutable⇒shared invariant.
`packed` reconstructs the original u64, including both high bits. This is
separate from Miri's concrete/wildcard provenance, not a substitute for it.
-/

namespace Miri.Memory

inductive CtfeProvenanceError where
  | allocationIdUsesFlagBits
  deriving DecidableEq, Repr

structure CtfeProvenance where
  private mk ::
  allocId : AllocId
  allocIdFits : allocId.value < 4611686018427387904
  immutable : Bool
  sharedRef : Bool
  immutableImpliesShared : immutable = true → sharedRef = true
  deriving DecidableEq, Repr

namespace CtfeProvenance

def fromAllocId (id : AllocId) : Except CtfeProvenanceError CtfeProvenance :=
  if h : id.value < 4611686018427387904 then
    .ok ⟨id, h, false, false, by simp⟩
  else .error .allocationIdUsesFlagBits

def asImmutable (prov : CtfeProvenance) : CtfeProvenance :=
  { prov with immutable := true, sharedRef := true, immutableImpliesShared := by simp }

def asSharedRef (prov : CtfeProvenance) : CtfeProvenance :=
  { prov with sharedRef := true, immutableImpliesShared := by simp }

def intoParts (prov : CtfeProvenance) : AllocId × Bool × Bool :=
  (prov.allocId, prov.immutable, prov.sharedRef)

def fromParts (parts : AllocId × Bool × Bool) : Except CtfeProvenanceError CtfeProvenance := do
  let (id, immutable, sharedRef) := parts
  let prov ← fromAllocId id
  if immutable then return prov.asImmutable
  else if sharedRef then return prov.asSharedRef
  else return prov

/-- The exact two high-bit masks from the source representation. -/
def packed (prov : CtfeProvenance) : UInt64 :=
  prov.allocId.value |||
    (if prov.immutable then 9223372036854775808 else 0) |||
    (if prov.sharedRef then 4611686018427387904 else 0)

private theorem nat_and_high_bit (value bit : Nat) (h : value < 2 ^ bit) :
    value &&& 2 ^ bit = 0 := by
  apply Nat.eq_of_testBit_eq
  intro index
  simp only [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hindex : bit = index
  · subst index
    simp [Nat.testBit_lt_two_pow h]
  · simp [hindex]

/-- Decoding the allocation bits recovers exactly the stored identity.
This uses kernel-checked bitwise lemmas; no native-decide certificate axiom. -/
theorem packed_allocation_bits (prov : CtfeProvenance) :
    prov.packed &&& 4611686018427387903 = prov.allocId.value := by
  rcases prov with ⟨⟨value, nonzero⟩, fits, immutable, shared, compatible⟩
  have fitsNat : value.toNat < 4611686018427387904 := UInt64.lt_iff_toNat_lt.mp fits
  have low : value.toNat &&& 4611686018427387903 = value.toNat :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 62) fitsNat
  cases immutable <;> cases shared <;>
    apply UInt64.toNat_inj.mp <;>
    simp [packed, UInt64.toNat_and, UInt64.toNat_or, Nat.and_or_distrib_right, low]

theorem packed_immutable_bit (prov : CtfeProvenance) :
    (prov.packed &&& 9223372036854775808 ≠ 0) ↔ prov.immutable = true := by
  rcases prov with ⟨⟨value, nonzero⟩, fits, immutable, shared, compatible⟩
  have fitsNat : value.toNat < 4611686018427387904 := UInt64.lt_iff_toNat_lt.mp fits
  have high : value.toNat &&& 9223372036854775808 = 0 :=
    nat_and_high_bit value.toNat 63 (by change value.toNat < 9223372036854775808; omega)
  cases immutable <;> cases shared <;>
    simp only [ne_eq, ← UInt64.toNat_inj] <;>
    simp [packed, UInt64.toNat_and, UInt64.toNat_or, Nat.and_or_distrib_right, high]

theorem packed_shared_bit (prov : CtfeProvenance) :
    (prov.packed &&& 4611686018427387904 ≠ 0) ↔ prov.sharedRef = true := by
  rcases prov with ⟨⟨value, nonzero⟩, fits, immutable, shared, compatible⟩
  have fitsNat : value.toNat < 4611686018427387904 := UInt64.lt_iff_toNat_lt.mp fits
  have high : value.toNat &&& 4611686018427387904 = 0 :=
    nat_and_high_bit value.toNat 62 fitsNat
  cases immutable <;> cases shared <;>
    simp only [ne_eq, ← UInt64.toNat_inj] <;>
    simp [packed, UInt64.toNat_and, UInt64.toNat_or, Nat.and_or_distrib_right, high]

theorem packed_nonzero (prov : CtfeProvenance) : prov.packed ≠ 0 := by
  intro h
  have allocation := prov.packed_allocation_bits
  rw [h] at allocation
  have zero : prov.allocId.value = 0 := by simpa using allocation.symm
  exact prov.allocId.nonzero zero

theorem immutable_is_shared (prov : CtfeProvenance) (h : prov.immutable = true) :
    prov.sharedRef = true := prov.immutableImpliesShared h

theorem asImmutable_sets_both (prov : CtfeProvenance) :
    prov.asImmutable.immutable = true ∧ prov.asImmutable.sharedRef = true := ⟨rfl, rfl⟩

theorem asImmutable_retains_allocation (prov : CtfeProvenance) :
    prov.asImmutable.allocId = prov.allocId := rfl

theorem asSharedRef_retains_allocation (prov : CtfeProvenance) :
    prov.asSharedRef.allocId = prov.allocId := rfl

end CtfeProvenance

instance : PointerProvenance CtfeProvenance where
  offsetIsAddr := false
  wildcard := none
  getAllocId := fun prov => some prov.allocId

def Pointer.provAndRelativeOffset (ptr : Pointer CtfeProvenance) :
    CtfeProvenance × Miri.ABI.Size := ptr.intoRawParts

def Pointer.fromCtfeProvenance (prov : CtfeProvenance) : Pointer CtfeProvenance :=
  .new prov Miri.ABI.Size.ZERO

def Pointer.fromAllocId (id : AllocId) : Except CtfeProvenanceError (Pointer CtfeProvenance) := do
  return .fromCtfeProvenance (← CtfeProvenance.fromAllocId id)

end Miri.Memory
