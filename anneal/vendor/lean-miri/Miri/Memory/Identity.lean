import Std

/-!
Allocation and borrow identities from the pinned rustc/Miri sources.
`AllocId` is a nonzero u64 (`mir/interpret/mod.rs`); `BorTag` is a distinct
nonzero u64 (`borrow_tracker/mod.rs`). No address or validity is inferred from
either identity. Allocation liveness belongs to the allocation state.
-/

namespace Miri.Memory

structure AllocId where
  value : UInt64
  nonzero : value ≠ 0
  deriving DecidableEq, Repr

namespace AllocId

def ofUInt64 (value : UInt64) : Option AllocId :=
  if h : value = 0 then none else some ⟨value, h⟩

theorem zero_is_rejected : ofUInt64 0 = none := by
  simp [ofUInt64]

theorem constructed_value {value : UInt64} {id : AllocId}
    (h : ofUInt64 value = some id) : id.value = value := by
  unfold ofUInt64 at h
  split at h
  · contradiction
  · cases h
    rfl

end AllocId

structure BorTag where
  value : UInt64
  nonzero : value ≠ 0
  deriving DecidableEq, Repr

namespace BorTag

def ofUInt64 (value : UInt64) : Option BorTag :=
  if h : value = 0 then none else some ⟨value, h⟩

def one : BorTag := ⟨1, by decide⟩

instance : Inhabited BorTag := ⟨one⟩

/-- Source `NonZero<u64>::checked_add(1)` preserves overflow as `None`. -/
def succ (tag : BorTag) : Option BorTag :=
  if tag.value = 18446744073709551615 then none
  else ofUInt64 (tag.value + 1)

theorem zero_is_rejected : ofUInt64 0 = none := by
  simp [ofUInt64]

theorem max_has_no_successor (h : tag.value = 18446744073709551615) :
    succ tag = none := by simp [succ, h]

end BorTag

/-- Pinned Miri `machine::Provenance`. Wildcard is distinct from no provenance. -/
inductive Provenance where
  | concrete (allocId : AllocId) (tag : BorTag)
  | wildcard
  deriving DecidableEq, Repr

namespace Provenance

def offsetIsAddr : Bool := true
def wildcardProvenance : Option Provenance := some .wildcard

def getAllocId : Provenance → Option AllocId
  | .concrete id _ => some id
  | .wildcard => none

theorem wildcard_has_no_fixed_allocation : getAllocId .wildcard = none := rfl

theorem concrete_retains_allocation (id : AllocId) (tag : BorTag) :
    getAllocId (.concrete id tag) = some id := rfl

end Provenance

/-- The semantic members of rustc's `interpret::Provenance` trait. The
formatting callback is diagnostic-only. Implementations are fixed by the
library for each concrete engine provenance type. -/
class PointerProvenance (Prov : Type u) where
  offsetIsAddr : Bool
  wildcard : Option Prov
  getAllocId : Prov → Option AllocId

instance : PointerProvenance Provenance where
  offsetIsAddr := true
  wildcard := some .wildcard
  getAllocId := Provenance.getAllocId

instance : PointerProvenance AllocId where
  offsetIsAddr := false
  wildcard := none
  getAllocId := some

/-- The extra information from Miri's `machine::ProvenanceExtra`. -/
inductive ProvenanceExtra where
  | concrete (tag : BorTag)
  | wildcard
  deriving DecidableEq, Repr

def ProvenanceExtra.andThen (extra : ProvenanceExtra) (f : BorTag → Option α) : Option α :=
  match extra with
  | .concrete tag => f tag
  | .wildcard => none

end Miri.Memory
