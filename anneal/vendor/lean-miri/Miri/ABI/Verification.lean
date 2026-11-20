import Miri.ABI.Size

/-! Proofs directly about the checked size arithmetic. -/

namespace Miri.ABI.Verification

/-- Every successful target-bounded addition is below the exclusive object-size bound. -/
theorem checkedAdd_success_below_bound {α : Type} [HasDataLayout α]
    (size offset : Size) (cx : α) :
    ∀ value, Size.checkedAdd size offset cx = some value →
      value.bytes < (HasDataLayout.dataLayout cx).objSizeBound := by
  intro value h
  by_cases hover : size.bytes + offset.bytes < size.bytes
  · simp [Size.checkedAdd, hover] at h
  · by_cases hbound : size.bytes + offset.bytes <
        (HasDataLayout.dataLayout cx).objSizeBound
    · simp [Size.checkedAdd, hover, hbound] at h
      cases h
      exact hbound
    · simp [Size.checkedAdd, hover, hbound] at h

/-- A 16-bit target rejects a result equal to its 2^15-byte exclusive bound. -/
theorem checkedAdd_rejects_obj_size_bound_16 :
    Size.checkedAdd (Size.ofBytes 32767) (Size.ofBytes 1)
      ({ endian := .little, pointerWidth := .w16 } : TargetDataLayout) = none := by
  decide

end Miri.ABI.Verification
