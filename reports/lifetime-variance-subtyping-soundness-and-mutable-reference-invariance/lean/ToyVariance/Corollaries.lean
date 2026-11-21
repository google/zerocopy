import ToyVariance.Results

/-!
# Tightness corollaries

The tightness witnesses for the hypotheses `hv` of `rustTable_entry_not_le_admits_dangling` and
`bodyRule_not_le_inferVar_admits_dangling_of_dataBody` state the failure of the conclusion as
`¬ AdmitsDanglingAccess`. The two lemmas below record that the same instances are also sound, so
the bundled corollaries `rustTable_entry_not_le_unsound` and
`bodyRule_not_le_inferVar_unsound_of_dataBody` fail there as well.
-/

namespace Toy.Variance

/-- The Rust entry itself (`p = refMutTy`, `v = inv`) gives a sound table. -/
theorem rustTable_entry_le_sound :
    Pos.refMutTy ≠ .phantom ∧ Variance.inv.le (rustTable .refMutTy) = true ∧
      Sound (SubGen (rustTable.set .refMutTy .inv) NoAx) :=
  ⟨by decide, rfl, (rustTable_entry_sound_iff .refMutTy (by decide) .inv).2 rfl⟩

/-- For the data body `&'static mut T`, the body rule at the inferred variance `inv` is sound. -/
theorem bodyRule_refMut_inv_sound :
    (Ty.refMut .static .param).dataBody = true ∧
      Variance.inv.le (inferVar rustTable (.refMut .static .param)) = true ∧
      Sound (SubGen rustTable (BodyAx (.refMut .static .param) .inv)) :=
  ⟨rfl, rfl, bodyRule_le_inferVar_sound _ _ rfl⟩

end Toy.Variance
