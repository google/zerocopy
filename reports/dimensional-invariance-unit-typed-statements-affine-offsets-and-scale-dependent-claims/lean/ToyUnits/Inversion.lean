import ToyUnits.Syntax

/-!
# Inversion lemmas for dimension checking
-/

namespace Toy.Units

variable {m : Nat} {K : Type} {Γ : Ctx m}

theorem hasDim_var_inv {x : Nat} {d : Dim m} (h : HasDim (K := K) Γ (.var x) d) : d = Γ x := by
  cases h; rfl

theorem hasDim_lit_inv {c : K} {d' d : Dim m} (h : HasDim Γ (.lit c d') d) : d = d' := by
  cases h; rfl

theorem hasDim_add_inv {a b : Expr m K} {d : Dim m} (h : HasDim Γ (.add a b) d) :
    HasDim Γ a d ∧ HasDim Γ b d := by
  cases h; exact ⟨‹_›, ‹_›⟩

theorem hasDim_sub_inv {a b : Expr m K} {d : Dim m} (h : HasDim Γ (.sub a b) d) :
    HasDim Γ a d ∧ HasDim Γ b d := by
  cases h; exact ⟨‹_›, ‹_›⟩

theorem hasDim_mul_inv {a b : Expr m K} {d : Dim m} (h : HasDim Γ (.mul a b) d) :
    ∃ d₁ d₂, HasDim Γ a d₁ ∧ HasDim Γ b d₂ ∧ d = Dim.mul d₁ d₂ := by
  cases h; exact ⟨_, _, ‹_›, ‹_›, rfl⟩

theorem hasDim_div_inv {a b : Expr m K} {d : Dim m} (h : HasDim Γ (.div a b) d) :
    ∃ d₁ d₂, HasDim Γ a d₁ ∧ HasDim Γ b d₂ ∧ d = Dim.div d₁ d₂ := by
  cases h; exact ⟨_, _, ‹_›, ‹_›, rfl⟩

theorem hasDim_zpow_inv {a : Expr m K} {k : Int} {d : Dim m} (h : HasDim Γ (.zpow a k) d) :
    ∃ d₁, HasDim Γ a d₁ ∧ d = Dim.pow d₁ k := by
  cases h; exact ⟨_, ‹_›, rfl⟩

/-- An expression has at most one dimension. -/
theorem hasDim_unique {e : Expr m K} {d d' : Dim m} (h : HasDim Γ e d) (h' : HasDim Γ e d') :
    d = d' := by
  induction h generalizing d' with
  | var x => exact (hasDim_var_inv h').symm
  | lit c d => exact (hasDim_lit_inv h').symm
  | add _ _ ih₁ _ => exact ih₁ (hasDim_add_inv h').1
  | sub _ _ ih₁ _ => exact ih₁ (hasDim_sub_inv h').1
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := hasDim_mul_inv h'
    rw [ih₁ h₁, ih₂ h₂]
  | div _ _ ih₁ ih₂ =>
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := hasDim_div_inv h'
    rw [ih₁ h₁, ih₂ h₂]
  | zpow k _ ih =>
    obtain ⟨d₁, h₁, rfl⟩ := hasDim_zpow_inv h'
    rw [ih h₁]

theorem wellTypedAt_le_inv {O : Dim m → Prop} {a b : Expr m K}
    (h : WellTypedAt O Γ (.le a b)) : ∃ d, O d ∧ HasDim Γ a d ∧ HasDim Γ b d := by
  cases h; exact ⟨_, ‹_›, ‹_›, ‹_›⟩

theorem wellTypedAt_eq_inv {O : Dim m → Prop} {a b : Expr m K}
    (h : WellTypedAt O Γ (.eq a b)) : ∃ d, HasDim Γ a d ∧ HasDim Γ b d := by
  cases h; exact ⟨_, ‹_›, ‹_›⟩

end Toy.Units
