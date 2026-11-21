/-
Toy.Modality.Imported
=====================

**Imported definitions (not results of this package).**  These two definitions
are copied verbatim, up to the namespace, from the published package
`galois-connections-best-abstract-transformers-and-fixpoint-transfer` on the
`reference` branch of `google/zerocopy` at commit
`a0dca4883c555805181f8149eafd7e65ab238991`:

* `Pred` and its `LE` instance: `lean/Toy/AbsInt/Basic.lean` lines 21 and 25
  (git blob `ae1c1a94c6c73ef95c162cdc585fbfd044eecf90`);
* `GaloisConnection`: `lean/Toy/AbsInt/Galois.lean` lines 27-28
  (git blob `7828c554deffea6e4da6073f8eaa36a11844adfe`).

They are copied (not imported) because library packages are self-contained.
The cited package proves the characterization of this notion (its card
`R1-gc-iff`) and the soundness and optimality of best abstract transformers
(cards `R2-best-sound`, `R2-best-least`); those results are cited, not
re-proved, here.  This module contains no theorem.
-/

namespace Toy.Modality.Imported

/-- Predicates on `σ` (sets of states), ordered by inclusion. -/
def Pred (σ : Type) : Type := σ → Prop

/-- Inclusion order on predicates. -/
instance instLEPred (σ : Type) : LE (Pred σ) := ⟨fun x y => ∀ s, x s → y s⟩

/-- `α` and `γ` form a Galois connection (isotone form, `α ⊣ γ`):
`α x ≤ a` exactly when `x ⊆ γ a`. -/
def GaloisConnection {σ A : Type} [LE A] (α : Pred σ → A) (γ : A → Pred σ) : Prop :=
  ∀ x a, α x ≤ a ↔ x ≤ γ a

end Toy.Modality.Imported
