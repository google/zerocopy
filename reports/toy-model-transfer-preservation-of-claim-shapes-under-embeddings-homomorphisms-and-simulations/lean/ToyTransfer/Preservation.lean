import ToyTransfer.Maps

/-!
# The easy preservation theorems

Each theorem is an induction on the formula, pushing the environment through the map.
The map laws are separate hypotheses, so each theorem names exactly the laws it uses.
-/

namespace Toy.Transfer

variable {A B : Str}

/-- Quantifier-free formulas are preserved and reflected by maps that are injective
and preserve and reflect `R` and `P` (that is, by embeddings). -/
theorem qf_sat_iff_of_embedding_laws (h : A.carrier → B.carrier)
    (hinj : Function.Injective h) (hpR : PreservesR h) (hpP : PreservesP h)
    (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsQF φ) (e : Fin n → A.carrier) :
    Sat A φ e ↔ Sat B φ (h ∘ e) := by
  induction hφ with
  | rel i j => exact ⟨hpR _ _, hrR _ _⟩
  | pred i => exact ⟨hpP _, hrP _⟩
  | eq i j => exact ⟨fun hij => congrArg h hij, fun hij => hinj hij⟩
  | neg _ ih => exact not_congr ih
  | and _ _ ih1 ih2 => exact and_congr ih1 ih2
  | or _ _ ih1 ih2 => exact or_congr ih1 ih2

/-- Equality-free quantifier-free formulas are preserved and reflected by maps that
preserve and reflect `R` and `P` (strong homomorphisms), injective or not. -/
theorem qf_sat_iff_of_strongHom_of_eqFree (h : A.carrier → B.carrier)
    (hpR : PreservesR h) (hpP : PreservesP h) (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsQF φ) (hef : IsEqFree φ) (e : Fin n → A.carrier) :
    Sat A φ e ↔ Sat B φ (h ∘ e) := by
  induction hφ with
  | rel i j => exact ⟨hpR _ _, hrR _ _⟩
  | pred i => exact ⟨hpP _, hrP _⟩
  | eq i j => exact absurd hef (fun h => nomatch h)
  | neg _ ih =>
    cases hef with
    | neg h1 => exact not_congr (ih h1)
  | and _ _ ih1 ih2 =>
    cases hef with
    | and h1 h2 => exact and_congr (ih1 h1) (ih2 h2)
  | or _ _ ih1 ih2 =>
    cases hef with
    | or h1 h2 => exact or_congr (ih1 h1) (ih2 h2)

/-- **Universal formulas down to substructures.** Let `h : A → B` be injective and preserve and reflect `R` and `P`
(an embedding, so `A` is a substructure of `B` up to isomorphism). Then every
universal formula true in `B` (at the image of the environment) is true in `A`:
universal formulas are preserved from a structure to its substructures. -/
theorem univ_preserved_to_substructure_of_embedding (h : A.carrier → B.carrier)
    (hinj : Function.Injective h) (hpR : PreservesR h) (hpP : PreservesP h)
    (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsUniv φ) (e : Fin n → A.carrier) :
    Sat B φ (h ∘ e) → Sat A φ e := by
  induction hφ with
  | qf hq => exact (qf_sat_iff_of_embedding_laws h hinj hpR hpP hrR hrP hq e).2
  | all _ ih =>
    intro hB a
    apply ih
    rw [comp_cons]
    exact hB (h a)

/-- **Existential formulas up to extensions.** Let `h : A → B` be injective and preserve and reflect `R` and `P`
(an embedding, so `B` is an extension of `A`). Then every existential formula true in
`A` is true in `B` at the image of the environment: existential formulas are
preserved from a structure to its extensions. -/
theorem exist_preserved_to_extension_of_embedding (h : A.carrier → B.carrier)
    (hinj : Function.Injective h) (hpR : PreservesR h) (hpP : PreservesP h)
    (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsExist φ) (e : Fin n → A.carrier) :
    Sat A φ e → Sat B φ (h ∘ e) := by
  induction hφ with
  | qf hq => exact (qf_sat_iff_of_embedding_laws h hinj hpR hpP hrR hrP hq e).1
  | ex _ ih =>
    rintro ⟨a, ha⟩
    refine ⟨h a, ?_⟩
    rw [← comp_cons]
    exact ih _ ha

/-- **Positive existential formulas forward along homomorphisms.** Let `h : A → B` preserve `R` and `P` (a homomorphism; not
necessarily injective, surjective, or reflecting). Then every positive existential
formula true in `A` is true in `B` at the image of the environment. -/
theorem posExist_preserved_forward_of_hom (h : A.carrier → B.carrier)
    (hpR : PreservesR h) (hpP : PreservesP h)
    {n : Nat} {φ : Fml n} (hφ : IsPosExist φ) (e : Fin n → A.carrier) :
    Sat A φ e → Sat B φ (h ∘ e) := by
  induction hφ with
  | rel i j => exact hpR _ _
  | pred i => exact hpP _
  | eq i j => exact fun hij => congrArg h hij
  | and _ _ ih1 ih2 => exact fun ⟨h1, h2⟩ => ⟨ih1 _ h1, ih2 _ h2⟩
  | or _ _ ih1 ih2 => exact fun hor => hor.elim (fun h1 => .inl (ih1 _ h1)) (fun h2 => .inr (ih2 _ h2))
  | ex _ ih =>
    rintro ⟨a, ha⟩
    refine ⟨h a, ?_⟩
    rw [← comp_cons]
    exact ih _ ha

/-- **Positive formulas forward along surjective homomorphisms.** Let `h : A → B` be surjective and preserve `R` and `P` (a
surjective homomorphism; reflection not required). Then every positive formula
(quantifiers of both kinds allowed, no negation) true in `A` is true in `B` at the
image of the environment. -/
theorem pos_preserved_forward_of_surjHom (h : A.carrier → B.carrier)
    (hsurj : Function.Surjective h) (hpR : PreservesR h) (hpP : PreservesP h)
    {n : Nat} {φ : Fml n} (hφ : IsPos φ) (e : Fin n → A.carrier) :
    Sat A φ e → Sat B φ (h ∘ e) := by
  induction hφ with
  | rel i j => exact hpR _ _
  | pred i => exact hpP _
  | eq i j => exact fun hij => congrArg h hij
  | and _ _ ih1 ih2 => exact fun ⟨h1, h2⟩ => ⟨ih1 _ h1, ih2 _ h2⟩
  | or _ _ ih1 ih2 => exact fun hor => hor.elim (fun h1 => .inl (ih1 _ h1)) (fun h2 => .inr (ih2 _ h2))
  | all _ ih =>
    intro hA b
    obtain ⟨a, rfl⟩ := hsurj b
    rw [← comp_cons]
    exact ih _ (hA a)
  | ex _ ih =>
    rintro ⟨a, ha⟩
    refine ⟨h a, ?_⟩
    rw [← comp_cons]
    exact ih _ ha

end Toy.Transfer
