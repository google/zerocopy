import Toy.Ledger.Families

/-!
# Ledgers are relative to a reference class and to the stated conclusion

Sufficiency transfers to subclasses and tightness to superclasses, and not, in general, the other way;
`tight` and `harmless` exclude each other relative to one fixed reference class over which
the theorem holds, and are not exhaustive. A hypothesis is tight for a conjunction of
conclusions exactly when it is tight for at least one conjunct, so a per-conjunct summary
can over-read a ledger.
-/

namespace Toy.Ledger

universe u v w

section General

variable {M : Type u} {ι : Type v}

/-- Sufficiency over the class of all models is plain sufficiency. -/
theorem sufficientIn_true_iff (H : ι → M → Prop) (C : M → Prop) :
    SufficientIn (fun _ => True) H C ↔ Sufficient H C :=
  ⟨fun h x hx => h x trivial hx, fun h x _ hx => h x hx⟩

/-- Tightness over the class of all models is plain tightness. -/
theorem tightIn_true_iff (H : ι → M → Prop) (C : M → Prop) (i : ι) :
    TightIn (fun _ => True) H C i ↔ TightAt H C i :=
  ⟨fun ⟨x, _, hx, hc⟩ => ⟨x, hx, hc⟩, fun ⟨x, hx, hc⟩ => ⟨x, trivial, hx, hc⟩⟩

/-- Non-vacuity over the class of all models is plain non-vacuity. -/
theorem nonVacuousIn_true_iff (H : ι → M → Prop) :
    NonVacuousIn (fun _ => True) H ↔ NonVacuous H :=
  ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩

/-! ## Transfer between reference classes -/

/-- For a subclass `P ⊆ Q`: sufficiency over `Q` gives sufficiency over `P`, and for every
index, a tightness witness in `P` is a tightness witness in `Q`. -/
theorem sufficientIn_antitone_and_tightIn_monotone {P Q : M → Prop} {H : ι → M → Prop}
    {C : M → Prop} (hPQ : ∀ x, P x → Q x) :
    (SufficientIn Q H C → SufficientIn P H C) ∧ (∀ i, TightIn P H C i → TightIn Q H C i) :=
  ⟨fun hQ x hPx hx => hQ x (hPQ x hPx) hx,
   fun _ ⟨x, hPx, ho, hnc⟩ => ⟨x, hPQ x hPx, ho, hnc⟩⟩

/-- For a subclass `P ⊆ Q`, non-vacuity over `P` gives non-vacuity over `Q` (the same
direction as tightness, opposite to sufficiency). -/
theorem nonVacuousIn_monotone {P Q : M → Prop} {H : ι → M → Prop}
    (hPQ : ∀ x, P x → Q x) : NonVacuousIn P H → NonVacuousIn Q H :=
  fun ⟨x, hPx, hx⟩ => ⟨x, hPQ x hPx, hx⟩

/-- Relative to one fixed class `P` over which the theorem holds, a tight hypothesis is
not harmless. -/
theorem not_harmlessIn_of_tightIn_of_sufficientIn {P : M → Prop} {H : ι → M → Prop}
    {C : M → Prop} {i : ι} (hs : SufficientIn P H C) (ht : TightIn P H C i) :
    ¬ HarmlessIn P H i :=
  fun hh =>
    let ⟨x, hPx, ho, hnc⟩ := ht
    hnc (hs x hPx fun j => (Classical.em (j = i)).elim (fun h => h ▸ hh x hPx) (ho j))

/-! ## Conjunctions of conclusions -/

/-- For a fixed hypothesis family `H`: (1) for any two conclusions, a hypothesis is tight
for `C₁ ∧ C₂` exactly when it is tight for `C₁` or for `C₂`; (2) for any family of
conclusions `D : κ → M → Prop`, the hypotheses suffice for all of them exactly when they
suffice for each; (3) for any such family, a hypothesis is tight for the conjunction of all
of them exactly when it is tight for at least one. -/
theorem sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some
    (H : ι → M → Prop) :
    (∀ (C₁ C₂ : M → Prop) (i : ι),
      TightAt H (fun x => C₁ x ∧ C₂ x) i ↔ TightAt H C₁ i ∨ TightAt H C₂ i) ∧
    (∀ {κ : Type w} (D : κ → M → Prop),
      Sufficient H (fun x => ∀ k, D k x) ↔ ∀ k, Sufficient H (D k)) ∧
    (∀ {κ : Type w} (D : κ → M → Prop) (i : ι),
      TightAt H (fun x => ∀ k, D k x) i ↔ ∃ k, TightAt H (D k) i) := by
  refine ⟨fun C₁ C₂ i => ⟨?_, ?_⟩, fun D => ⟨fun hs k x hx => hs x hx k,
    fun hs x hx k => hs k x hx⟩, fun D i => ⟨?_, ?_⟩⟩
  · rintro ⟨x, ho, hnc⟩
    exact (Classical.em (C₁ x)).elim
      (fun hc1 => Or.inr ⟨x, ho, fun hc2 => hnc ⟨hc1, hc2⟩⟩)
      (fun hnc1 => Or.inl ⟨x, ho, hnc1⟩)
  · rintro (⟨x, ho, hnc1⟩ | ⟨x, ho, hnc2⟩)
    · exact ⟨x, ho, fun h => hnc1 h.1⟩
    · exact ⟨x, ho, fun h => hnc2 h.2⟩
  · rintro ⟨x, ho, hnc⟩
    have ⟨k, hnk⟩ : ∃ k, ¬ D k x :=
      Classical.byContradiction fun h => hnc fun k =>
        Classical.byContradiction fun hnk => h ⟨k, hnk⟩
    exact ⟨k, x, ho, hnk⟩
  · rintro ⟨k, x, ho, hnk⟩
    exact ⟨x, ho, fun hall => hnk (hall k)⟩

end General

/-! ## Witnesses: transfer between reference classes -/

/-- Counterexample for `hPQ` in `sufficientIn_antitone_and_tightIn_monotone` (first
conjunct): with `P` = all naturals and `Q` = `x ≤ 1` (so `P ⊄ Q`), `x ≥ 1 ⊢ x = 1` holds
over `Q` but not over `P`. -/
theorem sufficientIn_antitone_ce_not_subclass :
    ¬ ((SufficientIn bounded (single fun x : Nat => 1 ≤ x) pinC →
          SufficientIn trueC (single fun x : Nat => 1 ≤ x) pinC) ∧
        (∀ i, TightIn trueC (single fun x : Nat => 1 ≤ x) pinC i →
          TightIn bounded (single fun x : Nat => 1 ≤ x) pinC i)) :=
  fun h => not_sufficientIn_true_single (h.1 sufficientIn_bounded_single)

/-- Counterexample for `hPQ` in `sufficientIn_antitone_and_tightIn_monotone` (second
conjunct): with `P` = all naturals and `Q` = `x ≤ 1`, hypothesis `x ≤ 1` of
`x ≥ 1, x ≤ 1 ⊢ x = 1` is tight over `P` (witness `2`) but not over `Q`. -/
theorem tightIn_monotone_ce_not_subclass :
    ¬ ((SufficientIn bounded pinH pinC → SufficientIn trueC pinH pinC) ∧
        (∀ i, TightIn trueC pinH pinC i → TightIn bounded pinH pinC i)) :=
  fun h => not_tightIn_bounded_pin_h2 (h.2 .h2 tightIn_true_pin_h2)

/-- Non-vacuity for `sufficientIn_antitone_and_tightIn_monotone`: `x ≤ 1` is a subclass of
all naturals, `x ≥ 1, x ≤ 1 ⊢ x = 1` holds over all naturals, and `x ≥ 1` is tight over the
subclass (witness `0`). -/
theorem sufficientIn_antitone_nonvacuity :
    (∀ x, bounded x → trueC x) ∧ SufficientIn trueC pinH pinC ∧ TightIn bounded pinH pinC .h1 :=
  ⟨fun _ _ => trivial, fun x _ hx => sufficient_pin x hx,
    ⟨0, by simp [bounded], by simp [pinH], by simp [pinC]⟩⟩

/-- Non-vacuity does not transfer to subclasses: `zeroClass` (`x = 0`) is a subclass of
`bounded` (`x ≤ 1`), `x ≥ 1, x ≤ 1 ⊢ x = 1` holds and is non-vacuous over `bounded`, and it
holds vacuously over `zeroClass`. -/
theorem nonVacuousIn_not_antitone :
    (∀ x, zeroClass x → bounded x) ∧ SufficientIn bounded pinH pinC ∧
      NonVacuousIn bounded pinH ∧ SufficientIn zeroClass pinH pinC ∧
      ¬ NonVacuousIn zeroClass pinH :=
  ⟨fun x hx => by simp [zeroClass] at hx; simp [bounded, hx],
    fun x _ hx => sufficient_pin x hx, nonVacuousIn_bounded_pin,
    fun x _ hx => sufficient_pin x hx, not_nonVacuousIn_zeroClass_pin⟩

/-- A tightness witness says nothing about a class that does not contain it. For
`x ≥ 1, x ≤ 1 ⊢ x = 1`, which holds over all naturals and over the reference class `x ≤ 1`
and is non-vacuous over that class (witness `1`): hypothesis `x ≤ 1` is tight over all
naturals (witness `x = 2`, outside the class), harmless over the class, and not tight over
the class. -/
theorem tightIn_all_models_harmlessIn_bounded :
    SufficientIn trueC pinH pinC ∧ SufficientIn bounded pinH pinC ∧
      NonVacuousIn bounded pinH ∧
      TightIn trueC pinH pinC .h2 ∧ HarmlessIn bounded pinH .h2 ∧
      ¬ TightIn bounded pinH pinC .h2 :=
  ⟨fun x _ hx => sufficient_pin x hx, fun x _ hx => sufficient_pin x hx,
    nonVacuousIn_bounded_pin, tightIn_true_pin_h2,
    harmlessIn_bounded_pin_h2, not_tightIn_bounded_pin_h2⟩

/-- Counterexample for `hs` in `not_harmlessIn_of_tightIn_of_sufficientIn`: for
`True ⊢ False` over `Unit`, the hypothesis is both tight and harmless. -/
theorem not_harmlessIn_ce_not_sufficientIn :
    TightIn trueC topH falseC () ∧ HarmlessIn trueC topH () :=
  ⟨(tightIn_true_iff _ _ _).mpr tightAt_topH_falseC, fun _ _ => trivial⟩

/-- Counterexample for `ht` in `not_harmlessIn_of_tightIn_of_sufficientIn`: for
`True ⊢ True` over `Unit`, the theorem holds and the hypothesis is harmless. -/
theorem not_harmlessIn_ce_not_tightIn :
    SufficientIn trueC topH trueC ∧ HarmlessIn trueC topH () :=
  ⟨fun _ _ _ => trivial, fun _ _ => trivial⟩

/-- Non-vacuity for `not_harmlessIn_of_tightIn_of_sufficientIn`. -/
theorem not_harmlessIn_nonvacuity :
    SufficientIn trueC pinH pinC ∧ TightIn trueC pinH pinC .h2 :=
  ⟨fun x _ hx => sufficient_pin x hx, tightIn_true_pin_h2⟩

/-- `tight` and `harmless` are not exhaustive: in `x ≥ 1, x ≤ 1 ⊢ x ≤ 1` over all naturals
(where the theorem holds), the hypothesis `x ≥ 1` is neither tight nor harmless (it fails at
`x = 0`, so it excludes models of the class without being needed). -/
theorem tightIn_harmlessIn_not_exhaustive :
    SufficientIn trueC pinH pinWeakC ∧ ¬ TightIn trueC pinH pinWeakC .h1 ∧
      ¬ HarmlessIn trueC pinH .h1 :=
  ⟨fun x _ hx => isolatingAt_sufficient_not_tightAt_pinWeak.1 x hx,
    fun h => not_tightAt_pinWeak_h1 ((tightIn_true_iff _ _ _).mp h),
    fun h => by have := h 0 trivial; simp [pinH] at this⟩

/-! ## Witnesses: conjunctions of conclusions -/

/-- In `x ≤ 1, y ≤ 1 ⊢ x ≤ 1 ∧ y ≤ 1` (non-vacuous: witness `(0, 0)`), hypothesis `x ≤ 1`
is tight for the conjunction but not for the conjunct `y ≤ 1`; a summary "under `x ≤ 1`,
`y ≤ 1`" over-reads the ledger. -/
theorem tight_for_conjunction_not_for_conjunct :
    NonVacuous sumH ∧ Sufficient sumH (fun p => p.1 ≤ 1 ∧ p.2 ≤ 1) ∧
      TightAt sumH (fun p => p.1 ≤ 1 ∧ p.2 ≤ 1) .h1 ∧
      Sufficient sumH (fun p => p.2 ≤ 1) ∧ ¬ TightAt sumH (fun p => p.2 ≤ 1) .h1 := by
  refine ⟨⟨(0, 0), by simp [sumH]⟩, fun p hp => by simpa [sumH] using hp,
    ⟨(5, 0), by simp [sumH], by simp⟩, fun p hp => by simpa [sumH] using hp .h2, ?_⟩
  rintro ⟨p, hp, hc⟩
  simp [sumH] at hp
  exact hc hp

/-- Non-vacuity for `sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some`,
with both sides of each part true: `x ≤ 1` is tight for `x ≤ 1 ∧ y ≤ 1` and for `x ≤ 1`;
for the family `D := sumH` (so `∀ k, D k p` is `x ≤ 1 ∧ y ≤ 1`), `sumH` suffices for every
`D k` and for their conjunction, and `h1` is tight for the conjunction and for `D h1`. -/
theorem sufficient_conjunction_nonvacuity :
    TightAt sumH (fun p => p.1 ≤ 1 ∧ p.2 ≤ 1) .h1 ∧ TightAt sumH (fun p => p.1 ≤ 1) .h1 ∧
      Sufficient sumH (fun p => ∀ k : Two, sumH k p) ∧ (∀ k, Sufficient sumH (sumH k)) ∧
      TightAt sumH (fun p => ∀ k : Two, sumH k p) .h1 ∧ TightAt sumH (sumH .h1) .h1 :=
  ⟨⟨(5, 0), by simp [sumH], by simp⟩, ⟨(5, 0), by simp [sumH], by simp⟩,
    fun _ hp k => hp k, fun k _ hp => hp k,
    ⟨(5, 0), by simp [sumH], fun h => by have := h .h1; simp [sumH] at this⟩,
    ⟨(5, 0), by simp [sumH], by simp [sumH]⟩⟩

/-- Unweakenability does not pass from a conjunction to its conjuncts: with the single
hypothesis `x = 1` over `Nat`, the hypothesis is necessary and unweakenable for
`1 ≤ x ∧ x ≤ 1`, but not unweakenable for `1 ≤ x` (take `x = 2`) nor for `x ≤ 1`
(take `x = 0`), though it suffices for both. -/
theorem unweakenable_for_conjunction_not_for_conjuncts :
    Sufficient (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) ∧
      NecessaryAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) () ∧
      UnweakenableAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) () ∧
      Sufficient (single fun x : Nat => x = 1) (fun x => 1 ≤ x) ∧
      ¬ UnweakenableAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x) () ∧
      Sufficient (single fun x : Nat => x = 1) (fun x => x ≤ 1) ∧
      ¬ UnweakenableAt (single fun x : Nat => x = 1) (fun x => x ≤ 1) () := by
  have hnec : NecessaryAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) () :=
    fun x hx => by simp only [single]; omega
  refine ⟨fun x hx => ?_, hnec, unweakenableAt_of_necessaryAt hnec, fun x hx => ?_, fun h => ?_,
    fun x hx => ?_, fun h => ?_⟩
  · have := hx (); simp only [single] at this; omega
  · have := hx (); simp only [single] at this; omega
  · have := h 2 (fun j hj => absurd (by cases j; rfl) hj) (by decide)
    simp [single] at this
  · have := hx (); simp only [single] at this; omega
  · have := h 0 (fun j hj => absurd (by cases j; rfl) hj) (by decide)
    simp [single] at this

end Toy.Ledger
