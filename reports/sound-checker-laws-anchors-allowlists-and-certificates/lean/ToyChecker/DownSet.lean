import ToyChecker.Basic

/-!
# The set of sound checkers

For a fixed semantic predicate `good`, the set of sound checkers is a
down-set of the pointwise order, closed under pointwise `or`, containing
`rejectAll`; it is exactly the principal down-set below the classical oracle
of `good`. Consequently no law that every sound checker satisfies can
exclude `rejectAll`.

All statements are elementary (`definitional`); their value is in fixing
the exact strength of the informal remark "soundness alone cannot rule out
the do-nothing tool". The polarity is that of certifying tools (`true` =
certified good); for bug finders the dual statements hold with `acceptAll`
as the degenerate tool (see `ToyChecker.Basic`).
-/

namespace Toy.Checker

universe u

/-! ## Main statements -/

/-- R1a (part). `rejectAll` is sound for every semantic predicate. -/
theorem sound_rejectAll {P : Type u} (good : P → Prop) : Sound good rejectAll := by
  intro p h
  simp [rejectAll] at h

/-- R1a (part). Soundness is downward closed: a checker below a sound
checker is sound. -/
theorem sound_of_checkerLE_of_sound {P : Type u} {good : P → Prop} {c₁ c₂ : P → Bool}
    (hle : CheckerLE c₁ c₂) (h₂ : Sound good c₂) : Sound good c₁ :=
  fun p h => h₂ p (hle p h)

/-- R1a (part). Soundness is closed under pointwise `or` (for two checkers
sound for the same predicate `good`). -/
theorem sound_orChecker_of_sound_of_sound {P : Type u} {good : P → Prop} {c₁ c₂ : P → Bool}
    (h₁ : Sound good c₁) (h₂ : Sound good c₂) : Sound good (orChecker c₁ c₂) := by
  intro p h
  simp only [orChecker, Bool.or_eq_true] at h
  rcases h with h | h
  · exact h₁ p h
  · exact h₂ p h

/-- R1a. Exact description of the set of sound checkers: a checker is sound
iff it is pointwise below the classical oracle of `good`. The oracle is in
general noncomputable; see `classicalOracle_eq_decide` for decidable
`good`. -/
theorem sound_iff_checkerLE_classicalOracle {P : Type u} (good : P → Prop) (c : P → Bool) :
    Sound good c ↔ CheckerLE c (classicalOracle good) := by
  constructor
  · intro h p hp
    exact (classicalOracle_eq_true_iff good p).mpr (h p hp)
  · intro h p hp
    exact (classicalOracle_eq_true_iff good p).mp (h p hp)

/-- R1e. Any law satisfied by every sound checker is also satisfied by
`rejectAll`; consequently no law implied by soundness alone can exclude
`rejectAll`. (A law that excludes `rejectAll` need not exclude any other
sound checker: `fun c => c ≠ rejectAll` excludes exactly `rejectAll`.) -/
theorem law_of_all_sound_holds_for_rejectAll {P : Type u} (good : P → Prop) (L : Law P)
    (hL : ∀ c, Sound good c → L c) : L rejectAll :=
  hL rejectAll (sound_rejectAll good)

/-! ## Tightness counterexamples (canonical form: all other hypotheses hold,
the conclusion fails) -/

/-- R1a (`sound_of_checkerLE_of_sound`) without `hle`: `acceptAll` is not below `rejectAll`, `rejectAll` is
sound, and `acceptAll` is not sound. -/
theorem cex_sound_of_checkerLE_needs_le :
    Sound evenGood rejectAll ∧ ¬ Sound evenGood acceptAll :=
  ⟨sound_rejectAll evenGood, not_sound_example_acceptAll⟩

/-- R1a (`sound_of_checkerLE_of_sound`) without `h₂`: `acceptAll ≤ acceptAll` holds, yet `acceptAll` is not
sound for `evenGood`. -/
theorem cex_sound_of_checkerLE_needs_sound :
    CheckerLE (acceptAll : Nat → Bool) acceptAll ∧ ¬ Sound evenGood acceptAll :=
  ⟨fun _ h => h, not_sound_example_acceptAll⟩

/-- R1a (`sound_orChecker_of_sound_of_sound`) without `h₁`: the second component (`rejectAll`) is sound, but the
disjunction with `acceptAll` is not. -/
theorem cex_sound_orChecker_needs_left :
    Sound evenGood rejectAll ∧ ¬ Sound evenGood (orChecker acceptAll rejectAll) := by
  refine ⟨sound_rejectAll evenGood, ?_⟩
  intro h
  have h1 := h 1 rfl
  simp [evenGood] at h1

/-- R1a (`sound_orChecker_of_sound_of_sound`) without `h₂`: the first component (`rejectAll`) is sound, but the
disjunction with `acceptAll` is not. -/
theorem cex_sound_orChecker_needs_right :
    Sound evenGood rejectAll ∧ ¬ Sound evenGood (orChecker rejectAll acceptAll) := by
  refine ⟨sound_rejectAll evenGood, ?_⟩
  intro h
  have h1 := h 1 rfl
  simp [evenGood] at h1

/-- The law "accepts program `0`" (an anchor law). -/
def acceptsZeroLaw : Law Nat := fun c => c 0 = true

/-- R1e without `hL` (and positive control for R1e as an impossibility): the
anchor law "accepts `0`" excludes `rejectAll`; it is not satisfied by every
sound checker (`rejectAll` is sound and violates it). -/
theorem cex_law_of_all_sound_needs_hL :
    ¬ acceptsZeroLaw rejectAll ∧ Sound evenGood rejectAll :=
  ⟨by simp [acceptsZeroLaw, rejectAll], sound_rejectAll evenGood⟩

/-- Positive control for R1e: a nearby law (soundness plus the anchor `0`)
is satisfied by some sound checker and excludes `rejectAll`. -/
theorem positive_control_anchor_law_excludes_rejectAll :
    (Sound evenGood evenExact ∧ acceptsZeroLaw evenExact) ∧ ¬ acceptsZeroLaw rejectAll :=
  ⟨⟨sound_example_evenExact, rfl⟩, by simp [acceptsZeroLaw, rejectAll]⟩

/-! ## Non-vacuity witnesses (all hypotheses hold in an intended instance) -/

/-- `sound_of_checkerLE_of_sound` hypotheses hold for `evenBelowTen ≤ evenExact`. -/
theorem nonvacuous_sound_of_checkerLE_of_sound :
    CheckerLE evenBelowTen evenExact ∧ Sound evenGood evenExact :=
  ⟨checkerLE_example_evenBelowTen_evenExact, sound_example_evenExact⟩

/-- `sound_orChecker_of_sound_of_sound` hypotheses hold for two different sound single-program checkers. -/
theorem nonvacuous_sound_orChecker :
    Sound evenGood (fun n => n == 0) ∧ Sound evenGood (fun n => n == 2) := by
  constructor
  · intro p h; simp at h; subst h; rfl
  · intro p h; simp at h; subst h; rfl

/-- `sound_iff_checkerLE_classicalOracle` is non-degenerate: both sides hold for `evenExact` and both fail for
`acceptAll`. -/
theorem nonvacuous_sound_iff_checkerLE_classicalOracle :
    CheckerLE evenExact (classicalOracle evenGood) ∧
    ¬ CheckerLE (acceptAll : Nat → Bool) (classicalOracle evenGood) := by
  constructor
  · exact (sound_iff_checkerLE_classicalOracle evenGood evenExact).mp sound_example_evenExact
  · intro h
    exact not_sound_example_acceptAll
      ((sound_iff_checkerLE_classicalOracle evenGood acceptAll).mpr h)

/-- R1e hypothesis holds for the law "is sound for `evenGood`" itself. -/
theorem nonvacuous_law_of_all_sound :
    ∀ c, Sound evenGood c → (fun c => Sound evenGood c) c :=
  fun _ h => h

end Toy.Checker
