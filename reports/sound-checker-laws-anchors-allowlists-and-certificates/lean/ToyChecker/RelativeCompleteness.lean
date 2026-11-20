import ToyChecker.Relabel

/-!
# Relative completeness versus lockout

The law "sound, and complete on the fragment `F`" asks a tool to accept
every good program in `F` and nothing bad anywhere. In the Boolean-function
model:

* its satisfiers are exactly the checkers between the oracle of `F ∧ good`
  and the oracle of `good` in the pointwise order, and the lower end is one
  of them, so the law is always satisfiable (by a noncomputable function in
  general) (R6a);
* a single checker satisfies it iff it is sound everywhere and decides
  `good` on `F`; hence, relative to any class `K` of admissible checkers
  (for instance the computable ones, which this model does not define), it
  is satisfiable in `K` iff some checker in `K` is sound and decides `good`
  on `F`; for `F = everything` this is "`good` is `K`-decidable"; and if `K`
  is closed under pointwise `&&` and contains a decider for `F`, the
  soundness requirement can be dropped (R6c; R6h shows it cannot be dropped
  in general);
* it excludes `rejectAll` iff `F` contains a good program (R6e);
* it admits an allowlist `A` iff the anchors are good and every good program
  of `F` is listed (R6f), so when `F` contains infinitely many good programs
  it excludes every lookup table (concrete instance R6g).

Honesty about decidability: Lean's logic is classical, so "there exists a
Boolean checker with this property" never encodes an implementability or
computability constraint. Rice-style lockout of *implementable* tools is a
statement about a class `K`, here left abstract.
-/

namespace Toy.Checker

universe u

/-- `SoundCompleteOn good F c`: `c` is sound and complete on the fragment
`F`. Captures the strongest per-fragment admission law a framework might
impose on a tool. -/
def SoundCompleteOn {P : Type u} (good F : P → Prop) (c : P → Bool) : Prop :=
  Sound good c ∧ CompleteOn good F c

/-- Positive example: `evenBelowTen` is sound and complete on `n < 10`. -/
theorem soundCompleteOn_example_evenBelowTen :
    SoundCompleteOn evenGood (fun n => n < 10) evenBelowTen :=
  ⟨sound_example_evenBelowTen, completeOn_example_evenBelowTen⟩

/-- Positive example: `rejectAll` is sound and complete on a fragment with no
good programs (`n = 1`). -/
theorem soundCompleteOn_example_rejectAll_odd_fragment :
    SoundCompleteOn evenGood (fun n => n = 1) rejectAll := by
  refine ⟨sound_rejectAll evenGood, fun p hg hF => ?_⟩
  subst hF
  simp [evenGood] at hg

/-- Negative example: `evenBelowTen` is not sound and complete on all
programs. -/
theorem not_soundCompleteOn_example_evenBelowTen :
    ¬ SoundCompleteOn evenGood (fun _ => True) evenBelowTen :=
  fun h => not_completeOn_example_evenBelowTen h.2

/-- Negative example: `acceptAll` is complete everywhere but not sound. -/
theorem not_soundCompleteOn_example_acceptAll :
    ¬ SoundCompleteOn evenGood (fun _ => True) acceptAll :=
  fun h => not_sound_example_acceptAll h.1

/-- `AndClosed K`: the class `K` of admissible checkers is closed under
pointwise conjunction. Captures a closure property shared by natural
classes such as "computable" or "polynomial-time" checkers. -/
def AndClosed {P : Type u} (K : (P → Bool) → Prop) : Prop :=
  ∀ c₁ c₂, K c₁ → K c₂ → K (fun p => c₁ p && c₂ p)

/-- `DecidedIn K F`: some checker in the class `K` decides the fragment `F`
(returns `true` exactly on `F`). Captures "membership in the fragment is
itself checkable by an admissible tool". -/
def DecidedIn {P : Type u} (K : (P → Bool) → Prop) (F : P → Prop) : Prop :=
  ∃ d, K d ∧ ∀ p, d p = true ↔ F p

/-- Positive example: the class of all checkers is closed under `&&` and
decides the fragment `n < 10`. -/
theorem andClosed_decidedIn_example_all :
    AndClosed (fun _ : Nat → Bool => True) ∧ DecidedIn (fun _ : Nat → Bool => True) (fun n => n < 10) :=
  ⟨fun _ _ _ _ => trivial, ⟨fun n => decide (n < 10), trivial, fun p => by simp⟩⟩

/-- Negative example: the singleton class `{acceptAll}` does not decide the
fragment `n = 0`. -/
theorem not_decidedIn_example_acceptAll :
    ¬ DecidedIn (fun c => c = (acceptAll : Nat → Bool)) (fun n => n = 0) := by
  rintro ⟨d, rfl, hd⟩
  exact absurd ((hd 1).mp rfl) (by decide)

/-- Fragment decider used in counterexamples: accept exactly `0` and `1`. -/
def belowTwo : Nat → Bool := fun n => decide (n < 2)

/-- A checker that agrees with "is `0`" on `n < 2` but accepts every
`n ≥ 2`. -/
def zeroOrLarge : Nat → Bool := fun n => decide (n = 0 ∨ 2 ≤ n)

/-- Negative example: the two-element class `{belowTwo, zeroOrLarge}` is not
closed under `&&` (their conjunction accepts exactly `0`, and is neither). -/
theorem not_andClosed_example_belowTwo_zeroOrLarge :
    ¬ AndClosed (fun c => c = belowTwo ∨ c = zeroOrLarge) := by
  intro h
  rcases h belowTwo zeroOrLarge (Or.inl rfl) (Or.inr rfl) with h1 | h1
  · have := congrFun h1 1
    revert this
    decide
  · have := congrFun h1 2
    revert this
    decide

/-! ## Main statements -/

/-- R6a (part). The law is always satisfiable in the Boolean-function model:
the classical oracle of `F ∧ good` is sound and complete on `F`. The witness
is noncomputable in general. -/
theorem soundCompleteOn_classicalOracle_inter {P : Type u} (good F : P → Prop) :
    SoundCompleteOn good F (classicalOracle (fun p => F p ∧ good p)) :=
  ⟨fun p hp => ((classicalOracle_eq_true_iff _ p).mp hp).2,
   fun p hg hF => (classicalOracle_eq_true_iff _ p).mpr ⟨hF, hg⟩⟩

/-- R6a. Exact description of the satisfiers: a checker is sound and
complete on `F` iff it lies between the oracle of `F ∧ good` and the oracle
of `good` in the pointwise order. -/
theorem soundCompleteOn_iff_between {P : Type u} (good F : P → Prop) (c : P → Bool) :
    SoundCompleteOn good F c ↔
      CheckerLE (classicalOracle (fun p => F p ∧ good p)) c ∧
      CheckerLE c (classicalOracle good) := by
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨fun p hp => ?_, (sound_iff_checkerLE_classicalOracle good c).mp hs⟩
    obtain ⟨hF, hg⟩ := (classicalOracle_eq_true_iff _ p).mp hp
    exact hc p hg hF
  · rintro ⟨hle1, hle2⟩
    refine ⟨(sound_iff_checkerLE_classicalOracle good c).mpr hle2, fun p hg hF => ?_⟩
    exact hle1 p ((classicalOracle_eq_true_iff _ p).mpr ⟨hF, hg⟩)

/-- R6c. Pointwise characterization: a checker `c` is sound and complete on
`F` iff the same `c` is sound everywhere and decides `good` on `F`. -/
theorem soundCompleteOn_iff_sound_and_decides_on {P : Type u} (good F : P → Prop)
    (c : P → Bool) :
    SoundCompleteOn good F c ↔ Sound good c ∧ ∀ p, F p → (c p = true ↔ good p) :=
  ⟨fun ⟨hs, hc⟩ => ⟨hs, fun p hF => ⟨hs p, fun hg => hc p hg hF⟩⟩,
   fun ⟨hs, hdec⟩ => ⟨hs, fun p hg hF => (hdec p hF).mpr hg⟩⟩

/-- R6c (part). Satisfiability within an arbitrary class `K` of admissible
checkers: the law has a satisfier in `K` iff some checker in `K` is sound
and decides `good` on `F` (the existential form of the pointwise
characterization). -/
theorem exists_soundCompleteOn_in_class_iff {P : Type u} (good F : P → Prop)
    (K : (P → Bool) → Prop) :
    (∃ c, K c ∧ SoundCompleteOn good F c) ↔
      ∃ c, K c ∧ Sound good c ∧ ∀ p, F p → (c p = true ↔ good p) :=
  exists_congr fun c => and_congr_right fun _ => soundCompleteOn_iff_sound_and_decides_on good F c

/-- R6c (part). Full fragment, pointwise: a checker is sound and complete on
all programs iff it decides `good`. -/
theorem soundCompleteOn_univ_iff_decides {P : Type u} (good : P → Prop) (c : P → Bool) :
    SoundCompleteOn good (fun _ => True) c ↔ ∀ p, c p = true ↔ good p :=
  ⟨fun ⟨hs, hc⟩ p => ⟨hs p, fun hg => hc p hg trivial⟩,
   fun hdec => ⟨fun p hp => (hdec p).mp hp, fun p hg _ => (hdec p).mpr hg⟩⟩

/-- R6c (part). Full fragment, class form: the law "sound and complete on
all programs" has a satisfier in the class `K` iff `good` is decided by some
checker in `K`. -/
theorem exists_soundCompleteOn_univ_in_class_iff {P : Type u} (good : P → Prop)
    (K : (P → Bool) → Prop) :
    (∃ c, K c ∧ SoundCompleteOn good (fun _ => True) c) ↔
      ∃ c, K c ∧ ∀ p, c p = true ↔ good p :=
  exists_congr fun c => and_congr_right fun _ => soundCompleteOn_univ_iff_decides good c

/-- R6c (part). When the soundness requirement can be dropped: if the class
`K` is closed under pointwise `&&` and contains a decider for the fragment
`F`, then the law has a satisfier in `K` iff some checker in `K` decides
`good` on `F` (restricting such a checker to `F` makes it sound). -/
theorem exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn
    {P : Type u} (good F : P → Prop) (K : (P → Bool) → Prop)
    (hK : AndClosed K) (hF : DecidedIn K F) :
    (∃ c, K c ∧ SoundCompleteOn good F c) ↔ ∃ c, K c ∧ ∀ p, F p → (c p = true ↔ good p) := by
  obtain ⟨d, hdK, hdF⟩ := hF
  constructor
  · rintro ⟨c, hcK, hs, hc⟩
    exact ⟨c, hcK, fun p hFp => ⟨hs p, fun hg => hc p hg hFp⟩⟩
  · rintro ⟨c, hcK, hdec⟩
    refine ⟨fun p => d p && c p, hK d c hdK hcK, ?_, ?_⟩
    · intro p hp
      dsimp only at hp
      cases hd : d p with
      | false => rw [hd] at hp; exact Bool.noConfusion hp
      | true =>
        rw [hd, Bool.true_and] at hp
        exact (hdec p ((hdF p).mp hd)).mp hp
    · intro p hg hFp
      dsimp only
      rw [(hdF p).mpr hFp, Bool.true_and]
      exact (hdec p hFp).mpr hg

/-- R6e. Lockout of the do-nothing tool: the law excludes `rejectAll` iff
`F` contains a good program. (The left-to-right direction is classical.) -/
theorem not_soundCompleteOn_rejectAll_iff {P : Type u} (good F : P → Prop) :
    ¬ SoundCompleteOn good F rejectAll ↔ ∃ p, F p ∧ good p := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    exact h ⟨sound_rejectAll good, fun p hg hF => False.elim (hne ⟨p, hF, hg⟩)⟩
  · rintro ⟨p, hF, hg⟩ ⟨_, hc⟩
    exact Bool.noConfusion (hc p hg hF)

/-- R6f. Lookup tables under relative completeness: the allowlist of `A` is
sound and complete on `F` iff every anchor is good and every good program of
`F` is an anchor. -/
theorem soundCompleteOn_allowlist_iff {P : Type u} [DecidableEq P] (good F : P → Prop)
    (A : List P) :
    SoundCompleteOn good F (allowlist A) ↔
      (∀ a ∈ A, good a) ∧ ∀ p, F p → good p → p ∈ A := by
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨fun a ha => hs a (decide_eq_true ha),
           fun p hF hg => of_decide_eq_true (hc p hg hF)⟩
  · rintro ⟨hA, hF⟩
    exact ⟨fun p hp => hA p (of_decide_eq_true hp),
           fun p hg hFp => decide_eq_true (hF p hFp hg)⟩

/-- R6g. Concrete lockout of lookup tables: for `evenGood` on all programs,
no allowlist is sound and complete (there are infinitely many good
programs). The law itself is satisfiable (`evenExact`, see
`nonvacuous_no_allowlist_soundCompleteOn_evenGood_univ`). -/
theorem no_allowlist_soundCompleteOn_evenGood_univ (A : List Nat) :
    ¬ SoundCompleteOn evenGood (fun _ => True) (allowlist A) := by
  rintro ⟨_, hc⟩
  have hgood : evenGood (2 * (A.sum + 1)) := by
    unfold evenGood
    omega
  have hacc := hc (2 * (A.sum + 1)) hgood trivial
  have hmem : 2 * (A.sum + 1) ∈ A := by simpa [allowlist] using hacc
  have := le_sum_of_mem_nat hmem
  omega

/-! ## Counterexamples and positive controls -/

/-- R6h. The soundness conjunct of R6c cannot be dropped in general. In the
class `K = {acceptAll}`, with `good = F = (· = 0)`, the checker `acceptAll`
decides `good` on `F`, yet the law has no satisfier in `K` (accept-all is
unsound off `F`). So "`good` restricted to `F` is `K`-decidable" is not by
itself equivalent to satisfiability in `K`. -/
theorem cex_decides_on_fragment_without_soundness :
    (∃ c, (fun c => c = (acceptAll : Nat → Bool)) c ∧
      ∀ p, (fun n => n = 0) p → (c p = true ↔ (fun n => n = 0) p)) ∧
    ¬ ∃ c, (fun c => c = (acceptAll : Nat → Bool)) c ∧
      SoundCompleteOn (fun n => n = 0) (fun n => n = 0) c := by
  constructor
  · refine ⟨acceptAll, rfl, fun p hp => ?_⟩
    simp [acceptAll, hp]
  · rintro ⟨c, hc, hs, _⟩
    subst hc
    exact absurd (hs 1 rfl) (by decide)

/-- `exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn`
without `hF`: `K = {acceptAll}` is closed under `&&`, but does not decide
`F = (· = 0)`; the equivalence fails (this is R6h). -/
theorem cex_decides_on_iff_needs_decidedIn :
    AndClosed (fun c => c = (acceptAll : Nat → Bool)) ∧
    ¬ ((∃ c, (fun c => c = (acceptAll : Nat → Bool)) c ∧
          SoundCompleteOn (fun n => n = 0) (fun n => n = 0) c) ↔
        ∃ c, (fun c => c = (acceptAll : Nat → Bool)) c ∧
          ∀ p, (fun n => n = 0) p → (c p = true ↔ (fun n => n = 0) p)) := by
  refine ⟨fun c₁ c₂ h₁ h₂ => ?_, fun h => cex_decides_on_fragment_without_soundness.2
    (h.mpr cex_decides_on_fragment_without_soundness.1)⟩
  subst h₁; subst h₂
  rfl

/-- Same theorem without `hK`: `K = {belowTwo, zeroOrLarge}` contains the
decider `belowTwo` of `F = (· < 2)`, and `zeroOrLarge` decides `good = (· = 0)`
on `F`, but neither member is sound, so the equivalence fails. -/
theorem cex_decides_on_iff_needs_andClosed :
    DecidedIn (fun c => c = belowTwo ∨ c = zeroOrLarge) (fun n => n < 2) ∧
    ¬ ((∃ c, (fun c => c = belowTwo ∨ c = zeroOrLarge) c ∧
          SoundCompleteOn (fun n => n = 0) (fun n => n < 2) c) ↔
        ∃ c, (fun c => c = belowTwo ∨ c = zeroOrLarge) c ∧
          ∀ p, (fun n => n < 2) p → (c p = true ↔ (fun n => n = 0) p)) := by
  refine ⟨⟨belowTwo, Or.inl rfl, fun p => by simp [belowTwo]⟩, fun h => ?_⟩
  have hr : ∃ c, (fun c => c = belowTwo ∨ c = zeroOrLarge) c ∧
      ∀ p, (fun n => n < 2) p → (c p = true ↔ (fun n => n = 0) p) := by
    refine ⟨zeroOrLarge, Or.inr rfl, fun p hp => ?_⟩
    simp only [zeroOrLarge, decide_eq_true_eq]
    omega
  obtain ⟨c, hc, hs, _⟩ := h.mpr hr
  rcases hc with rfl | rfl
  · exact absurd (hs 1 rfl) (by decide)
  · exact absurd (hs 2 rfl) (by decide)

/-- Positive control for R6g (and a satisfier for R6f): on the finite
fragment `n < 10`, the allowlist `[0, 2, 4, 6, 8]` is sound and complete. -/
theorem positive_control_allowlist_soundCompleteOn_finite_fragment :
    SoundCompleteOn evenGood (fun n => n < 10) (allowlist [0, 2, 4, 6, 8]) := by
  constructor
  · intro p hp
    have hmem : p ∈ [0, 2, 4, 6, 8] := by simpa [allowlist] using hp
    have hall : ∀ a ∈ [0, 2, 4, 6, 8], evenGood a := by decide
    exact hall p hmem
  · intro p hg hF
    have hall : ∀ q, q < 10 → evenGood q → q ∈ [0, 2, 4, 6, 8] := by decide
    simpa [allowlist] using hall p hF hg

/-! ## Non-vacuity witnesses -/

/-- R6a instance: the law on `n < 10` has a computable satisfier
(`evenBelowTen`) and excludes `rejectAll`. -/
theorem nonvacuous_soundCompleteOn :
    SoundCompleteOn evenGood (fun n => n < 10) evenBelowTen ∧
    ¬ SoundCompleteOn evenGood (fun n => n < 10) rejectAll :=
  ⟨soundCompleteOn_example_evenBelowTen, fun h => not_completeOn_example_rejectAll h.2⟩

/-- R6c pointwise and class forms are non-degenerate on the proper fragment
`n < 10`: the right-hand side holds for `evenBelowTen` (which is conservative
off the fragment: it rejects the good program `10`) and fails for
`rejectAll`; correspondingly the class right-hand side holds for
`K = {evenBelowTen}` and fails for `K = {rejectAll}`. -/
theorem nonvacuous_soundCompleteOn_iff_sound_and_decides_on :
    (Sound evenGood evenBelowTen ∧ ∀ p, p < 10 → (evenBelowTen p = true ↔ evenGood p)) ∧
    evenBelowTen 10 = false ∧ evenGood 10 ∧
    ¬ (Sound evenGood rejectAll ∧ ∀ p, p < 10 → (rejectAll p = true ↔ evenGood p)) ∧
    (∃ c, (fun c => c = evenBelowTen) c ∧ Sound evenGood c ∧
      ∀ p, p < 10 → (c p = true ↔ evenGood p)) ∧
    ¬ (∃ c, (fun c => c = (rejectAll : Nat → Bool)) c ∧ Sound evenGood c ∧
      ∀ p, p < 10 → (c p = true ↔ evenGood p)) := by
  have hpos : Sound evenGood evenBelowTen ∧ ∀ p, p < 10 → (evenBelowTen p = true ↔ evenGood p) :=
    ⟨sound_example_evenBelowTen, fun p hp =>
      ⟨sound_example_evenBelowTen p, fun hg => completeOn_example_evenBelowTen p hg hp⟩⟩
  have hneg : ¬ (Sound evenGood rejectAll ∧ ∀ p, p < 10 → (rejectAll p = true ↔ evenGood p)) := by
    rintro ⟨_, hdec⟩
    have h0 := (hdec 0 (by decide)).mpr rfl
    simp [rejectAll] at h0
  refine ⟨hpos, rfl, rfl, hneg, ⟨evenBelowTen, rfl, hpos⟩, ?_⟩
  rintro ⟨c, rfl, h⟩
  exact hneg h

/-- R6c full-fragment forms are non-degenerate: `evenExact` decides
`evenGood` and `evenBelowTen` does not; correspondingly the class right-hand
side holds for `K = {evenExact}` and fails for `K = {evenBelowTen}`. -/
theorem nonvacuous_soundCompleteOn_univ_iff_decides :
    (∀ p, evenExact p = true ↔ evenGood p) ∧ ¬ (∀ p, evenBelowTen p = true ↔ evenGood p) ∧
    (∃ c, (fun c => c = evenExact) c ∧ ∀ p, c p = true ↔ evenGood p) ∧
    ¬ (∃ c, (fun c => c = evenBelowTen) c ∧ ∀ p, c p = true ↔ evenGood p) := by
  have hpos : ∀ p, evenExact p = true ↔ evenGood p := fun p => by simp [evenExact, evenGood]
  have hneg : ¬ (∀ p, evenBelowTen p = true ↔ evenGood p) := by
    intro h
    have h10 := (h 10).mpr rfl
    simp [evenBelowTen] at h10
  refine ⟨hpos, hneg, ⟨evenExact, rfl, hpos⟩, ?_⟩
  rintro ⟨c, rfl, h⟩
  exact hneg h

/-- Hypotheses of the `&&`-closure statement of R6c hold: the class of all
checkers is closed under `&&` and decides the fragment `n < 10`. -/
theorem nonvacuous_exists_soundCompleteOn_in_class_iff_decides_on :
    AndClosed (fun _ : Nat → Bool => True) ∧ DecidedIn (fun _ : Nat → Bool => True) (fun n => n < 10) :=
  andClosed_decidedIn_example_all

/-! ## Restricted classes for the `&&`-closure statement of R6c

The class of all checkers (used above) already contains a sound decider of
`good` on `F`, so it does not exercise the step of the closure statement in
which an unsound decider is repaired by `&&`-ing it with a decider of `F`.
The two finite classes below do. -/

/-- In the four-element class `{rejectAll, belowTwo, zeroOrLarge, (· == 0)}`,
which is closed under `&&` and contains the decider `belowTwo` of
`F = (· < 2)`, the member `zeroOrLarge` decides `good = (· = 0)` on `F` but is
unsound; `belowTwo && zeroOrLarge` is `(· == 0)`, a member that is sound and
complete on `F`. -/
theorem andClosed_class_repairs_unsound_decider_example :
    AndClosed (fun c => c = rejectAll ∨ c = belowTwo ∨ c = zeroOrLarge ∨ c = (fun n : Nat => n == 0)) ∧
    DecidedIn (fun c => c = rejectAll ∨ c = belowTwo ∨ c = zeroOrLarge ∨ c = (fun n : Nat => n == 0))
      (fun n => n < 2) ∧
    (¬ Sound (fun n => n = 0) zeroOrLarge ∧ ∀ p, p < 2 → (zeroOrLarge p = true ↔ p = 0)) ∧
    (fun p => belowTwo p && zeroOrLarge p) = (fun n : Nat => n == 0) ∧
    SoundCompleteOn (fun n => n = 0) (fun n => n < 2) (fun n : Nat => n == 0) := by
  refine ⟨?_, ⟨belowTwo, Or.inr (Or.inl rfl), fun p => by simp [belowTwo]⟩,
    ⟨fun hs => absurd (hs 2 (by decide)) (by decide), fun p hp => ?_⟩, ?_, ?_, ?_⟩
  · intro c₁ c₂ h₁ h₂
    rcases h₁ with rfl | rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl <;>
      first
      | (left; funext p; rcases p with _ | _ | p <;> simp [rejectAll, belowTwo, zeroOrLarge]; done)
      | (right; left; funext p; rcases p with _ | _ | p <;>
          simp [belowTwo, zeroOrLarge]; done)
      | (right; right; left; funext p; rcases p with _ | _ | p <;>
          simp [belowTwo, zeroOrLarge]; done)
      | (right; right; right; funext p; rcases p with _ | _ | p <;>
          simp [belowTwo, zeroOrLarge]; done)
  · simp only [zeroOrLarge, decide_eq_true_eq]
    omega
  · funext p
    rcases p with _ | _ | p <;> simp [belowTwo, zeroOrLarge]
  · intro p hp
    simpa using hp
  · intro p hg _
    simpa using hg

/-- In the two-element class `{rejectAll, belowTwo}`, which is closed under
`&&` and decides `F = (· < 2)`, both sides of the closure statement are false
for `good = (· = 0)`. -/
theorem andClosed_class_both_sides_false_example :
    AndClosed (fun c => c = rejectAll ∨ c = belowTwo) ∧
    DecidedIn (fun c => c = rejectAll ∨ c = belowTwo) (fun n => n < 2) ∧
    ¬ (∃ c, (c = rejectAll ∨ c = belowTwo) ∧ ∀ p, p < 2 → (c p = true ↔ p = 0)) ∧
    ¬ (∃ c, (c = rejectAll ∨ c = belowTwo) ∧
        SoundCompleteOn (fun n => n = 0) (fun n => n < 2) c) := by
  have hrhs : ¬ (∃ c, (c = rejectAll ∨ c = belowTwo) ∧ ∀ p, p < 2 → (c p = true ↔ p = 0)) := by
    rintro ⟨c, rfl | rfl, h⟩
    · exact Bool.noConfusion ((h 0 (by decide)).mpr rfl)
    · exact absurd ((h 1 (by decide)).mp rfl) (by decide)
  refine ⟨?_, ⟨belowTwo, Or.inr rfl, fun p => by simp [belowTwo]⟩, hrhs, ?_⟩
  · intro c₁ c₂ h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · left; rfl
    · left; rfl
    · left; funext p; simp [rejectAll]
    · right; funext p; simp [belowTwo]
  · rintro ⟨c, hc, hs, hcomp⟩
    exact hrhs ⟨c, hc, fun p hp => ⟨hs p, fun hg => hcomp p hg hp⟩⟩

/-- R6e is non-degenerate: on `n < 10` the right-hand side holds; on the
fragment `n = 1` it fails and `rejectAll` is admitted. -/
theorem nonvacuous_not_soundCompleteOn_rejectAll_iff :
    (∃ p, p < 10 ∧ evenGood p) ∧ SoundCompleteOn evenGood (fun n => n = 1) rejectAll :=
  ⟨⟨0, by decide, rfl⟩, soundCompleteOn_example_rejectAll_odd_fragment⟩

/-- R6f is non-degenerate on the fragment `n < 10`: the right-hand side holds
for `[0, 2, 4, 6, 8]` and fails for `[0, 2, 4, 6]` (which misses the good
program `8`). -/
theorem nonvacuous_soundCompleteOn_allowlist_iff :
    ((∀ a ∈ [0, 2, 4, 6, 8], evenGood a) ∧
      ∀ p, p < 10 → evenGood p → p ∈ [0, 2, 4, 6, 8]) ∧
    ¬ ((∀ a ∈ [0, 2, 4, 6], evenGood a) ∧
      ∀ p, p < 10 → evenGood p → p ∈ [0, 2, 4, 6]) := by
  refine ⟨⟨by decide, by decide⟩, fun h => ?_⟩
  have := h.2 8 (by decide) rfl
  revert this
  decide

/-- R6g is not vacuous: the law "sound and complete for `evenGood` on all
programs" is satisfied by `evenExact`, so excluding every allowlist is not
an artifact of an unsatisfiable law. -/
theorem nonvacuous_no_allowlist_soundCompleteOn_evenGood_univ :
    SoundCompleteOn evenGood (fun _ => True) evenExact :=
  ⟨sound_example_evenExact, fun p hg _ => by simpa [evenExact, evenGood] using hg⟩

end Toy.Checker
