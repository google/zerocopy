import ToyIL.Basic

/-!
# Consequence rules, duality, and the agreement/denial principles

Hoare triples allow strengthening the pre and weakening the post; IL triples allow the
reverse. The exact post-image is the unique assertion that is both a Hoare post and an IL
post. IL triples refute Hoare triples (the Principle of Denial), and every invalid Hoare
triple is refuted by an IL triple whose post is a single state outside the Hoare post.
-/

namespace Toy.IL

variable {σ : Type}

/-! ### Consequence -/

/-- Hoare consequence: strengthen the pre (`P' ⊆ P`) and weaken the post (`Q ⊆ Q'`). -/
theorem hoare_consequence_strengthen_pre_weaken_post {P P' Q Q' : Assn σ} {c : Cmd σ}
    {e : Exit} (hpre : Entails P' P) (h : Hoare P c e Q) (hpost : Entails Q Q') :
    Hoare P' c e Q' := by
  rintro t ⟨s, hs, hst⟩
  exact hpost t (h t ⟨s, hpre s hs, hst⟩)

/-- IL consequence, in the reverse direction: weaken the pre (`P ⊆ P'`) and strengthen
the post (`Q' ⊆ Q`). -/
theorem il_consequence_weaken_pre_strengthen_post {P P' Q Q' : Assn σ} {c : Cmd σ}
    {e : Exit} (hpre : Entails P P') (h : IL P c e Q) (hpost : Entails Q' Q) :
    IL P' c e Q' := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := h t (hpost t ht)
  exact ⟨s, hpre s hs, hst⟩

/-! #### Counterexamples: each hypothesis is needed, and the other logic's direction fails

Each statement instantiates `c := skip`, `e := ok` over `Nat`, makes all the *other*
hypotheses true, makes the hypothesis under test false (where it is a direction
hypothesis, its *reverse* direction is shown to hold instead), and shows the conclusion
false. -/

/-- Weakening the pre of a Hoare triple is unsound: `P ⊆ P'` (IL direction) instead of
`P' ⊆ P`. -/
theorem hoare_consequence_pre_tight :
    let P : Assn Nat := fun n => n = 0
    let P' : Assn Nat := fun _ => True
    let Q : Assn Nat := fun n => n = 0
    let Q' : Assn Nat := fun n => n = 0
    Entails P P' ∧ ¬ Entails P' P ∧ Hoare P Cmd.skip .ok Q ∧ Entails Q Q' ∧
      ¬ Hoare P' Cmd.skip .ok Q' := by
  refine ⟨fun _ _ => trivial, fun h => absurd (h 1 trivial) (by decide), ?_, fun _ h => h, ?_⟩
  · rintro t ⟨s, hs, h⟩; simp at h; omega
  · intro h; exact absurd (h 1 ⟨1, trivial, by simp⟩) (by decide)

/-- The Hoare triple premise is needed. -/
theorem hoare_consequence_triple_tight :
    let P : Assn Nat := fun _ => True
    let Q : Assn Nat := fun n => n = 0
    Entails P P ∧ ¬ Hoare P Cmd.skip .ok Q ∧ Entails Q Q ∧ ¬ Hoare P Cmd.skip .ok Q := by
  have h : ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun n => n = 0) := by
    intro h; exact absurd (h 1 ⟨1, trivial, by simp⟩) (by decide)
  exact ⟨fun _ h => h, h, fun _ h => h, h⟩

/-- Strengthening the post of a Hoare triple is unsound: `Q' ⊆ Q` (IL direction) instead
of `Q ⊆ Q'`. -/
theorem hoare_consequence_post_tight :
    let P : Assn Nat := fun _ => True
    let Q : Assn Nat := fun _ => True
    let Q' : Assn Nat := fun n => n = 0
    Entails P P ∧ Hoare P Cmd.skip .ok Q ∧ Entails Q' Q ∧ ¬ Entails Q Q' ∧
      ¬ Hoare P Cmd.skip .ok Q' := by
  refine ⟨fun _ h => h, fun _ _ => trivial, fun _ _ => trivial,
    fun h => absurd (h 1 trivial) (by decide), ?_⟩
  intro h; exact absurd (h 1 ⟨1, trivial, by simp⟩) (by decide)

/-- Strengthening the pre of an IL triple is unsound: `P' ⊆ P` (Hoare direction) instead
of `P ⊆ P'`. -/
theorem il_consequence_pre_tight :
    let P : Assn Nat := fun _ => True
    let P' : Assn Nat := fun n => n = 0
    let Q : Assn Nat := fun n => n = 1
    let Q' : Assn Nat := fun n => n = 1
    Entails P' P ∧ ¬ Entails P P' ∧ IL P Cmd.skip .ok Q ∧ Entails Q' Q ∧
      ¬ IL P' Cmd.skip .ok Q' := by
  refine ⟨fun _ _ => trivial, fun h => absurd (h 1 trivial) (by decide), ?_, fun _ h => h, ?_⟩
  · intro t ht; exact ⟨t, trivial, by simp⟩
  · intro h
    obtain ⟨s, hs, hst⟩ := h 1 rfl
    simp at hst; omega

/-- The IL triple premise is needed. -/
theorem il_consequence_triple_tight :
    let P : Assn Nat := fun n => n = 0
    let Q : Assn Nat := fun n => n = 1
    Entails P P ∧ ¬ IL P Cmd.skip .ok Q ∧ Entails Q Q ∧ ¬ IL P Cmd.skip .ok Q := by
  have h : ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) := by
    intro h
    obtain ⟨s, hs, hst⟩ := h 1 rfl
    simp at hst; omega
  exact ⟨fun _ h => h, h, fun _ h => h, h⟩

/-- Weakening the post of an IL triple is unsound: `Q ⊆ Q'` (Hoare direction) instead of
`Q' ⊆ Q`. -/
theorem il_consequence_post_tight :
    let P : Assn Nat := fun n => n = 0
    let Q : Assn Nat := fun n => n = 0
    let Q' : Assn Nat := fun _ => True
    Entails P P ∧ IL P Cmd.skip .ok Q ∧ Entails Q Q' ∧ ¬ Entails Q' Q ∧
      ¬ IL P Cmd.skip .ok Q' := by
  refine ⟨fun _ h => h, ?_, fun _ _ => trivial, fun h => absurd (h 1 trivial) (by decide), ?_⟩
  · intro t ht; exact ⟨t, ht, by simp⟩
  · intro h
    obtain ⟨s, hs, hst⟩ := h 1 trivial
    simp at hst; omega

/-- Non-vacuity of Hoare consequence: all three hypotheses hold with a strict
strengthening of the pre (`{x = 0} ⊊ {x ≤ 1}`) and a strict weakening of the post
(`{x ≤ 2} ⊊ {x ≤ 3}`), and the conclusion holds. -/
theorem nonvacuity_hoare_consequence :
    Entails (fun n : Nat => n = 0) (fun n => n ≤ 1) ∧
    ¬ Entails (fun n : Nat => n ≤ 1) (fun n => n = 0) ∧
    Hoare (fun n : Nat => n ≤ 1) (.assign Nat.succ) .ok (fun n => n ≤ 2) ∧
    Entails (fun n : Nat => n ≤ 2) (fun n => n ≤ 3) ∧
    ¬ Entails (fun n : Nat => n ≤ 3) (fun n => n ≤ 2) ∧
    Hoare (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun n => n ≤ 3) := by
  refine ⟨fun _ h => by omega, fun h => absurd (h 1 (by decide)) (by decide), ?_,
    fun _ h => by omega, fun h => absurd (h 3 (by decide)) (by decide), ?_⟩
  · rintro t ⟨s, hs, h⟩; simp at h; omega
  · rintro t ⟨s, hs, h⟩; simp at h; omega

/-- Non-vacuity of IL consequence: all three hypotheses hold with a strict weakening of
the pre (`{x ≤ 1} ⊊ {x ≤ 2}`) and a strict strengthening of the post
(`{x = 1} ⊊ {x = 1 ∨ x = 2}`), and the conclusion holds. -/
theorem nonvacuity_il_consequence :
    Entails (fun n : Nat => n ≤ 1) (fun n => n ≤ 2) ∧
    ¬ Entails (fun n : Nat => n ≤ 2) (fun n => n ≤ 1) ∧
    IL (fun n : Nat => n ≤ 1) (.assign Nat.succ) .ok (fun n => n = 1 ∨ n = 2) ∧
    Entails (fun n : Nat => n = 1) (fun n => n = 1 ∨ n = 2) ∧
    ¬ Entails (fun n : Nat => n = 1 ∨ n = 2) (fun n => n = 1) ∧
    IL (fun n : Nat => n ≤ 2) (.assign Nat.succ) .ok (fun n => n = 1) := by
  refine ⟨fun _ h => by omega, fun h => absurd (h 2 (by decide)) (by decide), ?_,
    fun _ h => Or.inl h, fun h => absurd (h 2 (Or.inr rfl)) (by decide), ?_⟩
  · rintro t (rfl | rfl)
    · exact ⟨0, by decide, .assign⟩
    · exact ⟨1, by decide, .assign⟩
  · rintro t rfl; exact ⟨0, by decide, .assign⟩

/-! ### Duality -/

/-- An assertion is both a Hoare post and an IL post (for the same pre, command and exit
kind) iff it is exactly the post-image. -/
theorem hoare_and_il_iff_eq_post {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
    Hoare P c e Q ∧ IL P c e Q ↔ ∀ t, Q t ↔ post c e P t := by
  constructor
  · rintro ⟨h₁, h₂⟩ t; exact ⟨h₂ t, h₁ t⟩
  · intro h; exact ⟨fun t ht => (h t).2 ht, fun t ht => (h t).1 ht⟩

/-- The post-image is always an IL post (the largest one). -/
theorem il_post_self (P : Assn σ) (c : Cmd σ) (e : Exit) : IL P c e (post c e P) :=
  fun _ h => h

/-- The post-image is always a Hoare post (the smallest one). -/
theorem hoare_post_self (P : Assn σ) (c : Cmd σ) (e : Exit) : Hoare P c e (post c e P) :=
  fun _ h => h

/-- O'Hearn's ∧∨ symmetry, IL half: IL posts for a fixed pre are closed under
disjunction (and conversely). -/
theorem il_or_post_iff {P Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit} :
    IL P c e Q₁ ∧ IL P c e Q₂ ↔ IL P c e (fun t => Q₁ t ∨ Q₂ t) := by
  constructor
  · rintro ⟨h₁, h₂⟩ t (ht | ht)
    · exact h₁ t ht
    · exact h₂ t ht
  · intro h; exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩

/-- O'Hearn's ∧∨ symmetry, Hoare half: Hoare posts for a fixed pre are closed under
conjunction (and conversely). -/
theorem hoare_and_post_iff {P Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit} :
    Hoare P c e Q₁ ∧ Hoare P c e Q₂ ↔ Hoare P c e (fun t => Q₁ t ∧ Q₂ t) := by
  constructor
  · rintro ⟨h₁, h₂⟩ t ht; exact ⟨h₁ t ht, h₂ t ht⟩
  · intro h; exact ⟨fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩

/-- Non-vacuity of the duality: for `x := 0 + x := 2` from `True`, the post `x = 0 ∨ x = 2`
is exact, while `x = 2` is only an IL post and `x ≤ 5` only a Hoare post. -/
theorem nonvacuity_duality :
    let c : Cmd Nat := .choice (.assign (fun _ => 0)) (.assign (fun _ => 2))
    (Hoare (fun _ => True) c .ok (fun n => n = 0 ∨ n = 2) ∧
      IL (fun _ => True) c .ok (fun n => n = 0 ∨ n = 2)) ∧
    (IL (fun _ => True) c .ok (fun n => n = 2) ∧ ¬ Hoare (fun _ => True) c .ok (fun n => n = 2)) ∧
    (Hoare (fun _ => True) c .ok (fun n => n ≤ 5) ∧ ¬ IL (fun _ => True) c .ok (fun n => n ≤ 5)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro t ⟨s, _, h⟩; simp at h; omega
  · rintro t (rfl | rfl)
    · exact ⟨0, trivial, .choiceL .assign⟩
    · exact ⟨0, trivial, .choiceR .assign⟩
  · rintro t rfl; exact ⟨0, trivial, .choiceR .assign⟩
  · intro h; exact absurd (h 0 ⟨0, trivial, .choiceL .assign⟩) (by decide)
  · rintro t ⟨s, _, h⟩; simp at h; omega
  · intro h
    obtain ⟨s, _, hs⟩ := h 1 (by decide)
    simp at hs

/-- For a fixed pre, IL posts are also closed under conjunction (by strengthening the
post); what fails for IL is conjoining triples with *different* pres
(`il_conjunction_rule_unsound`). -/
theorem il_and_post_of_il_left {P Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h : IL P c e Q₁) : IL P c e (fun t => Q₁ t ∧ Q₂ t) :=
  fun t ht => h t ht.1

/-- The converse of `il_and_post_of_il_left` fails: an IL triple with a conjunctive post does
not split. `[x = 0] skip [ok : True ∧ False]` holds (empty post) but
`[x = 0] skip [ok : True]` does not. -/
theorem il_and_post_not_split :
    IL (fun n : Nat => n = 0) Cmd.skip .ok (fun _ => True ∧ False) ∧
      ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun _ => True) := by
  refine ⟨fun _ h => h.2.elim, ?_⟩
  intro h
  obtain ⟨s, hs, hst⟩ := h 1 trivial
  simp at hst; omega

/-- A Hoare triple with a disjunctive post does not split: for `x := 0 + x := 2` from
`True`, `{ok : x = 0 ∨ x = 2}` holds but `{ok : x = 0}` does not. (Hoare triples with
different pres *are* closed under disjunction: `hoare_disjunction_sound`.) -/
theorem hoare_or_post_not_split :
    let c : Cmd Nat := .choice (.assign (fun _ => 0)) (.assign (fun _ => 2))
    Hoare (fun _ => True) c .ok (fun n => n = 0 ∨ n = 2) ∧
      ¬ Hoare (fun _ => True) c .ok (fun n => n = 0) := by
  refine ⟨?_, ?_⟩
  · rintro t ⟨s, _, h⟩; simp at h; omega
  · intro h; exact absurd (h 2 ⟨0, trivial, .choiceR .assign⟩) (by decide)

/-! ### Agreement and denial -/

/-- O'Hearn's Principle of Agreement: if `[U] c [e : U']`, `U ⊆ O`, and `{O} c {e : O'}`,
then `U' ⊆ O'`. -/
theorem il_hoare_agreement {U U' O O' : Assn σ} {c : Cmd σ} {e : Exit}
    (hil : IL U c e U') (hsub : Entails U O) (hh : Hoare O c e O') : Entails U' O' := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := hil t ht
  exact hh t ⟨s, hsub s hs, hst⟩

/-- O'Hearn's Principle of Denial (the contrapositive form of agreement): an IL triple
whose pre lies inside `O` and whose post escapes `O'` refutes `{O} c {e : O'}`. -/
theorem il_denies_hoare {U U' O O' : Assn σ} {c : Cmd σ} {e : Exit}
    (hil : IL U c e U') (hsub : Entails U O) (hout : ¬ Entails U' O') :
    ¬ Hoare O c e O' :=
  fun hh => hout (il_hoare_agreement hil hsub hh)

/-- The IL premise of agreement is needed. -/
theorem il_hoare_agreement_il_tight :
    let U : Assn Nat := fun n => n = 0
    let U' : Assn Nat := fun n => n = 1
    let O : Assn Nat := fun n => n = 0
    let O' : Assn Nat := fun n => n = 0
    ¬ IL U Cmd.skip .ok U' ∧ Entails U O ∧ Hoare O Cmd.skip .ok O' ∧ ¬ Entails U' O' := by
  refine ⟨?_, fun _ h => h, ?_, fun h => absurd (h 1 rfl) (by decide)⟩
  · intro h
    obtain ⟨s, hs, hst⟩ := h 1 rfl
    simp at hst; omega
  · rintro t ⟨s, hs, h⟩; simp at h; omega

/-- The inclusion premise `U ⊆ O` of agreement is needed. -/
theorem il_hoare_agreement_sub_tight :
    let U : Assn Nat := fun _ => True
    let U' : Assn Nat := fun n => n = 1
    let O : Assn Nat := fun n => n = 0
    let O' : Assn Nat := fun n => n = 0
    IL U Cmd.skip .ok U' ∧ ¬ Entails U O ∧ Hoare O Cmd.skip .ok O' ∧ ¬ Entails U' O' := by
  refine ⟨?_, fun h => absurd (h 1 trivial) (by decide), ?_,
    fun h => absurd (h 1 rfl) (by decide)⟩
  · intro t _; exact ⟨t, trivial, by simp⟩
  · rintro t ⟨s, hs, h⟩; simp at h; omega

/-- The Hoare premise of agreement is needed. -/
theorem il_hoare_agreement_hoare_tight :
    let U : Assn Nat := fun _ => True
    let U' : Assn Nat := fun n => n = 1
    let O : Assn Nat := fun _ => True
    let O' : Assn Nat := fun n => n = 0
    IL U Cmd.skip .ok U' ∧ Entails U O ∧ ¬ Hoare O Cmd.skip .ok O' ∧ ¬ Entails U' O' := by
  refine ⟨?_, fun _ h => h, ?_, fun h => absurd (h 1 rfl) (by decide)⟩
  · intro t _; exact ⟨t, trivial, by simp⟩
  · intro h; exact absurd (h 1 ⟨1, trivial, by simp⟩) (by decide)

/-- Non-vacuity of agreement with a proper inclusion and a nondeterministic program. -/
theorem nonvacuity_agreement :
    let c : Cmd Nat := .choice (.assign (fun _ => 0)) (.assign (fun _ => 2))
    IL (fun n => n = 5) c .ok (fun n => n = 2) ∧ Entails (fun n : Nat => n = 5) (fun _ => True) ∧
      Hoare (fun _ => True) c .ok (fun n => n % 2 = 0) ∧
      Entails (fun n : Nat => n = 2) (fun n => n % 2 = 0) := by
  refine ⟨?_, fun _ _ => trivial, ?_, fun _ h => by omega⟩
  · rintro t rfl; exact ⟨5, rfl, .choiceR .assign⟩
  · rintro t ⟨s, _, h⟩; simp at h; omega

/-- Non-vacuity of denial: for `x := 0 + x := 2`, `[x = 5] c [ok : x = 2]` holds,
`{x = 5} ⊆ True`, and the post `{x = 2}` escapes `{x = 0}`; hence
`{True} c {ok : x = 0}` is refuted (the conclusion holds). -/
theorem nonvacuity_denial :
    let c : Cmd Nat := .choice (.assign (fun _ => 0)) (.assign (fun _ => 2))
    IL (fun n => n = 5) c .ok (fun n => n = 2) ∧ Entails (fun n : Nat => n = 5) (fun _ => True) ∧
      ¬ Entails (fun n : Nat => n = 2) (fun n => n = 0) ∧
      ¬ Hoare (fun _ => True) c .ok (fun n => n = 0) := by
  refine ⟨?_, fun _ _ => trivial, fun h => absurd (h 2 rfl) (by decide), ?_⟩
  · rintro t rfl; exact ⟨5, rfl, .choiceR .assign⟩
  · intro h; exact absurd (h 2 ⟨5, trivial, .choiceR .assign⟩) (by decide)

/-- The escape hypothesis `hout : ¬ Entails U' O'` of denial is needed: with `hil` and
`hsub` true but `U' ⊆ O'`, the Hoare triple is valid, so the conclusion `¬ Hoare O c e O'`
fails. -/
theorem il_denies_hoare_hout_tight :
    let c : Cmd Nat := .choice (.assign (fun _ => 0)) (.assign (fun _ => 2))
    IL (fun n => n = 5) c .ok (fun n => n = 2) ∧ Entails (fun n : Nat => n = 5) (fun _ => True) ∧
      Entails (fun n : Nat => n = 2) (fun n => n % 2 = 0) ∧
      Hoare (fun _ => True) c .ok (fun n => n % 2 = 0) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := nonvacuity_agreement
  exact ⟨h₁, h₂, h₄, h₃⟩

/-- An empty post is contained in every assertion, so an IL triple with empty post never
satisfies the escape hypothesis of denial. -/
theorem entails_empty_left (O' : Assn σ) : Entails (fun _ => False) O' :=
  fun _ h => h.elim

/-- Refutation is complete: a Hoare triple is invalid iff some single state outside its
post is the post of a valid IL triple with the same pre, command and exit kind. -/
theorem not_hoare_iff_exists_il_singleton_outside {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
    ¬ Hoare P c e Q ↔ ∃ t, ¬ Q t ∧ IL P c e (fun x => x = t) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro t ht
    apply Classical.byContradiction
    intro hq
    exact hne ⟨t, hq, fun x hx => hx ▸ ht⟩
  · rintro ⟨t, hq, hil⟩ hh
    exact hq (hh t (hil t rfl))

/-- Non-vacuity: `{x = 0} x := x + 1 {ok : x = 0}` is refuted by `[x = 0] x := x + 1 [ok : x = 1]`. -/
theorem nonvacuity_not_hoare_singleton :
    ¬ Hoare (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun n => n = 0) ∧
    (¬ (1 = 0) ∧ IL (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun x => x = 1)) :=
  ⟨hoare_neg, by decide, il_pos⟩

end Toy.IL
