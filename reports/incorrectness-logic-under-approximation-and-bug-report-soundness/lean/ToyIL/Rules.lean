import ToyIL.Licensing

/-!
# Proof rules: soundness of the IL rules, conjunction vs disjunction, completeness

`ILDeriv` is the generic proof system of O'Hearn's *Incorrectness Logic* (POPL 2020,
Fig. 2) specialised to this language, with semantic assertions and semantic entailment as
the consequence oracle. The `[ok : false]` / `[er : false]` halves of the Unit, Error,
Assume and Assignment axioms are instances of `empty` and are therefore not separate
constructors; the Unit axiom `[p] skip [ok : p]` is `assumeOk` for `skip = assume true`
followed by consequence.
-/

namespace Toy.IL

variable {σ : Type}

/-- Derivability in the IL proof system. Each constructor is one rule of O'Hearn's Fig. 2.
`backwardsVariant` takes the semantic reading of "`n` fresh": its premise is one
derivation for every natural number `n`. -/
inductive ILDeriv : Assn σ → Cmd σ → Exit → Assn σ → Prop where
  /-- Empty under-approximates: `[p] C [ε : false]`. -/
  | empty {P : Assn σ} {c : Cmd σ} {e : Exit} : ILDeriv P c e (fun _ => False)
  /-- Consequence (IL direction): `p ⊆ p'`, `[p] C [ε : q]`, `q' ⊆ q` give `[p'] C [ε : q']`. -/
  | conseq {P P' Q Q' : Assn σ} {c : Cmd σ} {e : Exit} :
      Entails P P' → ILDeriv P c e Q → Entails Q' Q → ILDeriv P' c e Q'
  /-- Disjunction. -/
  | disj {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit} :
      ILDeriv P₁ c e Q₁ → ILDeriv P₂ c e Q₂ →
        ILDeriv (fun s => P₁ s ∨ P₂ s) c e (fun s => Q₁ s ∨ Q₂ s)
  /-- Sequencing (short-circuit). -/
  | seqShort {P R : Assn σ} {c₁ c₂ : Cmd σ} :
      ILDeriv P c₁ .er R → ILDeriv P (.seq c₁ c₂) .er R
  /-- Sequencing (normal). -/
  | seqNormal {P Q R : Assn σ} {c₁ c₂ : Cmd σ} {e : Exit} :
      ILDeriv P c₁ .ok Q → ILDeriv Q c₂ e R → ILDeriv P (.seq c₁ c₂) e R
  /-- Iterate zero. -/
  | iterZero {P : Assn σ} {c : Cmd σ} : ILDeriv P (.star c) .ok P
  /-- Iterate non-zero. -/
  | iterNonzero {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
      ILDeriv P (.seq (.star c) c) e Q → ILDeriv P (.star c) e Q
  /-- Backwards variant. -/
  | backwardsVariant {c : Cmd σ} (p : Nat → Assn σ) :
      (∀ n, ILDeriv (p n) c .ok (p (n + 1))) →
        ILDeriv (p 0) (.star c) .ok (fun s => ∃ n, p n s)
  /-- Choice (left). -/
  | choiceL {P Q : Assn σ} {c₁ c₂ : Cmd σ} {e : Exit} :
      ILDeriv P c₁ e Q → ILDeriv P (.choice c₁ c₂) e Q
  /-- Choice (right). -/
  | choiceR {P Q : Assn σ} {c₁ c₂ : Cmd σ} {e : Exit} :
      ILDeriv P c₂ e Q → ILDeriv P (.choice c₁ c₂) e Q
  /-- Error: `[p] error() [er : p]`. -/
  | errorEr {P : Assn σ} : ILDeriv P .error .er P
  /-- Assume: `[p] assume B [ok : p ∧ B]`. -/
  | assumeOk {P : Assn σ} {b : σ → Bool} :
      ILDeriv P (.assume b) .ok (fun s => P s ∧ b s = true)
  /-- Assignment (as a state update): `[p] f [ok : ∃ s, p s ∧ t = f s]`. -/
  | assign {P : Assn σ} {f : σ → σ} :
      ILDeriv P (.assign f) .ok (fun t => ∃ s, P s ∧ t = f s)

/-! ### Soundness -/

/-- Semantic soundness of the backwards-variant rule. -/
theorem il_backwardsVariant_sound {c : Cmd σ} (p : Nat → Assn σ)
    (h : ∀ n, IL (p n) c .ok (p (n + 1))) : IL (p 0) (.star c) .ok (fun s => ∃ n, p n s) := by
  rintro t ⟨n, hn⟩
  induction n generalizing t with
  | zero => exact ⟨t, hn, .starNil⟩
  | succ n ih =>
    obtain ⟨m, hm, hmt⟩ := h n t hn
    obtain ⟨s, hs, hsm⟩ := ih m hm
    exact ⟨s, hs, exec_star_snoc hsm hmt⟩

/-- Soundness of the IL proof system: every derivable triple is a valid under-approximate
triple. -/
theorem ilDeriv_sound {P Q : Assn σ} {c : Cmd σ} {e : Exit} (h : ILDeriv P c e Q) :
    IL P c e Q := by
  induction h with
  | empty => exact il_empty_post _ _ _
  | conseq hpre _ hpost ih => exact il_consequence_weaken_pre_strengthen_post hpre ih hpost
  | disj _ _ ih₁ ih₂ =>
    rintro t (ht | ht)
    · obtain ⟨s, hs, hst⟩ := ih₁ t ht; exact ⟨s, Or.inl hs, hst⟩
    · obtain ⟨s, hs, hst⟩ := ih₂ t ht; exact ⟨s, Or.inr hs, hst⟩
  | seqShort _ ih =>
    intro t ht
    obtain ⟨s, hs, hst⟩ := ih t ht
    exact ⟨s, hs, .seqEr hst⟩
  | seqNormal _ _ ih₁ ih₂ =>
    intro t ht
    obtain ⟨m, hm, hmt⟩ := ih₂ t ht
    obtain ⟨s, hs, hsm⟩ := ih₁ m hm
    exact ⟨s, hs, .seqOk hsm hmt⟩
  | iterZero => intro t ht; exact ⟨t, ht, .starNil⟩
  | iterNonzero _ ih =>
    intro t ht
    obtain ⟨s, hs, hst⟩ := ih t ht
    refine ⟨s, hs, ?_⟩
    cases hst with
    | seqOk h₁ h₂ => exact exec_star_snoc h₁ h₂
    | seqEr h₁ => exact h₁
  | backwardsVariant p _ ih => exact il_backwardsVariant_sound p ih
  | choiceL _ ih =>
    intro t ht
    obtain ⟨s, hs, hst⟩ := ih t ht
    exact ⟨s, hs, .choiceL hst⟩
  | choiceR _ ih =>
    intro t ht
    obtain ⟨s, hs, hst⟩ := ih t ht
    exact ⟨s, hs, .choiceR hst⟩
  | errorEr => intro t ht; exact ⟨t, ht, .error⟩
  | assumeOk => rintro t ⟨ht, hb⟩; exact ⟨t, ht, .assume hb⟩
  | assign => rintro t ⟨s, hs, rfl⟩; exact ⟨s, hs, .assign⟩

/-- The derivation premise is needed: `[True] skip [er : True]` is neither derivable nor
valid. -/
theorem ilDeriv_sound_deriv_tight :
    ¬ ILDeriv (fun _ : Nat => True) Cmd.skip .er (fun _ => True) ∧
      ¬ IL (fun _ : Nat => True) Cmd.skip .er (fun _ => True) :=
  ⟨fun h => il_er_nonempty_post_true_positive_il_tight.1 (ilDeriv_sound h),
    il_er_nonempty_post_true_positive_il_tight.1⟩

/-- Non-vacuity of `il_backwardsVariant_sound`: its premise holds for `c = x := x + 1` and
`p n = (x = n)`, and so does its conclusion `[x = 0] (x := x + 1)⋆ [ok : ∃ n, x = n]`. -/
theorem nonvacuity_backwardsVariant :
    (∀ n : Nat, IL (fun m => m = n) (.assign Nat.succ) .ok (fun m => m = n + 1)) ∧
      IL (fun m : Nat => m = 0) (.star (.assign Nat.succ)) .ok (fun s => ∃ n, s = n) := by
  refine ⟨fun n t ht => ⟨n, rfl, by simp [ht]⟩, ?_⟩
  exact il_backwardsVariant_sound (fun n m => m = n) (fun n t ht => ⟨n, rfl, by simp [ht]⟩)

/-- The premise of the backwards-variant rule is needed (all of it, not just its first
instance): for `c = assume (x = 0); x := x + 1` and `p = (x = 0), (x = 1), (x = 2), …`, the
premise holds at `n = 0` but fails at `n = 1`, and the conclusion fails because `x = 2` is
not reachable. -/
theorem il_backwardsVariant_sound_premise_tight :
    let c : Cmd Nat := .seq (.assume (fun n => n == 0)) (.assign Nat.succ)
    let p : Nat → Assn Nat := fun
      | 0 => fun n => n = 0
      | 1 => fun n => n = 1
      | _ => fun n => n = 2
    IL (p 0) c .ok (p 1) ∧
      ¬ (∀ n, IL (p n) c .ok (p (n + 1))) ∧
      ¬ IL (p 0) (.star c) .ok (fun s => ∃ n, p n s) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t rfl
    exact ⟨0, rfl, .seqOk (.assume rfl) .assign⟩
  · intro h
    obtain ⟨s, hs, hst⟩ := h 1 2 rfl
    simp at hs hst
    omega
  · intro h
    obtain ⟨s, hs, hst⟩ := h 2 ⟨2, rfl⟩
    have hle : ∀ a b, Exec (.star (.seq (.assume (fun n : Nat => n == 0)) (.assign Nat.succ)))
        a .ok b → a = 0 → b ≤ 1 := by
      intro a b hex
      generalize hc : Cmd.star (.seq (.assume (fun n : Nat => n == 0)) (.assign Nat.succ)) = cs
        at hex
      generalize he : Exit.ok = eo at hex
      induction hex with
      | starNil => intro ha; omega
      | starOk h₁ h₂ _ _ =>
        cases hc
        intro ha
        simp only [exec_seq_iff, exec_assume_iff, exec_assign_iff] at h₁
        rcases h₁ with ⟨m, ⟨_, rfl, _⟩, _, rfl⟩ | ⟨hbad, _⟩
        · cases h₂ with
          | starNil => omega
          | starOk h₃ _ =>
            simp only [exec_seq_iff, exec_assume_iff, exec_assign_iff] at h₃
            rcases h₃ with ⟨m', ⟨_, rfl, hb⟩, _, _⟩ | ⟨hbad, _⟩
            · simp [ha] at hb
            · cases hbad
          | starEr _ => cases he
        · cases hbad
      | starEr _ => cases he
      | assign => cases hc
      | assume _ => cases hc
      | error => cases hc
      | seqOk _ _ _ _ => cases hc
      | seqEr _ _ => cases hc
      | choiceL _ _ => cases hc
      | choiceR _ _ => cases hc
    have := hle s 2 hst hs
    omega

/-- `iterZero` is derivable from `backwardsVariant`, `empty` and `conseq` (as O'Hearn notes);
it is kept as a constructor to mirror the rule list of his Fig. 2. -/
theorem iterZero_derivable {P : Assn σ} {c : Cmd σ} : ILDeriv P (.star c) .ok P := by
  let p : Nat → Assn σ := fun
    | 0 => P
    | _ + 1 => fun _ => False
  have hstep : ∀ n, ILDeriv (p n) c .ok (p (n + 1)) := fun _ => .empty
  exact .conseq (fun _ h => h) (.backwardsVariant p hstep) (fun s hs => ⟨0, hs⟩)

/-- A derivation that uses the backwards-variant rule: `[x = 0] (x := x + 1)⋆ [ok : True]`. -/
theorem ilDeriv_count_up :
    ILDeriv (fun n : Nat => n = 0) (.star (.assign Nat.succ)) .ok (fun _ => True) := by
  have hstep : ∀ n : Nat, ILDeriv (fun m => m = n) (.assign Nat.succ) .ok (fun m => m = n + 1) :=
    fun n => .conseq (fun _ h => h) .assign (fun t ht => ⟨n, rfl, ht⟩)
  have hv := ILDeriv.backwardsVariant (fun n : Nat => fun m => m = n) hstep
  exact .conseq (fun _ h => h) hv (fun t _ => ⟨t, rfl⟩)

/-- A derivation of a true-positive error triple through a loop:
`[x = 0] (x := x + 1)⋆; assume (x = 3); error() [er : x = 3]`. -/
theorem ilDeriv_count_up_error :
    ILDeriv (fun n : Nat => n = 0)
      (.seq (.star (.assign Nat.succ)) (.seq (.assume (fun n => n == 3)) .error)) .er
      (fun n => n = 3) := by
  refine .seqNormal ilDeriv_count_up (.seqNormal .assumeOk ?_)
  exact .conseq (fun t ht => ⟨trivial, by simp [ht]⟩) .errorEr (fun _ h => h)

/-- Non-vacuity of soundness: the derived loop triples are valid. -/
theorem nonvacuity_ilDeriv_sound :
    IL (fun n : Nat => n = 0) (.star (.assign Nat.succ)) .ok (fun _ => True) ∧
    IL (fun n : Nat => n = 0)
      (.seq (.star (.assign Nat.succ)) (.seq (.assume (fun n => n == 3)) .error)) .er
      (fun n => n = 3) :=
  ⟨ilDeriv_sound ilDeriv_count_up, ilDeriv_sound ilDeriv_count_up_error⟩

/-! ### Conjunction and disjunction -/

/-- Disjunction is sound for IL (semantically). -/
theorem il_disjunction_sound {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : IL P₁ c e Q₁) (h₂ : IL P₂ c e Q₂) :
    IL (fun s => P₁ s ∨ P₂ s) c e (fun s => Q₁ s ∨ Q₂ s) := by
  rintro t (ht | ht)
  · obtain ⟨s, hs, hst⟩ := h₁ t ht; exact ⟨s, Or.inl hs, hst⟩
  · obtain ⟨s, hs, hst⟩ := h₂ t ht; exact ⟨s, Or.inr hs, hst⟩

/-- Disjunction is sound for Hoare triples. -/
theorem hoare_disjunction_sound {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : Hoare P₁ c e Q₁) (h₂ : Hoare P₂ c e Q₂) :
    Hoare (fun s => P₁ s ∨ P₂ s) c e (fun s => Q₁ s ∨ Q₂ s) := by
  rintro t ⟨s, hs | hs, hst⟩
  · exact Or.inl (h₁ t ⟨s, hs, hst⟩)
  · exact Or.inr (h₂ t ⟨s, hs, hst⟩)

/-- Conjunction is sound for Hoare triples. -/
theorem hoare_conjunction_sound {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : Hoare P₁ c e Q₁) (h₂ : Hoare P₂ c e Q₂) :
    Hoare (fun s => P₁ s ∧ P₂ s) c e (fun s => Q₁ s ∧ Q₂ s) := by
  rintro t ⟨s, ⟨hs₁, hs₂⟩, hst⟩
  exact ⟨h₁ t ⟨s, hs₁, hst⟩, h₂ t ⟨s, hs₂, hst⟩⟩

/-- Non-vacuity for the conjunction/disjunction rules with distinct pres and posts. -/
theorem nonvacuity_conj_disj :
    let c : Cmd Nat := .assign Nat.succ
    (Hoare (fun n => n ≤ 1) c .ok (fun n => n ≤ 2) ∧ Hoare (fun n => 1 ≤ n) c .ok (fun n => 2 ≤ n)) ∧
    (IL (fun n => n = 0) c .ok (fun n => n = 1) ∧ IL (fun n => n = 4) c .ok (fun n => n = 5)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro t ⟨s, hs, h⟩; simp at h; omega
  · rintro t ⟨s, hs, h⟩; simp at h; omega
  · rintro t rfl; exact ⟨0, rfl, .assign⟩
  · rintro t rfl; exact ⟨4, rfl, .assign⟩

/-- Each premise of the Hoare conjunction and disjunction rules is needed: with the second
premise invalid (and the first valid) the conclusion fails. -/
theorem hoare_rules_premise_tight :
    (Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => True) ∧
      ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => True ∧ True) Cmd.skip .ok (fun _ => True ∧ False)) ∧
    (Hoare (fun _ : Nat => False) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => False ∨ True) Cmd.skip .ok (fun _ => False ∨ False)) := by
  have hbad : ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) :=
    fun h => h 0 ⟨0, trivial, by simp⟩
  refine ⟨⟨fun _ _ => trivial, hbad, ?_⟩, ⟨?_, hbad, ?_⟩⟩
  · intro h; exact (h 0 ⟨0, ⟨trivial, trivial⟩, by simp⟩).2
  · rintro t ⟨s, hs, _⟩; exact hs
  · intro h
    rcases h 0 ⟨0, Or.inr trivial, by simp⟩ with h | h <;> exact h

/-- Each premise of the IL disjunction rule is needed: with the second premise invalid (and
the first valid) the conclusion fails. -/
theorem il_disjunction_premise_tight :
    IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 0) ∧
      ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) ∧
      ¬ IL (fun n : Nat => n = 0 ∨ n = 0) Cmd.skip .ok (fun n => n = 0 ∨ n = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t rfl; exact ⟨0, rfl, by simp⟩
  · intro h; obtain ⟨s, hs, hst⟩ := h 1 rfl; simp at hst; omega
  · intro h; obtain ⟨s, hs, hst⟩ := h 1 (Or.inr rfl); simp at hst; omega

/-- O'Hearn's counterexample program for conjunction:
`(assume x = 1; x := 88) + (assume x = 2; x := 88)`. -/
def conjCounterProg : Cmd Nat :=
  .choice (.seq (.assume (fun n => n == 1)) (.assign (fun _ => 88)))
    (.seq (.assume (fun n => n == 2)) (.assign (fun _ => 88)))

/-- The conjunction rule is unsound for IL: `[x = 1] C [ok : x = 88]` and
`[x = 2] C [ok : x = 88]` hold, but `[x = 1 ∧ x = 2] C [ok : x = 88 ∧ x = 88]` does not. -/
theorem il_conjunction_counterexample :
    IL (fun n => n = 1) conjCounterProg .ok (fun n => n = 88) ∧
    IL (fun n => n = 2) conjCounterProg .ok (fun n => n = 88) ∧
    ¬ IL (fun n => n = 1 ∧ n = 2) conjCounterProg .ok (fun n => n = 88 ∧ n = 88) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t rfl; exact ⟨1, rfl, .choiceL (.seqOk (.assume rfl) .assign)⟩
  · rintro t rfl; exact ⟨2, rfl, .choiceR (.seqOk (.assume rfl) .assign)⟩
  · intro h
    obtain ⟨s, ⟨h₁, h₂⟩, _⟩ := h 88 ⟨rfl, rfl⟩
    omega

/-- The conjunction rule, stated over all IL triples, is refuted. -/
theorem il_conjunction_rule_unsound :
    ¬ ∀ (P₁ P₂ Q₁ Q₂ : Assn Nat) (c : Cmd Nat) (e : Exit),
      IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (fun s => P₁ s ∧ P₂ s) c e (fun s => Q₁ s ∧ Q₂ s) := by
  intro h
  obtain ⟨h₁, h₂, h₃⟩ := il_conjunction_counterexample
  exact h₃ (h _ _ _ _ _ _ h₁ h₂)

/-- Positive control: conjunction *is* sound for IL on commands whose `e`-relation is
backward-unique (each final state has at most one initial state). -/
theorem il_conjunction_sound_of_backward_unique {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (huniq : ∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂)
    (h₁ : IL P₁ c e Q₁) (h₂ : IL P₂ c e Q₂) :
    IL (fun s => P₁ s ∧ P₂ s) c e (fun s => Q₁ s ∧ Q₂ s) := by
  rintro t ⟨ht₁, ht₂⟩
  obtain ⟨s₁, hs₁, h₁t⟩ := h₁ t ht₁
  obtain ⟨s₂, hs₂, h₂t⟩ := h₂ t ht₂
  obtain rfl := huniq s₁ s₂ t h₁t h₂t
  exact ⟨s₁, ⟨hs₁, hs₂⟩, h₁t⟩

/-- Backward uniqueness is needed in the positive control: O'Hearn's program is not
backward-unique, and conjunction fails for it. -/
theorem il_conjunction_sound_of_backward_unique_tight :
    ¬ (∀ s₁ s₂ t, Exec conjCounterProg s₁ .ok t → Exec conjCounterProg s₂ .ok t → s₁ = s₂) ∧
    IL (fun n => n = 1) conjCounterProg .ok (fun n => n = 88) ∧
    IL (fun n => n = 2) conjCounterProg .ok (fun n => n = 88) ∧
    ¬ IL (fun n => n = 1 ∧ n = 2) conjCounterProg .ok (fun n => n = 88 ∧ n = 88) := by
  refine ⟨?_, il_conjunction_counterexample⟩
  intro h
  have := h 1 2 88 (.choiceL (.seqOk (.assume rfl) .assign))
    (.choiceR (.seqOk (.assume rfl) .assign))
  omega

/-- Non-vacuity of the positive control: `x := x + 1` is backward-unique. -/
theorem nonvacuity_il_conjunction_backward_unique :
    (∀ s₁ s₂ t, Exec (Cmd.assign Nat.succ) s₁ .ok t → Exec (Cmd.assign Nat.succ) s₂ .ok t →
        s₁ = s₂) ∧
    IL (fun n : Nat => n ≤ 3) (.assign Nat.succ) .ok (fun n => n = 2) ∧
    IL (fun n : Nat => 1 ≤ n) (.assign Nat.succ) .ok (fun n => n = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s₁ s₂ t h₁ h₂; simp at h₁ h₂; omega
  · rintro t rfl; exact ⟨1, by decide, .assign⟩
  · rintro t rfl; exact ⟨1, by decide, .assign⟩

/-- `skip` is backward-unique at every exit kind. -/
theorem skip_backward_unique (e : Exit) :
    ∀ s₁ s₂ t : Nat, Exec Cmd.skip s₁ e t → Exec Cmd.skip s₂ e t → s₁ = s₂ := by
  intro s₁ s₂ t h₁ h₂; simp at h₁ h₂; omega

/-- The first premise `h₁` of each of the four rules is needed: in each conjunct the other
hypotheses hold (including backward uniqueness of `skip` for the IL conjunction rule), `h₁`
fails, and the conclusion fails. Order: Hoare conjunction, Hoare disjunction, IL
disjunction, IL conjunction for backward-unique commands. -/
theorem conj_disj_rules_h1_tight :
    (¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) ∧
      Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => True) ∧
      ¬ Hoare (fun _ : Nat => True ∧ True) Cmd.skip .ok (fun _ => False ∧ True)) ∧
    (¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) ∧
      Hoare (fun _ : Nat => False) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => True ∨ False) Cmd.skip .ok (fun _ => False ∨ False)) ∧
    (¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) ∧
      IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 0) ∧
      ¬ IL (fun n : Nat => n = 0 ∨ n = 0) Cmd.skip .ok (fun n => n = 1 ∨ n = 0)) ∧
    ((∀ s₁ s₂ t : Nat, Exec Cmd.skip s₁ .ok t → Exec Cmd.skip s₂ .ok t → s₁ = s₂) ∧
      ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) ∧
      IL (fun _ : Nat => True) Cmd.skip .ok (fun _ => True) ∧
      ¬ IL (fun n : Nat => n = 0 ∧ True) Cmd.skip .ok (fun n => n = 1 ∧ True)) := by
  have hbad : ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) :=
    fun h => h 0 ⟨0, trivial, by simp⟩
  have ilbad : ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) := by
    intro h; obtain ⟨s, hs, hst⟩ := h 1 rfl; simp at hst; omega
  refine ⟨⟨hbad, fun _ _ => trivial, ?_⟩, ⟨hbad, ?_, ?_⟩, ⟨ilbad, ?_, ?_⟩,
    ⟨skip_backward_unique .ok, ilbad, ?_, ?_⟩⟩
  · intro h; exact (h 0 ⟨0, ⟨trivial, trivial⟩, by simp⟩).1
  · rintro t ⟨s, hs, _⟩; exact hs
  · intro h; rcases h 0 ⟨0, Or.inl trivial, by simp⟩ with h | h <;> exact h
  · rintro t rfl; exact ⟨0, rfl, by simp⟩
  · intro h; obtain ⟨s, hs, hst⟩ := h 1 (Or.inl rfl); simp at hst; omega
  · intro t _; exact ⟨t, trivial, by simp⟩
  · intro h; obtain ⟨s, ⟨hs, _⟩, hst⟩ := h 1 ⟨rfl, trivial⟩; simp at hst; omega

/-- The second premise `h₂` of each of the four rules is needed (same order as
`conj_disj_rules_h1_tight`). -/
theorem conj_disj_rules_h2_tight :
    (Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => True) ∧
      ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => True ∧ True) Cmd.skip .ok (fun _ => True ∧ False)) ∧
    (Hoare (fun _ : Nat => False) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => True) Cmd.skip .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => False ∨ True) Cmd.skip .ok (fun _ => False ∨ False)) ∧
    (IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 0) ∧
      ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) ∧
      ¬ IL (fun n : Nat => n = 0 ∨ n = 0) Cmd.skip .ok (fun n => n = 0 ∨ n = 1)) ∧
    ((∀ s₁ s₂ t : Nat, Exec Cmd.skip s₁ .ok t → Exec Cmd.skip s₂ .ok t → s₁ = s₂) ∧
      IL (fun _ : Nat => True) Cmd.skip .ok (fun _ => True) ∧
      ¬ IL (fun n : Nat => n = 0) Cmd.skip .ok (fun n => n = 1) ∧
      ¬ IL (fun n : Nat => True ∧ n = 0) Cmd.skip .ok (fun n => True ∧ n = 1)) := by
  obtain ⟨⟨_, _, _⟩, ⟨_, _, _⟩, ⟨ilbad, _, _⟩, ⟨_, _, iltrue, _⟩⟩ := conj_disj_rules_h1_tight
  refine ⟨hoare_rules_premise_tight.1, hoare_rules_premise_tight.2, il_disjunction_premise_tight,
    ⟨skip_backward_unique .ok, iltrue, ilbad, ?_⟩⟩
  intro h; obtain ⟨s, ⟨_, hs⟩, hst⟩ := h 1 ⟨trivial, rfl⟩; simp at hst; omega

/-- Exact characterization: for a fixed command `c` and exit kind `e`, the IL conjunction
rule holds for all assertions `P₁ P₂ Q₁ Q₂` iff the `e`-relation of `c` is backward-unique. -/
theorem il_conjunction_rule_iff_backward_unique (c : Cmd σ) (e : Exit) :
    (∀ P₁ P₂ Q₁ Q₂ : Assn σ, IL P₁ c e Q₁ → IL P₂ c e Q₂ →
        IL (fun s => P₁ s ∧ P₂ s) c e (fun t => Q₁ t ∧ Q₂ t)) ↔
      (∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂) := by
  constructor
  · intro hconj s₁ s₂ t h₁ h₂
    have hil₁ : IL (fun s => s = s₁) c e (fun x => x = t) := fun x hx => hx ▸ ⟨s₁, rfl, h₁⟩
    have hil₂ : IL (fun s => s = s₂) c e (fun x => x = t) := fun x hx => hx ▸ ⟨s₂, rfl, h₂⟩
    obtain ⟨s, ⟨rfl, rfl⟩, _⟩ := hconj _ _ _ _ hil₁ hil₂ t ⟨rfl, rfl⟩
    rfl
  · intro huniq _ _ _ _ h₁ h₂
    exact il_conjunction_sound_of_backward_unique huniq h₁ h₂

/-- Non-vacuity of the characterization: both sides hold for `x := x + 1` and both fail
for O'Hearn's program. -/
theorem nonvacuity_il_conjunction_rule_iff :
    (∀ s₁ s₂ t, Exec (Cmd.assign Nat.succ) s₁ .ok t → Exec (Cmd.assign Nat.succ) s₂ .ok t →
        s₁ = s₂) ∧
    ¬ (∀ s₁ s₂ t, Exec conjCounterProg s₁ .ok t → Exec conjCounterProg s₂ .ok t → s₁ = s₂) :=
  ⟨nonvacuity_il_conjunction_backward_unique.1, il_conjunction_sound_of_backward_unique_tight.1⟩

/-- The characterization is about the rule for *all* assertions at a fixed `(c, e)`: a
single instance of the conclusion can hold for a command that is not backward-unique (here
with empty posts). -/
theorem il_conjunction_instance_without_backward_unique :
    ¬ (∀ s₁ s₂ t, Exec conjCounterProg s₁ .ok t → Exec conjCounterProg s₂ .ok t → s₁ = s₂) ∧
    IL (fun n => n = 1) conjCounterProg .ok (fun _ => False) ∧
    IL (fun n => n = 2) conjCounterProg .ok (fun _ => False) ∧
    IL (fun n => n = 1 ∧ n = 2) conjCounterProg .ok (fun _ => False ∧ False) :=
  ⟨il_conjunction_sound_of_backward_unique_tight.1,
    il_empty_post _ _ _, il_empty_post _ _ _, fun _ h => h.1.elim⟩

/-- Over a fixed state type, the IL conjunction rule holds for all commands and assertions
iff the state type has at most one element. -/
theorem il_conjunction_rule_sound_iff_subsingleton (τ : Type) :
    (∀ (P₁ P₂ Q₁ Q₂ : Assn τ) (c : Cmd τ) (e : Exit),
        IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (fun s => P₁ s ∧ P₂ s) c e (fun t => Q₁ t ∧ Q₂ t)) ↔
      (∀ s₁ s₂ : τ, s₁ = s₂) := by
  constructor
  · intro h s₁ s₂
    have huniq := (il_conjunction_rule_iff_backward_unique
      (.assign (fun _ : τ => s₁)) .ok).1 (fun P₁ P₂ Q₁ Q₂ => h P₁ P₂ Q₁ Q₂ _ _)
    exact huniq s₁ s₂ s₁ .assign .assign
  · intro hsub P₁ P₂ Q₁ Q₂ c e h₁ h₂
    exact il_conjunction_sound_of_backward_unique (fun s₁ s₂ _ _ _ => hsub s₁ s₂) h₁ h₂

/-- Positive control: over the one-element state type the conjunction rule is sound. -/
theorem il_conjunction_rule_sound_on_unit :
    ∀ (P₁ P₂ Q₁ Q₂ : Assn Unit) (c : Cmd Unit) (e : Exit),
      IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (fun s => P₁ s ∧ P₂ s) c e (fun t => Q₁ t ∧ Q₂ t) :=
  (il_conjunction_rule_sound_iff_subsingleton Unit).2 (fun () () => rfl)

/-- Escape hatch: with the *same* pre, conjoining posts is always sound (by strengthening
the post). -/
theorem il_conjunction_same_pre_sound {P Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : IL P c e Q₁) (_h₂ : IL P c e Q₂) : IL (fun s => P s ∧ P s) c e (fun t => Q₁ t ∧ Q₂ t) :=
  fun t ht => let ⟨s, hs, hst⟩ := h₁ t ht.1; ⟨s, ⟨hs, hs⟩, hst⟩

/-- Escape hatch (constancy): conjoining an assertion `F` that `c` preserves *backwards* at
exit `e` (every `e`-run ending in `F` started in `F`) to both pre and post is sound, even
for commands that merge states. -/
theorem il_conjunction_backward_preserved_sound {P Q F : Assn σ} {c : Cmd σ} {e : Exit}
    (hF : ∀ s t, Exec c s e t → F t → F s) (h : IL P c e Q) :
    IL (fun s => P s ∧ F s) c e (fun t => Q t ∧ F t) :=
  fun t ⟨hq, hf⟩ => let ⟨s, hs, hst⟩ := h t hq; ⟨s, ⟨hs, hF s t hst hf⟩, hst⟩

/-! ### Completeness -/

/-- `iterPost c P n`: the states reachable from `P` by exactly `n` normal runs of `c`. -/
def iterPost (c : Cmd σ) (P : Assn σ) : Nat → Assn σ
  | 0 => P
  | n + 1 => post c .ok (iterPost c P n)

theorem iterPost_shift (c : Cmd σ) (P : Assn σ) (n : Nat) :
    iterPost c (post c .ok P) n = iterPost c P (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterPost] at ih ⊢; rw [ih]

theorem exists_iterPost_of_exec_star {c : Cmd σ} {s t : σ} (h : Exec (.star c) s .ok t) :
    ∀ P : Assn σ, P s → ∃ n, iterPost c P n t := by
  generalize hc : Cmd.star c = cs at h
  generalize he : Exit.ok = eo at h
  induction h with
  | starNil => intro P hs; exact ⟨0, hs⟩
  | starOk ha _ _ ih₂ =>
    cases hc
    intro P hs
    obtain ⟨n, hn⟩ := ih₂ rfl he (post c .ok P) ⟨_, hs, ha⟩
    exact ⟨n + 1, iterPost_shift c P n ▸ hn⟩
  | starEr _ => cases he
  | assign => cases hc
  | assume _ => cases hc
  | error => cases hc
  | seqOk _ _ _ _ => cases hc
  | seqEr _ _ => cases hc
  | choiceL _ _ => cases hc
  | choiceR _ _ => cases hc

/-- Every triple whose post is the post-image is derivable. -/
theorem ilDeriv_post (c : Cmd σ) : ∀ (P : Assn σ) (e : Exit), ILDeriv P c e (post c e P) := by
  induction c with
  | assign f =>
    intro P e
    cases e with
    | ok =>
      refine .conseq (fun _ h => h) .assign ?_
      rintro t ⟨s, hs, hst⟩; simp at hst; exact ⟨s, hs, hst⟩
    | er =>
      refine .conseq (fun _ h => h) .empty ?_
      rintro t ⟨s, _, hst⟩; simp at hst
  | assume b =>
    intro P e
    cases e with
    | ok =>
      refine .conseq (fun _ h => h) .assumeOk ?_
      rintro t ⟨s, hs, hst⟩; simp at hst; obtain ⟨rfl, hb⟩ := hst; exact ⟨hs, hb⟩
    | er =>
      refine .conseq (fun _ h => h) .empty ?_
      rintro t ⟨s, _, hst⟩; simp at hst
  | error =>
    intro P e
    cases e with
    | ok =>
      refine .conseq (fun _ h => h) .empty ?_
      rintro t ⟨s, _, hst⟩; simp at hst
    | er =>
      refine .conseq (fun _ h => h) .errorEr ?_
      rintro t ⟨s, hs, hst⟩; simp at hst; exact hst ▸ hs
  | seq c₁ c₂ ih₁ ih₂ =>
    intro P e
    cases e with
    | ok =>
      refine .conseq (fun _ h => h) (.seqNormal (ih₁ P .ok) (ih₂ _ .ok)) ?_
      rintro t ⟨s, hs, hst⟩
      simp only [exec_seq_iff] at hst
      rcases hst with ⟨m, h₁, h₂⟩ | ⟨h, _⟩
      · exact ⟨m, ⟨s, hs, h₁⟩, h₂⟩
      · cases h
    | er =>
      refine .conseq (fun _ h => h.elim id id)
        (.disj (.seqNormal (ih₁ P .ok) (ih₂ _ .er)) (.seqShort (ih₁ P .er))) ?_
      rintro t ⟨s, hs, hst⟩
      simp only [exec_seq_iff] at hst
      rcases hst with ⟨m, h₁, h₂⟩ | ⟨_, h⟩
      · exact Or.inl ⟨m, ⟨s, hs, h₁⟩, h₂⟩
      · exact Or.inr ⟨s, hs, h⟩
  | choice c₁ c₂ ih₁ ih₂ =>
    intro P e
    refine .conseq (fun _ h => h.elim id id) (.disj (.choiceL (ih₁ P e)) (.choiceR (ih₂ P e))) ?_
    rintro t ⟨s, hs, hst⟩
    simp only [exec_choice_iff] at hst
    rcases hst with h | h
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨s, hs, h⟩
  | star c ih =>
    have hok : ∀ P : Assn σ, ILDeriv P (.star c) .ok (post (.star c) .ok P) := by
      intro P
      have hv := ILDeriv.backwardsVariant (iterPost c P) (fun n => ih (iterPost c P n) .ok)
      refine .conseq (fun _ h => h) hv ?_
      rintro t ⟨s, hs, hst⟩
      exact exists_iterPost_of_exec_star hst P hs
    intro P e
    cases e with
    | ok => exact hok P
    | er =>
      refine .conseq (fun _ h => h) (.iterNonzero (.seqNormal (hok P) (ih _ .er))) ?_
      rintro t ⟨s, hs, hst⟩
      obtain ⟨m, h₁, h₂⟩ := exec_star_er_split hst
      exact ⟨m, ⟨s, hs, h₁⟩, h₂⟩

/-- Relative completeness of the IL proof system for this language (with semantic
assertions and semantic entailment as the consequence oracle): every valid IL triple is
derivable. -/
theorem ilDeriv_relatively_complete {P Q : Assn σ} {c : Cmd σ} {e : Exit} (h : IL P c e Q) :
    ILDeriv P c e Q :=
  .conseq (fun _ h => h) (ilDeriv_post c P e) h

/-- The validity premise of completeness is needed: an invalid triple is not derivable. -/
theorem ilDeriv_complete_valid_tight :
    ¬ IL (fun _ : Nat => True) Cmd.skip .er (fun _ => True) ∧
      ¬ ILDeriv (fun _ : Nat => True) Cmd.skip .er (fun _ => True) :=
  ⟨ilDeriv_sound_deriv_tight.2, ilDeriv_sound_deriv_tight.1⟩

/-- Non-vacuity of completeness: a valid loop-and-error triple. -/
theorem nonvacuity_ilDeriv_complete :
    IL (fun n : Nat => n = 0)
      (.seq (.star (.assign Nat.succ)) (.seq (.assume (fun n => n == 3)) .error)) .er
      (fun n => n = 3) :=
  nonvacuity_ilDeriv_sound.2

end Toy.IL
