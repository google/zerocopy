import ToyIL.Rules

/-!
# Analyses: over-approximate alarms, under-approximate silence

An *analysis* maps a command, an exit kind and a pre to a computed post. It is *sound
over-approximate* if every computed post is a Hoare post, and *sound under-approximate* if
every computed post is an IL post. An *alarm* is a nonempty computed error post.

* Under-approximate alarms are true positives; over-approximate silence is safety.
* Over-approximate alarms need not be real: a compositional analysis built from the
  interval hull on `Nat` (sound by `absPost_sound`, and silent on every program without
  `error`) raises a false alarm.
* Under-approximate silence need not be safety: bounded loop unrolling (sound
  under-approximate by `unrollAnalysis_soundUnder`, and exact on loop-free programs) misses
  an error that needs one more iteration.
-/

namespace Toy.IL

variable {σ : Type}

/-- An analysis: from a command, an exit kind and a pre, a computed post. -/
abbrev Analysis (σ : Type) := Cmd σ → Exit → Assn σ → Assn σ

/-- Sound over-approximate analysis: every computed post is a Hoare post. -/
def SoundOver (A : Analysis σ) : Prop := ∀ P c e, Hoare P c e (A c e P)

/-- Sound under-approximate analysis: every computed post is an IL post. -/
def SoundUnder (U : Analysis σ) : Prop := ∀ P c e, IL P c e (U c e P)

/-- The analysis reports a possible error for `P` and `c`: its computed error post is
nonempty. -/
def Alarm (A : Analysis σ) (P : Assn σ) (c : Cmd σ) : Prop := ∃ t, A c .er P t

/-- The exact analysis: the post-image itself (not computable in general). -/
def exactAnalysis : Analysis σ := fun c e P => post c e P

/-- The trivial over-approximate analysis: everything is possible. -/
def topAnalysis : Analysis σ := fun _ _ _ _ => True

/-- The trivial under-approximate analysis: nothing is reported. -/
def botAnalysis : Analysis σ := fun _ _ _ _ => False

theorem soundOver_exactAnalysis : SoundOver (exactAnalysis : Analysis σ) :=
  fun P c e => hoare_post_self P c e

theorem soundUnder_exactAnalysis : SoundUnder (exactAnalysis : Analysis σ) :=
  fun P c e => il_post_self P c e

theorem soundOver_topAnalysis : SoundOver (topAnalysis : Analysis σ) :=
  fun _ _ _ _ _ => trivial

theorem soundUnder_botAnalysis : SoundUnder (botAnalysis : Analysis σ) :=
  fun _ _ _ _ h => h.elim

/-- Negative example: reporting nothing is not over-approximate. -/
theorem not_soundOver_botAnalysis : ¬ SoundOver (botAnalysis : Analysis Nat) :=
  fun h => h (fun _ => True) .error .er 0 ⟨0, trivial, .error⟩

/-- Negative example: reporting everything is not under-approximate. -/
theorem not_soundUnder_topAnalysis : ¬ SoundUnder (topAnalysis : Analysis Nat) := by
  intro h
  obtain ⟨s, _, hs⟩ := h (fun _ => True) Cmd.skip .er 0 trivial
  simp at hs

theorem alarm_pos : Alarm (exactAnalysis : Analysis Nat) (fun _ => True) .error :=
  ⟨0, 0, trivial, .error⟩

theorem alarm_neg : ¬ Alarm (exactAnalysis : Analysis Nat) (fun _ => True) Cmd.skip := by
  rintro ⟨t, s, _, h⟩; simp at h

/-! ### What sound analyses license -/

/-- An alarm of a sound under-approximate analysis is a true positive. -/
theorem soundUnder_alarm_errReachable {U : Analysis σ} {P : Assn σ} {c : Cmd σ}
    (hU : SoundUnder U) (ha : Alarm U P c) : ErrReachable P c := by
  obtain ⟨s, t, hs, _, hst⟩ := il_er_nonempty_post_true_positive (hU P c .er) ha
  exact ⟨s, t, hs, hst⟩

/-- Silence of a sound over-approximate analysis is safety. -/
theorem soundOver_no_alarm_safe {A : Analysis σ} {P : Assn σ} {c : Cmd σ}
    (hA : SoundOver A) (hna : ¬ Alarm A P c) : Safe P c :=
  fun s t hs hst => hna ⟨t, hA P c .er t ⟨s, hs, hst⟩⟩

/-- Under-approximate soundness is needed for the first: the top analysis alarms on
`skip`, which is safe. -/
theorem soundUnder_alarm_errReachable_tight :
    ¬ SoundUnder (topAnalysis : Analysis Nat) ∧ Alarm (topAnalysis : Analysis Nat) (fun _ => True)
      Cmd.skip ∧ ¬ ErrReachable (fun _ : Nat => True) Cmd.skip := by
  refine ⟨not_soundUnder_topAnalysis, ⟨0, trivial⟩, ?_⟩
  rintro ⟨s, t, _, h⟩; simp at h

/-- Over-approximate soundness is needed for the second: the bottom analysis is silent
on `error()`, which is unsafe. -/
theorem soundOver_no_alarm_safe_tight :
    ¬ SoundOver (botAnalysis : Analysis Nat) ∧
      ¬ Alarm (botAnalysis : Analysis Nat) (fun _ => True) .error ∧
      ¬ Safe (fun _ : Nat => True) (.error : Cmd Nat) :=
  ⟨not_soundOver_botAnalysis, fun ⟨_, h⟩ => h, fun h => h 0 0 trivial .error⟩

/-- The alarm premise of the first is needed: the exact analysis is silent on `skip`, which
has no reachable error. -/
theorem soundUnder_alarm_errReachable_alarm_tight :
    SoundUnder (exactAnalysis : Analysis Nat) ∧
      ¬ Alarm (exactAnalysis : Analysis Nat) (fun _ => True) Cmd.skip ∧
      ¬ ErrReachable (fun _ : Nat => True) Cmd.skip := by
  refine ⟨soundUnder_exactAnalysis, alarm_neg, ?_⟩
  rintro ⟨s, t, _, h⟩; simp at h

/-- The silence premise of the second is needed: the exact analysis alarms on `error()`,
which is unsafe. -/
theorem soundOver_no_alarm_safe_alarm_tight :
    SoundOver (exactAnalysis : Analysis Nat) ∧
      Alarm (exactAnalysis : Analysis Nat) (fun _ => True) .error ∧
      ¬ Safe (fun _ : Nat => True) (.error : Cmd Nat) :=
  ⟨soundOver_exactAnalysis, alarm_pos, fun h => h 0 0 trivial .error⟩

/-- Non-vacuity: the exact analysis alarms on `error()` and is silent on `skip`. -/
theorem nonvacuity_analysis_licensing :
    (SoundUnder (exactAnalysis : Analysis Nat) ∧ Alarm (exactAnalysis : Analysis Nat)
        (fun _ => True) .error) ∧
    (SoundOver (exactAnalysis : Analysis Nat) ∧ ¬ Alarm (exactAnalysis : Analysis Nat)
        (fun _ => True) Cmd.skip) :=
  ⟨⟨soundUnder_exactAnalysis, alarm_pos⟩, ⟨soundOver_exactAnalysis, alarm_neg⟩⟩

/-- The exact analysis alarms exactly on reachable errors. -/
theorem exactAnalysis_alarm_iff_errReachable {P : Assn σ} {c : Cmd σ} :
    Alarm (exactAnalysis : Analysis σ) P c ↔ ErrReachable P c := by
  constructor
  · rintro ⟨t, s, hs, hst⟩; exact ⟨s, t, hs, hst⟩
  · rintro ⟨s, t, hs, hst⟩; exact ⟨t, s, hs, hst⟩

/-! ### A compositional over-approximate analysis from an extensive map -/

/-- `ρ` is extensive: `X ⊆ ρ X`. This is the only property of `ρ` that soundness of
`absPost ρ` uses; `ρ` need not be monotone or idempotent, so it need not be an upper closure
operator in the sense of abstract interpretation. -/
def Extensive (ρ : Assn σ → Assn σ) : Prop := ∀ X, Entails X (ρ X)

/-- The compositional abstract post induced by a map `ρ` on assertions:
* atomic commands (`assign`, `assume`, `error`): `ρ (post c e P)`;
* `c₁; c₂` at `ok`: `absPost c₂ ok (absPost c₁ ok P)` (no extra `ρ`);
* `c₁; c₂` at `er`: `ρ (absPost c₁ er P ∨ absPost c₂ er (absPost c₁ ok P))`;
* `c₁ + c₂` at `e`: `ρ (absPost c₁ e P ∨ absPost c₂ e P)`;
* `c⋆` at `ok`: `ρ Inv`, where `Inv` is the intersection of all assertions `X` with
  `P ⊆ X` and `absPost c ok X ⊆ X` (written impredicatively);
* `c⋆` at `er`: `ρ (absPost c er Inv)` (the body's error post is taken from `Inv` itself,
  not from `ρ Inv`).
When `ρ` is not monotone, `Inv` itself need not satisfy `absPost c ok Inv ⊆ Inv`
(`absPost_loop_set_not_closed_of_nonmonotone`). -/
def absPost (ρ : Assn σ → Assn σ) : Cmd σ → Exit → Assn σ → Assn σ
  | .assign f, e, P => ρ (post (.assign f) e P)
  | .assume b, e, P => ρ (post (.assume b) e P)
  | .error, e, P => ρ (post .error e P)
  | .seq c₁ c₂, .ok, P => absPost ρ c₂ .ok (absPost ρ c₁ .ok P)
  | .seq c₁ c₂, .er, P =>
      ρ (fun t => absPost ρ c₁ .er P t ∨ absPost ρ c₂ .er (absPost ρ c₁ .ok P) t)
  | .choice c₁ c₂, e, P => ρ (fun t => absPost ρ c₁ e P t ∨ absPost ρ c₂ e P t)
  | .star c, .ok, P =>
      ρ (fun t => ∀ X : Assn σ, Entails P X → Entails (absPost ρ c .ok X) X → X t)
  | .star c, .er, P =>
      ρ (absPost ρ c .er
        (fun t => ∀ X : Assn σ, Entails P X → Entails (absPost ρ c .ok X) X → X t))

/-- A normal run of `c⋆` stays inside any set closed under normal runs of `c`. -/
theorem star_ok_closed {c : Cmd σ} {X : Assn σ}
    (hX : ∀ s t, X s → Exec c s .ok t → X t) {s t : σ} (h : Exec (.star c) s .ok t)
    (hs : X s) : X t := by
  generalize hc : Cmd.star c = cs at h
  generalize he : Exit.ok = eo at h
  induction h with
  | starNil => exact hs
  | starOk ha _ _ ih₂ =>
    cases hc
    exact ih₂ (hX _ _ hs ha) rfl he
  | starEr _ => cases he
  | assign => cases hc
  | assume _ => cases hc
  | error => cases hc
  | seqOk _ _ _ _ => cases hc
  | seqEr _ _ => cases hc
  | choiceL _ _ => cases hc
  | choiceR _ _ => cases hc

theorem absPost_sound_aux {ρ : Assn σ → Assn σ} (hρ : Extensive ρ) (c : Cmd σ) :
    ∀ (P : Assn σ) (s : σ) (e : Exit) (t : σ), P s → Exec c s e t → absPost ρ c e P t := by
  induction c with
  | assign f => intro P s e t hs h; exact hρ _ t ⟨s, hs, h⟩
  | assume b => intro P s e t hs h; exact hρ _ t ⟨s, hs, h⟩
  | error => intro P s e t hs h; exact hρ _ t ⟨s, hs, h⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    intro P s e t hs h
    simp only [exec_seq_iff] at h
    cases e with
    | ok =>
      rcases h with ⟨m, h₁, h₂⟩ | ⟨h, _⟩
      · exact ih₂ _ m .ok t (ih₁ P s .ok m hs h₁) h₂
      · cases h
    | er =>
      apply hρ
      rcases h with ⟨m, h₁, h₂⟩ | ⟨_, h⟩
      · exact Or.inr (ih₂ _ m .er t (ih₁ P s .ok m hs h₁) h₂)
      · exact Or.inl (ih₁ P s .er t hs h)
  | choice c₁ c₂ ih₁ ih₂ =>
    intro P s e t hs h
    apply hρ
    simp only [exec_choice_iff] at h
    rcases h with h | h
    · exact Or.inl (ih₁ P s e t hs h)
    · exact Or.inr (ih₂ P s e t hs h)
  | star c ih =>
    intro P s e t hs h
    have hinv : ∀ m, Exec (.star c) s .ok m →
        ∀ X : Assn σ, Entails P X → Entails (absPost ρ c .ok X) X → X m := by
      intro m hm X hPX hX
      exact star_ok_closed (fun a b ha hab => hX b (ih X a .ok b ha hab)) hm (hPX s hs)
    cases e with
    | ok => exact hρ _ t (hinv t h)
    | er =>
      obtain ⟨m, h₁, h₂⟩ := exec_star_er_split h
      exact hρ _ t (ih _ m .er t (hinv m h₁) h₂)

/-- Soundness of the compositional analysis: for every extensive `ρ`, `absPost ρ`
is a sound over-approximate analysis. -/
theorem absPost_sound {ρ : Assn σ → Assn σ} (hρ : Extensive ρ) : SoundOver (absPost ρ) := by
  rintro P c e t ⟨s, hs, hst⟩
  exact absPost_sound_aux hρ c P s e t hs hst

/-- `skip` does not change the state, so its normal-exit post-image is the pre itself. -/
theorem post_skip_ok (X : Assn σ) : post (Cmd.skip : Cmd σ) .ok X = X := by
  funext t
  apply propext
  constructor
  · rintro ⟨a, ha, hex⟩; simp at hex; exact hex ▸ ha
  · intro ht; exact ⟨t, ht, by simp⟩

/-- Exact characterization: `absPost ρ` is a sound over-approximate analysis iff `ρ` is
extensive. (`→`: analyse `skip`, whose abstract post is `ρ X`.) -/
theorem soundOver_absPost_iff_extensive (ρ : Assn σ → Assn σ) :
    SoundOver (absPost ρ) ↔ Extensive ρ := by
  constructor
  · intro h X s hs
    have h1 := h X Cmd.skip .ok s ⟨s, hs, by simp⟩
    change ρ (post Cmd.skip .ok X) s at h1
    rw [post_skip_ok] at h1
    exact h1
  · exact absPost_sound

/-- An extensive map on assertions over `Nat` that is not monotone: it sends `{0}` to
everything and every other assertion to itself. -/
noncomputable def nonMonoRho (X : Assn Nat) : Assn Nat :=
  letI := Classical.propDecidable (X = fun n => n = 0)
  if X = fun n => n = 0 then fun _ => True else X

theorem nonMonoRho_extensive : Extensive nonMonoRho := by
  intro X s hs
  unfold nonMonoRho
  split
  · trivial
  · exact hs

theorem nonMonoRho_not_monotone :
    ¬ (∀ X Y : Assn Nat, Entails X Y → Entails (nonMonoRho X) (nonMonoRho Y)) := by
  intro hmono
  have hsub : Entails (fun n : Nat => n = 0) (fun n => n ≤ 1) := fun _ h => by omega
  have h0 : nonMonoRho (fun n => n = 0) 2 := by simp [nonMonoRho]
  have h2 : nonMonoRho (fun n => n ≤ 1) 2 := hmono _ _ hsub 2 h0
  have hne : (fun n : Nat => n ≤ 1) ≠ (fun n => n = 0) := by
    intro heq
    have h1 : (1 : Nat) = 0 := Eq.mp (congrFun heq 1) (Nat.le_refl 1)
    omega
  simp [nonMonoRho, hne] at h2

/-- For the non-monotone extensive map `nonMonoRho`, the loop set `Inv` used by
`absPost nonMonoRho (skip⋆) ok {0}` (the intersection of all `X ⊇ {0}` with
`absPost skip ok X ⊆ X`) is `{0}`, and it is not itself closed under the abstract body. -/
theorem absPost_loop_set_not_closed_of_nonmonotone :
    let P : Assn Nat := fun n => n = 0
    let L : Assn Nat := fun t =>
      ∀ X : Assn Nat, Entails P X → Entails (absPost nonMonoRho Cmd.skip .ok X) X → X t
    ¬ Entails (absPost nonMonoRho Cmd.skip .ok L) L := by
  dsimp only
  intro hclosed
  have hne : ∀ k : Nat, k ≠ 0 → (fun n : Nat => n = 0 ∨ n = k) ≠ (fun n => n = 0) := by
    intro k hk heq
    have : k = 0 := Eq.mp (congrFun heq k) (Or.inr rfl)
    exact hk this
  have hclosedX : ∀ k : Nat, k ≠ 0 →
      Entails (absPost nonMonoRho Cmd.skip .ok (fun n => n = 0 ∨ n = k))
        (fun n => n = 0 ∨ n = k) := by
    intro k hk s hs
    change nonMonoRho (post Cmd.skip .ok (fun n => n = 0 ∨ n = k)) s at hs
    rw [post_skip_ok] at hs
    simp [nonMonoRho, hne k hk] at hs
    exact hs
  have hL_eq : (fun t : Nat =>
      ∀ X : Assn Nat, Entails (fun n => n = 0) X →
        Entails (absPost nonMonoRho Cmd.skip .ok X) X → X t) = (fun n => n = 0) := by
    funext t
    apply propext
    constructor
    · intro ht
      have ht1 := ht (fun n => n = 0 ∨ n = 1) (fun _ h => Or.inl h) (hclosedX 1 (by decide))
      have ht2 := ht (fun n => n = 0 ∨ n = 2) (fun _ h => Or.inl h) (hclosedX 2 (by decide))
      omega
    · rintro rfl X hPX _
      exact hPX 0 rfl
  have h1 : absPost nonMonoRho Cmd.skip .ok (fun n => n = 0) 1 := by
    change nonMonoRho (post Cmd.skip .ok (fun n => n = 0)) 1
    rw [post_skip_ok]
    simp [nonMonoRho]
  have hcontra := hclosed 1 (by rw [hL_eq]; exact h1)
  rw [hL_eq] at hcontra
  omega

/-- The interval hull on `Nat`: the smallest interval (possibly unbounded above)
containing `X`. This is the abstraction of the interval domain. -/
def hull (X : Assn Nat) : Assn Nat := fun n => ∃ a b, X a ∧ X b ∧ a ≤ n ∧ n ≤ b

theorem hull_extensive : Extensive hull := fun _ n hn => ⟨n, n, hn, hn, Nat.le_refl n, Nat.le_refl n⟩

/-- Positive example: the hull of `{0, 2}` contains `1`. -/
theorem hull_pos : hull (fun n => n = 0 ∨ n = 2) 1 := ⟨0, 2, Or.inl rfl, Or.inr rfl, by decide, by decide⟩

/-- Negative example: the hull of `{0, 2}` does not contain `3`. -/
theorem hull_neg : ¬ hull (fun n => n = 0 ∨ n = 2) 3 := by
  rintro ⟨a, b, _, hb, _, h⟩; omega

/-- Extensiveness is needed: the constant-empty map is not extensive, and its analysis is
unsound. -/
theorem absPost_sound_extensive_tight :
    ¬ Extensive (fun _ : Assn Nat => fun _ => False) ∧
      ¬ SoundOver (absPost (fun _ : Assn Nat => fun _ => False)) := by
  refine ⟨fun h => h (fun _ => True) 0 trivial, ?_⟩
  intro h
  exact h (fun _ => True) .error .er 0 ⟨0, trivial, .error⟩

/-- Non-vacuity: the interval-hull analysis is sound. -/
theorem nonvacuity_absPost_sound : Extensive hull ∧ SoundOver (absPost hull) :=
  ⟨hull_extensive, absPost_sound hull_extensive⟩

/-- The interval-hull analysis. -/
def hullAnalysis : Analysis Nat := absPost hull

/-! ### Over-approximate alarms -/

/-- `c` contains no `error` command. -/
def Cmd.errorFree : Cmd σ → Bool
  | .assign _ => true
  | .assume _ => true
  | .error => false
  | .seq c₁ c₂ => c₁.errorFree && c₂.errorFree
  | .choice c₁ c₂ => c₁.errorFree && c₂.errorFree
  | .star c => c.errorFree

/-- A program without `error` never terminates erroneously. -/
theorem not_exec_er_of_errorFree {c : Cmd σ} {s t : σ} (h : Exec c s .er t) :
    c.errorFree = false := by
  generalize he : Exit.er = ee at h
  induction h with
  | assign => cases he
  | assume _ => cases he
  | error => rfl
  | seqOk _ _ _ ih₂ => simp [Cmd.errorFree, ih₂ he]
  | seqEr _ ih => simp [Cmd.errorFree, ih rfl]
  | choiceL _ ih => simp [Cmd.errorFree, ih he]
  | choiceR _ ih => simp [Cmd.errorFree, ih he]
  | starNil => cases he
  | starOk _ _ _ ih₂ => exact ih₂ he
  | starEr _ ih => simp [Cmd.errorFree, ih rfl]

/-- Non-degeneracy condition on an analysis: it never alarms on a program without
`error`. The trivial analysis `topAnalysis` violates it. -/
def SilentOnErrorFree (A : Analysis σ) : Prop :=
  ∀ P c, Cmd.errorFree c = true → ¬ Alarm A P c

theorem not_silentOnErrorFree_topAnalysis : ¬ SilentOnErrorFree (topAnalysis : Analysis Nat) :=
  fun h => h (fun _ => True) Cmd.skip rfl ⟨0, trivial⟩

theorem silentOnErrorFree_exactAnalysis : SilentOnErrorFree (exactAnalysis : Analysis σ) := by
  rintro P c hc ⟨t, s, _, h⟩
  rw [not_exec_er_of_errorFree h] at hc
  cases hc

/-- If `ρ` maps the empty assertion to the empty assertion, `absPost ρ` computes an empty
error post for every program without `error`. -/
theorem absPost_er_empty_of_errorFree {ρ : Assn σ → Assn σ} (hρ : ∀ t, ¬ ρ (fun _ => False) t) :
    ∀ (c : Cmd σ), c.errorFree = true → ∀ P t, ¬ absPost ρ c .er P t := by
  have hempty : ∀ X : Assn σ, (∀ t, ¬ X t) → ∀ t, ¬ ρ X t := by
    intro X hX
    have : X = fun _ => False := funext fun t => propext ⟨fun h => hX t h, False.elim⟩
    subst this; exact hρ
  have hatom : ∀ (c : Cmd σ), c.errorFree = true → ∀ P t, ¬ ρ (post c .er P) t := by
    intro c hc P
    apply hempty
    rintro t ⟨s, _, h⟩
    rw [not_exec_er_of_errorFree h] at hc
    cases hc
  intro c
  induction c with
  | assign f => intro hc P t h; exact hatom _ hc P t h
  | assume b => intro hc P t h; exact hatom _ hc P t h
  | error => intro hc; cases hc
  | seq c₁ c₂ ih₁ ih₂ =>
    intro hc P
    simp only [Cmd.errorFree, Bool.and_eq_true] at hc
    apply hempty
    rintro t (h | h)
    · exact ih₁ hc.1 _ t h
    · exact ih₂ hc.2 _ t h
  | choice c₁ c₂ ih₁ ih₂ =>
    intro hc P
    simp only [Cmd.errorFree, Bool.and_eq_true] at hc
    apply hempty
    rintro t (h | h)
    · exact ih₁ hc.1 _ t h
    · exact ih₂ hc.2 _ t h
  | star c ih =>
    intro hc P
    exact hempty _ (ih hc _)

theorem hull_empty : ∀ t, ¬ hull (fun _ => False) t := fun _ ⟨_, _, h, _⟩ => h

theorem silentOnErrorFree_hullAnalysis : SilentOnErrorFree hullAnalysis := by
  rintro P c hc ⟨t, ht⟩
  exact absPost_er_empty_of_errorFree hull_empty c hc P t ht

/-- The interval-hull analysis is also silent on `mkevenProg`, whose `error` is
unreachable. -/
theorem hullAnalysis_silent_on_mkevenProg : ¬ Alarm hullAnalysis (fun _ => True) mkevenProg := by
  rintro ⟨t, a, b, ha, _, _, _⟩
  rcases ha with ⟨a1, _, ⟨s, _, hex⟩, _, _, _⟩ | ⟨a2, _, ha2, _, _, _⟩
  · simp at hex
  · rcases ha2 with ⟨a3, _, ⟨s, _, hex⟩, _, _, _⟩ | ⟨a4, _, ⟨s, hs, hex⟩, _, _, _⟩
    · simp at hex
    · simp at hex
      rcases hs with ⟨c1, c2, ⟨m, hm, hm_ass⟩, ⟨m', hm', hm'_ass⟩, hc1, hc2⟩
      simp at hm_ass
      rcases hm with ⟨d1, d2, ⟨s1, _, hs1⟩, ⟨s2, _, hs2⟩, hd1, hd2⟩
      simp at hs1 hs2
      omega

/-- Positive control (pointwise): an alarm is a true positive whenever the computed error
post at `(P, c)` is contained in the true error post. -/
theorem alarm_errReachable_of_er_post_under {A : Analysis σ} {P : Assn σ} {c : Cmd σ}
    (h : Entails (A c .er P) (post c .er P)) (ha : Alarm A P c) : ErrReachable P c := by
  obtain ⟨t, ht⟩ := ha
  obtain ⟨s, hs, hst⟩ := h t ht
  exact ⟨s, t, hs, hst⟩

/-- `(x := 0 + x := 2); assume (x = 1); error()`: the error is unreachable, but the hull
of `{0, 2}` contains `1`. -/
def falseAlarmProg : Cmd Nat :=
  .seq (.choice (.assign (fun _ => 0)) (.assign (fun _ => 2)))
    (.seq (.assume (fun n => n == 1)) .error)

/-- A sound over-approximate analysis that raises a false alarm: the interval-hull
analysis is sound, never alarms on a program without `error`, alarms on `falseAlarmProg`,
and `falseAlarmProg` has no reachable error. -/
theorem hullAnalysis_false_alarm :
    SoundOver hullAnalysis ∧ SilentOnErrorFree hullAnalysis ∧
      Alarm hullAnalysis (fun _ => True) falseAlarmProg ∧
      ¬ ErrReachable (fun _ => True) falseAlarmProg := by
  refine ⟨absPost_sound hull_extensive, silentOnErrorFree_hullAnalysis, ⟨1, ?_⟩, ?_⟩
  · -- the abstract state after the choice is `hull {0, 2}`, which contains `1`
    have h0 : absPost hull (.assign (fun _ => 0)) .ok (fun _ => True) 0 :=
      hull_extensive _ 0 ⟨0, trivial, .assign⟩
    have h2 : absPost hull (.assign (fun _ => 2)) .ok (fun _ => True) 2 :=
      hull_extensive _ 2 ⟨0, trivial, .assign⟩
    have hmid : absPost hull (.choice (.assign (fun _ => 0)) (.assign (fun _ => 2))) .ok
        (fun _ => True) 1 :=
      ⟨0, 2, Or.inl h0, Or.inr h2, by decide, by decide⟩
    have hass : absPost hull (.assume (fun n => n == 1)) .ok
        (absPost hull (.choice (.assign (fun _ => 0)) (.assign (fun _ => 2))) .ok
          (fun _ => True)) 1 :=
      hull_extensive _ 1 ⟨1, hmid, .assume rfl⟩
    exact hull_extensive _ 1 (Or.inr (hull_extensive _ 1 (Or.inr
      (hull_extensive _ 1 ⟨1, hass, .error⟩))))
  · rintro ⟨s, t, _, h⟩
    simp [falseAlarmProg] at h

/-- Over-approximate alarms are not true positives in general, even for analyses that never
alarm on programs without `error`: soundness plus this non-degeneracy condition does not
make an alarm a reachable error. -/
theorem soundOver_silentOnErrorFree_alarm_not_imply_errReachable :
    ¬ ∀ (A : Analysis Nat), SoundOver A → SilentOnErrorFree A →
      ∀ P c, Alarm A P c → ErrReachable P c := by
  intro h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hullAnalysis_false_alarm
  exact h₄ (h _ h₁ h₂ _ _ h₃)

/-! ### A sound under-approximate analysis: bounded loop unrolling -/

/-- `upTo n c`: at most `n` iterations of `c`. -/
def Cmd.upTo : Nat → Cmd σ → Cmd σ
  | 0, _ => .skip
  | n + 1, c => .choice .skip (.seq c (Cmd.upTo n c))

/-- Replace every loop by at most `k` iterations of its (unrolled) body. -/
def Cmd.unroll (k : Nat) : Cmd σ → Cmd σ
  | .assign f => .assign f
  | .assume b => .assume b
  | .error => .error
  | .seq c₁ c₂ => .seq (c₁.unroll k) (c₂.unroll k)
  | .choice c₁ c₂ => .choice (c₁.unroll k) (c₂.unroll k)
  | .star c => Cmd.upTo k (c.unroll k)

/-- The bounded-unrolling analysis: the exact post of the `k`-unrolled program. -/
def unrollAnalysis (k : Nat) : Analysis σ := fun c e P => post (c.unroll k) e P

theorem exec_star_of_exec_upTo {c c' : Cmd σ} (hc : ∀ s e t, Exec c' s e t → Exec c s e t) :
    ∀ (n : Nat) (s : σ) (e : Exit) (t : σ), Exec (Cmd.upTo n c') s e t → Exec (.star c) s e t := by
  intro n
  induction n with
  | zero =>
    intro s e t h
    simp only [Cmd.upTo, exec_skip_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .starNil
  | succ n ih =>
    intro s e t h
    simp only [Cmd.upTo, exec_choice_iff, exec_skip_iff, exec_seq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨m, h₁, h₂⟩ | ⟨rfl, h₁⟩
    · exact .starNil
    · exact .starOk (hc _ _ _ h₁) (ih m e t h₂)
    · exact .starEr (hc _ _ _ h₁)

theorem exec_of_exec_unroll (k : Nat) (c : Cmd σ) :
    ∀ (s : σ) (e : Exit) (t : σ), Exec (c.unroll k) s e t → Exec c s e t := by
  induction c with
  | assign f => intro s e t h; exact h
  | assume b => intro s e t h; exact h
  | error => intro s e t h; exact h
  | seq c₁ c₂ ih₁ ih₂ =>
    intro s e t h
    simp only [Cmd.unroll, exec_seq_iff] at h ⊢
    rcases h with ⟨m, h₁, h₂⟩ | ⟨he, h₁⟩
    · exact Or.inl ⟨m, ih₁ _ _ _ h₁, ih₂ _ _ _ h₂⟩
    · exact Or.inr ⟨he, ih₁ _ _ _ h₁⟩
  | choice c₁ c₂ ih₁ ih₂ =>
    intro s e t h
    simp only [Cmd.unroll, exec_choice_iff] at h ⊢
    rcases h with h | h
    · exact Or.inl (ih₁ _ _ _ h)
    · exact Or.inr (ih₂ _ _ _ h)
  | star c ih =>
    intro s e t h
    exact exec_star_of_exec_upTo ih k s e t h

/-- Bounded unrolling is a sound under-approximate analysis, for every bound `k`. -/
theorem unrollAnalysis_soundUnder (k : Nat) : SoundUnder (unrollAnalysis k : Analysis σ) := by
  rintro P c e t ⟨s, hs, hst⟩
  exact ⟨s, hs, exec_of_exec_unroll k c s e t hst⟩

/-- `(x := x + 1)⋆; assume (x = 3); error()`: from `x = 0` the error needs three
iterations. -/
def countProg : Cmd Nat :=
  .seq (.star (.assign Nat.succ)) (.seq (.assume (fun n => n == 3)) .error)

/-- `c` contains no loop. -/
def Cmd.loopFree : Cmd σ → Bool
  | .assign _ => true
  | .assume _ => true
  | .error => true
  | .seq c₁ c₂ => c₁.loopFree && c₂.loopFree
  | .choice c₁ c₂ => c₁.loopFree && c₂.loopFree
  | .star _ => false

/-- Unrolling does not change a loop-free program. -/
theorem unroll_of_loopFree (k : Nat) {c : Cmd σ} (hc : c.loopFree = true) : c.unroll k = c := by
  induction c with
  | assign f => rfl
  | assume b => rfl
  | error => rfl
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.loopFree, Bool.and_eq_true] at hc
    simp only [Cmd.unroll, ih₁ hc.1, ih₂ hc.2]
  | choice c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.loopFree, Bool.and_eq_true] at hc
    simp only [Cmd.unroll, ih₁ hc.1, ih₂ hc.2]
  | star c _ => cases hc

/-- Non-degeneracy condition on an analysis: on loop-free programs it computes exactly the
post-image (at both exit kinds). The trivial analysis `botAnalysis` violates it. -/
def ExactOnLoopFree (U : Analysis σ) : Prop :=
  ∀ P c e t, Cmd.loopFree c = true → (U c e P t ↔ post c e P t)

theorem unrollAnalysis_exactOnLoopFree (k : Nat) :
    ExactOnLoopFree (unrollAnalysis k : Analysis σ) := by
  intro P c e t hc
  show post (c.unroll k) e P t ↔ post c e P t
  rw [unroll_of_loopFree k hc]

theorem not_exactOnLoopFree_botAnalysis : ¬ ExactOnLoopFree (botAnalysis : Analysis Nat) :=
  fun h => (h (fun _ => True) .error .er 0 rfl).2 ⟨0, trivial, .error⟩

/-- Positive control: on a loop-free program, silence of an analysis that is exact on
loop-free programs is safety. -/
theorem exactOnLoopFree_no_alarm_safe {U : Analysis σ} {P : Assn σ} {c : Cmd σ}
    (hU : ExactOnLoopFree U) (hc : c.loopFree = true) (hna : ¬ Alarm U P c) : Safe P c :=
  fun s t hs hst => hna ⟨t, (hU P c .er t hc).2 ⟨s, hs, hst⟩⟩

/-- A sound under-approximate analysis that misses a real error: unrolling loops at most
twice is sound under-approximate, exact on loop-free programs, and silent on `countProg`
from `x = 0`, yet `countProg` errs from `x = 0`. -/
theorem unrollAnalysis_two_false_negative :
    SoundUnder (unrollAnalysis 2 : Analysis Nat) ∧ ExactOnLoopFree (unrollAnalysis 2 : Analysis Nat) ∧
      ¬ Alarm (unrollAnalysis 2) (fun n => n = 0) countProg ∧
      ¬ Safe (fun n => n = 0) countProg := by
  refine ⟨unrollAnalysis_soundUnder 2, unrollAnalysis_exactOnLoopFree 2, ?_, ?_⟩
  · rintro ⟨t, s, rfl, h⟩
    simp [countProg, Cmd.unroll, Cmd.upTo] at h
  · intro h
    exact h 0 3 rfl (.seqOk exec_pos_star_three (.seqOk (.assume rfl) .error))

/-- The two-fold unrolling does find errors that need at most two iterations. -/
theorem unrollAnalysis_two_alarm_two_iterations :
    Alarm (unrollAnalysis 2 : Analysis Nat) (fun n => n = 0)
      (.seq (.star (.assign Nat.succ)) (.seq (.assume (fun n => n == 2)) .error)) := by
  refine ⟨2, 0, rfl, ?_⟩
  simp [Cmd.unroll, Cmd.upTo]

/-- Positive control for the bound: unrolling three times finds the error. -/
theorem unrollAnalysis_three_alarm : Alarm (unrollAnalysis 3) (fun n => n = 0) countProg := by
  refine ⟨3, 0, rfl, ?_⟩
  simp [countProg, Cmd.unroll, Cmd.upTo]

/-- Under-approximate silence is not safety in general, even for analyses that are exact
on every loop-free program: soundness plus this non-degeneracy condition does not make the
absence of an alarm imply safety. -/
theorem soundUnder_exactOnLoopFree_no_alarm_not_imply_safe :
    ¬ ∀ (U : Analysis Nat), SoundUnder U → ExactOnLoopFree U →
      ∀ P c, ¬ Alarm U P c → Safe P c := by
  intro h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := unrollAnalysis_two_false_negative
  exact h₄ (h _ h₁ h₂ _ _ h₃)

/-! ### Boundary: the refuted implications need at least one state -/

/-- Over the empty state type every implication refuted in this package (over `Nat`) holds
vacuously (and so do the versions with extra non-degeneracy hypotheses). -/
theorem refuted_implications_hold_on_empty_state_space :
    (∀ (P : Assn Empty) (c : Cmd Empty), IL P c .er (fun _ => False) → Safe P c) ∧
    (∀ (P Q : Assn Empty) (c : Cmd Empty), Hoare P c .er Q → (∃ t, Q t) → ErrReachable P c) ∧
    (∀ (P Q R : Assn Empty) (c₁ c₂ : Cmd Empty),
      Hoare P c₁ .ok Q → IL Q c₂ .er R → (∃ t, R t) → ErrReachable P (.seq c₁ c₂)) ∧
    (∀ (A : Analysis Empty), SoundOver A → ∀ P c, Alarm A P c → ErrReachable P c) ∧
    (∀ (U : Analysis Empty), SoundUnder U → ∀ P c, ¬ Alarm U P c → Safe P c) :=
  ⟨fun _ _ _ s => s.elim, fun _ _ _ _ ⟨t, _⟩ => t.elim, fun _ _ _ _ _ _ _ ⟨t, _⟩ => t.elim,
    fun _ _ _ _ ⟨t, _⟩ => t.elim, fun _ _ _ _ _ s => s.elim⟩

end Toy.IL
