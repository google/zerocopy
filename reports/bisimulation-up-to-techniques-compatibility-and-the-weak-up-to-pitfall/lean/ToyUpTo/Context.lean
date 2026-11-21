import ToyUpTo.Weak

/-!
# Up to `+`-contexts

Weak bisimilarity is not a congruence for choice (`τ.a.0 ≈ a.0` but
`τ.a.0 + b.0 ≉ a.0 + b.0`), and correspondingly "weak bisimulation up to
`+`-contexts" is unsound; one visible label already suffices, and over the
empty label type the technique is sound.  Strong bisimulation up to
`+`-contexts is compatible with `sb`; adding prefix contexts breaks this.
-/

namespace Toy.UpTo

open Proc

universe v

/-! ### Main result -/

/-- **Strong bisimulation up to `+`-contexts** (`SumClo`: hole, closed terms,
nested binary choice) is compatible with the strong functional of the toy
process language, over any label type. -/
theorem strong_upto_sum_context_compatible {L : Type v} :
    Compatible (sb (@PStep L)) SumClo := by
  refine ⟨?_, ?_⟩
  · intro R R' h p q hpq
    induction hpq with
    | base hr => exact SumClo.base (h _ _ hr)
    | refl p => exact SumClo.refl p
    | sum _ _ ih1 ih2 => exact SumClo.sum ih1 ih2
  · intro R p q hpq
    induction hpq with
    | base hr => exact sb_mono _ R _ (fun _ _ h => SumClo.base h) _ _ hr
    | refl _ =>
      exact ⟨fun l p' hs => ⟨p', hs, SumClo.refl _⟩, fun l q' hs => ⟨q', hs, SumClo.refl _⟩⟩
    | sum _ _ ih1 ih2 =>
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · rcases PStep.sum_inv hs with h | h
        · obtain ⟨q', h1, h2⟩ := ih1.1 l p' h; exact ⟨q', PStep.sumL h1, h2⟩
        · obtain ⟨q', h1, h2⟩ := ih2.1 l p' h; exact ⟨q', PStep.sumR h1, h2⟩
      · rcases PStep.sum_inv hs with h | h
        · obtain ⟨p', h1, h2⟩ := ih1.2 l q' h; exact ⟨p', PStep.sumL h1, h2⟩
        · obtain ⟨p', h1, h2⟩ := ih2.2 l q' h; exact ⟨p', PStep.sumR h1, h2⟩

/-- Strong bisimulation up to `+`-contexts is sound (corollary). -/
theorem strong_upto_sum_context_sound {L : Type v} : Sound (sb (@PStep L)) SumClo :=
  let h := @strong_upto_sum_context_compatible L
  sound_of_compatible_of_monotone_functional (sb_mono PStep) h.mono h.comm

/-! ### Weak bisimilarity is not a `+`-congruence (fully proved) -/

/-- `τ.a.0 + b.0 ≉ a.0 + b.0`. -/
theorem not_wbisim_tau_sum :
    ¬ wbisim (@PStep Lbl) (.sum (tau (act .a .nil)) (act .b .nil)) (.sum (act .a .nil) (act .b .nil)) := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨q', hq', hw'⟩ := (hW _ _ hw).1 none (act .a .nil) (PStep.sumL (PStep.pre _ _))
  have := WStep.none_of_noTau (PStep.sum_noTau (PStep.act_noTau _ _) (PStep.act_noTau _ _)) hq'
  subst this
  obtain ⟨p', hp', _⟩ := (hW _ _ hw').2 (some .b) .nil (PStep.sumR (PStep.pre _ _))
  obtain ⟨_, hs, _⟩ := WStep.some_of_noTau (PStep.act_noTau _ _) hp'
  cases (PStep.pre_inv hs).1

/-- **Weak bisimilarity is not preserved by `+`**: `τ.a.0 ≈ a.0`, but
`τ.a.0 + b.0 ≉ a.0 + b.0`. -/
theorem wbisim_not_sum_congruence :
    wbisim (@PStep Lbl) (tau (act .a .nil)) (act .a .nil) ∧
    ¬ wbisim (@PStep Lbl) (.sum (tau (act .a .nil)) (act .b .nil)) (.sum (act .a .nil) (act .b .nil)) :=
  ⟨wbisim_tau _, not_wbisim_tau_sum⟩

/-! ### Weak bisimulation up to `+`-contexts is unsound (fully proved) -/

/-- `{(a.(τ.a.0 + b.0), a.(a.0 + b.0)), (τ.a.0, a.0)}`. -/
def ctxRel : Rel (Proc Lbl) := fun p q =>
  (p = act .a (.sum (tau (act .a .nil)) (act .b .nil)) ∧
    q = act .a (.sum (act .a .nil) (act .b .nil))) ∨
  (p = tau (act .a .nil) ∧ q = act .a .nil)

/-- `a.(τ.a.0 + b.0) ≉ a.(a.0 + b.0)`. -/
theorem not_wbisim_ctx_pair :
    ¬ wbisim (@PStep Lbl) (act .a (.sum (tau (act .a .nil)) (act .b .nil)))
      (act .a (.sum (act .a .nil) (act .b .nil))) := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨q', hq', hw'⟩ := (hW _ _ hw).1 (some .a) _ (PStep.pre _ _)
  obtain ⟨p₂, hs, ht⟩ := WStep.some_of_noTau (PStep.act_noTau _ _) hq'
  obtain ⟨_, rfl⟩ := PStep.pre_inv hs
  have := TauStar.eq_of_noTau (PStep.sum_noTau (PStep.act_noTau _ _) (PStep.act_noTau _ _)) ht
  subst this
  exact not_wbisim_tau_sum ⟨W, hW, hw'⟩

/-- **Weak bisimulation up to `+`-contexts is unsound**: `ctxRel` progresses
to `SumClo ctxRel` under `wb` (the pair `(τ.a.0 + b.0, a.0 + b.0)` reached after the
initial `a` is obtained from `(τ.a.0, a.0) ∈ ctxRel` by the context `[·] + b.0`),
yet `a.(τ.a.0 + b.0) ≉ a.(a.0 + b.0)`. -/
theorem weak_upto_sum_context_unsound :
    ctxRel ⊑ wb PStep (SumClo ctxRel) ∧ ¬ ctxRel ⊑ wbisim PStep := by
  refine ⟨?_, fun h => not_wbisim_ctx_pair (h _ _ (Or.inl ⟨rfl, rfl⟩))⟩
  rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · have hmid : SumClo ctxRel (.sum (tau (act .a .nil)) (act .b .nil))
        (.sum (act .a .nil) (act .b .nil)) :=
      SumClo.sum (SumClo.base (Or.inr ⟨rfl, rfl⟩)) (SumClo.refl _)
    refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨_, WStep.single (PStep.pre _ _), hmid⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨_, WStep.single (PStep.pre _ _), hmid⟩
  · refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨_, WStep.refl_none _ _, SumClo.refl _⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨_, WStep.tau_cons (PStep.pre _ _) (WStep.single (PStep.pre _ _)), SumClo.refl _⟩

/-- Corollary in `Sound` form. -/
theorem weak_upto_sum_context_not_sound : ¬ Sound (wb (@PStep Lbl)) SumClo :=
  fun hs => weak_upto_sum_context_unsound.2 (hs _ weak_upto_sum_context_unsound.1)

/-- Positive control (witness level): `ctxRel` does not progress to
`SumClo ctxRel` under the *strong* functional (the pair `(τ.a.0, a.0)` fails). -/
theorem sum_context_control_strong : ¬ ctxRel ⊑ sb PStep (SumClo ctxRel) := by
  intro h
  obtain ⟨q', hs, _⟩ := (h _ _ (Or.inr ⟨rfl, rfl⟩)).1 none (act .a .nil) (PStep.pre _ _)
  exact PStep.act_noTau _ _ _ hs

/-! ### Definition examples for `Proc`, `PStep` and `SumClo` -/

/-- `PStep`, positive: `a.0 + 0 -a→ 0`. -/
theorem pstep_example_pos : PStep (.sum (act Lbl.a .nil) .nil) (some .a) .nil :=
  PStep.sumL (PStep.pre _ _)

/-- `PStep`, negative: `a.0` has no `b`-move. -/
theorem pstep_example_neg : ¬ PStep (act Lbl.a .nil) (some .b) .nil := by
  intro h
  cases (PStep.pre_inv h).1

/-- `SumClo`, positive: `(τ.a.0 + b.0, a.0 + b.0)` is in the `+`-context closure of
`ctxRel`. -/
theorem sumClo_example_pos :
    SumClo ctxRel (.sum (tau (act .a .nil)) (act .b .nil)) (.sum (act .a .nil) (act .b .nil)) :=
  SumClo.sum (SumClo.base (Or.inr ⟨rfl, rfl⟩)) (SumClo.refl _)

/-- `SumClo`, negative: prefix contexts are not included — `(a.τ.a.0, a.a.0)` is
not in the closure of `{(τ.a.0, a.0)}`. -/
theorem sumClo_example_neg :
    ¬ SumClo (fun p q => p = tau (act Lbl.a .nil) ∧ q = act .a .nil)
      (act .a (tau (act .a .nil))) (act .a (act .a .nil)) := by
  intro h
  cases h with
  | base h => cases h.1

/-! ### Usefulness witness (non-vacuity) for `strong_upto_sum_context_compatible` -/

/-- `{(a.((0+0) + b.0), a.(0 + b.0)), (0+0, 0)}`. -/
def relC : Rel (Proc Lbl) := fun p q =>
  (p = act .a (.sum (.sum .nil .nil) (act .b .nil)) ∧ q = act .a (.sum .nil (act .b .nil))) ∨
  (p = .sum .nil .nil ∧ q = .nil)

/-- `relC` is not a strong bisimulation but progresses to `SumClo relC`. -/
theorem strong_upto_sum_context_useful :
    relC ⊑ sb PStep (SumClo relC) ∧ ¬ relC ⊑ sb PStep relC := by
  refine ⟨?_, ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hmid : SumClo relC (.sum (.sum .nil .nil) (act .b .nil)) (.sum .nil (act .b .nil)) :=
        SumClo.sum (SumClo.base (Or.inr ⟨rfl, rfl⟩)) (SumClo.refl _)
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨_, PStep.pre _ _, hmid⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨_, PStep.pre _ _, hmid⟩
    · exact sb_of_dead (PStep.sum_dead PStep.nil_dead PStep.nil_dead) PStep.nil_dead
  · intro h
    obtain ⟨q', _, hr⟩ := (h _ _ (Or.inl ⟨rfl, rfl⟩)).1 (some .a) _ (PStep.pre _ _)
    rcases hr with ⟨hp, _⟩ | ⟨hp, _⟩ <;> cases hp

/-! ### A single visible label suffices for the weak failures

The counterexamples above use two labels `a` and `b`; the same failures occur
over any non-empty label type, with `τ.0 ≈ 0` and `τ.0 + a.0 ≉ 0 + a.0`.  Over
the empty label type every up-to function is sound for `wb`
(`sound_wb_of_no_visible`). -/

section OneLabel

variable {L : Type v}

/-- `τ.0 + a.0 ≉ 0 + a.0`, for any label `a`. -/
theorem not_wbisim_tau_nil_sum (a : L) :
    ¬ wbisim (@PStep L) (.sum (tau .nil) (act a .nil)) (.sum .nil (act a .nil)) := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨q', hq', hw'⟩ := (hW _ _ hw).1 none .nil (PStep.sumL (PStep.pre _ _))
  have := WStep.none_of_noTau (PStep.sum_noTau (PStep.nil_dead none) (PStep.act_noTau _ _)) hq'
  subst this
  obtain ⟨p', hp', _⟩ := (hW _ _ hw').2 (some a) .nil (PStep.sumR (PStep.pre _ _))
  exact WStep.not_some_of_dead PStep.nil_dead hp'

/-- Weak bisimilarity is not a `+`-congruence over any non-empty label type:
`τ.0 ≈ 0` but `τ.0 + a.0 ≉ 0 + a.0`. -/
theorem wbisim_not_sum_congruence_one_label (a : L) :
    wbisim (@PStep L) (tau .nil) .nil ∧
    ¬ wbisim (@PStep L) (.sum (tau .nil) (act a .nil)) (.sum .nil (act a .nil)) :=
  ⟨wbisim_tau _, not_wbisim_tau_nil_sum a⟩

/-- `{(a.(τ.0 + a.0), a.(0 + a.0)), (τ.0, 0)}`. -/
def ctxRel1 (a : L) : Rel (Proc L) := fun p q =>
  (p = act a (.sum (tau .nil) (act a .nil)) ∧ q = act a (.sum .nil (act a .nil))) ∨
  (p = tau .nil ∧ q = .nil)

/-- Weak bisimulation up to `+`-contexts is unsound over any non-empty label
type: `ctxRel1 a` progresses to `SumClo (ctxRel1 a)` under `wb`, yet
`a.(τ.0 + a.0) ≉ a.(0 + a.0)`. -/
theorem weak_upto_sum_context_unsound_one_label (a : L) :
    ctxRel1 a ⊑ wb PStep (SumClo (ctxRel1 a)) ∧ ¬ ctxRel1 a ⊑ wbisim PStep := by
  refine ⟨?_, fun h => ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hmid : SumClo (ctxRel1 a) (.sum (tau .nil) (act a .nil)) (.sum .nil (act a .nil)) :=
        SumClo.sum (SumClo.base (Or.inr ⟨rfl, rfl⟩)) (SumClo.refl _)
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨_, WStep.single (PStep.pre _ _), hmid⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨_, WStep.single (PStep.pre _ _), hmid⟩
    · refine ⟨fun l p' hs => ?_, fun l q' hs => absurd hs (PStep.nil_dead l q')⟩
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨_, WStep.refl_none _ _, SumClo.refl _⟩
  · obtain ⟨W, hW, hw⟩ := h _ _ (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨q', hq', hw'⟩ := (hW _ _ hw).1 (some a) _ (PStep.pre _ _)
    obtain ⟨p₂, hs, ht⟩ := WStep.some_of_noTau (PStep.act_noTau _ _) hq'
    obtain ⟨_, rfl⟩ := PStep.pre_inv hs
    have := TauStar.eq_of_noTau (PStep.sum_noTau (PStep.nil_dead none) (PStep.act_noTau _ _)) ht
    subst this
    exact not_wbisim_tau_nil_sum a ⟨W, hW, hw'⟩

/-- **Characterization.**  Over the toy process language with label type `L`,
weak bisimulation up to `+`-contexts is sound if and only if `L` is empty. -/
theorem weak_upto_sum_context_sound_iff_no_visible :
    Sound (wb (@PStep L)) SumClo ↔ (L → False) := by
  refine ⟨fun hs a => ?_, fun hL => sound_wb_of_no_visible hL _⟩
  exact (weak_upto_sum_context_unsound_one_label a).2
    (hs _ (weak_upto_sum_context_unsound_one_label a).1)

/-- Over the empty label type, weak bisimulation up to `+`-contexts is
sound. -/
theorem weak_upto_sum_context_sound_no_visible : Sound (wb (@PStep Empty)) SumClo :=
  sound_wb_of_no_visible (fun e => e.elim) _

/-- Over the empty label type, `+` preserves weak bisimilarity (all
processes are weakly bisimilar). -/
theorem wbisim_sum_congruence_no_visible (P P' Q : Proc Empty) (_ : wbisim PStep P P') :
    wbisim PStep (.sum P Q) (.sum P' Q) :=
  wbisim_total_of_no_visible (fun e => e.elim) _ _

/-- **Guarded choice preserves weak bisimilarity**: if `P ≈ P'` then
`μ.P + Q ≈ μ.P' + Q`, for every prefix `μ` (including `τ`). -/
theorem wbisim_guarded_sum_congruence (μ : Option L) {P P' : Proc L} (Q : Proc L)
    (h : wbisim PStep P P') : wbisim PStep (.sum (.pre μ P) Q) (.sum (.pre μ P') Q) := by
  let W : Rel (Proc L) := fun x y =>
    (x = .sum (.pre μ P) Q ∧ y = .sum (.pre μ P') Q) ∨ wbisim PStep x y
  refine ⟨W, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro x y (⟨rfl, rfl⟩ | hxy)
  · refine ⟨fun l x' hs => ?_, fun l y' hs => ?_⟩
    · rcases PStep.sum_inv hs with hs | hs
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨P', WStep.single (PStep.sumL (PStep.pre _ _)), Or.inr h⟩
      · exact ⟨x', WStep.single (PStep.sumR hs), Or.inr (wbisim_refl _ _)⟩
    · rcases PStep.sum_inv hs with hs | hs
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨P, WStep.single (PStep.sumL (PStep.pre _ _)), Or.inr h⟩
      · exact ⟨y', WStep.single (PStep.sumR hs), Or.inr (wbisim_refl _ _)⟩
  · exact wb_mono PStep _ W (fun _ _ h => Or.inr h) _ _ (gfp_postfixed (wb_mono PStep) _ _ hxy)

end OneLabel

/-! ### Prefix contexts and the role of closed terms in `SumClo` -/

/-- Closure under all contexts of the toy language: hole, closed terms,
prefix and binary choice. -/
inductive CtxClo {L : Type v} (R : Rel (Proc L)) : Rel (Proc L)
  | base {P Q : Proc L} : R P Q → CtxClo R P Q
  | refl (P : Proc L) : CtxClo R P P
  | pre (μ : Option L) {P Q : Proc L} : CtxClo R P Q → CtxClo R (.pre μ P) (.pre μ Q)
  | sum {P₁ Q₁ P₂ Q₂ : Proc L} :
      CtxClo R P₁ Q₁ → CtxClo R P₂ Q₂ → CtxClo R (.sum P₁ P₂) (.sum Q₁ Q₂)

theorem ctxClo_bot_eq {L : Type v} {P Q : Proc L} (h : CtxClo botRel P Q) : P = Q := by
  induction h with
  | base h => exact h.elim
  | refl => rfl
  | pre μ _ ih => rw [ih]
  | sum _ _ ih1 ih2 => rw [ih1, ih2]

/-- **Prefix contexts are not compatible with `sb`.**  The full context
closure is monotone, but does not commute with `sb`: `(0+0, 0) ∈ sb ∅`, so
`(a.(0+0), a.0)` is in the closure of `sb ∅`, while its `a`-derivative
`(0+0, 0)` is not in the closure of `∅` (which is the identity). -/
theorem prefix_context_not_compatible_sb :
    MonoRel (CtxClo (L := Lbl)) ∧ ¬ Commutes (sb (@PStep Lbl)) CtxClo ∧
    ¬ Compatible (sb (@PStep Lbl)) CtxClo := by
  have hmono : MonoRel (CtxClo (L := Lbl)) := by
    intro R R' h p q hpq
    induction hpq with
    | base hr => exact CtxClo.base (h _ _ hr)
    | refl p => exact CtxClo.refl p
    | pre μ _ ih => exact CtxClo.pre μ ih
    | sum _ _ ih1 ih2 => exact CtxClo.sum ih1 ih2
  have hnc : ¬ Commutes (sb (@PStep Lbl)) CtxClo := by
    intro h
    have hmem : CtxClo (sb PStep botRel) (act .a (.sum .nil .nil)) (act Lbl.a .nil) :=
      CtxClo.pre _ (CtxClo.base (sb_of_dead (PStep.sum_dead PStep.nil_dead PStep.nil_dead)
        PStep.nil_dead))
    obtain ⟨q', hs, hc⟩ := (h botRel _ _ hmem).1 (some .a) (.sum .nil .nil) (PStep.pre _ _)
    obtain ⟨_, rfl⟩ := PStep.pre_inv hs
    cases ctxClo_bot_eq hc
  exact ⟨hmono, hnc, fun h => hnc h.comm⟩

/-- `+`-context closure *without* closed terms: only the hole and binary
choice. -/
inductive SumCloNoRefl {L : Type v} (R : Rel (Proc L)) : Rel (Proc L)
  | base {P Q : Proc L} : R P Q → SumCloNoRefl R P Q
  | sum {P₁ Q₁ P₂ Q₂ : Proc L} :
      SumCloNoRefl R P₁ Q₁ → SumCloNoRefl R P₂ Q₂ → SumCloNoRefl R (.sum P₁ P₂) (.sum Q₁ Q₂)

/-- The closed-term constructor `SumClo.refl` is *not* needed for
compatibility: the closure without it is also compatible with `sb`. -/
theorem sumCloNoRefl_compatible_sb {L : Type v} : Compatible (sb (@PStep L)) SumCloNoRefl := by
  refine ⟨?_, ?_⟩
  · intro R R' h p q hpq
    induction hpq with
    | base hr => exact SumCloNoRefl.base (h _ _ hr)
    | sum _ _ ih1 ih2 => exact SumCloNoRefl.sum ih1 ih2
  · intro R p q hpq
    induction hpq with
    | base hr => exact sb_mono _ R _ (fun _ _ h => SumCloNoRefl.base h) _ _ hr
    | sum _ _ ih1 ih2 =>
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · rcases PStep.sum_inv hs with h | h
        · obtain ⟨q', h1, h2⟩ := ih1.1 l p' h; exact ⟨q', PStep.sumL h1, h2⟩
        · obtain ⟨q', h1, h2⟩ := ih2.1 l p' h; exact ⟨q', PStep.sumR h1, h2⟩
      · rcases PStep.sum_inv hs with h | h
        · obtain ⟨p', h1, h2⟩ := ih1.2 l q' h; exact ⟨p', PStep.sumL h1, h2⟩
        · obtain ⟨p', h1, h2⟩ := ih2.2 l q' h; exact ⟨p', PStep.sumR h1, h2⟩

/-- What closed terms add: without them, the context `[·] + b.0` used by the
counterexample `ctxRel` is not available. -/
theorem sumCloNoRefl_misses_closed_context :
    ¬ SumCloNoRefl ctxRel (.sum (tau (act .a .nil)) (act .b .nil))
      (.sum (act .a .nil) (act .b .nil)) := by
  intro h
  cases h with
  | base h => rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  | sum _ h2 =>
    cases h2 with
    | base h => rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h

end Toy.UpTo
