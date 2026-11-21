import ToyUpTo.Strong
import ToyUpTo.WeakFacts

/-!
# Weak bisimulation up to: the pitfall and its repairs

* `weak_upto_weak_bisim_unsound`: weak bisimulation up to weak bisimilarity
  (`≈ R ≈`) is unsound (concrete counterexample).
* `weak_upto_strong_bisim_compatible`: up to strong bisimilarity (`~ R ~`) is
  compatible with the weak functional.
* `weak_upto_expansion_sound`: up to expansion (`≳ R ≲`) is sound;
  `weak_upto_expansion_not_compatible`: but it is not compatible with `wb`.
* `weak_upto_expansion_asymmetric_sound`: the asymmetric technique — `≳ R ≈`
  for moves of the left state, `≈ R ≲` for moves of the right state — is sound.
* `weak_upto_expansion_left_weak_right_unsound`: using `≳ R ≈` for *both*
  clauses of the symmetric functional is unsound.
* Escape hatches: `R ∪ ≈`, reflexive and symmetric closure are compatible with
  `wb`; `≈ R ≈` is sound without silent steps, without visible labels, or with
  weak challenges (`WeakFacts`); `≳ R ≈` is sound for one-sided simulation.
-/

namespace Toy.UpTo

open Proc

universe u v

section General

variable {S : Type u} {L : Type v}

/-- A pair of states without transitions is in `wb T R` for every `R`. -/
theorem wb_of_dead {T : LTS S L} {R : Rel S} {p q : S}
    (hp : ∀ l p', ¬ T p l p') (hq : ∀ l q', ¬ T q l q') : wb T R p q :=
  ⟨fun l p' hs => absurd hs (hp l p'), fun l q' hs => absurd hs (hq l q')⟩

/-! ### Lifting lemmas for the asymmetric up-to-expansion technique

The invariant is `X ≳ X₁ R Y₁ ≈ Y` (for moves of the left state) and
`X ≈ X₁ R Y₁ ≲ Y` (for moves of the right state). -/

theorem asym_stepL {T : LTS S L} {R : Rel S}
    (hL : R ⊑ wsimL T (expWeakUpTo T R)) {X Y X'' : S} {α : Option L}
    (hI : expWeakUpTo T R X Y) (hs : T X α X'') :
    ∃ Y'', WStep T Y α Y'' ∧ expWeakUpTo T R X'' Y'' := by
  obtain ⟨X₁, Y₁, hx, hr, hy⟩ := hI
  obtain ⟨X₁'', hsh, hx''⟩ := (gfp_postfixed (ex_mono T) _ _ hx).1 α X'' hs
  rcases hsh with h1 | ⟨rfl, rfl⟩
  · obtain ⟨Y₁'', hw, ⟨X₂, Y₂, e2, r2, w2⟩⟩ := hL X₁ Y₁ hr α X₁'' h1
    obtain ⟨Y'', hw', hy''⟩ := wbisim_lift_wstep hw hy
    exact ⟨Y'', hw', X₂, Y₂, expands_trans hx'' e2, r2, wbisim_trans w2 hy''⟩
  · exact ⟨Y, WStep.refl_none _ _, _, Y₁, hx'', hr, hy⟩

theorem asym_tauStarL {T : LTS S L} {R : Rel S}
    (hL : R ⊑ wsimL T (expWeakUpTo T R)) {X X' Y : S}
    (ht : TauStar T X X') (hI : expWeakUpTo T R X Y) :
    ∃ Y', TauStar T Y Y' ∧ expWeakUpTo T R X' Y' := by
  induction ht generalizing Y with
  | refl => exact ⟨Y, TauStar.refl _, hI⟩
  | step hs _ ih =>
    obtain ⟨Ym, hm, hIm⟩ := asym_stepL hL hI hs
    obtain ⟨Y', h1, h2⟩ := ih hIm
    exact ⟨Y', TauStar.trans hm h1, h2⟩

theorem asym_wstepL {T : LTS S L} {R : Rel S}
    (hL : R ⊑ wsimL T (expWeakUpTo T R)) {X X' Y : S} {l : Option L}
    (hw : WStep T X l X') (hI : expWeakUpTo T R X Y) :
    ∃ Y', WStep T Y l Y' ∧ expWeakUpTo T R X' Y' := by
  cases l with
  | none => exact asym_tauStarL hL hw hI
  | some _ =>
    obtain ⟨X₁, X₂, h1, h2, h3⟩ := hw
    obtain ⟨Y₁, hy1, hI1⟩ := asym_tauStarL hL h1 hI
    obtain ⟨Y₂, hy2, hI2⟩ := asym_stepL hL hI1 h2
    obtain ⟨Y', hy3, hI3⟩ := asym_tauStarL hL h3 hI2
    exact ⟨Y', WStep.tauStar_left hy1 (WStep.tauStar_right hy2 hy3), hI3⟩

theorem asym_stepR {T : LTS S L} {R : Rel S}
    (hR : R ⊑ wsimR T (weakExpUpTo T R)) {X Y Y'' : S} {α : Option L}
    (hJ : weakExpUpTo T R X Y) (hs : T Y α Y'') :
    ∃ X'', WStep T X α X'' ∧ weakExpUpTo T R X'' Y'' := by
  obtain ⟨X₁, Y₁, hx, hr, hy⟩ := hJ
  obtain ⟨Y₁'', hsh, hy''⟩ := (gfp_postfixed (ex_mono T) _ _ hy).1 α Y'' hs
  rcases hsh with h1 | ⟨rfl, rfl⟩
  · obtain ⟨X₁'', hw, ⟨X₂, Y₂, w2, r2, e2⟩⟩ := hR X₁ Y₁ hr α Y₁'' h1
    obtain ⟨X'', hw', hx''⟩ := wbisim_lift_wstep hw (wbisim_symm hx)
    exact ⟨X'', hw', X₂, Y₂, wbisim_trans (wbisim_symm hx'') w2, r2, expands_trans hy'' e2⟩
  · exact ⟨X, WStep.refl_none _ _, X₁, _, hx, hr, hy''⟩

theorem asym_tauStarR {T : LTS S L} {R : Rel S}
    (hR : R ⊑ wsimR T (weakExpUpTo T R)) {X Y Y' : S}
    (ht : TauStar T Y Y') (hJ : weakExpUpTo T R X Y) :
    ∃ X', TauStar T X X' ∧ weakExpUpTo T R X' Y' := by
  induction ht generalizing X with
  | refl => exact ⟨X, TauStar.refl _, hJ⟩
  | step hs _ ih =>
    obtain ⟨Xm, hm, hJm⟩ := asym_stepR hR hJ hs
    obtain ⟨X', h1, h2⟩ := ih hJm
    exact ⟨X', TauStar.trans hm h1, h2⟩

theorem asym_wstepR {T : LTS S L} {R : Rel S}
    (hR : R ⊑ wsimR T (weakExpUpTo T R)) {X Y Y' : S} {l : Option L}
    (hw : WStep T Y l Y') (hJ : weakExpUpTo T R X Y) :
    ∃ X', WStep T X l X' ∧ weakExpUpTo T R X' Y' := by
  cases l with
  | none => exact asym_tauStarR hR hw hJ
  | some _ =>
    obtain ⟨Y₁, Y₂, h1, h2, h3⟩ := hw
    obtain ⟨X₁, hx1, hJ1⟩ := asym_tauStarR hR h1 hJ
    obtain ⟨X₂, hx2, hJ2⟩ := asym_stepR hR hJ1 h2
    obtain ⟨X', hx3, hJ3⟩ := asym_tauStarR hR h3 hJ2
    exact ⟨X', WStep.tauStar_left hx1 (WStep.tauStar_right hx2 hx3), hJ3⟩

/-! ### Main results -/

/-- **Weak bisimulation up to strong bisimilarity** (`~ R ~`) is compatible
with the weak bisimulation functional `wb`, for every transition system. -/
theorem weak_upto_strong_bisim_compatible (T : LTS S L) :
    Compatible (wb T) (strongUpTo T) := by
  refine ⟨fun R R' h p q ⟨p₁, q₁, h1, h2, h3⟩ => ⟨p₁, q₁, h1, h _ _ h2, h3⟩, ?_⟩
  intro R p q ⟨p₁, q₁, hp, hr, hq⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨p₁', hs1, hb1⟩ := (gfp_postfixed (sb_mono T) _ _ hp).1 l p' hs
    obtain ⟨q₁', hw2, hr2⟩ := hr.1 l p₁' hs1
    obtain ⟨q', hw3, hb3⟩ := bisim_lift_wstep hw2 hq
    exact ⟨q', hw3, p₁', q₁', hb1, hr2, hb3⟩
  · obtain ⟨q₁', hs1, hb1⟩ := (gfp_postfixed (sb_mono T) _ _ hq).2 l q' hs
    obtain ⟨p₁', hw2, hr2⟩ := hr.2 l q₁' hs1
    obtain ⟨p', hw3, hb3⟩ := bisim_lift_wstep hw2 (bisim_symm hp)
    exact ⟨p', hw3, p₁', q₁', bisim_symm hb3, hr2, hb1⟩

/-- `~ R ~` is sound for `wb` (corollary of compatibility). -/
theorem weak_upto_strong_bisim_sound (T : LTS S L) : Sound (wb T) (strongUpTo T) :=
  let h := weak_upto_strong_bisim_compatible T
  sound_of_compatible_of_monotone_functional (wb_mono T) h.mono h.comm

/-- **Weak bisimulation up to expansion, asymmetric form.**  If every move of
the left state of an `R`-pair is answered into `≳ R ≈` and every move of the
right state is answered into `≈ R ≲`, then `R ⊑ ≈`.  In both clauses the
expansion sits on the side of the *challenger's* derivative. -/
theorem weak_upto_expansion_asymmetric_sound (T : LTS S L) (R : Rel S)
    (hL : R ⊑ wsimL T (expWeakUpTo T R)) (hR : R ⊑ wsimR T (weakExpUpTo T R)) :
    R ⊑ wbisim T := by
  have post : weakUpTo T R ⊑ wb T (weakUpTo T R) := by
    intro p q ⟨p₁, q₁, hp, hr, hq⟩
    refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨p₁', hw1, hpp⟩ := (gfp_postfixed (wb_mono T) _ _ hp).1 l p' hs
      obtain ⟨q₁', hw2, ⟨X, Y, e, r, w⟩⟩ :=
        asym_wstepL hL hw1 ⟨p₁, q₁, expands_refl _ _, hr, wbisim_refl _ _⟩
      obtain ⟨q', hw3, hqq⟩ := wbisim_lift_wstep hw2 hq
      exact ⟨q', hw3, X, Y, wbisim_trans hpp (expands_incl_wbisim e), r, wbisim_trans w hqq⟩
    · obtain ⟨q₁', hw1, hqq⟩ := (gfp_postfixed (wb_mono T) _ _ hq).2 l q' hs
      obtain ⟨p₁', hw2, ⟨X, Y, w, r, e⟩⟩ :=
        asym_wstepR hR hw1 ⟨p₁, q₁, wbisim_refl _ _, hr, expands_refl _ _⟩
      obtain ⟨p', hw3, hpp⟩ := wbisim_lift_wstep hw2 (wbisim_symm hp)
      exact ⟨p', hw3, X, Y, wbisim_trans (wbisim_symm hpp) w, r,
        wbisim_trans (wbisim_symm (expands_incl_wbisim e)) hqq⟩
  exact fun p q h => incl_gfp_of_postfixed post p q ⟨p, q, wbisim_refl _ _, h, wbisim_refl _ _⟩

/-- **Weak bisimulation up to expansion** (`≳ R ≲`, symmetric form) is sound
for `wb`, for every transition system.  It follows from the asymmetric form
because `≳ ⊑ ≈` and `≈` is symmetric. -/
theorem weak_upto_expansion_sound (T : LTS S L) : Sound (wb T) (expUpTo T) := by
  intro R hR
  refine weak_upto_expansion_asymmetric_sound T R ?_ ?_
  · exact fun p q h => wsimL_mono T _ _
      (fun _ _ ⟨x₁, y₁, e1, r, e2⟩ => ⟨x₁, y₁, e1, r, wbisim_symm (expands_incl_wbisim e2)⟩)
      p q (hR p q h).1
  · exact fun p q h => wsimR_mono T _ _
      (fun _ _ ⟨x₁, y₁, e1, r, e2⟩ => ⟨x₁, y₁, expands_incl_wbisim e1, r, e2⟩)
      p q (hR p q h).2

/-! ### Further sound and compatible techniques for `wb` (escape hatches) -/

/-- **Up to union with weak bisimilarity** (`R ∪ ≈`) is compatible with `wb`
(instance of `compatible_union_gfp_of_monotone_functional`).  Contrast with
`≈ R ≈` (`weak_upto_weak_bisim_unsound`): adding `≈` as a union is fine, it is
composing `≈` with `R` on both sides that fails. -/
theorem weak_upto_union_wbisim_compatible (T : LTS S L) :
    Compatible (wb T) (unionWbisim T) :=
  compatible_union_gfp_of_monotone_functional (wb_mono T)

/-- `R ∪ ≈` is sound for `wb`. -/
theorem weak_upto_union_wbisim_sound (T : LTS S L) : Sound (wb T) (unionWbisim T) :=
  sound_union_gfp_of_monotone_functional (wb_mono T)

/-- Up to reflexivity (`R ∪ id`) is compatible with `wb`. -/
theorem reflClo_compatible_wb (T : LTS S L) : Compatible (wb T) reflClo := by
  refine ⟨fun _ _ h _ _ hpq => hpq.elim (fun hr => Or.inl (h _ _ hr)) Or.inr, ?_⟩
  intro R p q hpq
  rcases hpq with hr | rfl
  · exact wb_mono T R _ (fun _ _ h => Or.inl h) _ _ hr
  · exact ⟨fun l p' hs => ⟨p', WStep.single hs, Or.inr rfl⟩,
      fun l q' hs => ⟨q', WStep.single hs, Or.inr rfl⟩⟩

/-- Up to symmetry (`R ∪ R⁻¹`) is compatible with `wb`. -/
theorem symClo_compatible_wb (T : LTS S L) : Compatible (wb T) symClo := by
  refine ⟨fun _ _ h _ _ hpq =>
    hpq.elim (fun hr => Or.inl (h _ _ hr)) (fun hr => Or.inr (h _ _ hr)), ?_⟩
  intro R p q hpq
  rcases hpq with hr | hr
  · exact wb_mono T R _ (fun _ _ h => Or.inl h) _ _ hr
  · exact ⟨fun l p' hs => let ⟨q', h1, h2⟩ := hr.2 l p' hs; ⟨q', h1, Or.inr h2⟩,
           fun l q' hs => let ⟨p', h1, h2⟩ := hr.1 l q' hs; ⟨p', h1, Or.inr h2⟩⟩

/-- **One-sided escape hatch for `≳ R ≈`.**  For the one-sided weak
simulation functional `wsimL`, the up-to function `≳ R ≈` is sound: if every
move of the left state is answered into `≳ R ≈`, then `R` is contained in
weak similarity `gfp (wsimL T)`.  (Card
`weak-upto-expansion-left-weak-right-symmetric-unsound` shows it is unsound
when also used for moves of the right state of the symmetric functional.) -/
theorem weak_upto_expansion_left_weak_right_sound_for_wsimL (T : LTS S L) (R : Rel S)
    (hL : R ⊑ wsimL T (expWeakUpTo T R)) : R ⊑ gfp (wsimL T) := by
  have post : expWeakUpTo T R ⊑ wsimL T (expWeakUpTo T R) :=
    fun _ _ hI _ _ hs => asym_stepL hL hI hs
  exact fun p q h => incl_gfp_of_postfixed post p q ⟨p, q, expands_refl _ _, h, wbisim_refl _ _⟩

/-- **τ-free escape hatch for the pitfall.**  On a transition system without
silent steps, weak bisimulation up to weak bisimilarity is sound. -/
theorem weak_upto_weak_bisim_sound_of_noTau {T : LTS S L} (hT : NoTau T) :
    Sound (wb T) (weakUpTo T) := by
  intro R hR
  have h1 : R ⊑ sb T (strongUpTo T R) := fun p q h =>
    sb_mono T _ _ (fun _ _ ⟨p₁, q₁, hp, hr, hq⟩ =>
      ⟨p₁, q₁, wbisim_incl_bisim_of_noTau hT _ _ hp, hr, wbisim_incl_bisim_of_noTau hT _ _ hq⟩)
      p q (wb_incl_sb_of_noTau hT _ p q (hR p q h))
  exact Incl.trans (strong_upto_bisim_both_sides_sound T R h1) (bisim_incl_wbisim T)

/-- **τ-free escape hatch for non-compatibility of up to expansion.**  On a
transition system without silent steps, `≳ R ≲` commutes with `wb`. -/
theorem expUpTo_commutes_of_noTau {T : LTS S L} (hT : NoTau T) :
    Commutes (wb T) (expUpTo T) := by
  intro R p q ⟨p₁, q₁, hp, hw, hq⟩
  have hs : strongUpTo T (sb T R) p q :=
    ⟨p₁, q₁, expands_incl_bisim_of_noTau hT _ _ hp, wb_incl_sb_of_noTau hT R _ _ hw,
      bisim_symm (expands_incl_bisim_of_noTau hT _ _ hq)⟩
  have h2 := sb_incl_wb T _ p q ((strong_upto_bisim_both_sides_compatible T).comm R p q hs)
  exact wb_mono T _ _ (fun _ _ ⟨x, y, hx, hr, hy⟩ =>
    ⟨x, y, bisim_incl_expands T _ _ hx, hr, bisim_incl_expands T _ _ (bisim_symm hy)⟩) p q h2

/-- Up to expansion is monotone. -/
theorem expUpTo_mono (T : LTS S L) : MonoRel (expUpTo T) :=
  fun _ _ h _ _ ⟨p₁, q₁, hp, hr, hq⟩ => ⟨p₁, q₁, hp, h _ _ hr, hq⟩

/-- Up to expansion with the symbols reversed, `≲ R ≳`: `p₁ ≳ p`, `p₁ R q₁`
and `q₁ ≳ q` (the faster processes on the outside). -/
def revExpUpTo (T : LTS S L) (R : Rel S) : Rel S :=
  fun p q => ∃ p₁ q₁, expands T p₁ p ∧ R p₁ q₁ ∧ expands T q₁ q

end General

/-! ### Concrete weak facts -/

section Concrete

/-- `τ.P ≈ P`. -/
theorem wbisim_tau {L : Type v} (P : Proc L) : wbisim PStep (tau P) P := by
  refine ⟨_, postfixed_union_id (wb_mono _) (idRel_wb _)
    (R := fun p q => p = tau P ∧ q = P) ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨_, WStep.refl_none _ _, Or.inr rfl⟩
  · exact ⟨q', WStep.tau_cons (PStep.pre _ _) (WStep.single hs), Or.inr rfl⟩

/-- `τ.P ≳ P`: `τ.P` expands `P`. -/
theorem expands_tau {L : Type v} (P : Proc L) : expands PStep (tau P) P := by
  refine ⟨_, postfixed_union_id (ex_mono _) (idRel_ex _)
    (R := fun p q => p = tau P ∧ q = P) ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨_, Or.inr ⟨rfl, rfl⟩, Or.inr rfl⟩
  · refine ⟨q', ?_, Or.inr rfl⟩
    cases l with
    | none => exact ⟨_, PStep.pre _ _, TauStar.step hs (TauStar.refl _)⟩
    | some a => exact WStep.tau_cons (PStep.pre _ _) (WStep.single hs)

/-- `τ.a.0 ≉ 0`. -/
theorem not_wbisim_tau_act_nil : ¬ wbisim (@PStep Lbl) (tau (act .a .nil)) .nil := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨q', hq', hw'⟩ := (hW _ _ hw).1 none (act .a .nil) (PStep.pre _ _)
  have := WStep.none_of_noTau (PStep.nil_dead none) hq'
  subst this
  obtain ⟨q'', hq'', _⟩ := (hW _ _ hw').1 (some .a) .nil (PStep.pre _ _)
  exact WStep.not_some_of_dead PStep.nil_dead hq''

/-- `a.0 ⋧ τ.a.0`: `a.0` does not expand `τ.a.0`. -/
theorem not_expands_act_tau : ¬ expands (@PStep Lbl) (act .a .nil) (tau (act .a .nil)) := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨q', hq', _⟩ := (hW _ _ hw).1 (some .a) .nil (PStep.pre _ _)
  rcases hq' with hs | ⟨hl, _⟩
  · cases (PStep.pre_inv hs).1
  · cases hl

/-! ### Definition examples -/

/-- `TauStar`, positive: `τ.0 =τ*⇒ 0`. -/
theorem tauStar_example_pos : TauStar (@PStep Lbl) (tau .nil) .nil :=
  TauStar.step (PStep.pre _ _) (TauStar.refl _)

/-- `TauStar`, negative: `0` cannot reach `τ.0`. -/
theorem tauStar_example_neg : ¬ TauStar (@PStep Lbl) .nil (tau .nil) := by
  intro h
  cases TauStar.eq_of_noTau (PStep.nil_dead none) h

/-- `WStep`, positive: `τ.a.0 =â⇒ 0`. -/
theorem wstep_example_pos : WStep (@PStep Lbl) (tau (act .a .nil)) (some .a) .nil :=
  WStep.tau_cons (PStep.pre _ _) (WStep.single (PStep.pre _ _))

/-- `WStep`, negative: `a.0` has no weak `b`-transition. -/
theorem wstep_example_neg : ¬ WStep (@PStep Lbl) (act .a .nil) (some .b) .nil := by
  intro h
  obtain ⟨_, hs, _⟩ := WStep.some_of_noTau (PStep.act_noTau _ _) h
  cases (PStep.pre_inv hs).1

/-- `StepHat`, positive: for τ, standing still counts. -/
theorem stepHat_example_pos : StepHat (@PStep Lbl) .nil none .nil := Or.inr ⟨rfl, rfl⟩

/-- `StepHat`, negative: for a visible label, standing still does not count. -/
theorem stepHat_example_neg : ¬ StepHat (@PStep Lbl) .nil (some .a) .nil := by
  rintro (h | ⟨h, _⟩)
  · exact PStep.nil_dead _ _ h
  · cases h

/-- `WStepPlus`, positive: `τ.0 =τ⁺⇒ 0`. -/
theorem wstepPlus_example_pos : WStepPlus (@PStep Lbl) (tau .nil) none .nil :=
  ⟨.nil, PStep.pre _ _, TauStar.refl _⟩

/-- `WStepPlus`, negative: `τ⁺` needs at least one step, unlike `WStep` for
τ (`WStep.refl_none`). -/
theorem wstepPlus_example_neg : ¬ WStepPlus (@PStep Lbl) .nil none .nil :=
  fun ⟨_, h, _⟩ => PStep.nil_dead _ _ h

/-- `wsimL`, positive: a dead left state is vacuously simulated. -/
theorem wsimL_example_pos : wsimL (@PStep Lbl) botRel .nil (act .a .nil) :=
  fun l p' hs => absurd hs (PStep.nil_dead l p')

/-- `wsimL`, negative: `a.0`'s move cannot be answered by `0`. -/
theorem wsimL_example_neg : ¬ wsimL (@PStep Lbl) topRel (act .a .nil) .nil := by
  intro h
  obtain ⟨_, hq, _⟩ := h (some .a) .nil (PStep.pre _ _)
  exact WStep.not_some_of_dead PStep.nil_dead hq

/-- `wsimR`, positive: a dead right state is vacuously simulated. -/
theorem wsimR_example_pos : wsimR (@PStep Lbl) botRel (act .a .nil) .nil :=
  fun l q' hs => absurd hs (PStep.nil_dead l q')

/-- `wsimR`, negative: `a.0`'s move (on the right) cannot be answered by
`0`. -/
theorem wsimR_example_neg : ¬ wsimR (@PStep Lbl) topRel .nil (act .a .nil) := by
  intro h
  obtain ⟨_, hp, _⟩ := h (some .a) .nil (PStep.pre _ _)
  exact WStep.not_some_of_dead PStep.nil_dead hp

/-- `wb`/`wbisim`, positive: `τ.a.0 ≈ a.0`. -/
theorem wbisim_example_pos : wbisim (@PStep Lbl) (tau (act .a .nil)) (act .a .nil) :=
  wbisim_tau _

/-- `wb`/`wbisim`, negative: `τ.a.0 ≉ 0`. -/
theorem wbisim_example_neg : ¬ wbisim (@PStep Lbl) (tau (act .a .nil)) .nil :=
  not_wbisim_tau_act_nil

/-- `ex`/`expands`, positive: `τ.a.0 ≳ a.0`. -/
theorem expands_example_pos : expands (@PStep Lbl) (tau (act .a .nil)) (act .a .nil) :=
  expands_tau _

/-- `ex`/`expands`, negative: `a.0 ⋧ τ.a.0` (expansion is not symmetric). -/
theorem expands_example_neg : ¬ expands (@PStep Lbl) (act .a .nil) (tau (act .a .nil)) :=
  not_expands_act_tau

/-! ### The pitfall: weak bisimulation up to weak bisimilarity -/

/-- The one-pair relation `{(τ.a.0, 0)}`. -/
def pitfallRel : Rel (Proc Lbl) := fun p q => p = tau (act .a .nil) ∧ q = .nil

/-- `a.0 ≈ τ.a.0 R 0 ≈ 0`. -/
theorem weakUpTo_pitfall_mem : weakUpTo PStep pitfallRel (act .a .nil) .nil :=
  ⟨tau (act .a .nil), .nil, wbisim_symm (wbisim_tau _), ⟨rfl, rfl⟩, wbisim_refl _ _⟩

/-- **Weak bisimulation up to weak bisimilarity is unsound** (concrete
counterexample): `{(τ.a.0, 0)}` progresses to `≈ R ≈` under `wb`, because the
τ-move `τ.a.0 -τ→ a.0` is answered by `0` standing still and
`a.0 ≈ τ.a.0 R 0 ≈ 0`; yet `τ.a.0 ≉ 0`. -/
theorem weak_upto_weak_bisim_unsound :
    pitfallRel ⊑ wb PStep (weakUpTo PStep pitfallRel) ∧ ¬ pitfallRel ⊑ wbisim PStep := by
  refine ⟨?_, fun h => not_wbisim_tau_act_nil (h _ _ ⟨rfl, rfl⟩)⟩
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => absurd hs (PStep.nil_dead l q')⟩
  obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
  exact ⟨.nil, WStep.refl_none _ _, weakUpTo_pitfall_mem⟩

/-- Corollary in `Sound` form. -/
theorem weak_upto_weak_bisim_not_sound : ¬ Sound (wb (@PStep Lbl)) (weakUpTo PStep) :=
  fun hs => weak_upto_weak_bisim_unsound.2 (hs _ weak_upto_weak_bisim_unsound.1)

/-- `weakUpTo`, positive example. -/
theorem weakUpTo_example_pos : weakUpTo (@PStep Lbl) pitfallRel (act .a .nil) .nil :=
  weakUpTo_pitfall_mem

/-- `weakUpTo`, negative example: with `R` empty nothing is related. -/
theorem weakUpTo_example_neg : ¬ weakUpTo (@PStep Lbl) botRel .nil .nil :=
  fun ⟨_, _, _, h, _⟩ => h

/-- Positive control (witness level): the same relation does *not* progress
to `~ R ~` under `wb`, because `a.0 ≁ τ.a.0`. -/
theorem pitfall_control_strong :
    ¬ pitfallRel ⊑ wb PStep (strongUpTo PStep pitfallRel) := by
  intro h
  obtain ⟨q', hq', ⟨_, _, hb, ⟨rfl, rfl⟩, _⟩⟩ :=
    (h _ _ ⟨rfl, rfl⟩).1 none (act .a .nil) (PStep.pre _ _)
  exact not_bisim_act_tau hb

/-- Positive control (witness level): the same relation does *not* progress
to `≳ R ≲` under `wb`, because `a.0 ⋧ τ.a.0`. -/
theorem pitfall_control_expansion :
    ¬ pitfallRel ⊑ wb PStep (expUpTo PStep pitfallRel) := by
  intro h
  obtain ⟨q', hq', ⟨_, _, he, ⟨rfl, rfl⟩, _⟩⟩ :=
    (h _ _ ⟨rfl, rfl⟩).1 none (act .a .nil) (PStep.pre _ _)
  exact not_expands_act_tau he

/-- `expUpTo`, negative example (the control above at the level of the
up-to function). -/
theorem expUpTo_example_neg : ¬ expUpTo (@PStep Lbl) pitfallRel (act .a .nil) .nil :=
  fun ⟨_, _, he, ⟨h1, _⟩, _⟩ => by subst h1; exact not_expands_act_tau he

/-- `expUpTo`, positive example: `τ.0 ≳ 0 R 0 ≲ 0` with `R = {(0, 0)}`. -/
theorem expUpTo_example_pos :
    expUpTo (@PStep Lbl) (fun p q => p = .nil ∧ q = .nil) (tau .nil) .nil :=
  ⟨.nil, .nil, expands_tau _, ⟨rfl, rfl⟩, expands_refl _ _⟩

/-! ### The literal "`≳ R ≈` in both clauses" variant is unsound -/

/-- The one-pair relation `{(0, τ.a.0)}` (the mirror image of `pitfallRel`). -/
def mirrorRel : Rel (Proc Lbl) := fun p q => p = .nil ∧ q = tau (act .a .nil)

/-- `0 ≳ 0 R τ.a.0 ≈ a.0`. -/
theorem expWeakUpTo_mirror_mem : expWeakUpTo PStep mirrorRel .nil (act .a .nil) :=
  ⟨.nil, tau (act .a .nil), expands_refl _ _, ⟨rfl, rfl⟩, wbisim_tau _⟩

/-- **Expansion on the left and weak bisimilarity on the right, used in both
clauses of the symmetric functional `wb`, is unsound**: `{(0, τ.a.0)}`
progresses to `≳ R ≈` (the right state's τ-move is answered by `0` standing
still, and `0 ≳ 0 R τ.a.0 ≈ a.0`), yet `0 ≉ τ.a.0`. -/
theorem weak_upto_expansion_left_weak_right_unsound :
    mirrorRel ⊑ wb PStep (expWeakUpTo PStep mirrorRel) ∧ ¬ mirrorRel ⊑ wbisim PStep := by
  refine ⟨?_, fun h => not_wbisim_tau_act_nil (wbisim_symm (h _ _ ⟨rfl, rfl⟩))⟩
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => absurd hs (PStep.nil_dead l p'), fun l q' hs => ?_⟩
  obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
  exact ⟨.nil, WStep.refl_none _ _, expWeakUpTo_mirror_mem⟩

/-- Corollary in `Sound` form. -/
theorem weak_upto_expansion_left_weak_right_not_sound :
    ¬ Sound (wb (@PStep Lbl)) (expWeakUpTo PStep) :=
  fun hs => weak_upto_expansion_left_weak_right_unsound.2
    (hs _ weak_upto_expansion_left_weak_right_unsound.1)

/-- `expWeakUpTo`, positive example. -/
theorem expWeakUpTo_example_pos : expWeakUpTo (@PStep Lbl) mirrorRel .nil (act .a .nil) :=
  expWeakUpTo_mirror_mem

/-- `expWeakUpTo`, negative example: `a.0 ⋧ τ.a.0`, so `(a.0, 0)` is not in
`≳ {(τ.a.0, 0)} ≈`. -/
theorem expWeakUpTo_example_neg : ¬ expWeakUpTo (@PStep Lbl) pitfallRel (act .a .nil) .nil :=
  fun ⟨_, _, he, ⟨h1, _⟩, _⟩ => by subst h1; exact not_expands_act_tau he

/-- Positive control (witness level): `{(0, τ.a.0)}` does not progress to
`≳ R ≲`. -/
theorem mirror_control_expansion :
    ¬ mirrorRel ⊑ wb PStep (expUpTo PStep mirrorRel) := by
  intro h
  obtain ⟨p', hp', ⟨_, _, _, ⟨rfl, rfl⟩, he⟩⟩ :=
    (h _ _ ⟨rfl, rfl⟩).2 none (act .a .nil) (PStep.pre _ _)
  exact not_expands_act_tau he

/-- Positive control (witness level): `{(0, τ.a.0)}` violates the right-hand
hypothesis of the asymmetric technique (`≈ R ≲`). -/
theorem mirror_control_asymmetric :
    ¬ mirrorRel ⊑ wsimR PStep (weakExpUpTo PStep mirrorRel) := by
  intro h
  obtain ⟨p', hp', ⟨_, _, _, ⟨rfl, rfl⟩, he⟩⟩ :=
    h _ _ ⟨rfl, rfl⟩ none (act .a .nil) (PStep.pre _ _)
  exact not_expands_act_tau he

/-- `weakExpUpTo`, negative example (the control above at the level of the
up-to function). -/
theorem weakExpUpTo_example_neg : ¬ weakExpUpTo (@PStep Lbl) mirrorRel .nil (act .a .nil) :=
  fun ⟨_, _, _, ⟨_, h2⟩, he⟩ => by subst h2; exact not_expands_act_tau he

/-! ### Tightness counterexamples for `weak_upto_expansion_asymmetric_sound`

Each satisfies the *other* hypothesis exactly as stated, satisfies the dropped
hypothesis in a weakened form (expansion replaced by weak bisimilarity), and
the conclusion fails.  A fortiori, neither hypothesis can be dropped. -/

/-- Weakening `hL` from `≳ R ≈` to `≈ R ≈` (keeping `hR`): the pitfall
relation `{(τ.a.0, 0)}`. -/
theorem asym_counterexample_left_weakened :
    pitfallRel ⊑ wsimL PStep (weakUpTo PStep pitfallRel) ∧
    pitfallRel ⊑ wsimR PStep (weakExpUpTo PStep pitfallRel) ∧
    ¬ pitfallRel ⊑ wbisim PStep := by
  refine ⟨fun p q h => (weak_upto_weak_bisim_unsound.1 p q h).1, ?_,
    weak_upto_weak_bisim_unsound.2⟩
  rintro p q ⟨rfl, rfl⟩
  exact fun l q' hs => absurd hs (PStep.nil_dead l q')

/-- Weakening `hR` from `≈ R ≲` to `≈ R ≈` (keeping `hL`): the mirror relation
`{(0, τ.a.0)}`. -/
theorem asym_counterexample_right_weakened :
    mirrorRel ⊑ wsimL PStep (expWeakUpTo PStep mirrorRel) ∧
    mirrorRel ⊑ wsimR PStep (weakUpTo PStep mirrorRel) ∧
    ¬ mirrorRel ⊑ wbisim PStep := by
  refine ⟨?_, ?_, weak_upto_expansion_left_weak_right_unsound.2⟩
  · rintro p q ⟨rfl, rfl⟩
    exact fun l p' hs => absurd hs (PStep.nil_dead l p')
  · rintro p q ⟨rfl, rfl⟩
    intro l q' hs
    obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, WStep.refl_none _ _,
      ⟨.nil, tau (act .a .nil), wbisim_refl _ _, ⟨rfl, rfl⟩, wbisim_tau _⟩⟩

/-! ### Up to expansion is sound but not compatible -/

/-- **Witness that `≳ R ≲` does not commute with `wb`**, over any label type
(including the empty one): with `R = ∅`, the pair `(τ.0, 0)` is in
`≳ (wb ∅) ≲` (as `τ.0 ≳ 0`, `0 (wb ∅) 0`, `0 ≳ 0`) but not in `wb (≳ ∅ ≲)`,
and `wb (≳ ∅ ≲)` and `wb ∅` coincide. -/
theorem weak_upto_expansion_commutes_counterexample {L : Type v} :
    expUpTo (@PStep L) (wb PStep botRel) (tau .nil) .nil ∧
    ¬ wb (@PStep L) (expUpTo PStep botRel) (tau .nil) .nil ∧
    (wb (@PStep L) (expUpTo PStep botRel) ⊑ wb PStep botRel) ∧
    (wb (@PStep L) botRel ⊑ wb PStep (expUpTo PStep botRel)) := by
  refine ⟨⟨.nil, .nil, expands_tau _, wb_of_dead PStep.nil_dead PStep.nil_dead,
    expands_refl _ _⟩, ?_, ?_, ?_⟩
  · intro hwb
    obtain ⟨_, _, ⟨_, _, _, hbot, _⟩⟩ := hwb.1 none .nil (PStep.pre _ _)
    exact hbot
  · exact wb_mono PStep _ _ (fun _ _ ⟨_, _, _, h, _⟩ => h)
  · exact wb_mono PStep _ _ (botRel_incl _)

/-- **`≳ R ≲` is not compatible with `wb`**, over any label type: it is
monotone, so the commutation `≳ (wb R) ≲ ⊑ wb (≳ R ≲)` is exactly what fails
(witness: `weak_upto_expansion_commutes_counterexample`). -/
theorem weak_upto_expansion_not_compatible {L : Type v} :
    MonoRel (expUpTo (@PStep L)) ∧
    ¬ Commutes (wb (@PStep L)) (expUpTo PStep) ∧
    ¬ Compatible (wb (@PStep L)) (expUpTo PStep) := by
  have hnc : ¬ Commutes (wb (@PStep L)) (expUpTo PStep) := fun h =>
    weak_upto_expansion_commutes_counterexample.2.1
      (h botRel _ _ weak_upto_expansion_commutes_counterexample.1)
  exact ⟨expUpTo_mono PStep, hnc, fun h => hnc h.comm⟩

/-! ### Usefulness witnesses (non-vacuity) for the weak techniques -/

/-- `relS = {(a.(0+0), a.0), (0, 0)}` is not a weak bisimulation but
progresses to `~ relS ~` under `wb`. -/
theorem weak_upto_strong_bisim_useful :
    relS ⊑ wb PStep (strongUpTo PStep relS) ∧ ¬ relS ⊑ wb PStep relS := by
  refine ⟨?_, ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hmid : strongUpTo PStep relS (.sum .nil .nil) .nil :=
        ⟨.nil, .nil, bisim_sum_nil_nil, Or.inr ⟨rfl, rfl⟩, bisim_refl _ _⟩
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.nil, WStep.single (PStep.pre _ _), hmid⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.sum .nil .nil, WStep.single (PStep.pre _ _), hmid⟩
    · exact wb_of_dead PStep.nil_dead PStep.nil_dead
  · intro h
    obtain ⟨q', _, hr⟩ := (h _ _ (Or.inl ⟨rfl, rfl⟩)).1 (some .a) (.sum .nil .nil) (PStep.pre _ _)
    rcases hr with ⟨hp, _⟩ | ⟨hp, _⟩ <;> cases hp

/-- `{(a.τ.0, a.0), (0, 0)}`. -/
def relExp : Rel (Proc Lbl) := fun p q =>
  (p = act .a (tau .nil) ∧ q = act .a .nil) ∨ (p = .nil ∧ q = .nil)

/-- `relExp` is not a weak bisimulation but progresses to `≳ relExp ≲` under
`wb`. -/
theorem weak_upto_expansion_useful :
    relExp ⊑ wb PStep (expUpTo PStep relExp) ∧ ¬ relExp ⊑ wb PStep relExp := by
  refine ⟨?_, ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hmid : expUpTo PStep relExp (tau .nil) .nil :=
        ⟨.nil, .nil, expands_tau _, Or.inr ⟨rfl, rfl⟩, expands_refl _ _⟩
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.nil, WStep.single (PStep.pre _ _), hmid⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨tau .nil, WStep.single (PStep.pre _ _), hmid⟩
    · exact wb_of_dead PStep.nil_dead PStep.nil_dead
  · intro h
    obtain ⟨q', _, hr⟩ := (h _ _ (Or.inl ⟨rfl, rfl⟩)).1 (some .a) (tau .nil) (PStep.pre _ _)
    rcases hr with ⟨hp, _⟩ | ⟨hp, _⟩ <;> cases hp

/-- Non-vacuity of `weak_upto_expansion_asymmetric_sound`: `relExp` satisfies
both hypotheses and is not itself a weak bisimulation. -/
theorem weak_upto_expansion_asymmetric_nonvacuity :
    relExp ⊑ wsimL PStep (expWeakUpTo PStep relExp) ∧
    relExp ⊑ wsimR PStep (weakExpUpTo PStep relExp) ∧ ¬ relExp ⊑ wb PStep relExp := by
  refine ⟨?_, ?_, weak_upto_expansion_useful.2⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · intro l p' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, WStep.single (PStep.pre _ _),
        ⟨.nil, .nil, expands_tau _, Or.inr ⟨rfl, rfl⟩, wbisim_refl _ _⟩⟩
    · exact fun l p' hs => absurd hs (PStep.nil_dead l p')
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · intro l q' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨tau .nil, WStep.single (PStep.pre _ _),
        ⟨.nil, .nil, wbisim_tau _, Or.inr ⟨rfl, rfl⟩, expands_refl _ _⟩⟩
    · exact fun l q' hs => absurd hs (PStep.nil_dead l q')

/-- `weakExpUpTo`, positive example: `τ.0 ≈ 0 R 0 ≲ 0`. -/
theorem weakExpUpTo_example_pos : weakExpUpTo (@PStep Lbl) relExp (tau .nil) .nil :=
  ⟨.nil, .nil, wbisim_tau _, Or.inr ⟨rfl, rfl⟩, expands_refl _ _⟩

/-- Strictly asymmetric witness for `weak_upto_expansion_asymmetric_sound`:
`{(τ.b.τ.0, b.0), (b.τ.0, b.τ.0), (τ.0, τ.0), (0, 0)}`. -/
def asymStrictRel : Rel (Proc Lbl) := fun p q =>
  (p = tau (act .b (tau .nil)) ∧ q = act .b .nil) ∨
  (p = act .b (tau .nil) ∧ q = act .b (tau .nil)) ∨
  (p = tau .nil ∧ q = tau .nil) ∨
  (p = .nil ∧ q = .nil)

/-- `b.τ.0 ≈ b.0`. -/
theorem wbisim_act_b_tau_nil : wbisim (@PStep Lbl) (act .b (tau .nil)) (act .b .nil) := by
  let W : Rel (Proc Lbl) := fun p q =>
    (p = act .b (tau .nil) ∧ q = act .b .nil) ∨ (p = tau .nil ∧ q = .nil) ∨ p = q
  refine ⟨W, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl)
  · refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, WStep.single (PStep.pre _ _), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨tau .nil, WStep.single (PStep.pre _ _), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · refine ⟨fun l p' hs => ?_, fun l q' hs => absurd hs (PStep.nil_dead l q')⟩
    obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, WStep.refl_none _ _, Or.inr (Or.inr rfl)⟩
  · exact wb_mono PStep idRel W (fun _ _ h => Or.inr (Or.inr h)) _ _ (idRel_wb PStep _ _ rfl)

/-- Strict non-vacuity of `weak_upto_expansion_asymmetric_sound`:
`asymStrictRel` satisfies both asymmetric hypotheses, yet does *not* progress
under the symmetric technique `≳ R ≲` (so the asymmetric form is strictly more
permissive on this instance) and is not itself a weak bisimulation. -/
theorem weak_upto_expansion_asymmetric_strict_nonvacuity :
    asymStrictRel ⊑ wsimL PStep (expWeakUpTo PStep asymStrictRel) ∧
    asymStrictRel ⊑ wsimR PStep (weakExpUpTo PStep asymStrictRel) ∧
    ¬ asymStrictRel ⊑ wb PStep (expUpTo PStep asymStrictRel) ∧
    ¬ asymStrictRel ⊑ wb PStep asymStrictRel := by
  have hnot : ¬ asymStrictRel ⊑ wb PStep (expUpTo PStep asymStrictRel) := by
    intro hwb
    obtain ⟨q', hq', ⟨p₁, q₁, hp₁, hr, hq₁⟩⟩ :=
      (hwb _ _ (Or.inl ⟨rfl, rfl⟩)).1 none (act .b (tau .nil)) (PStep.pre _ _)
    have hq_eq := WStep.none_of_noTau (PStep.act_noTau _ _) hq'
    subst hq_eq
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨W, hW, hw⟩ := hp₁
      obtain ⟨_, hsh, _⟩ := (hW _ _ hw).1 (some .b) (tau .nil) (PStep.pre _ _)
      rcases hsh with hs | ⟨hl, _⟩
      · cases (PStep.pre_inv hs).1
      · cases hl
    · obtain ⟨W, hW, hw⟩ := hq₁
      obtain ⟨r', hsh, hw'⟩ := (hW _ _ hw).1 (some .b) .nil (PStep.pre _ _)
      rcases hsh with hs | ⟨hl, _⟩
      · obtain ⟨_, rfl⟩ := PStep.pre_inv hs
        obtain ⟨_, ⟨_, hstep, _⟩, _⟩ := (hW _ _ hw').2 none .nil (PStep.pre _ _)
        exact PStep.nil_dead _ _ hstep
      · cases hl
    · obtain ⟨W, hW, hw⟩ := hq₁
      obtain ⟨_, hsh, _⟩ := (hW _ _ hw).1 (some .b) .nil (PStep.pre _ _)
      rcases hsh with hs | ⟨hl, _⟩
      · cases (PStep.pre_inv hs).1
      · cases hl
    · obtain ⟨W, hW, hw⟩ := hq₁
      obtain ⟨_, hsh, _⟩ := (hW _ _ hw).1 (some .b) .nil (PStep.pre _ _)
      rcases hsh with hs | ⟨hl, _⟩
      · exact PStep.nil_dead _ _ hs
      · cases hl
  refine ⟨?_, ?_, hnot, fun h => hnot (Incl.trans h (wb_mono PStep _ _
    (fun p q hr => ⟨p, q, expands_refl _ _, hr, expands_refl _ _⟩)))⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · intro l p' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨act .b .nil, WStep.refl_none _ _,
        ⟨act .b (tau .nil), act .b (tau .nil), expands_refl _ _,
          Or.inr (Or.inl ⟨rfl, rfl⟩), wbisim_act_b_tau_nil⟩⟩
    · intro l p' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨tau .nil, WStep.single (PStep.pre _ _),
        ⟨tau .nil, tau .nil, expands_refl _ _,
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), wbisim_refl _ _⟩⟩
    · intro l p' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, WStep.single (PStep.pre _ _),
        ⟨.nil, .nil, expands_refl _ _,
          Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), wbisim_refl _ _⟩⟩
    · exact fun l p' hs => absurd hs (PStep.nil_dead l p')
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · intro l q' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      have hw : WStep (@PStep Lbl) (tau (act .b (tau .nil))) (some .b) .nil :=
        ⟨act .b (tau .nil), tau .nil,
          TauStar.step (PStep.pre _ _) (TauStar.refl _),
          PStep.pre _ _,
          TauStar.step (PStep.pre _ _) (TauStar.refl _)⟩
      exact ⟨.nil, hw, ⟨.nil, .nil, wbisim_refl _ _,
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), expands_refl _ _⟩⟩
    · intro l q' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨tau .nil, WStep.single (PStep.pre _ _),
        ⟨tau .nil, tau .nil, wbisim_refl _ _,
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), expands_refl _ _⟩⟩
    · intro l q' hs
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, WStep.single (PStep.pre _ _),
        ⟨.nil, .nil, wbisim_refl _ _,
          Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), expands_refl _ _⟩⟩
    · exact fun l q' hs => absurd hs (PStep.nil_dead l q')

/-! ### Two-sided closures need a middle `R`-pair -/

/-- `{(a.τ.0, a.0)}`, a single pair of processes related by expansion. -/
def singletonExpRel : Rel (Proc Lbl) := fun p q => p = act .a (tau .nil) ∧ q = act .a .nil

/-- `a.τ.0 ≳ a.0` holds, yet `{(a.τ.0, a.0)}` does not progress under `~ R ~`,
`≳ R ≲`, or (for left moves) `≳ R ≈`: these closures are relational
compositions and need a middle `R`-pair, and `(0, 0)` is not in the relation. -/
theorem singleton_expanding_pair_fails_without_refl_pair :
    expands (@PStep Lbl) (act .a (tau .nil)) (act .a .nil) ∧
    ¬ (singletonExpRel ⊑ wb PStep (strongUpTo PStep singletonExpRel)) ∧
    ¬ (singletonExpRel ⊑ wb PStep (expUpTo PStep singletonExpRel)) ∧
    ¬ (singletonExpRel ⊑ wsimL PStep (expWeakUpTo PStep singletonExpRel)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let W : Rel (Proc Lbl) := fun p q =>
      (p = act .a (tau .nil) ∧ q = act .a .nil) ∨ (p = tau .nil ∧ q = .nil) ∨ p = q
    refine ⟨W, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl)
    · refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.nil, StepHat.single (PStep.pre _ _), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨tau .nil, WStepPlus.single (PStep.pre _ _), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · refine ⟨fun l p' hs => ?_, fun l q' hs => absurd hs (PStep.nil_dead l q')⟩
      obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, Or.inr ⟨rfl, rfl⟩, Or.inr (Or.inr rfl)⟩
    · exact ex_mono PStep idRel W (fun _ _ h => Or.inr (Or.inr h)) _ _ (idRel_ex PStep _ _ rfl)
  · intro h
    obtain ⟨_, _, ⟨_, _, hb, ⟨rfl, rfl⟩, _⟩⟩ :=
      (h _ _ ⟨rfl, rfl⟩).1 (some .a) (tau .nil) (PStep.pre _ _)
    obtain ⟨W, hW, hw⟩ := hb
    obtain ⟨_, hs, _⟩ := (hW _ _ hw).2 (some .a) (tau .nil) (PStep.pre _ _)
    cases (PStep.pre_inv hs).1
  · intro h
    obtain ⟨_, _, ⟨_, _, he, ⟨rfl, rfl⟩, _⟩⟩ :=
      (h _ _ ⟨rfl, rfl⟩).1 (some .a) (tau .nil) (PStep.pre _ _)
    obtain ⟨W, hW, hw⟩ := he
    obtain ⟨_, hwp, _⟩ := (hW _ _ hw).2 (some .a) (tau .nil) (PStep.pre _ _)
    obtain ⟨x, _, htau, hstep, _⟩ := hwp
    rcases htau with _ | ⟨hs0, htau'⟩
    · cases (PStep.pre_inv hstep).1
    · obtain ⟨_, rfl⟩ := PStep.pre_inv hs0
      have hx := TauStar.eq_of_noTau (PStep.nil_dead none) htau'
      subst hx
      exact PStep.nil_dead _ _ hstep
  · intro h
    obtain ⟨_, _, ⟨_, _, he, ⟨rfl, rfl⟩, _⟩⟩ :=
      h _ _ ⟨rfl, rfl⟩ (some .a) (tau .nil) (PStep.pre _ _)
    obtain ⟨W, hW, hw⟩ := he
    obtain ⟨_, hwp, _⟩ := (hW _ _ hw).2 (some .a) (tau .nil) (PStep.pre _ _)
    obtain ⟨x, _, htau, hstep, _⟩ := hwp
    rcases htau with _ | ⟨hs0, htau'⟩
    · cases (PStep.pre_inv hstep).1
    · obtain ⟨_, rfl⟩ := PStep.pre_inv hs0
      have hx := TauStar.eq_of_noTau (PStep.nil_dead none) htau'
      subst hx
      exact PStep.nil_dead _ _ hstep

/-! ### Escape hatches and orientation for the pitfall -/

/-- With weak challenges (`wbWeak`), the pitfall relation does not progress
to `≈ R ≈`: the challenge `τ.a.0 =a⇒ 0` has no answer from `0`.  (In general
`≈ R ≈` is sound for `wbWeak`: `weak_challenge_upto_weak_bisim_sound`.) -/
theorem pitfall_not_progress_wbWeak :
    ¬ pitfallRel ⊑ wbWeak PStep (weakUpTo PStep pitfallRel) := fun h =>
  weak_upto_weak_bisim_unsound.2 (weak_challenge_upto_weak_bisim_sound PStep pitfallRel h)

/-- **Reversing the expansion symbols is unsound**: with `≲ R ≳`
(`revExpUpTo`), the pitfall relation `{(τ.a.0, 0)}` progresses
(`a.0 ≲ τ.a.0 R 0 ≳ 0`), yet `τ.a.0 ≉ 0`. -/
theorem weak_upto_reversed_expansion_unsound :
    pitfallRel ⊑ wb PStep (revExpUpTo PStep pitfallRel) ∧ ¬ pitfallRel ⊑ wbisim PStep := by
  refine ⟨?_, weak_upto_weak_bisim_unsound.2⟩
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => absurd hs (PStep.nil_dead l q')⟩
  obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
  exact ⟨.nil, WStep.refl_none _ _, tau (act .a .nil), .nil, expands_tau _, ⟨rfl, rfl⟩,
    expands_refl _ _⟩

/-- Corollary in `Sound` form. -/
theorem weak_upto_reversed_expansion_not_sound : ¬ Sound (wb (@PStep Lbl)) (revExpUpTo PStep) :=
  fun hs => weak_upto_reversed_expansion_unsound.2 (hs _ weak_upto_reversed_expansion_unsound.1)

/-- Without visible labels, the pitfall cannot occur: every up-to function is
sound for `wb` on `Proc Empty` (instance of `sound_wb_of_no_visible`). -/
theorem weak_upto_weak_bisim_sound_no_visible : Sound (wb (@PStep Empty)) (weakUpTo PStep) :=
  sound_wb_of_no_visible (fun e => e.elim) _

/-! ### Non-degenerate definition examples for the weak functional -/

/-- `wsimL` and `wsimR`, positive examples with a live visible transition:
`a.0` and `τ.a.0` answer each other's `a`-move into the identity. -/
theorem wsimL_wsimR_example_pos_live :
    wsimL (@PStep Lbl) idRel (act .a .nil) (tau (act .a .nil)) ∧
    wsimR (@PStep Lbl) idRel (tau (act .a .nil)) (act .a .nil) := by
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, wstep_example_pos, rfl⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, wstep_example_pos, rfl⟩

end Concrete

end Toy.UpTo
