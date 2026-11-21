import ToyUpTo.Companion

/-!
# Supplementary witnesses

Additional kernel-checked instances cited by the result cards.  Nothing here
is used by, or changes, any definition or statement of the other modules.

* non-vacuity of the escape-hatch theorems for transition systems without
  silent steps (`weak_upto_weak_bisim_sound_of_noTau`,
  `expUpTo_commutes_of_noTau`), without visible labels
  (`sound_wb_of_no_visible`), with weak challenges
  (`weak_challenge_upto_weak_bisim_sound`), for the one-sided functional
  (`weak_upto_expansion_left_weak_right_sound_for_wsimL`) and for guarded choice
  (`wbisim_guarded_sum_congruence`);
* strict growth of the iterates of `stepSq` on the process language itself;
* a weak-functional instance for up to union with weak bisimilarity;
* a `Prop`-level proof that the one-pair relation
  `{(τ.a.0 + b.0, a.0 + b.0)}` does not progress to its `+`-context closure
  under `wb`.

Concrete instances are written inline (with `let`) so that each statement
exposes the instance it is about.
-/

namespace Toy.UpTo

open Proc

/-- Up to union with weak bisimilarity on the weak functional does real work
even on a singleton: `{(a.τ.0, a.0)}` is not a weak bisimulation, but
progresses to `R ∪ ≈` under `wb`. -/
theorem weak_upto_union_wbisim_useful_singleton :
    singletonExpRel ⊑ wb PStep (unionWbisim PStep singletonExpRel) ∧
    ¬ singletonExpRel ⊑ wb PStep singletonExpRel := by
  refine ⟨?_, ?_⟩
  · rintro p q ⟨rfl, rfl⟩
    refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, WStep.single (PStep.pre _ _), Or.inr (wbisim_tau .nil)⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨tau .nil, WStep.single (PStep.pre _ _), Or.inr (wbisim_tau .nil)⟩
  · intro h
    obtain ⟨_, _, ⟨hp, _⟩⟩ := (h _ _ ⟨rfl, rfl⟩).1 (some .a) (tau .nil) (PStep.pre _ _)
    cases hp

/-- The iterates of `stepSq` (`R ↦ R ∪ R;R`) grow strictly on the process
language: on the chain `0 → τ.0 → τ.τ.0 → τ.τ.τ.0`, the pair
`(0, τ.τ.τ.0)` is in the second iterate but not in the first. -/
theorem stepSq_strict_on_proc :
    let C : Rel (Proc Lbl) := fun p q =>
      (p = .nil ∧ q = tau .nil) ∨
      (p = tau .nil ∧ q = tau (tau .nil)) ∨
      (p = tau (tau .nil) ∧ q = tau (tau (tau .nil)))
    ¬ iter stepSq 1 C .nil (tau (tau (tau .nil))) ∧
    iter stepSq 2 C .nil (tau (tau (tau .nil))) := by
  intro C
  refine ⟨?_, ?_⟩
  · rintro (h0 | ⟨r, hr1, hr2⟩)
    · rcases h0 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    · rcases hr1 with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · rcases hr2 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h
      · cases h
      · cases h
  · exact Or.inr ⟨tau (tau .nil),
      Or.inr ⟨tau .nil, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩,
      Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- Non-vacuity of the hypothesis `NoTau T` (used by
`weak_upto_weak_bisim_sound_of_noTau` and `expUpTo_commutes_of_noTau`): a
three-state system with one visible label and no silent steps
(`0 -a→ 2`, `1 -a→ 2`) in which weak bisimilarity is not the identity
(`0 ≈ 1`) and not total (`0 ≉ 2`). -/
theorem noTau_nonvacuity :
    let T : LTS (Fin 3) Unit := fun p l q =>
      l = some () ∧ ((p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 2))
    NoTau T ∧ wbisim T 0 1 ∧ ¬ wbisim T 0 2 := by
  intro T
  have hnt : NoTau T := by
    intro p q ⟨hl, _⟩
    cases hl
  refine ⟨hnt, ?_, ?_⟩
  · refine ⟨fun p q => (p = 0 ∧ q = 1) ∨ p = q, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rintro p q (⟨rfl, rfl⟩ | rfl)
    · refine ⟨fun l p' ⟨hl, hp'⟩ => ?_, fun l q' ⟨hl, hq'⟩ => ?_⟩
      · subst hl
        rcases hp' with ⟨_, rfl⟩ | ⟨h, _⟩
        · exact ⟨2, WStep.single ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, Or.inr rfl⟩
        · exact absurd h (by decide)
      · subst hl
        rcases hq' with ⟨h, _⟩ | ⟨_, rfl⟩
        · exact absurd h (by decide)
        · exact ⟨2, WStep.single ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, Or.inr rfl⟩
    · exact wb_mono T idRel _ (fun _ _ h => Or.inr h) _ _ (idRel_wb T _ _ rfl)
  · rintro ⟨W, hW, hw⟩
    obtain ⟨q', hq', _⟩ := (hW 0 2 hw).1 (some ()) 2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    have hs := WStep.some_of_noTau' hnt hq'
    rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- Non-vacuity of the hypothesis `L → False` (used by
`sound_wb_of_no_visible`): a two-state system over the empty label type with
a live silent loop, in which a looping state and a dead state are weakly
bisimilar. -/
theorem no_visible_nonvacuity :
    let T : LTS Bool Empty := fun p l q => p = true ∧ l = none ∧ q = true
    (Empty → False) ∧ T true none true ∧ wbisim T true false :=
  ⟨Empty.elim, ⟨rfl, rfl, rfl⟩, wbisim_total_of_no_visible Empty.elim true false⟩

/-- `weak_challenge_upto_weak_bisim_sound` does real work: `relExp` is not a
post-fixpoint of the weak-challenge functional `wbWeak`, but progresses to
`≈ relExp ≈` under it. -/
theorem weak_challenge_upto_weak_bisim_useful :
    relExp ⊑ wbWeak PStep (weakUpTo PStep relExp) ∧
    ¬ relExp ⊑ wbWeak PStep relExp := by
  refine ⟨?_, ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨fun l p' hw => ?_, fun l q' hw => ?_⟩
      · cases l with
        | none =>
          have hp := TauStar.eq_of_noTau (PStep.act_noTau _ _) hw
          subst hp
          exact ⟨act .a .nil, WStep.refl_none _ _,
            act .a (tau .nil), act .a .nil, wbisim_refl _ _, Or.inl ⟨rfl, rfl⟩, wbisim_refl _ _⟩
        | some x =>
          obtain ⟨p₂, hs, ht⟩ := WStep.some_of_noTau (PStep.act_noTau _ _) hw
          obtain ⟨hl, rfl⟩ := PStep.pre_inv hs
          injection hl with hx; subst hx
          have hnil : wbisim (@PStep Lbl) p' .nil := by
            cases ht with
            | refl => exact wbisim_tau .nil
            | step hs' ht' =>
              obtain ⟨_, rfl⟩ := PStep.pre_inv hs'
              have heq := TauStar.eq_of_noTau (PStep.nil_dead none) ht'
              subst heq
              exact wbisim_refl _ _
          exact ⟨.nil, WStep.single (PStep.pre _ _),
            .nil, .nil, hnil, Or.inr ⟨rfl, rfl⟩, wbisim_refl _ _⟩
      · cases l with
        | none =>
          have hq := TauStar.eq_of_noTau (PStep.act_noTau _ _) hw
          subst hq
          exact ⟨act .a (tau .nil), WStep.refl_none _ _,
            act .a (tau .nil), act .a .nil, wbisim_refl _ _, Or.inl ⟨rfl, rfl⟩, wbisim_refl _ _⟩
        | some x =>
          obtain ⟨q₂, hs, ht⟩ := WStep.some_of_noTau (PStep.act_noTau _ _) hw
          obtain ⟨hl, rfl⟩ := PStep.pre_inv hs
          injection hl with hx; subst hx
          have heq := TauStar.eq_of_noTau (PStep.nil_dead none) ht
          subst heq
          exact ⟨.nil,
            ⟨act .a (tau .nil), tau .nil, TauStar.refl _, PStep.pre _ _,
              TauStar.step (PStep.pre _ _) (TauStar.refl _)⟩,
            .nil, .nil, wbisim_refl _ _, Or.inr ⟨rfl, rfl⟩, wbisim_refl _ _⟩
    · refine ⟨fun l p' hw => ?_, fun l q' hw => ?_⟩
      · cases l with
        | none =>
          have hp := TauStar.eq_of_noTau (PStep.nil_dead none) hw
          subst hp
          exact ⟨.nil, WStep.refl_none _ _, .nil, .nil,
            wbisim_refl _ _, Or.inr ⟨rfl, rfl⟩, wbisim_refl _ _⟩
        | some x => exact absurd hw (WStep.not_some_of_dead PStep.nil_dead)
      · cases l with
        | none =>
          have hq := TauStar.eq_of_noTau (PStep.nil_dead none) hw
          subst hq
          exact ⟨.nil, WStep.refl_none _ _, .nil, .nil,
            wbisim_refl _ _, Or.inr ⟨rfl, rfl⟩, wbisim_refl _ _⟩
        | some x => exact absurd hw (WStep.not_some_of_dead PStep.nil_dead)
  · intro h
    exact weak_upto_expansion_useful.2 (Incl.trans h (wbWeak_incl_wb PStep relExp))

/-- Non-vacuity of `weak_upto_expansion_left_weak_right_sound_for_wsimL`:
`mirrorRel = {(0, τ.a.0)}` satisfies its hypothesis, hence is contained in weak
similarity, although it is not contained in weak bisimilarity. -/
theorem one_sided_wsimL_nonvacuity :
    mirrorRel ⊑ wsimL PStep (expWeakUpTo PStep mirrorRel) ∧
    mirrorRel ⊑ gfp (wsimL PStep) ∧ ¬ mirrorRel ⊑ wbisim PStep :=
  ⟨asym_counterexample_right_weakened.1,
   weak_upto_expansion_left_weak_right_sound_for_wsimL PStep mirrorRel
     asym_counterexample_right_weakened.1,
   weak_upto_expansion_left_weak_right_unsound.2⟩

/-- Non-vacuity of `wbisim_guarded_sum_congruence` with distinct processes and
the silent prefix: `τ.0 ≠ 0`, `τ.0 ≈ 0`, and `τ.τ.0 + a.0 ≈ τ.0 + a.0`. -/
theorem guarded_sum_congruence_nonvacuity :
    tau (.nil : Proc Lbl) ≠ .nil ∧
    wbisim (@PStep Lbl) (tau .nil) .nil ∧
    wbisim (@PStep Lbl) (.sum (tau (tau .nil)) (act .a .nil)) (.sum (tau .nil) (act .a .nil)) :=
  ⟨(by intro h; cases h), wbisim_tau .nil,
   wbisim_guarded_sum_congruence none (act Lbl.a .nil) (wbisim_tau .nil)⟩

/-- The one-pair relation `{(τ.a.0 + b.0, a.0 + b.0)}` does not progress to its
`+`-context closure under `wb`: the challenge `τ.a.0 + b.0 -τ→ a.0` can only be
answered by `a.0 + b.0` standing still, and `(a.0, a.0 + b.0)` is not in the
closure.  (So the prefix `a.[·]` in the counterexample `ctxRel` is needed to
reach the bad pair as a derivative.) -/
theorem one_pair_sum_not_progresses_sumClo :
    let R : Rel (Proc Lbl) := fun p q =>
      p = .sum (tau (act .a .nil)) (act .b .nil) ∧ q = .sum (act .a .nil) (act .b .nil)
    ¬ (R ⊑ wb PStep (SumClo R)) := by
  intro R h
  obtain ⟨q', hq', hsc⟩ :=
    (h _ _ ⟨rfl, rfl⟩).1 none (act .a .nil) (PStep.sumL (PStep.pre _ _))
  have hq_eq := WStep.none_of_noTau
    (PStep.sum_noTau (PStep.act_noTau _ _) (PStep.act_noTau _ _)) hq'
  subst hq_eq
  cases hsc with
  | base hb => cases hb.1

end Toy.UpTo
