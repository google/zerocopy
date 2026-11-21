import ToyUpTo.BasicExamples
import ToyUpTo.Proc
import ToyUpTo.WeakFacts

/-!
# Sound up-to techniques for strong bisimilarity

Compatibility (hence soundness) of three classical techniques with the strong
bisimulation functional `sb`, together with definition examples, non-vacuity
(usefulness) witnesses, the non-vacuity theorems for the abstract results, and
the "up to the total relation" counterexample.
-/

namespace Toy.UpTo

open Proc

universe u v

section General

variable {S : Type u} {L : Type v}

/-- A pair of states without transitions is in `sb T R` for every `R`. -/
theorem sb_of_dead {T : LTS S L} {R : Rel S} {p q : S}
    (hp : ∀ l p', ¬ T p l p') (hq : ∀ l q', ¬ T q l q') : sb T R p q :=
  ⟨fun l p' hs => absurd hs (hp l p'), fun l q' hs => absurd hs (hq l q')⟩

/-! ### Main results -/

/-- **Strong bisimulation up to union with bisimilarity** (`R ∪ ~`) is
compatible with `sb`, for every transition system (instance of
`compatible_union_gfp_of_monotone_functional`). -/
theorem strong_upto_union_bisim_compatible (T : LTS S L) :
    Compatible (sb T) (unionBisim T) :=
  compatible_union_gfp_of_monotone_functional (sb_mono T)

/-- **Strong bisimulation up to bisimilarity on both sides** (`~ R ~`) is
compatible with `sb`, for every transition system. -/
theorem strong_upto_bisim_both_sides_compatible (T : LTS S L) :
    Compatible (sb T) (strongUpTo T) := by
  refine ⟨fun R R' h p q ⟨p₁, q₁, h1, h2, h3⟩ => ⟨p₁, q₁, h1, h _ _ h2, h3⟩, ?_⟩
  intro R p q ⟨p₁, q₁, hp, hr, hq⟩
  have hp' := gfp_postfixed (sb_mono T) _ _ hp
  have hq' := gfp_postfixed (sb_mono T) _ _ hq
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨p₁', hs1, hb1⟩ := hp'.1 l p' hs
    obtain ⟨q₁', hs2, hr2⟩ := hr.1 l p₁' hs1
    obtain ⟨q', hs3, hb3⟩ := hq'.1 l q₁' hs2
    exact ⟨q', hs3, p₁', q₁', hb1, hr2, hb3⟩
  · obtain ⟨q₁', hs1, hb1⟩ := hq'.2 l q' hs
    obtain ⟨p₁', hs2, hr2⟩ := hr.2 l q₁' hs1
    obtain ⟨p', hs3, hb3⟩ := hp'.2 l p₁' hs2
    exact ⟨p', hs3, p₁', q₁', hb3, hr2, hb1⟩

/-- **Strong bisimulation up to equivalence closure** (reflexive, symmetric,
transitive closure) is compatible with `sb`, for every transition system. -/
theorem strong_upto_equivalence_closure_compatible (T : LTS S L) :
    Compatible (sb T) (EqvClo (S := S)) := by
  refine ⟨?_, ?_⟩
  · intro R R' h p q hpq
    induction hpq with
    | base hr => exact EqvClo.base (h _ _ hr)
    | refl p => exact EqvClo.refl p
    | symm _ ih => exact EqvClo.symm ih
    | trans _ _ ih1 ih2 => exact EqvClo.trans ih1 ih2
  · intro R p q hpq
    induction hpq with
    | base hr => exact sb_mono T R _ (fun _ _ h => EqvClo.base h) _ _ hr
    | refl _ =>
      exact ⟨fun l p' hs => ⟨p', hs, EqvClo.refl _⟩, fun l q' hs => ⟨q', hs, EqvClo.refl _⟩⟩
    | symm _ ih =>
      exact ⟨fun l p' hs => let ⟨q', h1, h2⟩ := ih.2 l p' hs; ⟨q', h1, EqvClo.symm h2⟩,
             fun l q' hs => let ⟨p', h1, h2⟩ := ih.1 l q' hs; ⟨p', h1, EqvClo.symm h2⟩⟩
    | trans _ _ ih1 ih2 =>
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨r', h1, h2⟩ := ih1.1 l p' hs
        obtain ⟨q', h3, h4⟩ := ih2.1 l r' h1
        exact ⟨q', h3, EqvClo.trans h2 h4⟩
      · obtain ⟨r', h1, h2⟩ := ih2.2 l q' hs
        obtain ⟨p', h3, h4⟩ := ih1.2 l r' h1
        exact ⟨p', h3, EqvClo.trans h4 h2⟩

/-- `R ∪ ~` is sound for `sb` (corollary of compatibility). -/
theorem strong_upto_union_bisim_sound (T : LTS S L) : Sound (sb T) (unionBisim T) :=
  let h := strong_upto_union_bisim_compatible T
  sound_of_compatible_of_monotone_functional (sb_mono T) h.mono h.comm

/-- `~ R ~` is sound for `sb` (corollary of compatibility). -/
theorem strong_upto_bisim_both_sides_sound (T : LTS S L) : Sound (sb T) (strongUpTo T) :=
  let h := strong_upto_bisim_both_sides_compatible T
  sound_of_compatible_of_monotone_functional (sb_mono T) h.mono h.comm

/-- Equivalence closure is sound for `sb` (corollary of compatibility). -/
theorem strong_upto_equivalence_closure_sound (T : LTS S L) :
    Sound (sb T) (EqvClo (S := S)) :=
  let h := strong_upto_equivalence_closure_compatible T
  sound_of_compatible_of_monotone_functional (sb_mono T) h.mono h.comm

/-! ### Further compatible functions for `sb` (used as non-degenerate witnesses) -/

theorem reflClo_compatible_sb (T : LTS S L) : Compatible (sb T) reflClo := by
  refine ⟨fun _ _ h _ _ hpq => hpq.elim (fun hr => Or.inl (h _ _ hr)) Or.inr, ?_⟩
  intro R p q hpq
  rcases hpq with hr | rfl
  · exact sb_mono T R _ (fun _ _ h => Or.inl h) _ _ hr
  · exact ⟨fun l p' hs => ⟨p', hs, Or.inr rfl⟩, fun l q' hs => ⟨q', hs, Or.inr rfl⟩⟩

theorem symClo_compatible_sb (T : LTS S L) : Compatible (sb T) symClo := by
  refine ⟨fun _ _ h _ _ hpq =>
    hpq.elim (fun hr => Or.inl (h _ _ hr)) (fun hr => Or.inr (h _ _ hr)), ?_⟩
  intro R p q hpq
  rcases hpq with hr | hr
  · exact sb_mono T R _ (fun _ _ h => Or.inl h) _ _ hr
  · exact ⟨fun l p' hs => let ⟨q', h1, h2⟩ := hr.2 l p' hs; ⟨q', h1, Or.inr h2⟩,
           fun l q' hs => let ⟨p', h1, h2⟩ := hr.1 l q' hs; ⟨p', h1, Or.inr h2⟩⟩

theorem stepSq_compatible_sb (T : LTS S L) : Compatible (sb T) stepSq := by
  refine ⟨fun _ _ h _ _ hpq => hpq.elim (fun hr => Or.inl (h _ _ hr))
    (fun ⟨r, h1, h2⟩ => Or.inr ⟨r, h _ _ h1, h _ _ h2⟩), ?_⟩
  intro R p q hpq
  rcases hpq with hr | ⟨r, hpr, hrq⟩
  · exact sb_mono T R _ (fun _ _ h => Or.inl h) _ _ hr
  · refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨r', h1, h2⟩ := hpr.1 l p' hs
      obtain ⟨q', h3, h4⟩ := hrq.1 l r' h1
      exact ⟨q', h3, Or.inr ⟨r', h2, h4⟩⟩
    · obtain ⟨r', h1, h2⟩ := hrq.2 l q' hs
      obtain ⟨p', h3, h4⟩ := hpr.2 l r' h1
      exact ⟨p', h3, Or.inr ⟨r', h4, h2⟩⟩

end General

/-! ### Concrete processes and their (non-)bisimilarity -/

section Concrete

/-- `0 + 0 ~ 0` (over any label type). -/
theorem bisim_sum_nil_nil {L : Type v} : bisim (@PStep L) (.sum .nil .nil) .nil := by
  refine ⟨fun p q => p = .sum .nil .nil ∧ q = .nil, ?_, rfl, rfl⟩
  rintro p q ⟨rfl, rfl⟩
  exact sb_of_dead (PStep.sum_dead PStep.nil_dead PStep.nil_dead) PStep.nil_dead

/-- `a.0 ≁ a.a.0`. -/
theorem not_bisim_act_actact : ¬ bisim (@PStep Lbl) (act .a .nil) (act .a (act .a .nil)) := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨p', hs, hw'⟩ := (hW _ _ hw).2 (some .a) (act .a .nil) (PStep.pre _ _)
  obtain ⟨_, rfl⟩ := PStep.pre_inv hs
  obtain ⟨_, hs', _⟩ := (hW _ _ hw').2 (some .a) .nil (PStep.pre _ _)
  exact PStep.nil_dead _ _ hs'

/-- `a.0 ≁ τ.a.0`: strong bisimilarity distinguishes the silent step. -/
theorem not_bisim_act_tau : ¬ bisim (@PStep Lbl) (act .a .nil) (tau (act .a .nil)) := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨q', hs, _⟩ := (hW _ _ hw).1 (some .a) .nil (PStep.pre _ _)
  cases (PStep.pre_inv hs).1

/-! ### Definition examples -/

/-- `sb`/`bisim`, positive: `0 + 0 ~ 0`. -/
theorem bisim_example_pos : bisim (@PStep Lbl) (.sum .nil .nil) .nil := bisim_sum_nil_nil

/-- `sb`/`bisim`, negative: `a.0 ≁ τ.a.0`. -/
theorem bisim_example_neg : ¬ bisim (@PStep Lbl) (act .a .nil) (tau (act .a .nil)) :=
  not_bisim_act_tau

/-- `unionBisim`, positive: bisimilar pairs are added. -/
theorem unionBisim_example_pos : unionBisim (@PStep Lbl) botRel (.sum .nil .nil) .nil :=
  Or.inr bisim_sum_nil_nil

/-- `unionBisim`, negative: non-bisimilar pairs outside `R` are not added. -/
theorem unionBisim_example_neg :
    ¬ unionBisim (@PStep Lbl) botRel (act .a .nil) (act .a (act .a .nil)) := by
  rintro (h | h)
  · exact h
  · exact not_bisim_act_actact h

/-- `strongUpTo`, positive: `0 + 0 ~ 0 R 0 ~ 0` with `R = {(0, 0)}`. -/
theorem strongUpTo_example_pos :
    strongUpTo (@PStep Lbl) (fun p q => p = .nil ∧ q = .nil) (.sum .nil .nil) .nil :=
  ⟨.nil, .nil, bisim_sum_nil_nil, ⟨rfl, rfl⟩, bisim_refl _ _⟩

/-- `strongUpTo`, negative: with `R` empty nothing is related, not even
bisimilar pairs (`~ R ~` needs an `R`-pair in the middle). -/
theorem strongUpTo_example_neg : ¬ strongUpTo (@PStep Lbl) botRel .nil .nil :=
  fun ⟨_, _, _, h, _⟩ => h

/-- `EqvClo`, positive: the closure is symmetric. -/
theorem eqvClo_example_pos :
    EqvClo (fun p q => p = (.sum .nil .nil : Proc Lbl) ∧ q = .nil) .nil (.sum .nil .nil) :=
  EqvClo.symm (EqvClo.base ⟨rfl, rfl⟩)

theorem eqvClo_bot_eq {S : Type u} {p q : S} (h : EqvClo (botRel : Rel S) p q) : p = q := by
  induction h with
  | base h => exact h.elim
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- `EqvClo`, negative: the equivalence closure of the empty relation is the
identity, so it does not relate distinct states. -/
theorem eqvClo_example_neg : ¬ EqvClo (botRel : Rel (Proc Lbl)) (act .a .nil) .nil := by
  intro h
  cases eqvClo_bot_eq h

/-! ### Usefulness witnesses (non-vacuity) for the strong techniques

Each exhibits a relation that is *not* a strong bisimulation but progresses to
its image under the technique. -/

/-- `{(a.(0+0), a.0)}`. -/
def relU : Rel (Proc Lbl) := fun p q => p = act .a (.sum .nil .nil) ∧ q = act .a .nil

/-- `relU` is not a strong bisimulation but progresses to `relU ∪ ~`. -/
theorem strong_upto_union_bisim_useful :
    relU ⊑ sb PStep (unionBisim PStep relU) ∧ ¬ relU ⊑ sb PStep relU := by
  refine ⟨?_, ?_⟩
  · rintro p q ⟨rfl, rfl⟩
    refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.nil, PStep.pre _ _, Or.inr bisim_sum_nil_nil⟩
    · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
      exact ⟨.sum .nil .nil, PStep.pre _ _, Or.inr bisim_sum_nil_nil⟩
  · intro h
    obtain ⟨q', hs, ⟨hp, _⟩⟩ := (h _ _ ⟨rfl, rfl⟩).1 (some .a) (.sum .nil .nil) (PStep.pre _ _)
    cases hp

/-- `{(a.(0+0), a.0), (0, 0)}`. -/
def relS : Rel (Proc Lbl) := fun p q =>
  (p = act .a (.sum .nil .nil) ∧ q = act .a .nil) ∨ (p = .nil ∧ q = .nil)

/-- `relS` is not a strong bisimulation but progresses to `~ relS ~`. -/
theorem strong_upto_bisim_both_sides_useful :
    relS ⊑ sb PStep (strongUpTo PStep relS) ∧ ¬ relS ⊑ sb PStep relS := by
  refine ⟨?_, ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hmid : strongUpTo PStep relS (.sum .nil .nil) .nil :=
        ⟨.nil, .nil, bisim_sum_nil_nil, Or.inr ⟨rfl, rfl⟩, bisim_refl _ _⟩
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.nil, PStep.pre _ _, hmid⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.sum .nil .nil, PStep.pre _ _, hmid⟩
    · exact sb_of_dead PStep.nil_dead PStep.nil_dead
  · intro h
    obtain ⟨q', hs, hr⟩ := (h _ _ (Or.inl ⟨rfl, rfl⟩)).1 (some .a) (.sum .nil .nil) (PStep.pre _ _)
    rcases hr with ⟨hp, _⟩ | ⟨hp, _⟩ <;> cases hp

/-- `{(a.0, a.(0+0)), (0+0, 0)}`. -/
def relE : Rel (Proc Lbl) := fun p q =>
  (p = act .a .nil ∧ q = act .a (.sum .nil .nil)) ∨ (p = .sum .nil .nil ∧ q = .nil)

/-- `relE` is not a strong bisimulation but progresses to its equivalence
closure. -/
theorem strong_upto_equivalence_closure_useful :
    relE ⊑ sb PStep (EqvClo relE) ∧ ¬ relE ⊑ sb PStep relE := by
  refine ⟨?_, ?_⟩
  · rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hmid : EqvClo relE .nil (.sum .nil .nil) := EqvClo.symm (EqvClo.base (Or.inr ⟨rfl, rfl⟩))
      refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.sum .nil .nil, PStep.pre _ _, hmid⟩
      · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
        exact ⟨.nil, PStep.pre _ _, hmid⟩
    · exact sb_of_dead (PStep.sum_dead PStep.nil_dead PStep.nil_dead) PStep.nil_dead
  · intro h
    obtain ⟨q', hs, hr⟩ := (h _ _ (Or.inl ⟨rfl, rfl⟩)).1 (some .a) .nil (PStep.pre _ _)
    obtain ⟨_, rfl⟩ := PStep.pre_inv hs
    rcases hr with ⟨hp, _⟩ | ⟨hp, _⟩ <;> cases hp

/-! ### The "up to the total relation" counterexample

This is the tightness counterexample for the `Commutes` hypothesis of
`sound_of_compatible_of_monotone_functional`, on a genuine bisimulation
functional. -/

/-- `{(a.0, a.a.0)}`. -/
def relTop : Rel (Proc Lbl) := fun p q => p = act .a .nil ∧ q = act .a (act .a .nil)

/-- `relTop ⊑ sb (⊤)`: `a.0` and `a.a.0` have the same initial actions. -/
theorem relTop_progresses_top : Progresses (sb PStep) relTop topRel := by
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨act .a .nil, PStep.pre _ _, trivial⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, PStep.pre _ _, trivial⟩

/-- Dropping `Commutes b f`: "strong bisimulation up to the total relation"
has a monotone functional and a monotone up-to function, but is unsound
(`{(a.0, a.a.0)}` progresses to `⊤` while `a.0 ≁ a.a.0`). -/
theorem sound_counterexample_noncommuting :
    MonoRel (sb (@PStep Lbl)) ∧ MonoRel (fun _ : Rel (Proc Lbl) => (topRel : Rel (Proc Lbl))) ∧
    ¬ Sound (sb (@PStep Lbl)) (fun _ => topRel) := by
  refine ⟨sb_mono _, fun _ _ _ => Incl.refl _, ?_⟩
  intro hs
  exact not_bisim_act_actact (hs relTop relTop_progresses_top _ _ ⟨rfl, rfl⟩)

/-- `Sound`, negative example on a bisimulation functional: up to the total
relation is unsound for `sb`. -/
theorem sound_example_neg_sb : ¬ Sound (sb (@PStep Lbl)) (fun _ => topRel) :=
  sound_counterexample_noncommuting.2.2

/-- `Commutes`, negative example on a bisimulation functional. -/
theorem commutes_example_neg_sb : ¬ Commutes (sb (@PStep Lbl)) (fun _ => topRel) := by
  intro h
  -- `sb ⊤` is not total: it does not relate `a.0` and `0`.
  obtain ⟨q', hs, _⟩ := (h botRel (act .a .nil) .nil trivial).1 (some .a) .nil (PStep.pre _ _)
  exact PStep.nil_dead _ _ hs

/-! ### Non-vacuity of the abstract results on the strong functional

Each witness satisfies all hypotheses of its theorem with genuinely
non-degenerate up-to functions, and exhibits a relation that is not a
post-fixpoint of `b` yet progresses to its image, so the technique does real
work. -/

/-- Non-vacuity of `sound_of_compatible_of_monotone_functional`: the strong
bisimulation functional with the up-to function "constantly `~`"; the relation
`relU` is not a strong bisimulation but progresses to `constGfp (sb PStep) relU`. -/
theorem sound_of_compatible_nonvacuity :
    MonoRel (sb (@PStep Lbl)) ∧ MonoRel (constGfp (sb (@PStep Lbl))) ∧
    Commutes (sb (@PStep Lbl)) (constGfp (sb PStep)) ∧
    Progresses (sb PStep) relU (constGfp (sb PStep) relU) ∧ ¬ relU ⊑ sb PStep relU := by
  refine ⟨sb_mono _, (compatible_constGfp (sb_mono _)).mono, (compatible_constGfp (sb_mono _)).comm,
    ?_, strong_upto_union_bisim_useful.2⟩
  rintro p q ⟨rfl, rfl⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, PStep.pre _ _, bisim_sum_nil_nil⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.sum .nil .nil, PStep.pre _ _, bisim_sum_nil_nil⟩

/-- Non-vacuity of `compatible_comp`: `f = symClo` and `g = reflClo` on `sb`.
Neither is constant or the identity, and the composite differs from each
component (`(0, 0)` and `(a.0, a.(0+0))` are in `symClo (reflClo relU)`, but
the first is not in `symClo relU` and the second is not in `reflClo relU`). -/
theorem compatible_comp_nonvacuity :
    MonoRel (symClo (S := Proc Lbl)) ∧ MonoRel (reflClo (S := Proc Lbl)) ∧
    Commutes (sb (@PStep Lbl)) symClo ∧ Commutes (sb (@PStep Lbl)) reflClo ∧
    comp symClo reflClo relU .nil .nil ∧ ¬ symClo relU .nil .nil ∧
    comp symClo reflClo relU (act .a .nil) (act .a (.sum .nil .nil)) ∧
    ¬ reflClo relU (act .a .nil) (act .a (.sum .nil .nil)) := by
  refine ⟨(symClo_compatible_sb PStep).mono, (reflClo_compatible_sb PStep).mono,
    (symClo_compatible_sb PStep).comm, (reflClo_compatible_sb PStep).comm,
    Or.inl (Or.inr rfl), ?_, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> cases h
  · rintro (⟨h, _⟩ | h) <;> cases h

/-- The family `{id, const ~}`; its union is `R ↦ R ∪ ~`. -/
def idOrBisim : Bool → Rel (Proc Lbl) → Rel (Proc Lbl) :=
  fun i => if i then (fun R => R) else constGfp (sb PStep)

/-- Non-vacuity of `compatible_iSup_of_monotone_functional`: the family
`{id, const ~}` on `sb`. -/
theorem compatible_iSup_nonvacuity :
    MonoRel (sb (@PStep Lbl)) ∧ (∀ i, MonoRel (idOrBisim i)) ∧
    (∀ i, Commutes (sb (@PStep Lbl)) (idOrBisim i)) := by
  refine ⟨sb_mono _, fun i => ?_, fun i => ?_⟩
  · cases i
    · exact (compatible_constGfp (sb_mono _)).mono
    · exact monoRel_id
  · cases i
    · exact (compatible_constGfp (sb_mono _)).comm
    · exact commutes_id _

/-- The three-edge chain `0 → 1 → 2 → 3` on `Fin 4`. -/
def chain4 : Rel (Fin 4) :=
  fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3)

/-- Iterating `stepSq` really iterates: `(0, 3)` is in `stepSq² chain4` but
not in `stepSq⁰ chain4` or `stepSq¹ chain4`. -/
theorem iter_stepSq_chain4 :
    ¬ iter stepSq 0 chain4 0 3 ∧ ¬ iter stepSq 1 chain4 0 3 ∧ iter stepSq 2 chain4 0 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> revert h <;> decide
  · rintro (h03 | ⟨r, hr1, hr2⟩)
    · rcases h03 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> revert h <;> decide
    · rcases hr1 with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · rcases hr2 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> revert h <;> decide
      · revert h; decide
      · revert h; decide
  · exact Or.inr ⟨2, Or.inr ⟨1, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩,
      Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- Non-vacuity of `compatible_omega_of_monotone_functional`: `f = stepSq`
(`R ↦ R ∪ R;R`) on `sb`, whose iterates grow strictly (`iter_stepSq_chain4`). -/
theorem compatible_omega_nonvacuity :
    MonoRel (sb (@PStep Lbl)) ∧ MonoRel (stepSq (S := Proc Lbl)) ∧
    Commutes (sb (@PStep Lbl)) stepSq ∧
    (¬ iter stepSq 1 chain4 0 3 ∧ iter stepSq 2 chain4 0 3) :=
  ⟨sb_mono _, (stepSq_compatible_sb PStep).mono, (stepSq_compatible_sb PStep).comm,
    iter_stepSq_chain4.2.1, iter_stepSq_chain4.2.2⟩

/-! ### Non-degenerate definition examples on the strong functional -/

/-- `Progresses`, positive example with live transitions: `{(a.0, a.a.0)}`
progresses to the total relation under `sb`. -/
theorem progresses_example_pos_live : Progresses (sb PStep) relTop topRel :=
  relTop_progresses_top

/-- `Commutes`, positive example with a non-identity functional. -/
theorem commutes_example_pos_live : Commutes (sb (@PStep Lbl)) (constGfp (sb PStep)) :=
  (compatible_constGfp (sb_mono _)).comm

/-- `Compatible`, positive example with a non-identity functional. -/
theorem compatible_example_pos_live : Compatible (sb (@PStep Lbl)) (constGfp (sb PStep)) :=
  compatible_constGfp (sb_mono _)

/-- `Sound`, positive example with a non-identity functional and a monotone
`b` whose greatest fixpoint is non-trivial. -/
theorem sound_example_pos_live : Sound (sb (@PStep Lbl)) (strongUpTo PStep) :=
  strong_upto_bisim_both_sides_sound _

/-- `omega`, positive example where the union needs a non-zero iterate. -/
theorem omega_example_pos_live : omega stepSq chain4 0 3 ∧ ¬ iter stepSq 1 chain4 0 3 :=
  ⟨⟨2, iter_stepSq_chain4.2.2⟩, iter_stepSq_chain4.2.1⟩

end Concrete

end Toy.UpTo
