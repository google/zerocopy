import ToyUpTo.Context

/-!
# The companion

The companion of a functional `b` is the pointwise union of all
`b`-compatible functions (Pous).  It contains every compatible function by
construction; for monotone `b` it is itself compatible, hence sound.
-/

namespace Toy.UpTo

open Proc

universe u

section General

variable {S : Type u}

/-- The companion of `b`: `companion b R` relates `p` and `q` when some
monotone `f` commuting with `b` has `f R p q`. -/
def companion (b : Rel S → Rel S) : Rel S → Rel S :=
  fun R p q => ∃ f : Rel S → Rel S, MonoRel f ∧ Commutes b f ∧ f R p q

/-- Every compatible function is below the companion (definitional). -/
theorem companion_greatest {b f : Rel S → Rel S} (hf : MonoRel f) (hc : Commutes b f)
    (R : Rel S) : f R ⊑ companion b R :=
  fun _ _ h => ⟨f, hf, hc, h⟩

/-- Each compatible function maps `∅` to a post-fixpoint of `b`, hence so
does the companion: `companion b ∅ ⊑ gfp b` (no monotonicity of `b` needed). -/
theorem companion_bot_incl_gfp {b : Rel S → Rel S} :
    companion b botRel ⊑ gfp b := by
  intro p q ⟨f, hf, hc, h⟩
  refine ⟨f botRel, fun x y hxy => ?_, h⟩
  exact hc botRel x y (hf botRel (b botRel) (botRel_incl _) x y hxy)

/-- Every post-fixpoint of `b`, and hence `gfp b`, is below the companion
applied to any relation (no monotonicity of `b` needed): a post-fixpoint
`R₀ ⊑ b R₀` makes the constant function `fun _ => R₀` compatible. -/
theorem gfp_incl_companion {b : Rel S → Rel S} (R : Rel S) : gfp b ⊑ companion b R :=
  fun _ _ ⟨R₀, h0, h⟩ => ⟨fun _ => R₀, fun _ _ _ => Incl.refl _, fun _ => h0, h⟩

/-- `companion b ∅` and `gfp b` coincide (both inclusions; no monotonicity
of `b` needed). -/
theorem companion_bot_eq_gfp {b : Rel S → Rel S} :
    companion b botRel ⊑ gfp b ∧ gfp b ⊑ companion b botRel :=
  ⟨companion_bot_incl_gfp, gfp_incl_companion botRel⟩

/-! ### Main result -/

/-- **The companion is compatible and sound** for every monotone functional
`b`. -/
theorem companion_compatible_and_sound_of_monotone_functional {b : Rel S → Rel S}
    (hb : MonoRel b) : Compatible b (companion b) ∧ Sound b (companion b) := by
  have hc : Compatible b (companion b) :=
    ⟨fun R R' h p q ⟨f, hf, hc, hfr⟩ => ⟨f, hf, hc, hf R R' h p q hfr⟩,
     fun R p q ⟨f, hf, hc, hfr⟩ => hb _ _ (companion_greatest hf hc R) p q (hc R p q hfr)⟩
  exact ⟨hc, sound_of_compatible_of_monotone_functional hb hc.mono hc.comm⟩

end General

/-! ### Examples, tightness and non-vacuity (fully proved) -/

/-- `companion`, positive: the companion contains the identity. -/
theorem companion_example_pos (R : Rel (Proc Lbl)) : R ⊑ companion (sb PStep) R :=
  companion_greatest monoRel_id (commutes_id _) R

theorem not_bisim_act_nil : ¬ bisim (@PStep Lbl) (act .a .nil) .nil := by
  rintro ⟨W, hW, hw⟩
  obtain ⟨_, hs, _⟩ := (hW _ _ hw).1 (some .a) .nil (PStep.pre _ _)
  exact PStep.nil_dead _ _ hs

/-- `companion`, negative: `companion sb ∅` does not relate `a.0` and `0`
(it is contained in strong bisimilarity). -/
theorem companion_example_neg : ¬ companion (sb (@PStep Lbl)) botRel (act .a .nil) .nil :=
  fun h => not_bisim_act_nil (companion_bot_incl_gfp _ _ h)

/-- Dropping `MonoRel b` (there are no other hypotheses): for the
non-monotone `swapB`, the companion is neither compatible nor sound.  Both
`id` and `const {(true,true)}` are compatible with `swapB`, so the companion of
`{(false,false)}` contains both pairs; then `{(false,false)}` progresses to its
companion image although `(false,false) ∉ gfp swapB`. -/
theorem companion_counterexample_nonmonotone_functional :
    ¬ Compatible swapB (companion swapB) ∧ ¬ Sound swapB (companion swapB) := by
  refine ⟨?_, ?_⟩
  · intro hcompat
    have hlhs : companion swapB (swapB topRel) true true :=
      ⟨fun _ => relY, fun _ _ _ => Incl.refl _, const_relY_commutes_swapB, ⟨rfl, rfl⟩⟩
    have hrhs : swapB (companion swapB topRel) true true := hcompat.comm topRel true true hlhs
    have hff : companion swapB topRel false false :=
      ⟨fun R => R, monoRel_id, commutes_id swapB, trivial⟩
    rcases hrhs.2 with ⟨_, htf, _⟩ | ⟨hnff, _, _⟩
    · exact Bool.noConfusion htf
    · exact hnff hff
  · intro hsound
    have hprog : Progresses swapB relX (companion swapB relX) := by
      rintro p q ⟨rfl, rfl⟩
      have hff : companion swapB relX false false :=
        ⟨fun R => R, monoRel_id, commutes_id swapB, ⟨rfl, rfl⟩⟩
      have htt : companion swapB relX true true :=
        ⟨fun _ => relY, fun _ _ _ => Incl.refl _, const_relY_commutes_swapB, ⟨rfl, rfl⟩⟩
      exact ⟨htt, Or.inl ⟨hff, rfl, rfl⟩⟩
    exact not_gfp_swapB_ff (hsound relX hprog false false ⟨rfl, rfl⟩)

/-- For the non-monotone `killB` the companion is not compatible, but it *is*
sound (`killB` empties every relation containing both `(false,false)` and
`(true,true)`, and the companion of any relation contains both).  So `killB`
only shows that compatibility of the companion needs `MonoRel b`; `swapB`
shows the same for soundness. -/
theorem killB_companion_not_compatible_but_sound :
    ¬ Compatible killB (companion killB) ∧ Sound killB (companion killB) := by
  have hX : ∀ R, companion killB R false false :=
    fun _ => ⟨fun _ => relX, fun _ _ _ => Incl.refl _, xyFamily_commutes true, ⟨rfl, rfl⟩⟩
  have hY : ∀ R, companion killB R true true :=
    fun _ => ⟨fun _ => relY, fun _ _ _ => Incl.refl _, xyFamily_commutes false, ⟨rfl, rfl⟩⟩
  refine ⟨fun h => (h.comm botRel false false (hX _)).2 ⟨hX _, hY _⟩, ?_⟩
  intro R hprog p q hr
  exact False.elim ((hprog p q hr).2 ⟨hX R, hY R⟩)

/-- Non-vacuity of `companion_compatible_and_sound_of_monotone_functional`:
the strong bisimulation functional is monotone, and the companion does real
work: `relU` is not a strong bisimulation but progresses to its companion
image. -/
theorem companion_nonvacuity :
    MonoRel (sb (@PStep Lbl)) ∧ Progresses (sb PStep) relU (companion (sb PStep) relU) ∧
    ¬ relU ⊑ sb PStep relU := by
  refine ⟨sb_mono _, ?_, strong_upto_union_bisim_useful.2⟩
  rintro p q ⟨rfl, rfl⟩
  have hc := compatible_constGfp (sb_mono (@PStep Lbl))
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.nil, PStep.pre _ _, companion_greatest hc.mono hc.comm relU _ _ bisim_sum_nil_nil⟩
  · obtain ⟨rfl, rfl⟩ := PStep.pre_inv hs
    exact ⟨.sum .nil .nil, PStep.pre _ _,
      companion_greatest hc.mono hc.comm relU _ _ bisim_sum_nil_nil⟩

/-- **The companion is not monotone in the functional.**  Although
`sb PStep R ⊑ wb PStep R` for every `R`, the companion of `sb` is not below
the companion of `wb`: `SumClo` is below the former (it is `sb`-compatible)
but not below the latter (it is unsound for `wb`, while the companion of `wb`
is sound). -/
theorem companion_not_monotone_in_functional :
    (∀ R, sb (@PStep Lbl) R ⊑ wb PStep R) ∧
    ¬ (∀ R, companion (sb (@PStep Lbl)) R ⊑ companion (wb PStep) R) := by
  refine ⟨sb_incl_wb PStep, fun h => weak_upto_sum_context_not_sound ?_⟩
  intro R hR
  have hc := @strong_upto_sum_context_compatible Lbl
  have hsub : SumClo R ⊑ companion (wb PStep) R :=
    Incl.trans (companion_greatest hc.mono hc.comm R) (h R)
  exact (companion_compatible_and_sound_of_monotone_functional (wb_mono PStep)).2 R
    (Incl.trans hR (wb_mono PStep _ _ hsub))

end Toy.UpTo
