import Toy.Sep.Basic

/-!
# Locality and the frame rule

All results in this module hold in an arbitrary `SepStruct`: **no algebraic
laws** (commutativity, associativity, unit, cancellativity) are assumed.
Assertions range over *all* predicates on states.
-/

namespace Toy.Sep

open SepStruct

variable {S : Type u} [SepStruct S]

/-- **Locality implies the frame rule.** If `c` is safety-monotone and has the
frame property, then every fault-avoiding triple `{P} c {Q}` can be framed:
`{P * R} c {Q * R}` for every assertion `R`. No algebraic laws on the separation
structure are needed. -/
theorem frame_rule_of_safetyMono_of_frameProp {c : Cmd S}
    (hsm : SafetyMono c) (hfp : FrameProp c) {P Q R : Assn S}
    (ht : Triple P c Q) : Triple (sep P R) c (sep Q R) := by
  rintro h ⟨h₁, h₂, hd, rfl, hP, hR⟩
  obtain ⟨hs₁, hpost₁⟩ := ht h₁ hP
  refine ⟨hsm h₁ h₂ hd hs₁, fun h'' hrun => ?_⟩
  obtain ⟨h₀, hrun₀, hd₀, rfl⟩ := hfp h₁ h₂ h'' hd hs₁ hrun
  exact ⟨h₀, h₂, hd₀, rfl, hpost₁ h₀ hrun₀, hR⟩

/-- **The frame rule at singleton instances implies locality.** If, for every
pair of states `h, h'`, the frame rule holds for the instance with precondition
`{h}`, postcondition `post c h` (the strongest postcondition of `c` from `h`) and
frame `{h'}`, then `c` is safety-monotone and has the frame property. No
algebraic laws on the separation structure are needed. -/
theorem safetyMono_and_frameProp_of_frameRuleAtSingletons {c : Cmd S}
    (H : FrameRuleAtSingletons c) : SafetyMono c ∧ FrameProp c := by
  have hstep : ∀ {h h' : S}, disj h h' → Safe c h →
      Triple (sep (sing h) (sing h')) c (sep (post c h) (sing h')) := fun {h h'} _ hs =>
    H h h' (fun x hx => by have hx' : x = h := hx; subst hx'; exact ⟨hs, fun _ hr => hr⟩)
  refine ⟨fun h h' hd hs => (hstep hd hs (union h h') ⟨h, h', hd, rfl, rfl, rfl⟩).1,
    fun h h' h'' hd hs hrun => ?_⟩
  obtain ⟨h₀, x, hd₀, heq, hrun₀, hx⟩ :=
    (hstep hd hs (union h h') ⟨h, h', hd, rfl, rfl, rfl⟩).2 h'' hrun
  have hx' : x = h' := hx
  subst hx'
  exact ⟨h₀, hrun₀, hd₀, heq⟩

/-- **Characterization.** For every command `c` in every separation structure,
the frame rule is sound for `c` (for all assertions `P Q R`) iff `c` is
safety-monotone and has the frame property. -/
theorem frameRuleSound_iff_safetyMono_and_frameProp (c : Cmd S) :
    FrameRuleSound c ↔ SafetyMono c ∧ FrameProp c :=
  ⟨fun H => safetyMono_and_frameProp_of_frameRuleAtSingletons
      (fun h h' ht => H (sing h) (post c h) (sing h') ht),
   fun ⟨hsm, hfp⟩ _ _ _ ht => frame_rule_of_safetyMono_of_frameProp hsm hfp ht⟩

/-- **The frame rule for precise frames already forces locality.** If the frame
rule holds for `c` for all `P`, `Q` and all *precise* frames `R`, then `c` is
safety-monotone and has the frame property. (Restricting a logic's frame rule to
precise frames does not admit any additional non-local commands.) -/
theorem safetyMono_and_frameProp_of_frameRuleForPreciseFrames {c : Cmd S}
    (H : FrameRuleForPreciseFrames c) : SafetyMono c ∧ FrameProp c :=
  safetyMono_and_frameProp_of_frameRuleAtSingletons
    (fun h h' ht => H (sing h) (post c h) (sing h')
      (fun _ r₁ _ r₂ _ _ _ h1 h2 => (h1 : r₁ = h').trans (h2 : r₂ = h').symm) ht)

end Toy.Sep
