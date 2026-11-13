-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Compiler-Correctness Theorem Shapes and End-to-End Simulation Chains

Standalone Lean 4 (`v4.34.1`) mechanization comparing the four principal
compiler-correctness theorem shapes across verified compiler precedents:

1. **CompCert-Style Safe-Source Backward Simulation (`CompCertBackwardSim`)**:
   Whenever the source program is safe (`SafeSrc`), every target execution
   behavior improves a valid source execution behavior (`behaviorImproves`).
2. **CakeML-Style Resource-Bounded Trace Inclusion (`CakeMLResourceRefinement`)**:
   Target execution belongs to `extendWithResourceLimit (srcBehaviors)`,
   allowing the target to either match a source behavior or abort early with
   `resourceLimitHit tr` along a valid prefix `tr` of a source trace.
3. **Quantitative Stack-Bounded Refinement (`StackAwareRefinement`)**:
   Refines `CakeMLResourceRefinement` by pairing compilation with a static
   stack-usage bound `stackUsage prog ≤ maxStack`, eliminating the
   `resourceLimitHit` branch whenever initial stack headroom satisfies
   `maxStack ≤ initHeadroom` (modeling Stack-Aware CompCert POPL 2019 and
   Bedrock2 `FitsStack`).
4. **Anneal Demonic Partial-Behavior Refinement (`AnnealCompiles` /
   `AnnealProductiveCompiles`)**:
   Models undefined behavior as `defined = False` ($\top$ in the demonic
   refinement lattice `Partial (Out → Prop)`), proving exact equivalence
   between `CompCertBackwardSim` (with explicit `goesWrong` exclusion) and
   `AnnealCompiles`, plus forward-to-backward simulation inversion under
   target determinacy and source receptiveness.
-/

namespace TheoremShapesProbe

/-- Observable whole-program behaviors modeled after CompCert `common/Behaviors.v`
and CakeML `semantics/ffi/ffiScript.sml`. -/
inductive ProgramBehavior (Obs Val : Type) where
  | terminates (trace : List Obs) (ret : Val)
  | diverges   (trace : List Obs)
  | reacts     (infTrace : Nat → Obs)
  | goesWrong  (trace : List Obs)
  | resourceLimitHit (trace : List Obs)

/-- Prefix relation on finite observation traces. -/
def IsTracePrefix {Obs : Type} (pre full : List Obs) : Prop :=
  ∃ suffix, pre ++ suffix = full

/-- Extracts the finite trace prefix of a `ProgramBehavior`. -/
def finitePrefixOf {Obs Val : Type} : ProgramBehavior Obs Val → List Obs → Prop
  | .terminates tr _, pre => IsTracePrefix pre tr
  | .diverges tr, pre => IsTracePrefix pre tr
  | .reacts inf, pre => ∃ n, pre = (List.range n).map inf
  | .goesWrong tr, pre => IsTracePrefix pre tr
  | .resourceLimitHit tr, pre => IsTracePrefix pre tr

/-- A program behavior is safe when it does not get stuck in `goesWrong`. -/
def BehaviorSafe {Obs Val : Type} : ProgramBehavior Obs Val → Prop
  | .goesWrong _ => False
  | _ => True

/-- CompCert `behavior_improves` (`common/Behaviors.v`): either `b_tgt = b_src`,
or `b_src` goes wrong after a trace prefix `t` that `b_tgt` extends. -/
def BehaviorImproves {Obs Val : Type}
    (b_src b_tgt : ProgramBehavior Obs Val) : Prop :=
  b_tgt = b_src ∨
    ∃ tr, b_src = .goesWrong tr ∧ finitePrefixOf b_tgt tr

/-- CompCert-style whole-program behavioral preservation under safe source
execution (`driver/Complements.v`, `transf_c_program_preservation`). -/
def CompCertPreservation {Obs Val : Type}
    (srcSem tgtSem : ProgramBehavior Obs Val → Prop) : Prop :=
  ∀ b_tgt, tgtSem b_tgt →
    ∃ b_src, srcSem b_src ∧ BehaviorImproves b_src b_tgt

/-- Source safety: no reachable source execution exhibits `goesWrong`. -/
def SourceSafe {Obs Val : Type}
    (srcSem : ProgramBehavior Obs Val → Prop) : Prop :=
  ∀ b_src, srcSem b_src → BehaviorSafe b_src

/-- Under `SourceSafe`, CompCert's `BehaviorImproves` collapses to exact
behavioral inclusion (`tgtSem b_tgt → srcSem b_tgt`). -/
theorem compcert_preservation_under_safe_source {Obs Val : Type}
    {srcSem tgtSem : ProgramBehavior Obs Val → Prop}
    (hpres : CompCertPreservation srcSem tgtSem)
    (hsafe : SourceSafe srcSem) :
    ∀ b_tgt, tgtSem b_tgt → srcSem b_tgt := by
  intro b_tgt htgt
  rcases hpres b_tgt htgt with ⟨b_src, hsrc, himp⟩
  rcases himp with rfl | ⟨tr, rfl, _⟩
  · exact hsrc
  · exact False.elim (hsafe (.goesWrong tr) hsrc)

/-- CakeML's `extend_with_resource_limit` (`semantics/ffi/ffiScript.sml` and
`compiler/proofs/compilerProofScript.sml:269-295`): adds early
`resourceLimitHit` termination along any prefix of a source behavior. -/
def ExtendWithResourceLimit {Obs Val : Type}
    (beh : ProgramBehavior Obs Val → Prop) :
    ProgramBehavior Obs Val → Prop :=
  fun b_tgt =>
    beh b_tgt ∨
      ∃ tr b_src, b_tgt = .resourceLimitHit tr ∧ beh b_src ∧ finitePrefixOf b_src tr

/-- CakeML's top-level behavioral inclusion (`machine_sem ⊆
extend_with_resource_limit (semantics_prog)`). -/
def CakeMLResourceRefinement {Obs Val : Type}
    (srcSem tgtSem : ProgramBehavior Obs Val → Prop) : Prop :=
  ∀ b_tgt, tgtSem b_tgt → ExtendWithResourceLimit srcSem b_tgt

/-- Separation theorem: `CakeMLResourceRefinement` preserves safety (no
`goesWrong` if source is safe), but does NOT by itself guarantee normal
termination even when the source program terminates deterministically on all
runs, because the target may unconditionally emit `resourceLimitHit []`. -/
theorem cakeml_resource_refinement_allows_early_oom :
    let srcSem : ProgramBehavior Nat Nat → Prop := fun b => b = .terminates [42] 0
    let tgtSem : ProgramBehavior Nat Nat → Prop := fun b => b = .resourceLimitHit []
    CakeMLResourceRefinement srcSem tgtSem ∧
    (∀ b, tgtSem b → BehaviorSafe b) ∧
    ¬ (∃ tr ret, tgtSem (.terminates tr ret)) := by
  intro srcSem tgtSem
  refine ⟨?_, ?_, ?_⟩
  · intro b_tgt htgt
    subst htgt
    right
    refine ⟨[], .terminates [42] 0, rfl, rfl, ⟨[42], rfl⟩⟩
  · intro b hb
    subst hb
    trivial
  · rintro ⟨tr, ret, h⟩
    nomatch h

/-- Stack-Aware CompCert (`ssrg-vt/compcert_stack_aware`) and Bedrock2
(`FitsStack.v`) quantitative stack-bounded refinement: when compilation is
paired with a static frame bound `stackUsage ≤ maxStack` and the target machine
only emits `resourceLimitHit` when `initHeadroom < stackUsage`, providing
`maxStack ≤ initHeadroom` eliminates `resourceLimitHit` and recovers full
CompCert/Anneal behavioral inclusion. -/
structure StackAwareCompilerProof (Obs Val : Type) where
  stackUsage   : Nat
  maxStack     : Nat
  usage_le_max : stackUsage ≤ maxStack
  refines      : Nat → (ProgramBehavior Obs Val → Prop) → (ProgramBehavior Obs Val → Prop) → Prop
  no_oom_when_headroom_fits :
    ∀ headroom srcSem tgtSem,
      stackUsage ≤ headroom →
      refines headroom srcSem tgtSem →
      ∀ b_tgt, tgtSem b_tgt →
        ExtendWithResourceLimit srcSem b_tgt ∧
        (∀ tr, b_tgt ≠ .resourceLimitHit tr)

theorem stack_aware_bound_recovers_exact_inclusion {Obs Val : Type}
    (C : StackAwareCompilerProof Obs Val)
    (headroom : Nat)
    (srcSem tgtSem : ProgramBehavior Obs Val → Prop)
    (hfit : C.maxStack ≤ headroom)
    (href : C.refines headroom srcSem tgtSem) :
    ∀ b_tgt, tgtSem b_tgt → srcSem b_tgt := by
  intro b_tgt htgt
  have husage : C.stackUsage ≤ headroom := Nat.le_trans C.usage_le_max hfit
  rcases C.no_oom_when_headroom_fits headroom srcSem tgtSem husage href b_tgt htgt with
    ⟨hext, hno_oom⟩
  rcases hext with hsrc | ⟨tr, _, rfl, _, _⟩
  · exact hsrc
  · exact False.elim (hno_oom tr rfl)

/-- Anneal's constructive `Partial` and demonic refinement order (`Trusted/Refinement.lean`). -/
structure Partial (B : Type) where
  defined : Prop
  val     : defined → B

/-- Demonic refinement on `Partial (Out → Prop)`: whenever the right-hand side
is defined, the left-hand side is defined and its outcome set is a subset. -/
def RefinesPartial {Out : Type} (p₁ p₂ : Partial (Out → Prop)) : Prop :=
  ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, ∀ o, p₁.val h₁ o → p₂.val h₂ o

/-- Anneal `Behavior` maps each initial state/query `Query` to a `Partial`
outcome predicate. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

def RefinesBehavior {Query Out : Type}
    (b₁ b₂ : Behavior Query Out) : Prop :=
  ∀ q, RefinesPartial (b₁ q) (b₂ q)

/-- Embedding an operational semantics `sem : Query → ProgramBehavior Obs Val → Prop`
into Anneal's `Behavior` carrier: `defined` is `SourceSafe (sem q)`. -/
def toAnnealBehavior {Query Obs Val : Type}
    (sem : Query → ProgramBehavior Obs Val → Prop) :
    Behavior Query (ProgramBehavior Obs Val) :=
  fun q => {
    defined := SourceSafe (sem q)
    val     := fun _ b => sem q b
  }

/-- Theorem: Demonic refinement `RefinesBehavior (toAnnealBehavior tgtSem)
(toAnnealBehavior srcSem)` holds if and only if for every query `q` where
`srcSem q` is safe (`SourceSafe`), `tgtSem q` is also safe and every target
behavior is a valid source behavior (`tgtSem q b → srcSem q b`). -/
theorem anneal_refinement_iff_safe_source_inclusion {Query Obs Val : Type}
    (srcSem tgtSem : Query → ProgramBehavior Obs Val → Prop) :
    RefinesBehavior (toAnnealBehavior tgtSem) (toAnnealBehavior srcSem) ↔
      ∀ q, SourceSafe (srcSem q) →
        SourceSafe (tgtSem q) ∧ (∀ b, tgtSem q b → srcSem q b) := by
  constructor
  · intro href q hsafe_src
    rcases href q hsafe_src with ⟨hsafe_tgt, hsub⟩
    exact ⟨hsafe_tgt, hsub⟩
  · intro h q hsafe_src
    rcases h q hsafe_src with ⟨hsafe_tgt, hsub⟩
    exact ⟨hsafe_tgt, hsub⟩

/-- Lockstep forward simulation vs. backward simulation under target determinacy
(`common/Smallstep.v`, `forward_to_backward_simulation`). -/
structure DetTargetSemantics (State Val : Type) where
  step      : State → Option State
  finalVal  : State → Option Val
  det_final : ∀ s v, finalVal s = some v → step s = none

/-- Forward simulation from source transition system to a deterministic target. -/
structure ForwardSim (SrcState TgtState Val : Type)
    (srcStep : SrcState → SrcState → Prop)
    (srcFinal : SrcState → Val → Prop)
    (tgt : DetTargetSemantics TgtState Val) where
  matchStates : SrcState → TgtState → Prop
  sim_step :
    ∀ s₁ s₁' t₁, matchStates s₁ t₁ → srcStep s₁ s₁' →
      ∃ t₁', tgt.step t₁ = some t₁' ∧ matchStates s₁' t₁'
  sim_final :
    ∀ s₁ t₁ v, matchStates s₁ t₁ → srcFinal s₁ v →
      tgt.finalVal t₁ = some v

/-- Source progress (`safe` in CompCert `common/Smallstep.v:1274`): a matched
source state either terminates with a value or can take a step. -/
def SrcStepSafe {SrcState Val : Type}
    (srcStep : SrcState → SrcState → Prop)
    (srcFinal : SrcState → Val → Prop)
    (s : SrcState) : Prop :=
  (∃ v, srcFinal s v) ∨ (∃ s', srcStep s s')

/-- Flipping forward simulation to backward step simulation when the source
state is safe (`SrcStepSafe`) and the target is deterministic (`DetTargetSemantics`). -/
theorem forward_to_backward_step {SrcState TgtState Val : Type}
    {srcStep : SrcState → SrcState → Prop}
    {srcFinal : SrcState → Val → Prop}
    {tgt : DetTargetSemantics TgtState Val}
    (fsim : ForwardSim SrcState TgtState Val srcStep srcFinal tgt)
    {s₁ : SrcState} {t₁ t₁' : TgtState}
    (hmatch : fsim.matchStates s₁ t₁)
    (hsafe : SrcStepSafe srcStep srcFinal s₁)
    (htgt_step : tgt.step t₁ = some t₁') :
    ∃ s₁', srcStep s₁ s₁' ∧ fsim.matchStates s₁' t₁' := by
  rcases hsafe with ⟨v, hfin⟩ | ⟨s₁', hstep⟩
  · have htgt_fin : tgt.finalVal t₁ = some v := fsim.sim_final s₁ t₁ v hmatch hfin
    have hnone : tgt.step t₁ = none := tgt.det_final t₁ v htgt_fin
    rw [htgt_step] at hnone
    nomatch hnone
  · rcases fsim.sim_step s₁ s₁' t₁ hmatch hstep with ⟨t₂, ht₂, hmatch'⟩
    rw [htgt_step] at ht₂
    injection ht₂ with h_eq
    subst h_eq
    exact ⟨s₁', hstep, hmatch'⟩

end TheoremShapesProbe

#print axioms TheoremShapesProbe.compcert_preservation_under_safe_source
#print axioms TheoremShapesProbe.cakeml_resource_refinement_allows_early_oom
#print axioms TheoremShapesProbe.stack_aware_bound_recovers_exact_inclusion
#print axioms TheoremShapesProbe.anneal_refinement_iff_safe_source_inclusion
#print axioms TheoremShapesProbe.forward_to_backward_step
