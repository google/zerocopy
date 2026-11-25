-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Trusted.MirAst
public import Trusted.MirModel

public section

/-!
# Active-Mask `Uninit`-Padding Independence & Stencil Framing (`Stencil`)

Zero-TCB laws for universal demonic padding independence on SIMD row tails,
four-zone overlapping in-place stencil framing (`.readOnly`, `.readWrite`,
`.writeOnly`, `.frame`), and monotone causal wavefront prefix transfer (such as
AV1 IntraBC / raster superblock sweeps) over `Trusted.MirSemantics.AllocByte`:

1. **Universal Demonic `Uninit`-Padding Independence (`[]` zero axioms):**
   - `AgreeOnActive active m₁ m₂`: `m₁` and `m₂` agree at every active
     coordinate `active i = true`.
   - `AllActiveInit active m`: every active coordinate holds an initialized
     byte (`.init _ _`).
   - `PaddingIndependent activeIn activeOut kernel`: active output bytes depend
     only on active input bytes (`paddingIndependent_id`,
     `paddingIndependent_comp`, `paddingIndependent_demonic_uninit_free`).
2. **Four-Zone In-Place Stencil Framing (`StencilZone`,
   `OverlapKernelSound`, `[]` zero axioms):**
   - Four-constructor `StencilZone` (`.readOnly`, `.readWrite`, `.writeOnly`,
     `.frame`) with computable `classifyZone inR inW a` and
     `classifyZone_complete`.
   - `OverlapKernelSound inR inW kernel`: preserves all non-written bytes
     (`.readOnly` and `.frame`), determines all written bytes (`inW`) strictly
     from read bytes (`inR`, ignoring `.writeOnly` `.uninit` pixels and
     `.frame`), and preserves `AllActiveInit` on `inW` when initialized on
     `inR`.
   - `overlapKernelSound_preserves_nonWritten` &
     `overlapKernelSound_writeOnly_uninit_insensitive`.
3. **Causal Multi-Step Prefix Transfer (`CausalStep`, `causalSweep_sound`,
   `[]` zero axioms):**
   - Models multi-step causal sweeps (`k = 0..K-1`) where step `k` reads inside
     the already-initialized causal prefix `inR k ⊆ prefix k` and writes
     `inW k`, growing the initialized prefix monotonically to `prefix k ∪
     inW k` via `List.foldr` (`0` `._unsafe_rec`) while framing all untouched
     coordinates.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles with zero axioms (`[]`; Lean's auto-generated `.injEq` helpers use
`[propext]`).
-/

namespace Anneal.SpatialPinV2

open Trusted.MirAst Trusted.MirSemantics

/-! ## Part I: Active-Mask Universal Demonic `Uninit`-Padding Independence -/

/-- Two byte maps agree on all active coordinates selected by `active`. -/
@[expose] def AgreeOnActive (active : Nat → Bool)
    (m₁ m₂ : Nat → AllocByte) : Prop :=
  ∀ i : Nat, active i = true → m₁ i = m₂ i

/-- Every active coordinate in `m` holds an initialized byte (`.init _ _`). -/
@[expose] def AllActiveInit (active : Nat → Bool)
    (m : Nat → AllocByte) : Prop :=
  ∀ i : Nat, active i = true →
    ∃ (b : UInt8) (p : Option AllocId), m i = .init b p

/-- Universal demonic padding independence: any two inputs agreeing on
`activeIn` (regardless of `.uninit` or arbitrary padding bytes outside
`activeIn`) produce identical outputs on `activeOut`. -/
@[expose] def PaddingIndependent (activeIn activeOut : Nat → Bool)
    (kernel : (Nat → AllocByte) → (Nat → AllocByte)) : Prop :=
  ∀ m₁ m₂ : Nat → AllocByte,
    AgreeOnActive activeIn m₁ m₂ →
    AgreeOnActive activeOut (kernel m₁) (kernel m₂)

/-- Reflexivity of `AgreeOnActive` (`[]` zero axioms). -/
theorem agreeOnActive_refl (active : Nat → Bool) (m : Nat → AllocByte) :
    AgreeOnActive active m m :=
  fun _ _ => rfl

/-- Symmetry of `AgreeOnActive` (`[]` zero axioms). -/
theorem agreeOnActive_symm {active : Nat → Bool} {m₁ m₂ : Nat → AllocByte}
    (h : AgreeOnActive active m₁ m₂) : AgreeOnActive active m₂ m₁ :=
  fun i hi => (h i hi).symm

/-- Transitivity of `AgreeOnActive` (`[]` zero axioms). -/
theorem agreeOnActive_trans {active : Nat → Bool} {m₁ m₂ m₃ : Nat → AllocByte}
    (h₁₂ : AgreeOnActive active m₁ m₂) (h₂₃ : AgreeOnActive active m₂ m₃) :
    AgreeOnActive active m₁ m₃ :=
  fun i hi => Eq.trans (h₁₂ i hi) (h₂₃ i hi)

/-- Identity kernel is `PaddingIndependent` (`[]` zero axioms). -/
theorem paddingIndependent_id (active : Nat → Bool) :
    PaddingIndependent active active (fun m => m) :=
  fun _ _ h => h

/-- Sequential composition preserves `PaddingIndependent` (`[]` zero axioms). -/
theorem paddingIndependent_comp {a₁ a₂ a₃ : Nat → Bool}
    {k₁ k₂ : (Nat → AllocByte) → (Nat → AllocByte)}
    (h₁ : PaddingIndependent a₁ a₂ k₁) (h₂ : PaddingIndependent a₂ a₃ k₂) :
    PaddingIndependent a₁ a₃ (fun m => k₂ (k₁ m)) :=
  fun m₁ m₂ hAgree => h₂ (k₁ m₁) (k₁ m₂) (h₁ m₁ m₂ hAgree)

/-- Overwrites every inactive coordinate (`active i = false`) with `padEnv i`,
modeling demonic uninitialized or garbage SIMD stride-tail bytes. -/
@[expose] def withDemonicPadding (active : Nat → Bool)
    (spec padEnv : Nat → AllocByte) : Nat → AllocByte :=
  fun i => if active i then spec i else padEnv i

/-- Demonic `Uninit`-padding elimination (`[]` zero axioms): a
`PaddingIndependent` kernel produces the exact `spec` output on `activeOut`
under any demonic padding environment `padEnv` (including `.uninit` tails). -/
theorem paddingIndependent_demonic_uninit_free {activeIn activeOut : Nat → Bool}
    {kernel : (Nat → AllocByte) → (Nat → AllocByte)}
    (hInd : PaddingIndependent activeIn activeOut kernel)
    (spec padEnv : Nat → AllocByte) :
    AgreeOnActive activeOut
      (kernel (withDemonicPadding activeIn spec padEnv))
      (kernel spec) := by
  apply hInd
  intro i hi
  dsimp only [withDemonicPadding]
  rw [hi]
  rfl

/-! ## Part II: Tri-Partitioned Stencil Framing (`OverlapKernelSound`) -/

/-- Four mutually exclusive footprint zones partitioning any address space
under read footprint `inR` and write footprint `inW`. -/
inductive StencilZone where
  | readOnly
  | readWrite
  | writeOnly
  | frame

/-- Computable zone classifier for overlapping read/write footprints (`0`
`._unsafe_rec`). -/
@[expose] def classifyZone (inR inW : Nat → Bool) (a : Nat) : StencilZone :=
  match inR a, inW a with
  | true, false => .readOnly
  | true, true => .readWrite
  | false, true => .writeOnly
  | false, false => .frame

/-- Complete four-zone characterization (`[]` zero axioms): `classifyZone`
uniquely characterizes `.readOnly` (`R \ W`), `.readWrite` (`R ∩ W`),
`.writeOnly` (`W \ R`), and `.frame` (`¬ R ∧ ¬ W`). -/
theorem classifyZone_complete (inR inW : Nat → Bool) (a : Nat) :
    (classifyZone inR inW a = .readOnly ↔ inR a = true ∧ inW a = false) ∧
    (classifyZone inR inW a = .readWrite ↔ inR a = true ∧ inW a = true) ∧
    (classifyZone inR inW a = .writeOnly ↔ inR a = false ∧ inW a = true) ∧
    (classifyZone inR inW a = .frame ↔ inR a = false ∧ inW a = false) := by
  unfold classifyZone
  cases inR a with
  | true =>
    cases inW a with
    | true =>
      exact
        ⟨⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.2)⟩,
         ⟨(fun _ => ⟨rfl, rfl⟩), (fun _ => rfl)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩⟩
    | false =>
      exact
        ⟨⟨(fun _ => ⟨rfl, rfl⟩), (fun _ => rfl)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.2)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩⟩
  | false =>
    cases inW a with
    | true =>
      exact
        ⟨⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩,
         ⟨(fun _ => ⟨rfl, rfl⟩), (fun _ => rfl)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.2)⟩⟩
    | false =>
      exact
        ⟨⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.1)⟩,
         ⟨(fun h => nomatch h), (fun h => Bool.noConfusion h.2)⟩,
         ⟨(fun _ => ⟨rfl, rfl⟩), (fun _ => rfl)⟩⟩

/-- Tri-partitioned overlapping-stencil soundness contract:
1. `framePreserved`: every coordinate outside `inW` (`.readOnly` and `.frame`)
   is preserved untouched.
2. `readLocal`: written outputs (`inW`) depend strictly on input bytes in `inR`
   (`.readOnly` and `.readWrite`), ignoring `.writeOnly` (`.uninit`-admissible)
   and `.frame`.
3. `initOutput`: whenever `inR` is initialized, `kernel m` produces initialized
   bytes across `inW`. -/
structure OverlapKernelSound (inR inW : Nat → Bool)
    (kernel : (Nat → AllocByte) → (Nat → AllocByte)) : Prop where
  framePreserved :
    ∀ (m : Nat → AllocByte) (a : Nat), inW a = false → kernel m a = m a
  readLocal :
    ∀ (m₁ m₂ : Nat → AllocByte),
      AgreeOnActive inR m₁ m₂ → AgreeOnActive inW (kernel m₁) (kernel m₂)
  initOutput :
    ∀ (m : Nat → AllocByte), AllActiveInit inR m → AllActiveInit inW (kernel m)

/-- Frame and read-only zone preservation under `OverlapKernelSound` (`[]`
zero axioms). -/
theorem overlapKernelSound_preserves_nonWritten {inR inW : Nat → Bool}
    {kernel : (Nat → AllocByte) → (Nat → AllocByte)}
    (hS : OverlapKernelSound inR inW kernel) (m : Nat → AllocByte) (a : Nat)
    (hZone : classifyZone inR inW a = .readOnly ∨
      classifyZone inR inW a = .frame) :
    kernel m a = m a := by
  have hNotW : inW a = false := by
    cases hZone with
    | inl hRO => exact ((classifyZone_complete inR inW a).1.mp hRO).2
    | inr hFr => exact ((classifyZone_complete inR inW a).2.2.2.mp hFr).2
  exact hS.framePreserved m a hNotW

/-- `.writeOnly` (`W \ R`) `.uninit`-insensitivity (`[]` zero axioms):
replacing every `.writeOnly` byte of `m` with `.uninit` (or any `padEnv`) never
changes `kernel m` at any written coordinate in `inW`. -/
theorem overlapKernelSound_writeOnly_uninit_insensitive {inR inW : Nat → Bool}
    {kernel : (Nat → AllocByte) → (Nat → AllocByte)}
    (hS : OverlapKernelSound inR inW kernel)
    (m padEnv : Nat → AllocByte) :
    AgreeOnActive inW
      (kernel (withDemonicPadding inR m padEnv))
      (kernel m) :=
  paddingIndependent_demonic_uninit_free hS.readLocal m padEnv

/-- Initialized-prefix growth after one overlapping stencil step (`[]` zero
axioms): if `prefix` is initialized and `inR ⊆ prefix`, then `prefix ∪ inW` is
initialized after `kernel m`. -/
theorem overlapKernelSound_grows_initPrefix {inR inW pfx : Nat → Bool}
    {kernel : (Nat → AllocByte) → (Nat → AllocByte)}
    (hS : OverlapKernelSound inR inW kernel)
    (hCausal : ∀ a : Nat, inR a = true → pfx a = true)
    {m : Nat → AllocByte} (hInit : AllActiveInit pfx m) :
    AllActiveInit (fun a => pfx a || inW a) (kernel m) := by
  have hInitR : AllActiveInit inR m :=
    fun a ha => hInit a (hCausal a ha)
  intro a ha
  cases hW : inW a with
  | true => exact hS.initOutput m hInitR a hW
  | false =>
    dsimp only at ha
    rw [hW, Bool.or_false] at ha
    rw [hS.framePreserved m a hW]
    exact hInit a ha

/-! ## Part III: Causal Multi-Step Wavefront Prefix Sweep (`IntraBC`) -/

/-- One causal sweep step (e.g., an AV1 IntraBC or superblock raster step)
carrying read footprint `inR`, write footprint `inW`, and pure transition
`kernel`. -/
structure CausalStep where
  inR : Nat → Bool
  inW : Nat → Bool
  kernel : (Nat → AllocByte) → (Nat → AllocByte)

/-- Runs `steps` sequentially from left to right using `List.foldr` over
reversed composition (`0` `._unsafe_rec`): `runCausalSteps [s₁, s₂] m =
s₂.kernel (s₁.kernel m)`. -/
@[expose] def runCausalSteps (steps : List CausalStep)
    (m : Nat → AllocByte) : Nat → AllocByte :=
  List.foldr (fun s ih m' => ih (s.kernel m')) (fun m' => m') steps m

/-- Cumulative initialized-coordinate mask after executing `steps` starting
from initial prefix `pfx₀` (`List.foldr`, `0` `._unsafe_rec`). -/
@[expose] def causalPrefixAfter (steps : List CausalStep)
    (pfx₀ : Nat → Bool) : Nat → Bool :=
  List.foldr
    (fun s ih pfx => ih (fun a => pfx a || s.inW a))
    (fun pfx => pfx)
    steps pfx₀

/-- Inductive causal-sweep admissibility: every step satisfies
`OverlapKernelSound` and reads strictly inside the monotone prefix accumulated
by earlier steps (`List.foldr`, `0` `._unsafe_rec`). -/
@[expose] def CausalSweepValid (steps : List CausalStep)
    (pfx₀ : Nat → Bool) : Prop :=
  List.foldr
    (fun s ih pfx =>
      OverlapKernelSound s.inR s.inW s.kernel ∧
      (∀ a : Nat, s.inR a = true → pfx a = true) ∧
      ih (fun a => pfx a || s.inW a))
    (fun _ => True)
    steps pfx₀

/-- Multi-step causal wavefront prefix soundness (`[]` zero axioms):
1. Executing a `CausalSweepValid` sequence from an initialized `pfx₀` yields an
   initialized final state across `causalPrefixAfter steps pfx₀`.
2. Every coordinate never written by any step (`causalPrefixAfter steps
   (fun _ => false) a = false`) is framed untouched across the entire sweep. -/
theorem causalSweep_sound :
    ∀ (steps : List CausalStep) (pfx₀ : Nat → Bool) (m : Nat → AllocByte),
      CausalSweepValid steps pfx₀ →
      AllActiveInit pfx₀ m →
      AllActiveInit (causalPrefixAfter steps pfx₀) (runCausalSteps steps m) ∧
      (∀ a : Nat,
        causalPrefixAfter steps (fun _ => false) a = false →
        runCausalSteps steps m a = m a)
  | [], _, _, _, hInit => ⟨hInit, fun _ _ => rfl⟩
  | s :: rest, pfx₀, m, hValid, hInit => by
    have hNextInit :
        AllActiveInit (fun a => pfx₀ a || s.inW a) (s.kernel m) :=
      overlapKernelSound_grows_initPrefix hValid.1 hValid.2.1 hInit
    have hRest :=
      causalSweep_sound rest (fun a => pfx₀ a || s.inW a) (s.kernel m)
        hValid.2.2 hNextInit
    refine ⟨hRest.1, ?_⟩
    intro a hNotWritten
    have hMono :
        ∀ (ss : List CausalStep) (p₁ p₂ : Nat → Bool),
          (∀ x, p₁ x = true → p₂ x = true) →
          causalPrefixAfter ss p₁ a = true →
          causalPrefixAfter ss p₂ a = true := by
      intro ss
      induction ss with
      | nil => intro p₁ p₂ hImp hp; exact hImp a hp
      | cons st tl ih =>
        intro p₁ p₂ hImp hp
        apply ih (fun x => p₁ x || st.inW x) (fun x => p₂ x || st.inW x) _ hp
        intro x hx
        cases h1 : p₁ x with
        | true => rw [hImp x h1]; rfl
        | false =>
          cases h2 : st.inW x with
          | false => rw [h1, h2] at hx; exact Bool.noConfusion hx
          | true => cases p₂ x <;> rfl
    have hStayFalse :
        ∀ (ss : List CausalStep) (p : Nat → Bool),
          p a = true → causalPrefixAfter ss p a = true := by
      intro ss
      induction ss with
      | nil => intro p hp; exact hp
      | cons st tl ih =>
        intro p hp
        apply ih (fun x => p x || st.inW x)
        rw [hp]
        rfl
    have hSWFalse : s.inW a = false := by
      cases hw : s.inW a with
      | false => rfl
      | true =>
        have hTrue :
            causalPrefixAfter rest (fun x => false || s.inW x) a = true :=
          hStayFalse rest (fun x => false || s.inW x) (by rw [hw]; rfl)
        change causalPrefixAfter rest (fun x => false || s.inW x) a = false
          at hNotWritten
        rw [hTrue] at hNotWritten
        exact Bool.noConfusion hNotWritten
    have hRestFalse : causalPrefixAfter rest (fun _ => false) a = false := by
      cases hr : causalPrefixAfter rest (fun _ => false) a with
      | false => rfl
      | true =>
        have hTrue :
            causalPrefixAfter rest (fun x => false || s.inW x) a = true :=
          hMono rest (fun _ => false) (fun x => false || s.inW x)
            (fun _ h => Bool.noConfusion h) hr
        change causalPrefixAfter rest (fun x => false || s.inW x) a = false
          at hNotWritten
        rw [hTrue] at hNotWritten
        exact Bool.noConfusion hNotWritten
    change runCausalSteps rest (s.kernel m) a = m a
    rw [hRest.2 a hRestFalse, hValid.1.framePreserved m a hSWFalse]

end Anneal.SpatialPinV2

end
