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
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.ConjunctiveWp.Wlp

public section

/-!
# Relational `SafeTwin` Equivalence, Property Transfer, & Constant-Time 2-Safety

Statement-origin-separated relational equivalence contracts (`SafeTwin`) over
`Trusted.MirSemantics`, fuel-bounded and productive-divergence proof bridges,
weak-contract loophole characterizations, and convention-level phantom secrecy
tagging + specification-level leak-trace 2-safety:

1. **Query- & Body-Level `SafeTwin` Equivalence (`SafeTwinQueryEquiv`,
   `TotalSafeTwinBodyEquiv`):**
   - `SafeTwinQueryEquiv pSafe pCand q`: enforces `WellFormed` on both programs,
     bidirectional `Behavior` parity across all `TerminalOut` outcomes (both
     `.returned out` and `.unwound callerMem`), and bidirectional `Diverges`
     parity (`refl`, `symm`, `trans`).
   - `satisfiesPost_iff_of_safeTwinQueryEquiv` &
     `terminatesWith_iff_of_safeTwinQueryEquiv`: bidirectional transfer of
     partial- and total-correctness `TerminalOut` contracts.
   - `TotalSafeTwinBodyEquiv`: binds `(pSafe, safeId, bodySafe)` and
     `(pCand, candId, bodyCand)` under `BodyStaticAdmitted` and an input domain
     relation `argRel`, discharging `Trusted.MirSemantics.BodyVerified` via
     `bodyVerified_of_totalSafeTwinBodyEquiv`.
2. **Fuel-Bounded WP, Pow2-Fuel, & Productive-Divergence Proof Rules:**
   - `safeTwinQueryEquiv_of_wpProg_sameOut`,
     `safeTwinQueryEquiv_of_execProg_sameOut`, and
     `safeTwinQueryEquiv_of_execProgPow2_sameOut`: prove unbounded
     `SafeTwinQueryEquiv` from finite-fuel (potentially asymmetric) `wpProg` /
     `execProg` / `execProgPow2` proofs reaching a common `out₀ : TerminalOut`.
   - `wellFormed_and_noBehavior_of_productiveWitness` &
     `safeTwinQueryEquiv_of_productiveWitnesses`: prove constructive
     `SafeTwinQueryEquiv` between diverging reactive loops (`0`
     `Classical.choice`).
3. **Weak-Equivalence Loopholes (`ReturnOnlyMirEquiv`, `PartialMirEquiv`,
   `DiscrimOnlyTermEq`):**
   - Formalizes the weak contracts that `SafeTwinQueryEquiv` strengthens
     (return-only implication missing fault/unwind laundering, partial
     implication missing silent candidate divergence, and discriminant-only
     `TerminalOut` comparison ignoring pre-unwind `CallerMemory` mutations).
   - Note on Profile v1 (`Trusted/MirSemantics/Step.lean`): single-body Profile
     v1 steps `.unwindResume`, `.assert`, and `.call` to `.fault .unsupported`,
     while `TerminalOut.unwound callerMem` is already present on the outer
     `Trusted.MirSemantics` boundary so `SafeTwinQueryEquiv` and
     `DiscrimOnlyTermEq` cover `.unwound` payloads without change as unwind
     stepping lands.
4. **Phantom `SecScalar` Tagging & Specification-Level `LeakObs` 2-Safety
   (`[]` zero axioms):**
   - `SecLevel` (`.pub` | `.sec`), transparent convention-level wrapper
     `SecScalar` (public constructor and `raw` field), `secClassify`, `secMap`,
     `secMap2`, and convention-level `declassifySecScalar` marker.
   - Specification-level `LeakObs` traces (`.branch` | `.memAddr` |
     `.varTimeOp`; supplied as specification functions rather than derived from
     `evalStep`), `LeakNonInterference`, `ObsTraceAligned`, and
     `leakNonInterference_transfer_of_obsAligned` (showing 2-safety
     constant-time transfer holds under `ObsTraceAligned` despite McLean's
     Refinement Paradox for functional equivalence alone).
-/

namespace Anneal.SafeTwin

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp Anneal.ConjunctiveWp

/-! ## Part I: `SafeTwinQueryEquiv` & `TotalSafeTwinBodyEquiv` -/

/-- Total observational equivalence between reference program `pSafe` and
candidate program `pCand` at query `q` in $M_{\text{anneal}}$: both are
`WellFormed` (fault-free and non-stuck), agree on every `TerminalOut`
(`.returned` and `.unwound callerMem`), and agree on `Diverges`. -/
structure SafeTwinQueryEquiv (pSafe pCand : Program) (q : Query) : Prop where
  wfCand : WellFormed pCand q
  wfSafe : WellFormed pSafe q
  behaviorIff : ∀ out : TerminalOut, Behavior pCand q out ↔ Behavior pSafe q out
  divergesIff : Diverges pCand q ↔ Diverges pSafe q

/-- Reflexivity of `SafeTwinQueryEquiv` on any `WellFormed` `(p, q)`
(`[propext]` only). -/
theorem safeTwinQueryEquiv_refl {p : Program} {q : Query}
    (hWf : WellFormed p q) : SafeTwinQueryEquiv p p q :=
  ⟨hWf, hWf, fun _ => Iff.rfl, Iff.rfl⟩

/-- Symmetry of `SafeTwinQueryEquiv` (`[propext]` only). -/
theorem safeTwinQueryEquiv_symm {p₁ p₂ : Program} {q : Query}
    (h : SafeTwinQueryEquiv p₁ p₂ q) : SafeTwinQueryEquiv p₂ p₁ q :=
  ⟨h.wfSafe, h.wfCand, fun out => (h.behaviorIff out).symm, h.divergesIff.symm⟩

/-- Transitivity of `SafeTwinQueryEquiv` (`[propext]` only), enabling $K$
backend implementations to compose through a shared scalar reference twin. -/
theorem safeTwinQueryEquiv_trans {p₁ p₂ p₃ : Program} {q : Query}
    (h₁₂ : SafeTwinQueryEquiv p₁ p₂ q) (h₂₃ : SafeTwinQueryEquiv p₂ p₃ q) :
    SafeTwinQueryEquiv p₁ p₃ q :=
  ⟨h₂₃.wfCand, h₁₂.wfSafe,
   fun out => Iff.trans (h₂₃.behaviorIff out) (h₁₂.behaviorIff out),
   Iff.trans h₂₃.divergesIff h₁₂.divergesIff⟩

/-- Bidirectional `SatisfiesPost` transfer across `SafeTwinQueryEquiv`
(`[propext]` only). -/
theorem satisfiesPost_iff_of_safeTwinQueryEquiv {pSafe pCand : Program}
    {q : Query} (h : SafeTwinQueryEquiv pSafe pCand q)
    (post : TerminalOut → Prop) :
    SatisfiesPost pCand q post ↔ SatisfiesPost pSafe q post := by
  refine ⟨?_, ?_⟩
  · intro hSatC
    exact ⟨h.wfSafe, fun out hBehS =>
      hSatC.2 out ((h.behaviorIff out).mpr hBehS)⟩
  · intro hSatS
    exact ⟨h.wfCand, fun out hBehC =>
      hSatS.2 out ((h.behaviorIff out).mp hBehC)⟩

/-- Bidirectional total-correctness (`¬ Diverges` + witnessing `Behavior`)
transfer across `SafeTwinQueryEquiv` (`[propext]` only). -/
theorem terminatesWith_iff_of_safeTwinQueryEquiv {pSafe pCand : Program}
    {q : Query} (h : SafeTwinQueryEquiv pSafe pCand q)
    (post : TerminalOut → Prop) :
    (¬ Diverges pCand q ∧ ∃ out, Behavior pCand q out ∧ post out) ↔
      (¬ Diverges pSafe q ∧ ∃ out, Behavior pSafe q out ∧ post out) := by
  refine ⟨?_, ?_⟩
  · intro hC
    cases hC.2 with
    | intro out hOut =>
      exact ⟨fun hDivS => hC.1 (h.divergesIff.mpr hDivS),
        out, (h.behaviorIff out).mp hOut.1, hOut.2⟩
  · intro hS
    cases hS.2 with
    | intro out hOut =>
      exact ⟨fun hDivC => hS.1 (h.divergesIff.mp hDivC),
        out, (h.behaviorIff out).mpr hOut.1, hOut.2⟩

/-- Body-level `SafeTwin` contract binding `(pSafe, safeId, bodySafe)` and
`(pCand, candId, bodyCand)` under `BodyStaticAdmitted` and an input domain
precondition `argRel : List Val → Prop`. -/
structure TotalSafeTwinBodyEquiv
    (pSafe : Program) (safeId : DefId) (bodySafe : Body)
    (pCand : Program) (candId : DefId) (bodyCand : Body)
    (argRel : List Val → Prop) : Prop where
  safeLookup : Trusted.MirSemantics.getElem? pSafe.bodies safeId = some bodySafe
  safeAdmitted : BodyStaticAdmitted pSafe bodySafe = true
  candLookup : Trusted.MirSemantics.getElem? pCand.bodies candId = some bodyCand
  candAdmitted : BodyStaticAdmitted pCand bodyCand = true
  queryEquiv :
    ∀ args : List Val,
      ValidEntryArgs bodySafe args →
      ValidEntryArgs bodyCand args →
      argRel args →
      SafeTwinQueryEquiv
        (entryProgForBody pSafe safeId)
        (entryProgForBody pCand candId)
        { args := args }

/-- Discharges `Trusted.MirSemantics.BodyVerified` for `bodyCand` from
`TotalSafeTwinBodyEquiv` whenever `safetyPre` (on `unsafe` bodies) implies
`ValidEntryArgs bodySafe args ∧ argRel args` (`[propext]` only). Candidate
UB-freedom comes directly from the `wfCand` field bundled inside
`SafeTwinQueryEquiv`. -/
theorem bodyVerified_of_totalSafeTwinBodyEquiv
    {pSafe : Program} {safeId : DefId} {bodySafe : Body}
    {pCand : Program} {candId : DefId} {bodyCand : Body}
    {argRel safetyPre : List Val → Prop}
    (hTwin : TotalSafeTwinBodyEquiv
      pSafe safeId bodySafe pCand candId bodyCand argRel)
    (hDomain : ∀ args : List Val,
      ValidEntryArgs bodyCand args →
      (bodyCand.isUnsafe = true → safetyPre args) →
      ValidEntryArgs bodySafe args ∧ argRel args) :
    BodyVerified pCand candId bodyCand safetyPre := by
  refine ⟨hTwin.candLookup, hTwin.candAdmitted, ?_⟩
  intro args hValidC hUnsafePre
  have hDom := hDomain args hValidC hUnsafePre
  exact (hTwin.queryEquiv args hDom.1 hValidC hDom.2).wfCand

/-! ## Part II: Fuel-Bounded WP & Productive-Divergence Adequacy Bridges -/

/-- Exact terminal characterization from `wpProg p fuel q (fun o => o = out₀)`
(`[propext]` only). -/
theorem behavior_iff_eq_of_wpProg_eq {p : Program} {q : Query} {fuel : Nat}
    {out₀ : TerminalOut} (hWp : wpProg p fuel q (fun o => o = out₀)) :
    WellFormed p q ∧ ¬ Diverges p q ∧
      ∀ out : TerminalOut, Behavior p q out ↔ out = out₀ := by
  cases wellFormed_and_spec_of_wp_base p q fuel (fun o => o = out₀) hWp with
  | intro hSat hRest =>
    cases hRest with
    | intro hNdiv hEx =>
      cases hEx with
      | intro out' hOut' =>
        have hBeh₀ : Behavior p q out₀ := by
          rw [← hOut'.2]
          exact hOut'.1
        refine ⟨hSat.1, hNdiv, fun out => ⟨hSat.2 out, fun hEq => ?_⟩⟩
        rw [hEq]
        exact hBeh₀

/-- Asymmetric-fuel `wpProg` bridge into unbounded `SafeTwinQueryEquiv`
(`[propext]` only): when `pSafe` (at `fuelSafe`) and `pCand` (at `fuelCand`)
both satisfy `wpProg` for the same terminal outcome `out₀`, `SafeTwinQueryEquiv
pSafe pCand q` holds. -/
theorem safeTwinQueryEquiv_of_wpProg_sameOut {pSafe pCand : Program} {q : Query}
    {fuelSafe fuelCand : Nat} {out₀ : TerminalOut}
    (hSafe : wpProg pSafe fuelSafe q (fun o => o = out₀))
    (hCand : wpProg pCand fuelCand q (fun o => o = out₀)) :
    SafeTwinQueryEquiv pSafe pCand q := by
  have hS := behavior_iff_eq_of_wpProg_eq hSafe
  have hC := behavior_iff_eq_of_wpProg_eq hCand
  exact ⟨hC.1, hS.1,
    fun out => Iff.trans (hC.2.2 out) (hS.2.2 out).symm,
    ⟨fun hDivC => False.elim (hC.2.1 hDivC),
     fun hDivS => False.elim (hS.2.1 hDivS)⟩⟩

/-- Deterministic `execProg` fast-path bridge into `SafeTwinQueryEquiv`
(`[propext]` only). -/
theorem safeTwinQueryEquiv_of_execProg_sameOut {pSafe pCand : Program}
    {q : Query} {fuelSafe fuelCand : Nat} {out₀ : TerminalOut}
    (hSafe : execProg pSafe fuelSafe q (fun o => o = out₀))
    (hCand : execProg pCand fuelCand q (fun o => o = out₀)) :
    SafeTwinQueryEquiv pSafe pCand q :=
  safeTwinQueryEquiv_of_wpProg_sameOut
    (wpProg_of_execProg hSafe) (wpProg_of_execProg hCand)

/-- Logarithmic-depth `execProgPow2` bridge into `SafeTwinQueryEquiv`
(`[propext]` only), allowing multi-hundred-step scalar reference loops and
unrolled/vectorized twins to discharge `SafeTwinQueryEquiv` by `rfl` inside
Lean's default `maxRecDepth`. -/
theorem safeTwinQueryEquiv_of_execProgPow2_sameOut {pSafe pCand : Program}
    {q : Query} {kSafe kCand : Nat} {out₀ : TerminalOut}
    (hSafe : execProgPow2 pSafe kSafe q (fun o => o = out₀))
    (hCand : execProgPow2 pCand kCand q (fun o => o = out₀)) :
    SafeTwinQueryEquiv pSafe pCand q :=
  safeTwinQueryEquiv_of_wpProg_sameOut
    (wpProgPow2_iff_wpProg.mp (wpProgPow2_of_execProgPow2 hSafe))
    (wpProgPow2_iff_wpProg.mp (wpProgPow2_of_execProgPow2 hCand))

private theorem reaches_inv_of_productiveWitness {p : Program}
    {next : State → State} {inv : State → Prop}
    (hw : ProductiveStepWitness p next inv) {s₀ : State} (hInv₀ : inv s₀) :
    ∀ {s : State}, Reaches p s₀ s → inv s
  | _, .refl _ => hInv₀
  | _, .tail hR hStep => by
    have hInvMid := reaches_inv_of_productiveWitness hw hInv₀ hR
    cases hStep with
    | intro c hc =>
      have hc0 : c = 0 := hc.1
      have hEval := hc.2
      rw [hc0, hw.stepOk _ hInvMid] at hEval
      injection hEval with hs'
      rw [← hs']
      exact hw.preserves _ hInvMid

/-- Constructive adequacy of a `ProductiveStepWitness` (`[propext]` only, `0`
`Classical.choice`): any entry state satisfying `hw` is `WellFormed`, never
terminates in `Behavior p q out`, and `Diverges`. -/
theorem wellFormed_and_noBehavior_of_productiveWitness {p : Program} {q : Query}
    {next : State → State} {inv : State → Prop} {s₀ : State}
    (hInit : initState p q = .ok s₀) (hInv₀ : inv s₀)
    (hw : ProductiveStepWitness p next inv) :
    WellFormed p q ∧ (∀ out : TerminalOut, ¬ Behavior p q out) ∧
      Diverges p q := by
  refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_,
    diverges_of_productiveWitness hInit hInv₀ hw⟩
  · intro k hFault
    unfold ReachesResult at hFault
    rw [hInit] at hFault
    cases hFault with
    | intro s hs =>
      have hInv := reaches_inv_of_productiveWitness hw hInv₀ hs.1
      cases hs.2 with
      | intro c hc =>
        have hc0 : c = 0 := hc.1
        have hEval := hc.2
        rw [hc0, hw.stepOk s hInv] at hEval
        nomatch hEval
  · intro out hBeh
    unfold Behavior ReachesResult at hBeh
    rw [hInit] at hBeh
    cases hBeh with
    | intro s hs =>
      have hInv := reaches_inv_of_productiveWitness hw hInv₀ hs.1
      cases hs.2 with
      | intro c hc =>
        have hc0 : c = 0 := hc.1
        have hEval := hc.2
        rw [hc0, hw.stepOk s hInv] at hEval
        nomatch hEval

/-- Constructive `SafeTwinQueryEquiv` between two productive diverging MIR
programs (`[propext]` only, `0` `Classical.choice`). -/
theorem safeTwinQueryEquiv_of_productiveWitnesses {pSafe pCand : Program}
    {q : Query} {nextSafe nextCand : State → State}
    {invSafe invCand : State → Prop} {sSafe₀ sCand₀ : State}
    (hInitS : initState pSafe q = .ok sSafe₀) (hInvS₀ : invSafe sSafe₀)
    (hwS : ProductiveStepWitness pSafe nextSafe invSafe)
    (hInitC : initState pCand q = .ok sCand₀) (hInvC₀ : invCand sCand₀)
    (hwC : ProductiveStepWitness pCand nextCand invCand) :
    SafeTwinQueryEquiv pSafe pCand q := by
  have hS := wellFormed_and_noBehavior_of_productiveWitness hInitS hInvS₀ hwS
  have hC := wellFormed_and_noBehavior_of_productiveWitness hInitC hInvC₀ hwC
  exact ⟨hC.1, hS.1,
    fun out =>
      ⟨fun hBC => False.elim (hC.2.1 out hBC),
       fun hBS => False.elim (hS.2.1 out hBS)⟩,
    ⟨fun _ => hS.2.2, fun _ => hC.2.2⟩⟩

/-! ## Part III: Weak-Equivalence Loophole Contracts (`L1`–`L4`) -/

/-- Weak return-only relation (`Loopholes L1/L2`): checks only `.returned`
outcomes of `pCand`, ignoring `.fault` UB/unsupported escapes and `.unwound`. -/
@[expose] def ReturnOnlyMirEquiv (pSafe pCand : Program) (q : Query) : Prop :=
  ∀ out : Out, Behavior pCand q (.returned out) →
    Behavior pSafe q (.returned out)

/-- Weak partial-refinement relation (`Loophole L3`): checks `WellFormed pCand`
and forward `Behavior` inclusion without reverse `Behavior` or `Diverges`
parity, permitting an infinite loop in `pCand` when `pSafe` terminates. -/
@[expose] def PartialMirEquiv (pSafe pCand : Program) (q : Query) : Prop :=
  WellFormed pCand q ∧
    ∀ out : TerminalOut, Behavior pCand q out → Behavior pSafe q out

/-- Discriminant-only `TerminalOut` comparison (`Loophole L4`): equates any two
`.unwound` outcomes regardless of pre-unwind `CallerMemory` mutations. -/
@[expose] def DiscrimOnlyTermEq (o₁ o₂ : TerminalOut) : Prop :=
  match o₁, o₂ with
  | .returned r₁, .returned r₂ => r₁ = r₂
  | .unwound _, .unwound _ => True
  | .returned _, .unwound _ => False
  | .unwound _, .returned _ => False

/-- `SafeTwinQueryEquiv` implies `PartialMirEquiv` (`[propext]` only). -/
theorem partialMirEquiv_of_safeTwinQueryEquiv {pSafe pCand : Program}
    {q : Query} (h : SafeTwinQueryEquiv pSafe pCand q) :
    PartialMirEquiv pSafe pCand q :=
  ⟨h.wfCand, fun out hBehC => (h.behaviorIff out).mp hBehC⟩

/-- `PartialMirEquiv` implies `ReturnOnlyMirEquiv` (`[propext]` only). -/
theorem returnOnlyMirEquiv_of_partialMirEquiv {pSafe pCand : Program}
    {q : Query} (h : PartialMirEquiv pSafe pCand q) :
    ReturnOnlyMirEquiv pSafe pCand q :=
  fun out hRetC => h.2 (.returned out) hRetC

/-- `DiscrimOnlyTermEq` fails to distinguish `.unwound` outcomes with different
pre-unwind `CallerMemory` allocations, whereas exact `TerminalOut` equality
inside `SafeTwinQueryEquiv` rejects them (`[]` zero axioms). -/
theorem discrimOnlyTermEq_ignores_unwound_callerMem :
    let mClean : CallerMemory := ⟨[]⟩
    let mTorn : CallerMemory :=
      ⟨[{ allocId := 0
          alignLog2 := 0
          mutability := .mut
          bytes := [.init 0xDE none]
          live := true }]⟩
    DiscrimOnlyTermEq (.unwound mClean) (.unwound mTorn) ∧
    (TerminalOut.unwound mClean ≠ TerminalOut.unwound mTorn) := by
  intro mClean mTorn
  refine ⟨True.intro, ?_⟩
  intro hEq
  injection hEq with hMem
  injection hMem with hList
  nomatch hList

/-! ## Part IV: Phantom `SecScalar` Tagging & `LeakObs` 2-Safety -/

/-- Secrecy lattice (`PUB` vs. `SEC`) for convention-level constant-time value
tagging. -/
inductive SecLevel where
  | pub
  | sec

/-- Transparent phantom secrecy wrapper tagging a pure value `raw : α` with its
secrecy level `lvl` (`0` runtime overhead; unfolds away in `rfl`). Both the
constructor and `raw` projection are public, so secrecy separation is enforced
by convention rather than type-level opacity; formal 2-safety is enforced by
`LeakNonInterference` and `ObsTraceAligned` below. -/
structure SecScalar (lvl : SecLevel) (α : Type) where
  raw : α

/-- Promotes a public value into a `SecScalar .sec` value. -/
@[expose] def secClassify {α : Type} (x : SecScalar .pub α) :
    SecScalar .sec α :=
  ⟨x.raw⟩

/-- Convention-level declassification marker (`SecScalar .sec α →
SecScalar .pub α`); `SecScalar` itself is transparent. -/
@[expose] def declassifySecScalar {α : Type} (x : SecScalar .sec α) :
    SecScalar .pub α :=
  ⟨x.raw⟩

/-- Applies a pure unary operation inside `SecScalar lvl` while preserving its
phantom secrecy tag. -/
@[expose] def secMap {lvl : SecLevel} {α β : Type} (f : α → β)
    (x : SecScalar lvl α) : SecScalar lvl β :=
  ⟨f x.raw⟩

/-- Applies a pure binary operation across two `SecScalar lvl` operands. -/
@[expose] def secMap2 {lvl : SecLevel} {α β γ : Type} (f : α → β → γ)
    (x : SecScalar lvl α) (y : SecScalar lvl β) : SecScalar lvl γ :=
  ⟨f x.raw y.raw⟩

/-- Specification-level side-channel leakage observation: control-flow branch
direction, memory access address/index, or variable-time arithmetic operand
(supplied as specification trace functions rather than derived from
`evalStep`). -/
inductive LeakObs where
  | branch (taken : Bool)
  | memAddr (addr : Nat)
  | varTimeOp (operand : Nat)

/-- Constant-time 2-safety non-interference: any two inputs agreeing on their
public projection `pubProj` emit identical specification-level leakage traces
`obsTrace`. -/
@[expose] def LeakNonInterference {In Pub : Type} (pubProj : In → Pub)
    (obsTrace : In → List LeakObs) : Prop :=
  ∀ x₁ x₂ : In, pubProj x₁ = pubProj x₂ → obsTrace x₁ = obsTrace x₂

/-- Exact leakage-trace alignment between specification-level traces `obsSafe`
and `obsCand` on input domain `dom`. -/
@[expose] def ObsTraceAligned {In : Type} (dom : In → Prop)
    (obsSafe obsCand : In → List LeakObs) : Prop :=
  ∀ x : In, dom x → obsCand x = obsSafe x

/-- Sequential concatenation of two `LeakNonInterference` traces over the same
public projection `pubProj` (`[]` zero axioms). -/
theorem leakNonInterference_append {In Pub : Type} {pubProj : In → Pub}
    {obs₁ obs₂ : In → List LeakObs}
    (h₁ : LeakNonInterference pubProj obs₁)
    (h₂ : LeakNonInterference pubProj obs₂) :
    LeakNonInterference pubProj (fun x => obs₁ x ++ obs₂ x) := by
  intro x₁ x₂ hPub
  dsimp only
  rw [h₁ x₁ x₂ hPub, h₂ x₁ x₂ hPub]

/-- Constant-time 2-safety transfer (`[]` zero axioms): unlike functional
equivalence alone (McLean's Refinement Paradox), `ObsTraceAligned` transfers
`LeakNonInterference` from `obsSafe` to `obsCand` across all domain inputs. -/
theorem leakNonInterference_transfer_of_obsAligned {In Pub : Type}
    {dom : In → Prop} {pubProj : In → Pub}
    {obsSafe obsCand : In → List LeakObs}
    (hSafeNI : LeakNonInterference pubProj obsSafe)
    (hAlign : ObsTraceAligned dom obsSafe obsCand)
    {x₁ x₂ : In} (hx₁ : dom x₁) (hx₂ : dom x₂)
    (hPub : pubProj x₁ = pubProj x₂) :
    obsCand x₁ = obsCand x₂ := by
  rw [hAlign x₁ hx₁, hAlign x₂ hx₂]
  exact hSafeNI x₁ x₂ hPub

end Anneal.SafeTwin

end
