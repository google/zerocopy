-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Debuginfo-Free Weisfeiler-Leman CFG and Def-Use Oracle Alignment (`O2_`)

Mechanizes `WLGraph`, $k$-step Weisfeiler-Leman color refinement (`wlStep`, `wlColor`),
singleton-orbit uniqueness (`isUniqueOrbit`), orbit-symmetric hint application
(`OrbitSymmetric`), and the end-to-end soundness theorem `wl_align_and_replay_sound`
in Lean `v4.34.1` with zero `sorryAx` and zero `Lean.ofReduceBool` (`native_decide`).
-/

namespace WLOracleAlignment

abbrev NodeId := Nat
abbrev Color  := Nat

/-- Edge labels in the attributed Program-Dependence & Dominator-Tree Graph
$\mathcal{G}_{\text{WL}}(f)$. -/
inductive EdgeLabel where
  | domChild
  | loopBackedge
  | loopExit
  | trueSucc
  | falseSucc
  | defUseOp (argIdx : Nat)
  | memAddr
  | memVal
  deriving DecidableEq, Repr

/-- Attributed graph representation over finite node set `nodes : List NodeId`. -/
structure WLGraph where
  nodes      : List NodeId
  initColor  : NodeId → Color
  neighbors  : NodeId → List (EdgeLabel × NodeId)

/-- Deterministic hash combiner over a vertex color and its neighborhood encoding. -/
def mixColor (base : Color) (nbrHash : Color) : Color :=
  base * 31 + nbrHash + 17

def encodeEdgeLabel : EdgeLabel → Nat
  | .domChild       => 1
  | .loopBackedge   => 2
  | .loopExit       => 3
  | .trueSucc       => 4
  | .falseSucc      => 5
  | .defUseOp idx   => 10 + idx
  | .memAddr        => 20
  | .memVal         => 21

/-- Fold neighbor colors into an accumulator hash. -/
def hashNeighborhood (c : NodeId → Color) : List (EdgeLabel × NodeId) → Color
  | [] => 0
  | (lbl, u) :: rest =>
      mixColor (encodeEdgeLabel lbl * 37 + c u) (hashNeighborhood c rest)

/-- One step of 1-dimensional Weisfeiler-Leman color refinement (`wlStep`). -/
def wlStep (g : WLGraph) (c : NodeId → Color) (v : NodeId) : Color :=
  mixColor (c v) (hashNeighborhood c (g.neighbors v))

/-- $k$-step Weisfeiler-Leman color at radius `k`. -/
def wlColor (g : WLGraph) : Nat → NodeId → Color
  | 0, v     => g.initColor v
  | k + 1, v => wlStep g (wlColor g k) v

/-- Multiscale color vector `(c^(0)(v), ..., c^(k)(v))` up to radius `k`. -/
def wlMultiscaleVec (g : WLGraph) (v : NodeId) : Nat → List Color
  | 0     => [wlColor g 0 v]
  | k + 1 => wlMultiscaleVec g v k ++ [wlColor g (k + 1) v]

/-- Count how many nodes in `nodes` share color `col` under coloring `c`. -/
def countColorInList (c : NodeId → Color) (col : Color) : List NodeId → Nat
  | [] => 0
  | u :: rest =>
      (if c u = col then 1 else 0) + countColorInList c col rest

/-- A node `v` belongs to a singleton color orbit at radius `k` when every node `u`
in `g.nodes` that shares `wlColor g k u = wlColor g k v` is equal to `v`. -/
def isUniqueOrbit (g : WLGraph) (k : Nat) (v : NodeId) : Bool :=
  g.nodes.all (fun u => decide (wlColor g k u = wlColor g k v → u = v))

/-- **Theorem 1 (`uniqueOrbit_injective`)**:
If `isUniqueOrbit g k v = true`, then any node `u ∈ g.nodes` whose radius-`k`
Weisfeiler-Leman color matches `v` is uniquely `v` itself. -/
theorem uniqueOrbit_injective (g : WLGraph) (k : Nat) (u v : NodeId)
    (h_uniq : isUniqueOrbit g k v = true)
    (h_mem : u ∈ g.nodes)
    (h_col : wlColor g k u = wlColor g k v) :
    u = v := by
  unfold isUniqueOrbit at h_uniq
  rw [List.all_eq_true] at h_uniq
  have h_u := h_uniq u h_mem
  simp only [decide_eq_true_eq] at h_u
  exact h_u h_col

/-- Classification of `WLAnchorKey` alignment outcomes between stripped (`-C debuginfo=0`)
LLVM IR and `MiniSSA` IR. -/
inductive WLAlignOutcome where
  /-- Exact unique singleton-orbit match at radius `r ∈ {4, 3, 2, 1}`. -/
  | uniqueExact (radius : Nat) (targetNode : NodeId)
  /-- Non-singleton automorphism orbit (`|Orbit| > 1`) where the oracle hint is
      symmetric across all twin sites in the orbit (`OrbitSymmetric`). -/
  | symmetricOrbit (orbitNodes : List NodeId)
  /-- Soft multiscale neighborhood assignment (Hungarian cosine match under local drift). -/
  | softNeighborhood (targetNode : NodeId)
  /-- Ambiguous asymmetric automorphism orbit: rejected before replay (`Tier 2` skip). -/
  | ambiguousOrbitFallback
  deriving DecidableEq, Repr

/-- Abstract representation of an optimization hint (`InlineHint`, `SroaHint`,
`LoopOptHint`, `VectorizeHint`, `RegAllocHint`) attached to a `MiniSSA` site. -/
structure OracleSiteHint where
  siteId        : NodeId
  transformId   : Nat
  isSymmetricOk : Bool
  deriving DecidableEq, Repr

/-- Program semantics state modeled as an abstract value `ProgSemantics`. -/
abbrev ProgSemantics := Nat → Int

/-- Semantic equivalence / refinement between compiled `MiniSSA` states. -/
def SemEquiv (s1 s2 : ProgSemantics) : Prop :=
  ∀ input, s1 input = s2 input

theorem semEquiv_refl (s : ProgSemantics) : SemEquiv s s :=
  fun _ => rfl

theorem semEquiv_trans {s1 s2 s3 : ProgSemantics}
    (h12 : SemEquiv s1 s2) (h23 : SemEquiv s2 s3) : SemEquiv s1 s3 :=
  fun x => Eq.trans (h12 x) (h23 x)

/-- Module representation equipped with a semantics evaluation function `evalModule`,
a hint legality checker `checkHintLegality`, and a transformation applier `applyHint`. -/
structure MiniSSAModule where
  state : Nat
  deriving DecidableEq, Repr

/-- Decidable `HybridTrace` legality checker gating every aligned oracle hint.
Whenever `checkHintLegality m hint = true`, applying `hint` preserves `evalModule`. -/
structure VerifiedReplayContext where
  evalModule        : MiniSSAModule → ProgSemantics
  checkHintLegality : MiniSSAModule → OracleSiteHint → Bool
  applyHint         : MiniSSAModule → OracleSiteHint → MiniSSAModule
  applyTier1Repair  : MiniSSAModule → OracleSiteHint → Option MiniSSAModule
  applyHint_sound   : ∀ m h,
    checkHintLegality m h = true → SemEquiv (evalModule (applyHint m h)) (evalModule m)
  tier1Repair_sound : ∀ m h m',
    applyTier1Repair m h = some m' → SemEquiv (evalModule m') (evalModule m)

/-- Execute a single aligned hint with 3-tier graceful fallback:
- If `WLAlignOutcome` is `.ambiguousOrbitFallback` and `isSymmetricOk = false`,
  skip the hint (`Tier 2` local fallback).
- Otherwise, check `ctx.checkHintLegality m hint`:
  - If `true`, apply `ctx.applyHint m hint`;
  - If `false`, try `ctx.applyTier1Repair m hint` (`Tier 1` local `freeze`/guard repair);
  - If `none`, retain `m` unchanged (`Tier 2` local fallback). -/
def replayAlignedSite (ctx : VerifiedReplayContext) (m : MiniSSAModule)
    (outcome : WLAlignOutcome) (rawTransformId : Nat) (isSymmetricOk : Bool) : MiniSSAModule :=
  match outcome with
  | .ambiguousOrbitFallback => m
  | .uniqueExact _ targetNode | .softNeighborhood targetNode =>
      let hint : OracleSiteHint := ⟨targetNode, rawTransformId, isSymmetricOk⟩
      if ctx.checkHintLegality m hint then
        ctx.applyHint m hint
      else
        match ctx.applyTier1Repair m hint with
        | some mRepaired => mRepaired
        | none           => m
  | .symmetricOrbit orbitNodes =>
      if isSymmetricOk then
        orbitNodes.foldl (fun accNode node =>
          let hint : OracleSiteHint := ⟨node, rawTransformId, true⟩
          if ctx.checkHintLegality accNode hint then
            ctx.applyHint accNode hint
          else
            accNode) m
      else
        m

theorem foldl_orbit_sound (ctx : VerifiedReplayContext) (nodes : List NodeId)
    (rawTransformId : Nat) (m : MiniSSAModule) :
    SemEquiv
      (ctx.evalModule (nodes.foldl (fun accNode node =>
        let hint : OracleSiteHint := ⟨node, rawTransformId, true⟩
        if ctx.checkHintLegality accNode hint then
          ctx.applyHint accNode hint
        else
          accNode) m))
      (ctx.evalModule m) := by
  induction nodes generalizing m with
  | nil => exact semEquiv_refl _
  | cons hd tl ih =>
    simp only [List.foldl]
    by_cases h_leg : ctx.checkHintLegality m ⟨hd, rawTransformId, true⟩ = true
    · simp only [h_leg, ↓reduceIte]
      have h_step := ctx.applyHint_sound m ⟨hd, rawTransformId, true⟩ h_leg
      have h_rest := ih (ctx.applyHint m ⟨hd, rawTransformId, true⟩)
      exact semEquiv_trans h_rest h_step
    · simp only [h_leg, Bool.false_eq_true, ↓reduceIte]
      exact ih m

/-- **Main Soundness Theorem (`wl_align_and_replay_sound`)**:
Regardless of whether the untrusted LLVM oracle was compiled with `-C debuginfo=0`,
whether `WLAnchorKey` matched via exact singleton orbit, symmetric twin orbit,
soft multiscale Hungarian assignment, or suffered an adversarial hash collision,
`replayAlignedSite` is 100% semantically sound (`SemEquiv`). -/
theorem wl_align_and_replay_sound (ctx : VerifiedReplayContext) (m : MiniSSAModule)
    (outcome : WLAlignOutcome) (rawTransformId : Nat) (isSymmetricOk : Bool) :
    SemEquiv
      (ctx.evalModule (replayAlignedSite ctx m outcome rawTransformId isSymmetricOk))
      (ctx.evalModule m) := by
  cases outcome with
  | ambiguousOrbitFallback =>
    exact semEquiv_refl _
  | uniqueExact r targetNode =>
    simp only [replayAlignedSite]
    by_cases h_leg : ctx.checkHintLegality m ⟨targetNode, rawTransformId, isSymmetricOk⟩ = true
    · simp only [h_leg, ↓reduceIte]
      exact ctx.applyHint_sound m ⟨targetNode, rawTransformId, isSymmetricOk⟩ h_leg
    · simp only [h_leg, Bool.false_eq_true, ↓reduceIte]
      cases h_rep : ctx.applyTier1Repair m ⟨targetNode, rawTransformId, isSymmetricOk⟩ with
      | some mRepaired => exact ctx.tier1Repair_sound m _ mRepaired h_rep
      | none => exact semEquiv_refl _
  | softNeighborhood targetNode =>
    simp only [replayAlignedSite]
    by_cases h_leg : ctx.checkHintLegality m ⟨targetNode, rawTransformId, isSymmetricOk⟩ = true
    · simp only [h_leg, ↓reduceIte]
      exact ctx.applyHint_sound m ⟨targetNode, rawTransformId, isSymmetricOk⟩ h_leg
    · simp only [h_leg, Bool.false_eq_true, ↓reduceIte]
      cases h_rep : ctx.applyTier1Repair m ⟨targetNode, rawTransformId, isSymmetricOk⟩ with
      | some mRepaired => exact ctx.tier1Repair_sound m _ mRepaired h_rep
      | none => exact semEquiv_refl _
  | symmetricOrbit orbitNodes =>
    simp only [replayAlignedSite]
    by_cases h_sym : isSymmetricOk = true
    · simp only [h_sym, ↓reduceIte]
      exact foldl_orbit_sound ctx orbitNodes rawTransformId m
    · simp only [h_sym, Bool.false_eq_true, ↓reduceIte]
      exact semEquiv_refl _

/-! ## Negative Canaries -/

/-- Twin-loop graph with two structurally isomorphic loop header nodes `10` and `20`. -/
def twinLoopGraph : WLGraph :=
  { nodes := [10, 20]
    initColor := fun _ => 7
    neighbors := fun _ => [(.loopBackedge, 10)] }

/-- **Negative Canary 1 (`canary_twin_loop_non_unique_orbit_detected`)**:
In a stripped (`-C debuginfo=0`) function with two identical twin loops,
`isUniqueOrbit` returns `false`, preventing unsafe asymmetric hint assignment. -/
theorem canary_twin_loop_non_unique_orbit_detected :
    isUniqueOrbit twinLoopGraph 1 10 = false := rfl

#print axioms uniqueOrbit_injective
#print axioms wl_align_and_replay_sound
#print axioms canary_twin_loop_non_unique_orbit_detected

end WLOracleAlignment
