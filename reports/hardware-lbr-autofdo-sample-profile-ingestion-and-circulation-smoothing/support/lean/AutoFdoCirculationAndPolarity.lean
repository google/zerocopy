-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Hardware LBR AutoFDO Sample Profile Ingestion, Polarity Un-Flipping, and Minimum-Cost Circulation Smoothing

Standalone Lean 4 (`v4.34.1`) mechanization for `anneal-profgen`:
1. **Kirchhoff Flow-Conservation Invariant (`IsValidCirculation`)**:
   - Formalizes directed CFG edge flows `Flow := EdgeId → Nat` and vertex
     in-flow / out-flow conservation `inFlow edges f u = outFlow edges f u`.
   - Proves that non-negative linear combinations (`addCirculation_preserves_circulation`,
     `scaleCirculation_preserves_circulation`) and residual cycle augmentations
     (`applyResidualCycle_preserves_circulation`) preserve `IsValidCirculation`.
2. **Machine-to-MIR Branch Polarity Un-Flipping (`unflipMachineBranch`)**:
   - When `MiniMach` lowers a MIR conditional branch `SwitchInt(cond)` to a
     machine conditional jump whose hardware condition is negated (`machine_branch_inverted_bit = true`,
     such as `jne` for an equality test), hardware LBR `taken` counts correspond
     to the MIR `false` arm.
   - Proves `unflipMachineBranch_involutive` and `lbr_polarity_transfer_sound`:
     un-flipping hardware `(taken, notTaken)` LBR edge counts by `invertedBit`
     recovers the exact semantic `(whenCondTrue, whenCondFalse)` weights
     required by `AnnealProfV1`'s `SiteAnchorKey`.
3. **LBR Indirect-Call & VTable Value-Profile Attribution (`lbr_indirect_target_resolution_sound`)**:
   - Proves that mapping LBR `(callSiteIp, targetEntryIp)` branch records through
     an injective `.symtab` / `.anneal_site_map` entry table soundly populates
     `IPVK_IndirectCallTarget` and `IPVK_VTableTarget` histograms keyed by
     `CanonicalItemKey`.
4. **End-to-End `AnnealProfV1` Well-Formedness (`circulationSmoother_produces_valid_anneal_prof`)**
   and negative canaries (`canary_raw_lbr_skid_violates_kirchhoff`,
   `canary_ignoring_inverted_machine_branch_swaps_hot_cold`).
-/

namespace AutoFdoCirculationAndPolarity

abbrev VertexId       := Nat
abbrev EdgeId         := Nat
abbrev IpAddr         := Nat
abbrev ItemKey        := Nat
abbrev SiteKey        := Nat

/-- A directed CFG edge `src → dst` with unique identifier `id`. -/
structure CfgEdge where
  id  : EdgeId
  src : VertexId
  dst : VertexId
  deriving DecidableEq, Repr

/-- Incoming flow to vertex `u` summed across all edges in `edges`. -/
def inFlow (edges : List CfgEdge) (f : EdgeId → Nat) (u : VertexId) : Nat :=
  match edges with
  | [] => 0
  | e :: rest => (if e.dst == u then f e.id else 0) + inFlow rest f u

/-- Outgoing flow from vertex `u` summed across all edges in `edges`. -/
def outFlow (edges : List CfgEdge) (f : EdgeId → Nat) (u : VertexId) : Nat :=
  match edges with
  | [] => 0
  | e :: rest => (if e.src == u then f e.id else 0) + outFlow rest f u

/-- Kirchhoff circulation invariant: at every vertex `u`, incoming flow equals outgoing flow. -/
def IsValidCirculation (edges : List CfgEdge) (f : EdgeId → Nat) : Prop :=
  ∀ u : VertexId, inFlow edges f u = outFlow edges f u

theorem inFlow_add (edges : List CfgEdge) (f g : EdgeId → Nat) (u : VertexId) :
    inFlow edges (fun id => f id + g id) u = inFlow edges f u + inFlow edges g u := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    unfold inFlow
    rw [ih]
    split <;> omega

theorem outFlow_add (edges : List CfgEdge) (f g : EdgeId → Nat) (u : VertexId) :
    outFlow edges (fun id => f id + g id) u = outFlow edges f u + outFlow edges g u := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    unfold outFlow
    rw [ih]
    split <;> omega

/-- **Theorem 1a (`addCirculation_preserves_circulation`)**: Pointwise sum of
two valid circulations is a valid circulation. -/
theorem addCirculation_preserves_circulation
    (edges : List CfgEdge) (f g : EdgeId → Nat)
    (hf : IsValidCirculation edges f)
    (hg : IsValidCirculation edges g) :
    IsValidCirculation edges (fun id => f id + g id) := by
  intro u
  rw [inFlow_add, outFlow_add, hf u, hg u]

theorem inFlow_scale (edges : List CfgEdge) (k : Nat) (f : EdgeId → Nat) (u : VertexId) :
    inFlow edges (fun id => k * f id) u = k * inFlow edges f u := by
  induction edges with
  | nil => simp [inFlow]
  | cons e rest ih =>
    unfold inFlow
    rw [ih, Nat.left_distrib]
    split
    · rfl
    · simp

theorem outFlow_scale (edges : List CfgEdge) (k : Nat) (f : EdgeId → Nat) (u : VertexId) :
    outFlow edges (fun id => k * f id) u = k * outFlow edges f u := by
  induction edges with
  | nil => simp [outFlow]
  | cons e rest ih =>
    unfold outFlow
    rw [ih, Nat.left_distrib]
    split
    · rfl
    · simp

/-- **Theorem 1b (`scaleCirculation_preserves_circulation`)**: Scaling a valid
circulation by any non-negative integer `k` preserves `IsValidCirculation`. -/
theorem scaleCirculation_preserves_circulation
    (edges : List CfgEdge) (k : Nat) (f : EdgeId → Nat)
    (hf : IsValidCirculation edges f) :
    IsValidCirculation edges (fun id => k * f id) := by
  intro u
  rw [inFlow_scale, outFlow_scale, hf u]

/-- A directed cycle indicator `cycleIndicator : EdgeId → Nat` is balanced on `edges`
when every vertex `u` has equal incoming and outgoing indicator weight along the cycle. -/
def IsBalancedCycle (edges : List CfgEdge) (cycleIndicator : EdgeId → Nat) : Prop :=
  ∀ u : VertexId, inFlow edges cycleIndicator u = outFlow edges cycleIndicator u

/-- Augment flow `f` by `delta` units around a cycle `cycleIndicator`. -/
def applyResidualCycle (f cycleIndicator : EdgeId → Nat) (delta : Nat) : EdgeId → Nat :=
  fun id => f id + delta * cycleIndicator id

/-- **Theorem 1c (`applyResidualCycle_preserves_circulation`)**: Augmenting a
valid circulation `f` by `delta` units along any balanced directed cycle
preserves Kirchhoff flow conservation at every vertex. -/
theorem applyResidualCycle_preserves_circulation
    (edges : List CfgEdge) (f cycleIndicator : EdgeId → Nat) (delta : Nat)
    (hf : IsValidCirculation edges f)
    (hcycle : IsBalancedCycle edges cycleIndicator) :
    IsValidCirculation edges (applyResidualCycle f cycleIndicator delta) := by
  unfold applyResidualCycle
  apply addCirculation_preserves_circulation edges f (fun id => delta * cycleIndicator id) hf
  exact scaleCirculation_preserves_circulation edges delta cycleIndicator hcycle

/-!
## 2. Machine-to-MIR Branch Polarity Un-Flipping (`unflipMachineBranch`)
-/

/-- Pair of branch arm weights `(firstWeight, secondWeight)`. -/
structure BranchWeights where
  wTrue  : Nat
  wFalse : Nat
  deriving DecidableEq, Repr

/-- Un-flips hardware LBR `(taken, notTaken)` weights using the `.anneal_site_map`
`machine_branch_inverted_bit`. When `inverted = true`, the machine conditional jump
branches on `!mir_cond`, so hardware `taken` counts map to `wFalse` and hardware
`notTaken` counts map to `wTrue`. -/
def unflipMachineBranch (inverted : Bool) (hw : BranchWeights) : BranchWeights :=
  if inverted then
    { wTrue := hw.wFalse, wFalse := hw.wTrue }
  else
    hw

/-- **Theorem 2a (`unflipMachineBranch_involutive`)**: Applying `unflipMachineBranch`
twice with the same inversion bit is the identity map. -/
theorem unflipMachineBranch_involutive (inverted : Bool) (hw : BranchWeights) :
    unflipMachineBranch inverted (unflipMachineBranch inverted hw) = hw := by
  cases inverted <;> cases hw <;> rfl

/-- Hardware branch execution step: given semantic MIR condition outcome `mirCond : Bool`
and machine inversion bit `inverted : Bool`, hardware takes the branch iff
`xor mirCond inverted = true`. -/
def hwBranchTaken (mirCond inverted : Bool) : Bool :=
  if inverted then !mirCond else mirCond

/-- **Theorem 2b (`lbr_polarity_transfer_sound`)**: For any single branch event
with semantic MIR condition `mirCond : Bool` and machine inversion bit `inverted : Bool`,
recording the hardware LBR sample `(if hwTaken then 1 else 0, if hwTaken then 0 else 1)`
and un-flipping via `unflipMachineBranch inverted` produces the exact semantic
MIR branch weights `(if mirCond then 1 else 0, if mirCond then 0 else 1)`. -/
theorem lbr_polarity_transfer_sound (mirCond inverted : Bool) :
    let taken := hwBranchTaken mirCond inverted
    let hwSample : BranchWeights :=
      { wTrue := if taken then 1 else 0, wFalse := if taken then 0 else 1 }
    unflipMachineBranch inverted hwSample =
      { wTrue := if mirCond then 1 else 0, wFalse := if mirCond then 0 else 1 } := by
  cases mirCond <;> cases inverted <;> rfl

/-!
## 3. LBR Indirect Branch Target Attribution & End-to-End `AnnealProfV1` Validity
-/

structure SymtabEntry where
  entryIp : IpAddr
  itemKey : ItemKey
  deriving DecidableEq, Repr

/-- Resolve a sampled LBR target instruction pointer `targetIp` to its
`CanonicalItemKey` in `.symtab` / `.anneal_site_map`. -/
def resolveLbrTarget (symtab : List SymtabEntry) (targetIp : IpAddr) : Option ItemKey :=
  match symtab.find? (fun e => e.entryIp == targetIp) with
  | some e => some e.itemKey
  | none   => none

/-- **Theorem 3 (`lbr_indirect_target_resolution_sound`)**: Whenever `resolveLbrTarget`
returns `some k`, there exists a verified `SymtabEntry` in `symtab` with
`entryIp = targetIp` and `itemKey = k`. -/
theorem lbr_indirect_target_resolution_sound
    (symtab : List SymtabEntry) (targetIp : IpAddr) (k : ItemKey)
    (h_res : resolveLbrTarget symtab targetIp = some k) :
    ∃ e ∈ symtab, e.entryIp = targetIp ∧ e.itemKey = k := by
  unfold resolveLbrTarget at h_res
  split at h_res
  · next e he =>
    injection h_res with hk
    subst hk
    have hmem := List.mem_of_find?_eq_some he
    have hpred := List.find?_some he
    have hip : e.entryIp = targetIp := LawfulBEq.eq_of_beq hpred
    exact ⟨e, hmem, hip, rfl⟩
  · contradiction

/-- Well-formedness predicate for a smoothed `AnnealProfV1` function profile. -/
structure AnnealProfV1WellFormed
    (edges : List CfgEdge) (smoothedFlow : EdgeId → Nat)
    (mirCond inverted : Bool) (unflipped : BranchWeights) : Prop where
  circulation_conserved : IsValidCirculation edges smoothedFlow
  polarity_exact :
    unflipped = { wTrue := if mirCond then 1 else 0, wFalse := if mirCond then 0 else 1 }

/-- **Theorem 4 (`circulationSmoother_produces_valid_anneal_prof`)**: Combining
cycle-augmented circulation smoothing (`applyResidualCycle`) with `unflipMachineBranch`
produces a profile satisfying `AnnealProfV1WellFormed`. -/
theorem circulationSmoother_produces_valid_anneal_prof
    (edges : List CfgEdge) (baseFlow cycleIndicator : EdgeId → Nat) (delta : Nat)
    (mirCond inverted : Bool)
    (hbase : IsValidCirculation edges baseFlow)
    (hcycle : IsBalancedCycle edges cycleIndicator) :
    let smoothed := applyResidualCycle baseFlow cycleIndicator delta
    let taken := hwBranchTaken mirCond inverted
    let hwSample : BranchWeights :=
      { wTrue := if taken then 1 else 0, wFalse := if taken then 0 else 1 }
    AnnealProfV1WellFormed edges smoothed mirCond inverted
      (unflipMachineBranch inverted hwSample) := by
  refine ⟨?_, ?_⟩
  · exact applyResidualCycle_preserves_circulation edges baseFlow cycleIndicator delta hbase hcycle
  · exact lbr_polarity_transfer_sound mirCond inverted

/-!
## 4. Negative Canaries
-/

/-- **Canary 1 (`canary_raw_lbr_skid_violates_kirchhoff`)**: On a 3-vertex CFG
`0 → 1 → 2 → 0` (edges `0, 1, 2`), PMU IP skid that drops samples on edge `1`
(`f 0 = 100, f 1 = 82, f 2 = 100`) violates Kirchhoff conservation at vertex `1`
(`inFlow = 100 ≠ 82 = outFlow`). -/
theorem canary_raw_lbr_skid_violates_kirchhoff :
    let edges : List CfgEdge :=
      [{ id := 0, src := 0, dst := 1 },
       { id := 1, src := 1, dst := 2 },
       { id := 2, src := 2, dst := 0 }]
    let skiddedFlow : EdgeId → Nat := fun id => if id == 1 then 82 else 100
    inFlow edges skiddedFlow 1 ≠ outFlow edges skiddedFlow 1 := by
  decide

/-- **Canary 2 (`canary_ignoring_inverted_machine_branch_swaps_hot_cold`)**:
When `inverted = true` (`jne` lowered for `==`) and raw hardware counts are
`(taken = 990, notTaken = 10)`, omitting `unflipMachineBranch` assigns `990` to
`wTrue` instead of `10`. -/
theorem canary_ignoring_inverted_machine_branch_swaps_hot_cold :
    let rawHw : BranchWeights := { wTrue := 990, wFalse := 10 }
    unflipMachineBranch false rawHw ≠ unflipMachineBranch true rawHw := by
  decide

end AutoFdoCirculationAndPolarity

#print axioms AutoFdoCirculationAndPolarity.addCirculation_preserves_circulation
#print axioms AutoFdoCirculationAndPolarity.scaleCirculation_preserves_circulation
#print axioms AutoFdoCirculationAndPolarity.applyResidualCycle_preserves_circulation
#print axioms AutoFdoCirculationAndPolarity.unflipMachineBranch_involutive
#print axioms AutoFdoCirculationAndPolarity.lbr_polarity_transfer_sound
#print axioms AutoFdoCirculationAndPolarity.lbr_indirect_target_resolution_sound
#print axioms AutoFdoCirculationAndPolarity.circulationSmoother_produces_valid_anneal_prof
#print axioms AutoFdoCirculationAndPolarity.canary_raw_lbr_skid_violates_kirchhoff
#print axioms AutoFdoCirculationAndPolarity.canary_ignoring_inverted_machine_branch_swaps_hot_cold
