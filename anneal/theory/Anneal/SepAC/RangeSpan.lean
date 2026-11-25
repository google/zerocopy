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
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Anneal.PTree
public import Anneal.Core.SepPCM
public import Anneal.MirMemComp.Memory
public import Anneal.SepAC.Normalize

public section

/-!
# Lithium `PTree` Keyed Framing & $O(1)$ Symbolic `ByteRange` (`RangeSpan`)

Combines canonical `Anneal.PTree` separation-algebra framing (inspired by
Sammler et al.'s RefinedC/Lithium deterministic non-backtracking framing) with
$O(1)$ symbolic byte-range splitting (`split_at_mut` without materializing $N$
per-byte points-to atoms), explicit bridges to `Anneal.Core.SepPCM`, and a
direct `Trusted.MirSemantics.MemoryState` disjoint-write frame bridge
(complementing `Anneal.ByteRun.readBytes_after_writeBytes_disjoint` with
`AllocBytesAt` slice-ownership splitting and `execWriteBytes` framing):

1. **Canonical `PTree` Partial Commutative Monoid & Lithium Keyed Framing:**
   - Proves `ptree_disjoint_symm`, `ptree_union_assoc`,
     `ptree_disjoint_union_left_iff`, and `ptree_disjoint_union_right_iff`
     with zero axioms (`[]`).
   - Defines `PHeapProp α := PTree α → Prop`, `PHeapEntails`, `pheapEmp`,
     `pheapPointsTo`, and `pheapSepConj`, proving `pheapProp_sepACULaws`
     (connecting canonical `PTree` heaps directly into `Anneal.SepAC.Normalize`
     with zero permutation wrappers) and `not_affineEntails_pheapProp`, plus
     `coreSepProp_sepACULaws` bridging `Anneal.Core.SepProp`.
   - `LithiumTriple` (in-place footprint update preserving all disjoint frames,
     hence `dom post ⊆ dom req`), `ptree_set_lithiumTriple_exists` (concrete
     single-key `PTree.set` inhabitation), `lithiumTriple_union_disjoint`
     (combining disjoint triples), `lithiumFrame_of_diffWith`
     (zero-backtracking framing via `PTree.diffWith`), and
     `lithiumFrame_diamond_comm` (`PTree.union` commutation under
     `PTree.DisjointProp post₁ post₂`).
2. **$O(1)$ Symbolic `ByteRange` Algebra (`rangeSplit` / `rangeMerge`):**
   - `ByteRange` (`allocId`, `start`, `len`): constant-size slice descriptor
     independent of `len` (scaling flatly to `len = 1_000_000+`), bridged to
     `Anneal.Core.ByteRange` via `toCoreByteRange` / `ofCoreByteRange`
     (`ofCoreByteRange_toCore`, `toCoreByteRange_ofCore`).
   - `InRange`, `RangeDisjoint` (conservative for zero-length ranges),
     computable `rangeDisjointBool` + `rangeDisjointBool_iff`,
     `rangeDisjoint_symm`, and `rangeDisjoint_no_shared_offset`.
   - `rangeSplit`, `rangeMerge` (total adjacent-range combiner characterized by
     `rangeMerge_split`), `rangeSplit_disjoint`, `rangeSplit_covers_iff`,
     `rangeMerge_split`, and `rangeDisjoint_of_subrange`.
3. **`MemoryState` `AllocBytesAt` Split & Disjoint-Write Frame Bridge:**
   - `AllocBytesAt m r bs`: allocation `r.allocId` is live in `m`, in bounds
     for `[r.start, r.start + r.len)`, and its byte slice equals `bs`.
   - `ownRange_split_iff`: `AllocBytesAt m r bs ↔ AllocBytesAt m rL (bs.take k)
     ∧ AllocBytesAt m rR (bs.drop k)` for `k ≤ r.len`.
   - `allocBytesAt_frame_of_execWriteBytes_disjoint`: writing `newBytes` at any
     `rW` disjoint from `rF` via `Anneal.MirMemComp.execWriteBytes` preserves
     `AllocBytesAt m rF bsF` unconditionally—both across distinct allocations
     and across disjoint sub-ranges inside the same allocation.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.SepAC

open Trusted.MirAst Trusted.MirSemantics
open Anneal.PTree Anneal.MirMemComp

/-! ## Part I: `PTree` Partial Monoid, `PHeapProp`, & Lithium Framing -/

/-- Symmetry of `PTree.DisjointProp` (`[]` zero axioms). -/
theorem ptree_disjoint_symm {α : Type} {a b : PTree α}
    (h : PTree.DisjointProp a b) : PTree.DisjointProp b a := by
  intro k
  cases h k with
  | inl ha => exact Or.inr ha
  | inr hb => exact Or.inl hb

/-- Empty left disjointness for `PTree` (`[]` zero axioms). -/
theorem ptree_disjoint_empty_left {α : Type} (t : PTree α) :
    PTree.DisjointProp PTree.empty t :=
  fun _ => Or.inl rfl

/-- Empty right disjointness for `PTree` (`[]` zero axioms). -/
theorem ptree_disjoint_empty_right {α : Type} (t : PTree α) :
    PTree.DisjointProp t PTree.empty :=
  fun _ => Or.inr rfl

/-- Associativity of `PTree.union` (`[]` zero axioms). -/
theorem ptree_union_assoc {α : Type} (a b c : PTree α) :
    PTree.union (PTree.union a b) c = PTree.union a (PTree.union b c) := by
  apply ptree_eq_of_get
  intro k
  rw [ptree_get_union, ptree_get_union, ptree_get_union, ptree_get_union]
  cases a.get k with
  | some _ => rfl
  | none =>
    cases b.get k <;> rfl

/-- Disjointness with a left `PTree.union` splits conjunctively (`[]` zero
axioms). -/
theorem ptree_disjoint_union_left_iff {α : Type} (a b c : PTree α) :
    PTree.DisjointProp (PTree.union a b) c ↔
      PTree.DisjointProp a c ∧ PTree.DisjointProp b c := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · cases h k with
      | inr hc => exact Or.inr hc
      | inl hab =>
        rw [ptree_get_union] at hab
        cases ha : a.get k with
        | none => exact Or.inl rfl
        | some _ =>
          rw [ha] at hab
          nomatch hab
    · cases h k with
      | inr hc => exact Or.inr hc
      | inl hab =>
        rw [ptree_get_union] at hab
        cases ha : a.get k with
        | some _ =>
          rw [ha] at hab
          nomatch hab
        | none =>
          rw [ha] at hab
          exact Or.inl hab
  · intro h k
    cases h.1 k with
    | inr hc => exact Or.inr hc
    | inl ha =>
      cases h.2 k with
      | inr hc => exact Or.inr hc
      | inl hb =>
        left
        rw [ptree_get_union, ha, hb]

/-- Disjointness with a right `PTree.union` splits conjunctively (`[]` zero
axioms). -/
theorem ptree_disjoint_union_right_iff {α : Type} (a b c : PTree α) :
    PTree.DisjointProp a (PTree.union b c) ↔
      PTree.DisjointProp a b ∧ PTree.DisjointProp a c := by
  refine ⟨?_, ?_⟩
  · intro h
    have hSym :=
      (ptree_disjoint_union_left_iff b c a).mp (ptree_disjoint_symm h)
    exact ⟨ptree_disjoint_symm hSym.1, ptree_disjoint_symm hSym.2⟩
  · intro h
    exact ptree_disjoint_symm
      ((ptree_disjoint_union_left_iff b c a).mpr
        ⟨ptree_disjoint_symm h.1, ptree_disjoint_symm h.2⟩)

/-- Canonical separation-logic assertion over a keyed `PTree α` heap. -/
@[expose] def PHeapProp (α : Type) : Type :=
  PTree α → Prop

/-- Entailment between canonical `PHeapProp α` assertions. -/
@[expose] def PHeapEntails {α : Type} (P Q : PHeapProp α) : Prop :=
  ∀ h : PTree α, P h → Q h

/-- Empty `PTree` heap assertion (`h = PTree.empty`). -/
@[expose] def pheapEmp {α : Type} : PHeapProp α :=
  fun h => h = PTree.empty

/-- Single-key `PTree` points-to assertion (`h = PTree.singleton k v`). -/
@[expose] def pheapPointsTo {α : Type} (k : Pos) (v : α) : PHeapProp α :=
  fun h => h = PTree.singleton k v

/-- Separating conjunction over canonical `PTree α` heaps. -/
@[expose] def pheapSepConj {α : Type} (P Q : PHeapProp α) : PHeapProp α :=
  fun h =>
    ∃ h₁ h₂ : PTree α,
      PTree.DisjointProp h₁ h₂ ∧ PTree.union h₁ h₂ = h ∧ P h₁ ∧ Q h₂

/-- `PHeapProp α` with `pheapSepConj`, `pheapEmp`, and `PHeapEntails` satisfies
`SepACULaws` natively (`[]` zero axioms), plugging canonical `PTree` heaps
directly into `Anneal.SepAC.Normalize`'s reflective ACU normalizer and
`cancelAtoms` without permutation wrappers. -/
theorem pheapProp_sepACULaws (α : Type) :
    SepACULaws (@pheapSepConj α) (@pheapEmp α) (@PHeapEntails α) := by
  refine ⟨fun _ _ h => h, fun _ _ _ h12 h23 h hp => h23 h (h12 h hp),
    ?_, ?_, ?_, ?_⟩
  · intro F P Q hPQ h hSep
    cases hSep with
    | intro h1 hR =>
      cases hR with
      | intro h2 hC =>
        exact ⟨h1, h2, hC.1, hC.2.1, hC.2.2.1, hPQ h2 hC.2.2.2⟩
  · intro P Q R
    refine ⟨?_, ?_⟩
    · intro h hL
      cases hL with
      | intro h12 hR1 =>
        cases hR1 with
        | intro h3 hC1 =>
          cases hC1.2.2.1 with
          | intro h1 hR2 =>
            cases hR2 with
            | intro h2 hC2 =>
              have hD12_3 : PTree.DisjointProp (PTree.union h1 h2) h3 := by
                rw [hC2.2.1]
                exact hC1.1
              have hSplits := (ptree_disjoint_union_left_iff h1 h2 h3).mp hD12_3
              have hD1_23 : PTree.DisjointProp h1 (PTree.union h2 h3) :=
                (ptree_disjoint_union_right_iff h1 h2 h3).mpr
                  ⟨hC2.1, hSplits.1⟩
              have hEq : PTree.union h1 (PTree.union h2 h3) = h := by
                rw [← ptree_union_assoc h1 h2 h3, hC2.2.1, hC1.2.1]
              exact ⟨h1, PTree.union h2 h3, hD1_23, hEq, hC2.2.2.1,
                ⟨h2, h3, hSplits.2, rfl, hC2.2.2.2, hC1.2.2.2⟩⟩
    · intro h hR
      cases hR with
      | intro h1 hR1 =>
        cases hR1 with
        | intro h23 hC1 =>
          cases hC1.2.2.2 with
          | intro h2 hR2 =>
            cases hR2 with
            | intro h3 hC2 =>
              have hD1_23 : PTree.DisjointProp h1 (PTree.union h2 h3) := by
                rw [hC2.2.1]
                exact hC1.1
              have hSplits :=
                (ptree_disjoint_union_right_iff h1 h2 h3).mp hD1_23
              have hD12_3 : PTree.DisjointProp (PTree.union h1 h2) h3 :=
                (ptree_disjoint_union_left_iff h1 h2 h3).mpr
                  ⟨hSplits.2, hC2.1⟩
              have hEq : PTree.union (PTree.union h1 h2) h3 = h := by
                rw [ptree_union_assoc h1 h2 h3, hC2.2.1, hC1.2.1]
              exact ⟨PTree.union h1 h2, h3, hD12_3, hEq,
                ⟨h1, h2, hSplits.1, rfl, hC1.2.2.1, hC2.2.2.1⟩,
                hC2.2.2.2⟩
  · intro P Q
    have hOneDir :
        ∀ (A B : PHeapProp α),
          PHeapEntails (pheapSepConj A B) (pheapSepConj B A) := by
      intro A B h hAB
      cases hAB with
      | intro h1 hR =>
        cases hR with
        | intro h2 hC =>
          refine ⟨h2, h1, ptree_disjoint_symm hC.1, ?_, hC.2.2.2, hC.2.2.1⟩
          rw [ptree_union_comm_of_disjoint (ptree_disjoint_symm hC.1)]
          exact hC.2.1
    exact ⟨hOneDir P Q, hOneDir Q P⟩
  · intro P
    refine ⟨?_, ?_⟩
    · intro h hPE
      cases hPE with
      | intro h1 hR =>
        cases hR with
        | intro h2 hC =>
          have h2Emp : h2 = PTree.empty := hC.2.2.2
          have hEq : h1 = h := by
            rw [h2Emp, ptree_union_empty_right h1] at hC
            exact hC.2.1
          rw [← hEq]
          exact hC.2.2.1
    · intro h hP
      exact ⟨h, PTree.empty, ptree_disjoint_empty_right h,
        ptree_union_empty_right h, hP, rfl⟩

/-- `PHeapProp α` is strictly linear (not affine) whenever `α` is inhabited
(`[]` zero axioms). -/
theorem not_affineEntails_pheapProp {α : Type} (v₀ : α) :
    ¬ AffineEntails (@pheapEmp α) (@PHeapEntails α) := by
  intro hAff
  have hEq : PTree.singleton Pos.xH v₀ = PTree.empty :=
    hAff (pheapPointsTo Pos.xH v₀) (PTree.singleton Pos.xH v₀) rfl
  have hGet : (PTree.singleton Pos.xH v₀).get Pos.xH =
      (PTree.empty : PTree α).get Pos.xH :=
    congrArg (fun t => t.get Pos.xH) hEq
  nomatch hGet

/-- Bridge from `Anneal.Core.SepProp M` (`Anneal.Core.SepPCM`) into
`SepACULaws` (`[]` zero axioms). -/
theorem coreSepProp_sepACULaws {M : Type} (pcm : Anneal.Core.ExplPCM M) :
    SepACULaws (Anneal.Core.sepConj pcm) (Anneal.Core.sepEmp pcm)
      Anneal.Core.SepEntails where
  refl := Anneal.Core.SepEntails.refl
  trans _ _ _ h1 h2 := Anneal.Core.SepEntails.trans h1 h2
  monoRight _ _ _ h :=
    Anneal.Core.sepConj_mono pcm (Anneal.Core.SepEntails.refl _) h
  assoc P Q R :=
    ⟨fun m hm => (Anneal.Core.sepConj_assoc pcm P Q R m).mp hm,
     fun m hm => (Anneal.Core.sepConj_assoc pcm P Q R m).mpr hm⟩
  comm P Q :=
    ⟨fun m hm => (Anneal.Core.sepConj_comm pcm P Q m).mp hm,
     fun m hm => (Anneal.Core.sepConj_comm pcm P Q m).mpr hm⟩
  rightUnit P :=
    ⟨fun m hm => (Anneal.Core.sepConj_emp_right pcm P m).mp hm,
     fun m hm => (Anneal.Core.sepConj_emp_right pcm P m).mpr hm⟩

/-- Local in-place framed transition over a canonical `PTree α` context:
preserves every disjoint frame `rem` while transforming `req` into `post`.
Because `PTree.DisjointProp post rem` holds for every `rem` disjoint from
`req`, `LithiumTriple` describes in-place footprint updates (`dom post ⊆ dom
req`); allocating fresh keys requires a separate rule. -/
@[expose] def LithiumTriple {α : Type} (req post : PTree α)
    (step : PTree α → Option (PTree α)) : Prop :=
  ∀ rem : PTree α,
    PTree.DisjointProp req rem →
    PTree.DisjointProp post rem ∧
      step (PTree.union req rem) = some (PTree.union post rem)

private theorem posBeq_refl_rs : ∀ p : Pos, Pos.beq p p = true
  | .xH => rfl
  | .xO q => posBeq_refl_rs q
  | .xI q => posBeq_refl_rs q

private theorem posEq_of_beq_true_rs :
    ∀ {p q : Pos}, Pos.beq p q = true → p = q
  | .xH, .xH, _ => rfl
  | .xH, .xO _, h => Bool.noConfusion h
  | .xH, .xI _, h => Bool.noConfusion h
  | .xO _, .xH, h => Bool.noConfusion h
  | .xO _, .xI _, h => Bool.noConfusion h
  | .xI _, .xH, h => Bool.noConfusion h
  | .xI _, .xO _, h => Bool.noConfusion h
  | .xO _, .xO _, h => congrArg Pos.xO (posEq_of_beq_true_rs h)
  | .xI _, .xI _, h => congrArg Pos.xI (posEq_of_beq_true_rs h)

/-- Concrete `LithiumTriple` inhabitation theorem (`[propext]` only) for an
in-place single-key `PTree.set` update `k ↦ v₁` to `k ↦ v₂`. -/
theorem ptree_set_lithiumTriple_exists {α : Type} (eqB : α → α → Bool)
    (hRefl : ∀ x : α, eqB x x = true) (k : Pos) (v₁ v₂ : α) :
    ∃ step : PTree α → Option (PTree α),
      LithiumTriple (PTree.singleton k v₁) (PTree.singleton k v₂) step := by
  let step : PTree α → Option (PTree α) := fun ctx =>
    match ctx.get k with
    | none => none
    | some v =>
      match eqB v v₁ with
      | true => some (ctx.set k v₂)
      | false => none
  refine ⟨step, ?_⟩
  intro rem hDisj
  have hRemK : rem.get k = none := by
    cases hDisj k with
    | inl hS =>
      dsimp only [PTree.singleton] at hS
      rw [ptree_get_set_same] at hS
      nomatch hS
    | inr hR => exact hR
  refine ⟨?_, ?_⟩
  · intro k'
    cases hEq : Pos.beq k k' with
    | true =>
      have hkEq : k = k' := posEq_of_beq_true_rs hEq
      rw [← hkEq]
      exact Or.inr hRemK
    | false =>
      have hkNe : k ≠ k' := fun heq => by
        rw [heq, posBeq_refl_rs] at hEq
        exact Bool.noConfusion hEq
      left
      dsimp only [PTree.singleton]
      rw [ptree_get_set_other PTree.empty k k' v₂ hkNe, ptree_get_empty]
  · dsimp only [step]
    rw [ptree_get_union]
    dsimp only [PTree.singleton]
    rw [ptree_get_set_same]
    dsimp only
    rw [hRefl v₁]
    dsimp only
    apply congrArg some
    apply ptree_eq_of_get
    intro k'
    cases hEq : Pos.beq k k' with
    | true =>
      have hkEq : k = k' := posEq_of_beq_true_rs hEq
      rw [← hkEq, ptree_get_set_same, ptree_get_union, ptree_get_set_same]
    | false =>
      have hkNe : k ≠ k' := fun heq => by
        rw [heq, posBeq_refl_rs] at hEq
        exact Bool.noConfusion hEq
      rw [ptree_get_set_other _ k k' v₂ hkNe, ptree_get_union,
        ptree_get_union, ptree_get_set_other PTree.empty k k' v₁ hkNe,
        ptree_get_set_other PTree.empty k k' v₂ hkNe, ptree_get_empty]

/-- Sequential composition of two `Option`-returning `PTree` transitions. -/
@[expose] def ptreeBindStep {α : Type}
    (step₁ step₂ : PTree α → Option (PTree α)) (ctx : PTree α) :
    Option (PTree α) :=
  match step₁ ctx with
  | none => none
  | some mid => step₂ mid

/-- Disjoint footprint composition of two `LithiumTriple`s (`[]` zero axioms):
combines `(req₁ → post₁)` and `(req₂ → post₂)` into a joint `LithiumTriple` on
`PTree.union req₁ req₂` and `PTree.union post₁ post₂`. -/
theorem lithiumTriple_union_disjoint {α : Type}
    {req₁ post₁ req₂ post₂ : PTree α}
    {step₁ step₂ : PTree α → Option (PTree α)}
    (hDreq : PTree.DisjointProp req₁ req₂)
    (hT1 : LithiumTriple req₁ post₁ step₁)
    (hT2 : LithiumTriple req₂ post₂ step₂) :
    LithiumTriple (PTree.union req₁ req₂) (PTree.union post₁ post₂)
      (ptreeBindStep step₁ step₂) := by
  intro rem hDisj
  have hParts := (ptree_disjoint_union_left_iff req₁ req₂ rem).mp hDisj
  have h1Rem :=
    (ptree_disjoint_union_right_iff req₁ req₂ rem).mpr ⟨hDreq, hParts.1⟩
  have hRes1 := hT1 (PTree.union req₂ rem) h1Rem
  have hP1Parts :=
    (ptree_disjoint_union_right_iff post₁ req₂ rem).mp hRes1.1
  have h2Rem :=
    (ptree_disjoint_union_right_iff req₂ post₁ rem).mpr
      ⟨ptree_disjoint_symm hP1Parts.1, hParts.2⟩
  have hRes2 := hT2 (PTree.union post₁ rem) h2Rem
  have hP2Parts :=
    (ptree_disjoint_union_right_iff post₂ post₁ rem).mp hRes2.1
  refine ⟨(ptree_disjoint_union_left_iff post₁ post₂ rem).mpr
      ⟨hP1Parts.2, hP2Parts.2⟩, ?_⟩
  dsimp only [ptreeBindStep]
  rw [ptree_union_assoc req₁ req₂ rem, hRes1.2]
  dsimp only
  rw [← ptree_union_assoc post₁ req₂ rem,
    ptree_union_comm_of_disjoint hP1Parts.1,
    ptree_union_assoc req₂ post₁ rem, hRes2.2,
    ← ptree_union_assoc post₂ post₁ rem,
    ptree_union_comm_of_disjoint hP2Parts.1,
    ptree_union_assoc post₁ post₂ rem]

/-- Lithium deterministic non-backtracking frame rule (`[]` zero axioms): a
single `PTree.diffWith eqB ctx req = some rem` pass splits `ctx = req ⊎ rem`
and lifts any `LithiumTriple req post step` onto `ctx` without context search.
-/
theorem lithiumFrame_of_diffWith {α : Type} (eqB : α → α → Bool)
    (hSoundEq : ∀ {x y : α}, eqB x y = true → x = y)
    {ctx req post rem : PTree α} {step : PTree α → Option (PTree α)}
    (hDiff : PTree.diffWith eqB ctx req = some rem)
    (hTr : LithiumTriple req post step) :
    PTree.DisjointProp req rem ∧
    PTree.DisjointProp post rem ∧
    step ctx = some (PTree.union post rem) := by
  have hSplit := ptree_diffWith_sound eqB hSoundEq hDiff
  have hRes := hTr rem hSplit.1
  rw [hSplit.2] at hRes
  exact ⟨hSplit.1, hRes.1, hRes.2⟩

/-- Canonical `PTree.union` commutation lemma (`[]` zero axioms): given
`PTree.DisjointProp post₁ post₂`, prepending `post₁` and `post₂` onto any
canonical remainder `rem` in either order yields identical tries (`=`). -/
theorem lithiumFrame_diamond_comm {α : Type}
    {post₁ post₂ rem : PTree α}
    (hD12 : PTree.DisjointProp post₁ post₂) :
    PTree.union post₁ (PTree.union post₂ rem) =
      PTree.union post₂ (PTree.union post₁ rem) := by
  rw [← ptree_union_assoc post₁ post₂ rem,
    ptree_union_comm_of_disjoint hD12,
    ptree_union_assoc post₂ post₁ rem]

/-! ## Part II: $O(1)$ Symbolic `ByteRange` Algebra (`split` & `merge`) -/

/-- Constant-size half-open byte range `[start, start + len)` inside allocation
`allocId`, representing arbitrarily large slices (`len = 1_000_000+`) in $O(1)$
space without per-byte points-to materialization. Converts losslessly to/from
`Anneal.Core.ByteRange` via `toCoreByteRange` and `ofCoreByteRange`. -/
structure ByteRange where
  allocId : AllocId
  start : Nat
  len : Nat

/-- Lossless conversion from `Anneal.SepAC.ByteRange` to
`Anneal.Core.ByteRange`. -/
@[expose] def toCoreByteRange (r : ByteRange) : Anneal.Core.ByteRange :=
  ⟨r.allocId, r.start, r.len⟩

/-- Lossless conversion from `Anneal.Core.ByteRange` to
`Anneal.SepAC.ByteRange`. -/
@[expose] def ofCoreByteRange (r : Anneal.Core.ByteRange) : ByteRange :=
  ⟨r.allocId, r.offset, r.len⟩

/-- Round-trip identity `ofCoreByteRange (toCoreByteRange r) = r` (`[]` zero
axioms). -/
theorem ofCoreByteRange_toCore (r : ByteRange) :
    ofCoreByteRange (toCoreByteRange r) = r := by
  cases r
  rfl

/-- Round-trip identity `toCoreByteRange (ofCoreByteRange r) = r` (`[]` zero
axioms). -/
theorem toCoreByteRange_ofCore (r : Anneal.Core.ByteRange) :
    toCoreByteRange (ofCoreByteRange r) = r := by
  cases r
  rfl

/-- Byte membership predicate: `(aid, off)` lies inside `r`. -/
@[expose] def InRange (r : ByteRange) (aid : AllocId) (off : Nat) : Prop :=
  r.allocId = aid ∧ r.start ≤ off ∧ off < r.start + r.len

/-- Disjointness between two `ByteRange`s: either distinct allocations or
non-overlapping half-open byte intervals (conservative for empty ranges: a
zero-length range inside an enclosing range is not declared disjoint). -/
@[expose] def RangeDisjoint (r₁ r₂ : ByteRange) : Prop :=
  r₁.allocId ≠ r₂.allocId ∨
    r₁.start + r₁.len ≤ r₂.start ∨
    r₂.start + r₂.len ≤ r₁.start

/-- Computable $O(1)$ boolean decision procedure for `RangeDisjoint` (`0`
`._unsafe_rec`). -/
@[expose] def rangeDisjointBool (r₁ r₂ : ByteRange) : Bool :=
  (!Nat.beq r₁.allocId r₂.allocId) ||
    Nat.ble (r₁.start + r₁.len) r₂.start ||
    Nat.ble (r₂.start + r₂.len) r₁.start

private theorem natBeq_refl_rs : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | n + 1 => natBeq_refl_rs n

private theorem natEq_of_beq_rs : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq_rs h)

private theorem natLe_of_ble_rs : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, b, _ => Nat.zero_le b
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (natLe_of_ble_rs h)

private theorem natBle_of_le_rs : ∀ {a b : Nat}, a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ a, Nat.succ b, h =>
    @natBle_of_le_rs a b (Nat.le_of_succ_le_succ h)

/-- Boolean reflection equivalence
`rangeDisjointBool r₁ r₂ = true ↔ RangeDisjoint r₁ r₂` (`[]` zero axioms). -/
theorem rangeDisjointBool_iff (r₁ r₂ : ByteRange) :
    rangeDisjointBool r₁ r₂ = true ↔ RangeDisjoint r₁ r₂ := by
  dsimp only [rangeDisjointBool, RangeDisjoint]
  refine ⟨?_, ?_⟩
  · intro h
    cases hId : Nat.beq r₁.allocId r₂.allocId with
    | false =>
      left
      intro hEq
      rw [hEq, natBeq_refl_rs] at hId
      exact Bool.noConfusion hId
    | true =>
      rw [hId] at h
      cases h12 : Nat.ble (r₁.start + r₁.len) r₂.start with
      | true => exact Or.inr (Or.inl (natLe_of_ble_rs h12))
      | false =>
        rw [h12] at h
        exact Or.inr (Or.inr (natLe_of_ble_rs h))
  · intro h
    cases h with
    | inl hNe =>
      cases hId : Nat.beq r₁.allocId r₂.allocId with
      | false => rfl
      | true => exact False.elim (hNe (natEq_of_beq_rs hId))
    | inr hInt =>
      cases hInt with
      | inl h12 =>
        rw [natBle_of_le_rs h12]
        cases Nat.beq r₁.allocId r₂.allocId <;> rfl
      | inr h21 =>
        rw [natBle_of_le_rs h21]
        cases Nat.beq r₁.allocId r₂.allocId <;>
          cases Nat.ble (r₁.start + r₁.len) r₂.start <;> rfl

/-- Symmetry of `RangeDisjoint` (`[]` zero axioms). -/
theorem rangeDisjoint_symm {r₁ r₂ : ByteRange} (h : RangeDisjoint r₁ r₂) :
    RangeDisjoint r₂ r₁ := by
  cases h with
  | inl hNe => exact Or.inl (fun heq => hNe heq.symm)
  | inr hInt =>
    cases hInt with
    | inl h12 => exact Or.inr (Or.inr h12)
    | inr h21 => exact Or.inr (Or.inl h21)

/-- Two disjoint `ByteRange`s share no `(allocId, offset)` byte (`[]` zero
axioms). -/
theorem rangeDisjoint_no_shared_offset {r₁ r₂ : ByteRange} {aid : AllocId}
    {off : Nat} (hD : RangeDisjoint r₁ r₂)
    (h1 : InRange r₁ aid off) (h2 : InRange r₂ aid off) : False := by
  cases hD with
  | inl hNe => exact hNe (Eq.trans h1.1 h2.1.symm)
  | inr hInt =>
    cases hInt with
    | inl h12 =>
      exact Nat.not_lt_of_ge (Nat.le_trans h12 h2.2.1) h1.2.2
    | inr h21 =>
      exact Nat.not_lt_of_ge (Nat.le_trans h21 h1.2.1) h2.2.2

/-- $O(1)$ `slice::split_at_mut` descriptor split at index `k`. -/
@[expose] def rangeSplit (r : ByteRange) (k : Nat) : ByteRange × ByteRange :=
  (⟨r.allocId, r.start, k⟩, ⟨r.allocId, r.start + k, r.len - k⟩)

/-- $O(1)$ total adjacent-range combiner: adds lengths keeping `rL.allocId` and
`rL.start` (characterized on adjacent split halves by `rangeMerge_split`). -/
@[expose] def rangeMerge (rL rR : ByteRange) : ByteRange :=
  ⟨rL.allocId, rL.start, rL.len + rR.len⟩

/-- Both halves produced by `rangeSplit r k` are unconditionally disjoint (`[]`
zero axioms). -/
theorem rangeSplit_disjoint (r : ByteRange) (k : Nat) :
    RangeDisjoint (rangeSplit r k).1 (rangeSplit r k).2 :=
  Or.inr (Or.inl (Nat.le_refl (r.start + k)))

private theorem natSub_add_cancel_rs :
    ∀ {k n : Nat}, k ≤ n → k + (n - k) = n
  | 0, n, _ => by
    rw [Nat.zero_add, Nat.sub_zero]
  | k + 1, 0, h => nomatch h
  | k + 1, n + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_add]
    exact congrArg Nat.succ (natSub_add_cancel_rs (Nat.le_of_succ_le_succ h))

/-- Re-merging `rangeSplit r k` recovers `r` identically whenever `k ≤ r.len`
(`[]` zero axioms). -/
theorem rangeMerge_split (r : ByteRange) {k : Nat} (hk : k ≤ r.len) :
    rangeMerge (rangeSplit r k).1 (rangeSplit r k).2 = r := by
  cases r with
  | mk aid st len =>
    dsimp only [rangeMerge, rangeSplit]
    rw [natSub_add_cancel_rs hk]

/-- Exact byte coverage of `rangeSplit r k` (`[]` zero axioms): when
`k ≤ r.len`, `(aid, off)` lies in `r` iff it lies in the left or right half. -/
theorem rangeSplit_covers_iff (r : ByteRange) {k : Nat} (hk : k ≤ r.len)
    (aid : AllocId) (off : Nat) :
    InRange r aid off ↔
      InRange (rangeSplit r k).1 aid off ∨
      InRange (rangeSplit r k).2 aid off := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  dsimp only [InRange, rangeSplit]
  refine ⟨?_, ?_⟩
  · intro hIn
    cases Nat.lt_or_ge off (r.start + k) with
    | inl hLt => exact Or.inl ⟨hIn.1, hIn.2.1, hLt⟩
    | inr hGe =>
      right
      refine ⟨hIn.1, hGe, ?_⟩
      rw [hEnd]
      exact hIn.2.2
  · intro hOr
    cases hOr with
    | inl hL =>
      refine ⟨hL.1, hL.2.1, Nat.lt_of_lt_of_le hL.2.2 ?_⟩
      exact Nat.add_le_add_left hk r.start
    | inr hR =>
      refine ⟨hR.1, Nat.le_trans (Nat.le_add_right r.start k) hR.2.1, ?_⟩
      rw [← hEnd]
      exact hR.2.2

/-- Disjointness descends from a parent `ByteRange` to both halves of
`rangeSplit r k` whenever `k ≤ r.len` (`[]` zero axioms). -/
theorem rangeDisjoint_of_subrange {r rOther : ByteRange} {k : Nat}
    (hk : k ≤ r.len) (hD : RangeDisjoint r rOther) :
    RangeDisjoint (rangeSplit r k).1 rOther ∧
    RangeDisjoint (rangeSplit r k).2 rOther := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  cases hD with
  | inl hNe => exact ⟨Or.inl hNe, Or.inl hNe⟩
  | inr hInt =>
    cases hInt with
    | inl hLe =>
      dsimp only [rangeSplit]
      refine ⟨Or.inr (Or.inl
        (Nat.le_trans (Nat.add_le_add_left hk r.start) hLe)),
        Or.inr (Or.inl ?_)⟩
      rw [hEnd]
      exact hLe
    | inr hGe =>
      exact ⟨Or.inr (Or.inr hGe),
        Or.inr (Or.inr (Nat.le_trans hGe (Nat.le_add_right r.start k)))⟩

/-! ## Part III: `MemoryState` `AllocBytesAt` Split & Disjoint-Write Framing -/

/-- Exact in-bounds live byte-slice predicate over `Trusted.MirSemantics`'s
`MemoryState`: allocation `r.allocId` is live, `[r.start, r.start + r.len)` is
in bounds, and its stored bytes equal `bs`. -/
@[expose] def AllocBytesAt (m : MemoryState) (r : ByteRange)
    (bs : List AllocByte) : Prop :=
  ∃ a : Allocation,
    execFindAllocation r.allocId m.allocations = some a ∧
    a.live = true ∧
    r.start + r.len ≤ a.bytes.length ∧
    bs.length = r.len ∧
    (a.bytes.drop r.start).take r.len = bs

private theorem listDrop_nil_rs :
    ∀ k : Nat, ([] : List AllocByte).drop k = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem listDrop_drop_rs :
    ∀ (m n : Nat) (xs : List AllocByte),
      (xs.drop m).drop n = xs.drop (m + n)
  | 0, n, xs => by
    rw [Nat.zero_add]
    rfl
  | m + 1, n, [] => by
    change ([] : List AllocByte).drop n =
      ([] : List AllocByte).drop (m + 1 + n)
    rw [listDrop_nil_rs, listDrop_nil_rs]
  | m + 1, n, _ :: xs => by
    rw [Nat.succ_add]
    exact listDrop_drop_rs m n xs

private theorem listTake_add_rs :
    ∀ (a b : Nat) (xs : List AllocByte),
      xs.take (a + b) = xs.take a ++ (xs.drop a).take b
  | 0, b, xs => by
    rw [Nat.zero_add]
    rfl
  | a + 1, b, [] => by
    rw [Nat.succ_add]
    change [] = [] ++ (([] : List AllocByte).drop (a + 1)).take b
    rw [listDrop_nil_rs]
    cases b <;> rfl
  | a + 1, b, x :: xs => by
    rw [Nat.succ_add]
    exact congrArg (List.cons x) (listTake_add_rs a b xs)

private theorem listTake_take_of_le_rs :
    ∀ (a b : Nat) (xs : List AllocByte),
      a ≤ b → (xs.take b).take a = xs.take a
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, h => nomatch h
  | _ + 1, _ + 1, [], _ => rfl
  | a + 1, b + 1, x :: xs, h =>
    congrArg (List.cons x)
      (listTake_take_of_le_rs a b xs (Nat.le_of_succ_le_succ h))

private theorem listDrop_take_rs :
    ∀ (a b : Nat) (xs : List AllocByte),
      (xs.take b).drop a = (xs.drop a).take (b - a)
  | 0, _, xs => by
    rw [Nat.sub_zero]
    rfl
  | a + 1, 0, _ => by
    change ([] : List AllocByte).drop (a + 1) =
      ((_ : List AllocByte).drop (a + 1)).take (0 - (a + 1))
    rw [listDrop_nil_rs]
    have hZ : 0 - (a + 1) = 0 := Nat.zero_sub (a + 1)
    rw [hZ]
    rfl
  | _ + 1, _ + 1, [] => by
    rw [Nat.succ_sub_succ]
    change ([] : List AllocByte).drop _ = ([] : List AllocByte).take _
    rw [listDrop_nil_rs]
    cases (_ : Nat) - _ <;> rfl
  | a + 1, b + 1, _ :: xs => by
    rw [Nat.succ_sub_succ]
    exact listDrop_take_rs a b xs

private theorem listSplit_take_drop_rs :
    ∀ (k : Nat) (bs : List AllocByte), bs.take k ++ bs.drop k = bs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => congrArg (List.cons b) (listSplit_take_drop_rs k bs)

private theorem listLength_take_of_le_rs :
    ∀ (k : Nat) (bs : List AllocByte),
      k ≤ bs.length → (bs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => nomatch h
  | k + 1, _ :: bs, h =>
    congrArg Nat.succ (listLength_take_of_le_rs k bs (Nat.le_of_succ_le_succ h))

private theorem listLength_drop_rs :
    ∀ (k : Nat) (bs : List AllocByte), (bs.drop k).length = bs.length - k
  | 0, _ => rfl
  | k + 1, [] => by
    change 0 = 0 - (k + 1)
    rw [Nat.zero_sub]
  | k + 1, _ :: bs => by
    change (bs.drop k).length = (bs.length + 1) - (k + 1)
    rw [Nat.succ_sub_succ, listLength_drop_rs k bs]

/-- $O(1)$ `slice::split_at_mut` soundness over `MemoryState` (`[propext]`
only): for any `k ≤ r.len`, `AllocBytesAt m r bs` holds iff the left half
holds `bs.take k` and the right half holds `bs.drop k`. -/
theorem ownRange_split_iff (m : MemoryState) (r : ByteRange)
    (bs : List AllocByte) {k : Nat} (hk : k ≤ r.len) :
    AllocBytesAt m r bs ↔
      AllocBytesAt m (rangeSplit r k).1 (bs.take k) ∧
      AllocBytesAt m (rangeSplit r k).2 (bs.drop k) := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  refine ⟨?_, ?_⟩
  · intro hAll
    cases hAll with
    | intro a ha =>
      have hBsLen : bs.length = r.len := ha.2.2.2.1
      have hTakeLen : (bs.take k).length = k :=
        listLength_take_of_le_rs k bs (by rw [hBsLen]; exact hk)
      have hDropLen : (bs.drop k).length = r.len - k := by
        rw [listLength_drop_rs, hBsLen]
      refine ⟨⟨a, ha.1, ha.2.1,
        Nat.le_trans (Nat.add_le_add_left hk r.start) ha.2.2.1,
        hTakeLen, ?_⟩,
        ⟨a, ha.1, ha.2.1, ?_, hDropLen, ?_⟩⟩
      · dsimp only [rangeSplit]
        rw [← ha.2.2.2.2]
        exact (listTake_take_of_le_rs k r.len (a.bytes.drop r.start) hk).symm
      · dsimp only [rangeSplit]
        rw [hEnd]
        exact ha.2.2.1
      · dsimp only [rangeSplit]
        rw [← ha.2.2.2.2, ← listDrop_drop_rs r.start k a.bytes]
        exact (listDrop_take_rs k r.len (a.bytes.drop r.start)).symm
  · intro hPair
    cases hPair.1 with
    | intro aL haL =>
      cases hPair.2 with
      | intro aR haR =>
        dsimp only [rangeSplit] at haL haR
        have hFindEq : some aL = some aR := Eq.trans haL.1.symm haR.1
        injection hFindEq with hAeq
        rw [← hAeq] at haR
        have hBsLen : bs.length = r.len := by
          rw [← listSplit_take_drop_rs k bs, List.length_append,
            haL.2.2.2.1, haR.2.2.2.1, natSub_add_cancel_rs hk]
        refine ⟨aL, haL.1, haL.2.1, ?_, hBsLen, ?_⟩
        · rw [← hEnd]
          exact haR.2.2.1
        · have hSplitSlice :
              (aL.bytes.drop r.start).take r.len =
                (aL.bytes.drop r.start).take k ++
                  ((aL.bytes.drop r.start).drop k).take (r.len - k) := by
            have hT := listTake_add_rs k (r.len - k) (aL.bytes.drop r.start)
            rw [natSub_add_cancel_rs hk] at hT
            exact hT
          rw [hSplitSlice, listDrop_drop_rs r.start k aL.bytes,
            haL.2.2.2.2, haR.2.2.2.2, listSplit_take_drop_rs k bs]

private theorem findAllocation_replace_eq (a' : Allocation) :
    ∀ {allocs : List Allocation} {a : Allocation},
      findAllocation a'.allocId allocs = some a →
      findAllocation a'.allocId (replaceAllocation a' allocs) = some a'
  | [], _, hFind => nomatch hFind
  | h :: rest, a, hFind => by
    dsimp only [findAllocation] at hFind
    dsimp only [replaceAllocation]
    cases hHit : Nat.beq h.allocId a'.allocId with
    | true =>
      change
        (if Nat.beq a'.allocId a'.allocId then some a'
         else findAllocation a'.allocId rest) = some a'
      rw [natBeq_refl_rs a'.allocId]
      rfl
    | false =>
      rw [hHit] at hFind
      change
        (if Nat.beq h.allocId a'.allocId then some h
         else findAllocation a'.allocId (replaceAllocation a' rest)) = some a'
      rw [hHit]
      exact findAllocation_replace_eq a' hFind

private theorem execFindAllocation_replace_eq (a' : Allocation)
    {allocs : List Allocation} {a : Allocation}
    (hFind : execFindAllocation a'.allocId allocs = some a) :
    execFindAllocation a'.allocId (execReplaceAllocation a' allocs) =
      some a' := by
  rw [execFindAllocation_eq, execReplaceAllocation_eq]
  rw [execFindAllocation_eq] at hFind
  exact findAllocation_replace_eq a' hFind

private theorem listTake_append_prefix_rs :
    ∀ (xs ys : List AllocByte), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => congrArg (List.cons x) (listTake_append_prefix_rs xs ys)

private theorem listDrop_append_ge_rs :
    ∀ (xs ys : List AllocByte) {n : Nat},
      xs.length ≤ n → (xs ++ ys).drop n = ys.drop (n - xs.length)
  | [], ys, n, _ => by
    change ys.drop n = ys.drop (n - 0)
    rw [Nat.sub_zero]
  | _ :: _, _, 0, h => nomatch h
  | _ :: xs, ys, n + 1, h => by
    change (xs ++ ys).drop n = ys.drop ((n + 1) - (xs.length + 1))
    rw [Nat.succ_sub_succ]
    exact listDrop_append_ge_rs xs ys (Nat.le_of_succ_le_succ h)

private theorem listDrop_take_inside_prefix (xs : List AllocByte)
    {a b n : Nat} (hLe : a + b ≤ n) :
    ((xs.take n).drop a).take b = (xs.drop a).take b := by
  rw [listDrop_take_rs a n xs]
  have hbLe : b ≤ n - a := by
    have hSub := Nat.sub_le_sub_right hLe a
    rw [Nat.add_sub_cancel_left] at hSub
    exact hSub
  exact listTake_take_of_le_rs b (n - a) (xs.drop a) hbLe

private theorem listSlice_splice_left (xs mid : List AllocByte)
    {wStart fStart fLen : Nat}
    (hWLe : wStart ≤ xs.length)
    (hBefore : fStart + fLen ≤ wStart) :
    ((((xs.take wStart ++ mid) ++
        xs.drop (wStart + mid.length)).drop fStart).take fLen) =
      (xs.drop fStart).take fLen := by
  let spliced := (xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)
  have hTakeW : spliced.take wStart = xs.take wStart := by
    dsimp only [spliced]
    rw [List.append_assoc]
    have hLen : (xs.take wStart).length = wStart :=
      listLength_take_of_le_rs wStart xs hWLe
    have hPref := listTake_append_prefix_rs (xs.take wStart)
      (mid ++ xs.drop (wStart + mid.length))
    rw [hLen] at hPref
    exact hPref
  rw [← listDrop_take_inside_prefix spliced hBefore, hTakeW,
    listDrop_take_inside_prefix xs hBefore]

private theorem listSlice_splice_right (xs mid : List AllocByte)
    {wStart fStart fLen : Nat}
    (hWLe : wStart ≤ xs.length)
    (hAfter : wStart + mid.length ≤ fStart) :
    ((((xs.take wStart ++ mid) ++
        xs.drop (wStart + mid.length)).drop fStart).take fLen) =
      (xs.drop fStart).take fLen := by
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, listLength_take_of_le_rs wStart xs hWLe]
  have hDrop :
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)).drop fStart =
        xs.drop fStart := by
    rw [listDrop_append_ge_rs (xs.take wStart ++ mid)
      (xs.drop (wStart + mid.length)) (by rw [hPreLen]; exact hAfter)]
    rw [hPreLen, listDrop_drop_rs (wStart + mid.length)
      (fStart - (wStart + mid.length)) xs, natSub_add_cancel_rs hAfter]
  rw [hDrop]

private theorem findAllocation_allocId_eq (id : AllocId) {a : Allocation} :
    ∀ allocs : List Allocation,
      findAllocation id allocs = some a → a.allocId = id
  | [], h => nomatch h
  | hd :: tl, h => by
    dsimp only [findAllocation] at h
    cases hb : Nat.beq hd.allocId id with
    | true =>
      rw [hb] at h
      injection h with hHd
      rw [← hHd]
      exact natEq_of_beq_rs hb
    | false =>
      rw [hb] at h
      exact findAllocation_allocId_eq id tl h

private theorem execFindAllocation_allocId_eq (id : AllocId) {a : Allocation}
    (allocs : List Allocation)
    (h : execFindAllocation id allocs = some a) : a.allocId = id := by
  rw [execFindAllocation_eq] at h
  exact findAllocation_allocId_eq id allocs h

/-- Unconditional disjoint-write frame law over `MemoryState` (`[propext]`
only): writing `newBytes` (of length `rW.len`) to `rW` via
`Anneal.MirMemComp.execWriteBytes` preserves `AllocBytesAt m rF bsF` whenever
`RangeDisjoint rW rF`, covering both cross-allocation writes and same-allocation
`split_at_mut` sub-slice writes without requiring extra allocation-list
invariants. -/
theorem allocBytesAt_frame_of_execWriteBytes_disjoint
    {m m' : MemoryState} {rW rF : ByteRange} {alignLog2 : Nat}
    {newBytes bsF : List AllocByte}
    (hLenW : newBytes.length = rW.len)
    (hDisj : RangeDisjoint rW rF)
    (hWrite : execWriteBytes m ⟨rW.allocId, rW.start⟩ alignLog2 newBytes =
      .ok m')
    (hFrame : AllocBytesAt m rF bsF) :
    AllocBytesAt m' rF bsF := by
  unfold execWriteBytes at hWrite
  dsimp only at hWrite
  cases hFindW : execFindAllocation rW.allocId m.allocations with
  | none =>
    rw [hFindW] at hWrite
    nomatch hWrite
  | some aW =>
    rw [hFindW] at hWrite
    dsimp only at hWrite
    cases hZero : Nat.beq newBytes.length 0 with
    | true =>
      rw [hZero] at hWrite
      cases hAl0 : execIsAligned aW rW.start alignLog2 with
      | false =>
        rw [hAl0] at hWrite
        nomatch hWrite
      | true =>
        rw [hAl0] at hWrite
        injection hWrite with hMeq
        rw [← hMeq]
        exact hFrame
    | false =>
      rw [hZero] at hWrite
      cases hLiveW : aW.live with
      | false =>
        rw [hLiveW] at hWrite
        nomatch hWrite
      | true =>
        rw [hLiveW] at hWrite
        cases hBndW : execIsInBounds aW rW.start newBytes.length with
        | false =>
          rw [hBndW] at hWrite
          nomatch hWrite
        | true =>
          rw [hBndW] at hWrite
          cases hAlW : execIsAligned aW rW.start alignLog2 with
          | false =>
            rw [hAlW] at hWrite
            nomatch hWrite
          | true =>
            rw [hAlW] at hWrite
            cases hMutW : aW.mutability
            · rw [hMutW] at hWrite
              nomatch hWrite
            · rw [hMutW] at hWrite
              dsimp only at hWrite
              injection hWrite with hMeq
              let bytes' : List AllocByte :=
                (aW.bytes.take rW.start ++ newBytes) ++
                  aW.bytes.drop (rW.start + newBytes.length)
              let aW' : Allocation :=
                { aW with mutability := .mut, bytes := bytes', live := true }
              have hM'Alloc :
                  m'.allocations =
                    execReplaceAllocation aW' m.allocations := by
                rw [← hMeq]
              have hAwId : aW.allocId = rW.allocId :=
                execFindAllocation_allocId_eq rW.allocId m.allocations hFindW
              cases hFrame with
              | intro aF haF =>
                cases hDisj with
                | inl hNeId =>
                  refine ⟨aF, ?_, haF.2.1, haF.2.2.1, haF.2.2.2.1, haF.2.2.2.2⟩
                  have hFNe : rF.allocId ≠ aW'.allocId := by
                    dsimp only [aW']
                    rw [hAwId]
                    exact fun h => hNeId h.symm
                  rw [hM'Alloc,
                    execFindAllocation_replaceAllocation_ne m.allocations aW'
                      rF.allocId hFNe]
                  exact haF.1
                | inr hInt =>
                  cases hIdEq : Nat.beq rW.allocId rF.allocId with
                  | false =>
                    have hNeId : rW.allocId ≠ rF.allocId := fun h => by
                      rw [h, natBeq_refl_rs] at hIdEq
                      exact Bool.noConfusion hIdEq
                    have hFNe : rF.allocId ≠ aW'.allocId := by
                      dsimp only [aW']
                      rw [hAwId]
                      exact fun h => hNeId h.symm
                    refine ⟨aF, ?_, haF.2.1, haF.2.2.1, haF.2.2.2.1,
                      haF.2.2.2.2⟩
                    rw [hM'Alloc,
                      execFindAllocation_replaceAllocation_ne m.allocations aW'
                        rF.allocId hFNe]
                    exact haF.1
                  | true =>
                    have hIdSame : rW.allocId = rF.allocId :=
                      natEq_of_beq_rs hIdEq
                    have hFindSame : some aW = some aF := by
                      rw [← hFindW, hIdSame, haF.1]
                    injection hFindSame with hAeq
                    rw [← hAeq] at haF
                    have hLeBoundsW :
                        rW.start + newBytes.length ≤ aW.bytes.length :=
                      natLe_of_ble_rs hBndW
                    have hWStartLe : rW.start ≤ aW.bytes.length :=
                      Nat.le_trans (Nat.le_add_right rW.start newBytes.length)
                        hLeBoundsW
                    have hBytesLenEq : bytes'.length = aW.bytes.length := by
                      dsimp only [bytes']
                      rw [List.length_append, List.length_append,
                        listLength_take_of_le_rs rW.start aW.bytes hWStartLe,
                        listLength_drop_rs, Nat.add_sub_of_le hLeBoundsW]
                    have hFind' :
                        execFindAllocation rF.allocId m'.allocations =
                          some aW' := by
                      rw [hM'Alloc, ← hIdSame, ← hAwId]
                      exact execFindAllocation_replace_eq aW'
                        (by dsimp only [aW']; rw [hAwId]; exact hFindW)
                    refine ⟨aW', hFind', rfl, ?_, haF.2.2.2.1, ?_⟩
                    · dsimp only [aW']
                      rw [hBytesLenEq]
                      exact haF.2.2.1
                    · dsimp only [aW', bytes']
                      cases hInt with
                      | inl hAfter =>
                        rw [listSlice_splice_right aW.bytes newBytes hWStartLe
                          (by rw [hLenW]; exact hAfter)]
                        exact haF.2.2.2.2
                      | inr hBefore =>
                        rw [listSlice_splice_left aW.bytes newBytes hWStartLe
                          hBefore]
                        exact haF.2.2.2.2

end Anneal.SepAC

end
