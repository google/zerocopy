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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-!
# Heap Allocation Contract Proofs & Canaries (`Core.AllocContractCanaries`)

Machine-checked preservation, `AllocId` disjointness, frame preservation,
slice equivalence, and positive/negative end-to-end execution canaries for
`Trusted.MirSemantics.AllocContracts`.
-/

/-! ## Proof Vocabulary

Declarative predicates over the trusted decidable checks. They are defined
here, outside the TCB, because the semantics never uses them. -/

/-- Declarative well-formedness predicate for `VecModel` in `m`. -/
@[expose] def VecWf (m : MemoryState) (isMut : Bool)
    (v : VecModel) : Prop :=
  vecValidInMem m isMut v = .ok ()

/-- Declarative well-formedness predicate for `BoxModel` in `m`. -/
@[expose] def BoxWf (m : MemoryState) (isMut : Bool)
    (b : BoxModel) : Prop :=
  boxValidInMem m isMut b = .ok ()

/-- Disjointness of a freshly allocated `aid` from every allocation present in
`mBefore` (and from sentinel `0`). -/
@[expose] def AllocDisjoint (mBefore : MemoryState) (aid : AllocId) :
    Prop :=
  aid ≠ 0 ∧ findAllocation aid mBefore.allocations = none

/-- Preservation of all pre-existing allocations in `mBefore` except ids
explicitly retired (`retiredIds`) by reallocation. -/
@[expose] def AllocFramePreserved (mBefore mAfter : MemoryState)
    (retiredIds : List AllocId) : Prop :=
  ∀ a : Allocation,
    findAllocation a.allocId mBefore.allocations = some a →
    ¬(a.allocId ∈ retiredIds) →
    findAllocation a.allocId mAfter.allocations = some a

/-! ## Memory Allocation & Frame Preservation Lemmas -/

/-- Upper bound invariant: every allocation in `m.allocations` has `allocId`
strictly below `m.nextAllocId`. -/
@[expose] def NextAllocUpper (m : MemoryState) : Prop :=
  ∀ a : Allocation, a ∈ m.allocations → a.allocId < m.nextAllocId

theorem findAllocation_some_mem {id : AllocId} {a : Allocation} :
    ∀ {allocs : List Allocation},
      findAllocation id allocs = some a → a ∈ allocs ∧ a.allocId = id
  | [], h => by cases h
  | x :: xs, h => by
    unfold findAllocation at h
    cases hEq : Nat.beq x.allocId id with
    | true =>
      rw [hEq] at h
      injection h with hx
      subst hx
      exact ⟨.head xs, Nat.eq_of_beq_eq_true hEq⟩
    | false =>
      rw [hEq] at h
      let ⟨hMem, hId⟩ := findAllocation_some_mem h
      exact ⟨.tail x hMem, hId⟩

theorem findAllocation_append_ne {id : AllocId} {a' : Allocation}
    (hNe : a'.allocId ≠ id) :
    ∀ (allocs : List Allocation),
      findAllocation id (allocs ++ [a']) = findAllocation id allocs
  | [] => by
    change (if Nat.beq a'.allocId id then some a' else none) = none
    cases hEq : Nat.beq a'.allocId id with
    | false => rfl
    | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hEq))
  | x :: xs => by
    change (if Nat.beq x.allocId id then some x
        else findAllocation id (xs ++ [a'])) =
      (if Nat.beq x.allocId id then some x else findAllocation id xs)
    cases Nat.beq x.allocId id with
    | true => rfl
    | false => exact findAllocation_append_ne hNe xs

private theorem natBeq_eq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hEq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hEq))

private theorem natBeq_eq_true_of_eq {a b : Nat} (h : a = b) :
    Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

private theorem mem_of_mem_append {α : Type} {x : α} :
    ∀ {xs ys : List α}, x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys
  | [], _, h => .inr h
  | a :: xs, ys, h => by
    cases h with
    | head _ => exact .inl (.head xs)
    | tail _ hTail =>
      cases mem_of_mem_append hTail with
      | inl hIn => exact .inl (.tail a hIn)
      | inr hIn => exact .inr hIn

theorem findAllocation_replace_ne {id : AllocId} {a' : Allocation}
    (hNe : a'.allocId ≠ id) :
    ∀ (allocs : List Allocation),
      findAllocation id (replaceAllocation a' allocs) = findAllocation id allocs
  | [] => rfl
  | x :: xs => by
    change findAllocation id
      (if Nat.beq x.allocId a'.allocId then a' :: xs
       else x :: replaceAllocation a' xs) = findAllocation id (x :: xs)
    cases hEq : Nat.beq x.allocId a'.allocId with
    | true =>
      have hXEq : x.allocId = a'.allocId := Nat.eq_of_beq_eq_true hEq
      have hXNe : Nat.beq x.allocId id = false :=
        natBeq_eq_false_of_ne (hXEq ▸ hNe)
      have hANe : Nat.beq a'.allocId id = false :=
        natBeq_eq_false_of_ne hNe
      change (if Nat.beq a'.allocId id then some a' else findAllocation id xs) =
        (if Nat.beq x.allocId id then some x else findAllocation id xs)
      rw [hANe, hXNe]
      rfl
    | false =>
      change (if Nat.beq x.allocId id then some x
          else findAllocation id (replaceAllocation a' xs)) =
        (if Nat.beq x.allocId id then some x else findAllocation id xs)
      cases Nat.beq x.allocId id with
      | true => rfl
      | false => exact findAllocation_replace_ne hNe xs

theorem mem_replaceAllocation {a a' : Allocation} :
    ∀ {allocs : List Allocation},
      a ∈ replaceAllocation a' allocs → a = a' ∨ a ∈ allocs
  | [], h => by cases h
  | x :: xs, h => by
    change a ∈ (if Nat.beq x.allocId a'.allocId then a' :: xs
      else x :: replaceAllocation a' xs) at h
    cases hEq : Nat.beq x.allocId a'.allocId with
    | true =>
      rw [hEq] at h
      cases h with
      | head => exact .inl rfl
      | tail _ hXs => exact .inr (.tail x hXs)
    | false =>
      rw [hEq] at h
      cases h with
      | head => exact .inr (.head xs)
      | tail _ hRec =>
        cases mem_replaceAllocation hRec with
        | inl hEq' => exact .inl hEq'
        | inr hXs => exact .inr (.tail x hXs)

theorem findAllocation_none_of_lt {bound id : AllocId}
    (hLe : bound ≤ id) :
    ∀ {allocs : List Allocation},
      (∀ a : Allocation, a ∈ allocs → a.allocId < bound) →
      findAllocation id allocs = none
  | [], _ => rfl
  | x :: xs, hB => by
    unfold findAllocation
    have hLt : x.allocId < bound := hB x (.head xs)
    have hNe : x.allocId ≠ id := Nat.ne_of_lt (Nat.lt_of_lt_of_le hLt hLe)
    cases hEq : Nat.beq x.allocId id with
    | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hEq))
    | false =>
      exact findAllocation_none_of_lt hLe (fun a ha => hB a (.tail x ha))

theorem allocHeapBuffer_disjoint {m : MemoryState} (hUpper : NextAllocUpper m)
    (hPos : 0 < m.nextAllocId) (sz align : Nat) :
    let (m', ptr) := allocHeapBuffer m sz align
    ptr = ⟨some m.nextAllocId, 0, .isize⟩ ∧
      AllocDisjoint m m.nextAllocId ∧ NextAllocUpper m' := by
  dsimp only [allocHeapBuffer, MemoryState.reserveAllocId]
  refine ⟨rfl, ⟨Nat.ne_of_gt hPos, ?_⟩, ?_⟩
  · exact findAllocation_none_of_lt (Nat.le_refl m.nextAllocId) hUpper
  · intro a ha
    cases mem_of_mem_append ha with
    | inl hOld => exact Nat.lt_succ_of_lt (hUpper a hOld)
    | inr hNew =>
      cases hNew with
      | head _ => exact Nat.lt_succ_self m.nextAllocId
      | tail _ hEmpty => cases hEmpty

theorem allocHeapBuffer_frame {m : MemoryState} (hUpper : NextAllocUpper m)
    (sz align : Nat) :
    AllocFramePreserved m (allocHeapBuffer m sz align).1 [] := by
  intro a ha _
  let ⟨hMem, _⟩ := findAllocation_some_mem ha
  have hLt : a.allocId < m.nextAllocId := hUpper a hMem
  have hNe : m.nextAllocId ≠ a.allocId := Nat.ne_of_gt hLt
  dsimp only [allocHeapBuffer, MemoryState.reserveAllocId]
  exact (findAllocation_append_ne hNe m.allocations).trans ha

/-! ## `VecWf`, `BoxWf`, Disjointness, and Equivalence Theorems -/

private theorem intLayout_alignLog2_le_4 (w : IntWidth) :
    (intLayout w).alignLog2 ≤ 4 := by
  cases w <;> decide

private theorem zst_or_zero_cap_dangling_ok {lay : LayoutData}
    (hAlign : lay.alignLog2 ≤ 4) :
    Nat.beq (Nat.pow 2 lay.alignLog2) 0 = false ∧
    Nat.beq (Nat.mod (Nat.pow 2 lay.alignLog2) (Nat.pow 2 lay.alignLog2)) 0 =
      true := by
  cases lay with
  | mk _ al =>
    have hPowPos : 0 < Nat.pow 2 al := Nat.pow_pos (by decide)
    exact ⟨natBeq_eq_false_of_ne (Nat.ne_of_gt hPowPos),
      natBeq_eq_true_of_eq (Nat.mod_self _)⟩

theorem evalVecNew_vecWf {m : MemoryState} {isMut : Bool} {elem : MirTy}
    {v : Val} (hNew : evalVecNew elem = .ok v) :
    ∃ ptr cap len, v = .vec ptr cap len ∧
      VecWf m isMut ⟨elem, ptr, cap, len⟩ := by
  unfold evalVecNew at hNew
  cases hSup : isSupportedPointeeTy elem with
  | false => rw [hSup] at hNew; cases hNew
  | true =>
    rw [hSup] at hNew
    cases hLay : layoutOfTyV2 elem with
    | none => rw [hLay] at hNew; cases hNew
    | some lay =>
      rw [hLay] at hNew
      injection hNew with hv
      subst hv
      refine ⟨danglingAligned lay.alignLog2, 0, 0, rfl, ?_⟩
      unfold VecWf vecValidInMem ownedHeapBufValidInMem heapBufValidInMem
        zeroCapPtrValidInMem danglingAligned
      rw [hSup]
      dsimp only
      rw [hLay]
      have hAlign : lay.alignLog2 ≤ 4 := by
        cases elem with
        | bool | char | ordering | unit | never =>
          rw [layoutOfTyV2.eq_def] at hLay
          dsimp only [layoutOfTy] at hLay
          injection hLay with hL; subst hL; decide
        | int w _ =>
          rw [layoutOfTyV2.eq_def] at hLay
          dsimp only [layoutOfTy] at hLay
          injection hLay with hL; subst hL
          exact intLayout_alignLog2_le_4 w
        | enum ety =>
          rw [layoutOfTyV2.eq_def] at hLay
          dsimp only [layoutOfTy] at hLay
          cases hAdm : enumAdmitted ety <;> rw [hAdm] at hLay
          · cases hLay
          · cases hTag : ety.tagRepr with
            | zeroSized =>
              rw [hTag] at hLay; injection hLay with hL; subst hL; decide
            | scalar tw _ =>
              rw [hTag] at hLay; injection hLay with hL; subst hL
              exact intLayout_alignLog2_le_4 tw
        | tuple fs =>
          cases fs with
          | nil => cases hLay
          | cons t1 r1 =>
            cases t1 with
            | int w _ =>
              cases r1 with
              | nil => cases hLay
              | cons t2 r2 =>
                cases t2 with
                | bool =>
                  cases r2 with
                  | nil =>
                    rw [layoutOfTyV2.eq_def] at hLay
                    dsimp only [layoutOfTy, overflowPairLayout] at hLay
                    injection hLay with hL; subst hL
                    cases w <;> decide
                  | cons _ _ => cases hLay
                | _ => cases hLay
            | _ => cases hLay
        | _ => cases hSup
      have hPowLt : Nat.pow 2 lay.alignLog2 < UInt64.size := by
        have h16 : Nat.pow 2 lay.alignLog2 ≤ 16 :=
          Nat.pow_le_pow_right (by decide) hAlign
        exact Nat.lt_of_le_of_lt h16 (by decide)
      have hToNat : (UInt64.ofNat (Nat.pow 2 lay.alignLog2)).toNat =
          Nat.pow 2 lay.alignLog2 := by
        dsimp only [UInt64.toNat, UInt64.ofNat]
        exact Nat.mod_eq_of_lt hPowLt
      let ⟨hNz, hMod⟩ := zst_or_zero_cap_dangling_ok hAlign
      have hLtBool : Nat.blt (0 * lay.size) isizeMaxBytes = true := by
        rw [Nat.zero_mul]; decide
      have hZeroToNat : (0 : UInt64).toNat = 0 := rfl
      dsimp only [zeroCapPtrValidInMem, danglingAligned]
      have hW1 : (!IntWidth.beq IntWidth.isize IntWidth.isize) = false := rfl
      have hBle0 : Nat.ble 0 0 = true := rfl
      have hBeq0 : Nat.beq 0 0 = true := rfl
      rw [hW1, hZeroToNat, hBle0, hLtBool, hToNat, hNz, hMod, hBeq0]
      cases Nat.beq lay.size 0 <;> rfl

theorem evalVecWithCapacity_disjoint_and_frame {m m' : MemoryState}
    {elem : MirTy} {cap : UInt64} {val : Val}
    (hUpper : NextAllocUpper m) (hPos : 0 < m.nextAllocId)
    (hCall : evalVecWithCapacity m elem cap = .ok (val, m')) :
    AllocFramePreserved m m' [] ∧ NextAllocUpper m' ∧
      (∀ lay, layoutOfTyV2 elem = some lay → 0 < cap.toNat * lay.size →
        val = .vec ⟨some m.nextAllocId, 0, .isize⟩ cap 0 ∧
        AllocDisjoint m m.nextAllocId) := by
  unfold evalVecWithCapacity at hCall
  cases hSup : isSupportedPointeeTy elem with
  | false => rw [hSup] at hCall; cases hCall
  | true =>
    rw [hSup] at hCall
    cases hLay : layoutOfTyV2 elem with
    | none => rw [hLay] at hCall; cases hCall
    | some lay =>
      rw [hLay] at hCall
      dsimp only at hCall
      cases hLim : Nat.blt (cap.toNat * lay.size) isizeMaxBytes with
      | false => rw [hLim] at hCall; cases hCall
      | true =>
        rw [hLim] at hCall
        cases hZero : Nat.beq (cap.toNat * lay.size) 0 with
        | true =>
          rw [hZero] at hCall
          injection hCall with hPair
          have hm : m' = m := (congrArg Prod.snd hPair).symm
          subst hm
          refine ⟨fun a ha _ => ha, hUpper, fun lay' hLay' hPosSz => ?_⟩
          injection hLay' with hLeq; subst hLeq
          exact False.elim (Nat.ne_of_gt hPosSz (Nat.eq_of_beq_eq_true hZero))
        | false =>
          rw [hZero] at hCall
          injection hCall with hPair
          have hv : val = .vec (allocHeapBuffer m (cap.toNat * lay.size)
              lay.alignLog2).2 cap 0 :=
            (congrArg Prod.fst hPair).symm
          have hm : m' = (allocHeapBuffer m (cap.toNat * lay.size)
              lay.alignLog2).1 :=
            (congrArg Prod.snd hPair).symm
          let ⟨hPtr, hDisj, hUp'⟩ := allocHeapBuffer_disjoint hUpper hPos
            (cap.toNat * lay.size) lay.alignLog2
          have hFrame := allocHeapBuffer_frame hUpper
            (cap.toNat * lay.size) lay.alignLog2
          have hPtrEq : (allocHeapBuffer m (cap.toNat * lay.size)
              lay.alignLog2).2 = ⟨some m.nextAllocId, 0, .isize⟩ := rfl
          rw [← hm] at hFrame
          refine ⟨hFrame, ?_, fun _ _ _ => ⟨?_, hDisj⟩⟩
          · rw [hm]; exact hUp'
          · rw [hv, hPtrEq]

/-- A buffer that is valid with `cap` slots holding `len` elements is also
valid viewed as exactly `len` slots. -/
private theorem heapBufValidInMem_len_len {m : MemoryState} {elem : MirTy}
    {ptr : PtrVal} {cap len : UInt64}
    (hVec : heapBufValidInMem m true elem ptr cap len = .ok ()) :
    heapBufValidInMem m true elem ptr len len = .ok () := by
  unfold heapBufValidInMem at hVec
  unfold heapBufValidInMem
  cases hW : IntWidth.beq ptr.width .isize with
  | false => rw [hW] at hVec; cases hVec
  | true =>
    rw [hW] at hVec
    cases hLay : layoutOfTyV2 elem with
    | none => rw [hLay] at hVec; cases hVec
    | some lay =>
      rw [hLay] at hVec
      dsimp only at hVec; dsimp only
      cases hBle : Nat.ble len.toNat cap.toNat with
      | false => rw [hBle] at hVec; cases hVec
      | true =>
        rw [hBle] at hVec
        have hLeCap : len.toNat ≤ cap.toNat := Nat.le_of_ble_eq_true hBle
        rw [Nat.ble_eq.mpr (Nat.le_refl _)]
        have hCapMul : len.toNat * lay.size ≤ cap.toNat * lay.size :=
          Nat.mul_le_mul_right lay.size hLeCap
        cases hLimCap : Nat.blt (cap.toNat * lay.size) isizeMaxBytes with
        | false => rw [hLimCap] at hVec; cases hVec
        | true =>
          rw [hLimCap] at hVec
          have hLimLen :
              Nat.blt (len.toNat * lay.size) isizeMaxBytes = true :=
            Nat.blt_eq.mpr
              (Nat.lt_of_le_of_lt hCapMul (Nat.blt_eq.mp hLimCap))
          rw [hLimLen]
          cases hZst : Nat.beq lay.size 0 with
          | true => rw [hZst] at hVec; exact hVec
          | false =>
            rw [hZst] at hVec
            cases hCap0 : Nat.beq cap.toNat 0 with
            | true =>
              rw [hCap0] at hVec
              have hCapEq0 : cap.toNat = 0 := Nat.eq_of_beq_eq_true hCap0
              have hLenEq0 : len.toNat = 0 :=
                Nat.le_zero.mp (hCapEq0 ▸ hLeCap)
              rw [natBeq_eq_true_of_eq hLenEq0]
              exact hVec
            | false =>
              rw [hCap0] at hVec
              cases hLen0 : Nat.beq len.toNat 0 with
              | true =>
                cases hAid : ptr.allocId with
                | none => rw [hAid] at hVec; cases hVec
                | some aid =>
                  rw [hAid] at hVec
                  dsimp only at hVec
                  cases hFind : findAllocation aid m.allocations with
                  | none => rw [hFind] at hVec; cases hVec
                  | some a =>
                    rw [hFind] at hVec
                    unfold zeroCapPtrValidInMem
                    rw [hAid]
                    dsimp only
                    rw [hFind]
                    dsimp only at hVec; dsimp only
                    cases hL : a.live with
                    | false => rw [hL] at hVec; cases hVec
                    | true =>
                      rw [hL] at hVec
                      cases hB : isInBounds a ptr.offsetBytes.toNat
                          (cap.toNat * lay.size) with
                      | false => rw [hB] at hVec; cases hVec
                      | true =>
                        rw [hB] at hVec
                        cases hAl : isAligned a ptr.offsetBytes.toNat
                            lay.alignLog2 with
                        | false => rw [hAl] at hVec; cases hVec
                        | true =>
                          rw [hAl] at hVec
                          cases hM : Mutability.beq a.mutability .mut with
                          | false => rw [hM] at hVec; cases hVec
                          | true =>
                            rw [hM] at hVec
                            have hInB0 :
                                isInBounds a ptr.offsetBytes.toNat 0 =
                                  true := by
                              unfold isInBounds at hB; unfold isInBounds
                              exact Nat.ble_eq.mpr (Nat.le_trans
                                (Nat.add_le_add_left (Nat.zero_le _) _)
                                (Nat.ble_eq.mp hB))
                            rw [hInB0]; rfl
              | false =>
                cases hAid : ptr.allocId with
                | none => rw [hAid] at hVec; cases hVec
                | some aid =>
                  rw [hAid] at hVec
                  dsimp only at hVec; dsimp only
                  cases hFind : findAllocation aid m.allocations with
                  | none => rw [hFind] at hVec; cases hVec
                  | some a =>
                    rw [hFind] at hVec
                    dsimp only at hVec; dsimp only
                    cases hL : a.live with
                    | false => rw [hL] at hVec; cases hVec
                    | true =>
                      rw [hL] at hVec
                      cases hB : isInBounds a ptr.offsetBytes.toNat
                          (cap.toNat * lay.size) with
                      | false => rw [hB] at hVec; cases hVec
                      | true =>
                        rw [hB] at hVec
                        cases hAl : isAligned a ptr.offsetBytes.toNat
                            lay.alignLog2 with
                        | false => rw [hAl] at hVec; cases hVec
                        | true =>
                          rw [hAl] at hVec
                          cases hM : Mutability.beq a.mutability .mut with
                          | false => rw [hM] at hVec; cases hVec
                          | true =>
                            rw [hM] at hVec
                            have hInBLen : isInBounds a
                                ptr.offsetBytes.toNat
                                (len.toNat * lay.size) = true := by
                              unfold isInBounds at hB; unfold isInBounds
                              exact Nat.ble_eq.mpr (Nat.le_trans
                                (Nat.add_le_add_left hCapMul _)
                                (Nat.ble_eq.mp hB))
                            rw [hInBLen]; exact hVec

/-- When `Box<[T]>::from` keeps the `Vec` buffer (`cap = len`, or zero-sized
`T`), it returns a box over the same pointer, leaves memory unchanged, and the
box is well-formed. Otherwise the buffer is reallocated; see
`evalBoxFromVec_disjoint_and_frame` and
`box_from_vec_realloc_stale_provenance`. -/
theorem evalBoxFromVec_inPlace_boxWf {m m' : MemoryState} {elem : MirTy}
    {ptr : PtrVal} {cap len : UInt64} {res : Val}
    (hKeep : cap = len ∨ ∀ lay, layoutOfTyV2 elem = some lay → lay.size = 0)
    (hCall : evalBoxFromVec m elem ptr cap len = .ok (res, m')) :
    res = .boxPtr ptr (some len) ∧ m' = m ∧
      BoxWf m true ⟨.slice elem, ptr, some len⟩ := by
  unfold evalBoxFromVec at hCall
  dsimp only at hCall
  cases hVec : vecValidInMem m true ⟨elem, ptr, cap, len⟩ with
  | error k => rw [hVec] at hCall; cases hCall
  | ok u =>
    cases u
    rw [hVec] at hCall
    cases hLay : layoutOfTyV2 elem with
    | none => rw [hLay] at hCall; cases hCall
    | some lay =>
      rw [hLay] at hCall
      dsimp only at hCall
      have hCond :
          (Nat.beq lay.size 0 || Nat.beq cap.toNat len.toNat) = true := by
        cases hKeep with
        | inl hEq =>
          rw [hEq, Nat.beq_refl]
          cases Nat.beq lay.size 0 <;> rfl
        | inr hZ => rw [natBeq_eq_true_of_eq (hZ lay hLay)]; rfl
      rw [hCond] at hCall
      injection hCall with hPair
      refine ⟨(congrArg Prod.fst hPair).symm,
        (congrArg Prod.snd hPair).symm, ?_⟩
      unfold vecValidInMem at hVec
      cases hSup : isSupportedPointeeTy elem with
      | false => rw [hSup] at hVec; cases hVec
      | true =>
        rw [hSup] at hVec
        dsimp only at hVec
        unfold BoxWf boxValidInMem boxPointeeValidInMem
        dsimp only
        rw [hSup]
        cases hKeep with
        | inl hEq => rw [hEq] at hVec; exact hVec
        | inr hZ =>
          unfold ownedHeapBufValidInMem at hVec
          unfold ownedHeapBufValidInMem
          cases hHeap : heapBufValidInMem m true elem ptr cap len with
          | error k => rw [hHeap] at hVec; cases hVec
          | ok u =>
            cases u
            rw [heapBufValidInMem_len_len hHeap]
            dsimp only
            rw [hLay]
            dsimp only
            rw [natBeq_eq_true_of_eq (hZ lay hLay)]
            rfl

theorem evalVecDeref_slice_equiv {m : MemoryState} {reqMut : Mutability}
    {elem : MirTy} {selfPtr : PtrVal} {res : Val}
    (hDeref : evalVecDeref m reqMut elem selfPtr = .ok res) :
    ∃ v : VecModel,
      readVecFromRef m (Mutability.beq reqMut .mut) elem selfPtr = .ok v ∧
      res = .slicePtr v.ptr v.len ∧
      refValidInMem m reqMut (.slice elem) res = .ok () := by
  unfold evalVecDeref at hDeref
  dsimp only at hDeref
  cases hRead : readVecFromRef m (Mutability.beq reqMut .mut) elem selfPtr
    with
  | error k => rw [hRead] at hDeref; cases hDeref
  | ok v =>
    rw [hRead] at hDeref
    dsimp only at hDeref
    cases hValid : refValidInMem m reqMut (.slice elem)
        (.slicePtr v.ptr v.len) with
    | error k => rw [hValid] at hDeref; cases hDeref
    | ok u =>
      cases u
      rw [hValid] at hDeref
      injection hDeref with hEq
      subst hEq
      exact ⟨v, rfl, rfl, hValid⟩

private theorem readBoxFromRef_pointee {m : MemoryState} {reqMut : Bool}
    {pointee : MirTy} {selfPtr : PtrVal} {b : BoxModel}
    (hRead : readBoxFromRef m reqMut pointee selfPtr = .ok b) :
    b.pointee = pointee := by
  unfold readBoxFromRef at hRead
  dsimp only at hRead
  cases hRef : refValidInMem m (if reqMut then Mutability.mut
      else Mutability.shared) (.box pointee) (.ptr selfPtr) with
  | error k => rw [hRef] at hRead; cases hRead
  | ok u0 =>
    cases u0
    rw [hRef] at hRead
    dsimp only at hRead
    cases hAid : selfPtr.allocId with
    | none => rw [hAid] at hRead; cases hRead
    | some aid =>
      rw [hAid] at hRead
      dsimp only at hRead
      cases hLd : loadIndirectV2 m (.box pointee)
          ⟨aid, selfPtr.offsetBytes.toNat⟩ with
      | error k => rw [hLd] at hRead; cases hRead
      | ok optV =>
        rw [hLd] at hRead
        cases optV with
        | none => cases hRead
        | some dv =>
          cases dv with
          | boxPtr boxP optLen =>
            dsimp only at hRead
            cases hBox : boxValidInMem m reqMut ⟨pointee, boxP, optLen⟩ with
            | error k => rw [hBox] at hRead; cases hRead
            | ok u1 =>
              cases u1
              rw [hBox] at hRead
              injection hRead with hb
              subst hb
              rfl
          | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | rangeTo _
          | rangeFrom _ | bool _ | char _ | ordering _ | unit
          | enumVal _ _ | tuple _ | bytes _ | array _ | optionVal _ | range _ _ => cases hRead

theorem evalBoxDeref_slice_equiv {m : MemoryState} {reqMut : Mutability}
    {elem : MirTy} {selfPtr : PtrVal} {res : Val}
    (hDeref : evalBoxDeref m reqMut (.slice elem) selfPtr = .ok res) :
    ∃ b : BoxModel, ∃ len : UInt64,
      readBoxFromRef m (Mutability.beq reqMut .mut) (.slice elem) selfPtr =
        .ok b ∧
      b.len = some len ∧
      res = .slicePtr b.ptr len ∧
      refValidInMem m reqMut (.slice elem) res = .ok () := by
  unfold evalBoxDeref at hDeref
  dsimp only at hDeref
  cases hRead : readBoxFromRef m (Mutability.beq reqMut .mut) (.slice elem)
      selfPtr with
  | error k => rw [hRead] at hDeref; cases hDeref
  | ok b =>
    rw [hRead] at hDeref
    dsimp only at hDeref
    have hPt : b.pointee = .slice elem := readBoxFromRef_pointee hRead
    rw [hPt] at hDeref
    cases hLen : b.len with
    | none => rw [hLen] at hDeref; cases hDeref
    | some len =>
      rw [hLen] at hDeref
      dsimp only at hDeref
      cases hValid : refValidInMem m reqMut (.slice elem)
          (.slicePtr b.ptr len) with
      | error k => rw [hValid] at hDeref; cases hDeref
      | ok u =>
        cases u
        rw [hValid] at hDeref
        injection hDeref with hEq
        subst hEq
        exact ⟨b, len, rfl, hLen, rfl, hValid⟩

private theorem writeBytes_fresh_frame {m0 m1 m2 : MemoryState}
    {id : AllocId} {off al : Nat} {bs : List AllocByte}
    (hUpper0 : NextAllocUpper m0)
    (hUpper1 : NextAllocUpper m1)
    (hFrame01 : AllocFramePreserved m0 m1 [])
    (hBound : m0.nextAllocId ≤ id)
    (hWr : writeBytes m1 ⟨id, off⟩ al bs = .ok m2) :
    AllocFramePreserved m0 m2 [] ∧ NextAllocUpper m2 := by
  unfold writeBytes at hWr
  dsimp only at hWr
  cases hDst : findAllocation id m1.allocations with
  | none => rw [hDst] at hWr; cases hWr
  | some dstA =>
    rw [hDst] at hWr
    dsimp only at hWr
    cases hLen0 : Nat.beq bs.length 0 with
    | true =>
      rw [hLen0, ite_eq_left rfl] at hWr
      cases hAl : !isAligned dstA off al with
      | true => rw [hAl, ite_eq_left rfl] at hWr; cases hWr
      | false =>
        rw [hAl, ite_eq_right (by decide)] at hWr
        injection hWr with hEq
        rw [← hEq]
        exact ⟨hFrame01, hUpper1⟩
    | false =>
      rw [hLen0, ite_eq_right (by decide)] at hWr
      have hDstId : dstA.allocId = id := (findAllocation_some_mem hDst).2
      cases hCond : !dstA.live || !isInBounds dstA off bs.length ||
          !isAligned dstA off al with
      | true => rw [hCond] at hWr; cases hWr
      | false =>
        rw [hCond] at hWr
        cases hMut : dstA.mutability with
        | shared => rw [hMut] at hWr; cases hWr
        | _ =>
          rw [hMut] at hWr
          injection hWr with hm2Eq
          rw [← hm2Eq]
          refine ⟨?_, ?_⟩
          · intro a ha hNot
            have hIn1 := hFrame01 a ha hNot
            let ⟨hMem, _⟩ := findAllocation_some_mem ha
            have hNe : dstA.allocId ≠ a.allocId :=
              hDstId ▸ Nat.ne_of_gt (Nat.lt_of_lt_of_le (hUpper0 a hMem) hBound)
            exact (findAllocation_replace_ne
              (a' := { dstA with mutability := .mut, bytes := _ })
              hNe m1.allocations).trans hIn1
          · intro a ha
            cases mem_replaceAllocation ha with
            | inl hEq =>
              rw [hEq]
              exact hUpper1 dstA (findAllocation_some_mem hDst).1
            | inr hIn => exact hUpper1 a hIn

theorem evalBoxNew_disjoint_and_frame {m m' : MemoryState} {pt : MirTy}
    {value res : Val} (hUpper : NextAllocUpper m) (hPos : 0 < m.nextAllocId)
    (hCall : evalBoxNew m pt value = .ok (res, m')) :
    AllocFramePreserved m m' [] ∧ NextAllocUpper m' ∧
      (∀ lay, layoutOfTyV2 pt = some lay → 0 < lay.size →
        res = .boxPtr ⟨some m.nextAllocId, 0, .isize⟩ none ∧
        AllocDisjoint m m.nextAllocId) := by
  unfold evalBoxNew at hCall
  cases hCond : isUnsizedTy pt || !isSupportedPointeeTy pt ||
      !checkValV2 value pt with
  | true => rw [hCond] at hCall; cases hCall
  | false =>
    rw [hCond] at hCall
    cases hLay : layoutOfTyV2 pt with
    | none => rw [hLay] at hCall; cases hCall
    | some lay =>
      rw [hLay] at hCall
      cases hEnc : encodeValV2 profileV2TargetEndian pt value with
      | error k => rw [hEnc] at hCall; cases hCall
      | ok bs =>
        rw [hEnc] at hCall
        dsimp only at hCall
        cases hZ : Nat.beq lay.size 0 with
        | true =>
          rw [hZ] at hCall
          injection hCall with hPair
          have hm : m' = m := (congrArg Prod.snd hPair).symm
          subst hm
          refine ⟨fun a ha _ => ha, hUpper, fun lay' hLay' hPosSz => ?_⟩
          injection hLay' with hL; subst hL
          exact False.elim (Nat.ne_of_gt hPosSz (Nat.eq_of_beq_eq_true hZ))
        | false =>
          rw [hZ] at hCall
          let ⟨_, hDisj, hUp1⟩ := allocHeapBuffer_disjoint hUpper hPos
            lay.size lay.alignLog2
          have hFrame := allocHeapBuffer_frame hUpper lay.size lay.alignLog2
          have hPtrEq : (allocHeapBuffer m lay.size lay.alignLog2).2 =
              ⟨some m.nextAllocId, 0, .isize⟩ := rfl
          rw [hPtrEq] at hCall
          dsimp only at hCall
          cases hWr : writeBytes (allocHeapBuffer m lay.size lay.alignLog2).1
              ⟨m.nextAllocId, 0⟩ lay.alignLog2 bs with
          | error k => rw [hWr] at hCall; cases hCall
          | ok m2 =>
            rw [hWr] at hCall
            injection hCall with hPair
            have hr : res = .boxPtr ⟨some m.nextAllocId, 0, .isize⟩ none :=
              (congrArg Prod.fst hPair).symm
            have hm2 : m' = m2 := (congrArg Prod.snd hPair).symm
            subst hm2
            let ⟨hFr2, hUp2⟩ := writeBytes_fresh_frame hUpper hUp1 hFrame
              (Nat.le_refl m.nextAllocId) hWr
            exact ⟨hFr2, hUp2, fun _ _ _ => ⟨hr, hDisj⟩⟩

theorem evalBoxClone_disjoint_and_frame {m m' : MemoryState} {pt : MirTy}
    {selfPtr : PtrVal} {res : Val} (hUpper : NextAllocUpper m)
    (hPos : 0 < m.nextAllocId)
    (hCall : evalBoxClone m pt selfPtr = .ok (res, m')) :
    AllocFramePreserved m m' [] ∧ NextAllocUpper m' := by
  unfold evalBoxClone at hCall
  cases hRead : readBoxFromRef m false pt selfPtr with
  | error k => rw [hRead] at hCall; cases hCall
  | ok b =>
    rw [hRead] at hCall
    dsimp only at hCall
    have hAfterEC : ∀ (lay : LayoutData) (count : Nat),
        ((if Nat.beq (count * lay.size) 0 then
            Except.ok (.boxPtr (danglingAligned lay.alignLog2) b.len, m)
          else
            match b.ptr.allocId with
            | none => Except.error .undefined
            | some srcAid =>
              match readBytes m ⟨srcAid, b.ptr.offsetBytes.toNat⟩
                  (count * lay.size) lay.alignLog2 with
              | .error k => Except.error k
              | .ok copiedBytes =>
                let r1 := allocHeapBuffer m (count * lay.size) lay.alignLog2
                match r1.2.allocId with
                | none => Except.error .undefined
                | some newAid =>
                  match writeBytes r1.1 ⟨newAid, 0⟩ lay.alignLog2
                      copiedBytes with
                  | .error k => Except.error k
                  | .ok m2 => Except.ok (.boxPtr r1.2 b.len, m2)) :
          Except FaultKind (Val × MemoryState)) = .ok (res, m') →
        AllocFramePreserved m m' [] ∧ NextAllocUpper m' := by
      intro lay count hBody
      cases hZ : Nat.beq (count * lay.size) 0 with
      | true =>
        rw [hZ] at hBody
        injection hBody with hPair
        have hm : m' = m := (congrArg Prod.snd hPair).symm
        subst hm
        exact ⟨fun a ha _ => ha, hUpper⟩
      | false =>
        rw [hZ] at hBody
        cases hAid : b.ptr.allocId with
        | none => rw [hAid] at hBody; cases hBody
        | some srcAid =>
          rw [hAid] at hBody
          dsimp only at hBody
          cases hRd : readBytes m ⟨srcAid, b.ptr.offsetBytes.toNat⟩
              (count * lay.size) lay.alignLog2 with
          | error k => rw [hRd] at hBody; cases hBody
          | ok copiedBytes =>
            rw [hRd] at hBody
            dsimp only at hBody
            let ⟨_, _, hUp1⟩ := allocHeapBuffer_disjoint hUpper hPos
              (count * lay.size) lay.alignLog2
            have hFrame := allocHeapBuffer_frame hUpper
              (count * lay.size) lay.alignLog2
            have hPtrEq : (allocHeapBuffer m (count * lay.size)
                lay.alignLog2).2 = ⟨some m.nextAllocId, 0, .isize⟩ := rfl
            rw [hPtrEq] at hBody
            dsimp only at hBody
            cases hWr : writeBytes (allocHeapBuffer m (count * lay.size)
                lay.alignLog2).1 ⟨m.nextAllocId, 0⟩ lay.alignLog2 copiedBytes
              with
            | error k => rw [hWr] at hBody; cases hBody
            | ok m2 =>
              rw [hWr] at hBody
              injection hBody with hPair
              have hm2 : m' = m2 := (congrArg Prod.snd hPair).symm
              subst hm2
              exact writeBytes_fresh_frame hUpper hUp1 hFrame
                (Nat.le_refl m.nextAllocId) hWr
    have hSlice : ∀ elem, b.pointee = .slice elem →
        AllocFramePreserved m m' [] ∧ NextAllocUpper m' := by
      intro elem hPt
      cases hLen : b.len with
      | none => rw [hPt, hLen] at hCall; cases hCall
      | some len =>
        rw [hPt, hLen] at hCall
        dsimp only at hCall
        cases hLay : layoutOfTyV2 elem with
        | none => rw [hLay] at hCall; cases hCall
        | some lay =>
          rw [hLay] at hCall
          dsimp only at hCall
          rw [← hLen] at hCall
          exact hAfterEC lay len.toNat hCall
    have hNonSlice : ∀ pt, (∀ elem, pt ≠ .slice elem) → b.pointee = pt →
        AllocFramePreserved m m' [] ∧ NextAllocUpper m' := by
      intro pt hNotSlice hPt
      cases hLen : b.len with
      | some len =>
        rw [hPt, hLen] at hCall
        cases pt with
        | slice elem => exact False.elim (hNotSlice elem rfl)
        | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | vec _ | box _ | rangeTo _ | rangeFrom _
        | unsupported | array _ _ | option _ | range _ | str | struct_ _ _ =>
          cases hCall
      | none =>
        rw [hPt, hLen] at hCall
        cases pt with
        | slice elem => exact False.elim (hNotSlice elem rfl)
        | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | vec _ | box _ | rangeTo _ | rangeFrom _
        | array _ _ | option _ | range _ | str | struct_ _ _
        | unsupported =>
          dsimp only at hCall
          cases hUn : isUnsizedTy _ with
          | true => rw [hUn] at hCall; cases hCall
          | false =>
            rw [hUn] at hCall
            cases hLay : layoutOfTyV2 _ with
            | none => rw [hLay] at hCall; cases hCall
            | some lay =>
              rw [hLay] at hCall
              dsimp only at hCall
              rw [← hLen] at hCall
              exact hAfterEC lay 1 hCall
    have hPtCases :
        (∃ elem, b.pointee = .slice elem) ∨
          (∃ pt, (∀ elem, pt ≠ .slice elem) ∧ b.pointee = pt) := by
      cases b.pointee with
      | slice elem => exact .inl ⟨elem, rfl⟩
      | bool => exact .inr ⟨.bool, (fun _ h => by cases h), rfl⟩
      | str => exact .inr ⟨.str, (fun _ h => by cases h), rfl⟩
      | array e n => exact .inr ⟨.array e n, (fun _ h => by cases h), rfl⟩
      | option e => exact .inr ⟨.option e, (fun _ h => by cases h), rfl⟩
      | range e => exact .inr ⟨.range e, (fun _ h => by cases h), rfl⟩
      | int w s => exact .inr ⟨.int w s, (fun _ h => by cases h), rfl⟩
      | unit => exact .inr ⟨.unit, (fun _ h => by cases h), rfl⟩
      | never => exact .inr ⟨.never, (fun _ h => by cases h), rfl⟩
      | char => exact .inr ⟨.char, (fun _ h => by cases h), rfl⟩
      | ordering => exact .inr ⟨.ordering, (fun _ h => by cases h), rfl⟩
      | enum ty => exact .inr ⟨.enum ty, (fun _ h => by cases h), rfl⟩
      | tuple fs => exact .inr ⟨.tuple fs, (fun _ h => by cases h), rfl⟩
      | ref mu pt => exact .inr ⟨.ref mu pt, (fun _ h => by cases h), rfl⟩
      | rawPtr mu pt =>
        exact .inr ⟨.rawPtr mu pt, (fun _ h => by cases h), rfl⟩
      | vec elem => exact .inr ⟨.vec elem, (fun _ h => by cases h), rfl⟩
      | box pt => exact .inr ⟨.box pt, (fun _ h => by cases h), rfl⟩
      | rangeTo e => exact .inr ⟨.rangeTo e, (fun _ h => by cases h), rfl⟩
      | rangeFrom e =>
        exact .inr ⟨.rangeFrom e, (fun _ h => by cases h), rfl⟩
      | unsupported =>
        exact .inr ⟨.unsupported, (fun _ h => by cases h), rfl⟩
      | struct_ l fs =>
        exact .inr ⟨.struct_ l fs, (fun _ h => by cases h), rfl⟩
    cases hPtCases with
    | inl hS =>
      cases hS with
      | intro elem hPt => exact hSlice elem hPt
    | inr hN =>
      cases hN with
      | intro pt hRest => exact hNonSlice pt hRest.1 hRest.2

/-- Allocation ids named by `p`'s provenance: the ids that `Box<[T]>::from`
may retire when it reallocates the buffer at `p`. -/
@[expose] def ptrAllocIds (p : PtrVal) : List AllocId :=
  match p.allocId with
  | some aid => [aid]
  | none => []

private theorem allocFramePreserved_trans {m0 m1 m2 : MemoryState}
    {retired : List AllocId} (h01 : AllocFramePreserved m0 m1 retired)
    (h12 : AllocFramePreserved m1 m2 []) :
    AllocFramePreserved m0 m2 retired :=
  fun a ha hNot => h12 a (h01 a ha hNot) (fun h => nomatch h)

/-- Deallocating `aid` keeps `nextAllocId` and every other allocation. -/
private theorem deallocateStack_frame {m m1 : MemoryState} {aid off : Nat}
    (hUpper : NextAllocUpper m)
    (hDealloc : deallocateStack m ⟨aid, off⟩ = .ok m1) :
    m1.nextAllocId = m.nextAllocId ∧ NextAllocUpper m1 ∧
      AllocFramePreserved m m1 [aid] := by
  unfold deallocateStack at hDealloc
  dsimp only at hDealloc
  cases hOff : Nat.beq off 0 with
  | false => rw [hOff] at hDealloc; cases hDealloc
  | true =>
    rw [hOff] at hDealloc
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hDealloc; cases hDealloc
    | some a =>
      rw [hFind] at hDealloc
      dsimp only at hDealloc
      cases hLive : a.live with
      | false => rw [hLive] at hDealloc; cases hDealloc
      | true =>
        rw [hLive] at hDealloc
        cases hMut : a.mutability with
        | shared => rw [hMut] at hDealloc; cases hDealloc
        | _ =>
          rw [hMut] at hDealloc
          injection hDealloc with hEq
          subst hEq
          let ⟨hMem, hId⟩ := findAllocation_some_mem hFind
          refine ⟨rfl, ?_, ?_⟩
          · intro b hb
            cases mem_replaceAllocation hb with
            | inl hEq => rw [hEq]; exact hUpper a hMem
            | inr hIn => exact hUpper b hIn
          · intro b hb hNot
            have hNe : a.allocId ≠ b.allocId := fun hEq =>
              hNot (by rw [← hEq, hId]; exact .head [])
            exact (findAllocation_replace_ne
              (a' := { a with mutability := .mut, live := false })
              hNe m.allocations).trans hb

/-- `Box<[T]>::from` preserves every allocation except the retired `Vec`
buffer, and when it reallocates a non-empty buffer the box points at a fresh
allocation disjoint from all of `m`. -/
theorem evalBoxFromVec_disjoint_and_frame {m m' : MemoryState}
    {elem : MirTy} {ptr : PtrVal} {cap len : UInt64} {res : Val}
    (hUpper : NextAllocUpper m) (hPos : 0 < m.nextAllocId)
    (hCall : evalBoxFromVec m elem ptr cap len = .ok (res, m')) :
    AllocFramePreserved m m' (ptrAllocIds ptr) ∧ NextAllocUpper m' ∧
      (Nat.beq cap.toNat len.toNat = false →
        ∀ lay, layoutOfTyV2 elem = some lay → 0 < len.toNat * lay.size →
        res = .boxPtr ⟨some m.nextAllocId, 0, .isize⟩ (some len) ∧
        AllocDisjoint m m.nextAllocId) := by
  unfold evalBoxFromVec at hCall
  dsimp only at hCall
  cases hVec : vecValidInMem m true ⟨elem, ptr, cap, len⟩ with
  | error k => rw [hVec] at hCall; cases hCall
  | ok u =>
    cases u
    rw [hVec] at hCall
    cases hLay : layoutOfTyV2 elem with
    | none => rw [hLay] at hCall; cases hCall
    | some lay =>
      rw [hLay] at hCall
      dsimp only at hCall
      have hDisj : AllocDisjoint m m.nextAllocId :=
        (allocHeapBuffer_disjoint hUpper hPos 0 0).2.1
      cases hKeep : (Nat.beq lay.size 0 || Nat.beq cap.toNat len.toNat) with
      | true =>
        rw [hKeep] at hCall
        injection hCall with hPair
        have hm : m' = m := (congrArg Prod.snd hPair).symm
        subst hm
        refine ⟨fun a ha _ => ha, hUpper, fun hNe lay' hLay' hPosSz => ?_⟩
        injection hLay' with hL
        subst hL
        rw [hNe] at hKeep
        have hZ : Nat.beq lay.size 0 = true := by
          cases hB : Nat.beq lay.size 0 with
          | true => rfl
          | false => rw [hB] at hKeep; cases hKeep
        rw [Nat.eq_of_beq_eq_true hZ, Nat.mul_zero] at hPosSz
        exact absurd hPosSz (Nat.lt_irrefl 0)
      | false =>
        rw [hKeep] at hCall
        cases hAid : ptr.allocId with
        | none => rw [hAid] at hCall; cases hCall
        | some oldAid =>
          rw [hAid] at hCall
          dsimp only at hCall
          have hIds : ptrAllocIds ptr = [oldAid] := by
            unfold ptrAllocIds; rw [hAid]
          rw [hIds]
          have hRetire : ∀ m1, retireHeapBuffer m ptr = .ok m1 →
              m1.nextAllocId = m.nextAllocId ∧ NextAllocUpper m1 ∧
                AllocFramePreserved m m1 [oldAid] := by
            intro m1 hRet
            unfold retireHeapBuffer at hRet
            rw [hAid] at hRet
            exact deallocateStack_frame hUpper hRet
          cases hZ : Nat.beq (len.toNat * lay.size) 0 with
          | true =>
            rw [hZ] at hCall
            cases hRet : retireHeapBuffer m ptr with
            | error k => rw [hRet] at hCall; cases hCall
            | ok m1 =>
              rw [hRet] at hCall
              dsimp only at hCall
              injection hCall with hPair
              have hm : m' = m1 := (congrArg Prod.snd hPair).symm
              subst hm
              let ⟨_, hUp1, hFr1⟩ := hRetire _ hRet
              refine ⟨hFr1, hUp1, fun _ lay' hLay' hPosSz => ?_⟩
              injection hLay' with hL
              subst hL
              rw [Nat.eq_of_beq_eq_true hZ] at hPosSz
              exact absurd hPosSz (Nat.lt_irrefl 0)
          | false =>
            rw [hZ] at hCall
            cases hRd : readBytes m ⟨oldAid, ptr.offsetBytes.toNat⟩
                (len.toNat * lay.size) lay.alignLog2 with
            | error k => rw [hRd] at hCall; cases hCall
            | ok bytes =>
              rw [hRd] at hCall
              cases hRet : retireHeapBuffer m ptr with
              | error k => rw [hRet] at hCall; cases hCall
              | ok m1 =>
                rw [hRet] at hCall
                dsimp only at hCall
                let ⟨hNext, hUp1, hFr1⟩ := hRetire _ hRet
                have hPos1 : 0 < m1.nextAllocId := hNext ▸ hPos
                let ⟨_, _, hUp2⟩ := allocHeapBuffer_disjoint hUp1 hPos1
                  (len.toNat * lay.size) lay.alignLog2
                have hFr2 := allocHeapBuffer_frame hUp1
                  (len.toNat * lay.size) lay.alignLog2
                have hPtrEq : (allocHeapBuffer m1 (len.toNat * lay.size)
                    lay.alignLog2).2 = ⟨some m1.nextAllocId, 0, .isize⟩ :=
                  rfl
                rw [hPtrEq] at hCall
                dsimp only at hCall
                have hCall' : (match writeBytes (allocHeapBuffer m1
                      (len.toNat * lay.size) lay.alignLog2).1
                      ⟨m1.nextAllocId, 0⟩ lay.alignLog2 bytes with
                    | .error k => .error k
                    | .ok m3 => .ok (Val.boxPtr
                        ⟨some m1.nextAllocId, 0, .isize⟩ (some len), m3) :
                    Except FaultKind (Val × MemoryState)) = .ok (res, m') :=
                  hCall
                cases hWr : writeBytes (allocHeapBuffer m1
                    (len.toNat * lay.size) lay.alignLog2).1
                    ⟨m1.nextAllocId, 0⟩ lay.alignLog2 bytes with
                | error k => rw [hWr] at hCall'; cases hCall'
                | ok m2 =>
                  rw [hWr] at hCall'
                  injection hCall' with hPair
                  have hr : res =
                      .boxPtr ⟨some m1.nextAllocId, 0, .isize⟩ (some len) :=
                    (congrArg Prod.fst hPair).symm
                  have hm : m' = m2 := (congrArg Prod.snd hPair).symm
                  subst hm
                  let ⟨hFr3, hUp3⟩ := writeBytes_fresh_frame hUp1 hUp2 hFr2
                    (Nat.le_refl m1.nextAllocId) hWr
                  refine ⟨allocFramePreserved_trans hFr1 hFr3, hUp3,
                    fun _ _ _ _ => ⟨?_, hDisj⟩⟩
                  rw [hr, hNext]

theorem evalVecLen_spec {m : MemoryState} {elem : MirTy}
    {selfPtr : PtrVal} {res : Val}
    (hCall : evalVecLen m elem selfPtr = .ok res) :
    ∃ v : VecModel,
      readVecFromRef m false elem selfPtr = .ok v ∧
      res = usizeScalarVal v.len.toNat := by
  unfold evalVecLen at hCall
  cases hRead : readVecFromRef m false elem selfPtr with
  | error k => rw [hRead] at hCall; cases hCall
  | ok v =>
    rw [hRead] at hCall
    injection hCall with hEq
    exact ⟨v, rfl, hEq.symm⟩

/-! ## Concrete Positive & Negative Program Canaries (Profile v2) -/

/-- Fuel-bounded Profile v2 fault-termination predicate over `evalStepV2`. -/
@[expose] def execFaultProgV2 (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initStateV2 p q with
  | .error k => k = expected
  | .ok s₀ =>
    execOutcomeStateV2 p (fun _ => False) (fun k => k = expected) fuel s₀

theorem faultProgV2_of_execFault {p : Program} {fuel : Nat} {q : Query}
    {expected : FaultKind} (hExec : execFaultProgV2 p fuel q expected) :
    ¬ WellFormedV2 p q := by
  intro hWf
  unfold execFaultProgV2 at hExec
  cases hInit : initStateV2 p q with
  | error k =>
    rw [hInit] at hExec
    let ⟨s0, hOk, _⟩ := hWf.1
    rw [hInit] at hOk
    cases hOk
  | ok s0 =>
    rw [hInit] at hExec
    let ⟨sEnd, res, hReach, hTerm, hRes⟩ :=
      exists_terminal_of_execOutcomeStateV2 hExec
    cases res with
    | step _ => exact hRes
    | done _ => exact hRes
    | fault k =>
      exact hWf.2 k (by unfold ReachesResultV2; rw [hInit]; exact
        ⟨sEnd, hReach, hTerm⟩)

private def u8Ty : MirTy := .int .i8 false
private def u64Ty : MirTy := .int .i64 false
private def usizeTy : MirTy := .int .isize false
private def vecU8Ty : MirTy := .vec u8Ty
private def boxSliceU8Ty : MirTy := .box (.slice u8Ty)
private def boxU64Ty : MirTy := .box u64Ty

private def u8Const (n : Nat) : Operand :=
  .constant ⟨u8Ty, .scalar (BitVec.ofNat 128 n)⟩

private def u64Const (n : Nat) : Operand :=
  .constant ⟨u64Ty, .scalar (BitVec.ofNat 128 n)⟩

private def usizeConst (n : Nat) : Operand :=
  .constant ⟨usizeTy, .scalar (BitVec.ofNat 128 n)⟩

private def unitConst : Operand := .constant ⟨.unit, .zeroSized⟩

@[expose] noncomputable def u8Val (n : Nat) : Val :=
  .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 n)⟩

@[expose] noncomputable def u64Val (n : Nat) : Val :=
  .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 n)⟩

@[expose] noncomputable def usizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 n)⟩

/-- Positive Canary 1 (`vecLifecycleProg`): exercises `Vec::<u8>::new`, `push`,
`len`, `resize`, `extend_from_slice`, `index`, `index_mut`, `deref`,
`Box<[u8]>::from`, and `Box<[u8]>::clone` end-to-end via `evalStepV2`.
Returns `(len, orig[0], cloned.len()) = (6, 10, 6)`; the returned caller
memory pins the cloned buffer's contents, including `cloned[1] = 42`.
`Box::from` retires the `Vec`'s 8-byte buffer (allocation `12`, `cap = 8`,
`len = 6`) and copies the six elements into a fresh 6-byte allocation
(`13`), so the stale `&v[0]`, `&mut v[1]`, and `&*v` locals keep pointing
at the dead allocation; `clone` allocates a further fresh disjoint buffer
(`15`). Both heap buffers outlive the call and are returned as
caller-visible memory. -/
def vecLifecycleBody : Body :=
  let locals : List MirTy := [
    .tuple [usizeTy, u8Ty, usizeTy],       -- 0: return
    .ref .shared (.slice u8Ty),            -- 1: input ext: &[u8]
    vecU8Ty,                               -- 2: v
    .ref .mut vecU8Ty,                     -- 3: &mut v
    .unit,                                 -- 4: ()
    .ref .shared vecU8Ty,                  -- 5: &v
    usizeTy,                               -- 6: len
    .ref .shared u8Ty,                     -- 7: &v[0]
    u8Ty,                                  -- 8: x0
    .ref .mut u8Ty,                        -- 9: &mut v[1]
    .ref .shared (.slice u8Ty),            -- 10: &*v
    boxSliceU8Ty,                          -- 11: b
    .ref .shared boxSliceU8Ty,             -- 12: &b
    boxSliceU8Ty,                          -- 13: c
    .ref .shared boxSliceU8Ty,             -- 14: &c
    .ref .shared (.slice u8Ty),            -- 15: &*c (box dereference)
    usizeTy                                -- 16: c.len()
  ]
  let bbs : List BasicBlock := [
    { statements := [.storageLive 2, .storageLive 3]
      terminator := .coreCall (.vecNew u8Ty) [] ⟨2, []⟩ (some 1) .unreachable },
    { statements := [.assign ⟨3, []⟩ (.ref .mut ⟨2, []⟩)]
      terminator := .coreCall .vecPush
        [.copy ⟨3, []⟩, u8Const 10] ⟨4, []⟩ (some 2) .unreachable },
    { statements := []
      terminator := .coreCall .vecPush
        [.copy ⟨3, []⟩, u8Const 20] ⟨4, []⟩ (some 3) .unreachable },
    { statements := [.storageLive 5]
      terminator := .coreCall .vecResize
        [.copy ⟨3, []⟩, usizeConst 4, u8Const 7] ⟨4, []⟩ (some 4)
        .unreachable },
    { statements := []
      terminator := .coreCall .vecExtendFromSlice
        [.copy ⟨3, []⟩, .copy ⟨1, []⟩] ⟨4, []⟩ (some 5) .unreachable },
    { statements := [.assign ⟨5, []⟩ (.ref .shared ⟨2, []⟩)]
      terminator := .coreCall .vecLen [.copy ⟨5, []⟩] ⟨6, []⟩ (some 6)
        .unreachable },
    { statements := []
      terminator := .coreCall .vecIndex
        [.copy ⟨5, []⟩, usizeConst 0] ⟨7, []⟩ (some 7) .unreachable },
    { statements := [.assign ⟨8, []⟩ (.use (.copy ⟨7, [.deref]⟩))]
      terminator := .coreCall .vecIndexMut
        [.copy ⟨3, []⟩, usizeConst 1] ⟨9, []⟩ (some 8) .unreachable },
    { statements := [
        .assign ⟨9, [.deref]⟩ (.use (u8Const 42)),
        .storageLive 10
      ]
      terminator := .coreCall .vecDeref [.copy ⟨5, []⟩] ⟨10, []⟩ (some 9)
        .unreachable },
    { statements := []
      terminator := .coreCall .boxFromVec [.move ⟨2, []⟩] ⟨11, []⟩ (some 10)
        .unreachable },
    { statements := [.assign ⟨12, []⟩ (.ref .shared ⟨11, []⟩)]
      terminator := .coreCall .boxClone [.copy ⟨12, []⟩] ⟨13, []⟩ (some 11)
        .unreachable },
    { statements := [
        .assign ⟨14, []⟩ (.ref .shared ⟨13, []⟩),
        .assign ⟨15, []⟩
          (.cast .boxAsRef (.copy ⟨13, []⟩) (.ref .shared (.slice u8Ty))),
        .assign ⟨16, []⟩ (.unaryOp .ptrMetadata (.copy ⟨15, []⟩)),
        .assign ⟨0, []⟩
          (.aggregateTuple [.copy ⟨6, []⟩, .copy ⟨8, []⟩, .copy ⟨16, []⟩])
      ]
      terminator := .return_ }
  ]
  { argumentCount := 1, isUnsafe := false,
    locals := locals, basicBlocks := bbs }

def vecLifecycleProg : Program :=
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit, bodies := [vecLifecycleBody] }

def extSliceAlloc : Allocation :=
  { allocId := 10, alignLog2 := 0, mutability := .shared,
    bytes := [.init 9 none, .init 11 none], live := true }

def vecLifecycleQuery : Query :=
  { args := [.slicePtr ⟨some 10, 0, .isize⟩ 2]
    callerMem := ⟨[extSliceAlloc]⟩ }


private inductive ChainStepV2 (p : Program) :
    State → StepResult State TerminalOut → Prop where
  | base {s : State} {r : StepResult State TerminalOut}
      (h : evalStepV2 p s = r) : ChainStepV2 p s r
  | step {s s' : State} {r : StepResult State TerminalOut}
      (h : evalStepV2 p s = .step s')
      (rest : ChainStepV2 p s' r) : ChainStepV2 p s r

private def isStepResult : StepResult State TerminalOut → Bool
  | .step _ => true
  | _ => false

private theorem reachesV2_chainStepV2 {p : Program} {s₀ s : State}
    {r : StepResult State TerminalOut}
    (hNonStep : isStepResult r = false)
    (hChain : ChainStepV2 p s₀ r) (hReach : ReachesV2 p s₀ s) :
    ChainStepV2 p s r := by
  induction hReach with
  | refl => exact hChain
  | tail _ hStep ih =>
    cases ih with
    | base hEnd =>
      let ⟨_, _, hEval⟩ := hStep
      have hEval' : evalStepV2 p _ = .step _ := hEval
      rw [hEnd] at hEval'
      rw [hEval'] at hNonStep
      cases hNonStep
    | step hNext rest =>
      let ⟨_, _, hEval⟩ := hStep
      have hEval' : evalStepV2 p _ = .step _ := hEval
      rw [hNext] at hEval'
      injection hEval' with hEq
      subst hEq
      exact rest

private theorem chainStepV2_reachesResultV2 {p : Program} {s : State}
    {r : StepResult State TerminalOut}
    (hChain : ChainStepV2 p s r) :
    ∃ sEnd, ReachesV2 p s sEnd ∧ StepV2 p sEnd r := by
  induction hChain with
  | @base sEnd r h => exact ⟨sEnd, .refl sEnd, ⟨0, rfl, h⟩⟩
  | @step s s' r h _ ih =>
    let ⟨sEnd, hRest, hEnd⟩ := ih
    exact ⟨sEnd, ReachesV2.head ⟨0, rfl, h⟩ hRest, hEnd⟩

private theorem chainStepV2_not_diverges {p : Program} {s : State}
    {r : StepResult State TerminalOut} (hNonStep : isStepResult r = false)
    (hChain : ChainStepV2 p s r) :
    ∀ trace : Nat → State, trace 0 = s →
      (∀ n : Nat, StepV2 p (trace n) (.step (trace (n + 1)))) → False := by
  induction hChain with
  | @base s r h =>
    intro trace h0 hSteps
    let ⟨_, _, hEval⟩ := hSteps 0
    have hEval' : evalStepV2 p (trace 0) = .step (trace 1) := hEval
    rw [h0, h] at hEval'
    rw [hEval'] at hNonStep
    cases hNonStep
  | @step s s' r h _ ih =>
    intro trace h0 hSteps
    let ⟨_, _, hEval⟩ := hSteps 0
    have hEval' : evalStepV2 p (trace 0) = .step (trace 1) := hEval
    rw [h0, h] at hEval'
    injection hEval' with hEq
    exact ih hNonStep (fun n => trace (n + 1)) hEq.symm
      (fun n => hSteps (n + 1))

private theorem spec_and_behaviorV2_of_chainStep {p : Program} {q : Query}
    {s₀ : State} {out : TerminalOut}
    (hInit : initStateV2 p q = .ok s₀)
    (hChain : ChainStepV2 p s₀ (.done out)) :
    WellFormedV2 p q ∧ BehaviorV2 p q out ∧ ¬ DivergesV2 p q := by
  have hNon : isStepResult (.done out) = false := rfl
  refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_, ?_⟩
  · intro k hFault
    unfold ReachesResultV2 at hFault
    rw [hInit] at hFault
    let ⟨s, hReach, _, _, hEval⟩ := hFault
    have hEval' : evalStepV2 p s = .fault k := hEval
    cases reachesV2_chainStepV2 hNon hChain hReach with
    | base hDone => rw [hDone] at hEval'; cases hEval'
    | step hStep _ => rw [hStep] at hEval'; cases hEval'
  · unfold BehaviorV2 ReachesResultV2
    rw [hInit]
    exact chainStepV2_reachesResultV2 hChain
  · intro hDiv
    let ⟨s0', hInit', trace, hTr0, hSteps⟩ := hDiv
    rw [hInit] at hInit'
    injection hInit' with hEq
    subst hEq
    exact chainStepV2_not_diverges hNon hChain trace hTr0 hSteps

private theorem not_wellFormedV2_of_chainStep_fault {p : Program} {q : Query}
    {s₀ : State} {k : FaultKind}
    (hInit : initStateV2 p q = .ok s₀)
    (hChain : ChainStepV2 p s₀ (.fault k)) :
    ¬ WellFormedV2 p q := by
  intro hWf
  let ⟨sEnd, hReach, hStep⟩ := chainStepV2_reachesResultV2 hChain
  exact hWf.2 k (by
    unfold ReachesResultV2; rw [hInit]; exact ⟨sEnd, hReach, hStep⟩)

private noncomputable def vl_va0 : Allocation :=
  Allocation.mk 11 3 .mut
    [.init 1 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def vl_va1 : Allocation :=
  Allocation.mk 11 3 .mut
    [.init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 8 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 1 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def vl_buf1 : Allocation :=
  Allocation.mk 12 0 .mut
    [.init 10 none, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
     .uninit] true
private noncomputable def vl_va2 : Allocation :=
  Allocation.mk 11 3 .mut
    [.init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 8 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 2 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def vl_buf2 : Allocation :=
  Allocation.mk 12 0 .mut
    [.init 10 none, .init 20 none, .uninit, .uninit, .uninit, .uninit,
     .uninit, .uninit] true
private noncomputable def vl_va3 : Allocation :=
  Allocation.mk 11 3 .mut
    [.init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 8 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 4 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def vl_buf3 : Allocation :=
  Allocation.mk 12 0 .mut
    [.init 10 none, .init 20 none, .init 7 none, .init 7 none, .uninit,
     .uninit, .uninit, .uninit] true
private noncomputable def vl_va4 : Allocation :=
  Allocation.mk 11 3 .mut
    [.init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 0 (some 12),
     .init 0 (some 12), .init 0 (some 12), .init 8 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 6 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def vl_buf4 : Allocation :=
  Allocation.mk 12 0 .mut
    [.init 10 none, .init 20 none, .init 7 none, .init 7 none,
     .init 9 none, .init 11 none, .uninit, .uninit] true
private noncomputable def vl_buf5 : Allocation :=
  Allocation.mk 12 0 .mut
    [.init 10 none, .init 42 none, .init 7 none, .init 7 none,
     .init 9 none, .init 11 none, .uninit, .uninit] true
private noncomputable def vl_va_uninit : Allocation :=
  Allocation.mk 11 3 .mut
    [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
     .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
     .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
     .uninit, .uninit, .uninit] true
private noncomputable def vl_buf5_dead : Allocation :=
  Allocation.mk 12 0 .mut
    [.init 10 none, .init 42 none, .init 7 none, .init 7 none,
     .init 9 none, .init 11 none, .uninit, .uninit] false
/-- Heap buffer of `b` in `vecLifecycleProg`: `Box<[u8]>::from` reallocates the
`Vec`'s 8-byte buffer (`cap = 8`, `len = 6`) into this exact 6-byte
allocation. It outlives the call, so it is caller-visible on return. -/
noncomputable def vecLifecycleBoxBuf : Allocation :=
  Allocation.mk 13 0 .mut
    [.init 10 none, .init 42 none, .init 7 none, .init 7 none,
     .init 9 none, .init 11 none] true
private noncomputable def vl_ba0 : Allocation :=
  Allocation.mk 14 3 .mut
    [.init 0 (some 13), .init 0 (some 13), .init 0 (some 13),
     .init 0 (some 13), .init 0 (some 13), .init 0 (some 13),
     .init 0 (some 13), .init 0 (some 13), .init 6 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none] true
/-- Heap buffer of `c = b.clone()` in `vecLifecycleProg`, a fresh allocation
disjoint from `vecLifecycleBoxBuf`. It is also caller-visible on return. -/
noncomputable def vecLifecycleCloneBuf : Allocation :=
  Allocation.mk 15 0 .mut
    [.init 10 none, .init 42 none, .init 7 none, .init 7 none,
     .init 9 none, .init 11 none] true
private noncomputable def vl_ca0 : Allocation :=
  Allocation.mk 16 3 .mut
    [.init 0 (some 15), .init 0 (some 15), .init 0 (some 15),
     .init 0 (some 15), .init 0 (some 15), .init 0 (some 15),
     .init 0 (some 15), .init 0 (some 15), .init 6 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none] true
private noncomputable def vl_s0 : State :=
  State.mk [FrameState.mk 0 0 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .dead, .dead, .immediate (some .unit), .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 11 [extSliceAlloc])
private noncomputable def vl_s1 : State :=
  State.mk [FrameState.mk 0 0 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .immediate none, .dead, .immediate (some .unit), .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .dead, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 11 [extSliceAlloc])
private noncomputable def vl_s2 : State :=
  State.mk [FrameState.mk 0 0 2
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .immediate none, .immediate none, .immediate (some .unit), .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .dead, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 11 [extSliceAlloc])
private noncomputable def vl_s3 : State :=
  State.mk [FrameState.mk 0 1 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .immediate (some (.vec (danglingAligned 0) 0 0)), .immediate none,
      .immediate (some .unit), .dead, .immediate none, .immediate none,
      .immediate none, .immediate none, .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 11 [extSliceAlloc])
private noncomputable def vl_s4 : State :=
  State.mk [FrameState.mk 0 1 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .dead, .immediate none, .immediate none,
      .immediate none, .immediate none, .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 12 [extSliceAlloc, vl_va0])
private noncomputable def vl_s5 : State :=
  State.mk [FrameState.mk 0 2 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .dead, .immediate none, .immediate none,
      .immediate none, .immediate none, .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va1, vl_buf1])
private noncomputable def vl_s6 : State :=
  State.mk [FrameState.mk 0 3 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .dead, .immediate none, .immediate none,
      .immediate none, .immediate none, .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va2, vl_buf2])
private noncomputable def vl_s7 : State :=
  State.mk [FrameState.mk 0 3 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none, .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va2, vl_buf2])
private noncomputable def vl_s8 : State :=
  State.mk [FrameState.mk 0 4 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none, .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va3, vl_buf3])
private noncomputable def vl_s9 : State :=
  State.mk [FrameState.mk 0 5 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none, .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf4])
private noncomputable def vl_s10 : State :=
  State.mk [FrameState.mk 0 5 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate none, .immediate none, .immediate none, .immediate none,
      .dead, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf4])
private noncomputable def vl_s11 : State :=
  State.mk [FrameState.mk 0 6 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate none, .immediate none,
      .immediate none, .dead, .immediate none, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf4])
private noncomputable def vl_s12 : State :=
  State.mk [FrameState.mk 0 7 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate none, .immediate none, .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf4])
private noncomputable def vl_s13 : State :=
  State.mk [FrameState.mk 0 7 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)), .immediate none, .dead,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf4])
private noncomputable def vl_s14 : State :=
  State.mk [FrameState.mk 0 8 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)), .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf4])
private noncomputable def vl_s15 : State :=
  State.mk [FrameState.mk 0 8 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)), .dead, .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf5])
private noncomputable def vl_s16 : State :=
  State.mk [FrameState.mk 0 8 2
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)), .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf5])
private noncomputable def vl_s17 : State :=
  State.mk [FrameState.mk 0 9 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .immediate none,
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 13 [extSliceAlloc, vl_va4, vl_buf5])
private noncomputable def vl_s18 : State :=
  State.mk [FrameState.mk 0 10 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)),
      .immediate (some (.boxPtr ⟨some 13, 0, .isize⟩ (some 6))),
      .immediate none, .immediate none, .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 14 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf])
private noncomputable def vl_s19 : State :=
  State.mk [FrameState.mk 0 10 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .indirect ⟨14,
      0⟩, .immediate (some (.ptr ⟨some 14, 0, .isize⟩)), .immediate none,
      .immediate none, .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 15 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf, vl_ba0])
private noncomputable def vl_s20 : State :=
  State.mk [FrameState.mk 0 11 0
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .indirect ⟨14,
      0⟩, .immediate (some (.ptr ⟨some 14, 0, .isize⟩)),
      .immediate (some (.boxPtr ⟨some 15, 0, .isize⟩ (some 6))),
      .immediate none, .immediate none, .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 16 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf, vl_ba0, vecLifecycleCloneBuf])
private noncomputable def vl_s21 : State :=
  State.mk [FrameState.mk 0 11 1
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .indirect ⟨14,
      0⟩, .immediate (some (.ptr ⟨some 14, 0, .isize⟩)), .indirect ⟨16, 0⟩,
      .immediate (some (.ptr ⟨some 16, 0, .isize⟩)), .immediate none,
      .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 17 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf, vl_ba0, vecLifecycleCloneBuf, vl_ca0])
private noncomputable def vl_s22 : State :=
  State.mk [FrameState.mk 0 11 2
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .indirect ⟨14,
      0⟩, .immediate (some (.ptr ⟨some 14, 0, .isize⟩)), .indirect ⟨16, 0⟩,
      .immediate (some (.ptr ⟨some 16, 0, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 15, 0, .isize⟩ 6)), .immediate none] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 17 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf, vl_ba0, vecLifecycleCloneBuf, vl_ca0])
private noncomputable def vl_s23 : State :=
  State.mk [FrameState.mk 0 11 3
    [.immediate none, .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .indirect ⟨14,
      0⟩, .immediate (some (.ptr ⟨some 14, 0, .isize⟩)), .indirect ⟨16, 0⟩,
      .immediate (some (.ptr ⟨some 16, 0, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 15, 0, .isize⟩ 6)),
      .immediate (some (usizeVal 6))] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 17 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf, vl_ba0, vecLifecycleCloneBuf, vl_ca0])
private noncomputable def vl_s24 : State :=
  State.mk [FrameState.mk 0 11 4
    [.immediate (some (.tuple [usizeVal 6, u8Val 10, usizeVal 6])),
      .immediate (some (.slicePtr ⟨some 10, 0, .isize⟩ 2)),
      .indirect ⟨11, 0⟩, .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some .unit), .immediate (some (.ptr ⟨some 11, 0, .isize⟩)),
      .immediate (some (usizeVal 6)), .immediate (some (.ptr ⟨some 12, 0,
      .isize⟩)), .immediate (some (u8Val 10)),
      .immediate (some (.ptr ⟨some 12, 1, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 12, 0, .isize⟩ 6)), .indirect ⟨14,
      0⟩, .immediate (some (.ptr ⟨some 14, 0, .isize⟩)), .indirect ⟨16, 0⟩,
      .immediate (some (.ptr ⟨some 16, 0, .isize⟩)),
      .immediate (some (.slicePtr ⟨some 15, 0, .isize⟩ 6)),
      .immediate (some (usizeVal 6))] none none none]
    ⟨[extSliceAlloc]⟩ (MemoryState.mk 17 [extSliceAlloc, vl_va_uninit,
      vl_buf5_dead, vecLifecycleBoxBuf, vl_ba0, vecLifecycleCloneBuf, vl_ca0])
private theorem vl_init :
    initStateV2 vecLifecycleProg vecLifecycleQuery = .ok vl_s0 := by rfl
private theorem vl_step0 : evalStepV2 vecLifecycleProg vl_s0 = .step vl_s1 :=
  by rfl
private theorem vl_step1 : evalStepV2 vecLifecycleProg vl_s1 = .step vl_s2 :=
  by rfl
private theorem vl_step2 : evalStepV2 vecLifecycleProg vl_s2 = .step vl_s3 :=
  by rfl
private theorem vl_step3 : evalStepV2 vecLifecycleProg vl_s3 = .step vl_s4 :=
  by rfl
private theorem vl_step4 : evalStepV2 vecLifecycleProg vl_s4 = .step vl_s5 :=
  by rfl
private theorem vl_step5 : evalStepV2 vecLifecycleProg vl_s5 = .step vl_s6 :=
  by rfl
private theorem vl_step6 : evalStepV2 vecLifecycleProg vl_s6 = .step vl_s7 :=
  by rfl
private theorem vl_step7 : evalStepV2 vecLifecycleProg vl_s7 = .step vl_s8 :=
  by rfl
private theorem vl_step8 : evalStepV2 vecLifecycleProg vl_s8 = .step vl_s9 :=
  by rfl
private theorem vl_step9 : evalStepV2 vecLifecycleProg vl_s9 = .step vl_s10 :=
  by rfl
private theorem vl_step10 : evalStepV2 vecLifecycleProg vl_s10 = .step vl_s11 :=
  by rfl
private theorem vl_step11 : evalStepV2 vecLifecycleProg vl_s11 = .step vl_s12 :=
  by rfl
private theorem vl_step12 : evalStepV2 vecLifecycleProg vl_s12 = .step vl_s13 :=
  by rfl
private theorem vl_step13 : evalStepV2 vecLifecycleProg vl_s13 = .step vl_s14 :=
  by rfl
private theorem vl_step14 : evalStepV2 vecLifecycleProg vl_s14 = .step vl_s15 :=
  by rfl
private theorem vl_step15 : evalStepV2 vecLifecycleProg vl_s15 = .step vl_s16 :=
  by rfl
private theorem vl_step16 : evalStepV2 vecLifecycleProg vl_s16 = .step vl_s17 :=
  by rfl
private theorem vl_step17 : evalStepV2 vecLifecycleProg vl_s17 = .step vl_s18 :=
  by rfl
private theorem vl_step18 : evalStepV2 vecLifecycleProg vl_s18 = .step vl_s19 :=
  by rfl
private theorem vl_step19 : evalStepV2 vecLifecycleProg vl_s19 = .step vl_s20 :=
  by rfl
private theorem vl_step20 : evalStepV2 vecLifecycleProg vl_s20 = .step vl_s21 :=
  by rfl
private theorem vl_step21 : evalStepV2 vecLifecycleProg vl_s21 = .step vl_s22 :=
  by rfl
private theorem vl_step22 : evalStepV2 vecLifecycleProg vl_s22 = .step vl_s23 :=
  by rfl
private theorem vl_step23 : evalStepV2 vecLifecycleProg vl_s23 = .step vl_s24 :=
  by rfl
private theorem vl_step24 :
    evalStepV2 vecLifecycleProg vl_s24 =
      .done (.returned ⟨.tuple [usizeVal 6, u8Val 10, usizeVal 6],
        ⟨[extSliceAlloc, vecLifecycleBoxBuf, vecLifecycleCloneBuf]⟩⟩) :=
  by rfl


theorem vecLifecycle_verified :
    WellFormedV2 vecLifecycleProg vecLifecycleQuery ∧
    BehaviorV2 vecLifecycleProg vecLifecycleQuery
      (.returned ⟨.tuple [usizeVal 6, u8Val 10, usizeVal 6],
        ⟨[extSliceAlloc, vecLifecycleBoxBuf, vecLifecycleCloneBuf]⟩⟩) ∧
    ¬ DivergesV2 vecLifecycleProg vecLifecycleQuery :=
  spec_and_behaviorV2_of_chainStep vl_init
    (ChainStepV2.step vl_step0 (ChainStepV2.step vl_step1
      (ChainStepV2.step vl_step2 (ChainStepV2.step vl_step3
      (ChainStepV2.step vl_step4 (ChainStepV2.step vl_step5
      (ChainStepV2.step vl_step6 (ChainStepV2.step vl_step7
      (ChainStepV2.step vl_step8 (ChainStepV2.step vl_step9
      (ChainStepV2.step vl_step10 (ChainStepV2.step vl_step11
      (ChainStepV2.step vl_step12 (ChainStepV2.step vl_step13
      (ChainStepV2.step vl_step14 (ChainStepV2.step vl_step15
      (ChainStepV2.step vl_step16 (ChainStepV2.step vl_step17
      (ChainStepV2.step vl_step18 (ChainStepV2.step vl_step19
      (ChainStepV2.step vl_step20 (ChainStepV2.step vl_step21
      (ChainStepV2.step vl_step22 (ChainStepV2.step vl_step23
      (ChainStepV2.base vl_step24)))))))))))))))))))))))))

/-- Positive Canary 2 (`boxNewAndCastDerefProg`): `Box::<u64>::new(0x1234)`
followed by `.cast .boxAsRef` and a `*ref` read returns `0x1234`. The
box's heap allocation (`boxNewHeapAlloc`) outlives the call and is returned
as caller-visible memory. -/
def boxNewAndCastDerefProg : Program :=
  let locals : List MirTy := [
    u64Ty,
    boxU64Ty,
    .ref .shared u64Ty
  ]
  let bbs : List BasicBlock := [
    { statements := [.storageLive 1, .storageLive 2]
      terminator := .coreCall (.boxNew u64Ty)
        [u64Const 0x1234] ⟨1, []⟩ (some 1) .unreachable },
    { statements := [
        .assign ⟨2, []⟩
          (.cast .boxAsRef (.copy ⟨1, []⟩) (.ref .shared u64Ty)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩))
      ]
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 0, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

/-- The heap allocation of `Box::<u64>::new(0x1234)` in
`boxNewAndCastDerefProg`: allocation id `2` (id `1` is the reserved return
place), 8-byte aligned, holding `0x1234` little-endian. -/
noncomputable def boxNewHeapAlloc : Allocation :=
  Allocation.mk 2 3 .mut
    [.init 0x34 none, .init 0x12 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true

theorem boxNewAndCastDeref_verified :
    WellFormedV2 boxNewAndCastDerefProg { args := [] } ∧
    BehaviorV2 boxNewAndCastDerefProg { args := [] }
      (.returned ⟨u64Val 0x1234, ⟨[boxNewHeapAlloc]⟩⟩) := by
  have hExec : execProgV2 boxNewAndCastDerefProg 10 { args := [] }
      (fun out => out = .returned ⟨u64Val 0x1234, ⟨[boxNewHeapAlloc]⟩⟩) := by
    rfl
  let ⟨h1, h2, _⟩ := spec_and_behaviorV2_of_exec_eq hExec
  exact ⟨h1, h2⟩

/-- Positive Canary 3 (`zstVecAndBoxProg`): `Vec::<()>::new()`, `push(())`,
`len()`, and `Box::<()>::new(())` succeed without heap allocation. -/
def zstVecAndBoxProg : Program :=
  let locals : List MirTy := [
    .tuple [usizeTy, .box .unit],
    .vec .unit,
    .ref .mut (.vec .unit),
    .unit,
    .ref .shared (.vec .unit),
    usizeTy,
    .box .unit
  ]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall (.vecNew .unit) [] ⟨1, []⟩ (some 1)
        .unreachable },
    { statements := [.assign ⟨2, []⟩ (.ref .mut ⟨1, []⟩)]
      terminator := .coreCall .vecPush
        [.copy ⟨2, []⟩, unitConst] ⟨3, []⟩ (some 2) .unreachable },
    { statements := [.assign ⟨4, []⟩ (.ref .shared ⟨1, []⟩)]
      terminator := .coreCall .vecLen [.copy ⟨4, []⟩] ⟨5, []⟩ (some 3)
        .unreachable },
    { statements := []
      terminator := .coreCall (.boxNew .unit) [unitConst] ⟨6, []⟩ (some 4)
        .unreachable },
    { statements := [
        .assign ⟨0, []⟩ (.aggregateTuple [.copy ⟨5, []⟩, .copy ⟨6, []⟩])
      ]
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 0, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

private noncomputable def zstVecAlloc2 : Allocation :=
  Allocation.mk 2 3 .mut
    [.init 1 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def zstVecAlloc2Len1 : Allocation :=
  Allocation.mk 2 3 .mut
    [.init 1 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 1 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 1 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def zst_s0 : State :=
  State.mk [FrameState.mk 0 0 0
    [.immediate none, .immediate none, .immediate none,
      .immediate (some .unit), .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 2 [])
private noncomputable def zst_s1 : State :=
  State.mk [FrameState.mk 0 1 0
    [.immediate none, .immediate (some (.vec (danglingAligned 0) 0 0)),
      .immediate none, .immediate (some .unit), .immediate none,
      .immediate none, .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 2 [])
private noncomputable def zst_s2 : State :=
  State.mk [FrameState.mk 0 1 1
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [zstVecAlloc2])
private noncomputable def zst_s3 : State :=
  State.mk [FrameState.mk 0 2 0
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate none, .immediate none,
      .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [zstVecAlloc2Len1])
private noncomputable def zst_s4 : State :=
  State.mk [FrameState.mk 0 2 1
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate none, .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [zstVecAlloc2Len1])
private noncomputable def zst_s5 : State :=
  State.mk [FrameState.mk 0 3 0
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some (usizeVal 1)), .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [zstVecAlloc2Len1])
private noncomputable def zst_s6 : State :=
  State.mk [FrameState.mk 0 4 0
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some (usizeVal 1)),
      .immediate (some (.boxPtr (danglingAligned 0) none))] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [zstVecAlloc2Len1])
private noncomputable def zst_s7 : State :=
  State.mk [FrameState.mk 0 4 1
    [.immediate (some (.tuple [usizeVal 1,
      .boxPtr (danglingAligned 0) none])), .indirect ⟨2, 0⟩,
      .immediate (some (.ptr ⟨some 2, 0, .isize⟩)), .immediate (some .unit),
      .immediate (some (.ptr ⟨some 2, 0, .isize⟩)),
      .immediate (some (usizeVal 1)),
      .immediate (some (.boxPtr (danglingAligned 0) none))] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [zstVecAlloc2Len1])
private theorem zst_init : initStateV2 zstVecAndBoxProg { args :=
  [] } = .ok zst_s0 := by rfl
private theorem zst_step0 : evalStepV2 zstVecAndBoxProg zst_s0 = .step zst_s1 :=
  by rfl
private theorem zst_step1 : evalStepV2 zstVecAndBoxProg zst_s1 = .step zst_s2 :=
  by rfl
private theorem zst_step2 : evalStepV2 zstVecAndBoxProg zst_s2 = .step zst_s3 :=
  by rfl
private theorem zst_step3 : evalStepV2 zstVecAndBoxProg zst_s3 = .step zst_s4 :=
  by rfl
private theorem zst_step4 : evalStepV2 zstVecAndBoxProg zst_s4 = .step zst_s5 :=
  by rfl
private theorem zst_step5 : evalStepV2 zstVecAndBoxProg zst_s5 = .step zst_s6 :=
  by rfl
private theorem zst_step6 : evalStepV2 zstVecAndBoxProg zst_s6 = .step zst_s7 :=
  by rfl
private theorem zst_step7 :
    evalStepV2 zstVecAndBoxProg zst_s7 =
      .done (.returned ⟨.tuple [usizeVal 1, .boxPtr (danglingAligned 0) none],
        ⟨[]⟩⟩) :=
  by rfl


theorem zstVecAndBox_verified :
    WellFormedV2 zstVecAndBoxProg { args := [] } ∧
    BehaviorV2 zstVecAndBoxProg { args := [] }
      (.returned ⟨.tuple [usizeVal 1, .boxPtr (danglingAligned 0) none],
        ⟨[]⟩⟩) :=
  let h := spec_and_behaviorV2_of_chainStep zst_init
    (ChainStepV2.step zst_step0 (ChainStepV2.step zst_step1
      (ChainStepV2.step zst_step2 (ChainStepV2.step zst_step3
      (ChainStepV2.step zst_step4 (ChainStepV2.step zst_step5
      (ChainStepV2.step zst_step6 (ChainStepV2.base zst_step7))))))))
  ⟨h.1, h.2.1⟩

/-- Positive Canary 4: `Vec::<u8>::new()` is an empty dangling `Vec`, and
`reserve(4)` on a full `Vec<u8>` (`cap = len = 1`) grows the capacity to at
least `len + 4 = 5` and keeps `len`. -/
theorem m2_new_reserve_canary :
    (match evalVecNew u8Ty with
     | .ok (.vec _ 0 0) => True
     | _ => False) ∧
    let m0 := MemoryState.empty
    let vecHandle : Allocation :=
      { allocId := 1, alignLog2 := 3, mutability := .mut,
        bytes := [
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2),
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    let bufAlloc : Allocation :=
      { allocId := 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 99 none], live := true }
    let m : MemoryState :=
      { m0 with nextAllocId := 3, allocations := [vecHandle, bufAlloc] }
    let selfPtr : PtrVal := ⟨some 1, 0, .isize⟩
    match evalVecReserve m u8Ty selfPtr 4 with
    | .ok mRes =>
      match readVecFromRef mRes false u8Ty selfPtr with
      | .ok v => Nat.ble 5 v.cap.toNat = true ∧ v.len.toNat = 1
      | .error _ => False
    | .error _ => False :=
  ⟨True.intro, rfl, rfl⟩

/-- Negative Canary (self-aliasing `extend_from_slice`): extending a full
`Vec<u8>` (`cap = len = 1`) from a slice of its own buffer grows the `Vec`,
which retires that buffer before the source is read, so the call faults with
`.undefined` instead of copying bytes from the dead allocation. -/
theorem vec_extend_from_own_buffer_grow_faults :
    let vecHandle : Allocation :=
      { allocId := 1, alignLog2 := 3, mutability := .mut,
        bytes := [
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2),
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    let bufAlloc : Allocation :=
      { allocId := 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 99 none], live := true }
    let m : MemoryState :=
      { MemoryState.empty with
        nextAllocId := 3, allocations := [vecHandle, bufAlloc] }
    evalVecExtendFromSlice m u8Ty ⟨some 1, 0, .isize⟩ ⟨some 2, 0, .isize⟩ 1 =
      .error .undefined :=
  rfl

/-- Self-aliasing `extend_from_slice` without growth (`cap = 4`, `len = 1`,
four initialized buffer bytes): copying `[0, 1)` to `[1, 2)` succeeds, but a
two-element source `[0, 2)` overlaps the destination `[1, 3)`, which upstream's
`ptr::copy_nonoverlapping` makes UB, so it faults with `.undefined`. -/
theorem vec_extend_from_own_buffer_overlap_canary :
    let vecHandle : Allocation :=
      { allocId := 1, alignLog2 := 3, mutability := .mut,
        bytes := [
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2),
          .init 4 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    let bufAlloc : Allocation :=
      { allocId := 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 5 none, .init 6 none, .init 7 none, .init 8 none],
        live := true }
    let m : MemoryState :=
      { MemoryState.empty with
        nextAllocId := 3, allocations := [vecHandle, bufAlloc] }
    (match evalVecExtendFromSlice m u8Ty ⟨some 1, 0, .isize⟩
        ⟨some 2, 0, .isize⟩ 1 with
     | .ok _ => true
     | .error _ => false) = true ∧
    evalVecExtendFromSlice m u8Ty ⟨some 1, 0, .isize⟩ ⟨some 2, 0, .isize⟩ 2 =
      .error .undefined :=
  ⟨rfl, rfl⟩

/-- Owned `Vec` and `Box` values contribute the mutable span of their heap
buffer to `refAccessSpans`, so two owned `Vec<u8>` arguments (or a `Vec` and a
`Box`) sharing one buffer fail the entry and return disjointness check. -/
theorem owned_heap_buffers_shared_not_disjoint :
    let vT : MirTy := .vec (.int .i8 false)
    let bT : MirTy := .box (.slice (.int .i8 false))
    spansPairwiseDisjoint (refAccessSpansList [vT, vT]
        [.vec ⟨some 1, 0, .isize⟩ 8 1, .vec ⟨some 1, 0, .isize⟩ 8 1]) =
      false ∧
    spansPairwiseDisjoint (refAccessSpansList [vT, bT]
        [.vec ⟨some 1, 0, .isize⟩ 8 1, .boxPtr ⟨some 1, 0, .isize⟩ (some 8)]) =
      false ∧
    spansPairwiseDisjoint (refAccessSpansList [vT, vT]
        [.vec ⟨some 1, 0, .isize⟩ 8 1, .vec ⟨some 2, 0, .isize⟩ 8 1]) =
      true :=
  ⟨rfl, rfl, rfl⟩

/-- `resize` to a shorter length (`truncate`) on a `Vec<u8>` (`cap = len = 2`,
buffer `[5, 6]`) sets `len = 1` and keeps the tail byte `6`, as Rust and Miri
do: `ptr::drop_in_place` on `u8` elements is a no-op. -/
theorem vec_resize_truncate_keeps_tail_bytes :
    let vecHandle : Allocation :=
      { allocId := 1, alignLog2 := 3, mutability := .mut,
        bytes := [
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2), .init 0 (some 2),
          .init 0 (some 2), .init 0 (some 2),
          .init 2 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 2 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    let bufAlloc : Allocation :=
      { allocId := 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 5 none, .init 6 none], live := true }
    let m : MemoryState :=
      { MemoryState.empty with
        nextAllocId := 3, allocations := [vecHandle, bufAlloc] }
    let selfPtr : PtrVal := ⟨some 1, 0, .isize⟩
    match evalVecResize m u8Ty selfPtr 1 (u8Val 0) with
    | .ok mRes =>
      readBytes mRes ⟨2, 1⟩ 1 0 = .ok [.init 6 none] ∧
      (match readVecFromRef mRes false u8Ty selfPtr with
       | .ok v => v.len.toNat = 1
       | .error _ => False)
    | .error _ => False :=
  ⟨rfl, rfl⟩

/-- Negative Canary 1: `Vec::index` out-of-bounds (`idx == len`) is a
bounds-check panic, which faults with `.unsupported`. -/
def negVecIndexOobProg : Program :=
  let locals : List MirTy := [
    u8Ty, vecU8Ty, .ref .shared vecU8Ty, .ref .shared u8Ty
  ]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall (.vecNew u8Ty) [] ⟨1, []⟩ (some 1) .unreachable },
    { statements := [.assign ⟨2, []⟩ (.ref .shared ⟨1, []⟩)]
      terminator := .coreCall .vecIndex
        [.copy ⟨2, []⟩, usizeConst 0] ⟨3, []⟩ (some 2) .unreachable },
    { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨3, [.deref]⟩))]
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 0, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

theorem neg_vec_index_oob_faults :
    ¬ WellFormedV2 negVecIndexOobProg { args := [] } :=
  faultProgV2_of_execFault (expected := .unsupported) (by
    change execFaultProgV2 negVecIndexOobProg 10 { args := [] } .unsupported
    rfl)

/-- Negative Canary 2: `Vec::index_mut` out-of-bounds is a bounds-check panic,
which faults with `.unsupported`. -/
def negVecIndexMutOobProg : Program :=
  let locals : List MirTy := [
    .unit, vecU8Ty, .ref .mut vecU8Ty, .ref .mut u8Ty
  ]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall (.vecNew u8Ty) [] ⟨1, []⟩ (some 1) .unreachable },
    { statements := [.assign ⟨2, []⟩ (.ref .mut ⟨1, []⟩)]
      terminator := .coreCall .vecIndexMut
        [.copy ⟨2, []⟩, usizeConst 0] ⟨3, []⟩ (some 2) .unreachable },
    { statements := [
        .assign ⟨3, [.deref]⟩ (.use (u8Const 1)),
        .assign ⟨0, []⟩ (.use unitConst)
      ]
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 0, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

theorem neg_vec_index_mut_oob_faults :
    ¬ WellFormedV2 negVecIndexMutOobProg { args := [] } :=
  faultProgV2_of_execFault (expected := .unsupported) (by
    change execFaultProgV2 negVecIndexMutOobProg 10 { args := [] }
      .unsupported
    rfl)

/-- Negative Canary 3: `Vec::<u64>::with_capacity(2^62)` capacity overflow
(`2^62 * 8 > isize::MAX`) is a capacity-overflow panic, which faults with
`.unsupported`. -/
def negVecWithCapOverflowProg : Program :=
  let locals : List MirTy := [.vec u64Ty]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall (.vecWithCapacity u64Ty)
        [usizeConst (Nat.pow 2 62)] ⟨0, []⟩ (some 1) .unreachable },
    { statements := []
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 0, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

theorem neg_vec_with_capacity_overflow_faults :
    ¬ WellFormedV2 negVecWithCapOverflowProg { args := [] } :=
  faultProgV2_of_execFault (expected := .unsupported) (by
    change execFaultProgV2 negVecWithCapOverflowProg 5 { args := [] }
      .unsupported
    rfl)

/-- Helper body taking `&Vec<u8>` and returning `v.len()`. -/
def readVecLenProg : Program :=
  let locals : List MirTy := [usizeTy, .ref .shared vecU8Ty]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall .vecLen [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1)
        .unreachable },
    { statements := []
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 1, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

/-- Negative Canary 4: dangling buffer `allocId = some 99` rejected on entry. -/
theorem neg_dangling_vec_arg_rejected :
    let badVec : Allocation :=
      { allocId := 10, alignLog2 := 3, mutability := .shared,
        bytes := [
          .init 0 (some 99), .init 0 (some 99), .init 0 (some 99),
          .init 0 (some 99), .init 0 (some 99), .init 0 (some 99),
          .init 0 (some 99), .init 0 (some 99),
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    ¬ WellFormedV2 readVecLenProg
        { args := [.ptr ⟨some 10, 0, .isize⟩], callerMem := ⟨[badVec]⟩ } :=
  faultProgV2_of_execFault (fuel := 0) (expected := .undefined) (by rfl)

/-- Negative Canary 5: uninitialized buffer byte inside `len = 1` rejected. -/
theorem neg_uninit_vec_buf_rejected :
    let vecSlot : Allocation :=
      { allocId := 10, alignLog2 := 3, mutability := .shared,
        bytes := [
          .init 0 (some 11), .init 0 (some 11), .init 0 (some 11),
          .init 0 (some 11), .init 0 (some 11), .init 0 (some 11),
          .init 0 (some 11), .init 0 (some 11),
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    let uninitBuf : Allocation :=
      { allocId := 11, alignLog2 := 0, mutability := .mut,
        bytes := [.uninit], live := true }
    ¬ WellFormedV2 readVecLenProg
        { args := [.ptr ⟨some 10, 0, .isize⟩],
          callerMem := ⟨[vecSlot, uninitBuf]⟩ } :=
  faultProgV2_of_execFault (fuel := 0) (expected := .undefined) (by rfl)

/-- Negative Canary 6: misaligned `Vec<u64>` backing buffer (`offset = 1`)
rejected on entry. -/
def readVecU64LenProg : Program :=
  let locals : List MirTy := [usizeTy, .ref .shared (.vec u64Ty)]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall .vecLen [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1)
        .unreachable },
    { statements := []
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 1, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

theorem neg_misaligned_vec_u64_rejected :
    let vecSlot : Allocation :=
      { allocId := 10, alignLog2 := 3, mutability := .shared,
        bytes := [
          .init 1 (some 11), .init 0 (some 11), .init 0 (some 11),
          .init 0 (some 11), .init 0 (some 11), .init 0 (some 11),
          .init 0 (some 11), .init 0 (some 11),
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 1 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    let bufAlloc : Allocation :=
      { allocId := 11, alignLog2 := 3, mutability := .mut,
        bytes := List.replicate 16 (.init 0 none), live := true }
    ¬ WellFormedV2 readVecU64LenProg
        { args := [.ptr ⟨some 10, 0, .isize⟩],
          callerMem := ⟨[vecSlot, bufAlloc]⟩ } :=
  faultProgV2_of_execFault (fuel := 0) (expected := .undefined) (by rfl)

/-- Negative Canary 7: aliasing `&mut Vec<u8>` arguments rejected by
`spansPairwiseDisjoint`. -/
def aliasingMutVecProg : Program :=
  let locals : List MirTy :=
    [.unit, .ref .mut vecU8Ty, .ref .mut vecU8Ty]
  let bbs : List BasicBlock := [
    { statements := [.assign ⟨0, []⟩ (.use unitConst)]
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 2, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

theorem neg_aliasing_mut_vec_rejected :
    let vecSlot : Allocation :=
      { allocId := 10, alignLog2 := 3, mutability := .mut,
        bytes := [
          .init 4 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init 0 none, .init 0 none, .init 0 none, .init 0 none
        ],
        live := true }
    ¬ WellFormedV2 aliasingMutVecProg
        { args := [.ptr ⟨some 10, 0, .isize⟩, .ptr ⟨some 10, 0, .isize⟩],
          callerMem := ⟨[vecSlot]⟩ } :=
  faultProgV2_of_execFault (fuel := 0) (expected := .undefined) (by rfl)

/-- Negative Canary 8: returning `&local_vec[..]` faults `.undefined` via
`refsStayInCallerMem`. -/
def negLeakedVecBorrowProg : Program :=
  let locals : List MirTy := [
    .ref .shared (.slice u8Ty),
    vecU8Ty,
    .ref .mut vecU8Ty,
    .unit,
    .ref .shared vecU8Ty
  ]
  let bbs : List BasicBlock := [
    { statements := []
      terminator := .coreCall (.vecNew u8Ty) [] ⟨1, []⟩ (some 1) .unreachable },
    { statements := [.assign ⟨2, []⟩ (.ref .mut ⟨1, []⟩)]
      terminator := .coreCall .vecPush
        [.copy ⟨2, []⟩, u8Const 5] ⟨3, []⟩ (some 2) .unreachable },
    { statements := [.assign ⟨4, []⟩ (.ref .shared ⟨1, []⟩)]
      terminator := .coreCall .vecDeref [.copy ⟨4, []⟩] ⟨0, []⟩ (some 3)
        .unreachable },
    { statements := []
      terminator := .return_ }
  ]
  { entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 2,
    scope := .unit,
    bodies := [{ argumentCount := 0, isUnsafe := false,
                 locals := locals, basicBlocks := bbs }] }

private noncomputable def n8VecAlloc2 : Allocation :=
  Allocation.mk 2 3 .mut
    [.init 1 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def n8VecAlloc2Push : Allocation :=
  Allocation.mk 2 3 .mut
    [.init 0 (some 3), .init 0 (some 3), .init 0 (some 3),
     .init 0 (some 3), .init 0 (some 3), .init 0 (some 3),
     .init 0 (some 3), .init 0 (some 3), .init 8 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 1 none, .init 0 none, .init 0 none, .init 0 none,
     .init 0 none, .init 0 none, .init 0 none, .init 0 none] true
private noncomputable def n8BufAlloc3 : Allocation :=
  Allocation.mk 3 0 .mut
    [.init 5 none, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
     .uninit] true
private noncomputable def n8_s0 : State :=
  State.mk [FrameState.mk 0 0 0
    [.immediate none, .immediate none, .immediate none,
      .immediate (some .unit), .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 2 [])
private noncomputable def n8_s1 : State :=
  State.mk [FrameState.mk 0 1 0
    [.immediate none, .immediate (some (.vec (danglingAligned 0) 0 0)),
      .immediate none, .immediate (some .unit), .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 2 [])
private noncomputable def n8_s2 : State :=
  State.mk [FrameState.mk 0 1 1
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 3 [n8VecAlloc2])
private noncomputable def n8_s3 : State :=
  State.mk [FrameState.mk 0 2 0
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate none] none none none]
    ⟨[]⟩ (MemoryState.mk 4 [n8VecAlloc2Push, n8BufAlloc3])
private noncomputable def n8_s4 : State :=
  State.mk [FrameState.mk 0 2 1
    [.immediate none, .indirect ⟨2, 0⟩, .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩)), .immediate (some .unit), .immediate (some (.ptr ⟨some 2, 0,
      .isize⟩))] none none none]
    ⟨[]⟩ (MemoryState.mk 4 [n8VecAlloc2Push, n8BufAlloc3])
private noncomputable def n8_s5 : State :=
  State.mk [FrameState.mk 0 3 0
    [.immediate (some (.slicePtr ⟨some 3, 0, .isize⟩ 1)), .indirect ⟨2, 0⟩,
      .immediate (some (.ptr ⟨some 2, 0, .isize⟩)), .immediate (some .unit),
      .immediate (some (.ptr ⟨some 2, 0, .isize⟩))] none none none]
    ⟨[]⟩ (MemoryState.mk 4 [n8VecAlloc2Push, n8BufAlloc3])
private theorem n8_init : initStateV2 negLeakedVecBorrowProg { args :=
  [] } = .ok n8_s0 := by rfl
private theorem n8_step0 :
    evalStepV2 negLeakedVecBorrowProg n8_s0 = .step n8_s1 := by rfl
private theorem n8_step1 :
    evalStepV2 negLeakedVecBorrowProg n8_s1 = .step n8_s2 := by rfl
private theorem n8_step2 :
    evalStepV2 negLeakedVecBorrowProg n8_s2 = .step n8_s3 := by rfl
private theorem n8_step3 :
    evalStepV2 negLeakedVecBorrowProg n8_s3 = .step n8_s4 := by rfl
private theorem n8_step4 :
    evalStepV2 negLeakedVecBorrowProg n8_s4 = .step n8_s5 := by rfl
private theorem n8_step5 :
    evalStepV2 negLeakedVecBorrowProg n8_s5 = .fault .undefined := by rfl


theorem neg_leaked_vec_borrow_faults :
    ¬ WellFormedV2 negLeakedVecBorrowProg { args := [] } :=
  not_wellFormedV2_of_chainStep_fault n8_init
    (ChainStepV2.step n8_step0 (ChainStepV2.step n8_step1
      (ChainStepV2.step n8_step2 (ChainStepV2.step n8_step3
      (ChainStepV2.step n8_step4 (ChainStepV2.base n8_step5))))))

/-! ## Reallocation Canaries -/

/-- Backing buffer of a `Vec<u8>` with `cap = 8` and `len = 2`: allocation `1`
of exactly 8 bytes, whose first two bytes are initialized. -/
noncomputable def staleVecBuf : Allocation :=
  Allocation.mk 1 0 .mut
    [.init 3 none, .init 5 none, .uninit, .uninit, .uninit, .uninit,
     .uninit, .uninit] true

/-- Memory holding only `staleVecBuf`. -/
noncomputable def staleVecMem : MemoryState :=
  MemoryState.mk 2 [staleVecBuf]

/-- Memory after `Box<[u8]>::from` consumes the `Vec` over `staleVecBuf`:
allocation `1` is dead, and the two elements live in a fresh allocation `2`
of exactly 2 bytes. -/
noncomputable def staleBoxMem : MemoryState :=
  MemoryState.mk 3
    [{ staleVecBuf with live := false },
     Allocation.mk 2 0 .mut [.init 3 none, .init 5 none] true]

/-- Negative Canary 9 (stale provenance): `Box<[u8]>::from` on a valid
`Vec<u8>` with `cap = 8` and `len = 2` shrinks the buffer by reallocating it.
The box points into a fresh allocation (`2`) that holds exactly the two
elements, the old allocation (`1`) is dead, and so every access through the
old pointer faults with `.undefined`, including its former excess capacity.
The new allocation has no excess capacity either. -/
theorem box_from_vec_realloc_stale_provenance :
    VecWf staleVecMem true ⟨u8Ty, ⟨some 1, 0, .isize⟩, 8, 2⟩ ∧
    evalBoxFromVec staleVecMem u8Ty ⟨some 1, 0, .isize⟩ 8 2 =
      .ok (.boxPtr ⟨some 2, 0, .isize⟩ (some 2), staleBoxMem) ∧
    (findAllocation 1 staleBoxMem.allocations).map Allocation.live =
      some false ∧
    readBytes staleBoxMem ⟨1, 0⟩ 2 0 = .error .undefined ∧
    readBytes staleBoxMem ⟨1, 2⟩ 1 0 = .error .undefined ∧
    readBytes staleBoxMem ⟨2, 0⟩ 2 0 = .ok [.init 3 none, .init 5 none] ∧
    readBytes staleBoxMem ⟨2, 2⟩ 1 0 = .error .undefined ∧
    BoxWf staleBoxMem true ⟨.slice u8Ty, ⟨some 2, 0, .isize⟩, some 2⟩ ∧
    boxValidInMem staleBoxMem true
        ⟨.slice u8Ty, ⟨some 1, 0, .isize⟩, some 2⟩ = .error .undefined :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Negative Canary 10 (doubling overflow): growing a `Vec<u8>` to hold
`minCap = 2^62 + 2` elements fits `isize::MAX` bytes, and `vecGrowCap` grants
exactly `minCap` when doubling the current capacity `2^61` does not exceed
it. From a current capacity of `2^62 + 1`, the doubled capacity
`2^63 + 2` exceeds `isize::MAX` bytes, so `vecGrowCap` fails rather than
falling back to `minCap` (upstream `finish_grow`'s `layout_array` rejects the
doubled capacity), and the growth faults with `.unsupported`, a
capacity-overflow panic. -/
theorem vec_grow_cap_doubling_overflow_canary :
    Nat.blt ((Nat.pow 2 62 + 2) * 1) isizeMaxBytes = true ∧
    vecGrowCap 1 (Nat.pow 2 61) (Nat.pow 2 62 + 2) =
      some (Nat.pow 2 62 + 2) ∧
    vecGrowCap 1 (Nat.pow 2 62 + 1) (Nat.pow 2 62 + 2) = none ∧
    ensureVecCapacity MemoryState.empty { size := 1, alignLog2 := 0 }
        ⟨u8Ty, ⟨some 1, 0, .isize⟩, UInt64.ofNat (Nat.pow 2 62 + 1),
          UInt64.ofNat (Nat.pow 2 62 + 1)⟩ (Nat.pow 2 62 + 2) =
      .error .unsupported :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `Some(Box::new(..))`: a `Box` handle has the pointer's `Scalar` copy
representation, so building `Option<Box<T>>` from a boxed payload passes the
assignment copy-hazard check, while `Some(vec)` (a three-word
`BackendRepr::Memory` handle) still fails closed. -/
theorem canary_aggregate_option_box_copy_hazard_ok (bl : List MirTy)
    (ls : List LocalSlot) (m : MemoryState) (d : PlaceDestV2) (op : Operand) :
    checkAssignCopyHazardV2 bl ls m d (.option (.box (.int .i8 false)))
        (.aggregateOption 1 (.box (.int .i8 false)) (some op)) = .ok () ∧
      checkAssignCopyHazardV2 bl ls m d (.option (.vec (.int .i8 false)))
        (.aggregateOption 1 (.vec (.int .i8 false)) (some op)) =
          .error .unsupported :=
  ⟨rfl, rfl⟩

end Anneal.Core

end
