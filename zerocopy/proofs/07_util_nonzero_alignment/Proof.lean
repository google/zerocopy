-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Init.Data.Nat.Lemmas
import Spec
import Expected
import Anneal.MirWp
import Anneal.InitLemmas
import Anneal.NatBitwise
import Anneal.BitVec

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Step & Profile v2 Execution Helpers -/

theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem ge_of_blt_false {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  cases Nat.lt_or_ge a b with
  | inl hLt =>
    have hT : Nat.blt a b = true := Nat.ble_eq_true_of_le hLt
    rw [hT] at h
    cases h
  | inr hGe => exact hGe

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro hEq
  subst hEq
  rw [Nat.beq_refl] at h
  cases h

theorem scalarVal_wf_isize {sv : ScalarVal} (hWf : ScalarVal.wf sv = true)
    (hW : sv.width = .isize) :
    truncateBits .isize sv.bits = sv.bits := by
  unfold ScalarVal.wf at hWf
  rw [hW] at hWf
  exact eq_of_beq hWf

theorem truncateBits_isize_toNat_lt {sv : ScalarVal} (hW : sv.width = .isize)
    (hWf : ScalarVal.wf sv = true) :
    sv.bits.toNat < Nat.pow 2 64 := by
  have hEq := scalarVal_wf_isize hWf hW
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

theorem toNat_truncateBits_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    (truncateBits .isize (BitVec.ofNat 128 n)).toNat = n := by
  rw [toNat_truncateBits]
  have h128 : n < Nat.pow 2 128 := Nat.lt_trans h (by decide)
  change (n % Nat.pow 2 128) % intWidthModulus .isize = n
  rw [Nat.mod_eq_of_lt h128]
  exact Nat.mod_eq_of_lt h

private theorem nat_pow_succ_mul (a n : Nat) :
    Nat.pow a (n + 1) = Nat.pow a n * a := rfl

private theorem nat_pow_add (a m n : Nat) :
    Nat.pow a (m + n) = Nat.pow a m * Nat.pow a n :=
  Anneal.InitLemmas.nat_pow_add a m n

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_zero_mod (b : Nat) : Nat.mod 0 b = 0 :=
  Nat.zero_mod b

private theorem nat_mod_self (a : Nat) : Nat.mod a a = 0 :=
  Nat.mod_self a

private theorem nat_mul_mod_right (a b : Nat) : Nat.mod (a * b) a = 0 :=
  Nat.mul_mod_right a b

private theorem nat_mul_add_mod_self_left (a b c : Nat) :
    Nat.mod (a * b + c) a = Nat.mod c a :=
  Nat.mul_add_mod_self_left a b c

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_add_mul_div_right (a b c : Nat) (hc : 0 < c) :
    Nat.div (a + b * c) c = Nat.div a c + b :=
  Nat.add_mul_div_right a b hc

private theorem pow128_eq_mul :
    Nat.pow 2 128 = Nat.pow 2 64 * Nat.pow 2 64 :=
  nat_pow_add 2 64 64

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by
  rw [pow128_eq_mul]
  have hPos : 0 < Nat.pow 2 64 := by decide
  have h2 : 2 ≤ Nat.pow 2 64 := by decide
  have hAdd : Nat.pow 2 64 < Nat.pow 2 64 + Nat.pow 2 64 := Nat.lt_add_of_pos_right hPos
  have hMul2 : Nat.pow 2 64 + Nat.pow 2 64 = Nat.pow 2 64 * 2 := (Nat.mul_two _).symm
  rw [hMul2] at hAdd
  exact Nat.lt_of_lt_of_le hAdd (Nat.mul_le_mul_left (Nat.pow 2 64) h2)

private theorem lt_pow128_of_lt_pow64 {x : Nat} (h : x < Nat.pow 2 64) :
    x < Nat.pow 2 128 :=
  Nat.lt_trans h pow64_lt_pow128

private theorem int_ofNat_pow (b : Nat) :
    ∀ n : Nat, (Int.ofNat b) ^ n = Int.ofNat (Nat.pow b n)
  | 0 => rfl
  | n + 1 => by
    change (Int.ofNat b) ^ n * Int.ofNat b = Int.ofNat (Nat.pow b n * b)
    rw [int_ofNat_pow b n]
    rfl

private theorem int_pow_128_eq :
    ((2 : Int) ^ 128) = Int.ofNat (Nat.pow 2 128) :=
  int_ofNat_pow 2 128

theorem execOutcomeStateV2_step {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execOutcomeStateV2 p onDone onFault fuel s') :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hNext

theorem execOutcomeStateV2_done {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out)
    (hDone : onDone out) :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hDone

private inductive ExecV2 (p : Program) (post : TerminalOut → Prop) :
    Nat → State → Prop where
  | mk {fuel : Nat} {s : State}
      (h : execOutcomeStateV2 p post (fun _ => False) fuel s) :
      ExecV2 p post fuel s

private theorem ExecV2.step {p : Program} {post : TerminalOut → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : ExecV2 p post fuel s') :
    ExecV2 p post (fuel + 1) s :=
  let ⟨hNext⟩ := hNext
  ⟨execOutcomeStateV2_step hStep hNext⟩

private theorem ExecV2.done {p : Program} {post : TerminalOut → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out)
    (hDone : post out) :
    ExecV2 p post (fuel + 1) s :=
  ⟨execOutcomeStateV2_done hStep hDone⟩

private theorem ExecV2.to_execProgV2 {p : Program} {q : Query}
    {fuel : Nat} {s₀ : State} {post : TerminalOut → Prop}
    (hInit : initStateV2 p q = .ok s₀)
    (hExec : ExecV2 p post fuel s₀) :
    execProgV2 p fuel q post := by
  unfold execProgV2
  rw [hInit]
  let ⟨hExec⟩ := hExec
  exact hExec

theorem extractCallerAllocations_suffix (m : MemoryState) :
    ∀ (pref suff : List Allocation),
      m.allocations = pref ++ suff →
      (∀ a, a ∈ suff → findAllocation a.allocId m.allocations = some a) →
      extractCallerAllocations m suff = suff
  | _, [], _, _ => rfl
  | pref, a :: rest, hEq, hFind => by
    have hFoundA : findAllocation a.allocId m.allocations = some a := hFind a (.head _)
    have hTail : extractCallerAllocations m rest = rest :=
      extractCallerAllocations_suffix m (pref ++ [a]) rest
        (by rw [hEq, List.append_assoc]; rfl)
        (fun b hb => hFind b (.tail _ hb))
    change (findAllocation a.allocId m.allocations).getD a ::
      extractCallerAllocations m rest = a :: rest
    rw [hFoundA, hTail]
    rfl

theorem natNotElem_cons_ne {x y : Nat} {ys : List Nat} :
    natNotElem x (y :: ys) = true → x ≠ y ∧ natNotElem x ys = true := by
  intro h
  unfold natNotElem at h
  cases hEq : Nat.beq x y with
  | true => rw [hEq] at h; cases h
  | false =>
    rw [hEq] at h
    exact ⟨(fun hxy => by subst hxy; rw [Nat.beq_refl] at hEq; cases hEq), h⟩

theorem natNotElem_iff_not_mem (x : Nat) :
    ∀ xs : List Nat, natNotElem x xs = true ↔ ∀ y, y ∈ xs → x ≠ y
  | [] => ⟨(fun _ _ hy => by cases hy), (fun _ => rfl)⟩
  | y :: ys =>
    ⟨(fun h z hz => by
      let ⟨hNe, hRest⟩ := natNotElem_cons_ne h
      cases hz with
      | head _ => exact hNe
      | tail _ hIn => exact (natNotElem_iff_not_mem x ys).mp hRest z hIn),
     (fun h => by
      have hNe : x ≠ y := h y (.head _)
      have hRest : natNotElem x ys = true :=
        (natNotElem_iff_not_mem x ys).mpr (fun z hz => h z (.tail _ hz))
      unfold natNotElem
      have hFalse : Nat.beq x y = false := by
        cases hB : Nat.beq x y with
        | false => rfl
        | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB))
      rw [hFalse]
      exact hRest)⟩

theorem natNotElem_of_forall_ne {x : Nat} :
    ∀ {xs : List Nat}, (∀ y, y ∈ xs → x ≠ y) → natNotElem x xs = true :=
  fun h => (natNotElem_iff_not_mem x _).mpr h

theorem mem_map_reverse_append {x : Allocation} {pref : List Allocation} {y : AllocId}
    (h : y ∈ (pref ++ [x]).map Allocation.allocId) :
    y = x.allocId ∨ y ∈ pref.map Allocation.allocId := by
  induction pref with
  | nil =>
    cases h with
    | head _ => exact .inl rfl
    | tail _ hEmpty => cases hEmpty
  | cons p ps ih =>
    cases h with
    | head _ => exact .inr (.head _)
    | tail _ hTail =>
      cases ih hTail with
      | inl hEq => exact .inl hEq
      | inr hIn => exact .inr (.tail _ hIn)

theorem mem_map_self_append (pref : List Allocation) (x : Allocation) :
    x.allocId ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => exact .head _
  | cons _ _ ih => exact .tail _ ih

theorem mem_map_append_left {pref : List Allocation} {x : Allocation} {w : AllocId}
    (h : w ∈ pref.map Allocation.allocId) :
    w ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => cases h
  | cons _ _ ih =>
    cases h with
    | head _ => exact .head _
    | tail _ h' => exact .tail _ (ih h')

theorem findAllocation_append_of_not_in_prefix
    (pref : List Allocation) (a : Allocation) (suff : List Allocation)
    (hDisj : natNotElem a.allocId (pref.map Allocation.allocId) = true) :
    findAllocation a.allocId (pref ++ a :: suff) = some a := by
  induction pref with
  | nil =>
    change (if Nat.beq a.allocId a.allocId then some a
      else findAllocation a.allocId suff) = some a
    rw [Nat.beq_refl]
    rfl
  | cons x xs ih =>
    have hCons : natNotElem a.allocId (x.allocId :: xs.map Allocation.allocId) = true := hDisj
    let ⟨hNe, hRest⟩ := natNotElem_cons_ne hCons
    change (if Nat.beq x.allocId a.allocId then some x
      else findAllocation a.allocId (xs ++ a :: suff)) = some a
    have hFlip : Nat.beq x.allocId a.allocId = false := by
      cases hB : Nat.beq x.allocId a.allocId with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB).symm)
    rw [hFlip]
    exact ih hRest

theorem findAllocation_in_allocIdsValid (pref : List Allocation) :
    ∀ (suff : List Allocation) (seen : List AllocId),
      (∀ z, z ∈ seen → natNotElem z (pref.map Allocation.allocId) = true → False) →
      (∀ z, z ∈ pref.map Allocation.allocId → z ∈ seen) →
      allocIdsValid seen suff = true →
      ∀ a, a ∈ suff → findAllocation a.allocId (pref ++ suff) = some a
  | [], _, _, _, _, _, ha => by cases ha
  | x :: xs, seen, hSeenSub, hPrefSub, hValid, a, ha => by
    unfold allocIdsValid at hValid
    cases hNz : !Nat.beq x.allocId 0 with
    | false => rw [hNz] at hValid; cases hValid
    | true =>
      rw [hNz] at hValid
      cases hNotElem : natNotElem x.allocId seen with
      | false => rw [hNotElem] at hValid; cases hValid
      | true =>
        rw [hNotElem] at hValid
        cases hLen : Nat.blt x.bytes.length isizeMaxBytes with
        | false => rw [hLen] at hValid; cases hValid
        | true =>
          rw [hLen] at hValid
          cases hAl : Nat.ble x.alignLog2 29 with
          | false => rw [hAl] at hValid; cases hValid
          | true =>
            rw [hAl] at hValid
            cases ha with
            | head _ =>
              have hForall := (natNotElem_iff_not_mem x.allocId seen).mp hNotElem
              have hNotPref : natNotElem x.allocId (pref.map Allocation.allocId) = true :=
                natNotElem_of_forall_ne (fun y hy => hForall y (hPrefSub y hy))
              exact findAllocation_append_of_not_in_prefix pref x xs hNotPref
            | tail _ hIn =>
              have hEq : pref ++ x :: xs = (pref ++ [x]) ++ xs := by
                rw [List.append_assoc]; rfl
              rw [hEq]
              exact findAllocation_in_allocIdsValid (pref ++ [x]) xs (x.allocId :: seen)
                (fun z hz hNot => by
                  cases hz with
                  | head _ =>
                    exact (natNotElem_iff_not_mem x.allocId _).mp hNot x.allocId
                      (mem_map_self_append pref x) rfl
                  | tail _ hZ =>
                    exact hSeenSub z hZ (natNotElem_of_forall_ne (fun w hw =>
                      (natNotElem_iff_not_mem z _).mp hNot w (mem_map_append_left hw))))
                (fun z hz => by
                  cases mem_map_reverse_append hz with
                  | inl hEqZ => subst hEqZ; exact .head _
                  | inr hInP => exact .tail _ (hPrefSub z hInP))
                hValid a hIn

theorem extractCallerMemory_entry (cm : CallerMemory)
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryWithCaller cm) = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hEq := extractCallerAllocations_suffix (entryMemoryWithCaller ⟨allocs⟩) [] allocs rfl
      (findAllocation_in_allocIdsValid [] allocs []
        (fun _ hz => by cases hz) (fun _ hz => by cases hz) hValid)
    rw [hEq]

/-! ## Entry Inversion & Place/Step Lemmas for `usize` and `NonZero<usize>` -/

theorem checkValV2_isize_inv {v : Val}
    (h : checkValV2 v (.int .isize false) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨.isize, false, bits⟩ ∧
      ScalarVal.wf ⟨.isize, false, bits⟩ = true := by
  cases v with
  | scalar sv =>
    have hCV : checkVal (.scalar sv) (.int .isize false) = true := h
    let ⟨bits, hEq, hTrunc⟩ := checkVal_int_iff.mp hCV
    have hWf : ScalarVal.wf ⟨.isize, false, bits⟩ = true := by
      unfold ScalarVal.wf
      dsimp only
      rw [hTrunc]
      exact beq_self_eq_true bits
    exact ⟨bits, hEq, hWf⟩
  | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | nonZero _ | bool _ | char _
  | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h

theorem checkValV2_nonZero_isize_inv {v : Val}
    (h : checkValV2 v (.nonZero .isize false) = true) :
    ∃ sv : ScalarVal,
      v = .nonZero sv ∧
      sv.wf = true ∧
      sv.width = .isize ∧
      sv.signed = false ∧
      sv.bits.toNat ≠ 0 := by
  cases v with
  | nonZero sv =>
    unfold checkValV2 at h
    cases hWf : sv.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h
      cases hW : IntWidth.beq sv.width .isize with
      | false => rw [hW] at h; cases h
      | true =>
        rw [hW] at h
        cases hS : (sv.signed == false) with
        | false => rw [hS] at h; cases h
        | true =>
          rw [hS] at h
          cases hNz : Nat.beq sv.bits.toNat 0 with
          | true => rw [hNz] at h; cases h
          | false =>
            exact ⟨sv, rfl, hWf, IntWidth.beq_iff.mp hW, eq_of_beq hS,
              ne_of_beq_false hNz⟩
  | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _ | char _
  | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h

theorem checkArgsMatchV2_usize_nonZero_inv {args : List Val}
    (h : checkArgsMatchV2 args [.int .isize false, .nonZero .isize false] = true) :
    ∃ (lenSv alignSv : ScalarVal),
      args = [.scalar lenSv, .nonZero alignSv] ∧
      lenSv.wf = true ∧ lenSv.width = .isize ∧ lenSv.signed = false ∧
      alignSv.wf = true ∧ alignSv.width = .isize ∧ alignSv.signed = false ∧
      alignSv.bits.toNat ≠ 0 := by
  cases args with
  | nil => cases h
  | cons v0 rest =>
    cases rest with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 (.int .isize false) <;>
        rw [hV0] at h <;> cases h
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 (.int .isize false) <;> rw [hV0] at h
        · cases h
        · cases hV1 : checkValV2 v1 (.nonZero .isize false) <;>
            rw [hV1] at h <;> cases h
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 (.int .isize false) with
        | false => rw [hV0] at h; cases h
        | true =>
          rw [hV0] at h
          cases hV1 : checkValV2 v1 (.nonZero .isize false) with
          | false => rw [hV1] at h; cases h
          | true =>
            let ⟨lBits, hv0, hLWf⟩ := checkValV2_isize_inv hV0
            let ⟨aSv, hv1, hAWf, hAW, hAS, hANz⟩ :=
              checkValV2_nonZero_isize_inv hV1
            subst hv0; subst hv1
            exact ⟨⟨.isize, false, lBits⟩, aSv, rfl, hLWf, rfl, rfl,
              hAWf, hAW, hAS, hANz⟩

theorem checkArgsMatchV2_nonZero_pair_inv {args : List Val}
    (h : checkArgsMatchV2 args
        [.nonZero .isize false, .nonZero .isize false] = true) :
    ∃ (aSv bSv : ScalarVal),
      args = [.nonZero aSv, .nonZero bSv] ∧
      aSv.wf = true ∧ aSv.width = .isize ∧ aSv.signed = false ∧
      aSv.bits.toNat ≠ 0 ∧
      bSv.wf = true ∧ bSv.width = .isize ∧ bSv.signed = false ∧
      bSv.bits.toNat ≠ 0 := by
  cases args with
  | nil => cases h
  | cons v0 rest =>
    cases rest with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 (.nonZero .isize false) <;>
        rw [hV0] at h <;> cases h
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 (.nonZero .isize false) <;> rw [hV0] at h
        · cases h
        · cases hV1 : checkValV2 v1 (.nonZero .isize false) <;>
            rw [hV1] at h <;> cases h
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 (.nonZero .isize false) with
        | false => rw [hV0] at h; cases h
        | true =>
          rw [hV0] at h
          cases hV1 : checkValV2 v1 (.nonZero .isize false) with
          | false => rw [hV1] at h; cases h
          | true =>
            let ⟨aSv, hv0, hAWf, hAW, hAS, hANz⟩ :=
              checkValV2_nonZero_isize_inv hV0
            let ⟨bSv, hv1, hBWf, hBW, hBS, hBNz⟩ :=
              checkValV2_nonZero_isize_inv hV1
            subst hv0; subst hv1
            exact ⟨aSv, bSv, rfl, hAWf, hAW, hAS, hANz, hBWf, hBW, hBS, hBNz⟩

theorem readPlaceV2_copy_local {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true) :
    readPlaceV2 bodyLocals locals mem false ⟨lid, []⟩ =
      .ok (ty, optVal, locals, mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  change (if false = true then Except.error FaultKind.unsupported else _) = _
  rw [ite_bool_false rfl]
  rfl

theorem readPlaceV2_move_local {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState}
    {lid : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) = some locals') :
    readPlaceV2 bodyLocals locals mem true ⟨lid, []⟩ =
      .ok (ty, optVal, locals', mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  change (if false = true then Except.error FaultKind.unsupported else _) = _
  rw [ite_bool_false rfl]
  change (if true = true then match setElem? locals lid (liveUninitSlot ty) with
    | some locals1 => Except.ok (ty, optVal, locals1, mem)
    | none => Except.error FaultKind.unsupported else _) = _
  rw [hSet]
  rfl

theorem evalPrimitiveOperandV2_move_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState}
    {lid : LocalId} {ty : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot :
      Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hRead : isPrimitiveReadableTy ty = true)
    (hSet :
      Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) =
        some locals') :
    evalPrimitiveOperandV2 bodyLocals locals mem (.move ⟨lid, []⟩) =
      .ok (v, locals', mem) := by
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_move_local hTy hSlot hSup hSet]
  dsimp only
  rw [ite_bool_false (b := !isPrimitiveReadableTy ty) (by rw [hRead]; rfl)]

theorem evalPrimitiveOperandV2_const_isize_one_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} :
    evalPrimitiveOperandV2 bodyLocals locals mem
      (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 1)⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩, locals, mem) := by
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2 evalConstLitV2 evalConstLit
  dsimp only
  have hOneTr :
      (truncateBits .isize (BitVec.ofNat 128 1) != BitVec.ofNat 128 1) =
        false := by
    decide
  rw [ite_bool_false hOneTr]
  dsimp only
  have hOneEq :
      truncateBits .isize (BitVec.ofNat 128 1) = BitVec.ofNat 128 1 := by
    decide
  rw [hOneEq]
  rw [ite_bool_false (b := !isPrimitiveReadableTy (.int .isize false))
    (by decide)]

theorem writePlaceV2_immediate_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) = some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val = .ok (locals', mem) := by
  unfold writePlaceV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

theorem evalRvalueV2_use_copy_ok {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {dstTy : MirTy} {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some dstTy)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy dstTy = true)
    (hEq : MirTy.beq dstTy dstTy = true) :
    evalRvalueV2 bodyLocals locals mem dstTy (.use (.copy ⟨lid, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [hEq]
  rfl

theorem evalTerminatorV2_return_scalar_ok {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {retTy : MirTy} {retVal : Val}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalTerminatorV2 body bb frame mem callerMem =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]

theorem initStateV2_ok_of {p : Program} {q : Query} {body : Body}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hCM : validCallerMemory q.callerMem = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValid body = true)
    (hCast : castTypesValid body = true)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0, initLocalsLoop body q.args 0 body.locals⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hLocs]
  rw [hArgs, hRefs, hDisj]
  rfl

theorem execCoreCallOp_nonZeroGet_isize_ok {m : MemoryState} {sv : ScalarVal}
    (hWf : sv.wf = true) (hW : sv.width = .isize) (hS : sv.signed = false)
    (hNz : sv.bits.toNat ≠ 0) :
    execCoreCallOp m .nonZeroGet [(.nonZero .isize false, .nonZero sv)]
      (.int .isize false) = .ok (.scalar sv) := by
  unfold execCoreCallOp
  dsimp only
  have hBad : (!MirTy.beq (.int .isize false) (.int .isize false) || !sv.wf ||
      !IntWidth.beq sv.width .isize || !(sv.signed == false)) = false := by
    rw [hWf, hW, hS]; rfl
  rw [ite_bool_false hBad]
  have hZ : Nat.beq sv.bits.toNat 0 = false := by
    cases hEq : Nat.beq sv.bits.toNat 0 with
    | false => rfl
    | true => exact False.elim (hNz (Nat.eq_of_beq_eq_true hEq))
  rw [ite_bool_false hZ]

theorem execCoreCallOp_usizeWrappingSub_one_ok {m : MemoryState} {sv : ScalarVal}
    (hWf : sv.wf = true) (hW : sv.width = .isize) (_hS : sv.signed = false) :
    let diff :=
      if Nat.ble 1 sv.bits.toNat then sv.bits.toNat - 1 else Nat.pow 2 64 - 1
    execCoreCallOp m .usizeWrappingSub
      [(.int .isize false, .scalar sv),
       (.int .isize false, .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩)]
      (.int .isize false) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 diff⟩) := by
  intro diff
  unfold execCoreCallOp
  dsimp only
  have hOneWf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 1⟩ = true := by decide
  have hBad : (!MirTy.beq (.int .isize false) (.int .isize false) ||
      !sv.wf || !ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 1⟩) = false := by
    rw [hWf, hOneWf]; rfl
  rw [ite_bool_false hBad]
  have hOneToNat : (BitVec.ofNat 128 1).toNat = 1 := by decide
  rw [hOneToNat]
  have hLt64 : sv.bits.toNat < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW hWf
  have hDiffLt64 : diff < Nat.pow 2 64 := by
    dsimp only [diff]
    cases hBle : Nat.ble 1 sv.bits.toNat with
    | true =>
      rw [ite_bool_true rfl]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLt64
    | false =>
      rw [ite_bool_false rfl]
      exact Nat.sub_lt (by decide) (by decide)
  have hExpr :
      (if Nat.ble 1 sv.bits.toNat then sv.bits.toNat - 1
       else Nat.pow 2 64 + sv.bits.toNat - 1) = diff := by
    cases hBle : Nat.ble 1 sv.bits.toNat with
    | true => dsimp only [diff]; rw [ite_bool_true hBle]; rfl
    | false =>
      have hZero : sv.bits.toNat = 0 := by
        cases hN : sv.bits.toNat with
        | zero => rfl
        | succ k =>
          have hT : Nat.ble 1 (k + 1) = true :=
            Nat.ble_eq_true_of_le (Nat.succ_le_succ (Nat.zero_le k))
          rw [hN] at hBle
          rw [hT] at hBle
          cases hBle
      dsimp only [diff]
      rw [ite_bool_false hBle, hZero, Nat.add_zero]
      rfl
  rw [hExpr, truncateBits_of_toNat_lt (by
    change (BitVec.ofNat 128 diff).toNat < intWidthModulus .isize
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt (lt_pow128_of_lt_pow64 hDiffLt64)]
    exact hDiffLt64)]

private theorem evalArithOp_sub_isize_ite (lossy : Bool) (val : ScalarVal) :
    (if (lossy && BinOp.isUnchecked .sub) = true then
      Except.error FaultKind.undefined
    else if BinOp.isOverflowing .sub = true then
      Except.ok (Val.tuple [Val.scalar val, Val.bool lossy])
    else Except.ok (Val.scalar val)) = Except.ok (Val.scalar val) := by
  cases lossy <;> rfl

theorem evalBinOp_isize_sub_one_ok {a : ScalarVal}
    (hWf : a.wf = true) (hW : a.width = .isize) (hS : a.signed = false)
    (hPos : 1 ≤ a.bits.toNat) :
    evalBinOp .sub (.scalar a) (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (a.bits.toNat - 1)⟩) := by
  have hLt64 : a.bits.toNat < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW hWf
  have hSubLt64 : a.bits.toNat - 1 < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLt64
  have hDecA : decodeScalar a = Int.ofNat a.bits.toNat := by
    dsimp only [decodeScalar]
    rw [hW, hS, scalarVal_wf_isize hWf hW]
    rfl
  have hDec1 : decodeScalar ⟨.isize, false, BitVec.ofNat 128 1⟩ = Int.ofNat 1 := by
    dsimp only [decodeScalar]
    change Int.ofNat (truncateBits .isize (BitVec.ofNat 128 1)).toNat = Int.ofNat 1
    rw [toNat_truncateBits_isize_ofNat (by decide)]
  have hSubInt : Int.ofNat a.bits.toNat - Int.ofNat 1 = Int.ofNat (a.bits.toNat - 1) := by
    change Int.subNatNat a.bits.toNat 1 = _
    unfold Int.subNatNat
    cases hZ : 1 - a.bits.toNat with
    | zero => rfl
    | succ k =>
      have hLt1 : a.bits.toNat < 1 := Nat.lt_of_sub_eq_succ hZ
      exact False.elim (Nat.not_lt_of_ge hPos hLt1)
  have hNotHost :
      (decide (Int.ofNat (a.bits.toNat - 1) < 0) ||
       decide (Int.ofNat (a.bits.toNat - 1) ≥ ((2 : Int) ^ 128))) = false := by
    have h1 : ¬ (Int.ofNat (a.bits.toNat - 1) < 0) := fun h => nomatch h
    have h2 : ¬ (Int.ofNat (a.bits.toNat - 1) ≥ ((2 : Int) ^ 128)) := by
      intro hGe
      rw [int_pow_128_eq] at hGe
      have hGeN : Nat.pow 2 128 ≤ a.bits.toNat - 1 := by
        change Int.NonNeg (Int.subNatNat (a.bits.toNat - 1) (Nat.pow 2 128)) at hGe
        unfold Int.subNatNat at hGe
        cases hS2 : Nat.pow 2 128 - (a.bits.toNat - 1) with
        | zero => exact Nat.le_of_sub_eq_zero hS2
        | succ _ => rw [hS2] at hGe; nomatch hGe
      exact Nat.not_lt_of_ge (Nat.le_trans (Nat.le_of_lt pow64_lt_pow128) hGeN) hSubLt64
    rw [decide_eq_false h1, decide_eq_false h2]
    rfl
  have hEval :
      evalBinOp .sub (.scalar a) (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) =
        evalArithOp .sub .isize false (decodeScalar a)
          (decodeScalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := by
    unfold evalBinOp
    dsimp only
    rw [hW, hS]
    rfl
  rw [hEval, hDecA, hDec1]
  unfold evalArithOp
  dsimp only
  rw [ite_bool_false (b := false && (Int.ofNat 1 == 0)) rfl]
  rw [ite_bool_false
    (b := false && false && (Int.ofNat a.bits.toNat == signedMinInt .isize &&
      Int.ofNat 1 == Neg.neg 1)) rfl]
  rw [hSubInt]
  unfold truncateScalar
  rw [ite_bool_false (b := false) rfl]
  dsimp only [bvOfInt, intEmod]
  rw [ite_bool_false (b := false) rfl, hNotHost, Bool.false_or]
  have hMod128 : Nat.mod (a.bits.toNat - 1) (Nat.pow 2 128) = a.bits.toNat - 1 :=
    nat_mod_eq_of_lt (lt_pow128_of_lt_pow64 hSubLt64)
  have hAbs128 : Int.natAbs (Int.ofNat (Nat.pow 2 128)) = Nat.pow 2 128 := rfl
  rw [hAbs128, hMod128]
  dsimp only [Int.toNat]
  rw [evalArithOp_sub_isize_ite]
  rw [truncateBits_of_toNat_lt (by
    rw [Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt (lt_pow128_of_lt_pow64 hSubLt64)]
    exact hSubLt64)]

private theorem truncateScalar_unsigned_ok (w : IntWidth) (i : Int) :
    truncateScalar w false i =
      .ok (⟨w, false, truncateBits w (bvOfInt 128 i)⟩,
        truncateBits w (bvOfInt 128 i) != bvOfInt 128 i) :=
  rfl

private theorem intEmod_negSucc_of_lt {x p : Nat} (hx : x < p) :
    (intEmod (.negSucc x) (Int.ofNat p)).toNat = p - 1 - x := by
  unfold intEmod
  dsimp only
  have hMod : Nat.mod x p = x := nat_mod_eq_of_lt hx
  have hAbs : Int.natAbs (Int.ofNat p) = p := rfl
  rw [hAbs, hMod]
  have hLe : x + 1 ≤ p := hx
  unfold Int.subNatNat
  have hZero : x + 1 - p = 0 := Nat.sub_eq_zero_of_le hLe
  rw [hZero]
  dsimp only [Int.toNat]
  rw [Nat.sub_sub, Nat.add_comm 1 x]

private theorem intEmod_negSucc_pow128 {x : Nat} (hx : x < Nat.pow 2 64) :
    (intEmod (.negSucc x) (Int.ofNat (Nat.pow 2 128))).toNat =
      Nat.pow 2 128 - 1 - x :=
  intEmod_negSucc_of_lt (lt_pow128_of_lt_pow64 hx)

private theorem nat_eq_sub_of_add_eq {a b c : Nat} (h : c + b = a) : c = a - b :=
  (Nat.sub_eq_of_eq_add h.symm).symm

private theorem nat_eq_sub_of_add_eq' {a b c : Nat} (h : b + c = a) : c = a - b :=
  nat_eq_sub_of_add_eq (by rw [Nat.add_comm]; exact h)

private theorem truncateBits_isize_pow128_sub {x : Nat} (hx : x < Nat.pow 2 64) :
    truncateBits .isize (BitVec.ofNat 128 (Nat.pow 2 128 - 1 - x)) =
      BitVec.ofNat 128 (Nat.pow 2 64 - 1 - x) := by
  have hCompLt64 : Nat.pow 2 64 - 1 - x < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.sub_lt (Nat.pow_pos (by decide : 0 < 2)) (by decide : 0 < 1))
  have hMod64 :
      Nat.mod (Nat.pow 2 128 - 1 - x) (Nat.pow 2 64) = Nat.pow 2 64 - 1 - x := by
    have hMul : Nat.pow 2 64 * (Nat.pow 2 64 - 1) = Nat.pow 2 128 - Nat.pow 2 64 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow128_eq_mul]
    have hGe : Nat.pow 2 64 ≤ Nat.pow 2 128 := Nat.le_of_lt pow64_lt_pow128
    have hSub128 : (Nat.pow 2 128 - Nat.pow 2 64) + Nat.pow 2 64 = Nat.pow 2 128 :=
      Nat.sub_add_cancel hGe
    have hAdd :
        ((Nat.pow 2 64 - (x + 1)) + (Nat.pow 2 128 - Nat.pow 2 64)) + (x + 1) =
          Nat.pow 2 128 := by
      rw [Nat.add_comm (Nat.pow 2 64 - (x + 1)) (Nat.pow 2 128 - Nat.pow 2 64),
        Nat.add_assoc, Nat.sub_add_cancel hx, hSub128]
    have hSub1 :
        (Nat.pow 2 64 - 1 - x) + (Nat.pow 2 128 - Nat.pow 2 64) =
          Nat.pow 2 128 - 1 - x := by
      rw [Nat.sub_sub, Nat.add_comm 1 x, Nat.sub_sub, Nat.add_comm 1 x]
      exact nat_eq_sub_of_add_eq hAdd
    have hSplit :
        Nat.pow 2 128 - 1 - x =
          (Nat.pow 2 64 - 1 - x) + Nat.pow 2 64 * (Nat.pow 2 64 - 1) := by
      rw [hMul, hSub1]
    rw [hSplit, Nat.add_comm (Nat.pow 2 64 - 1 - x), nat_mul_add_mod_self_left]
    exact nat_mod_eq_of_lt hCompLt64
  apply bitVec_eq_of_toNat_eq
  have hModulus : intWidthModulus .isize = Nat.pow 2 64 := rfl
  have hLt128 : Nat.pow 2 128 - 1 - x < Nat.pow 2 128 := by
    rw [Nat.sub_sub, Nat.add_comm 1 x]
    exact Nat.sub_lt (Nat.pow_pos (by decide : 0 < 2)) (Nat.zero_lt_succ x)
  have hCompLt128 : Nat.pow 2 64 - 1 - x < Nat.pow 2 128 :=
    lt_pow128_of_lt_pow64 hCompLt64
  have hMod128 : Nat.mod (Nat.pow 2 128 - 1 - x) (Nat.pow 2 128) = Nat.pow 2 128 - 1 - x :=
    nat_mod_eq_of_lt hLt128
  have hModComp : Nat.mod (Nat.pow 2 64 - 1 - x) (Nat.pow 2 128) = Nat.pow 2 64 - 1 - x :=
    nat_mod_eq_of_lt hCompLt128
  rw [toNat_truncateBits, hModulus, Anneal.BitVec.toNat_ofNat,
    Anneal.BitVec.toNat_ofNat, hMod128, hModComp, hMod64]

theorem evalUnOp_not_isize_ok {x : Nat} (hx : x < Nat.pow 2 64) :
    evalUnOp .not (.scalar ⟨.isize, false, BitVec.ofNat 128 x⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (Nat.pow 2 64 - 1 - x)⟩) := by
  have hDec : decodeScalar ⟨.isize, false, BitVec.ofNat 128 x⟩ = Int.ofNat x := by
    unfold decodeScalar
    change Int.ofNat (truncateBits .isize (BitVec.ofNat 128 x)).toNat = Int.ofNat x
    rw [toNat_truncateBits_isize_ofNat hx]
  have hEval :
      evalUnOp .not (.scalar ⟨.isize, false, BitVec.ofNat 128 x⟩) =
        .ok (.scalar ⟨.isize, false,
          truncateBits .isize (bvOfInt 128 (.negSucc x))⟩) := by
    unfold evalUnOp
    dsimp only
    rw [hDec]
    dsimp only [intNot]
    rw [truncateScalar_unsigned_ok]
  rw [hEval]
  dsimp only [bvOfInt]
  rw [intEmod_negSucc_pow128 hx, truncateBits_isize_pow128_sub hx]

theorem evalBinOp_isize_cmp_ok {op : BinOp}
    (hOp : op = .lt ∨ op = .gt)
    {a b : ScalarVal}
    (haWf : a.wf = true) (haW : a.width = .isize) (haS : a.signed = false)
    (hbWf : b.wf = true) (hbW : b.width = .isize) (hbS : b.signed = false) :
    evalBinOp op (.scalar a) (.scalar b) =
      .ok (.bool (match op with
        | .lt => Nat.blt a.bits.toNat b.bits.toNat
        | _ => Nat.blt b.bits.toNat a.bits.toNat)) := by
  have hDecA : decodeScalar a = Int.ofNat a.bits.toNat := by
    dsimp only [decodeScalar]
    rw [haW, haS, scalarVal_wf_isize haWf haW]
    rfl
  have hDecB : decodeScalar b = Int.ofNat b.bits.toNat := by
    dsimp only [decodeScalar]
    rw [hbW, hbS, scalarVal_wf_isize hbWf hbW]
    rfl
  cases hOp with
  | inl hLt =>
    subst hLt
    have hEval :
        evalBinOp .lt (.scalar a) (.scalar b) =
          .ok (.bool (decide (decodeScalar a < decodeScalar b))) := by
      unfold evalBinOp
      dsimp only
      rw [haW, haS, hbW, hbS]
      rfl
    rw [hEval, hDecA, hDecB]
    have hDec : decide (Int.ofNat a.bits.toNat < Int.ofNat b.bits.toNat) =
        Nat.blt a.bits.toNat b.bits.toNat := by
      cases hBlt : Nat.blt a.bits.toNat b.bits.toNat with
      | true =>
        have h : Int.ofNat a.bits.toNat < Int.ofNat b.bits.toNat :=
          Int.ofNat_lt.mpr (lt_of_blt_true hBlt)
        exact decide_eq_true h
      | false =>
        have h : ¬ (Int.ofNat a.bits.toNat < Int.ofNat b.bits.toNat) := by
          intro hI
          have hL : a.bits.toNat < b.bits.toNat := Int.ofNat_lt.mp hI
          exact Nat.not_lt_of_ge (ge_of_blt_false hBlt) hL
        exact decide_eq_false h
    exact congrArg (fun x => Except.ok (Val.bool x)) hDec
  | inr hGt =>
    subst hGt
    have hEval :
        evalBinOp .gt (.scalar a) (.scalar b) =
          .ok (.bool (decide (decodeScalar a > decodeScalar b))) := by
      unfold evalBinOp
      dsimp only
      rw [haW, haS, hbW, hbS]
      rfl
    rw [hEval, hDecA, hDecB]
    have hDec : decide (Int.ofNat a.bits.toNat > Int.ofNat b.bits.toNat) =
        Nat.blt b.bits.toNat a.bits.toNat := by
      cases hBlt : Nat.blt b.bits.toNat a.bits.toNat with
      | true =>
        have h : Int.ofNat b.bits.toNat < Int.ofNat a.bits.toNat :=
          Int.ofNat_lt.mpr (lt_of_blt_true hBlt)
        exact decide_eq_true h
      | false =>
        have h : ¬ (Int.ofNat a.bits.toNat > Int.ofNat b.bits.toNat) := by
          intro hI
          have hL : b.bits.toNat < a.bits.toNat := Int.ofNat_lt.mp hI
          exact Nat.not_lt_of_ge (ge_of_blt_false hBlt) hL
        exact decide_eq_false h
    exact congrArg (fun x => Except.ok (Val.bool x)) hDec

/-! ## Constructive Power-of-Two Bitmask Arithmetic -/

theorem nat_pow_two_lt_inj {i j : Nat} (h : Nat.pow 2 i < Nat.pow 2 j) : i < j := by
  cases Nat.lt_or_ge i j with
  | inl hLt => exact hLt
  | inr hGe =>
    exact False.elim (Nat.not_lt_of_ge (Anneal.BitVec.nat_pow_le_pow_right hGe) h)

private theorem nat_two_mul_add_bit (x : Nat) :
    2 * Nat.div x 2 + Nat.mod x 2 = x :=
  Nat.div_add_mod x 2

private theorem nat_div_two_lt {w x : Nat} (h : x < Nat.pow 2 (w + 1)) :
    Nat.div x 2 < Nat.pow 2 w := by
  have hMul : x < Nat.pow 2 w * 2 := by rw [← nat_pow_succ_mul]; exact h
  rw [Nat.mul_comm] at hMul
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by rw [Nat.mul_comm]; exact hMul)

private theorem nat_mod_two_lt (x : Nat) : Nat.mod x 2 < 2 :=
  Nat.mod_lt x (by decide)

private def bitwiseMeas (x : PSigma (fun _ : Nat => Nat)) : Nat :=
  PSigma.casesOn x (fun n _ => n)

private def bitwiseStep (f : Bool → Bool → Bool) :
    ∀ (x : PSigma (fun _ : Nat => Nat)),
      (∀ (y : PSigma (fun _ : Nat => Nat)),
        InvImage (fun a b => a < b) bitwiseMeas y x → Nat) →
      Nat :=
  fun _x a =>
    PSigma.casesOn
      (motive := fun x =>
        (∀ (y : PSigma (fun _ : Nat => Nat)),
          InvImage (fun a b => a < b) bitwiseMeas y x → Nat) →
        Nat)
      _x
      (fun n m a =>
        if h : n = 0 then
          if f false true = true then m else 0
        else if m = 0 then
          if f true false = true then n else 0
        else
          let r :=
            a ⟨Nat.div n 2, Nat.div m 2⟩
              (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2))
          if f (decide (Nat.mod n 2 = 1)) (decide (Nat.mod m 2 = 1)) = true then
            r + r + 1
          else
            r + r)
      a

private theorem bitwise_eq_fix (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m =
      WellFounded.Nat.fix bitwiseMeas (bitwiseStep f) ⟨n, m⟩ := by
  delta Nat.bitwise Nat.bitwise._unary
  rfl

private theorem fix_go_fuel_indep (f : Bool → Bool → Bool) (fuel1 : Nat) :
    ∀ (fuel2 n m : Nat) (h1 : n < fuel1) (h2 : n < fuel2),
      WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) fuel1 ⟨n, m⟩ h1 =
        WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) fuel2 ⟨n, m⟩ h2 := by
  induction fuel1 with
  | zero =>
    intro fuel2 n m h1 _
    exact False.elim (Nat.not_lt_zero n h1)
  | succ k1 ih =>
    intro fuel2 n m h1 h2
    cases fuel2 with
    | zero => exact False.elim (Nat.not_lt_zero n h2)
    | succ k2 =>
      change
        bitwiseStep f ⟨n, m⟩
            (fun y _ =>
              WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) k1 y _) =
          bitwiseStep f ⟨n, m⟩
            (fun y _ =>
              WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) k2 y _)
      dsimp only [bitwiseStep]
      cases n with
      | zero => rfl
      | succ n' =>
        have hn : Nat.succ n' ≠ 0 := fun h => nomatch h
        rw [dite_eq_right hn, dite_eq_right hn]
        cases m with
        | zero => rfl
        | succ m' =>
          have hm : Nat.succ m' ≠ 0 := fun h => nomatch h
          rw [ite_eq_right hm, ite_eq_right hm]
          have hdiv1 : Nat.div (Nat.succ n') 2 < k1 :=
            Nat.lt_of_lt_of_le
              (Nat.div_lt_self (Nat.succ_pos n') (by decide : 1 < 2))
              (Nat.le_of_lt_succ h1)
          have hdiv2 : Nat.div (Nat.succ n') 2 < k2 :=
            Nat.lt_of_lt_of_le
              (Nat.div_lt_self (Nat.succ_pos n') (by decide : 1 < 2))
              (Nat.le_of_lt_succ h2)
          rw [ih k2 (Nat.div (Nat.succ n') 2) (Nat.div (Nat.succ m') 2)
            hdiv1 hdiv2]

private theorem bitwise_eq_fix_go (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m =
      WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) (n + 1) ⟨n, m⟩
        (Nat.lt_succ_self n) := by
  rw [bitwise_eq_fix]
  change
    WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f)
        (WellFounded.Nat.eager (n + 1)) ⟨n, m⟩ _ =
      WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) (n + 1) ⟨n, m⟩
        (Nat.lt_succ_self n)
  exact
    fix_go_fuel_indep f (WellFounded.Nat.eager (n + 1)) (n + 1) n m _ _

private theorem nat_bitwise_unfold (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m =
      if n = 0 then
        if f false true then m else 0
      else if m = 0 then
        if f true false then n else 0
      else
        let r := Nat.bitwise f (Nat.div n 2) (Nat.div m 2)
        if f (decide (Nat.mod n 2 = 1)) (decide (Nat.mod m 2 = 1)) then
          r + r + 1
        else
          r + r := by
  rw [bitwise_eq_fix_go]
  change
    bitwiseStep f ⟨n, m⟩
        (fun y _ => WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) n y _) =
      _
  dsimp only [bitwiseStep]
  cases n with
  | zero =>
    rw [dite_eq_left (rfl : (0 : Nat) = 0), ite_eq_left (rfl : (0 : Nat) = 0)]
  | succ n' =>
    have hnz : Nat.succ n' ≠ 0 := fun h => nomatch h
    rw [dite_eq_right hnz, ite_eq_right hnz]
    cases m with
    | zero =>
      rw [ite_eq_left (rfl : (0 : Nat) = 0), ite_eq_left (rfl : (0 : Nat) = 0)]
    | succ m' =>
      have hmz : Nat.succ m' ≠ 0 := fun h => nomatch h
      rw [ite_eq_right hmz, ite_eq_right hmz]
      have hdiv : Nat.div (Nat.succ n') 2 < Nat.succ n' :=
        Nat.div_lt_self (Nat.succ_pos n') (by decide : 1 < 2)
      have hrec :
          WellFounded.Nat.fix.go bitwiseMeas (bitwiseStep f) (Nat.succ n')
              ⟨Nat.div (Nat.succ n') 2, Nat.div (Nat.succ m') 2⟩
              (Nat.lt_of_le_of_lt (Nat.le_refl _) hdiv) =
            Nat.bitwise f (Nat.div (Nat.succ n') 2)
              (Nat.div (Nat.succ m') 2) := by
        rw [bitwise_eq_fix_go]
        exact
          fix_go_fuel_indep f (Nat.succ n') (Nat.div (Nat.succ n') 2 + 1)
            _ _ _ _
      rw [hrec]

private theorem nat_land_unfold_succ {x y : Nat} (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.land x y =
      let r := Nat.land (Nat.div x 2) (Nat.div y 2)
      if (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) then
        r + r + 1
      else
        r + r := by
  rw [Anneal.NatBitwise.land_eq_bitwise, nat_bitwise_unfold Bool.and x y]
  cases x with
  | zero => exact absurd rfl hx
  | succ x' =>
    cases y with
    | zero => exact absurd rfl hy
    | succ y' =>
      dsimp only
      rfl

private theorem nat_land_zero_left (y : Nat) : Nat.land 0 y = 0 := by
  rw [Anneal.NatBitwise.land_eq_bitwise, nat_bitwise_unfold Bool.and 0 y]
  rfl

private theorem nat_land_zero_right (x : Nat) : Nat.land x 0 = 0 := by
  rw [Anneal.NatBitwise.land_eq_bitwise, nat_bitwise_unfold Bool.and x 0]
  cases x <;> rfl

private theorem nat_land_lt_two_pow :
    ∀ {w x y : Nat}, x < Nat.pow 2 w → y < Nat.pow 2 w → Nat.land x y < Nat.pow 2 w
  | 0, x, _, hx, _ => by
    have hx0 : x = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hx)
    subst hx0
    rw [nat_land_zero_left]
    decide
  | w + 1, x, y, hx, hy => by
    cases x with
    | zero =>
      rw [nat_land_zero_left]
      exact Anneal.BitVec.nat_two_pow_pos (w + 1)
    | succ x' =>
      cases y with
      | zero =>
        rw [nat_land_zero_right]
        exact Anneal.BitVec.nat_two_pow_pos (w + 1)
      | succ y' =>
        rw [nat_land_unfold_succ (Nat.succ_ne_zero x') (Nat.succ_ne_zero y')]
        have hx2 : Nat.div (Nat.succ x') 2 < Nat.pow 2 w := nat_div_two_lt hx
        have hy2 : Nat.div (Nat.succ y') 2 < Nat.pow 2 w := nat_div_two_lt hy
        have hr := nat_land_lt_two_pow hx2 hy2
        have hPow : Nat.pow 2 (w + 1) = Nat.pow 2 w + Nat.pow 2 w := by
          change Nat.pow 2 w * 2 = Nat.pow 2 w + Nat.pow 2 w
          exact Nat.mul_two (Nat.pow 2 w)
        dsimp only
        cases decide (Nat.mod (Nat.succ x') 2 = 1) &&
            decide (Nat.mod (Nat.succ y') 2 = 1) with
        | false =>
          rw [hPow]
          exact Nat.add_lt_add hr hr
        | true =>
          rw [hPow, Nat.add_assoc]
          exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hr _)
            (Nat.add_lt_add_right hr (Nat.pow 2 w))

theorem evalBinOp_isize_bitAnd_ok {x y : Nat}
    (hx : x < Nat.pow 2 64) (hy : y < Nat.pow 2 64) :
    evalBinOp .bitAnd
      (.scalar ⟨.isize, false, BitVec.ofNat 128 x⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 y⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (Nat.land x y)⟩) := by
  have hEval :
      evalBinOp .bitAnd
        (.scalar ⟨.isize, false, BitVec.ofNat 128 x⟩)
        (.scalar ⟨.isize, false, BitVec.ofNat 128 y⟩) =
        .ok (.scalar ⟨.isize, false,
          truncateBits .isize
            (bvAnd (truncateBits .isize (BitVec.ofNat 128 x))
              (truncateBits .isize (BitVec.ofNat 128 y)))⟩) := rfl
  rw [hEval]
  dsimp only [bvAnd]
  rw [toNat_truncateBits_isize_ofNat hx, toNat_truncateBits_isize_ofNat hy]
  have hLandLt : Nat.land x y < Nat.pow 2 64 := nat_land_lt_two_pow hx hy
  rw [truncateBits_of_toNat_lt (by
    change (BitVec.ofNat 128 (Nat.land x y)).toNat < intWidthModulus .isize
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt (lt_pow128_of_lt_pow64 hLandLt)]
    exact hLandLt)]

private theorem nat_land_pow_two_sub_one :
    ∀ (k x : Nat), Nat.land x (Nat.pow 2 k - 1) = Nat.mod x (Nat.pow 2 k)
  | 0, x => by
    change Nat.land x 0 = Nat.mod x 1
    rw [nat_land_zero_right]
    exact (Nat.mod_one x).symm
  | k + 1, x => by
    cases x with
    | zero =>
      rw [nat_land_zero_left]
      exact (Nat.zero_mod (Nat.pow 2 (k + 1))).symm
    | succ x' =>
      have hPowPos : 0 < Nat.pow 2 k := Anneal.BitVec.nat_two_pow_pos k
      have hPowSucc : Nat.pow 2 (k + 1) = 2 * Nat.pow 2 k := by
        rw [nat_pow_succ_mul, Nat.mul_comm]
      have hMask : Nat.pow 2 (k + 1) - 1 = 2 * (Nat.pow 2 k - 1) + 1 := by
        rw [hPowSucc, Nat.mul_sub_left_distrib, Nat.mul_one]
        have hTwo : 2 ≤ 2 * Nat.pow 2 k := Nat.mul_le_mul_left 2 hPowPos
        rw [← Nat.sub_add_comm hTwo]
        rfl
      have hMaskNe : Nat.pow 2 (k + 1) - 1 ≠ 0 := by
        rw [hMask]
        exact Nat.succ_ne_zero _
      have hMaskDiv : Nat.div (Nat.pow 2 (k + 1) - 1) 2 = Nat.pow 2 k - 1 := by
        rw [hMask, Nat.add_comm]
        change (1 + 2 * (Nat.pow 2 k - 1)) / 2 = Nat.pow 2 k - 1
        rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2),
          Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]
      have hMaskMod : Nat.mod (Nat.pow 2 (k + 1) - 1) 2 = 1 := by
        rw [hMask, Nat.add_comm, Nat.mul_comm 2 (Nat.pow 2 k - 1)]
        change (1 + (Nat.pow 2 k - 1) * 2) % 2 = 1
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by decide : 1 < 2)]
      rw [nat_land_unfold_succ (Nat.succ_ne_zero x') hMaskNe, hMaskDiv, hMaskMod]
      dsimp only
      have hIh := nat_land_pow_two_sub_one k (Nat.div (Nat.succ x') 2)
      rw [hIh]
      have hModDec : decide ((1 : Nat) = 1) = true := rfl
      rw [hModDec, Bool.and_true]
      let r := Nat.mod (Nat.div (Nat.succ x') 2) (Nat.pow 2 k)
      let q := Nat.div (Nat.div (Nat.succ x') 2) (Nat.pow 2 k)
      let b := Nat.mod (Nat.succ x') 2
      have hbLt : b < 2 := nat_mod_two_lt (Nat.succ x')
      have hStepBit :
          (if decide (b = 1) = true then r + r + 1 else r + r) = r + r + b := by
        cases hB : b with
        | zero => rfl
        | succ b' =>
          cases b' with
          | zero => rfl
          | succ b'' =>
            rw [hB] at hbLt
            exact absurd hbLt (Nat.not_lt_of_ge (Nat.le_add_left 2 b''))
      have hDivModK : Nat.pow 2 k * q + r = Nat.div (Nat.succ x') 2 :=
        Nat.div_add_mod _ _
      have hDivMod2 : 2 * Nat.div (Nat.succ x') 2 + b = Nat.succ x' :=
        Nat.div_add_mod (Nat.succ x') 2
      have hDecomp : Nat.succ x' = (r + r + b) + Nat.pow 2 (k + 1) * q := by
        rw [← hDivMod2, ← hDivModK, Nat.mul_add, ← Nat.mul_assoc, ← hPowSucc,
          Nat.two_mul r, Nat.add_assoc, Nat.add_comm (Nat.pow 2 (k + 1) * q)]
      have hRLt : r < Nat.pow 2 k := Nat.mod_lt _ hPowPos
      have hRPlusOneLe : r + 1 ≤ Nat.pow 2 k := hRLt
      have hRemLt : r + r + b < Nat.pow 2 (k + 1) := by
        have hLe : r + r + b ≤ r + (r + 1) := by
          rw [← Nat.add_assoc]
          exact Nat.add_le_add_left (Nat.le_of_lt_succ hbLt) (r + r)
        have hLtSum : r + (r + 1) < Nat.pow 2 k + Nat.pow 2 k :=
          Nat.add_lt_add_of_lt_of_le hRLt hRPlusOneLe
        rw [← Nat.two_mul, ← hPowSucc] at hLtSum
        exact Nat.lt_of_le_of_lt hLe hLtSum
      rw [hStepBit]
      change r + r + b = (Nat.succ x') % Nat.pow 2 (k + 1)
      rw [hDecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hRemLt]

theorem land_two_pow_sub_one {w k x : Nat}
    (_hx : x < Nat.pow 2 w) (_hk : k ≤ w) :
    Nat.land x (Nat.pow 2 k - 1) = Nat.mod x (Nat.pow 2 k) :=
  nat_land_pow_two_sub_one k x

theorem nat_land_add_land_complement :
    ∀ (w x y : Nat),
      x < Nat.pow 2 w → y < Nat.pow 2 w →
      Nat.land x y + Nat.land x (Nat.pow 2 w - 1 - y) = x
  | 0, x, y, hx, hy => by
    have hx0 : x = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hx)
    have hy0 : y = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hy)
    subst hx0; subst hy0; rfl
  | w + 1, x, y, hx, hy => by
    let cy := Nat.pow 2 (w + 1) - 1 - y
    have hPowPos : 0 < Nat.pow 2 w := Anneal.BitVec.nat_two_pow_pos w
    have hPowSucc : Nat.pow 2 (w + 1) = 2 * Nat.pow 2 w := by
      rw [nat_pow_succ_mul, Nat.mul_comm]
    have hSubOne : Nat.pow 2 (w + 1) - 1 = 2 * (Nat.pow 2 w - 1) + 1 := by
      rw [hPowSucc, Nat.mul_sub_left_distrib, Nat.mul_one]
      have hTwo : 2 ≤ 2 * Nat.pow 2 w := Nat.mul_le_mul_left 2 hPowPos
      rw [← Nat.sub_add_comm hTwo]
      rfl
    have hCyAddY : cy + y = Nat.pow 2 (w + 1) - 1 :=
      Nat.sub_add_cancel (Nat.le_pred_of_lt hy)
    have hx2 : Nat.div x 2 < Nat.pow 2 w := nat_div_two_lt hx
    have hy2 : Nat.div y 2 < Nat.pow 2 w := nat_div_two_lt hy
    have hIh := nat_land_add_land_complement w (Nat.div x 2) (Nat.div y 2) hx2 hy2
    have hY0Lt : Nat.mod y 2 < 2 := nat_mod_two_lt y
    have hX0Lt : Nat.mod x 2 < 2 := nat_mod_two_lt x
    have hCyDecomp :
        cy = 2 * (Nat.pow 2 w - 1 - Nat.div y 2) + (1 - Nat.mod y 2) := by
      have hCyLtEq : cy + (2 * Nat.div y 2 + Nat.mod y 2) =
          2 * (Nat.pow 2 w - 1) + 1 := by
        rw [nat_two_mul_add_bit, ← hSubOne]
        exact hCyAddY
      have hRhsSum :
          (2 * (Nat.pow 2 w - 1 - Nat.div y 2) + (1 - Nat.mod y 2)) +
            (2 * Nat.div y 2 + Nat.mod y 2) =
          2 * (Nat.pow 2 w - 1) + 1 := by
        have hYDivLe : Nat.div y 2 ≤ Nat.pow 2 w - 1 := Nat.le_pred_of_lt hy2
        have hYModLe : Nat.mod y 2 ≤ 1 := Nat.le_pred_of_lt hY0Lt
        have hAdd1 : (Nat.pow 2 w - 1 - Nat.div y 2) + Nat.div y 2 = Nat.pow 2 w - 1 :=
          Nat.sub_add_cancel hYDivLe
        have hAdd2 : (1 - Nat.mod y 2) + Nat.mod y 2 = 1 :=
          Nat.sub_add_cancel hYModLe
        rw [Nat.add_assoc, ← Nat.add_assoc (1 - Nat.mod y 2),
          Nat.add_comm (1 - Nat.mod y 2) (2 * Nat.div y 2),
          Nat.add_assoc (2 * Nat.div y 2) (1 - Nat.mod y 2), hAdd2,
          ← Nat.add_assoc, ← Nat.mul_add, hAdd1]
      exact Nat.add_right_cancel (hCyLtEq.trans hRhsSum.symm)
    have hCyDiv : Nat.div cy 2 = Nat.pow 2 w - 1 - Nat.div y 2 := by
      have hRemLt : 1 - Nat.mod y 2 < 2 :=
        Nat.lt_of_le_of_lt (Nat.sub_le 1 (Nat.mod y 2)) (by decide : 1 < 2)
      rw [hCyDecomp, Nat.add_comm, Nat.mul_comm 2 _,
        nat_add_mul_div_right _ _ 2 (by decide : 0 < 2),
        nat_div_eq_of_lt hRemLt, Nat.zero_add]
    have hCyMod : Nat.mod cy 2 = 1 - Nat.mod y 2 := by
      rw [hCyDecomp, nat_mul_add_mod_self_left]
      exact nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide))
    have hLandYBit :
        Nat.land x y =
          2 * Nat.land (Nat.div x 2) (Nat.div y 2) +
            (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) then 1 else 0) := by
      cases hxZ : x with
      | zero =>
        subst hxZ; rw [nat_land_zero_left]
        have hD : Nat.div 0 2 = 0 := rfl
        have hM : Nat.mod 0 2 = 0 := rfl
        rw [hD, hM, nat_land_zero_left]; rfl
      | succ x' =>
        cases hyZ : y with
        | zero =>
          subst hyZ; rw [nat_land_zero_right]
          have hD : Nat.div 0 2 = 0 := rfl
          have hM : Nat.mod 0 2 = 0 := rfl
          rw [hD, hM, nat_land_zero_right]
          cases decide (Nat.mod (x' + 1) 2 = 1) <;> rfl
        | succ y' =>
          rw [← hxZ, ← hyZ, nat_land_unfold_succ (by rw [hxZ]; exact Nat.succ_ne_zero _)
            (by rw [hyZ]; exact Nat.succ_ne_zero _)]
          cases (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) <;>
            simp [Nat.two_mul]
    have hLandCyBit :
        Nat.land x cy =
          2 * Nat.land (Nat.div x 2) (Nat.div cy 2) +
            (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod cy 2 = 1)) then 1 else 0) := by
      cases hxZ : x with
      | zero =>
        subst hxZ; rw [nat_land_zero_left]
        have hD : Nat.div 0 2 = 0 := rfl
        have hM : Nat.mod 0 2 = 0 := rfl
        rw [hD, hM, nat_land_zero_left]; rfl
      | succ x' =>
        cases hcyZ : cy with
        | zero =>
          rw [nat_land_zero_right]
          have hD : Nat.div 0 2 = 0 := rfl
          have hM : Nat.mod 0 2 = 0 := rfl
          rw [hD, hM, nat_land_zero_right]
          cases decide (Nat.mod (x' + 1) 2 = 1) <;> rfl
        | succ cy' =>
          rw [← hxZ, ← hcyZ, nat_land_unfold_succ (by rw [hxZ]; exact Nat.succ_ne_zero _)
            (by rw [hcyZ]; exact Nat.succ_ne_zero _)]
          cases (decide (Nat.mod x 2 = 1) && decide (Nat.mod cy 2 = 1)) <;>
            simp [Nat.two_mul]
    have hBitSum :
        (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) then 1 else 0) +
        (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod cy 2 = 1)) then 1 else 0) =
        Nat.mod x 2 := by
      rw [hCyMod]
      cases hMx : Nat.mod x 2 with
      | zero =>
        cases hMy : Nat.mod y 2 with
        | zero => rfl
        | succ k =>
          cases k with
          | zero => rfl
          | succ k' =>
            rw [hMy] at hY0Lt
            exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k') hY0Lt)
      | succ j =>
        cases j with
        | succ j' =>
          rw [hMx] at hX0Lt
          exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 j') hX0Lt)
        | zero =>
          cases hMy : Nat.mod y 2 with
          | zero => rfl
          | succ k =>
            cases k with
            | zero => rfl
            | succ k' =>
              rw [hMy] at hY0Lt
              exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k') hY0Lt)
    rw [hLandYBit, hLandCyBit, hCyDiv]
    have hRearrange :
        (2 * Nat.land (Nat.div x 2) (Nat.div y 2) +
          (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) then 1 else 0)) +
        (2 * Nat.land (Nat.div x 2) (Nat.pow 2 w - 1 - Nat.div y 2) +
          (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod cy 2 = 1)) then 1 else 0)) =
        2 * (Nat.land (Nat.div x 2) (Nat.div y 2) +
          Nat.land (Nat.div x 2) (Nat.pow 2 w - 1 - Nat.div y 2)) +
        ((if (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) then 1 else 0) +
          (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod cy 2 = 1)) then 1 else 0)) := by
      rw [Nat.mul_add, Nat.add_assoc (2 * Nat.land _ _),
        Nat.add_left_comm (if (decide (Nat.mod x 2 = 1) && decide (Nat.mod y 2 = 1)) then 1 else 0)
          (2 * Nat.land (Nat.div x 2) (Nat.pow 2 w - 1 - Nat.div y 2)),
        ← Nat.add_assoc]
    rw [hRearrange, hIh, hBitSum, nat_two_mul_add_bit]

private theorem scalarVal_isize_wf_of_lt {x : Nat} (hx : x < Nat.pow 2 64) :
    ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 x⟩ = true := by
  unfold ScalarVal.wf; dsimp only
  rw [truncateBits_of_toNat_lt (by
    change (BitVec.ofNat 128 x).toNat < intWidthModulus .isize
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt (lt_pow128_of_lt_pow64 hx)]
    exact hx)]
  exact beq_self_eq_true _

private theorem evalOperandToSlotV2_move_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) = some locals') :
    evalOperandToSlotV2 bodyLocals locals mem (.move ⟨lid, []⟩) =
      .ok (ty, some v, locals', mem) := by
  unfold evalOperandToSlotV2
  exact readPlaceV2_move_local hTy hSlot hSup hSet

private theorem evalOperandToSlotV2_const_isize_one_ok
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState} :
    evalOperandToSlotV2 bodyLocals locals mem
        (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 1)⟩) =
      .ok (.int .isize false,
        some (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩), locals, mem) := by
  unfold evalOperandToSlotV2 evalConstLitV2 evalConstLit
  dsimp only
  have hOneTr :
      (truncateBits .isize (BitVec.ofNat 128 1) != BitVec.ofNat 128 1) = false := by
    decide
  rw [ite_bool_false hOneTr]
  dsimp only
  have hOneEq : truncateBits .isize (BitVec.ofNat 128 1) = BitVec.ofNat 128 1 := by
    decide
  rw [hOneEq]

private theorem evalArgOperandsV2_singleton_ok {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem mem1 : MemoryState}
    {opnd : Operand} {ty : MirTy} {v : Val}
    (hOp : evalOperandToSlotV2 bodyLocals locals mem opnd =
      .ok (ty, some v, locals1, mem1)) :
    evalArgOperandsV2 bodyLocals locals mem [opnd] =
      .ok ([(ty, v)], locals1, mem1) := by
  unfold evalArgOperandsV2
  rw [hOp]; rfl

private theorem evalArgOperandsV2_pair_ok {bodyLocals : List MirTy}
    {locals locals1 locals2 : List LocalSlot} {mem mem1 mem2 : MemoryState}
    {o1 o2 : Operand} {t1 t2 : MirTy} {v1 v2 : Val}
    (h1 : evalOperandToSlotV2 bodyLocals locals mem o1 =
      .ok (t1, some v1, locals1, mem1))
    (h2 : evalOperandToSlotV2 bodyLocals locals1 mem1 o2 =
      .ok (t2, some v2, locals2, mem2)) :
    evalArgOperandsV2 bodyLocals locals mem [o1, o2] =
      .ok ([(t1, v1), (t2, v2)], locals2, mem2) := by
  unfold evalArgOperandsV2
  rw [h1]; dsimp only
  unfold evalArgOperandsV2
  rw [h2]; rfl

private theorem evalRvalueV2_unaryOp_not_ok {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem mem1 : MemoryState}
    {dstTy : MirTy} {opnd : Operand} {v res : Val}
    (hOp : evalPrimitiveOperandV2 bodyLocals locals mem opnd = .ok (v, locals1, mem1))
    (hUn : evalUnOp .not v = .ok res) :
    evalRvalueV2 bodyLocals locals mem dstTy (.unaryOp .not opnd) =
      .ok (res, locals1, mem1) := by
  unfold evalRvalueV2
  dsimp only
  rw [hOp]; dsimp only; rw [hUn]

private theorem evalRvalueV2_binaryOp_sub_ok {bodyLocals : List MirTy}
    {locals locals1 locals2 : List LocalSlot} {mem mem1 mem2 : MemoryState}
    {dstTy : MirTy} {lhs rhs : Operand} {lv rv res : Val}
    (hL : evalPrimitiveOperandV2 bodyLocals locals mem lhs = .ok (lv, locals1, mem1))
    (hR : evalPrimitiveOperandV2 bodyLocals locals1 mem1 rhs = .ok (rv, locals2, mem2))
    (hBin : evalBinOp .sub lv rv = .ok res) :
    evalRvalueV2 bodyLocals locals mem dstTy (.binaryOp .sub lhs rhs) =
      .ok (res, locals2, mem2) := by
  unfold evalRvalueV2
  dsimp only
  rw [hL]; dsimp only; rw [hR]; dsimp only; rw [hBin]

private theorem evalRvalueV2_binaryOp_bitAnd_ok {bodyLocals : List MirTy}
    {locals locals1 locals2 : List LocalSlot} {mem mem1 mem2 : MemoryState}
    {dstTy : MirTy} {lhs rhs : Operand} {lv rv res : Val}
    (hL : evalPrimitiveOperandV2 bodyLocals locals mem lhs = .ok (lv, locals1, mem1))
    (hR : evalPrimitiveOperandV2 bodyLocals locals1 mem1 rhs = .ok (rv, locals2, mem2))
    (hBin : evalBinOp .bitAnd lv rv = .ok res) :
    evalRvalueV2 bodyLocals locals mem dstTy (.binaryOp .bitAnd lhs rhs) =
      .ok (res, locals2, mem2) := by
  unfold evalRvalueV2
  dsimp only
  rw [hL]; dsimp only; rw [hR]; dsimp only; rw [hBin]

private theorem evalRvalueV2_use_const_bool_false_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} :
    evalRvalueV2 bodyLocals locals mem .bool
        (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)) =
      .ok (.bool false, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2 evalConstLitV2 evalConstLit
  rfl

private theorem evalRvalueV2_use_const_unit_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} :
    evalRvalueV2 bodyLocals locals mem .unit
        (.use (.constant ⟨.unit, .zeroSized⟩)) =
      .ok (.unit, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2 evalConstLitV2 evalConstLit
  rfl

private theorem evalStepV2_stmt_storageLive {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals locals1 : List LocalSlot} {callerMem : CallerMemory}
    {mem mem1 : MemoryState} {body : Body} {bb : BasicBlock}
    {lid : Nat} {localTy : MirTy} {old slot : LocalSlot}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = some (.storageLive lid))
    (hTy : Trusted.MirSemantics.getElem? body.locals lid = some localTy)
    (hOld : Trusted.MirSemantics.getElem? locals lid = some old)
    (hSlot : liveUninitSlot localTy = slot)
    (hSet : Trusted.MirSemantics.setElem? locals lid slot = some locals1)
    (hDealloc : deallocateLocal mem old = .ok mem1) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .step ⟨[⟨defId, blockIdx, stmtIdx + 1, locals1⟩], callerMem, mem1⟩ := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  unfold evalStatementV2; dsimp only
  rw [hTy, hOld]; dsimp only
  rw [hSlot, hSet]; dsimp only
  rw [hDealloc]

private theorem evalStepV2_stmt_storageDead {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals locals1 : List LocalSlot} {callerMem : CallerMemory}
    {mem mem1 : MemoryState} {body : Body} {bb : BasicBlock}
    {lid : Nat} {old : LocalSlot}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = some (.storageDead lid))
    (hNe0 : Nat.beq lid 0 = false)
    (hOld : Trusted.MirSemantics.getElem? locals lid = some old)
    (hSet : Trusted.MirSemantics.setElem? locals lid .dead = some locals1)
    (hDealloc : deallocateLocal mem old = .ok mem1) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .step ⟨[⟨defId, blockIdx, stmtIdx + 1, locals1⟩], callerMem, mem1⟩ := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  unfold evalStatementV2; dsimp only
  rw [ite_bool_false hNe0]
  rw [hOld]; dsimp only
  rw [hSet]; dsimp only
  rw [hDealloc]

private theorem evalStepV2_stmt_assign {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals locals1 locals2 : List LocalSlot} {callerMem : CallerMemory}
    {mem mem1 mem2 : MemoryState} {body : Body} {bb : BasicBlock}
    {dst : Place} {rv : Rvalue} {dstTy : MirTy} {v : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = some (.assign dst rv))
    (hDst : placeStaticTyV2 body.locals dst = some dstTy)
    (hRv : evalRvalueV2 body.locals locals mem dstTy rv = .ok (v, locals1, mem1))
    (hWr : writePlaceV2 body.locals locals1 mem1 dst dstTy v = .ok (locals2, mem2)) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .step ⟨[⟨defId, blockIdx, stmtIdx + 1, locals2⟩], callerMem, mem2⟩ := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  unfold evalStatementV2; dsimp only
  rw [hDst]; dsimp only
  rw [hRv]; dsimp only
  rw [hWr]

private theorem evalStepV2_term_coreCall {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals locals1 locals2 : List LocalSlot} {callerMem : CallerMemory}
    {mem mem1 mem2 : MemoryState} {body : Body} {bb : BasicBlock}
    {op : CoreCallOp} {args : List Operand} {dst : Place} {target : Nat}
    {cleanup : UnwindAction} {dstTy : MirTy} {typedArgs : List (MirTy × Val)} {resVal : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = none)
    (hLen : Nat.beq stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .coreCall op args dst (some target) cleanup)
    (hEmpty : dst.projection.isEmpty = true)
    (hDst : Trusted.MirSemantics.getElem? body.locals dst.localId = some dstTy)
    (hArgs : evalArgOperandsV2 body.locals locals mem args = .ok (typedArgs, locals1, mem1))
    (hCall : execCoreCallOp mem1 op typedArgs dstTy = .ok resVal)
    (hWr : writePlaceV2 body.locals locals1 mem1 dst dstTy resVal = .ok (locals2, mem2)) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .step ⟨[⟨defId, target, 0, locals2⟩], callerMem, mem2⟩ := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  rw [ite_bool_true hLen]
  unfold evalTerminatorV2
  rw [hTerm]; dsimp only
  rw [ite_bool_false (by rw [hEmpty]; rfl), hDst]; dsimp only
  rw [hArgs]; dsimp only
  rw [hCall]; dsimp only
  rw [hWr]; dsimp only
  rfl

private theorem evalStepV2_term_switchInt_bool {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals locals1 : List LocalSlot} {callerMem : CallerMemory}
    {mem mem1 : MemoryState} {body : Body} {bb : BasicBlock}
    {discr : Operand} {targets : SwitchTargets} {b : Bool} {target : Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = none)
    (hLen : Nat.beq stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .switchInt discr targets)
    (hDiscr : evalPrimitiveOperandV2 body.locals locals mem discr = .ok (.bool b, locals1, mem1))
    (hBr : evalBoolSwitchBranches b targets.otherwise targets.branches = .ok target) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .step ⟨[⟨defId, target, 0, locals1⟩], callerMem, mem1⟩ := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  rw [ite_bool_true hLen]
  unfold evalTerminatorV2
  rw [hTerm]; dsimp only
  rw [hDiscr]; dsimp only
  rw [hBr]; dsimp only
  rfl

private theorem evalStepV2_term_goto {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals : List LocalSlot} {callerMem : CallerMemory}
    {mem : MemoryState} {body : Body} {bb : BasicBlock} {target : Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = none)
    (hLen : Nat.beq stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .goto target) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .step ⟨[⟨defId, target, 0, locals⟩], callerMem, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  rw [ite_bool_true hLen]
  unfold evalTerminatorV2
  rw [hTerm]; rfl

private theorem evalStepV2_term_return_scalar {p : Program} {defId blockIdx stmtIdx : Nat}
    {locals : List LocalSlot} {callerMem : CallerMemory}
    {mem : MemoryState} {body : Body} {bb : BasicBlock}
    {retTy : MirTy} {retVal : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = none)
    (hLen : Nat.beq stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? locals 0 = some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalStepV2 p ⟨[⟨defId, blockIdx, stmtIdx, locals⟩], callerMem, mem⟩ =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalStepV2; dsimp only
  rw [hBody]; dsimp only
  rw [hBb]; dsimp only
  rw [hStmt]; dsimp only
  rw [ite_bool_true hLen]
  exact evalTerminatorV2_return_scalar_ok hTerm hCleanup hRetTy hRetSlot hStay hValid hDisj

/-! ## Correctness of Each of the 4 Verbatim `zerocopy::util` Functions -/

theorem padding_needed_for_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    match q.args with
    | [.scalar len, .nonZero align] =>
      ∃ res : ScalarVal,
        let out := TerminalOut.returned ⟨.scalar res, q.callerMem⟩
        res.wf ∧
        res.width = .isize ∧
        res.signed = false ∧
        BehaviorV2 (entryProgForBody Captured.program 0) q out ∧
        SatisfiesPostV2 (entryProgForBody Captured.program 0) q (fun o => o = out) ∧
        (Spec.IsPowerOfTwo align.bits.toNat →
          res.bits.toNat < align.bits.toNat ∧
          Nat.mod (len.bits.toNat + res.bits.toNat) align.bits.toNat = 0 ∧
          res.bits.toNat =
            Nat.mod
              (align.bits.toNat - Nat.mod len.bits.toNat align.bits.toNat)
              align.bits.toNat)
    | _ => False := by
  let ⟨hCM, hMatch, _, _⟩ := hValid
  let ⟨lenSv, alignSv, hArgs, hLWf, hLW, hLS, hAWf, hAW, hAS, hANz⟩ :=
    checkArgsMatchV2_usize_nonZero_inv hMatch
  have hQ : q = ⟨[.scalar lenSv, .nonZero alignSv], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hLenLt64 : lenSv.bits.toNat < Nat.pow 2 64 :=
    truncateBits_isize_toNat_lt hLW hLWf
  have hAlignLt64 : alignSv.bits.toNat < Nat.pow 2 64 :=
    truncateBits_isize_toNat_lt hAW hAWf
  have hAlignPos : 1 ≤ alignSv.bits.toNat := Nat.pos_of_ne_zero hANz
  let wsub : Nat :=
    if Nat.ble 1 lenSv.bits.toNat then lenSv.bits.toNat - 1 else Nat.pow 2 64 - 1
  have hWsubLt64 : wsub < Nat.pow 2 64 := by
    dsimp only [wsub]
    cases Nat.ble 1 lenSv.bits.toNat
    · exact Nat.sub_lt (by decide) (by decide)
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLenLt64
  let inv : Nat := Nat.pow 2 64 - 1 - wsub
  have hInvLt64 : inv < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (by decide) (by decide))
  let pad : Nat := Nat.land inv (alignSv.bits.toNat - 1)
  have hPadLt64 : pad < Nat.pow 2 64 :=
    nat_land_lt_two_pow hInvLt64
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hAlignLt64)
  have hS1Wf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 (alignSv.bits.toNat - 1)⟩ = true :=
    scalarVal_isize_wf_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hAlignLt64)
  have hWWf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 wsub⟩ = true :=
    scalarVal_isize_wf_of_lt hWsubLt64
  have hIWf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 inv⟩ = true :=
    scalarVal_isize_wf_of_lt hInvLt64
  let resSv : ScalarVal := ⟨.isize, false, BitVec.ofNat 128 pad⟩
  have hResWf : resSv.wf = true := scalarVal_isize_wf_of_lt hPadLt64
  have hResToNat : resSv.bits.toNat = pad := by
    dsimp only [resSv]
    exact Nat.mod_eq_of_lt (lt_pow128_of_lt_pow64 hPadLt64)
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  have hBody0 :
      Trusted.MirSemantics.getElem? (entryProgForBody Captured.program 0).bodies 0 =
        some Captured.body_0 := rfl
  have hInit :
      initStateV2 (entryProgForBody Captured.program 0)
        ⟨[.scalar lenSv, .nonZero alignSv], q.callerMem⟩ =
      .ok ⟨[⟨0, 0, 0,
        [.immediate none, .immediate (some (.scalar lenSv)),
         .immediate (some (.nonZero alignSv)),
         .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩],
        q.callerMem, m⟩ := by
    have hChk :
        checkArgsMatchV2 [.scalar lenSv, .nonZero alignSv]
          ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount) = true := by
      change checkArgsMatchV2 [.scalar lenSv, .nonZero alignSv]
        [.int .isize false, .nonZero .isize false] = true
      dsimp only [checkArgsMatchV2, checkValV2, checkVal, Val.ty?]
      rw [hLWf, hLW, hLS, hAWf, hAW, hAS]
      cases hNz : Nat.beq alignSv.bits.toNat 0 with
      | true => exact absurd (Nat.eq_of_beq_eq_true hNz) hANz
      | false => rfl
    have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 0)
      (q := ⟨[.scalar lenSv, .nonZero alignSv], q.callerMem⟩)
      (body := Captured.body_0)
      rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hChk rfl rfl
    rw [h0]
    rfl
  let expectedOut : TerminalOut := .returned ⟨.scalar resSv, q.callerMem⟩
  have hExec :
      execProgV2 (entryProgForBody Captured.program 0) 24
        ⟨[.scalar lenSv, .nonZero alignSv], q.callerMem⟩
        (fun o => o = expectedOut) := by
    apply ExecV2.to_execProgV2 hInit
    -- bb0 stmts 0..2: storageLive 3, 4, 5
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    -- bb0 stmt 3: 5 := copy 2
    apply ExecV2.step (evalStepV2_stmt_assign hBody0 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2]; rw [hAWf, hAW, hAS]
            cases hNz : Nat.beq alignSv.bits.toNat 0 with
            | true => exact absurd (Nat.eq_of_beq_eq_true hNz) hANz
            | false => rfl)
        rfl rfl))
    -- bb0 term: coreCall nonZeroGet [move 5] -> 4, bb1
    apply ExecV2.step (evalStepV2_term_coreCall hBody0 rfl rfl rfl rfl rfl rfl
      (evalArgOperandsV2_singleton_ok (evalOperandToSlotV2_move_ok rfl rfl rfl rfl))
      (execCoreCallOp_nonZeroGet_isize_ok hAWf hAW hAS hANz)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hAWf, hAW, hAS]; rfl)
        rfl rfl))
    -- bb1 stmt 0: storageDead 5
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    -- bb1 stmt 1: 3 := sub(move 4, 1)
    apply ExecV2.step (evalStepV2_stmt_assign hBody0 rfl rfl rfl
      (evalRvalueV2_binaryOp_sub_ok
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        evalPrimitiveOperandV2_const_isize_one_ok
        (evalBinOp_isize_sub_one_ok hAWf hAW hAS hAlignPos))
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hS1Wf]; rfl)
        rfl rfl))
    -- bb1 stmts 2..5: storageDead 4; storageLive 6, 7, 8
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    -- bb1 stmt 6: 8 := copy 1
    apply ExecV2.step (evalStepV2_stmt_assign hBody0 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hLWf, hLW, hLS]; rfl)
        rfl rfl))
    -- bb1 term: coreCall usizeWrappingSub [move 8, const 1] -> 7, bb2
    apply ExecV2.step (evalStepV2_term_coreCall hBody0 rfl rfl rfl rfl rfl rfl
      (evalArgOperandsV2_pair_ok
        (evalOperandToSlotV2_move_ok rfl rfl rfl rfl)
        evalOperandToSlotV2_const_isize_one_ok)
      (execCoreCallOp_usizeWrappingSub_one_ok hLWf hLW hLS)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hWWf]; rfl)
        rfl rfl))
    -- bb2 stmt 0: storageDead 8
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    -- bb2 stmt 1: 6 := not(move 7)
    apply ExecV2.step (evalStepV2_stmt_assign hBody0 rfl rfl rfl
      (evalRvalueV2_unaryOp_not_ok
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        (evalUnOp_not_isize_ok hWsubLt64))
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hIWf]; rfl)
        rfl rfl))
    -- bb2 stmts 2..3: storageDead 7; storageLive 9
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody0 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    -- bb2 stmt 4: 9 := copy 3
    apply ExecV2.step (evalStepV2_stmt_assign hBody0 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hS1Wf]; rfl)
        rfl rfl))
    -- bb2 stmt 5: 0 := bitAnd(move 6, move 9)
    apply ExecV2.step (evalStepV2_stmt_assign hBody0 rfl rfl rfl
      (evalRvalueV2_binaryOp_bitAnd_ok
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        (evalBinOp_isize_bitAnd_ok hInvLt64 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hAlignLt64)))
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hResWf]; rfl)
        rfl rfl))
    -- bb2 stmts 6..8: storageDead 9, 6, 3
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody0 rfl rfl rfl rfl rfl rfl)
    -- bb2 term: return_
    refine ExecV2.done (out := .returned ⟨.scalar resSv, extractCallerMemory q.callerMem m⟩) ?_ ?_
    · apply evalStepV2_term_return_scalar hBody0 <;> rfl
    · dsimp only [m, expectedOut]
      rw [hExt]
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  rw [← hQ] at hRes
  rw [hArgs]
  refine ⟨resSv, hResWf, rfl, rfl, hRes.2.1, hRes.2.2.2 _ rfl, ?_⟩
  intro hPow
  let ⟨k, hAlignEq⟩ := hPow
  have hkLt : k < 64 := nat_pow_two_lt_inj (by rw [← hAlignEq]; exact hAlignLt64)
  have hPadMod : pad = Nat.mod inv alignSv.bits.toNat := by
    dsimp only [pad]
    rw [hAlignEq]
    exact land_two_pow_sub_one hInvLt64 (Nat.le_of_lt hkLt)
  rw [hResToNat, hPadMod]
  have hkLe64 : k ≤ 64 := Nat.le_of_lt hkLt
  have hDivisor : Nat.pow 2 64 = alignSv.bits.toNat * Nat.pow 2 (64 - k) := by
    rw [hAlignEq, ← nat_pow_add, Nat.add_sub_cancel' hkLe64]
  have hLenCases :
      pad < alignSv.bits.toNat ∧
      Nat.mod (lenSv.bits.toNat + pad) alignSv.bits.toNat = 0 ∧
      pad = Nat.mod (alignSv.bits.toNat - Nat.mod lenSv.bits.toNat alignSv.bits.toNat)
        alignSv.bits.toNat := by
    cases hLen : lenSv.bits.toNat with
    | zero =>
      have hWsub0 : wsub = Nat.pow 2 64 - 1 := by
        dsimp only [wsub]; rw [hLen]; rfl
      have hInv0 : inv = 0 := by
        dsimp only [inv]; rw [hWsub0, Nat.sub_self]
      have hPad0 : pad = 0 := by rw [hPadMod, hInv0, nat_zero_mod]
      rw [hPad0]
      refine ⟨hAlignPos, by rw [Nat.zero_add, nat_zero_mod], ?_⟩
      rw [nat_zero_mod, Nat.sub_zero, nat_mod_self]
    | succ l' =>
      have hBle1 : Nat.ble 1 (l' + 1) = true :=
        Nat.ble_eq_true_of_le (Nat.succ_le_succ (Nat.zero_le _))
      have hWsubSucc : wsub = l' := by
        dsimp only [wsub]; rw [hLen, hBle1]; rfl
      have hInvSucc : inv = Nat.pow 2 64 - (l' + 1) := by
        dsimp only [inv]
        rw [hWsubSucc, Nat.sub_sub, Nat.add_comm 1 l']
      let d := Nat.div (l' + 1) alignSv.bits.toNat
      let r := Nat.mod (l' + 1) alignSv.bits.toNat
      let q := Nat.pow 2 (64 - k)
      have hDecomp : alignSv.bits.toNat * d + r = l' + 1 :=
        Nat.div_add_mod (l' + 1) alignSv.bits.toNat
      have hRLt : r < alignSv.bits.toNat :=
        Nat.mod_lt (l' + 1) hAlignPos
      have hDLtQ : d < q := by
        have hMulLt : alignSv.bits.toNat * d < alignSv.bits.toNat * q := by
          rw [← hDivisor]
          exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ r) (Nat.le_of_eq hDecomp))
            (by rw [← hLen]; exact hLenLt64)
        cases Nat.lt_or_ge d q with
        | inl h => exact h
        | inr hGe =>
          exact False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_left _ hGe) hMulLt)
      have hQSplit : q = d + 1 + (q - d - 1) := by
        have h1 : d + 1 ≤ q := hDLtQ
        rw [Nat.sub_sub, Nat.add_sub_cancel' h1]
      have hInvDecomp :
          inv = alignSv.bits.toNat * (q - d - 1) + (alignSv.bits.toNat - r) := by
        dsimp only [q] at hQSplit
        rw [hInvSucc, hDivisor, hQSplit, Nat.mul_add, Nat.mul_add, Nat.mul_one, ← hDecomp]
        have hSum :
            (alignSv.bits.toNat * d + alignSv.bits.toNat) +
              alignSv.bits.toNat * (q - d - 1) - (alignSv.bits.toNat * d + r) =
            alignSv.bits.toNat * (q - d - 1) + (alignSv.bits.toNat - r) := by
          have h1 : alignSv.bits.toNat * d + r ≤ alignSv.bits.toNat * d + alignSv.bits.toNat :=
            Nat.add_le_add_left (Nat.le_of_lt hRLt) _
          rw [Nat.add_comm (alignSv.bits.toNat * d + alignSv.bits.toNat),
            Nat.add_sub_assoc h1]
          have hStep :
              (alignSv.bits.toNat * d + alignSv.bits.toNat) -
                (alignSv.bits.toNat * d + r) = alignSv.bits.toNat - r :=
            Nat.add_sub_add_left _ _ _
          exact congrArg (fun z => alignSv.bits.toNat * (q - d - 1) + z) hStep
        exact hSum
      have hPadFormula : pad = Nat.mod (alignSv.bits.toNat - r) alignSv.bits.toNat := by
        rw [hPadMod, hInvDecomp, nat_mul_add_mod_self_left]
      have hPadLt : pad < alignSv.bits.toNat := by
        rw [hPadFormula]
        exact Nat.mod_lt _ hAlignPos
      refine ⟨hPadLt, ?_, hPadFormula⟩
      cases hR0 : r with
      | zero =>
        have hPad0 : pad = 0 := by
          rw [hPadFormula, hR0, Nat.sub_zero, nat_mod_self]
        rw [hPad0, Nat.add_zero]
        exact hR0
      | succ r' =>
        have hSubLt : alignSv.bits.toNat - (r' + 1) < alignSv.bits.toNat :=
          Nat.sub_lt hAlignPos (Nat.zero_lt_succ r')
        have hPadEq : pad = alignSv.bits.toNat - (r' + 1) := by
          rw [hPadFormula, hR0, nat_mod_eq_of_lt hSubLt]
        rw [hPadEq, ← hDecomp, hR0, Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt (hR0 ▸ hRLt))]
        rw [← Nat.mul_succ, nat_mul_mod_right]
  rw [← hPadMod]
  exact hLenCases

theorem round_down_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    match q.args with
    | [.scalar n, .nonZero align] =>
      ∃ res : ScalarVal,
        let out := TerminalOut.returned ⟨.scalar res, q.callerMem⟩
        res.wf ∧
        res.width = .isize ∧
        res.signed = false ∧
        BehaviorV2 (entryProgForBody Captured.program 1) q out ∧
        SatisfiesPostV2 (entryProgForBody Captured.program 1) q (fun o => o = out) ∧
        (Spec.IsPowerOfTwo align.bits.toNat →
          res.bits.toNat ≤ n.bits.toNat ∧
          Nat.mod res.bits.toNat align.bits.toNat = 0 ∧
          n.bits.toNat < res.bits.toNat + align.bits.toNat ∧
          res.bits.toNat =
            n.bits.toNat - Nat.mod n.bits.toNat align.bits.toNat)
    | _ => False := by
  let ⟨hCM, hMatch, _, _⟩ := hValid
  let ⟨nSv, alignSv, hArgs, hNWf, hNW, hNS, hAWf, hAW, hAS, hANz⟩ :=
    checkArgsMatchV2_usize_nonZero_inv hMatch
  have hQ : q = ⟨[.scalar nSv, .nonZero alignSv], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hNLt64 : nSv.bits.toNat < Nat.pow 2 64 :=
    truncateBits_isize_toNat_lt hNW hNWf
  have hAlignLt64 : alignSv.bits.toNat < Nat.pow 2 64 :=
    truncateBits_isize_toNat_lt hAW hAWf
  have hAlignPos : 1 ≤ alignSv.bits.toNat := Nat.pos_of_ne_zero hANz
  let mask : Nat := Nat.pow 2 64 - 1 - (alignSv.bits.toNat - 1)
  have hMaskLt64 : mask < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (by decide) (by decide))
  let res : Nat := Nat.land nSv.bits.toNat mask
  have hResLt64 : res < Nat.pow 2 64 :=
    nat_land_lt_two_pow hNLt64 hMaskLt64
  have hS1Wf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 (alignSv.bits.toNat - 1)⟩ = true :=
    scalarVal_isize_wf_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hAlignLt64)
  have hMWf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 mask⟩ = true :=
    scalarVal_isize_wf_of_lt hMaskLt64
  let resSv : ScalarVal := ⟨.isize, false, BitVec.ofNat 128 res⟩
  have hResWf : resSv.wf = true := scalarVal_isize_wf_of_lt hResLt64
  have hResToNat : resSv.bits.toNat = res := by
    dsimp only [resSv]
    exact Nat.mod_eq_of_lt (lt_pow128_of_lt_pow64 hResLt64)
  have hNValEq : (⟨.isize, false, BitVec.ofNat 128 nSv.bits.toNat⟩ : ScalarVal) = nSv := by
    cases nSv with
    | mk w s b =>
      dsimp only at hNW hNS
      subst hNW; subst hNS
      have hB : BitVec.ofNat 128 b.toNat = b :=
        bitVec_eq_of_toNat_eq (Nat.mod_eq_of_lt b.isLt)
      rw [hB]
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  have hBody1 :
      Trusted.MirSemantics.getElem? (entryProgForBody Captured.program 1).bodies 1 =
        some Captured.body_1 := rfl
  have hInit :
      initStateV2 (entryProgForBody Captured.program 1)
        ⟨[.scalar nSv, .nonZero alignSv], q.callerMem⟩ =
      .ok ⟨[⟨1, 0, 0,
        [.immediate none, .immediate (some (.scalar nSv)),
         .immediate (some (.nonZero alignSv)),
         .dead, .dead, .dead, .dead, .dead, .dead, .dead,
         .dead, .dead, .dead, .dead, .dead, .dead]⟩],
        q.callerMem, m⟩ := by
    have hChk :
        checkArgsMatchV2 [.scalar nSv, .nonZero alignSv]
          ((Captured.body_1.locals.drop 1).take Captured.body_1.argumentCount) = true := by
      change checkArgsMatchV2 [.scalar nSv, .nonZero alignSv]
        [.int .isize false, .nonZero .isize false] = true
      dsimp only [checkArgsMatchV2, checkValV2, checkVal, Val.ty?]
      rw [hNWf, hNW, hNS, hAWf, hAW, hAS]
      cases hNz : Nat.beq alignSv.bits.toNat 0 with
      | true => exact absurd (Nat.eq_of_beq_eq_true hNz) hANz
      | false => rfl
    have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 1)
      (q := ⟨[.scalar nSv, .nonZero alignSv], q.callerMem⟩)
      (body := Captured.body_1)
      rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hChk rfl rfl
    rw [h0]
    rfl
  let expectedOut : TerminalOut := .returned ⟨.scalar resSv, q.callerMem⟩
  have hExec :
      execProgV2 (entryProgForBody Captured.program 1) 36
        ⟨[.scalar nSv, .nonZero alignSv], q.callerMem⟩
        (fun o => o = expectedOut) := by
    apply ExecV2.to_execProgV2 hInit
    -- bb0: storageLive 3, 4; 4 := copy 2; nonZeroGet [move 4] -> 3, bb1
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2]; rw [hAWf, hAW, hAS]
            cases hNz : Nat.beq alignSv.bits.toNat 0 with
            | true => exact absurd (Nat.eq_of_beq_eq_true hNz) hANz
            | false => rfl)
        rfl rfl))
    apply ExecV2.step (evalStepV2_term_coreCall hBody1 rfl rfl rfl rfl rfl rfl
      (evalArgOperandsV2_singleton_ok (evalOperandToSlotV2_move_ok rfl rfl rfl rfl))
      (execCoreCallOp_nonZeroGet_isize_ok hAWf hAW hAS hANz)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hAWf, hAW, hAS]; rfl)
        rfl rfl))
    -- bb1: storageDead 4; storageLive 5, 6; 6 := const false; switchInt -> bb6
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate (some .unit)) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      evalRvalueV2_use_const_bool_false_ok
      (writePlaceV2_immediate_ok rfl rfl rfl))
    apply ExecV2.step (evalStepV2_term_switchInt_bool hBody1 rfl rfl rfl rfl
      (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
      rfl)
    -- bb6: 5 := const (); goto 7
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      evalRvalueV2_use_const_unit_ok
      (writePlaceV2_immediate_ok rfl rfl rfl))
    apply ExecV2.step (evalStepV2_term_goto hBody1 rfl rfl rfl rfl)
    -- bb7 stmts 0..6: storageDead 6,5; storageLive 11,12,13;
    -- 13 := copy 3; 12 := sub(move 13, 1)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hAWf, hAW, hAS]; rfl)
        rfl rfl))
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_binaryOp_sub_ok
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        evalPrimitiveOperandV2_const_isize_one_ok
        (evalBinOp_isize_sub_one_ok hAWf hAW hAS hAlignPos))
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hS1Wf]; rfl)
        rfl rfl))
    -- bb7 stmts 7..13: storageDead 13; 11 := not(move 12); storageDead 12;
    -- storageLive 14; 14 := copy 1; storageLive 15; 15 := copy 11
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_unaryOp_not_ok
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        (evalUnOp_not_isize_ok (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hAlignLt64)))
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hMWf]; rfl)
        rfl rfl))
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hNWf, hNW, hNS]; rfl)
        rfl rfl))
    apply ExecV2.step (evalStepV2_stmt_storageLive hBody1 rfl rfl rfl rfl (rfl : liveUninitSlot _ = .immediate none) rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hMWf]; rfl)
        rfl rfl))
    -- bb7 stmt 14: 0 := bitAnd(move 14, move 15)
    apply ExecV2.step (evalStepV2_stmt_assign hBody1 rfl rfl rfl
      (evalRvalueV2_binaryOp_bitAnd_ok
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        (evalPrimitiveOperandV2_move_ok rfl rfl rfl (by decide) rfl)
        (by rw [← hNValEq]; exact evalBinOp_isize_bitAnd_ok hNLt64 hMaskLt64))
      (writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hResWf]; rfl)
        rfl rfl))
    -- bb7 stmts 15..18: storageDead 15, 14, 11, 3
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    apply ExecV2.step (evalStepV2_stmt_storageDead hBody1 rfl rfl rfl rfl rfl rfl)
    -- bb7 term: return_
    refine ExecV2.done (out := .returned ⟨.scalar resSv, extractCallerMemory q.callerMem m⟩) ?_ ?_
    · apply evalStepV2_term_return_scalar hBody1 <;> rfl
    · dsimp only [m, expectedOut]
      rw [hExt]
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  rw [← hQ] at hRes
  rw [hArgs]
  refine ⟨resSv, hResWf, rfl, rfl, hRes.2.1, hRes.2.2.2 _ rfl, ?_⟩
  intro hPow
  let ⟨k, hAlignEq⟩ := hPow
  have hkLt : k < 64 := nat_pow_two_lt_inj (by rw [← hAlignEq]; exact hAlignLt64)
  have hSplit := nat_land_add_land_complement 64 nSv.bits.toNat (alignSv.bits.toNat - 1)
    hNLt64 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hAlignLt64)
  have hLow : Nat.land nSv.bits.toNat (alignSv.bits.toNat - 1) =
      Nat.mod nSv.bits.toNat alignSv.bits.toNat := by
    rw [hAlignEq]
    exact land_two_pow_sub_one hNLt64 (Nat.le_of_lt hkLt)
  have hResEq : res = nSv.bits.toNat - Nat.mod nSv.bits.toNat alignSv.bits.toNat := by
    dsimp only [res, mask]
    rw [← hLow]
    exact nat_eq_sub_of_add_eq' hSplit
  rw [hResToNat, hResEq]
  refine ⟨Nat.sub_le _ _, ?_, ?_, rfl⟩
  · have hDiv : alignSv.bits.toNat * Nat.div nSv.bits.toNat alignSv.bits.toNat =
        nSv.bits.toNat - Nat.mod nSv.bits.toNat alignSv.bits.toNat :=
      nat_eq_sub_of_add_eq (Nat.div_add_mod nSv.bits.toNat alignSv.bits.toNat)
    rw [← hDiv, nat_mul_mod_right]
  · have hModLt : Nat.mod nSv.bits.toNat alignSv.bits.toNat < alignSv.bits.toNat :=
      Nat.mod_lt _ hAlignPos
    have hModLe : Nat.mod nSv.bits.toNat alignSv.bits.toNat ≤ nSv.bits.toNat :=
      Nat.mod_le _ _
    have hSum :
        (nSv.bits.toNat - Nat.mod nSv.bits.toNat alignSv.bits.toNat) +
          Nat.mod nSv.bits.toNat alignSv.bits.toNat = nSv.bits.toNat :=
      Nat.sub_add_cancel hModLe
    have hLt := Nat.add_lt_add_left hModLt
      (nSv.bits.toNat - Nat.mod nSv.bits.toNat alignSv.bits.toNat)
    rw [hSum] at hLt
    exact hLt

theorem nonZero_bin_correct (defId : DefId) (body : Body)
    (op : Nat → Nat → Nat) (binOp : BinOp)
    (hBody : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hCmp : binOp = .lt ∨ binOp = .gt)
    (hMaxMin :
      (binOp = .lt ∧ op = Nat.max) ∨ (binOp = .gt ∧ op = Nat.min))
    (hLocsEq : body.locals = [
      .nonZero .isize false, .nonZero .isize false, .nonZero .isize false,
      .bool, .int .isize false, .nonZero .isize false,
      .int .isize false, .nonZero .isize false])
    (hArgCnt : body.argumentCount = 2)
    (_hUnsafe : body.isUnsafe = false)
    (hBlocks : body.basicBlocks = [
      { statements := [.storageLive 3, .storageLive 4, .storageLive 5,
          .assign ⟨5, []⟩ (.use (.copy ⟨1, []⟩))],
        terminator := .coreCall .nonZeroGet [.move ⟨5, []⟩] ⟨4, []⟩ (some 1) .continue_,
        cleanup := false },
      { statements := [.storageDead 5, .storageLive 6, .storageLive 7,
          .assign ⟨7, []⟩ (.use (.copy ⟨2, []⟩))],
        terminator := .coreCall .nonZeroGet [.move ⟨7, []⟩] ⟨6, []⟩ (some 2) .continue_,
        cleanup := false },
      { statements := [.storageDead 7,
          .assign ⟨3, []⟩ (.binaryOp binOp (.move ⟨4, []⟩) (.move ⟨6, []⟩))],
        terminator := .switchInt (.move ⟨3, []⟩) ⟨[(BitVec.ofNat 128 0, 4)], 3⟩,
        cleanup := false },
      { statements := [.storageDead 6, .storageDead 4,
          .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))],
        terminator := .goto 5, cleanup := false },
      { statements := [.storageDead 6, .storageDead 4,
          .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))],
        terminator := .goto 5, cleanup := false },
      { statements := [.storageDead 3],
        terminator := .return_, cleanup := false }])
    (hAdm : BodyStaticAdmittedV2 (entryProgForBody Captured.program defId) body = true) :
    ∀ q : Query, ValidEntryArgsV2 body q →
    match q.args with
    | [.nonZero a, .nonZero b] =>
      ∃ res : ScalarVal,
        let out := TerminalOut.returned ⟨.nonZero res, q.callerMem⟩
        res.wf ∧ res.width = .isize ∧ res.signed = false ∧ res.bits.toNat ≠ 0 ∧
        res.bits.toNat = op a.bits.toNat b.bits.toNat ∧
        BehaviorV2 (entryProgForBody Captured.program defId) q out ∧
        SatisfiesPostV2 (entryProgForBody Captured.program defId) q (fun o => o = out)
    | _ => False := by
  intro q hValid
  let ⟨hCM, hMatch, _, _⟩ := hValid
  have hParamTys : (body.locals.drop 1).take body.argumentCount =
      [.nonZero .isize false, .nonZero .isize false] := by
    rw [hLocsEq, hArgCnt]; rfl
  have hMatch' :
      checkArgsMatchV2 q.args [.nonZero .isize false, .nonZero .isize false] = true := by
    rw [← hParamTys]; exact hMatch
  let ⟨aSv, bSv, hArgs, hAWf, hAW, hAS, hANz, hBWf, hBW, hBS, hBNz⟩ :=
    checkArgsMatchV2_nonZero_pair_inv hMatch'
  have hQ : q = ⟨[.nonZero aSv, .nonZero bSv], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  have hCheckA : checkValV2 (.nonZero aSv) (.nonZero .isize false) = true := by
    dsimp only [checkValV2]; rw [hAWf, hAW, hAS]
    cases hZ : Nat.beq aSv.bits.toNat 0 with
    | true => exact absurd (Nat.eq_of_beq_eq_true hZ) hANz
    | false => rfl
  have hCheckB : checkValV2 (.nonZero bSv) (.nonZero .isize false) = true := by
    dsimp only [checkValV2]; rw [hBWf, hBW, hBS]
    cases hZ : Nat.beq bSv.bits.toNat 0 with
    | true => exact absurd (Nat.eq_of_beq_eq_true hZ) hBNz
    | false => rfl
  have hEntryBody :
      Trusted.MirSemantics.getElem? (entryProgForBody Captured.program defId).bodies
        (entryProgForBody Captured.program defId).entryDefId = some body := hBody
  have hBodyInfo :
      body.basicBlocks.isEmpty = false ∧
      Nat.blt body.argumentCount body.locals.length = true ∧
      storageAnnotationsInBounds body = true ∧
      discriminantTypesValid body = true ∧
      castTypesValid body = true ∧
      body.locals.all isSupportedV2LocalTy = true := by
    unfold BodyStaticAdmittedV2 at hAdm
    have h1 := Anneal.InitLemmas.bool_and_left hAdm
    have h2 := Anneal.InitLemmas.bool_and_left h1
    have h3 := Anneal.InitLemmas.bool_and_left h2
    have h4 := Anneal.InitLemmas.bool_and_left h3
    have h5 := Anneal.InitLemmas.bool_and_left h4
    have h6 := Anneal.InitLemmas.bool_and_left h5
    exact ⟨Anneal.InitLemmas.bool_not_true_eq_false (Anneal.InitLemmas.bool_and_right h6),
      Anneal.InitLemmas.bool_and_right h5,
      Anneal.InitLemmas.bool_and_right h4,
      Anneal.InitLemmas.bool_and_right h3,
      Anneal.InitLemmas.bool_and_right h2,
      Anneal.InitLemmas.bool_and_right hAdm⟩
  have hInitLoc :
      initLocalsLoop body [.nonZero aSv, .nonZero bSv] 0 body.locals =
        [.immediate none, .immediate (some (.nonZero aSv)),
         .immediate (some (.nonZero bSv)),
         .dead, .dead, .dead, .dead, .dead] := by
    rw [hLocsEq]
    repeat (unfold initLocalsLoop; rw [hArgCnt, hasStorageAnnotation, hBlocks]; dsimp only)
    rfl
  have hInit :
      initStateV2 (entryProgForBody Captured.program defId)
        ⟨[.nonZero aSv, .nonZero bSv], q.callerMem⟩ =
      .ok ⟨[⟨defId, 0, 0,
        [.immediate none, .immediate (some (.nonZero aSv)),
         .immediate (some (.nonZero bSv)),
         .dead, .dead, .dead, .dead, .dead]⟩],
        q.callerMem, m⟩ := by
    have hChk :
        checkArgsMatchV2 [.nonZero aSv, .nonZero bSv]
          ((body.locals.drop 1).take body.argumentCount) = true := by
      rw [hParamTys]
      dsimp only [checkArgsMatchV2]
      rw [hCheckA, hCheckB]
      rfl
    have hRefs :
        refsValidInMemList m ((body.locals.drop 1).take body.argumentCount)
          [.nonZero aSv, .nonZero bSv] = true := by
      rw [hParamTys]; rfl
    have hDisj :
        spansPairwiseDisjoint
          (refAccessSpansList ((body.locals.drop 1).take body.argumentCount)
            [.nonZero aSv, .nonZero bSv]) = true := by
      rw [hParamTys]; rfl
    have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program defId)
      (q := ⟨[.nonZero aSv, .nonZero bSv], q.callerMem⟩)
      (body := body)
      rfl rfl hCM hEntryBody hBodyInfo.1 hBodyInfo.2.1 hBodyInfo.2.2.1
      hBodyInfo.2.2.2.1 hBodyInfo.2.2.2.2.1 hBodyInfo.2.2.2.2.2
      hChk hRefs hDisj
    rw [h0, hInitLoc]
    rfl
  let cmp : Bool :=
    match binOp with
    | .lt => Nat.blt aSv.bits.toNat bSv.bits.toNat
    | _ => Nat.blt bSv.bits.toNat aSv.bits.toNat
  let resSv : ScalarVal := if cmp then bSv else aSv
  have hResWf : resSv.wf = true := by
    dsimp only [resSv]; cases cmp <;> assumption
  have hResW : resSv.width = .isize := by
    dsimp only [resSv]; cases cmp <;> assumption
  have hResS : resSv.signed = false := by
    dsimp only [resSv]; cases cmp <;> assumption
  have hResNz : resSv.bits.toNat ≠ 0 := by
    dsimp only [resSv]; cases cmp <;> assumption
  have hResCheck : checkValV2 (.nonZero resSv) (.nonZero .isize false) = true := by
    dsimp only [resSv]; cases cmp <;> assumption
  have hResOp : resSv.bits.toNat = op aSv.bits.toNat bSv.bits.toNat := by
    cases hMaxMin with
    | inl hML =>
      let ⟨hBin, hOpEq⟩ := hML
      subst hBin; subst hOpEq
      cases hB : Nat.blt aSv.bits.toNat bSv.bits.toNat with
      | true =>
        dsimp only [resSv, cmp]
        rw [ite_bool_true hB]
        exact (Nat.max_eq_right (Nat.le_of_lt (lt_of_blt_true hB))).symm
      | false =>
        dsimp only [resSv, cmp]
        rw [ite_bool_false hB]
        exact (Nat.max_eq_left (ge_of_blt_false hB)).symm
    | inr hMR =>
      let ⟨hBin, hOpEq⟩ := hMR
      subst hBin; subst hOpEq
      cases hB : Nat.blt bSv.bits.toNat aSv.bits.toNat with
      | true =>
        dsimp only [resSv, cmp]
        rw [ite_bool_true hB]
        exact (Nat.min_eq_right (Nat.le_of_lt (lt_of_blt_true hB))).symm
      | false =>
        dsimp only [resSv, cmp]
        rw [ite_bool_false hB]
        exact (Nat.min_eq_left (ge_of_blt_false hB)).symm
  let expectedOut : TerminalOut := .returned ⟨.nonZero resSv, q.callerMem⟩
  have hStepRest :
      execOutcomeStateV2 (entryProgForBody Captured.program defId)
        (fun o => o = expectedOut) (fun _ => False) 16
        ⟨[⟨defId, 2, 0,
          [.immediate none, .immediate (some (.nonZero aSv)),
           .immediate (some (.nonZero bSv)),
           .immediate none, .immediate (some (.scalar aSv)), .dead,
           .immediate (some (.scalar bSv)), .immediate none]⟩],
          q.callerMem, m⟩ := by
    -- bb2 stmt 0: storageDead 7
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]
      dsimp only
      rw [hBlocks]
      rfl)
    -- bb2 stmt 1: 3 := binaryOp binOp (move 4) (move 6)
    have hStep21 :
        evalStepV2 (entryProgForBody Captured.program defId)
          ⟨[⟨defId, 2, 1,
            [.immediate none, .immediate (some (.nonZero aSv)),
             .immediate (some (.nonZero bSv)),
             .immediate none, .immediate (some (.scalar aSv)), .dead,
             .immediate (some (.scalar bSv)), .dead]⟩],
            q.callerMem, m⟩ =
          .step
            ⟨[⟨defId, 2, 2,
              [.immediate none, .immediate (some (.nonZero aSv)),
               .immediate (some (.nonZero bSv)),
               .immediate (some (.bool cmp)),
               .immediate none, .dead, .immediate none, .dead]⟩],
              q.callerMem, m⟩ := by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]
      cases hCmp with
      | inl hBinEq =>
        subst hBinEq
        dsimp only [placeStaticTyV2, evalRvalueV2, Trusted.MirSemantics.getElem?]
        rw [evalPrimitiveOperandV2_move_ok
          (by rfl) (by rfl) (by rfl) (by decide) (by rfl)]
        dsimp only
        rw [evalPrimitiveOperandV2_move_ok
          (by rfl) (by rfl) (by rfl) (by decide) (by rfl)]
        dsimp only
        rw [evalBinOp_isize_cmp_ok (.inl rfl) hAWf hAW hAS hBWf hBW hBS]
        dsimp only
        rw [writePlaceV2_immediate_ok (by rfl) (by rfl) (by rfl)]
        rfl
      | inr hBinEq =>
        subst hBinEq
        dsimp only [placeStaticTyV2, evalRvalueV2, Trusted.MirSemantics.getElem?]
        rw [evalPrimitiveOperandV2_move_ok
          (by rfl) (by rfl) (by rfl) (by decide) (by rfl)]
        dsimp only
        rw [evalPrimitiveOperandV2_move_ok
          (by rfl) (by rfl) (by rfl) (by decide) (by rfl)]
        dsimp only
        rw [evalBinOp_isize_cmp_ok (.inr rfl) hAWf hAW hAS hBWf hBW hBS]
        dsimp only
        rw [writePlaceV2_immediate_ok (by rfl) (by rfl) (by rfl)]
        rfl
    apply execOutcomeStateV2_step hStep21
    -- bb2 term: switchInt (move 3) [(0, 4)] 3
    cases hCmpVal : cmp with
    | true =>
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]
        dsimp only [Trusted.MirSemantics.getElem?]
        have hLen :
            Nat.beq 2
              [StatementKind.storageDead 7,
               StatementKind.assign ⟨3, []⟩
                 (.binaryOp binOp (.move ⟨4, []⟩) (.move ⟨6, []⟩))].length =
              true := rfl
        rw [ite_bool_true hLen]
        dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
        rw [hLocsEq]
        rw [evalPrimitiveOperandV2_move_ok
          (by rfl) (by rfl) (by rfl) (by decide) (by rfl)]
        dsimp only [evalBoolSwitchBranches, evalConstLit]
        rfl)
      -- bb3 stmts 0,1: storageDead 6, 4; stmt 2: 0 := copy 2; goto 5
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]
        dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
        rw [hLocsEq]
        dsimp only [placeStaticTyV2, Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by decide) (by decide)]
        dsimp only
        rw [writePlaceV2_immediate_ok hCheckB (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      -- bb5: storageDead 3; return_
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      apply execOutcomeStateV2_done
      · dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]
        dsimp only [Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (b := Nat.beq 1 [StatementKind.storageDead 3].length) rfl]
        rw [evalTerminatorV2_return_scalar_ok (by rfl) (by rfl)
          (by rw [hLocsEq]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
      · dsimp only [resSv, expectedOut]
        rw [hCmpVal, ite_bool_true (b := true) rfl]
        dsimp only [m]
        rw [hExt]
    | false =>
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]
        dsimp only [Trusted.MirSemantics.getElem?]
        have hLen :
            Nat.beq 2
              [StatementKind.storageDead 7,
               StatementKind.assign ⟨3, []⟩
                 (.binaryOp binOp (.move ⟨4, []⟩) (.move ⟨6, []⟩))].length =
              true := rfl
        rw [ite_bool_true hLen]
        dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
        rw [hLocsEq]
        rw [evalPrimitiveOperandV2_move_ok
          (by rfl) (by rfl) (by rfl) (by decide) (by rfl)]
        dsimp only [evalBoolSwitchBranches, evalConstLit]
        rfl)
      -- bb4 stmts 0,1: storageDead 6, 4; stmt 2: 0 := copy 1; goto 5
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]
        dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
        rw [hLocsEq]
        dsimp only [placeStaticTyV2, Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by decide) (by decide)]
        dsimp only
        rw [writePlaceV2_immediate_ok hCheckA (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      -- bb5: storageDead 3; return_
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]; rfl)
      apply execOutcomeStateV2_done
      · dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
        rw [hBody]; dsimp only; rw [hBlocks]
        dsimp only [Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (b := Nat.beq 1 [StatementKind.storageDead 3].length) rfl]
        rw [evalTerminatorV2_return_scalar_ok (by rfl) (by rfl)
          (by rw [hLocsEq]; rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
      · dsimp only [resSv, expectedOut]
        rw [hCmpVal, ite_bool_false (b := false) rfl]
        dsimp only [m]
        rw [hExt]
  have hExec :
      execProgV2 (entryProgForBody Captured.program defId) 26
        ⟨[.nonZero aSv, .nonZero bSv], q.callerMem⟩
        (fun o => o = expectedOut) := by
    unfold execProgV2
    rw [hInit]
    -- bb0: storageLive 3, 4, 5; 5 := copy 1; nonZeroGet [move 5] -> 4, bb1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]; rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]; rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]; rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]
      dsimp only [placeStaticTyV2, Trusted.MirSemantics.getElem?]
      rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by decide) (by decide)]
      dsimp only
      rw [writePlaceV2_immediate_ok hCheckA (by rfl) (by rfl)])
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2,
        Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only
      rw [execCoreCallOp_nonZeroGet_isize_ok hAWf hAW hAS hANz]
      dsimp only
      rw [writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hAWf, hAW, hAS]; rfl)
        (by rfl) (by rfl)]
      rfl)
    -- bb1: storageDead 5; storageLive 6, 7; 7 := copy 2;
    -- nonZeroGet [move 7] -> 6, bb2
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]; rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [Trusted.MirSemantics.getElem?, evalStatementV2]
      rw [hLocsEq]; rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [Trusted.MirSemantics.getElem?, evalStatementV2]
      rw [hLocsEq]; rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalStatementV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]
      dsimp only [placeStaticTyV2, Trusted.MirSemantics.getElem?]
      rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by decide) (by decide)]
      dsimp only
      rw [writePlaceV2_immediate_ok hCheckB (by rfl) (by rfl)])
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Trusted.MirSemantics.getElem?]
      rw [hBody]; dsimp only; rw [hBlocks]
      dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
      rw [hLocsEq]
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2,
        Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only
      rw [execCoreCallOp_nonZeroGet_isize_ok hBWf hBW hBS hBNz]
      dsimp only
      rw [writePlaceV2_immediate_ok
        (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hBWf, hBW, hBS]; rfl)
        (by rfl) (by rfl)]
      rfl)
    dsimp only [liveUninitSlot]
    exact hStepRest
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  rw [← hQ] at hRes
  rw [hArgs]
  exact ⟨resSv, hResWf, hResW, hResS, hResNz, hResOp, hRes.2.1, hRes.2.2.2 _ rfl⟩

theorem max_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    match q.args with
    | [.nonZero a, .nonZero b] =>
      ∃ res : ScalarVal,
        let out := TerminalOut.returned ⟨.nonZero res, q.callerMem⟩
        res.wf ∧ res.width = .isize ∧ res.signed = false ∧ res.bits.toNat ≠ 0 ∧
        res.bits.toNat = Nat.max a.bits.toNat b.bits.toNat ∧
        BehaviorV2 (entryProgForBody Captured.program 2) q out ∧
        SatisfiesPostV2 (entryProgForBody Captured.program 2) q (fun o => o = out)
    | _ => False :=
  nonZero_bin_correct 2 Captured.body_2 Nat.max .lt rfl (.inl rfl)
    (.inl ⟨rfl, rfl⟩) rfl rfl rfl rfl (by decide) q hValid

theorem min_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_3 q) :
    match q.args with
    | [.nonZero a, .nonZero b] =>
      ∃ res : ScalarVal,
        let out := TerminalOut.returned ⟨.nonZero res, q.callerMem⟩
        res.wf ∧ res.width = .isize ∧ res.signed = false ∧ res.bits.toNat ≠ 0 ∧
        res.bits.toNat = Nat.min a.bits.toNat b.bits.toNat ∧
        BehaviorV2 (entryProgForBody Captured.program 3) q out ∧
        SatisfiesPostV2 (entryProgForBody Captured.program 3) q (fun o => o = out)
    | _ => False :=
  nonZero_bin_correct 3 Captured.body_3 Nat.min .gt rfl (.inr rfl)
    (.inr ⟨rfl, rfl⟩) rfl rfl rfl rfl (by decide) q hValid

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
      have hCor := padding_needed_for_correct q hValid
      let ⟨_, _, hArgs, _, _, _, _, _, _, _⟩ :=
        checkArgsMatchV2_usize_nonZero_inv hValid.2.1
      rw [hArgs] at hCor
      dsimp only at hCor
      let ⟨_, _, _, _, _, hBeh, _⟩ := hCor
      exact hBeh.1
    | succ d =>
      cases d with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
        have hCor := round_down_correct q hValid
        let ⟨_, _, hArgs, _, _, _, _, _, _, _⟩ :=
          checkArgsMatchV2_usize_nonZero_inv hValid.2.1
        rw [hArgs] at hCor
        dsimp only at hCor
        let ⟨_, _, _, _, _, hBeh, _⟩ := hCor
        exact hBeh.1
      | succ d =>
        cases d with
        | zero =>
          change some Captured.body_2 = some body at hBody
          cases hBody
          refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
          have hCor := max_correct q hValid
          let ⟨_, _, hArgs, _, _, _, _, _, _, _, _⟩ :=
            checkArgsMatchV2_nonZero_pair_inv hValid.2.1
          rw [hArgs] at hCor
          dsimp only at hCor
          let ⟨_, _, _, _, _, _, _, hSat⟩ := hCor
          exact hSat.1
        | succ d =>
          cases d with
          | zero =>
            change some Captured.body_3 = some body at hBody
            cases hBody
            refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
            have hCor := min_correct q hValid
            let ⟨_, _, hArgs, _, _, _, _, _, _, _, _⟩ :=
              checkArgsMatchV2_nonZero_pair_inv hValid.2.1
            rw [hArgs] at hCor
            dsimp only at hCor
            let ⟨_, _, _, _, _, _, _, hSat⟩ := hCor
            exact hSat.1
          | succ _ =>
            change none = some body at hBody
            cases hBody
  · refine ⟨⟨0, Captured.body_0, rfl, by decide, rfl, padding_needed_for_correct⟩,
      ⟨1, Captured.body_1, rfl, by decide, rfl, round_down_correct⟩,
      ⟨2, Captured.body_2, rfl, by decide, rfl, max_correct⟩,
      ⟨3, Captured.body_3, rfl, by decide, rfl, min_correct⟩⟩

end Proof
