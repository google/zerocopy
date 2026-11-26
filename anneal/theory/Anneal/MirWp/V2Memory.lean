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
public import Init.SimpLemmas
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp.Core
public import Anneal.MirWp.Scalars
public import Anneal.MirWp.Reflection

public section

/-!
# Opt-In Profile v2 Memory & `BodyCtx` Helpers (`Anneal.MirWp.V2Memory`)

Opt-in shared lemmas for Profile v2 `CallerMemory`, byte-slice invariants,
`initStateV2`, `BodyCtx`, and statement/terminator execution. Not re-exported
by `Anneal.Wp`, `Anneal.Scalar`, or `Anneal.MirWp` so targets opt in only when
needed.
-/

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Section 1: `Nat`, `UInt64`, `BitVec`, and `ScalarVal` Helpers -/

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem eq_false_of_not_eq_true {b : Bool} (h : (!b) = true) :
    b = false := by
  cases b with
  | false => rfl
  | true => cases h

private theorem ite_err_eq_ok {α : Type} {c : Bool} {k : FaultKind}
    {rest : Except FaultKind α} {v : α}
    (h : (if c = true then Except.error k else rest) = Except.ok v) :
    c = false ∧ rest = Except.ok v := by
  cases c with
  | true => cases h
  | false => exact ⟨rfl, h⟩

/-- Convert `Nat.blt a b = true` into `a < b`. -/
theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

/-- Convert `a < b` into `Nat.blt a b = true`. -/
theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

/-- Round-trip identity `UInt64.ofNat x.toNat = x`. -/
theorem uint64_ofNat_toNat (x : UInt64) : UInt64.ofNat x.toNat = x := by
  cases x with
  | ofBitVec bv =>
    have hNat : (BitVec.ofNat 64 bv.toNat).toNat = bv.toNat :=
      Nat.mod_eq_of_lt bv.isLt
    exact congrArg UInt64.ofBitVec (bitVec_eq_of_toNat_eq hNat)

/-- `.toNat` of `UInt64.ofNat n` when `n < 2^64`. -/
theorem toNat_uint64_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt h

/-- `.toNat` of `BitVec.ofNat 128 n` when `n < 2^128`. -/
theorem toNat_bvOfNat_128 {n : Nat} (h : n < Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n :=
  Nat.mod_eq_of_lt h

/-- Every `IntWidth` modulus fits in `2^128`. -/
theorem intWidthModulus_le_2_128 (w : IntWidth) :
    intWidthModulus w ≤ Nat.pow 2 128 := by
  cases w <;> decide

/-- `truncateBits w` preserves `BitVec.ofNat 128 n` when
`n < intWidthModulus w`. -/
theorem truncateBits_ofNat_of_lt (w : IntWidth) {n : Nat}
    (h : n < intWidthModulus w) :
    truncateBits w (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  apply truncateBits_of_toNat_lt
  rw [toNat_bvOfNat_128 (Nat.lt_of_lt_of_le h (intWidthModulus_le_2_128 w))]
  exact h

/-- `.i32` specialization of `truncateBits_ofNat_of_lt`. -/
theorem truncateBits_i32_of_lt {n : Nat} (h : n < Nat.pow 2 32) :
    truncateBits .i32 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
  truncateBits_ofNat_of_lt .i32 h

/-! ## Section 2: Profile v2 Execution and `BodyCtx` -/

/-- Single-body verification context pairing a captured `program : Program`,
body index `defId`, and the indexed `body : Body`. -/
structure BodyCtx where
  program : Program
  defId : DefId
  body : Body

/-- Entry program specialized to execute `ctx.defId` inside `ctx.program`.
Defined via `{ ... with ... }` record update so it inherits all other `Program`
fields automatically. -/
@[expose] def BodyCtx.entryProg (ctx : BodyCtx) : Program :=
  { ctx.program with entryDefId := ctx.defId }

/-- Proposition that `ctx.program.bodies` maps `ctx.defId` to `ctx.body`. -/
@[expose] def BodyCtx.HasBody (ctx : BodyCtx) : Prop :=
  Trusted.MirSemantics.getElem? ctx.program.bodies ctx.defId = some ctx.body

/-- Advance one Profile v2 `evalStepV2` step in `execOutcomeStateV2`. -/
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

/-- Discharge `execOutcomeStateV2` directly on a terminal `.done` step. -/
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

/-! ## Section 3: `CallerMemory`, `findAllocation`, and Entry Memory -/

/-- Split `natNotElem x (y :: ys) = true` into `x ≠ y` and tail validity. -/
theorem natNotElem_cons_ne {x y : Nat} {ys : List Nat} :
    natNotElem x (y :: ys) = true → x ≠ y ∧ natNotElem x ys = true := by
  intro h
  unfold natNotElem at h
  cases hEq : Nat.beq x y with
  | true => rw [hEq] at h; cases h
  | false =>
    rw [hEq] at h
    exact ⟨(fun hxy => by subst hxy; rw [Nat.beq_refl] at hEq; cases hEq), h⟩

/-- Equivalence between `natNotElem x xs = true` and `∀ y ∈ xs, x ≠ y`. -/
theorem natNotElem_iff_not_mem (x : Nat) :
    ∀ xs : List Nat, natNotElem x xs = true ↔ ∀ y, y ∈ xs → x ≠ y
  | [] =>
    ⟨(fun _ _ h => by cases h), (fun _ => rfl)⟩
  | y :: ys => by
    constructor
    · intro h z hz
      have hC := natNotElem_cons_ne h
      cases hz with
      | head _ => exact hC.1
      | tail _ hMem => exact (natNotElem_iff_not_mem x ys).mp hC.2 z hMem
    · intro h
      have hNe : x ≠ y := h y (.head _)
      have hBeq : Nat.beq x y = false := by
        cases hEq : Nat.beq x y with
        | false => rfl
        | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hEq))
      have hTail :=
        (natNotElem_iff_not_mem x ys).mpr (fun z hz => h z (.tail _ hz))
      unfold natNotElem
      rw [hBeq]
      exact hTail

/-- Construct `natNotElem x xs = true` from pointwise disequality. -/
theorem natNotElem_of_forall_ne {x : Nat} :
    ∀ {xs : List Nat}, (∀ y, y ∈ xs → x ≠ y) → natNotElem x xs = true :=
  fun h => (natNotElem_iff_not_mem x _).mpr h

/-- Membership lift on `List.map Allocation.allocId` along list append. -/
theorem mem_map_append_left {pref : List Allocation} {x : Allocation}
    {w : AllocId}
    (hw : w ∈ pref.map Allocation.allocId) :
    w ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => cases hw
  | cons p ps ih =>
    cases hw with
    | head _ => exact .head _
    | tail _ hp => exact .tail _ (ih hp)

/-- Membership decomposition on `(pref ++ [x]).map Allocation.allocId`. -/
theorem mem_map_reverse_append {x : Allocation} {pref : List Allocation}
    {y : AllocId}
    (h : y ∈ (pref ++ [x]).map Allocation.allocId) :
    y = x.allocId ∨ y ∈ pref.map Allocation.allocId := by
  induction pref with
  | nil =>
    cases h with
    | head _ => exact .inl rfl
    | tail _ ht => cases ht
  | cons p ps ih =>
    cases h with
    | head _ => exact .inr (.head _)
    | tail _ ht =>
      cases ih ht with
      | inl hx => exact .inl hx
      | inr hp => exact .inr (.tail _ hp)

/-- `x.allocId` is always in `(pref ++ [x]).map Allocation.allocId`. -/
theorem mem_map_self_append (pref : List Allocation) (x : Allocation) :
    x.allocId ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => exact .head _
  | cons _ _ ih => exact .tail _ ih

/-- `findAllocation` skips `pref` when `x.allocId` is not in `pref`. -/
theorem findAllocation_append_of_not_in_prefix :
    ∀ (pref : List Allocation) (x : Allocation) (xs : List Allocation),
      natNotElem x.allocId (pref.map Allocation.allocId) = true →
      findAllocation x.allocId (pref ++ x :: xs) = some x
  | [], x, _, _ => by
    unfold findAllocation
    dsimp only [List.nil_append]
    rw [Nat.beq_refl]
    rfl
  | p :: ps, x, xs, hNot => by
    have hC := natNotElem_cons_ne hNot
    have hBeq : Nat.beq p.allocId x.allocId = false := by
      cases hEq : Nat.beq p.allocId x.allocId with
      | false => rfl
      | true => exact False.elim (hC.1 (Nat.eq_of_beq_eq_true hEq).symm)
    unfold findAllocation
    dsimp only [List.cons_append]
    rw [hBeq]
    exact findAllocation_append_of_not_in_prefix ps x xs hC.2

/-- Every allocation in `pref ++ xs` satisfying `allocIdsValid seen xs` is found
by `findAllocation a.allocId`. -/
theorem findAllocation_in_allocIdsValid (pref : List Allocation) :
    ∀ (xs : List Allocation) (seen : List AllocId),
      (∀ z, z ∈ seen →
        natNotElem z (pref.map Allocation.allocId) = true → False) →
      (∀ z, z ∈ pref.map Allocation.allocId → z ∈ seen) →
      allocIdsValid seen xs = true →
      ∀ a, a ∈ xs → findAllocation a.allocId (pref ++ xs) = some a
  | [], _, _, _, _, _, ha => by cases ha
  | x :: xs, seen, hSeenSub, hPrefSub, hValid, a, ha => by
    unfold allocIdsValid at hValid
    -- `&&` is left-associative: `(((!beq && notElem) && blt) && ble) && tail`
    have hHead := bool_and_left hValid
    have hValidTail := bool_and_right hValid
    have hRest2 := bool_and_left hHead
    have hRest1 := bool_and_left hRest2
    have hNotElem : natNotElem x.allocId seen = true := bool_and_right hRest1
    have hForallX := (natNotElem_iff_not_mem x.allocId seen).mp hNotElem
    cases ha with
    | head _ =>
      have hNotPref :
          natNotElem x.allocId (pref.map Allocation.allocId) = true :=
        natNotElem_of_forall_ne (fun y hy => hForallX y (hPrefSub y hy))
      exact findAllocation_append_of_not_in_prefix pref x xs hNotPref
    | tail _ hIn =>
      have hEq : pref ++ x :: xs = (pref ++ [x]) ++ xs := by
        rw [List.append_assoc]; rfl
      rw [hEq]
      exact findAllocation_in_allocIdsValid (pref ++ [x]) xs
        (x.allocId :: seen)
        (fun z hz hNot => by
          cases hz with
          | head _ =>
            exact (natNotElem_iff_not_mem x.allocId _).mp hNot x.allocId
              (mem_map_self_append pref x) rfl
          | tail _ hZ =>
            exact hSeenSub z hZ (natNotElem_of_forall_ne (fun w hw =>
              (natNotElem_iff_not_mem z _).mp hNot w
                (mem_map_append_left hw))))
        (fun z hz => by
          cases mem_map_reverse_append hz with
          | inl hEqZ => subst hEqZ; exact .head _
          | inr hInP => exact .tail _ (hPrefSub z hInP))
        hValidTail a hIn

/-- Suffix preservation for `extractCallerAllocations` when every suffix
allocation resolves to itself in `m.allocations`. -/
theorem extractCallerAllocations_suffix (m : MemoryState) :
    ∀ (pref suff : List Allocation),
      m.allocations = pref ++ suff →
      (∀ a, a ∈ suff → findAllocation a.allocId m.allocations = some a) →
      extractCallerAllocations m suff = suff
  | _, [], _, _ => rfl
  | pref, a :: rest, hEq, hFind => by
    have hFoundA : findAllocation a.allocId m.allocations = some a :=
      hFind a (.head _)
    have hTail : extractCallerAllocations m rest = rest :=
      extractCallerAllocations_suffix m (pref ++ [a]) rest
        (by rw [hEq, List.append_assoc]; rfl)
        (fun b hb => hFind b (.tail _ hb))
    change (findAllocation a.allocId m.allocations).getD a ::
      extractCallerAllocations m rest = a :: rest
    rw [hFoundA, hTail]
    rfl

/-- Any allocation returned by `findAllocation aid allocs` is in `allocs`. -/
theorem findAllocation_mem {aid : AllocId} :
    ∀ {allocs : List Allocation} {a : Allocation},
      findAllocation aid allocs = some a → a ∈ allocs
  | [], _, h => by cases h
  | x :: xs, a, h => by
    unfold findAllocation at h
    cases hEq : Nat.beq x.allocId aid with
    | true =>
      rw [hEq] at h
      cases h
      exact .head _
    | false =>
      rw [hEq] at h
      exact .tail _ (findAllocation_mem h)

/-- `extractCallerMemory cm (entryMemoryWithCaller cm) = cm` for every valid
caller memory. -/
theorem extractCallerMemory_entry (cm : CallerMemory)
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryWithCaller cm) = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hEq := extractCallerAllocations_suffix
      (entryMemoryWithCaller ⟨allocs⟩) [] allocs rfl
      (findAllocation_in_allocIdsValid [] allocs []
        (fun _ hz => by cases hz) (fun _ hz => by cases hz) hValid)
    rw [hEq]

/-- Every allocation in an `allocIdsValid seen allocs` list has
`bytes.length < isizeMaxBytes` (and hence `< 2^64`). -/
theorem allocIdsValid_bytes_lt_isize :
    ∀ (seen : List AllocId) (allocs : List Allocation),
      allocIdsValid seen allocs = true →
      ∀ a, a ∈ allocs → a.bytes.length < isizeMaxBytes
  | _, [], _, _, ha => by cases ha
  | seen, x :: xs, hValid, a, ha => by
    unfold allocIdsValid at hValid
    have hHead := bool_and_left hValid
    have hValidTail := bool_and_right hValid
    have hRest2 := bool_and_left hHead
    have hLen : Nat.blt x.bytes.length isizeMaxBytes = true :=
      bool_and_right hRest2
    cases ha with
    | head _ => exact lt_of_blt_true hLen
    | tail _ hIn => exact allocIdsValid_bytes_lt_isize _ xs hValidTail a hIn

/-- Compatibility corollary bounding allocation byte lengths below `2^64`. -/
theorem allocIdsValid_bytes_lt {seen : List AllocId} {allocs : List Allocation}
    (hValid : allocIdsValid seen allocs = true) {a : Allocation}
    (ha : a ∈ allocs) :
    a.bytes.length < Nat.pow 2 64 :=
  Nat.lt_trans
    (allocIdsValid_bytes_lt_isize seen allocs hValid a ha) (by decide)

/-- Every resolved `entryMemoryWithCaller cm` allocation has
`bytes.length < 2^64`. -/
theorem entryMemoryWithCaller_bytes_lt (cm : CallerMemory)
    (hValid : validCallerMemory cm = true) {aid : AllocId} {a : Allocation}
    (hFind :
      findAllocation aid (entryMemoryWithCaller cm).allocations = some a) :
    a.bytes.length < Nat.pow 2 64 :=
  allocIdsValid_bytes_lt hValid (findAllocation_mem hFind)

/-! ## Section 4: Byte Slices, Subslices, References, and Byte Bounds -/

/-- `isSliceAllInit` is preserved under taking a prefix of any length. -/
theorem isSliceAllInit_take :
    ∀ (n : Nat) (bs : List AllocByte),
      isSliceAllInit bs = true → isSliceAllInit (bs.take n) = true
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => by cases h
  | n + 1, .init _ _ :: rest, h => isSliceAllInit_take n rest h

/-- `isSliceAllInit` is preserved under dropping any prefix. -/
theorem isSliceAllInit_drop :
    ∀ (off : Nat) (bs : List AllocByte),
      isSliceAllInit bs = true → isSliceAllInit (bs.drop off) = true
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => by cases h
  | off + 1, .init _ _ :: rest, h => isSliceAllInit_drop off rest h

private theorem list_drop_nil {α : Type} :
    ∀ (n : Nat), ([].drop n : List α) = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem list_take_nil {α : Type} :
    ∀ (n : Nat), ([].take n : List α) = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem list_take_take_le {α : Type} :
    ∀ (a b : Nat) (xs : List α), a ≤ b → (xs.take b).take a = xs.take a
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ + 1, _ + 1, [], _ => rfl
  | a + 1, b + 1, x :: xs, h => by
    dsimp only [List.take]
    exact congrArg (x :: ·)
      (list_take_take_le a b xs (Nat.le_of_succ_le_succ h))

private theorem list_take_drop {α : Type} :
    ∀ (o l : Nat) (xs : List α), (xs.take l).drop o = (xs.drop o).take (l - o)
  | 0, _, xs => by dsimp only [List.drop]; rw [Nat.sub_zero]
  | _ + 1, 0, xs => by
    rw [Nat.zero_sub]
    change ([].drop _ : List α) = [].take 0
    exact list_drop_nil _
  | _ + 1, _ + 1, [] => by
    change ([].drop _ : List α) = [].take _
    rw [list_drop_nil, list_take_nil]
  | o + 1, l + 1, _ :: xs => by
    dsimp only [List.take, List.drop]
    have hSub : l + 1 - (o + 1) = l - o := by rw [Nat.succ_sub_succ_eq_sub]
    rw [hSub]
    exact list_take_drop o l xs

private theorem list_drop_drop {α : Type} :
    ∀ (a b : Nat) (xs : List α), (xs.drop a).drop b = xs.drop (a + b)
  | 0, b, xs => by dsimp only [List.drop]; rw [Nat.zero_add]
  | a + 1, b, [] => by rw [list_drop_nil, list_drop_nil, list_drop_nil]
  | a + 1, b, _ :: xs => by
    dsimp only [List.drop]
    rw [Nat.succ_add]
    exact list_drop_drop a b xs

/-- Drop-take subslice initialization from initialization of a larger slice. -/
theorem isSliceAllInit_drop_take (base len off subLen : Nat)
    (bs : List AllocByte)
    (hSub : off + subLen ≤ len)
    (hInit : isSliceAllInit ((bs.drop base).take len) = true) :
    isSliceAllInit ((bs.drop (base + off)).take subLen) = true := by
  have hSubLe : subLen ≤ len - off :=
    Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hSub)
  have hTake :
      (((bs.drop base).take len).drop off).take subLen =
        (bs.drop (base + off)).take subLen := by
    rw [list_take_drop, list_drop_drop, list_take_take_le _ _ _ hSubLe]
  rw [← hTake]
  exact isSliceAllInit_take subLen (((bs.drop base).take len).drop off)
    (isSliceAllInit_drop off ((bs.drop base).take len) hInit)

/-- Length of `(bs.drop off).take n` when `off + n ≤ bs.length`. -/
theorem list_drop_take_len {α : Type} :
    ∀ (off n : Nat) (bs : List α),
      off + n ≤ bs.length → ((bs.drop off).take n).length = n := by
  intro off n bs hLe
  induction off generalizing bs with
  | zero =>
    dsimp only [List.drop]
    induction n generalizing bs with
    | zero => rfl
    | succ k ih =>
      cases bs with
      | nil => cases hLe
      | cons _ rest =>
        dsimp only [List.take, List.length]
        exact congrArg Nat.succ (ih rest (Nat.le_of_succ_le_succ hLe))
  | succ k ih =>
    cases bs with
    | nil =>
      rw [Nat.succ_add] at hLe
      exact False.elim (Nat.not_succ_le_zero _ hLe)
    | cons _ rest =>
      dsimp only [List.drop, List.length] at hLe
      dsimp only [List.drop, List.length]
      apply ih rest
      rw [Nat.succ_add] at hLe
      exact Nat.le_of_succ_le_succ hLe

/-- Four-byte specialization of `list_drop_take_len`. -/
theorem list_drop_take_four_len (off : Nat) (bs : List AllocByte)
    (hLe : off + 4 ≤ bs.length) :
    ((bs.drop off).take 4).length = 4 :=
  list_drop_take_len off 4 bs hLe

/-- Destructure a 4-byte all-initialized `List AllocByte`. -/
theorem isSliceAllInit_take_four (bs : List AllocByte)
    (hLen : bs.length = 4) (hInit : isSliceAllInit bs = true) :
    ∃ b0 b1 b2 b3 p0 p1 p2 p3,
      bs = [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] := by
  cases bs with
  | nil => cases hLen
  | cons x0 r0 =>
    cases x0 with
    | uninit => exact Bool.noConfusion hInit
    | init b0 p0 =>
      cases r0 with
      | nil => cases hLen
      | cons x1 r1 =>
        cases x1 with
        | uninit => exact Bool.noConfusion hInit
        | init b1 p1 =>
          cases r1 with
          | nil => cases hLen
          | cons x2 r2 =>
            cases x2 with
            | uninit => exact Bool.noConfusion hInit
            | init b2 p2 =>
              cases r2 with
              | nil => cases hLen
              | cons x3 r3 =>
                cases x3 with
                | uninit => exact Bool.noConfusion hInit
                | init b3 p3 =>
                  cases r3 with
                  | nil => exact ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl⟩
                  | cons _ _ => cases hLen

/-- Strict upper bound `natOfLeBytes bs < 256 ^ bs.length` without
`Init.Data.Nat.Lemmas`. -/
theorem natOfLeBytes_lt : ∀ (bs : List UInt8),
    natOfLeBytes bs < Nat.pow 256 bs.length
  | [] => by unfold natOfLeBytes; decide
  | b :: rest => by
    unfold natOfLeBytes
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hr : natOfLeBytes rest + 1 ≤ Nat.pow 256 rest.length :=
      natOfLeBytes_lt rest
    have hStep :
        b.toNat + 256 * natOfLeBytes rest < 256 + 256 * natOfLeBytes rest :=
      Nat.add_lt_add_right hb (256 * natOfLeBytes rest)
    have hMul :
        256 + 256 * natOfLeBytes rest = 256 * (natOfLeBytes rest + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    have hBound :
        256 * (natOfLeBytes rest + 1) ≤ 256 * Nat.pow 256 rest.length :=
      Nat.mul_le_mul_left 256 hr
    have hPow : 256 * Nat.pow 256 rest.length = Nat.pow 256 (rest.length + 1) :=
      Nat.mul_comm 256 (Nat.pow 256 rest.length)
    rw [hMul] at hStep
    dsimp only [List.length]
    rw [← hPow]
    exact Nat.lt_of_lt_of_le hStep hBound

/-- Four-byte little-endian decode fits strictly below `2^32`. -/
theorem decodeUInt_little_four_lt (b0 b1 b2 b3 : UInt8) :
    decodeUInt TargetEndian.little [b0, b1, b2, b3] < Nat.pow 2 32 := by
  unfold decodeUInt
  have hLt := natOfLeBytes_lt [b0, b1, b2, b3]
  have hEq : Nat.pow 256 [b0, b1, b2, b3].length = Nat.pow 2 32 := by
    change Nat.pow 256 4 = Nat.pow 2 32
    decide
  rw [hEq] at hLt
  exact hLt

/-- Exact value returned by `sliceFromRawPartsCheck` on `.ok`. -/
theorem sliceFromRawPartsCheck_ok_val {m : MemoryState} {isMut : Bool}
    {elemSize alignLog2 : Nat} {ptr : PtrVal} {len : UInt64} {val : Val}
    (h : sliceFromRawPartsCheck m isMut elemSize alignLog2 ptr len = .ok val) :
    val = .slicePtr ptr len := by
  unfold sliceFromRawPartsCheck at h
  cases hRaw : sliceRefRawCheck m isMut elemSize alignLog2 ptr len with
  | error k => rw [hRaw] at h; cases h
  | ok optAlloc =>
    rw [hRaw] at h
    cases optAlloc with
    | none => cases h; rfl
    | some a =>
      have ⟨_, hOk⟩ := ite_err_eq_ok h
      cases hOk
      rfl

/-- Weaken mutable `sliceRefRawCheck` to shared mode. -/
theorem sliceRefRawCheck_shared_of_mut {m : MemoryState}
    {elemSize alignLog2 : Nat} {ptr : PtrVal} {len : UInt64}
    {optAlloc : Option Allocation}
    (h : sliceRefRawCheck m true elemSize alignLog2 ptr len = .ok optAlloc) :
    sliceRefRawCheck m false elemSize alignLog2 ptr len = .ok optAlloc := by
  unfold sliceRefRawCheck at h
  unfold sliceRefRawCheck
  have ⟨hNotTot, h1⟩ := ite_err_eq_ok h
  rw [ite_bool_false hNotTot]
  cases hAid : ptr.allocId with
  | none => rw [hAid] at h1; exact h1
  | some aid =>
    rw [hAid] at h1
    dsimp only at h1
    dsimp only
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at h1; dsimp only at h1; cases h1
    | some a =>
      rw [hFind] at h1
      dsimp only at h1
      dsimp only
      have ⟨hG1, h3⟩ := ite_err_eq_ok h1
      have ⟨_, h4⟩ := ite_err_eq_ok h3
      rw [ite_bool_false hG1,
        ite_bool_false
          (rfl : (false && !Mutability.beq a.mutability .mut) = false)]
      exact h4

/-- Weaken mutable `sliceFromRawPartsCheck` to shared mode. -/
theorem sliceCheck_shared_of_mut {m : MemoryState} {elemSize alignLog2 : Nat}
    {ptr : PtrVal} {len : UInt64} {v : Val}
    (h : sliceFromRawPartsCheck m true elemSize alignLog2 ptr len = .ok v) :
    sliceFromRawPartsCheck m false elemSize alignLog2 ptr len = .ok v := by
  unfold sliceFromRawPartsCheck at h
  unfold sliceFromRawPartsCheck
  cases hRaw : sliceRefRawCheck m true elemSize alignLog2 ptr len with
  | error k => rw [hRaw] at h; cases h
  | ok optAlloc =>
    rw [hRaw] at h
    rw [sliceRefRawCheck_shared_of_mut hRaw]
    exact h

/-- Invert byte-slice `sliceFromRawPartsCheck m isMut 1 0 ptr len = .ok v`. -/
theorem sliceFromRawPartsCheck_u8_inv {m : MemoryState} {isMut : Bool}
    {ptr : PtrVal} {len : UInt64} {v : Val}
    (h : sliceFromRawPartsCheck m isMut 1 0 ptr len = .ok v) :
    v = .slicePtr ptr len ∧
    len.toNat < isizeMaxBytes ∧
    (ptr.allocId = none → ptr.offsetBytes.toNat ≠ 0 ∧ len.toNat = 0) ∧
    (∀ aid, ptr.allocId = some aid →
      ∃ a, findAllocation aid m.allocations = some a ∧
        a.live = true ∧
        ptr.offsetBytes.toNat + len.toNat ≤ a.bytes.length ∧
        (isMut = true → a.mutability = .mut) ∧
        isSliceAllInit
          ((a.bytes.drop ptr.offsetBytes.toNat).take len.toNat) = true) := by
  have hVal := sliceFromRawPartsCheck_ok_val h
  unfold sliceFromRawPartsCheck at h
  cases hRaw : sliceRefRawCheck m isMut 1 0 ptr len with
  | error k => rw [hRaw] at h; cases h
  | ok optAlloc =>
    rw [hRaw] at h
    unfold sliceRefRawCheck at hRaw
    have ⟨hNotTot, h1⟩ := ite_err_eq_ok hRaw
    have hTot : Nat.blt (len.toNat * 1) isizeMaxBytes = true := by
      cases hB : Nat.blt (len.toNat * 1) isizeMaxBytes with
      | true => rfl
      | false => rw [hB] at hNotTot; cases hNotTot
    have hLenLt : len.toNat < isizeMaxBytes := by
      rw [Nat.mul_one] at hTot
      exact lt_of_blt_true hTot
    refine ⟨hVal, hLenLt, ?_, ?_⟩
    · intro hNone
      rw [hNone] at h1
      dsimp only at h1
      have ⟨hOr, _⟩ := ite_err_eq_ok h1
      cases hNz : Nat.beq ptr.offsetBytes.toNat 0 with
      | true => rw [hNz] at hOr; cases hOr
      | false =>
        rw [hNz] at hOr
        refine ⟨(fun h0 => by rw [h0] at hNz; cases hNz), ?_⟩
        rw [Nat.mul_one] at hOr
        cases hZ : len.toNat with
        | zero => rfl
        | succ k =>
          have hPos : Nat.blt 0 (k + 1) = true :=
            blt_true_of_lt (Nat.succ_pos k)
          rw [hZ, hPos] at hOr
          cases hOr
    · intro aid hSome
      rw [hSome] at h1
      dsimp only at h1
      cases hFind : findAllocation aid m.allocations with
      | none => rw [hFind] at h1; dsimp only at h1; cases h1
      | some a =>
        rw [hFind] at h1
        dsimp only at h1
        have ⟨hG1, h3⟩ := ite_err_eq_ok h1
        have ⟨hG2, h4⟩ := ite_err_eq_ok h3
        cases h4
        have ⟨hG3, _⟩ := ite_err_eq_ok h
        have hLive : a.live = true := by
          cases hL : a.live with
          | true => rfl
          | false => rw [hL] at hG1; cases hG1
        have hBnd :
            isInBounds a ptr.offsetBytes.toNat (len.toNat * 1) = true := by
          cases hB : isInBounds a ptr.offsetBytes.toNat (len.toNat * 1) with
          | true => rfl
          | false => rw [hLive, hB] at hG1; cases hG1
        rw [Nat.mul_one] at hBnd
        have hMut' : isMut = true → a.mutability = .mut := by
          intro hm
          subst hm
          cases hM : Mutability.beq a.mutability .mut with
          | true => exact Mutability.beq_iff.mp hM
          | false => rw [hM] at hG2; cases hG2
        have hInit :
            isSliceAllInit
              ((a.bytes.drop ptr.offsetBytes.toNat).take len.toNat) = true := by
          rw [← Nat.mul_one len.toNat]
          cases hI : isSliceAllInit
              ((a.bytes.drop ptr.offsetBytes.toNat).take (len.toNat * 1)) with
          | true => rfl
          | false => rw [hI] at hG3; cases hG3
        exact ⟨a, rfl, hLive, Nat.le_of_ble_eq_true hBnd, hMut', hInit⟩

/-- Subslice preservation for `sliceFromRawPartsCheck m _ 1 0`: any subrange
`[off .. off + subLen]` of a valid byte slice `(ptr, len)` whose offset
fits in `UInt64` yields a valid byte slice. -/
theorem sliceFromRawPartsCheck_u8_to_subslice {m : MemoryState}
    {inMut outMut : Bool} {ptr : PtrVal} {len : UInt64} {v : Val}
    (off subLen : Nat)
    (hMut : outMut = true → inMut = true)
    (hSlice : sliceFromRawPartsCheck m inMut 1 0 ptr len = .ok v)
    (hSub : off + subLen ≤ len.toNat)
    (hOffLt : ptr.offsetBytes.toNat + off < Nat.pow 2 64) :
    sliceFromRawPartsCheck m outMut 1 0
      ⟨ptr.allocId, UInt64.ofNat (ptr.offsetBytes.toNat + off), ptr.width⟩
      (UInt64.ofNat subLen) =
    .ok (.slicePtr
      ⟨ptr.allocId, UInt64.ofNat (ptr.offsetBytes.toNat + off), ptr.width⟩
      (UInt64.ofNat subLen)) := by
  let ⟨_, hLenLt, hNoneInv, hSomeInv⟩ := sliceFromRawPartsCheck_u8_inv hSlice
  have hSubLeLen : subLen ≤ len.toNat :=
    Nat.le_trans (Nat.le_add_left subLen off) hSub
  have hSubLt64 : subLen < Nat.pow 2 64 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt hSubLeLen hLenLt) (by decide)
  have hSubLenNat : (UInt64.ofNat subLen).toNat = subLen :=
    toNat_uint64_ofNat_lt hSubLt64
  have hSubIsize : subLen < isizeMaxBytes := Nat.lt_of_le_of_lt hSubLeLen hLenLt
  have hTotBlt :
      Nat.blt ((UInt64.ofNat subLen).toNat * 1) isizeMaxBytes = true := by
    rw [hSubLenNat, Nat.mul_one]
    exact blt_true_of_lt hSubIsize
  have hOffNat : (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat =
      ptr.offsetBytes.toNat + off :=
    toNat_uint64_ofNat_lt hOffLt
  unfold sliceFromRawPartsCheck sliceRefRawCheck
  dsimp only
  rw [hTotBlt]
  cases hAid : ptr.allocId with
  | none =>
    let ⟨hNz, hLen0⟩ := hNoneInv hAid
    rw [hLen0] at hSub
    have hOff0 : off = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_right off subLen) hSub)
    have hSub0 : subLen = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_left subLen off) hSub)
    have hNzSub :
        Nat.beq (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat 0 =
          false := by
      rw [hOffNat, hOff0, Nat.add_zero]
      cases hEq : Nat.beq ptr.offsetBytes.toNat 0 with
      | false => rfl
      | true => exact False.elim (hNz (Nat.eq_of_beq_eq_true hEq))
    have hPos0 : Nat.blt 0 ((UInt64.ofNat subLen).toNat * 1) = false := by
      rw [hSubLenNat, hSub0, Nat.mul_one]
      rfl
    have hMod1 :
        Nat.beq (Nat.mod (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat
          (Nat.pow 2 0)) 0 = true := by
      have hM :
          Nat.mod (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat 1 = 0 :=
        Nat.mod_one _
      change Nat.beq (Nat.mod _ 1) 0 = true
      rw [hM]
      rfl
    dsimp only
    rw [hNzSub, hPos0, hMod1]
    rfl
  | some aid =>
    let ⟨a, hFind, hLive, hBnd, hMutIn, hInit⟩ := hSomeInv aid hAid
    dsimp only
    rw [hFind]
    dsimp only
    have hNotLive : (!a.live) = false := by rw [hLive]; rfl
    have hInBnd :
        isInBounds a (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat
          ((UInt64.ofNat subLen).toNat * 1) = true := by
      unfold isInBounds
      rw [hOffNat, hSubLenNat, Nat.mul_one, Nat.add_assoc]
      exact Nat.ble_eq_true_of_le
        (Nat.le_trans (Nat.add_le_add_left hSub ptr.offsetBytes.toNat) hBnd)
    have hAligned0 :
        isAligned a (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat 0 =
          true := by
      unfold isAligned
      have hMod :
          Nat.beq (Nat.mod (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat
            (Nat.pow 2 0)) 0 = true := by
        have hM :
            Nat.mod (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat 1 = 0 :=
          Nat.mod_one _
        change Nat.beq (Nat.mod _ 1) 0 = true
        rw [hM]
        rfl
      rw [Nat.ble_eq_true_of_le (Nat.zero_le _), hMod]
      rfl
    have hGuard1 :
        (!a.live ||
          !isInBounds a (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat
            ((UInt64.ofNat subLen).toNat * 1) ||
          !isAligned a (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat 0) =
          false := by
      rw [hNotLive, hInBnd, hAligned0]
      rfl
    have hGuard2 : (outMut && !Mutability.beq a.mutability .mut) = false := by
      cases outMut with
      | false => rfl
      | true =>
        rw [Mutability.beq_iff.mpr (hMutIn (hMut rfl))]
        rfl
    have hInitSub : isSliceAllInit
        ((a.bytes.drop (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat).take
          ((UInt64.ofNat subLen).toNat * 1)) = true := by
      rw [hOffNat, hSubLenNat, Nat.mul_one]
      exact isSliceAllInit_drop_take
        ptr.offsetBytes.toNat len.toNat off subLen a.bytes hSub hInit
    have hNotInit : (!isSliceAllInit
        ((a.bytes.drop (UInt64.ofNat (ptr.offsetBytes.toNat + off)).toNat).take
          ((UInt64.ofNat subLen).toNat * 1))) = false := by
      rw [hInitSub]; rfl
    rw [ite_bool_false (rfl : (!true) = false),
      ite_bool_false hGuard1, ite_bool_false hGuard2]
    dsimp only
    rw [ite_bool_false hNotInit]

/-- `ptrAddInMem m 1 ptr off` succeeds at any subslice offset `off ≤ len.toNat`
of a valid `sliceFromRawPartsCheck m isMut 1 0 ptr len`. -/
theorem ptrAddInMem_u8_of_sliceCheck {m : MemoryState} {isMut : Bool}
    {ptr : PtrVal} {len : UInt64} {v : Val} (off : Nat)
    (hSlice : sliceFromRawPartsCheck m isMut 1 0 ptr len = .ok v)
    (hOffLe : off ≤ len.toNat) :
    ptrAddInMem m 1 ptr off =
      .ok ⟨ptr.allocId,
        UInt64.ofNat (ptr.offsetBytes.toNat + off), ptr.width⟩ := by
  let ⟨_, hLenLt, hNoneInv, hSomeInv⟩ := sliceFromRawPartsCheck_u8_inv hSlice
  have hDeltaLt : Nat.blt (off * 1) isizeMaxBytes = true := by
    rw [Nat.mul_one]
    exact blt_true_of_lt (Nat.lt_of_le_of_lt hOffLe hLenLt)
  unfold ptrAddInMem
  dsimp only
  rw [ite_bool_false (by rw [hDeltaLt]; rfl)]
  cases hPtr : ptr with
  | mk pAid pOff pW =>
    cases pAid with
    | none =>
      let ⟨_, hLen0⟩ := hNoneInv (by rw [hPtr])
      rw [hLen0] at hOffLe
      have hOff0 : off = 0 := Nat.eq_zero_of_le_zero hOffLe
      subst hOff0
      have hB0 : Nat.beq (0 * 1) 0 = true := rfl
      dsimp only
      rw [ite_bool_true hB0, Nat.add_zero, uint64_ofNat_toNat]
    | some aid =>
      let ⟨a, hFind, hLive, hBnd, _, _⟩ := hSomeInv aid (by rw [hPtr])
      dsimp only
      rw [hFind]
      dsimp only
      have hNotLive : (!a.live) = false := by rw [hLive]; rfl
      have hBle : Nat.ble (pOff.toNat + off * 1) a.bytes.length = true := by
        rw [Nat.mul_one]
        exact Nat.ble_eq_true_of_le
          (Nat.le_trans (Nat.add_le_add_left hOffLe _)
            (by rw [hPtr] at hBnd; exact hBnd))
      have hGuard :
          (!a.live || !Nat.ble (pOff.toNat + off * 1) a.bytes.length) =
            false := by
        rw [hNotLive, hBle]; rfl
      rw [ite_bool_false hGuard]
      rw [Nat.mul_one]

/-- `sliceFromRawPartsCheck` for `.i8` proves
`refValidInMem m reqMut (.slice (.int .i8 false))`. -/
theorem refValidInMem_of_sliceCheck {m : MemoryState} {reqMut : Mutability}
    {ptr : PtrVal} {len : UInt64} {v : Val}
    (h : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len =
      .ok v) :
    refValidInMem m reqMut (.slice (.int .i8 false)) (.slicePtr ptr len) =
      .ok () := by
  unfold refValidInMem
  dsimp only
  rw [ite_bool_false
      (rfl : (!isSizedNoRefV2Ty (.int .i8 false)) = false),
    show layoutOfTyV2 (.int .i8 false) = some ⟨1, 0⟩ from rfl]
  dsimp only
  rw [h]

/-- Invert `refValidInMem m reqMut (.slice (.int .i8 false))`
back to `sliceFromRawPartsCheck`. -/
theorem sliceCheck_of_refValidInMem {m : MemoryState} {reqMut : Mutability}
    {ptr : PtrVal} {len : UInt64}
    (h : refValidInMem m reqMut (.slice (.int .i8 false)) (.slicePtr ptr len) =
      .ok ()) :
    sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len =
      .ok (.slicePtr ptr len) := by
  unfold refValidInMem at h
  dsimp only at h
  rw [ite_bool_false
      (rfl : (!isSizedNoRefV2Ty (.int .i8 false)) = false),
    show layoutOfTyV2 (.int .i8 false) = some ⟨1, 0⟩ from rfl] at h
  dsimp only at h
  cases hS : sliceFromRawPartsCheck m
      (Mutability.beq reqMut .mut) 1 0 ptr len with
  | error k => rw [hS] at h; cases h
  | ok v =>
    rw [sliceFromRawPartsCheck_ok_val hS]

/-- Weaken `&mut T` / `&mut [T]` `refValidInMem` to shared `&T` / `&[T]`. -/
theorem refValid_shared_of_mut {m : MemoryState} {pointee : MirTy} {v : Val}
    (h : refValidInMem m .mut pointee v = .ok ()) :
    refValidInMem m .shared pointee v = .ok () := by
  unfold refValidInMem at h
  unfold refValidInMem
  cases pointee with
  | slice elem =>
    cases v with
    | slicePtr p len =>
      dsimp only at h
      dsimp only
      let ⟨hSz, h1⟩ := ite_err_eq_ok h
      rw [ite_bool_false hSz]
      cases hLay : layoutOfTyV2 elem with
      | none => rw [hLay] at h1; cases h1
      | some lay =>
        rw [hLay] at h1
        dsimp only at h1
        dsimp only
        cases elem with
        | int w s =>
          dsimp only at h1
          dsimp only
          cases hS : sliceFromRawPartsCheck m (Mutability.beq .mut .mut)
              lay.size lay.alignLog2 p len with
          | error k => rw [hS] at h1; cases h1
          | ok res =>
            rw [hS] at h1
            rw [show Mutability.beq .shared .mut = false from rfl,
              sliceCheck_shared_of_mut hS]
        | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
        | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
        | option _ | range _ | unsupported =>
          dsimp only at h1
          dsimp only
          let ⟨hInh, h2⟩ := ite_err_eq_ok h1
          rw [ite_bool_false hInh]
          cases hS : sliceRefRawCheck m (Mutability.beq .mut .mut)
              lay.size lay.alignLog2 p len with
          | error k => rw [hS] at h2; cases h2
          | ok optAlloc =>
            rw [hS] at h2
            rw [show Mutability.beq .shared .mut = false from rfl,
              sliceRefRawCheck_shared_of_mut hS]
            exact h2
    | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | ptr _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _
    | array _ | optionVal _ | range _ _ => cases h
  | int _ _ | bool | char | ordering | unit | tuple _ | enum _ | unsupported
  | ref _ _ | rawPtr _ _ | rangeTo _ | rangeFrom _ | array _ _ | never
  | option _ | range _ =>
    cases v with
    | ptr p =>
      dsimp only at h
      dsimp only
      let ⟨hSup, h0⟩ := ite_err_eq_ok h
      rw [ite_bool_false hSup]
      cases hLay : layoutOfTyV2 _ with
      | none => rw [hLay] at h0; dsimp only at h0; cases h0
      | some lay =>
        rw [hLay] at h0
        dsimp only at h0
        dsimp only
        cases hAid : p.allocId with
        | none => rw [hAid] at h0; exact h0
        | some aid =>
          rw [hAid] at h0
          dsimp only at h0
          dsimp only
          cases hFind : findAllocation aid m.allocations with
          | none => rw [hFind] at h0; dsimp only at h0; cases h0
          | some a =>
            rw [hFind] at h0
            dsimp only at h0
            dsimp only
            let ⟨hG, h3⟩ := ite_err_eq_ok h0
            let ⟨_, h4⟩ := ite_err_eq_ok h3
            rw [ite_bool_false hG,
              ite_bool_false
                (rfl : (Mutability.beq .shared .mut &&
                  !Mutability.beq a.mutability .mut) = false)]
            exact h4
    | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _
    | array _ | optionVal _ | range _ _ => cases h

/-- Lift `refValidInMem` into boolean `refsValidInMem`. -/
theorem refsValidInMem_of_refValid {m : MemoryState} {reqMut : Mutability}
    {pt : MirTy} {v : Val}
    (h : refValidInMem m reqMut pt v = .ok ()) :
    refsValidInMem m (.ref reqMut pt) v = true := by
  unfold refsValidInMem
  rw [h]

/-- Any valid reference in `entryMemoryWithCaller cm` stays in `cm`. -/
theorem refsStayInCallerMem_of_refValid {cm : CallerMemory}
    {reqMut : Mutability} {pt : MirTy} {v : Val}
    (h : refValidInMem (entryMemoryWithCaller cm) reqMut pt v = .ok ()) :
    refsStayInCallerMem cm (.ref reqMut pt) v = true := by
  unfold refsStayInCallerMem
  cases pt with
  | slice elem =>
    cases v with
    | slicePtr p len =>
      cases p with
      | mk pAid pOff pW =>
        cases pAid with
        | none => rfl
        | some aid =>
          unfold refValidInMem at h
          dsimp only at h
          let ⟨_, h1⟩ := ite_err_eq_ok h
          cases hLay : layoutOfTyV2 elem with
          | none => rw [hLay] at h1; cases h1
          | some lay =>
            rw [hLay] at h1
            dsimp only at h1
            have hFound :
                ∃ a, findAllocation aid cm.allocations = some a := by
              cases elem with
              | int w s =>
                dsimp only at h1
                cases hRes : sliceFromRawPartsCheck (entryMemoryWithCaller cm)
                    (Mutability.beq reqMut .mut)
                    lay.size lay.alignLog2
                    ⟨some aid, pOff, pW⟩ len with
                | error k => rw [hRes] at h1; cases h1
                | ok _ =>
                  unfold sliceFromRawPartsCheck at hRes
                  cases hRaw : sliceRefRawCheck (entryMemoryWithCaller cm)
                      (Mutability.beq reqMut .mut)
                      lay.size lay.alignLog2
                      ⟨some aid, pOff, pW⟩ len with
                  | error k => rw [hRaw] at hRes; cases hRes
                  | ok _ =>
                    unfold sliceRefRawCheck entryMemoryWithCaller at hRaw
                    let ⟨_, h2⟩ := ite_err_eq_ok hRaw
                    dsimp only at h2
                    cases hFind : findAllocation aid cm.allocations with
                    | none => rw [hFind] at h2; dsimp only at h2; cases h2
                    | some a => exact ⟨a, rfl⟩
              | bool | unit | never | char | ordering | enum _ | tuple _
              | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _
              | rangeFrom _ | option _ | range _ | unsupported =>
                dsimp only at h1
                let ⟨_, h1b⟩ := ite_err_eq_ok h1
                cases hRes : sliceRefRawCheck (entryMemoryWithCaller cm)
                    (Mutability.beq reqMut .mut)
                    lay.size lay.alignLog2
                    ⟨some aid, pOff, pW⟩ len with
                | error k => rw [hRes] at h1b; cases h1b
                | ok _ =>
                  unfold sliceRefRawCheck entryMemoryWithCaller at hRes
                  let ⟨_, h2⟩ := ite_err_eq_ok hRes
                  dsimp only at h2
                  cases hFind : findAllocation aid cm.allocations with
                  | none => rw [hFind] at h2; dsimp only at h2; cases h2
                  | some a => exact ⟨a, rfl⟩
            let ⟨_, hFind⟩ := hFound
            unfold refAllocIds
            change (findAllocation aid cm.allocations).isSome && true = true
            rw [hFind]
            rfl
    | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | ptr _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _ | array _
    | optionVal _ | range _ _ =>
      unfold refValidInMem at h; cases h
  | int _ _ | bool | char | ordering | unit | tuple _ | enum _ | unsupported
  | ref _ _ | rawPtr _ _ | rangeTo _ | rangeFrom _ | array _ _ | never
  | option _ | range _ =>
    cases v with
    | ptr p =>
      cases p with
      | mk pAid pOff pW =>
        cases pAid with
        | none => rfl
        | some aid =>
          unfold refValidInMem entryMemoryWithCaller at h
          dsimp only at h
          let ⟨_, h0⟩ := ite_err_eq_ok h
          cases hLay : layoutOfTyV2 _ with
          | none => rw [hLay] at h0; dsimp only at h0; cases h0
          | some lay =>
            rw [hLay] at h0
            dsimp only at h0
            cases hFind : findAllocation aid cm.allocations with
            | none => rw [hFind] at h0; dsimp only at h0; cases h0
            | some _ =>
              unfold refAllocIds
              change (findAllocation aid cm.allocations).isSome && true =
                true
              rw [hFind]
              rfl
    | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _ | array _
    | optionVal _ | range _ _ =>
      unfold refValidInMem at h; cases h

/-- A single reference's access spans are trivially pairwise disjoint. -/
theorem spansDisjoint_single {reqMut : Mutability} {pt : MirTy} {v : Val} :
    spansPairwiseDisjoint (refAccessSpans (.ref reqMut pt) v) = true := by
  have hAtMostOne :
      ∀ xs : List (Bool × AllocId × Nat × Nat),
        xs.length ≤ 1 → spansPairwiseDisjoint xs = true := by
    intro xs h
    cases xs with
    | nil => rfl
    | cons _ rest =>
      cases rest with
      | nil => rfl
      | cons _ _ =>
        exact False.elim (Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ h))
  apply hAtMostOne
  unfold refAccessSpans
  cases pt with
  | slice elem =>
    cases v with
    | slicePtr p len =>
      dsimp only
      cases layoutOfTyV2 elem with
      | none => exact Nat.zero_le 1
      | some _ =>
        cases p with
        | mk pAid _ _ =>
          cases pAid with
          | none => exact Nat.zero_le 1
          | some _ => exact Nat.le_refl 1
    | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | ptr _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _ | array _
    | optionVal _ | range _ _ =>
      exact Nat.zero_le 1
  | int _ _ | bool | char | ordering | unit | tuple _ | enum _ | unsupported
  | ref _ _ | rawPtr _ _ | rangeTo _ | rangeFrom _ | array _ _ | never
  | option _ | range _ =>
    cases v with
    | ptr p =>
      dsimp only
      cases layoutOfTyV2 _ with
      | none => exact Nat.zero_le 1
      | some _ =>
        cases p with
        | mk pAid _ _ =>
          cases pAid with
          | none => exact Nat.zero_le 1
          | some _ => exact Nat.le_refl 1
    | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _ | array _
    | optionVal _ | range _ _ =>
      exact Nat.zero_le 1

/-- Pairwise disjointness for two `&[u8]`/`&mut [u8]` subslice pointers from
splitting or aliasing. -/
theorem spansPairwiseDisjoint_slice_u8_pair {m1 m2 : Mutability}
    {ptr pR : PtrVal} {lenL lenR : UInt64}
    (hDisj : (m1 = .shared ∧ m2 = .shared) ∨
      match ptr.allocId with
      | none => pR.allocId = none
      | some aid => pR.allocId = some aid ∧
          pR.offsetBytes.toNat = ptr.offsetBytes.toNat + lenL.toNat) :
    spansPairwiseDisjoint
      (refAccessSpansList
        [.ref m1 (.slice (.int .i8 false)), .ref m2 (.slice (.int .i8 false))]
        [.slicePtr ptr lenL, .slicePtr pR lenR]) = true := by
  cases hDisj with
  | inl hSh =>
    let ⟨hm1, hm2⟩ := hSh
    subst hm1; subst hm2
    dsimp only [refAccessSpansList, refAccessSpans]
    cases ptr.allocId <;> cases pR.allocId <;> rfl
  | inr hMut =>
    dsimp only [refAccessSpansList, refAccessSpans]
    cases hAid : ptr.allocId with
    | none =>
      rw [hAid] at hMut
      dsimp only at hMut
      rw [hMut]
      rfl
    | some aid =>
      rw [hAid] at hMut
      rw [hMut.1]
      change spansPairwiseDisjoint
        [(Mutability.beq m1 .mut, aid, ptr.offsetBytes.toNat, lenL.toNat * 1),
         (Mutability.beq m2 .mut, aid, pR.offsetBytes.toNat, lenR.toNat * 1)] =
        true
      dsimp only [spansPairwiseDisjoint, spanDisjointWith, spanDisjoint]
      cases hM : (Mutability.beq m1 .mut || Mutability.beq m2 .mut) with
      | false => rfl
      | true =>
        have hBle :
            Nat.ble (ptr.offsetBytes.toNat + lenL.toNat * 1)
              pR.offsetBytes.toNat = true := by
          rw [Nat.mul_one, hMut.2]
          exact Nat.ble_eq_true_of_le (Nat.le_refl _)
        rw [hBle, Nat.beq_refl]
        cases Nat.beq (lenL.toNat * 1) 0 <;>
          cases Nat.beq (lenR.toNat * 1) 0 <;> rfl

/-- Any offset is aligned for 1-byte alignment (`alignLog2 = 0`). -/
theorem isAligned_zero (a : Allocation) (offset : Nat) :
    isAligned a offset 0 = true := by
  unfold isAligned
  have h0 : Nat.ble 0 a.alignLog2 = true :=
    Nat.ble_eq_true_of_le (Nat.zero_le _)
  have hMod : Nat.mod offset 1 = 0 := Nat.mod_one _
  have hPow : Nat.pow 2 0 = 1 := rfl
  rw [h0, hPow, hMod]
  rfl

/-- Checked `readBytes` on a live, in-bounds, aligned allocation. -/
theorem readBytes_ok_of_alloc {m : MemoryState} {place : MemPlace}
    {size alignLog2 : Nat} {a : Allocation}
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a place.offset size = true)
    (hAlign : isAligned a place.offset alignLog2 = true) :
    readBytes m place size alignLog2 =
      .ok ((a.bytes.drop place.offset).take size) := by
  unfold readBytes
  rw [hFind]
  dsimp only
  cases hZero : Nat.beq size 0 with
  | true =>
    have hS : size = 0 := Nat.eq_of_beq_eq_true hZero
    subst hS
    rw [ite_bool_true rfl, ite_bool_false (by rw [hAlign]; rfl)]
    rfl
  | false =>
    rw [ite_bool_false rfl,
      ite_bool_false (by rw [hLive, hBounds, hAlign]; rfl)]

/-- Checked `writeBytes` on a live, mutable, in-bounds, aligned allocation. -/
theorem writeBytes_ok_of_alloc {m : MemoryState} {place : MemPlace}
    {alignLog2 : Nat} {bytes : List AllocByte} {a : Allocation}
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut)
    (hBounds : isInBounds a place.offset bytes.length = true)
    (hAlign : isAligned a place.offset alignLog2 = true) :
    writeBytes m place alignLog2 bytes =
      if Nat.beq bytes.length 0 then
        .ok m
      else
        let bytes' := a.bytes.take place.offset ++ bytes ++
          a.bytes.drop (place.offset + bytes.length)
        .ok { m with
          allocations :=
            replaceAllocation { a with bytes := bytes' } m.allocations } := by
  unfold writeBytes
  rw [hFind]
  dsimp only
  cases hZero : Nat.beq bytes.length 0 with
  | true =>
    rw [ite_bool_true rfl, ite_bool_true rfl,
      ite_bool_false (by rw [hAlign]; rfl)]
  | false =>
    rw [ite_bool_false rfl, ite_bool_false rfl,
      ite_bool_false (by rw [hLive, hBounds, hAlign]; rfl), hMut]

/-- Non-empty `writeBytes` on a live, mutable, in-bounds, aligned allocation. -/
theorem writeBytes_nonempty_ok_of_alloc {m : MemoryState} {place : MemPlace}
    {alignLog2 : Nat} {bytes : List AllocByte} {a : Allocation}
    (hPos : Nat.beq bytes.length 0 = false)
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut)
    (hBounds : isInBounds a place.offset bytes.length = true)
    (hAlign : isAligned a place.offset alignLog2 = true) :
    writeBytes m place alignLog2 bytes =
      let bytes' := a.bytes.take place.offset ++ bytes ++
        a.bytes.drop (place.offset + bytes.length)
      .ok { m with
        allocations :=
          replaceAllocation { a with bytes := bytes' } m.allocations } := by
  rw [writeBytes_ok_of_alloc hFind hLive hMut hBounds hAlign,
    ite_bool_false hPos]

/-! ## Section 5: `checkValV2`, `checkArgsMatchV2`, and `initStateV2` -/

/-- Invert `checkValV2 v (.ref reqMut (.slice (.int .i8 false))) = true`. -/
theorem checkValV2_slice_u8_inv {reqMut : Mutability} {v : Val}
    (h : checkValV2 v (.ref reqMut (.slice (.int .i8 false))) = true) :
    ∃ ptr len, v = .slicePtr ptr len ∧ ptr.width = .isize := by
  cases v with
  | slicePtr ptr len =>
    change IntWidth.beq ptr.width .isize = true at h
    cases hW : ptr.width with
    | i8 | i16 | i32 | i64 | i128 => rw [hW] at h; cases h
    | isize => exact ⟨ptr, len, rfl, hW⟩
  | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
  | rangeTo _ | rangeFrom _ | tuple _ | array _ | bytes _ | range _ _ =>
    cases h
  | optionVal o => cases o <;> cases h

/-- Field-level inversion for unsigned `.isize` `checkValV2 (.scalar s)`. -/
theorem checkValV2_isize_fields {s : ScalarVal}
    (h : checkValV2 (.scalar s) (.int .isize false) = true) :
    s.width = .isize ∧ s.signed = false ∧ ScalarVal.wf s = true := by
  cases s with
  | mk w sg bits =>
    have h' :
        (match (if ScalarVal.wf { width := w, signed := sg, bits := bits } =
            true then some (MirTy.int w sg) else none) with
          | some vTy => vTy.beq (.int .isize false)
          | none => false) = true := h
    cases hWf : ScalarVal.wf { width := w, signed := sg, bits := bits } with
    | false => rw [hWf] at h'; cases h'
    | true =>
      rw [hWf] at h'
      cases w <;> cases sg <;> cases h'
      exact ⟨rfl, rfl, rfl⟩

/-- Scalar inversion for unsigned `.isize` `checkValV2 v`. -/
theorem checkValV2_isize_scalar {v : Val}
    (h : checkValV2 v (.int .isize false) = true) :
    ∃ s : ScalarVal, v = .scalar s ∧ s.width = .isize ∧ s.signed = false ∧
      ScalarVal.wf s = true := by
  cases v with
  | scalar s => exact ⟨s, rfl, checkValV2_isize_fields h⟩
  | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
  | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ | tuple _
  | array _ | range _ _ => cases h
  | optionVal optV => cases optV <;> cases h

/-- Bitvector inversion for unsigned `.isize` `checkValV2 v`. -/
theorem checkValV2_isize_inv {v : Val}
    (h : checkValV2 v (.int .isize false) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨.isize, false, bits⟩ ∧
      ScalarVal.wf ⟨.isize, false, bits⟩ = true := by
  let ⟨s, hs, hW, hS, hWf⟩ := checkValV2_isize_scalar h
  cases s with
  | mk w sg bits =>
    dsimp only at hW hS hWf
    subst hW hS hs
    exact ⟨bits, rfl, hWf⟩

/-- Generic singleton inversion for `checkArgsMatchV2 args [t0] = true`. -/
theorem checkArgsMatchV2_singleton_inv {args : List Val} {t0 : MirTy}
    (h : checkArgsMatchV2 args [t0] = true) :
    ∃ v0 : Val, args = [v0] ∧ checkValV2 v0 t0 = true := by
  cases args with
  | nil => cases h
  | cons v0 rest =>
    cases rest with
    | cons _ _ =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 t0 <;> rw [hV0] at h <;> cases h
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 t0 with
      | false => rw [hV0] at h; cases h
      | true => exact ⟨v0, rfl, hV0⟩

/-- Generic pair inversion for `checkArgsMatchV2 args [t0, t1] = true`. -/
theorem checkArgsMatchV2_pair_inv {args : List Val} {t0 t1 : MirTy}
    (h : checkArgsMatchV2 args [t0, t1] = true) :
    ∃ v0 v1 : Val, args = [v0, v1] ∧
      checkValV2 v0 t0 = true ∧ checkValV2 v1 t1 = true := by
  cases args with
  | nil => cases h
  | cons v0 rest1 =>
    cases rest1 with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 t0 <;> rw [hV0] at h <;> cases h
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 t0 with
        | false => rw [hV0] at h; cases h
        | true =>
          rw [hV0] at h
          cases hV1 : checkValV2 v1 t1 <;> rw [hV1] at h <;> cases h
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 t0 with
        | false => rw [hV0] at h; cases h
        | true =>
          rw [hV0] at h
          cases hV1 : checkValV2 v1 t1 with
          | false => rw [hV1] at h; cases h
          | true => exact ⟨v0, v1, rfl, hV0, hV1⟩

/-- Invert `checkArgsMatchV2 args [.ref reqMut (.slice (.int .i8 false))]`. -/
theorem checkArgsMatchV2_slice_u8_inv {reqMut : Mutability} {args : List Val}
    (h : checkArgsMatchV2 args [.ref reqMut (.slice (.int .i8 false))] = true) :
    ∃ (ptrAid : Option AllocId) (ptrOff : UInt64) (len : UInt64),
      args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len] := by
  let ⟨v0, hv0, hMatch⟩ := checkArgsMatchV2_singleton_inv h
  let ⟨ptr, len, hPtr, hW⟩ := checkValV2_slice_u8_inv hMatch
  cases ptr with
  | mk ptrAid ptrOff ptrW =>
    dsimp only at hW
    subst hW hPtr hv0
    exact ⟨ptrAid, ptrOff, len, rfl⟩

/-- Invert `checkArgsMatchV2` for `[&'a [u8] / &'a mut [u8], usize]`. -/
theorem checkArgsMatchV2_slice_u8_isize_inv {reqMut : Mutability}
    {args : List Val}
    (h : checkArgsMatchV2 args
      [.ref reqMut (.slice (.int .i8 false)), .int .isize false] = true) :
    ∃ (ptr : PtrVal) (len : UInt64) (midBits : BitVec 128),
      args = [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩] ∧
      ptr.width = .isize ∧
      ScalarVal.wf ⟨.isize, false, midBits⟩ = true := by
  let ⟨v0, v1, hArgs, h0, h1⟩ := checkArgsMatchV2_pair_inv h
  let ⟨ptr, len, hv0, hPtrW⟩ := checkValV2_slice_u8_inv h0
  let ⟨midBits, hv1, hMidWf⟩ := checkValV2_isize_inv h1
  subst hv0 hv1 hArgs
  exact ⟨ptr, len, midBits, rfl, hPtrW, hMidWf⟩

/-- Invert `ValidEntryArgsV2` for one `&[u8]`/`&mut [u8]` slice param. -/
theorem validEntryArgsV2_slice_u8_inv {body : Body} {reqMut : Mutability}
    {q : Query}
    (hParams : (body.locals.drop 1).take body.argumentCount =
      [.ref reqMut (.slice (.int .i8 false))])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ (ptrAid : Option AllocId) (ptrOff : UInt64) (len : UInt64),
      q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len] ∧
      validCallerMemory q.callerMem = true ∧
      refValidInMem (entryMemoryWithCaller q.callerMem) reqMut
        (.slice (.int .i8 false)) (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len) =
        .ok () := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  have hMatch' :
      checkArgsMatchV2 q.args
        [.ref reqMut (.slice (.int .i8 false))] = true := by
    rw [← hParams]; exact hMatch
  let ⟨ptrAid, ptrOff, len, hArgs⟩ := checkArgsMatchV2_slice_u8_inv hMatch'
  refine ⟨ptrAid, ptrOff, len, hArgs, hCM, ?_⟩
  have hRefs' :
      refsValidInMemList (entryMemoryWithCaller q.callerMem)
        [.ref reqMut (.slice (.int .i8 false))]
        [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len] = true := by
    rw [← hArgs, ← hParams]; exact hRefs
  dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
  cases hR : refValidInMem (entryMemoryWithCaller q.callerMem) reqMut
      (.slice (.int .i8 false)) (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len) with
  | error k => rw [hR] at hRefs'; cases hRefs'
  | ok u => cases u; rfl

private theorem refValidInMem_allocations_eq {m1 m2 : MemoryState}
    (hEq : m1.allocations = m2.allocations) (reqMut : Mutability)
    (pt : MirTy) (v : Val) :
    refValidInMem m1 reqMut pt v = refValidInMem m2 reqMut pt v := by
  cases m1 with
  | mk n1 a1 =>
    cases m2 with
    | mk n2 a2 =>
      dsimp only at hEq
      subst hEq
      cases v with
      | ptr p =>
        unfold refValidInMem
        cases isUnsizedTy pt <;> rfl
      | slicePtr p len =>
        unfold refValidInMem
        cases pt with
        | slice elem =>
          unfold sliceFromRawPartsCheck
          rfl
        | _ => rfl
      | _ => rfl

mutual
  /-- `refsValidInMem` depends only on `m.allocations`, not `m.nextAllocId`. -/
  theorem refsValidInMem_allocations_eq {m1 m2 : MemoryState}
      (hEq : m1.allocations = m2.allocations) :
      ∀ (ty : MirTy) (v : Val),
        refsValidInMem m1 ty v = refsValidInMem m2 ty v
    | .ref reqMut pt, v => by
      unfold refsValidInMem
      rw [refValidInMem_allocations_eq hEq reqMut pt v]
    | .tuple fs, .tuple vs => by
      unfold refsValidInMem
      exact refsValidInMemList_allocations_eq hEq fs vs
    | .tuple _, .scalar _ | .tuple _, .bool _ | .tuple _, .char _
    | .tuple _, .ordering _ | .tuple _, .unit | .tuple _, .enumVal _ _
    | .tuple _, .ptr _ | .tuple _, .slicePtr _ _ | .tuple _, .rangeTo _
    | .tuple _, .rangeFrom _ | .tuple _, .range _ _ | .tuple _, .optionVal _
    | .tuple _, .array _ | .tuple _, .bytes _ => rfl
    | .array elem _, .array vs => by
      unfold refsValidInMem
      exact refsValidInMemArray_allocations_eq hEq elem vs
    | .array _ _, .scalar _ | .array _ _, .bool _ | .array _ _, .char _
    | .array _ _, .ordering _ | .array _ _, .unit | .array _ _, .enumVal _ _
    | .array _ _, .ptr _ | .array _ _, .slicePtr _ _ | .array _ _, .rangeTo _
    | .array _ _, .rangeFrom _ | .array _ _, .range _ _
    | .array _ _, .optionVal _ | .array _ _, .tuple _
    | .array _ _, .bytes _ => rfl
    | .option inner, .optionVal (some innerV) => by
      unfold refsValidInMem
      exact refsValidInMem_allocations_eq hEq inner innerV
    | .option _, .optionVal none => rfl
    | .option _, .scalar _ | .option _, .bool _ | .option _, .char _
    | .option _, .ordering _ | .option _, .unit | .option _, .enumVal _ _
    | .option _, .ptr _ | .option _, .slicePtr _ _ | .option _, .rangeTo _
    | .option _, .rangeFrom _ | .option _, .range _ _ | .option _, .tuple _
    | .option _, .array _ | .option _, .bytes _ => rfl
    | .bool, v | .int _ _, v | .unit, v | .never, v | .char, v
    | .ordering, v | .enum _, v | .rawPtr _ _, v | .slice _, v
    | .rangeTo _, v | .rangeFrom _, v | .range _, v | .unsupported, v => by
      unfold refsValidInMem
      cases v <;> rfl

  /-- `refsValidInMemList` depends only on `m.allocations`. -/
  theorem refsValidInMemList_allocations_eq {m1 m2 : MemoryState}
      (hEq : m1.allocations = m2.allocations) :
      ∀ (tys : List MirTy) (vs : List Val),
        refsValidInMemList m1 tys vs = refsValidInMemList m2 tys vs
    | [], [] => rfl
    | t :: ts, v :: vs => by
      unfold refsValidInMemList
      rw [refsValidInMem_allocations_eq hEq t v,
        refsValidInMemList_allocations_eq hEq ts vs]
    | [], _ :: _ | _ :: _, [] => rfl

  /-- `refsValidInMemArray` depends only on `m.allocations`. -/
  theorem refsValidInMemArray_allocations_eq {m1 m2 : MemoryState}
      (hEq : m1.allocations = m2.allocations) (elem : MirTy) :
      ∀ (vs : List Val),
        refsValidInMemArray m1 elem vs = refsValidInMemArray m2 elem vs
    | [] => rfl
    | v :: vs => by
      unfold refsValidInMemArray
      rw [refsValidInMem_allocations_eq hEq elem v,
        refsValidInMemArray_allocations_eq hEq elem vs]
end

/-- `entryMemoryForArgsV2` preserves `entryMemoryWithCaller`'s allocations. -/
theorem entryMemoryForArgsV2_allocations_eq (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val) :
    (entryMemoryForArgsV2 cm paramTys args).allocations =
      (entryMemoryWithCaller cm).allocations := by
  unfold entryMemoryForArgsV2
  cases tyListHasRawPtrV2 paramTys <;> rfl

/-- Reduce `initStateV2 p q` directly to `.ok` from its component checks. -/
theorem initStateV2_ok_of {p : Program} {q : Query} {body : Body}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hCM : validCallerMemory q.callerMem = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValidV2 body = true)
    (hCast : castTypesValid body = true)
    (hAct : assertConditionTypesValid body = true)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args
      ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0,
      initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
      q.callerMem,
      entryMemoryForArgsV2 q.callerMem
        ((body.locals.drop 1).take body.argumentCount) q.args⟩ := by
  have hRefsForArgs :
      refsValidInMemList
        (entryMemoryForArgsV2 q.callerMem
          ((body.locals.drop 1).take body.argumentCount) q.args)
        ((body.locals.drop 1).take body.argumentCount) q.args = true := by
    rw [refsValidInMemList_allocations_eq
      (entryMemoryForArgsV2_allocations_eq q.callerMem _ q.args)]
    exact hRefs
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hAct, hLocs]
  rw [hArgs, hRefsForArgs, hDisj]
  rfl

/-- Program-parameterized entry initialization from `BodyStaticAdmittedV2` and
`ValidEntryArgsV2` alone (shielding proofs from individual `Program` header
checks and future `Program` configuration fields). -/
theorem initStateV2_ok_of_admitted {p : Program} {q : Query} {body : Body}
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hAdm : BodyStaticAdmittedV2 p body = true)
    (hValid : ValidEntryArgsV2 body q) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0,
      initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
      q.callerMem,
      entryMemoryForArgsV2 q.callerMem
        ((body.locals.drop 1).take body.argumentCount) q.args⟩ := by
  unfold BodyStaticAdmittedV2 at hAdm
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  -- `&&` is left-associative in `BodyStaticAdmittedV2`.
  have hLocs := bool_and_right hAdm
  have r9 := bool_and_left hAdm
  have r8 := bool_and_left (bool_and_left r9)
  have hAct := bool_and_right r8
  have r7 := bool_and_left r8
  have hCast := bool_and_right r7
  have r6 := bool_and_left r7
  have hDiscr := bool_and_right r6
  have r5 := bool_and_left r6
  have hSto := bool_and_right r5
  have r4 := bool_and_left r5
  have hArgLt := bool_and_right r4
  have r3 := bool_and_left r4
  have hEmpty := eq_false_of_not_eq_true (bool_and_right r3)
  have r2 := bool_and_left r3
  have r1 := bool_and_left r2
  have hPV := bool_and_right r1
  have hPW := bool_and_left r1
  exact initStateV2_ok_of hPW hPV hCM hEntry hEmpty hArgLt hSto
    hDiscr hCast hAct hLocs hArgs hRefs hDisj

/-- Entry initialization equation specialized to `ctx.entryProg`. -/
theorem BodyCtx.initStateV2_ok_of (ctx : BodyCtx) (h_body : ctx.HasBody)
    {q : Query}
    (hAdm : BodyStaticAdmittedV2 ctx.program ctx.body = true)
    (hValid : ValidEntryArgsV2 ctx.body q) :
    initStateV2 ctx.entryProg q = .ok ⟨[⟨ctx.defId, 0, 0,
      initLocalsLoop ctx.body q.args 0 ctx.body.locals, none, none, none⟩],
      q.callerMem,
      entryMemoryForArgsV2 q.callerMem
        ((ctx.body.locals.drop 1).take ctx.body.argumentCount) q.args⟩ :=
  Anneal.MirWp.initStateV2_ok_of_admitted
    (p := ctx.entryProg) h_body hAdm hValid

/-- Convert an exact-outcome Profile v2 execution into the slice-identity
`WellFormedV2`, `BehaviorV2`, and `SatisfiesPostV2` postcondition. -/
theorem stable_slice_of_exec {p : Program} {defId : DefId} {q : Query}
    {fuel : Nat} {ptr : PtrVal} {len : UInt64}
    (hArgs : q.args = [.slicePtr ptr len])
    (hExec : execProgV2 (entryProgForBody p defId) fuel q
      (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩)) :
    WellFormedV2 (entryProgForBody p defId) q ∧
    match q.args with
    | [.slicePtr ptr len] =>
      let out := TerminalOut.returned ⟨.slicePtr ptr len, q.callerMem⟩
      BehaviorV2 (entryProgForBody p defId) q out ∧
      SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)
    | _ => False := by
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  rw [hArgs]
  exact ⟨hRes.1, hRes.2.1, hRes.2.2.2 _ rfl⟩

/-! ## Section 6: Profile v2 Place, Rvalue, CoreCallOp, and Terminators -/

/-- Copy an unprojected immediate local in Profile v2. -/
theorem readPlaceV2_copy_local {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate optVal))
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

/-- Move an unprojected immediate local in Profile v2. -/
theorem readPlaceV2_move_local {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) =
      some locals') :
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

/-- Evaluate `Rvalue.use (.copy ⟨lid, []⟩)` on an immediate local. -/
theorem evalRvalueV2_use_copy_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {dstTy : MirTy}
    {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some dstTy)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy dstTy = true) :
    evalRvalueV2 bodyLocals locals mem dstTy (.use (.copy ⟨lid, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [mirTy_beq_refl dstTy]
  rfl

/-- Evaluate `Rvalue.useRetag (.copy ⟨lid, []⟩)` on a reference-valid local. -/
theorem evalRvalueV2_useRetag_copy_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {ty : MirTy}
    {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hRV : refsValidInMem mem ty v = true) :
    evalRvalueV2 bodyLocals locals mem ty (.useRetag (.copy ⟨lid, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [mirTy_beq_refl ty, hRV]
  rfl

/-- Resolve an unprojected local destination `⟨lid, []⟩` in Profile v2. -/
theorem resolvePlaceDestV2_local_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {dstTy : MirTy} :
    resolvePlaceDestV2 bodyLocals locals mem ⟨lid, []⟩ dstTy =
      .ok (.local lid) := rfl

/-- Write a validated value into a resolved local destination `.local lid` in
Profile v2. -/
theorem writePlaceDestV2_immediate_ok {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val}
    {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) =
      some locals') :
    writePlaceDestV2 locals mem (.local lid) ty val = .ok (locals', mem) := by
  unfold writePlaceDestV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

/-- Write a validated value into a resolved dereference destination
`.deref pt lay pv` backed by a live mutable allocation in Profile v2. -/
theorem writePlaceDestV2_deref_ok {locals : List LocalSlot}
    {mem mem' : MemoryState} {pt : MirTy} {pv : PtrVal} {aid : AllocId}
    {a : Allocation} {lay : LayoutData} {val : Val}
    (hCheck : checkValV2 val pt = true)
    (hAid : pv.allocId = some aid)
    (hFind : findAllocation aid mem.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut)
    (hStore : storeIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ val =
      .ok mem') :
    writePlaceDestV2 locals mem (.deref pt lay pv) pt val =
      .ok (locals, mem') := by
  unfold writePlaceDestV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hAid]
  dsimp only
  rw [hFind]
  dsimp only
  rw [ite_bool_false (by
    rw [hLive, Mutability.beq_iff.mpr hMut]
    cases Nat.blt 0 lay.size <;> rfl)]
  rw [hStore]

/-- Write a validated value into an immediate local in Profile v2. -/
theorem writePlaceV2_immediate_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) =
      some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val =
      .ok (locals', mem) := by
  unfold writePlaceV2
  rw [resolvePlaceDestV2_local_ok]
  exact writePlaceDestV2_immediate_ok hCheck hSlot hSet

/-- Evaluate `CoreCallOp.sliceGetUncheckedRangeTo` on a `[u8]` slice. -/
theorem execCoreCallOp_sliceGetUncheckedRangeTo_ok {m : MemoryState}
    {inMut outMut : Mutability} {p pOut : PtrVal} {len lenOut endOff : UInt64}
    (hMut : (Mutability.beq inMut .shared &&
      Mutability.beq outMut .mut) = false)
    (hRef : refValidInMem m inMut (.slice (.int .i8 false))
      (.slicePtr p len) = .ok ())
    (hGet : sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat =
      .ok (.slicePtr pOut lenOut)) :
    execCoreCallOp m .sliceGetUncheckedRangeTo
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeTo (.int .isize false), .rangeTo endOff)]
      (.ref outMut (.slice (.int .i8 false))) =
      .ok (.slicePtr pOut lenOut) := by
  unfold execCoreCallOp
  dsimp only
  rw [ite_bool_false hMut]
  rw [hRef]
  exact hGet

/-- Specialize `execCoreCallOp_sliceGetUncheckedRangeTo_ok` to `&[u8]`. -/
theorem execCoreCallOp_sliceGetUncheckedRangeTo_shared_ok {m : MemoryState}
    {p pOut : PtrVal} {len lenOut endOff : UInt64}
    (hRef : refValidInMem m .shared (.slice (.int .i8 false))
      (.slicePtr p len) = .ok ())
    (hGet : sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat =
      .ok (.slicePtr pOut lenOut)) :
    execCoreCallOp m .sliceGetUncheckedRangeTo
      [(.ref .shared (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeTo (.int .isize false), .rangeTo endOff)]
      (.ref .shared (.slice (.int .i8 false))) = .ok (.slicePtr pOut lenOut) :=
  execCoreCallOp_sliceGetUncheckedRangeTo_ok rfl hRef hGet

/-- Evaluate `CoreCallOp.sliceGetUncheckedRangeFrom` on a `[u8]` slice. -/
theorem execCoreCallOp_sliceGetUncheckedRangeFrom_ok {m : MemoryState}
    {inMut outMut : Mutability} {p pOut : PtrVal} {len lenOut startOff : UInt64}
    (hMut : (Mutability.beq inMut .shared &&
      Mutability.beq outMut .mut) = false)
    (hRef : refValidInMem m inMut (.slice (.int .i8 false))
      (.slicePtr p len) = .ok ())
    (hGet : sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat =
      .ok (.slicePtr pOut lenOut)) :
    execCoreCallOp m .sliceGetUncheckedRangeFrom
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)]
      (.ref outMut (.slice (.int .i8 false))) =
      .ok (.slicePtr pOut lenOut) := by
  unfold execCoreCallOp
  dsimp only
  rw [ite_bool_false hMut]
  rw [hRef]
  exact hGet

/-- Specialize `execCoreCallOp_sliceGetUncheckedRangeFrom_ok` to `&[u8]`. -/
theorem execCoreCallOp_sliceGetUncheckedRangeFrom_shared_ok {m : MemoryState}
    {p pOut : PtrVal} {len lenOut startOff : UInt64}
    (hRef : refValidInMem m .shared (.slice (.int .i8 false))
      (.slicePtr p len) = .ok ())
    (hGet : sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat =
      .ok (.slicePtr pOut lenOut)) :
    execCoreCallOp m .sliceGetUncheckedRangeFrom
      [(.ref .shared (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)]
      (.ref .shared (.slice (.int .i8 false))) = .ok (.slicePtr pOut lenOut) :=
  execCoreCallOp_sliceGetUncheckedRangeFrom_ok rfl hRef hGet

/-- Evaluate `Rvalue.ref` / `&(*local)` reborrow when `refValidInMem` holds. -/
theorem evalRefRvalueV2_deref_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {srcMut reqMut : Mutability} {pt : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some (.ref srcMut pt))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hMut : (Mutability.beq srcMut .shared &&
      Mutability.beq reqMut .mut) = false)
    (hRef : refValidInMem mem reqMut pt v = .ok ()) :
    evalRefRvalueV2 bodyLocals locals mem (.ref reqMut pt) reqMut
      ⟨lid, [.deref]⟩ = .ok (v, locals, mem) := by
  unfold evalRefRvalueV2
  rw [hTy, hSlot]
  dsimp only
  rw [ite_bool_false hMut]
  rw [ite_bool_false (by rw [mirTy_beq_refl (.ref reqMut pt)]; rfl)]
  rw [hRef]

/-- If every allocation id in `ids` belongs to `cm`, none is a callee
`.rodata` allocation. -/
theorem anyRodataAllocId_false_of_all_in_caller {cm : CallerMemory}
    {mem : MemoryState} :
    ∀ (ids : List AllocId),
      ids.all (fun aid => (findAllocation aid cm.allocations).isSome) = true →
      anyRodataAllocId cm mem ids = false
  | [], _ => rfl
  | aid :: rest, hAll => by
    change ((findAllocation aid cm.allocations).isSome &&
      rest.all (fun a => (findAllocation a cm.allocations).isSome)) = true
      at hAll
    cases hFind : findAllocation aid cm.allocations with
    | none => rw [hFind] at hAll; cases hAll
    | some _ =>
      rw [hFind] at hAll
      have hRest :
          rest.all (fun a => (findAllocation a cm.allocations).isSome) =
            true := hAll
      unfold anyRodataAllocId isRodataAllocId
      rw [hFind]
      exact anyRodataAllocId_false_of_all_in_caller rest hRest

mutual
  /-- On types containing no raw pointers, `ptrOrRefAllocIds` agrees with
  `refAllocIds`. -/
  theorem ptrOrRefAllocIds_eq_refAllocIds_of_noRawPtr :
      ∀ (ty : MirTy) (v : Val),
        tyHasRawPtrV2 ty = false →
        ptrOrRefAllocIds ty v = refAllocIds ty v
    | .rawPtr _ _, _, hNoRaw => by cases hNoRaw
    | .tuple ts, v, hNoRaw => by
      cases v with
      | tuple vs => exact ptrOrRefAllocIdsList_eq_refAllocIdsList ts vs hNoRaw
      | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | bytes _
      | range _ _ => rfl
      | optionVal optV => cases optV <;> rfl
    | .array elem _, v, hNoRaw => by
      cases v with
      | array vs =>
        exact ptrOrRefAllocIdsArray_eq_refAllocIdsArray elem vs hNoRaw
      | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | tuple _ | bytes _
      | range _ _ => rfl
      | optionVal optV => cases optV <;> rfl
    | .option inner, v, hNoRaw => by
      cases v with
      | optionVal optV =>
        cases optV with
        | none => rfl
        | some iv =>
          exact ptrOrRefAllocIds_eq_refAllocIds_of_noRawPtr inner iv hNoRaw
      | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | tuple _ | array _ | bytes _
      | range _ _ => rfl
    | .ref _ pt, v, _ => by cases pt <;> cases v <;> rfl
    | .int _ _, v, _ | .bool, v, _ | .char, v, _ | .ordering, v, _
    | .unit, v, _ | .slice _, v, _ | .enum _, v, _ | .rangeTo _, v, _
    | .rangeFrom _, v, _ | .unsupported, v, _ | .never, v, _
    | .range _, v, _ => by
      cases v <;> rfl

  theorem ptrOrRefAllocIdsList_eq_refAllocIdsList :
      ∀ (ts : List MirTy) (vs : List Val),
        tyListHasRawPtrV2 ts = false →
        ptrOrRefAllocIdsList ts vs = refAllocIdsList ts vs
    | [], [], _ => rfl
    | [], _ :: _, _ => rfl
    | _ :: _, [], _ => rfl
    | t :: ts, v :: vs, hNoRaw => by
      change (tyHasRawPtrV2 t || tyListHasRawPtrV2 ts) = false at hNoRaw
      cases ht : tyHasRawPtrV2 t with
      | true => rw [ht] at hNoRaw; cases hNoRaw
      | false =>
        rw [ht] at hNoRaw
        unfold ptrOrRefAllocIdsList refAllocIdsList
        rw [ptrOrRefAllocIds_eq_refAllocIds_of_noRawPtr t v ht,
          ptrOrRefAllocIdsList_eq_refAllocIdsList ts vs hNoRaw]

  theorem ptrOrRefAllocIdsArray_eq_refAllocIdsArray (elem : MirTy) :
      ∀ (vs : List Val),
        tyHasRawPtrV2 elem = false →
        ptrOrRefAllocIdsArray elem vs = refAllocIdsArray elem vs
    | [], _ => rfl
    | v :: vs, hNoRaw => by
      unfold ptrOrRefAllocIdsArray refAllocIdsArray
      rw [ptrOrRefAllocIds_eq_refAllocIds_of_noRawPtr elem v hNoRaw,
        ptrOrRefAllocIdsArray_eq_refAllocIdsArray elem vs hNoRaw]
end

/-- A raw-pointer-free return value whose references stay in `cm` cannot carry
an escaping callee `.rodata` pointer. -/
theorem hasEscapingRodataPtr_false_of_refsStay {cm : CallerMemory}
    {mem : MemoryState} {ty : MirTy} {v : Val}
    (hStay : refsStayInCallerMem cm ty v = true)
    (hNoRaw : tyHasRawPtrV2 ty = false) :
    hasEscapingRodataPtr cm mem ty v = false := by
  unfold hasEscapingRodataPtr
  rw [ptrOrRefAllocIds_eq_refAllocIds_of_noRawPtr ty v hNoRaw]
  exact anyRodataAllocId_false_of_all_in_caller _ hStay

/-- Evaluate `TerminatorKind.return_` on an initialized immediate `_0` given an
explicit non-escaping `.rodata` witness. -/
theorem evalTerminatorV2_return_ok_of_noRodata {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {ps : PanicStrategy} {hLocal : Bool} {oc : Bool}
    {retTy : MirTy} {retVal : Val}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr callerMem mem retTy retVal = false)
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalTerminatorV2 body bb frame mem callerMem ps hLocal oc =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false hNoRodata,
    ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]

/-- Evaluate `TerminatorKind.return_` on an initialized immediate `_0` whose
return type contains no raw pointers (`tyHasRawPtrV2 retTy = false`, discharged
by `rfl` for concrete types). -/
theorem evalTerminatorV2_return_ok {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {ps : PanicStrategy} {hLocal : Bool} {oc : Bool}
    {retTy : MirTy} {retVal : Val}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true)
    (hNoRaw : tyHasRawPtrV2 retTy = false := by rfl) :
    evalTerminatorV2 body bb frame mem callerMem ps hLocal oc =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) :=
  evalTerminatorV2_return_ok_of_noRodata hTerm hCleanup hRetTy hRetSlot
    (hasEscapingRodataPtr_false_of_refsStay hStay hNoRaw) hStay hValid hDisj

end Anneal.MirWp

end
