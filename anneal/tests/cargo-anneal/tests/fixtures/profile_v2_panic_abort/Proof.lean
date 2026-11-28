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
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Captured
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Profile v2 Return Memory -/

private theorem rm2_natNotElem_false_of_mem {x : Nat} {xs : List Nat}
    (h : x ∈ xs) : natNotElem x xs = false := by
  induction h with
  | head _ =>
    unfold natNotElem
    rw [Nat.beq_refl]
    rfl
  | tail _ _ ih =>
    unfold natNotElem
    rw [ih, Bool.and_false]

private theorem rm2_mem_allocIdsOf {a : Allocation} {l : List Allocation}
    (h : a ∈ l) : a.allocId ∈ allocIdsOf l := by
  induction h with
  | head _ => unfold allocIdsOf; exact .head _
  | tail _ _ ih => unfold allocIdsOf; exact .tail _ ih

private theorem rm2_calleeLive_nil_of_sub {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    rw [rm2_natNotElem_false_of_mem (h a (.head _)), Bool.and_false,
      Bool.false_and]
    exact rm2_calleeLive_nil_of_sub (fun b hb => h b (.tail _ hb))

/-- If the call created no allocation outside the caller's ids, the Profile v2
return memory is exactly the updated caller memory. -/
private theorem rm2_extractReturnMemoryV2_eq {cm : CallerMemory}
    {mem : MemoryState} (locals : List LocalSlot)
    (h : ∀ a, a ∈ mem.allocations → a.allocId ∈ allocIdsOf cm.allocations) :
    extractReturnMemoryV2 cm mem locals = extractCallerMemory cm mem := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_sub h, List.append_nil]

private theorem rm2_extractReturnMemoryV2_entry (cm : CallerMemory)
    (locals : List LocalSlot) :
    extractReturnMemoryV2 cm (entryMemoryWithCaller cm) locals =
      extractCallerMemory cm (entryMemoryWithCaller cm) :=
  rm2_extractReturnMemoryV2_eq locals (fun _ ha => rm2_mem_allocIdsOf ha)

private theorem rm2_mem_replaceAllocation_ids {a' : Allocation}
    {ids : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      ∀ a, a ∈ replaceAllocation a' l → a.allocId ∈ ids
  | [], _, _, h => by cases h
  | b :: _, hl, a, ha => by
    unfold replaceAllocation at ha
    cases hB : Nat.beq b.allocId a'.allocId with
    | true =>
      rw [hB, ite_eq_left rfl] at ha
      cases ha with
      | head _ =>
        rw [← Nat.eq_of_beq_eq_true hB]
        exact hl b (.head _)
      | tail _ hr => exact hl a (.tail _ hr)
    | false =>
      rw [hB, ite_eq_right (fun h => Bool.noConfusion h)] at ha
      cases ha with
      | head _ => exact hl b (.head _)
      | tail _ hr =>
        exact rm2_mem_replaceAllocation_ids (fun c hc => hl c (.tail _ hc)) a hr

private theorem rm2_writeBytes_ids {ids : List AllocId} {m m' : MemoryState}
    {place : MemPlace} {al : Nat} {bs : List AllocByte}
    (h : writeBytes m place al bs = .ok m')
    (hm : ∀ b, b ∈ m.allocations → b.allocId ∈ ids) :
    ∀ b, b ∈ m'.allocations → b.allocId ∈ ids := by
  unfold writeBytes at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact hm
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; exact rm2_mem_replaceAllocation_ids hm

private theorem rm2_storeIndirectV2_ids {ids : List AllocId}
    {m m' : MemoryState} {ty : MirTy} {place : MemPlace} {v : Val}
    (h : storeIndirectV2 m ty place v = .ok m')
    (hm : ∀ b, b ∈ m.allocations → b.allocId ∈ ids) :
    ∀ b, b ∈ m'.allocations → b.allocId ∈ ids := by
  unfold storeIndirectV2 at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact rm2_writeBytes_ids h hm

private theorem execOutcomeStateV2_step {p : Program} {onDone : TerminalOut → Prop}
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

private theorem execOutcomeStateV2_done {p : Program} {onDone : TerminalOut → Prop}
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

private theorem toNat_bvOfNat_128 {n : Nat} (h : n < Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n :=
  Nat.mod_eq_of_lt h

private theorem scalarVal_wf_isize {sv : ScalarVal} (hWf : ScalarVal.wf sv = true)
    (hW : sv.width = .isize) :
    truncateBits .isize sv.bits = sv.bits := by
  unfold ScalarVal.wf at hWf
  rw [hW] at hWf
  exact eq_of_beq hWf

private theorem truncateBits_isize_toNat_lt {sv : ScalarVal} (hW : sv.width = .isize)
    (hWf : ScalarVal.wf sv = true) :
    sv.bits.toNat < Nat.pow 2 64 := by
  have hEq := scalarVal_wf_isize hWf hW
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

private theorem scalarWf_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 n⟩ = true := by
  unfold ScalarVal.wf
  dsimp only
  have hMod : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  rw [truncateBits_of_toNat_lt (by rw [hMod]; exact h)]
  exact beq_self_eq_true _

private theorem scalar_eq_of_fields {sv : ScalarVal} (hW : sv.width = .isize)
    (hS : sv.signed = false) (hLt : sv.bits.toNat < Nat.pow 2 64) :
    sv = ⟨.isize, false, BitVec.ofNat 128 sv.bits.toNat⟩ := by
  cases sv with
  | mk w s b =>
    dsimp only at hW hS hLt
    subst hW; subst hS
    cases b with
    | ofFin f =>
      cases f with
      | mk v h =>
        apply congrArg (fun bv => ScalarVal.mk .isize false bv)
        apply congrArg BitVec.ofFin
        apply Fin.eq_of_val_eq
        exact (Nat.mod_eq_of_lt (Nat.lt_trans hLt (by decide))).symm

private theorem decodeScalar_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  dsimp only
  have hMod : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact h)
  rw [hTr, hMod]
  rfl

private theorem bvOfInt_128_ofNat {n : Nat} (h : n < Nat.pow 2 128) :
    bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  unfold bvOfInt intEmod
  dsimp only [Int.natAbs, Int.toNat]
  have hMod : Nat.mod n (Nat.pow 2 128) = n := Nat.mod_eq_of_lt h
  change BitVec.ofNat 128 (Nat.mod n (Nat.pow 2 128)) = BitVec.ofNat 128 n
  rw [hMod]

private theorem truncateScalar_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    truncateScalar .isize false (Int.ofNat n) =
      .ok (⟨.isize, false, BitVec.ofNat 128 n⟩, false) := by
  have h128 : n < Nat.pow 2 128 := Nat.lt_trans h (by decide)
  have hMod : (BitVec.ofNat 128 n).toNat = n := toNat_bvOfNat_128 h128
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact h)
  have hBne : (BitVec.ofNat 128 n != BitVec.ofNat 128 n) = false := by
    change (!(BitVec.ofNat 128 n == BitVec.ofNat 128 n)) = false
    rw [beq_self_eq_true]
    rfl
  unfold truncateScalar
  rw [ite_bool_false rfl]
  dsimp only
  rw [bvOfInt_128_ofNat h128, hTr, hBne]

private theorem int_ofNat_beq_eq_nat_beq (a b : Nat) :
    (Int.ofNat a == Int.ofNat b) = Nat.beq a b := by
  change decide (Int.ofNat a = Int.ofNat b) = Nat.beq a b
  cases hB : Nat.beq a b with
  | true =>
    have hEq : a = b := Nat.eq_of_beq_eq_true hB
    subst hEq
    exact decide_eq_true rfl
  | false =>
    exact decide_eq_false (fun hEq => by
      have hab : a = b := Int.ofNat.inj hEq
      subst hab
      rw [Nat.beq_refl] at hB
      cases hB)

private theorem evalBinOp_isize_eq {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) :
    evalBinOp .eq
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.bool (Nat.beq a b)) := by
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false (rfl : BinOp.eq.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb, int_ofNat_beq_eq_nat_beq]

private theorem evalBinOp_isize_ne {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) :
    evalBinOp .ne
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.bool (!Nat.beq a b)) := by
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false (rfl : BinOp.ne.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb]
  change Except.ok (Val.bool (!(Int.ofNat a == Int.ofNat b))) =
    Except.ok (Val.bool (!Nat.beq a b))
  rw [int_ofNat_beq_eq_nat_beq]

private theorem evalArithOp_isize_plain (op : BinOp) (a b res : Nat)
    (hOp : op = .add ∨ op = .div ∨ op = .rem)
    (hRes : res < Nat.pow 2 64)
    (hbPos : op = .div ∨ op = .rem → 0 < b)
    (hBody :
      (match op with
       | .add => a + b
       | .div => a / b
       | .rem => a % b
       | _ => 0) = res) :
    evalArithOp op .isize false (Int.ofNat a) (Int.ofNat b) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 res⟩) := by
  have hTail :
      ∀ (r' : Nat) (op' : BinOp),
        op'.isUnchecked = false → op'.isOverflowing = false →
        (if (((if false = true then
                decide (Int.ofNat r' < -2 ^ 127) || decide (Int.ofNat r' ≥ 2 ^ 127)
              else decide (Int.ofNat r' < 0) || decide (Int.ofNat r' ≥ 2 ^ 128)) || false) &&
              op'.isUnchecked) = true then Except.error FaultKind.undefined
         else if op'.isOverflowing = true then
           Except.ok
             (Val.tuple
               [Val.scalar ⟨.isize, false, BitVec.ofNat 128 r'⟩,
                Val.bool
                  ((if false = true then
                      decide (Int.ofNat r' < -2 ^ 127) || decide (Int.ofNat r' ≥ 2 ^ 127)
                    else decide (Int.ofNat r' < 0) || decide (Int.ofNat r' ≥ 2 ^ 128)) || false)])
         else Except.ok (Val.scalar ⟨.isize, false, BitVec.ofNat 128 r'⟩)) =
        Except.ok (Val.scalar ⟨.isize, false, BitVec.ofNat 128 r'⟩) := by
    intro r' op' hU hO
    have h1 : (((if false = true then
          decide (Int.ofNat r' < -2 ^ 127) || decide (Int.ofNat r' ≥ 2 ^ 127)
        else decide (Int.ofNat r' < 0) || decide (Int.ofNat r' ≥ 2 ^ 128)) || false) &&
        op'.isUnchecked) = false := by rw [hU, Bool.and_false]
    rw [ite_bool_false h1, ite_bool_false hO]
  have hFalseAnd : ∀ x : Bool, (false && x) = false := fun _ => rfl
  have hFalseAnd2 : ∀ x y : Bool, ((false && x) && y) = false := fun _ _ => rfl
  have hZero : 0 < b → (Int.ofNat b == (0 : Int)) = false := by
    intro hp
    rw [show (0 : Int) = Int.ofNat 0 from rfl, int_ofNat_beq_eq_nat_beq]
    cases hEq : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (Nat.ne_of_gt hp (Nat.eq_of_beq_eq_true hEq))
  cases hOp with
  | inl hAdd =>
    subst hAdd; subst hBody
    unfold evalArithOp; dsimp only
    rw [ite_bool_false (hFalseAnd _), ite_bool_false (hFalseAnd2 _ _)]
    have hAddI : Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := rfl
    rw [hAddI, truncateScalar_isize_ofNat hRes]
    exact hTail (a + b) .add rfl rfl
  | inr hRest =>
    cases hRest with
    | inl hDiv =>
      subst hDiv; subst hBody
      have hp := hbPos (.inl rfl)
      unfold evalArithOp; dsimp only
      have hDZ : (true && (Int.ofNat b == (0 : Int))) = false := by rw [hZero hp]; rfl
      rw [ite_bool_false hDZ, ite_bool_false (hFalseAnd2 _ _)]
      have hDivI : intTdiv (Int.ofNat a) (Int.ofNat b) = Int.ofNat (a / b) := rfl
      rw [hDivI, truncateScalar_isize_ofNat hRes]
      exact hTail (a / b) .div rfl rfl
    | inr hRem =>
      subst hRem; subst hBody
      have hp := hbPos (.inr rfl)
      unfold evalArithOp; dsimp only
      have hDZ : (true && (Int.ofNat b == (0 : Int))) = false := by rw [hZero hp]; rfl
      rw [ite_bool_false hDZ, ite_bool_false (hFalseAnd2 _ _)]
      have hRemI : intTmod (Int.ofNat a) (Int.ofNat b) = Int.ofNat (a % b) := rfl
      rw [hRemI, truncateScalar_isize_ofNat hRes]
      exact hTail (a % b) .rem rfl rfl

private theorem evalBinOp_isize_div {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) (hbPos : 0 < b) :
    evalBinOp .div
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩) := by
  unfold evalBinOp; dsimp only
  rw [ite_bool_false (rfl : BinOp.div.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb]
  exact evalArithOp_isize_plain .div a b (a / b) (.inr (.inl rfl))
    (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha) (fun _ => hbPos) rfl

private theorem evalBinOp_isize_rem {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) (hbPos : 0 < b) :
    evalBinOp .rem
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (a % b)⟩) := by
  unfold evalBinOp; dsimp only
  rw [ite_bool_false (rfl : BinOp.rem.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb]
  exact evalArithOp_isize_plain .rem a b (a % b) (.inr (.inr rfl))
    (Nat.lt_trans (Nat.mod_lt a hbPos) hb) (fun _ => hbPos) rfl

private theorem evalBinOp_isize_add {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) (hSum : a + b < Nat.pow 2 64) :
    evalBinOp .add
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (a + b)⟩) := by
  unfold evalBinOp; dsimp only
  rw [ite_bool_false (rfl : BinOp.add.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb]
  exact evalArithOp_isize_plain .add a b (a + b) (.inl rfl) hSum
    (fun h => match h with | .inl h0 => nomatch h0 | .inr h0 => nomatch h0) rfl

private theorem initStateV2_body0_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    initStateV2 (entryProgForBody Captured.program 0) q =
      .ok {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals
        }]
        callerMem := q.callerMem
        mem := entryMemoryWithCaller q.callerMem
      } := by
  let ⟨hMem, hArgs, hRefs, hDisj⟩ := hValid
  unfold initStateV2 entryProgForBody Captured.program Trusted.MirSemantics.getElem?
  dsimp only
  have hHdr1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
  have hHdr2 : (!(true : Bool)) = false := rfl
  have hB1 : Captured.body_0.basicBlocks.isEmpty = false := rfl
  have hB2 : (!Nat.blt Captured.body_0.argumentCount Captured.body_0.locals.length) = false := rfl
  have hB3 : (!storageAnnotationsInBounds Captured.body_0) = false := by decide
  have hB4 : (!discriminantTypesValidV2 Captured.body_0) = false := by decide
  have hB5 : (!castTypesValid Captured.body_0) = false := by decide
  have hB6 : (!assertConditionTypesValid Captured.body_0) = false := by decide
  have hB7 : (!Captured.body_0.locals.all isSupportedV2LocalTy) = false := by decide
  rw [ite_bool_false hHdr1, hMem, ite_bool_false hHdr2]
  rw [ite_bool_false hB1, ite_bool_false hB2, ite_bool_false hB3,
    ite_bool_false hB4, ite_bool_false hB5, ite_bool_false hB6,
    ite_bool_false hB7]
  rw [hArgs, ite_bool_false hHdr2]
  rw [show entryMemoryForArgsV2 q.callerMem
      (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals))
      q.args = entryMemoryWithCaller q.callerMem from rfl]
  have hF1 : ((!true || !true) = false) := rfl
  have hR1 : (!refsValidInMemList (entryMemoryWithCaller q.callerMem)
      (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals)) q.args ||
      !spansPairwiseDisjoint
        (refAccessSpansList
          (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals))
          q.args)) = false := by
    rw [hRefs, hDisj]
    exact hF1
  rw [hR1]
  rfl

private theorem initLocalsLoop_body0 (va vb : Val) :
    initLocalsLoop Captured.body_0 [va, vb] 0 Captured.body_0.locals =
      [.immediate none, .immediate (some va), .immediate (some vb),
       .dead, .dead, .dead, .immediate none, .dead, .dead, .dead,
       .immediate none, .dead, .dead, .dead] :=
  rfl

private theorem ReachesV2_step {p : Program} {s₁ s₂ s₃ : State}
    (h12 : ReachesV2 p s₁ s₂) (hStep : evalStepV2 p s₂ = .step s₃) :
    ReachesV2 p s₁ s₃ :=
  .tail h12 ⟨0, rfl, hStep⟩

private theorem reachesV2_trans {p : Program} {s₁ s₂ s₃ : State}
    (h12 : ReachesV2 p s₁ s₂) (h23 : ReachesV2 p s₂ s₃) :
    ReachesV2 p s₁ s₃ := by
  induction h23 with
  | refl => exact h12
  | @tail sMid sNext _ hStep ih => exact .tail ih hStep

private theorem execOutcomeStateV2_of_reaches_post {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s₁ s₂ : State} {fuel : Nat}
    (hReach : ReachesV2 p s₁ s₂)
    (hExec : execOutcomeStateV2 p onDone onFault fuel s₂) :
    ∃ fuel', execOutcomeStateV2 p onDone onFault fuel' s₁ := by
  induction hReach generalizing fuel with
  | refl => exact ⟨fuel, hExec⟩
  | @tail sMid sNext _ hStep ih =>
    let ⟨_, _, hEval⟩ := hStep
    exact ih (execOutcomeStateV2_step hEval hExec)

private theorem evalStepV2_mk (p : Program) (frame : FrameState) (mem : MemoryState)
    (cm : CallerMemory) (stmt : StatementKind)
    (hBody : Trusted.MirSemantics.getElem? p.bodies frame.defId = some Captured.body_0)
    (bb : BasicBlock)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks frame.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = some stmt) :
    evalStepV2 p ⟨[frame], cm, mem⟩ = evalStatementV2 Captured.body_0 frame mem cm stmt := by
  unfold evalStepV2
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [hStmt]

private theorem evalStepV2_term (p : Program) (frame : FrameState) (mem : MemoryState)
    (cm : CallerMemory) (bb : BasicBlock)
    (hBody : Trusted.MirSemantics.getElem? p.bodies frame.defId = some Captured.body_0)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks frame.blockIdx = some bb)
    (hEnd : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (hLen : Nat.beq frame.stmtIdx bb.statements.length = true) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      evalTerminatorV2 Captured.body_0 bb frame mem cm p.panicStrategy
        p.hasLocalPanicHandler p.overflowChecks := by
  unfold evalStepV2
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [hEnd, ite_bool_true hLen]

private theorem evalConstLit_isize (n : Nat) (h : n < Nat.pow 2 64) :
    evalConstLit (.int .isize false) (.scalar (BitVec.ofNat 128 n)) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) := by
  unfold evalConstLit
  dsimp only
  have hMod128 : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod128]; exact h)
  have hBne : (BitVec.ofNat 128 n != BitVec.ofNat 128 n) = false := by
    change (!(BitVec.ofNat 128 n == BitVec.ofNat 128 n)) = false
    rw [beq_self_eq_true]; rfl
  rw [hTr, ite_bool_false hBne]

private theorem checkValV2_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) (.int .isize false) = true := by
  change checkVal (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) (.int .isize false) = true
  unfold checkVal Val.ty? ScalarVal.wf
  dsimp only
  have hMod128 : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod128]; exact h)
  rw [hTr, beq_self_eq_true]
  rfl

private theorem evalStepV2_storageLive_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx sIdx id : Nat) (locals locals' : List LocalSlot) (bb : BasicBlock)
    (localTy : MirTy)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements sIdx = some (.storageLive id))
    (hTy : Trusted.MirSemantics.getElem? Captured.body_0.locals id = some localTy)
    (hDead : Trusted.MirSemantics.getElem? locals id = some .dead)
    (hSet : setElem? locals id (liveUninitSlot localTy) = some locals') :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx, locals := locals }], cm, mem⟩ =
      .step ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx + 1, locals := locals' }], cm, mem⟩ := by
  rw [evalStepV2_mk _ _ mem cm _ rfl _ hBb hStmt]
  unfold evalStatementV2
  dsimp only
  rw [hTy, hDead]
  dsimp only
  rw [hSet]
  rfl

private theorem evalStepV2_storageDead_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx sIdx id : Nat) (locals locals' : List LocalSlot) (bb : BasicBlock)
    (oldVal : Option Val)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements sIdx = some (.storageDead id))
    (hNz : Nat.beq id 0 = false)
    (hSlot : Trusted.MirSemantics.getElem? locals id = some (.immediate oldVal))
    (hSet : setElem? locals id .dead = some locals') :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx, locals := locals }], cm, mem⟩ =
      .step ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx + 1, locals := locals' }], cm, mem⟩ := by
  rw [evalStepV2_mk _ _ mem cm _ rfl _ hBb hStmt]
  unfold evalStatementV2
  dsimp only
  rw [ite_bool_false hNz, hSlot]
  dsimp only
  rw [hSet]
  rfl

private theorem evalStepV2_copy_isize_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx sIdx dst src : Nat) (locals locals' : List LocalSlot) (bb : BasicBlock)
    (n : Nat) (hn : n < Nat.pow 2 64)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements sIdx =
      some (.assign ⟨dst, []⟩ (.use (.copy ⟨src, []⟩))))
    (hDstTy : Trusted.MirSemantics.getElem? Captured.body_0.locals dst = some (.int .isize false))
    (hSrcTy : Trusted.MirSemantics.getElem? Captured.body_0.locals src = some (.int .isize false))
    (hSrcVal : Trusted.MirSemantics.getElem? locals src =
      some (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩))))
    (hDstSlot : ∃ old, Trusted.MirSemantics.getElem? locals dst = some (.immediate old))
    (hSet : setElem? locals dst
      (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩))) = some locals') :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx, locals := locals }], cm, mem⟩ =
      .step ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx + 1, locals := locals' }], cm, mem⟩ := by
  rw [evalStepV2_mk _ _ mem cm _ rfl _ hBb hStmt]
  unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2 evalOperandToSlotV2 readPlaceV2
  dsimp only
  rw [hDstTy]
  dsimp only
  rw [hSrcTy, hSrcVal]
  dsimp only
  rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false)]
  rw [ite_prop_false (fun h => nomatch h)]
  dsimp only
  rw [ite_bool_false (rfl : (!MirTy.beq (.int .isize false) (.int .isize false)) = false)]
  dsimp only
  unfold writePlaceDestV2
  have hNotWf : (!checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) (.int .isize false)) =
      false := by
    rw [checkValV2_isize_ofNat hn]; rfl
  rw [ite_bool_false hNotWf]
  dsimp only
  let ⟨old, hOld⟩ := hDstSlot
  rw [hOld]
  dsimp only
  rw [hSet]
  rfl

private theorem evalStepV2_binop_move_const_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx sIdx dst src : Nat) (op : BinOp) (isMove : Bool)
    (locals locals1 locals' : List LocalSlot) (bb : BasicBlock)
    (dstTy : MirTy) (lNat rConst : Nat) (res : Val)
    (_hl : lNat < Nat.pow 2 64) (hr : rConst < Nat.pow 2 64)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements sIdx =
      some (.assign ⟨dst, []⟩ (.binaryOp op
        (if isMove then .move ⟨src, []⟩ else .copy ⟨src, []⟩)
        (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 rConst)⟩))))
    (hOp : op = .eq ∨ op = .ne ∨ op = .add)
    (hDstTy : Trusted.MirSemantics.getElem? Captured.body_0.locals dst = some dstTy)
    (hSrcTy : Trusted.MirSemantics.getElem? Captured.body_0.locals src = some (.int .isize false))
    (hSrcVal : Trusted.MirSemantics.getElem? locals src =
      some (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 lNat⟩))))
    (hLocals1 :
      (if isMove then setElem? locals src (.immediate none) else some locals) = some locals1)
    (hEval : evalBinOp op
      (.scalar ⟨.isize, false, BitVec.ofNat 128 lNat⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 rConst⟩) = .ok res)
    (hWf : checkValV2 res dstTy = true)
    (hDstSlot : ∃ old, Trusted.MirSemantics.getElem? locals1 dst = some (.immediate old))
    (hSet : setElem? locals1 dst (.immediate (some res)) = some locals') :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx, locals := locals }], cm, mem⟩ =
      .step ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx + 1, locals := locals' }], cm, mem⟩ := by
  rw [evalStepV2_mk _ _ mem cm _ rfl _ hBb hStmt]
  unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2
  dsimp only
  rw [hDstTy]
  dsimp only
  have hRv :
      evalRvalueV2 Captured.body_0.locals locals mem dstTy
        (.binaryOp op
          (if isMove then .move ⟨src, []⟩ else .copy ⟨src, []⟩)
          (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 rConst)⟩)) =
      .ok (res, locals1, mem) := by
    have stepOp : ∀ {op' : BinOp} {im : Bool},
        (match op' with | .offset => False | _ => True) →
        evalRvalueV2 Captured.body_0.locals locals mem dstTy
          (.binaryOp op'
            (if im then .move ⟨src, []⟩ else .copy ⟨src, []⟩)
            (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 rConst)⟩)) =
        (match evalPrimitiveOperandV2 Captured.body_0.locals locals mem
            (if im then .move ⟨src, []⟩ else .copy ⟨src, []⟩) with
         | .error k => .error k
         | .ok (lVal, l1, m1) =>
           match evalPrimitiveOperandV2 Captured.body_0.locals l1 m1
               (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 rConst)⟩) with
           | .error k => .error k
           | .ok (rVal, l2, m2) =>
             match evalBinOp op' lVal rVal with
             | .error k => .error k
             | .ok r => .ok (r, l2, m2)) := by
      intro op' im hNO
      cases op' <;> first | exact False.elim hNO | rfl
    have hEq' :
        evalRvalueV2 Captured.body_0.locals locals mem dstTy
          (.binaryOp op
            (if isMove then .move ⟨src, []⟩ else .copy ⟨src, []⟩)
            (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 rConst)⟩)) =
        (match evalPrimitiveOperandV2 Captured.body_0.locals locals mem
            (if isMove then .move ⟨src, []⟩ else .copy ⟨src, []⟩) with
         | .error k => .error k
         | .ok (lVal, l1, m1) =>
           match evalPrimitiveOperandV2 Captured.body_0.locals l1 m1
               (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 rConst)⟩) with
           | .error k => .error k
           | .ok (rVal, l2, m2) =>
             match evalBinOp op lVal rVal with
             | .error k => .error k
             | .ok r => .ok (r, l2, m2)) := by
      cases hOp with
      | inl h => subst h; exact stepOp trivial
      | inr h => cases h with
        | inl h => subst h; exact stepOp trivial
        | inr h => subst h; exact stepOp trivial
    rw [hEq']
    cases isMove with
    | false =>
      rw [ite_prop_false (fun h => nomatch h)]
      unfold evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
      dsimp only
      rw [hSrcTy, hSrcVal]
      dsimp only
      rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false)]
      rw [ite_prop_false (fun h => nomatch h)]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      rw [evalConstLit_isize rConst hr]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [hEval]
      have hL1 : locals = locals1 := Option.some.inj hLocals1
      rw [← hL1]
    | true =>
      rw [ite_prop_true rfl]
      have hLoc1' : setElem? locals src (.immediate none) = some locals1 := by
        rw [ite_prop_true rfl] at hLocals1; exact hLocals1
      have hLive : liveUninitSlot (.int .isize false) = .immediate none := rfl
      unfold evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
      dsimp only
      rw [hSrcTy, hSrcVal]
      dsimp only
      rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false)]
      rw [ite_prop_true rfl]
      rw [hLive, hLoc1']
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      rw [evalConstLit_isize rConst hr]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [hEval]
  rw [hRv]
  dsimp only
  unfold writePlaceDestV2
  have hNotWf : (!checkValV2 res dstTy) = false := by rw [hWf]; rfl
  rw [ite_bool_false hNotWf]
  dsimp only
  let ⟨old, hOld⟩ := hDstSlot
  rw [hOld]
  dsimp only
  rw [hSet]
  rfl

private theorem evalStepV2_binop_move_move_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx sIdx dst lId rId : Nat) (op : BinOp)
    (locals locals1 locals2 locals' : List LocalSlot) (bb : BasicBlock)
    (lNat rNat resNat : Nat)
    (hRes : resNat < Nat.pow 2 64)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements sIdx =
      some (.assign ⟨dst, []⟩ (.binaryOp op (.move ⟨lId, []⟩) (.move ⟨rId, []⟩))))
    (hOp : op = .div ∨ op = .rem)
    (hDstTy : Trusted.MirSemantics.getElem? Captured.body_0.locals dst = some (.int .isize false))
    (hLTy : Trusted.MirSemantics.getElem? Captured.body_0.locals lId = some (.int .isize false))
    (hRTy : Trusted.MirSemantics.getElem? Captured.body_0.locals rId = some (.int .isize false))
    (hLVal : Trusted.MirSemantics.getElem? locals lId =
      some (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 lNat⟩))))
    (hSet1 : setElem? locals lId (.immediate none) = some locals1)
    (hRVal : Trusted.MirSemantics.getElem? locals1 rId =
      some (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 rNat⟩))))
    (hSet2 : setElem? locals1 rId (.immediate none) = some locals2)
    (hEval : evalBinOp op
      (.scalar ⟨.isize, false, BitVec.ofNat 128 lNat⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 rNat⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 resNat⟩))
    (hDstSlot : ∃ old, Trusted.MirSemantics.getElem? locals2 dst = some (.immediate old))
    (hSet3 : setElem? locals2 dst
      (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 resNat⟩))) = some locals') :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx, locals := locals }], cm, mem⟩ =
      .step ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := sIdx + 1, locals := locals' }], cm, mem⟩ := by
  rw [evalStepV2_mk _ _ mem cm _ rfl _ hBb hStmt]
  unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2
  dsimp only
  rw [hDstTy]
  dsimp only
  have stepOp : ∀ {op' : BinOp},
      (match op' with | .offset => False | _ => True) →
      evalRvalueV2 Captured.body_0.locals locals mem (.int .isize false)
        (.binaryOp op' (.move ⟨lId, []⟩) (.move ⟨rId, []⟩)) =
      (match evalPrimitiveOperandV2 Captured.body_0.locals locals mem (.move ⟨lId, []⟩) with
       | .error k => .error k
       | .ok (lVal, l1, m1) =>
         match evalPrimitiveOperandV2 Captured.body_0.locals l1 m1 (.move ⟨rId, []⟩) with
         | .error k => .error k
         | .ok (rVal, l2, m2) =>
           match evalBinOp op' lVal rVal with
           | .error k => .error k
           | .ok r => .ok (r, l2, m2)) := by
    intro op' hNO
    cases op' <;> first | exact False.elim hNO | rfl
  have hEq' :
      evalRvalueV2 Captured.body_0.locals locals mem (.int .isize false)
        (.binaryOp op (.move ⟨lId, []⟩) (.move ⟨rId, []⟩)) =
      (match evalPrimitiveOperandV2 Captured.body_0.locals locals mem (.move ⟨lId, []⟩) with
       | .error k => .error k
       | .ok (lVal, l1, m1) =>
         match evalPrimitiveOperandV2 Captured.body_0.locals l1 m1 (.move ⟨rId, []⟩) with
         | .error k => .error k
         | .ok (rVal, l2, m2) =>
           match evalBinOp op lVal rVal with
           | .error k => .error k
           | .ok r => .ok (r, l2, m2)) := by
    cases hOp with
    | inl h => subst h; exact stepOp trivial
    | inr h => subst h; exact stepOp trivial
  rw [hEq']
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
  dsimp only
  rw [hLTy, hLVal]
  dsimp only
  rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false), ite_prop_true rfl]
  have hLiveIsize : liveUninitSlot (.int .isize false) = .immediate none := rfl
  rw [hLiveIsize, hSet1]
  dsimp only
  rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
  dsimp only
  rw [hRTy, hRVal]
  dsimp only
  rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false),
    ite_prop_true rfl, hLiveIsize, hSet2]
  dsimp only
  rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
  dsimp only
  rw [hEval]
  dsimp only
  unfold writePlaceDestV2
  have hNotWf : (!checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 resNat⟩)
      (.int .isize false)) = false := by
    rw [checkValV2_isize_ofNat hRes]; rfl
  rw [ite_bool_false hNotWf]
  dsimp only
  let ⟨old, hOld⟩ := hDstSlot
  rw [hOld]
  dsimp only
  rw [hSet3]
  rfl

private theorem evalStepV2_assert_abort_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx condId target : Nat) (msg : AssertKind) (expected condVal : Bool)
    (locals locals1 : List LocalSlot) (bb : BasicBlock)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hLen : Nat.beq bb.statements.length bb.statements.length = true)
    (hEnd : Trusted.MirSemantics.getElem? bb.statements bb.statements.length = none)
    (hTerm : bb.terminator = .assert (.move ⟨condId, []⟩) expected msg target .unreachable)
    (hMsg : msg = .divByZero ∨ msg = .remByZero)
    (hTy : Trusted.MirSemantics.getElem? Captured.body_0.locals condId = some .bool)
    (hVal : Trusted.MirSemantics.getElem? locals condId =
      some (.immediate (some (.bool condVal))))
    (hSet : setElem? locals condId (.immediate none) = some locals1) :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := bb.statements.length, locals := locals }],
          cm, mem⟩ =
      if (condVal == expected) then
        .step ⟨[{ defId := 0, blockIdx := target, stmtIdx := 0, locals := locals1 }], cm, mem⟩
      else .done (.aborted (extractCallerMemory cm mem)) := by
  rw [evalStepV2_term _ _ _ _ _ rfl hBb hEnd hLen]
  unfold evalTerminatorV2
  rw [hTerm]
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
  dsimp only
  rw [hTy, hVal]
  dsimp only
  rw [ite_bool_false (rfl : (!isSupportedV2LocalTy .bool) = false)]
  have hLive : liveUninitSlot .bool = .immediate none := rfl
  rw [ite_prop_true rfl, hLive, hSet]
  dsimp only
  rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false)]
  dsimp only
  cases hCmp : (condVal == expected) with
  | true =>
    rw [ite_prop_true rfl, ite_prop_true rfl]
    rfl
  | false =>
    rw [ite_prop_false (fun h => nomatch h), ite_prop_false (fun h => nomatch h)]
    cases hMsg with
    | inl h => subst h; rfl
    | inr h => subst h; rfl

private theorem evalStepV2_switchBool_0_4_3_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx condId : Nat) (condVal : Bool) (locals locals1 : List LocalSlot) (bb : BasicBlock)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hLen : Nat.beq bb.statements.length bb.statements.length = true)
    (hEnd : Trusted.MirSemantics.getElem? bb.statements bb.statements.length = none)
    (hTerm : bb.terminator =
      .switchInt (.move ⟨condId, []⟩) ⟨[(BitVec.ofNat 128 0, 4)], 3⟩)
    (hTy : Trusted.MirSemantics.getElem? Captured.body_0.locals condId = some .bool)
    (hVal : Trusted.MirSemantics.getElem? locals condId =
      some (.immediate (some (.bool condVal))))
    (hSet : setElem? locals condId (.immediate none) = some locals1) :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := bb.statements.length, locals := locals }],
          cm, mem⟩ =
      .step ⟨[{
        defId := 0,
        blockIdx := if condVal = true then 3 else 4,
        stmtIdx := 0,
        locals := locals1
      }], cm, mem⟩ := by
  rw [evalStepV2_term _ _ _ _ _ rfl hBb hEnd hLen]
  unfold evalTerminatorV2
  rw [hTerm]
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
  dsimp only
  rw [hTy, hVal]
  dsimp only
  rw [ite_bool_false (rfl : (!isSupportedV2LocalTy .bool) = false), ite_prop_true rfl]
  have hLiveBool : liveUninitSlot .bool = .immediate none := rfl
  rw [hLiveBool, hSet]
  dsimp only
  rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false)]
  dsimp only
  cases condVal <;> rfl

private theorem evalStepV2_goto_body0 (cm : CallerMemory) (mem : MemoryState)
    (bIdx target : Nat) (locals : List LocalSlot) (bb : BasicBlock)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hLen : Nat.beq bb.statements.length bb.statements.length = true)
    (hEnd : Trusted.MirSemantics.getElem? bb.statements bb.statements.length = none)
    (hTerm : bb.terminator = .goto target) :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := bb.statements.length, locals := locals }],
          cm, mem⟩ =
      .step ⟨[{ defId := 0, blockIdx := target, stmtIdx := 0, locals := locals }], cm, mem⟩ := by
  rw [evalStepV2_term _ _ _ _ _ rfl hBb hEnd hLen]
  unfold evalTerminatorV2
  rw [hTerm]
  rfl

private theorem evalStepV2_return_isize_body0 (cm : CallerMemory)
    (bIdx ret : Nat) (locals : List LocalSlot) (bb : BasicBlock)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_0.basicBlocks bIdx = some bb)
    (hLen : Nat.beq bb.statements.length bb.statements.length = true)
    (hEnd : Trusted.MirSemantics.getElem? bb.statements bb.statements.length = none)
    (hClean : bb.cleanup = false)
    (hTerm : bb.terminator = .return_)
    (hValidCm : validCallerMemory cm = true)
    (hRetTy : Trusted.MirSemantics.getElem? Captured.body_0.locals 0 = some (.int .isize false))
    (hRetVal : Trusted.MirSemantics.getElem? locals 0 =
      some (.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩)))) :
    evalStepV2 (entryProgForBody Captured.program 0)
        ⟨[{ defId := 0, blockIdx := bIdx, stmtIdx := bb.statements.length, locals := locals }],
          cm, entryMemoryWithCaller cm⟩ =
      .done (.returned ⟨.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩, cm⟩) := by
  rw [evalStepV2_term _ _ _ _ _ rfl hBb hEnd hLen]
  unfold evalTerminatorV2
  rw [hTerm, ite_bool_false hClean]
  dsimp only
  rw [hRetTy, hRetVal]
  dsimp only
  have h0 : hasEscapingRodataPtr cm (entryMemoryWithCaller cm)
      (.int .isize false) (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩) = false := rfl
  have h1 : refsStayInCallerMem cm (.int .isize false)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩) = true := rfl
  have h2 : refsValidInMem (entryMemoryWithCaller cm) (.int .isize false)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩) = true := rfl
  have h3 : spansPairwiseDisjoint (refAccessSpans (.int .isize false)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩)) = true := rfl
  have hGuard : (!refsStayInCallerMem cm (.int .isize false)
        (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩) ||
      !refsValidInMem (entryMemoryWithCaller cm) (.int .isize false)
        (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩) ||
      !spansPairwiseDisjoint (refAccessSpans (.int .isize false)
        (.scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩))) = false := by
    rw [h1, h2, h3]; rfl
  rw [ite_bool_false h0, ite_bool_false hGuard, rm2_extractReturnMemoryV2_entry,
    extractCallerMemory_entry cm hValidCm]

private theorem checkValV2_isize_fields {s : ScalarVal}
    (h : checkValV2 (.scalar s) (.int .isize false) = true) :
    s.width = .isize ∧ s.signed = false ∧ ScalarVal.wf s = true := by
  cases s with
  | mk w sg bits =>
    have h' : (match (if ScalarVal.wf { width := w, signed := sg, bits := bits } = true
        then some (MirTy.int w sg) else none) with
      | some vTy => vTy.beq (.int .isize false)
      | none => false) = true := h
    cases hWf : ScalarVal.wf { width := w, signed := sg, bits := bits } with
    | false => rw [hWf] at h'; cases h'
    | true =>
      rw [hWf] at h'
      cases w <;> cases sg <;> cases h'
      exact ⟨rfl, rfl, rfl⟩

private theorem checkValV2_isize_scalar {v : Val}
    (h : checkValV2 v (.int .isize false) = true) :
    ∃ s : ScalarVal,
      v = .scalar s ∧ s.width = .isize ∧ s.signed = false ∧ ScalarVal.wf s = true := by
  cases v with
  | scalar s => exact ⟨s, rfl, checkValV2_isize_fields h⟩
  | bool _ => cases h
  | char _ => cases h
  | ordering _ => cases h
  | unit => cases h
  | enumVal _ _ => cases h
  | ptr _ => cases h
  | slicePtr _ _ => cases h
  | rangeTo _ => cases h
  | rangeFrom _ => cases h
  | bytes _ => cases h
  | array _ => cases h
  | tuple _ => cases h
  | range _ _ => cases h
  | optionVal o => cases o <;> cases h
  | vec _ _ _ => cases h
  | boxPtr _ o => cases o <;> cases h

private theorem checkArgsMatchV2_two_isize {args : List Val}
    (h : checkArgsMatchV2 args [.int .isize false, .int .isize false] = true) :
    ∃ sa sb : ScalarVal, args = [.scalar sa, .scalar sb] ∧
      sa.width = .isize ∧ sa.signed = false ∧ sa.wf = true ∧
      sb.width = .isize ∧ sb.signed = false ∧ sb.wf = true := by
  cases args with
  | nil => unfold checkArgsMatchV2 at h; cases h
  | cons v1 rest1 =>
    cases rest1 with
    | nil =>
      unfold checkArgsMatchV2 at h
      cases h1 : checkValV2 v1 (.int .isize false) with
      | false => rw [h1] at h; cases h
      | true =>
        rw [h1] at h
        unfold checkArgsMatchV2 at h
        cases h
    | cons v2 rest2 =>
      cases rest2 with
      | cons _ _ =>
        unfold checkArgsMatchV2 at h
        cases h1 : checkValV2 v1 (.int .isize false) with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          unfold checkArgsMatchV2 at h
          cases h2 : checkValV2 v2 (.int .isize false) with
          | false => rw [h2] at h; cases h
          | true =>
            rw [h2] at h
            unfold checkArgsMatchV2 at h
            cases h
      | nil =>
        unfold checkArgsMatchV2 at h
        cases h1 : checkValV2 v1 (.int .isize false) with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          unfold checkArgsMatchV2 at h
          cases h2 : checkValV2 v2 (.int .isize false) with
          | false => rw [h2] at h; cases h
          | true =>
            let ⟨sa, hsa, hW1, hS1, hWf1⟩ := checkValV2_isize_scalar h1
            let ⟨sb, hsb, hW2, hS2, hWf2⟩ := checkValV2_isize_scalar h2
            exact ⟨sa, sb, by rw [hsa, hsb], hW1, hS1, hWf1, hW2, hS2, hWf2⟩

private theorem divCeilExpect_eq (a b : Nat) :
    Spec.divCeilExpect a b = if Nat.beq (a % b) 0 then a / b else a / b + 1 := by
  unfold Spec.divCeilExpect
  cases hB : Nat.beq (a % b) 0 with
  | true =>
    have hEq : a % b = 0 := Nat.eq_of_beq_eq_true hB
    rw [ite_prop_true hEq, Nat.add_zero]
    rfl
  | false =>
    have hNe : a % b ≠ 0 := fun h => by rw [h] at hB; cases hB
    rw [ite_prop_false hNe]
    rfl

private theorem div_add_one_lt_pow64 {a b : Nat}
    (ha : a < Nat.pow 2 64) (hbPos : 0 < b) (hRemNe : a % b ≠ 0) :
    a / b + 1 < Nat.pow 2 64 := by
  have hbGe2 : 2 ≤ b := by
    cases b with
    | zero => exact False.elim (Nat.lt_irrefl 0 hbPos)
    | succ k =>
      cases k with
      | zero => exact False.elim (hRemNe (Nat.mod_one a))
      | succ k' => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k'))
  have h2MulDiv : 2 * (a / b) ≤ a := by
    have h1 : 2 * (a / b) ≤ b * (a / b) := Nat.mul_le_mul_right (a / b) hbGe2
    have h2 : b * (a / b) ≤ a := Nat.mul_div_le a b
    exact Nat.le_trans h1 h2
  have hPow64 : Nat.pow 2 64 = 2 * Nat.pow 2 63 := by decide
  have hDivLt : a / b < Nat.pow 2 63 := by
    cases Nat.lt_or_ge (a / b) (Nat.pow 2 63) with
    | inl h => exact h
    | inr hGe =>
      have hMulGe : Nat.pow 2 64 ≤ 2 * (a / b) := by
        rw [hPow64]; exact Nat.mul_le_mul_left 2 hGe
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hMulGe h2MulDiv) ha)
  have hSuccLt : a / b + 1 ≤ Nat.pow 2 63 := hDivLt
  exact Nat.lt_of_le_of_lt hSuccLt (by decide)

private theorem safe_div_bb0_steps (a b : Nat) (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) (cm : CallerMemory) :
    let p0 := entryProgForBody Captured.program 0
    let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
    let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
    let mem0 := entryMemoryWithCaller cm
    let s0 : State := ⟨[{
      defId := 0, blockIdx := 0, stmtIdx := 0,
      locals := initLocalsLoop Captured.body_0 [va, vb] 0 Captured.body_0.locals
    }], cm, mem0⟩
    let l6 : List LocalSlot :=
      [.immediate none, .immediate (some va), .immediate (some vb),
       .immediate none, .immediate (some va), .immediate (some vb),
       .immediate (some (.bool (Nat.beq b 0))),
       .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
    let s6 : State := ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 6, locals := l6 }], cm, mem0⟩
    ReachesV2 p0 s0 s6 := by
  intro p0 va vb mem0 s0 l6 s6
  have hl0 := initLocalsLoop_body0 va vb
  let l1 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .dead, .dead, .immediate none, .dead, .dead, .dead,
     .immediate none, .dead, .dead, .dead]
  let l2 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate none, .dead, .immediate none, .dead, .dead, .dead,
     .immediate none, .dead, .dead, .dead]
  let l3 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate (some va), .dead, .immediate none, .dead, .dead, .dead,
     .immediate none, .dead, .dead, .dead]
  let l4 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate (some va), .immediate none, .immediate none, .dead, .dead, .dead,
     .immediate none, .dead, .dead, .dead]
  let l5 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate (some va), .immediate (some vb), .immediate none, .dead, .dead,
     .dead, .immediate none, .dead, .dead, .dead]
  have h01 : evalStepV2 p0 s0 =
      .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := l1 }], cm, mem0⟩ := by
    change evalStepV2 p0 ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := _ }], cm, mem0⟩ = _
    rw [hl0]
    exact evalStepV2_storageLive_body0 cm mem0 0 0 3 _ l1 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h12 := evalStepV2_storageLive_body0 cm mem0 0 1 4 l1 l2 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h23 := evalStepV2_copy_isize_body0 cm mem0 0 2 4 1 l2 l3 _ a ha rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have h34 := evalStepV2_storageLive_body0 cm mem0 0 3 5 l3 l4 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h45 := evalStepV2_copy_isize_body0 cm mem0 0 4 5 2 l4 l5 _ b hb rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have h56 := evalStepV2_binop_move_const_body0 cm mem0 0 5 6 5 .eq false l5 l5 l6 _
    .bool b 0 (.bool (Nat.beq b 0)) hb (by decide) rfl rfl (.inl rfl) rfl rfl rfl rfl
    (evalBinOp_isize_eq hb (by decide)) rfl ⟨none, rfl⟩ rfl
  exact ReachesV2_step (ReachesV2_step (ReachesV2_step
    (ReachesV2_step (ReachesV2_step (ReachesV2_step (.refl s0) h01) h12) h23) h34) h45) h56

private theorem safe_div_bb1_to_bb2 (a b : Nat)
    (ha : a < Nat.pow 2 64) (hb : b < Nat.pow 2 64) (hbPos : 0 < b)
    (cm : CallerMemory) (mem : MemoryState) :
    let p0 := entryProgForBody Captured.program 0
    let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
    let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
    let vq : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
    let s1 : State := ⟨[{
      defId := 0, blockIdx := 1, stmtIdx := 0,
      locals :=
        [.immediate none, .immediate (some va), .immediate (some vb),
         .immediate none, .immediate (some va), .immediate (some vb),
         .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
    }], cm, mem⟩
    let s2 : State := ⟨[{
      defId := 0, blockIdx := 2, stmtIdx := 0,
      locals :=
        [.immediate none, .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate none, .immediate (some va), .immediate (some vb),
         .immediate none, .dead, .dead, .dead]
    }], cm, mem⟩
    ReachesV2 p0 s1 s2 := by
  intro p0 va vb vq s1 s2
  have hDivLt : a / b < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
  have hbNz : Nat.beq b 0 = false := by
    cases hE : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (Nat.ne_of_gt hbPos (Nat.eq_of_beq_eq_true hE))
  let l0 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l0a : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate none, .immediate (some vb),
     .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l0b : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate none, .immediate none,
     .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l1 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .immediate none, .immediate none,
     .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l2 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .immediate none, .dead,
     .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l3 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l4 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .immediate none, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let l5 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .immediate none, .immediate none, .dead, .immediate none, .dead, .dead, .dead]
  let l6 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .immediate none, .immediate (some va), .dead, .immediate none, .dead, .dead, .dead]
  let l7 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .immediate none, .immediate (some va), .immediate none,
     .immediate none, .dead, .dead, .dead]
  let l8 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .dead, .dead, .dead]
  let l9 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead,
     .immediate none, .immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some (.bool (Nat.beq b 0))), .dead, .dead, .dead]
  have h01 := evalStepV2_binop_move_move_body0 cm mem 1 0 3 4 5 .div l0 l0a l0b l1 _
    a b (a / b) hDivLt rfl rfl (.inl rfl) rfl rfl rfl rfl rfl rfl rfl
    (evalBinOp_isize_div ha hb hbPos) ⟨none, rfl⟩ rfl
  have h12 := evalStepV2_storageDead_body0 cm mem 1 1 5 l1 l2 _ _ rfl rfl rfl rfl rfl
  have h23 := evalStepV2_storageDead_body0 cm mem 1 2 4 l2 l3 _ _ rfl rfl rfl rfl rfl
  have h34 := evalStepV2_storageLive_body0 cm mem 1 3 7 l3 l4 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h45 := evalStepV2_storageLive_body0 cm mem 1 4 8 l4 l5 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h56 := evalStepV2_copy_isize_body0 cm mem 1 5 8 1 l5 l6 _ a ha rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have h67 := evalStepV2_storageLive_body0 cm mem 1 6 9 l6 l7 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h78 := evalStepV2_copy_isize_body0 cm mem 1 7 9 2 l7 l8 _ b hb rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have h89 := evalStepV2_binop_move_const_body0 cm mem 1 8 10 9 .eq false l8 l8 l9 _
    .bool b 0 (.bool (Nat.beq b 0)) hb (by decide) rfl rfl (.inl rfl) rfl rfl rfl rfl
    (evalBinOp_isize_eq hb (by decide)) rfl ⟨none, rfl⟩ rfl
  have hTerm := evalStepV2_assert_abort_body0 cm mem 1 10 2 .remByZero false (Nat.beq b 0) l9 _
    _ rfl rfl rfl rfl (.inr rfl) rfl rfl rfl
  rw [hbNz] at hTerm
  exact ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step
    (ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step
      (.refl s1) h01) h12) h23) h34) h45) h56) h67) h78) h89) hTerm

private theorem safe_div_bb2_branch (a b : Nat)
    (ha : a < Nat.pow 2 64) (hb : b < Nat.pow 2 64) (hbPos : 0 < b)
    (cm : CallerMemory) (mem : MemoryState) :
    let p0 := entryProgForBody Captured.program 0
    let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
    let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
    let vq : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
    let vr : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a % b)⟩
    let s2 : State := ⟨[{
      defId := 0, blockIdx := 2, stmtIdx := 0,
      locals :=
        [.immediate none, .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate none, .immediate (some va), .immediate (some vb),
         .immediate none, .dead, .dead, .dead]
    }], cm, mem⟩
    let sNext : State := ⟨[{
      defId := 0, blockIdx := if Nat.beq (a % b) 0 then 4 else 3, stmtIdx := 0,
      locals :=
        [.immediate none, .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate (some vr), .dead, .dead, .immediate none,
         .immediate none, .immediate none, .dead]
    }], cm, mem⟩
    ReachesV2 p0 s2 sNext := by
  intro p0 va vb vq vr s2 sNext
  have hModLt : a % b < Nat.pow 2 64 := Nat.lt_trans (Nat.mod_lt a hbPos) hb
  let l0 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .dead, .dead, .dead]
  let l0a : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate none, .immediate none, .immediate (some vb),
     .immediate none, .dead, .dead, .dead]
  let l0b : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate none, .immediate none, .immediate none,
     .immediate none, .dead, .dead, .dead]
  let l1 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .immediate none, .immediate none,
     .immediate none, .dead, .dead, .dead]
  let l2 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .immediate none, .dead,
     .immediate none, .dead, .dead, .dead]
  let l3 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .dead, .dead, .dead]
  let l4 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .immediate none, .dead, .dead]
  let l5 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .immediate none, .immediate none, .dead]
  let l6 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .immediate none, .immediate (some vr), .dead]
  let l6a : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .immediate none, .immediate none, .dead]
  let l7 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .immediate (some (.bool (!(Nat.beq (a % b) 0)))), .immediate none, .dead]
  let l8 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead,
     .immediate none, .immediate none, .immediate none, .dead]
  have h01 := evalStepV2_binop_move_move_body0 cm mem 2 0 7 8 9 .rem l0 l0a l0b l1 _
    a b (a % b) hModLt rfl rfl (.inr rfl) rfl rfl rfl rfl rfl rfl rfl
    (evalBinOp_isize_rem ha hb hbPos) ⟨none, rfl⟩ rfl
  have h12 := evalStepV2_storageDead_body0 cm mem 2 1 9 l1 l2 _ _ rfl rfl rfl rfl rfl
  have h23 := evalStepV2_storageDead_body0 cm mem 2 2 8 l2 l3 _ _ rfl rfl rfl rfl rfl
  have h34 := evalStepV2_storageLive_body0 cm mem 2 3 11 l3 l4 _ .bool rfl rfl rfl rfl rfl
  have h45 := evalStepV2_storageLive_body0 cm mem 2 4 12 l4 l5 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h56 := evalStepV2_copy_isize_body0 cm mem 2 5 12 7 l5 l6 _ (a % b) hModLt rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have h67 := evalStepV2_binop_move_const_body0 cm mem 2 6 11 12 .ne true l6 l6a l7 _
    .bool (a % b) 0 (.bool (!(Nat.beq (a % b) 0))) hModLt (by decide) rfl rfl (.inr (.inl rfl))
    rfl rfl rfl rfl (evalBinOp_isize_ne hModLt (by decide)) rfl ⟨none, rfl⟩ rfl
  have hTerm := evalStepV2_switchBool_0_4_3_body0 cm mem 2 11 (!(Nat.beq (a % b) 0)) l7 l8 _
    rfl rfl rfl rfl rfl rfl rfl
  have hTargetEq : (if !(Nat.beq (a % b) 0) then 3 else 4) =
      if Nat.beq (a % b) 0 then 4 else 3 := by
    cases Nat.beq (a % b) 0 <;> rfl
  rw [hTargetEq] at hTerm
  exact ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step
    (ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step
      (.refl s2) h01) h12) h23) h34) h45) h56) h67) hTerm

private theorem safe_div_bb3_to_bb5 (a b : Nat)
    (ha : a < Nat.pow 2 64)
    (hAddLt : a / b + 1 < Nat.pow 2 64)
    (cm : CallerMemory) (mem : MemoryState) :
    let p0 := entryProgForBody Captured.program 0
    let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
    let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
    let vq : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
    let vr : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a % b)⟩
    let vret : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b + 1)⟩
    let s3 : State := ⟨[{
      defId := 0, blockIdx := 3, stmtIdx := 0,
      locals :=
        [.immediate none, .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate (some vr), .dead, .dead, .immediate none,
         .immediate none, .immediate none, .dead]
    }], cm, mem⟩
    let s5 : State := ⟨[{
      defId := 0, blockIdx := 5, stmtIdx := 0,
      locals :=
        [.immediate (some vret), .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate (some vr), .dead, .dead, .immediate none,
         .immediate none, .dead, .dead]
    }], cm, mem⟩
    ReachesV2 p0 s3 s5 := by
  intro p0 va vb vq vr vret s3 s5
  have hDivLt : a / b < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
  let l0 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .immediate none, .dead]
  let l1 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .dead]
  let l2 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .immediate none]
  let l3 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .immediate (some vq)]
  let l3a : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .immediate none]
  let l4 : List LocalSlot :=
    [.immediate (some vret), .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .immediate none]
  let l5 : List LocalSlot :=
    [.immediate (some vret), .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .dead]
  have h01 := evalStepV2_storageDead_body0 cm mem 3 0 12 l0 l1 _ _ rfl rfl rfl rfl rfl
  have h12 := evalStepV2_storageLive_body0 cm mem 3 1 13 l1 l2 _ (.int .isize false) rfl rfl rfl rfl rfl
  have h23 := evalStepV2_copy_isize_body0 cm mem 3 2 13 3 l2 l3 _ (a / b) hDivLt rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have h34 := evalStepV2_binop_move_const_body0 cm mem 3 3 0 13 .add true l3 l3a l4 _
    (.int .isize false) (a / b) 1 vret hDivLt (by decide) rfl rfl (.inr (.inr rfl))
    rfl rfl rfl rfl (evalBinOp_isize_add hDivLt (by decide) hAddLt)
    (checkValV2_isize_ofNat hAddLt) ⟨none, rfl⟩ rfl
  have h45 := evalStepV2_storageDead_body0 cm mem 3 4 13 l4 l5 _ _ rfl rfl rfl rfl rfl
  have hTerm := evalStepV2_goto_body0 cm mem 3 5 l5 _ rfl rfl rfl rfl
  exact ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step
    (ReachesV2_step (ReachesV2_step (.refl s3) h01) h12) h23) h34) h45) hTerm

private theorem safe_div_bb4_to_bb5 (a b : Nat) (ha : a < Nat.pow 2 64)
    (cm : CallerMemory) (mem : MemoryState) :
    let p0 := entryProgForBody Captured.program 0
    let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
    let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
    let vq : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
    let vr : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a % b)⟩
    let s4 : State := ⟨[{
      defId := 0, blockIdx := 4, stmtIdx := 0,
      locals :=
        [.immediate none, .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate (some vr), .dead, .dead, .immediate none,
         .immediate none, .immediate none, .dead]
    }], cm, mem⟩
    let s5 : State := ⟨[{
      defId := 0, blockIdx := 5, stmtIdx := 0,
      locals :=
        [.immediate (some vq), .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate (some vr), .dead, .dead, .immediate none,
         .immediate none, .dead, .dead]
    }], cm, mem⟩
    ReachesV2 p0 s4 s5 := by
  intro p0 va vb vq vr s4 s5
  have hDivLt : a / b < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
  let l0 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .immediate none, .dead]
  let l1 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .dead]
  let l2 : List LocalSlot :=
    [.immediate (some vq), .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .dead]
  have h01 := evalStepV2_storageDead_body0 cm mem 4 0 12 l0 l1 _ _ rfl rfl rfl rfl rfl
  have h12 := evalStepV2_copy_isize_body0 cm mem 4 1 0 3 l1 l2 _ (a / b) hDivLt
    rfl rfl rfl rfl rfl ⟨none, rfl⟩ rfl
  have hTerm := evalStepV2_goto_body0 cm mem 4 5 l2 _ rfl rfl rfl rfl
  exact ReachesV2_step (ReachesV2_step (ReachesV2_step (.refl s4) h01) h12) hTerm

private theorem safe_div_bb5_exec (a b ret : Nat) (cm : CallerMemory)
    (hValidCm : validCallerMemory cm = true) :
    let p0 := entryProgForBody Captured.program 0
    let mem0 := entryMemoryWithCaller cm
    let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
    let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
    let vq : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
    let vr : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a % b)⟩
    let vret : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 ret⟩
    let s5 : State := ⟨[{
      defId := 0, blockIdx := 5, stmtIdx := 0,
      locals :=
        [.immediate (some vret), .immediate (some va), .immediate (some vb),
         .immediate (some vq), .dead, .dead, .immediate none,
         .immediate (some vr), .dead, .dead, .immediate none,
         .immediate none, .dead, .dead]
    }], cm, mem0⟩
    execStateV2 p0 4 s5 (fun o => o = .returned ⟨vret, cm⟩) := by
  intro p0 mem0 va vb vq vr vret s5
  let l0 : List LocalSlot :=
    [.immediate (some vret), .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .immediate none, .dead, .dead]
  let l1 : List LocalSlot :=
    [.immediate (some vret), .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .immediate (some vr), .dead, .dead, .immediate none,
     .dead, .dead, .dead]
  let l2 : List LocalSlot :=
    [.immediate (some vret), .immediate (some va), .immediate (some vb),
     .immediate (some vq), .dead, .dead, .immediate none,
     .dead, .dead, .dead, .immediate none,
     .dead, .dead, .dead]
  let l3 : List LocalSlot :=
    [.immediate (some vret), .immediate (some va), .immediate (some vb),
     .dead, .dead, .dead, .immediate none,
     .dead, .dead, .dead, .immediate none,
     .dead, .dead, .dead]
  have h01 := evalStepV2_storageDead_body0 cm mem0 5 0 11 l0 l1 _ _ rfl rfl rfl rfl rfl
  have h12 := evalStepV2_storageDead_body0 cm mem0 5 1 7 l1 l2 _ _ rfl rfl rfl rfl rfl
  have h23 := evalStepV2_storageDead_body0 cm mem0 5 2 3 l2 l3 _ _ rfl rfl rfl rfl rfl
  have hRet := evalStepV2_return_isize_body0 cm 5 ret l3 _ rfl rfl rfl rfl rfl hValidCm rfl rfl
  exact execOutcomeStateV2_step h01
    (execOutcomeStateV2_step h12
      (execOutcomeStateV2_step h23
        (execOutcomeStateV2_done hRet rfl)))

private theorem body0_nonzero_satisfies (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (sa sb : ScalarVal)
    (hArgs : q.args = [.scalar sa, .scalar sb])
    (hW1 : sa.width = .isize) (hS1 : sa.signed = false) (hWf1 : sa.wf = true)
    (hW2 : sb.width = .isize) (hS2 : sb.signed = false) (hWf2 : sb.wf = true)
    (hbPos : 0 < sb.bits.toNat)
    (contract : SafeContractV2)
    (hRetOk : contract.post q (.returned
      ⟨.scalar ⟨.isize, false, BitVec.ofNat 128 (Spec.divCeilExpect sa.bits.toNat sb.bits.toNat)⟩,
        q.callerMem⟩)) :
    SatisfiesPostV2 (entryProgForBody Captured.program 0) q (contract.post q) := by
  let a := sa.bits.toNat
  let b := sb.bits.toNat
  have ha : a < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW1 hWf1
  have hb : b < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW2 hWf2
  have hsaEq : sa = ⟨.isize, false, BitVec.ofNat 128 a⟩ := scalar_eq_of_fields hW1 hS1 ha
  have hsbEq : sb = ⟨.isize, false, BitVec.ofNat 128 b⟩ := scalar_eq_of_fields hW2 hS2 hb
  have hQEq : q = {
      args := [.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩,
        .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩],
      callerMem := q.callerMem } := by
    cases q with
    | mk args0 cm0 =>
      dsimp only at hArgs ⊢
      subst hArgs
      rw [← hsaEq, ← hsbEq]
  have hValid' : ValidEntryArgsV2 Captured.body_0 {
      args := [.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩,
        .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩],
      callerMem := q.callerMem } := by
    rw [← hQEq]; exact hValid
  let cm := q.callerMem
  have hValidCm : validCallerMemory cm = true := hValid.1
  let p0 := entryProgForBody Captured.program 0
  let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
  let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
  let vq : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
  let vr : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (a % b)⟩
  let vret : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 (Spec.divCeilExpect a b)⟩
  let mem0 := entryMemoryWithCaller cm
  let s0 : State := ⟨[{
    defId := 0, blockIdx := 0, stmtIdx := 0,
    locals := initLocalsLoop Captured.body_0 [va, vb] 0 Captured.body_0.locals
  }], cm, mem0⟩
  let l6 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some (.bool (Nat.beq b 0))),
     .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let s6 : State := ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 6, locals := l6 }], cm, mem0⟩
  let s1 : State := ⟨[{
    defId := 0, blockIdx := 1, stmtIdx := 0,
    locals :=
      [.immediate none, .immediate (some va), .immediate (some vb),
       .immediate none, .immediate (some va), .immediate (some vb),
       .immediate none, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  }], cm, mem0⟩
  let s2 : State := ⟨[{
    defId := 0, blockIdx := 2, stmtIdx := 0,
    locals :=
      [.immediate none, .immediate (some va), .immediate (some vb),
       .immediate (some vq), .dead, .dead, .immediate none,
       .immediate none, .immediate (some va), .immediate (some vb),
       .immediate none, .dead, .dead, .dead]
  }], cm, mem0⟩
  let s5 : State := ⟨[{
    defId := 0, blockIdx := 5, stmtIdx := 0,
    locals :=
      [.immediate (some vret), .immediate (some va), .immediate (some vb),
       .immediate (some vq), .dead, .dead, .immediate none,
       .immediate (some vr), .dead, .dead, .immediate none,
       .immediate none, .dead, .dead]
  }], cm, mem0⟩
  have hBb0 := safe_div_bb0_steps a b ha hb cm
  have hbNz : Nat.beq b 0 = false := by
    cases hE : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (Nat.ne_of_gt hbPos (Nat.eq_of_beq_eq_true hE))
  have hTerm0 := evalStepV2_assert_abort_body0 cm mem0 0 6 1 .divByZero false (Nat.beq b 0) l6 _
    _ rfl rfl rfl rfl (.inl rfl) rfl rfl rfl
  rw [hbNz] at hTerm0
  have hTo1 : ReachesV2 p0 s0 s1 := ReachesV2_step hBb0 hTerm0
  have hTo2 : ReachesV2 p0 s0 s2 := reachesV2_trans hTo1 (safe_div_bb1_to_bb2 a b ha hb hbPos cm mem0)
  have hToBranch := reachesV2_trans hTo2 (safe_div_bb2_branch a b ha hb hbPos cm mem0)
  have hTo5 : ReachesV2 p0 s0 s5 := by
    cases hModZ : Nat.beq (a % b) 0 with
    | true =>
      rw [hModZ] at hToBranch
      have hVretEq : vret = vq := by
        dsimp only [vret, vq]
        rw [divCeilExpect_eq a b, hModZ]
        rfl
      dsimp only [s5]
      rw [hVretEq]
      exact reachesV2_trans hToBranch (safe_div_bb4_to_bb5 a b ha cm mem0)
    | false =>
      rw [hModZ] at hToBranch
      have hRemNe : a % b ≠ 0 := fun h => by rw [h] at hModZ; cases hModZ
      have hAddLt := div_add_one_lt_pow64 ha hbPos hRemNe
      have hVretEq : vret = .scalar ⟨.isize, false, BitVec.ofNat 128 (a / b + 1)⟩ := by
        dsimp only [vret]
        rw [divCeilExpect_eq a b, hModZ]
        rfl
      dsimp only [s5]
      rw [hVretEq]
      exact reachesV2_trans hToBranch (safe_div_bb3_to_bb5 a b ha hAddLt cm mem0)
  have hExec5 := safe_div_bb5_exec a b (Spec.divCeilExpect a b) cm hValidCm
  let ⟨fuel, hExecS0⟩ := execOutcomeStateV2_of_reaches_post hTo5 hExec5
  have hInit0 := initStateV2_body0_ok
    { args := [.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩,
        .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩],
      callerMem := cm } hValid'
  have hExecProg : execProgV2 p0 fuel q (fun o => o = .returned ⟨vret, cm⟩) := by
    rw [hQEq]
    unfold execProgV2
    rw [hInit0]
    exact hExecS0
  have hRes := spec_and_behaviorV2_of_exec_eq hExecProg
  exact hRes.2.2.2 (contract.post q) hRetOk

private theorem body0_zero_aborts (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (sa sb : ScalarVal)
    (hArgs : q.args = [.scalar sa, .scalar sb])
    (hW1 : sa.width = .isize) (hS1 : sa.signed = false) (hWf1 : sa.wf = true)
    (hW2 : sb.width = .isize) (hS2 : sb.signed = false) (hWf2 : sb.wf = true)
    (hbZero : sb.bits.toNat = 0) :
    SatisfiesPostV2 (entryProgForBody Captured.program 0) q (Spec.divCeilAllowAbort.post q) := by
  let a := sa.bits.toNat
  let b := sb.bits.toNat
  have ha : a < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW1 hWf1
  have hb : b < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW2 hWf2
  have hsaEq : sa = ⟨.isize, false, BitVec.ofNat 128 a⟩ := scalar_eq_of_fields hW1 hS1 ha
  have hsbEq : sb = ⟨.isize, false, BitVec.ofNat 128 b⟩ := scalar_eq_of_fields hW2 hS2 hb
  have hQEq : q = {
      args := [.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩,
        .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩],
      callerMem := q.callerMem } := by
    cases q with
    | mk args0 cm0 =>
      dsimp only at hArgs ⊢
      subst hArgs
      rw [← hsaEq, ← hsbEq]
  have hValid' : ValidEntryArgsV2 Captured.body_0 {
      args := [.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩,
        .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩],
      callerMem := q.callerMem } := by
    rw [← hQEq]; exact hValid
  let cm := q.callerMem
  let p0 := entryProgForBody Captured.program 0
  let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
  let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
  let mem0 := entryMemoryWithCaller cm
  let s0 : State := ⟨[{
    defId := 0, blockIdx := 0, stmtIdx := 0,
    locals := initLocalsLoop Captured.body_0 [va, vb] 0 Captured.body_0.locals
  }], cm, mem0⟩
  let l6 : List LocalSlot :=
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some (.bool (Nat.beq b 0))),
     .dead, .dead, .dead, .immediate none, .dead, .dead, .dead]
  let s6 : State := ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 6, locals := l6 }], cm, mem0⟩
  have hBb0 := safe_div_bb0_steps a b ha hb cm
  have hbZ : Nat.beq b 0 = true := by
    change Nat.beq sb.bits.toNat 0 = true
    rw [hbZero]
    rfl
  have hTerm0 := evalStepV2_assert_abort_body0 cm mem0 0 6 1 .divByZero false (Nat.beq b 0) l6 _
    _ rfl rfl rfl rfl (.inl rfl) rfl rfl rfl
  rw [hbZ] at hTerm0
  dsimp only at hTerm0
  rw [extractCallerMemory_entry cm hValid.1] at hTerm0
  have hDone6 : evalStepV2 p0 s6 = .done (.aborted cm) := hTerm0
  let ⟨fuel, hExecS0⟩ :=
    execOutcomeStateV2_of_reaches_post hBb0
      (execOutcomeStateV2_done (onDone := fun o => o = .aborted cm)
        (onFault := fun _ => False) (fuel := 0) hDone6 rfl)
  have hInit0 := initStateV2_body0_ok
    { args := [.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩,
        .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩],
      callerMem := cm } hValid'
  have hExecProg : execProgV2 p0 fuel q (fun o => o = .aborted cm) := by
    rw [hQEq]
    unfold execProgV2
    rw [hInit0]
    exact hExecS0
  have hRes := spec_and_behaviorV2_of_exec_eq hExecProg
  refine hRes.2.2.2 (Spec.divCeilAllowAbort.post q) ?_
  unfold SafeContractV2.post Spec.divCeilAllowAbort
  dsimp only
  rw [hArgs]
  exact ⟨rfl, hbZero, rfl⟩

private theorem body0_postReturn_ok (q : Query)
    (sa sb : ScalarVal) (hArgs : q.args = [.scalar sa, .scalar sb])
    (ha : sa.bits.toNat < Nat.pow 2 64) (hbPos : 0 < sb.bits.toNat) :
    Spec.divCeilPostReturn q
      ⟨.scalar ⟨.isize, false,
          BitVec.ofNat 128 (Spec.divCeilExpect sa.bits.toNat sb.bits.toNat)⟩,
        q.callerMem⟩ := by
  unfold Spec.divCeilPostReturn
  rw [hArgs]
  refine ⟨rfl, rfl, ?_, rfl⟩
  rw [divCeilExpect_eq]
  cases hMod : Nat.beq (sa.bits.toNat % sb.bits.toNat) 0 with
  | true =>
    have hLt : sa.bits.toNat / sb.bits.toNat < Nat.pow 2 128 :=
      Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha) (by decide)
    exact toNat_bvOfNat_128 hLt
  | false =>
    have hRemNe : sa.bits.toNat % sb.bits.toNat ≠ 0 := fun h => by
      rw [h] at hMod; cases hMod
    have hLt : sa.bits.toNat / sb.bits.toNat + 1 < Nat.pow 2 128 :=
      Nat.lt_trans (div_add_one_lt_pow64 ha hbPos hRemNe) (by decide)
    exact toNat_bvOfNat_128 hLt

private theorem body0_static_admitted :
    BodyStaticAdmittedV2 Captured.program Captured.body_0 = true := by
  decide

private theorem body0_allowAbort_contract :
    BodySatisfiesSafeContractV2 Captured.program 0 Captured.body_0
      Spec.divCeilAllowAbort := by
  refine ⟨rfl, body0_static_admitted, fun q hValid _ => ?_⟩
  have hMatch : checkArgsMatchV2 q.args [.int .isize false, .int .isize false] = true :=
    hValid.2.1
  let ⟨sa, sb, hArgs, hW1, hS1, hWf1, hW2, hS2, hWf2⟩ := checkArgsMatchV2_two_isize hMatch
  cases hBZ : Nat.beq sb.bits.toNat 0 with
  | true =>
    exact body0_zero_aborts q hValid sa sb hArgs hW1 hS1 hWf1 hW2 hS2 hWf2
      (Nat.eq_of_beq_eq_true hBZ)
  | false =>
    have hbPos : 0 < sb.bits.toNat :=
      Nat.pos_of_ne_zero (fun h => by rw [h] at hBZ; cases hBZ)
    have ha : sa.bits.toNat < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW1 hWf1
    exact body0_nonzero_satisfies q hValid sa sb hArgs hW1 hS1 hWf1 hW2 hS2 hWf2 hbPos
      Spec.divCeilAllowAbort (body0_postReturn_ok q sa sb hArgs ha hbPos)

private theorem body0_noAbort_contract :
    BodySatisfiesSafeContractV2 Captured.program 0 Captured.body_0
      Spec.divCeilNoAbort := by
  refine ⟨rfl, body0_static_admitted, fun q hValid hPre => ?_⟩
  have hMatch : checkArgsMatchV2 q.args [.int .isize false, .int .isize false] = true :=
    hValid.2.1
  let ⟨sa, sb, hArgs, hW1, hS1, hWf1, hW2, hS2, hWf2⟩ := checkArgsMatchV2_two_isize hMatch
  unfold Spec.divCeilNoAbort at hPre
  dsimp only at hPre
  rw [hArgs] at hPre
  have hbPos : 0 < sb.bits.toNat := Nat.pos_of_ne_zero hPre
  have ha : sa.bits.toNat < Nat.pow 2 64 := truncateBits_isize_toNat_lt hW1 hWf1
  exact body0_nonzero_satisfies q hValid sa sb hArgs hW1 hS1 hWf1 hW2 hS2 hWf2 hbPos
    Spec.divCeilNoAbort (body0_postReturn_ok q sa sb hArgs ha hbPos)

private theorem body1_static_admitted :
    BodyStaticAdmittedV2 Captured.program Captured.body_1 = true := by
  decide

private theorem bool_of_or_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem eq_true_of_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

private theorem mut_eq_mut_of_beq {m : Mutability} (h : Mutability.beq m .mut = true) :
    m = .mut := by
  cases m <;> first | rfl | cases h

private theorem evalStepV2_mk_body1 (frame : FrameState) (cm : CallerMemory)
    (mem : MemoryState) (bb : BasicBlock) (stmt : StatementKind)
    (hDef : frame.defId = 1)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_1.basicBlocks frame.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = some stmt)
    (_hLe : Nat.beq frame.stmtIdx bb.statements.length = false) :
    evalStepV2 (entryProgForBody Captured.program 1) ⟨[frame], cm, mem⟩ =
      evalStatementV2 Captured.body_1 frame mem cm stmt := by
  unfold evalStepV2
  dsimp only
  rw [hDef]
  dsimp only [entryProgForBody, Captured.program]
  change (match Trusted.MirSemantics.getElem? Captured.body_1.basicBlocks frame.blockIdx with
    | none => StepResult.fault .unsupported
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some stmt => evalStatementV2 Captured.body_1 frame mem cm stmt
      | none =>
        if Nat.beq frame.stmtIdx bb.statements.length then
          evalTerminatorV2 Captured.body_1 bb frame mem cm
            Captured.program.panicStrategy Captured.program.hasLocalPanicHandler
        else StepResult.fault .unsupported) = _
  rw [hBb]
  dsimp only
  rw [hStmt]

private theorem evalStepV2_term_body1 (frame : FrameState) (cm : CallerMemory)
    (mem : MemoryState) (bb : BasicBlock)
    (hDef : frame.defId = 1)
    (hBb : Trusted.MirSemantics.getElem? Captured.body_1.basicBlocks frame.blockIdx = some bb)
    (hEnd : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (hLen : Nat.beq frame.stmtIdx bb.statements.length = true) :
    evalStepV2 (entryProgForBody Captured.program 1) ⟨[frame], cm, mem⟩ =
      evalTerminatorV2 Captured.body_1 bb frame mem cm
        Captured.program.panicStrategy Captured.program.hasLocalPanicHandler := by
  unfold evalStepV2
  dsimp only
  rw [hDef]
  dsimp only [entryProgForBody, Captured.program]
  change (match Trusted.MirSemantics.getElem? Captured.body_1.basicBlocks frame.blockIdx with
    | none => StepResult.fault .unsupported
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some stmt => evalStatementV2 Captured.body_1 frame mem cm stmt
      | none =>
        if Nat.beq frame.stmtIdx bb.statements.length then
          evalTerminatorV2 Captured.body_1 bb frame mem cm
            Captured.program.panicStrategy Captured.program.hasLocalPanicHandler
        else StepResult.fault .unsupported) = _
  rw [hBb]
  dsimp only
  rw [hEnd]
  dsimp only
  rw [ite_bool_true hLen]
  rfl

private theorem checkValV2_ptr_mut_isize {v : Val}
    (h : checkValV2 v (.ref .mut (.int .isize false)) = true) :
    ∃ pv : PtrVal, v = .ptr pv ∧ checkValV2 (.ptr pv) (.ref .mut (.int .isize false)) = true := by
  cases v with
  | ptr pv => exact ⟨pv, rfl, h⟩
  | optionVal o => cases o <;> cases h
  | scalar _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _
  | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _
  | array _ | vec _ _ _ => cases h
  | boxPtr _ o => cases o <;> cases h

private theorem checkArgsMatchV2_body1 {args : List Val}
    (h : checkArgsMatchV2 args [.ref .mut (.int .isize false), .int .isize false, .int .isize false] = true) :
    ∃ (pv : PtrVal) (sa sb : ScalarVal),
      args = [.ptr pv, .scalar sa, .scalar sb] ∧
      checkValV2 (.ptr pv) (.ref .mut (.int .isize false)) = true ∧
      sa.width = .isize ∧ sa.signed = false ∧ sa.wf = true ∧
      sb.width = .isize ∧ sb.signed = false ∧ sb.wf = true := by
  cases args with
  | nil => cases h
  | cons v0 r0 =>
    dsimp only [checkArgsMatchV2] at h
    cases r0 with
    | nil =>
      cases h0 : checkValV2 v0 (.ref .mut (.int .isize false)) <;>
        rw [h0] at h <;> cases h
    | cons v1 r1 =>
      dsimp only [checkArgsMatchV2] at h
      cases r1 with
      | nil =>
        cases h0 : checkValV2 v0 (.ref .mut (.int .isize false)) <;>
          cases h1 : checkValV2 v1 (.int .isize false) <;>
          rw [h0, h1] at h <;> cases h
      | cons v2 r2 =>
        dsimp only [checkArgsMatchV2] at h
        cases r2 with
        | cons _ _ =>
          cases h0 : checkValV2 v0 (.ref .mut (.int .isize false)) <;>
            cases h1 : checkValV2 v1 (.int .isize false) <;>
            cases h2 : checkValV2 v2 (.int .isize false) <;>
            rw [h0, h1, h2] at h <;> cases h
        | nil =>
          have h012 : checkValV2 v0 (.ref .mut (.int .isize false)) = true ∧
              checkValV2 v1 (.int .isize false) = true ∧
              checkValV2 v2 (.int .isize false) = true := by
            cases h0 : checkValV2 v0 (.ref .mut (.int .isize false)) <;>
              cases h1 : checkValV2 v1 (.int .isize false) <;>
              cases h2 : checkValV2 v2 (.int .isize false) <;>
              rw [h0, h1, h2] at h <;> first | exact ⟨rfl, rfl, rfl⟩ | cases h
          let ⟨pv, hpv, hWfP⟩ := checkValV2_ptr_mut_isize h012.1
          let ⟨sa, hsa, hWA, hSA, hWfA⟩ := checkValV2_isize_scalar h012.2.1
          let ⟨sb, hsb, hWB, hSB, hWfB⟩ := checkValV2_isize_scalar h012.2.2
          subst hpv; subst hsa; subst hsb
          exact ⟨pv, sa, sb, rfl, hWfP, hWA, hSA, hWfA, hWB, hSB, hWfB⟩

private theorem ref_mut_isize_store_ok (cm : CallerMemory) (pv : PtrVal) (a : Nat)
    (ha : a < Nat.pow 2 64)
    (hRef : refValidInMem (entryMemoryWithCaller cm) .mut (.int .isize false) (.ptr pv) = .ok ()) :
    ∃ (aid : AllocId) (alloc : Allocation) (mem' : MemoryState),
      pv.allocId = some aid ∧
      findAllocation aid cm.allocations = some alloc ∧
      alloc.live = true ∧
      alloc.mutability = .mut ∧
      storeIndirectV2 (entryMemoryWithCaller cm) (.int .isize false)
        ⟨aid, pv.offsetBytes.toNat⟩ (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩) = .ok mem' := by
  unfold refValidInMem at hRef
  dsimp only at hRef
  rw [ite_bool_false (b := !isSupportedV2PointeeTy (.int .isize false) &&
      !isHeapHandleTyV2 (.int .isize false)) rfl,
    show layoutOfTyV2 (.int .isize false) = some ⟨8, 3⟩ from rfl] at hRef
  dsimp only at hRef
  cases hAid : pv.allocId with
  | none =>
    rw [hAid] at hRef
    dsimp only at hRef
    have hOr : (Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 8) = true := by
      cases Nat.beq pv.offsetBytes.toNat 0 <;> rfl
    rw [ite_bool_true hOr] at hRef
    cases hRef
  | some aid =>
    rw [hAid] at hRef
    dsimp only at hRef
    change (match findAllocation aid cm.allocations with
      | none => Except.error FaultKind.undefined
      | some alloc =>
        if !alloc.live || !isInBounds alloc pv.offsetBytes.toNat 8 ||
            !isAligned alloc pv.offsetBytes.toNat 3 then
          Except.error FaultKind.undefined
        else if Mutability.beq .mut .mut && !Mutability.beq alloc.mutability .mut then
          Except.error FaultKind.undefined
        else
          let sliceBytes := (alloc.bytes.drop pv.offsetBytes.toNat).take 8
          match decodeValV2 profileV2TargetEndian (.int .isize false) sliceBytes with
          | Except.ok (some _) => Except.ok ()
          | Except.ok none => Except.error FaultKind.undefined
          | Except.error k => Except.error k) = Except.ok () at hRef
    cases hFind : findAllocation aid cm.allocations with
    | none => rw [hFind] at hRef; cases hRef
    | some alloc =>
      rw [hFind] at hRef
      dsimp only at hRef
      cases hBad1 : (!alloc.live || !isInBounds alloc pv.offsetBytes.toNat 8 ||
          !isAligned alloc pv.offsetBytes.toNat 3) with
      | true => rw [ite_bool_true hBad1] at hRef; cases hRef
      | false =>
        rw [ite_bool_false hBad1] at hRef
        have hBad1' := bool_of_or_false hBad1
        have hBad0' := bool_of_or_false hBad1'.1
        have hLive : alloc.live = true := eq_true_of_not_eq_false hBad0'.1
        have hBounds : isInBounds alloc pv.offsetBytes.toNat 8 = true :=
          eq_true_of_not_eq_false hBad0'.2
        have hAlign : isAligned alloc pv.offsetBytes.toNat 3 = true :=
          eq_true_of_not_eq_false hBad1'.2
        cases hBad2 : (Mutability.beq .mut .mut && !Mutability.beq alloc.mutability .mut) with
        | true => rw [ite_bool_true hBad2] at hRef; cases hRef
        | false =>
          have hMutBeq : Mutability.beq alloc.mutability .mut = true := by
            cases hM : Mutability.beq alloc.mutability .mut with
            | true => rfl
            | false =>
              have : (Mutability.beq .mut .mut && !Mutability.beq alloc.mutability .mut) = true := by
                rw [hM]; rfl
              rw [this] at hBad2
              cases hBad2
          have hMut : alloc.mutability = .mut := mut_eq_mut_of_beq hMutBeq
          have hEnc : encodeValV2 profileV2TargetEndian (.int .isize false)
              (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩) =
              .ok ((encodeUInt profileV2TargetEndian 8 a).map (fun b => AllocByte.init b none)) := by
            delta encodeValV2
            dsimp only
            try (delta encodeValV2._f; dsimp only)
            have hCv := checkValV2_isize_ofNat ha
            rw [ite_bool_false (by rw [hCv]; rfl)]
            unfold encodeVal
            rw [ite_bool_false (by have hV1 : checkVal (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩) (.int .isize false) = true := hCv; rw [hV1]; rfl)]
            dsimp only
            rw [toNat_bvOfNat_128 (Nat.lt_trans ha (by decide))]
            rfl
          refine ⟨aid, alloc, ({
              (entryMemoryWithCaller cm) with
              allocations := replaceAllocation
                { alloc with
                  bytes := alloc.bytes.take pv.offsetBytes.toNat ++
                    ((encodeUInt profileV2TargetEndian 8 a).map (fun b => AllocByte.init b none)) ++
                    alloc.bytes.drop (pv.offsetBytes.toNat + 8) }
                cm.allocations
            } : MemoryState), rfl, hFind, hLive, hMut, ?_⟩
          · unfold storeIndirectV2
            rw [show layoutOfTyV2 (.int .isize false) = some ⟨8, 3⟩ from rfl]
            dsimp only
            rw [hEnc]
            dsimp only
            have hLen8 : ((encodeUInt profileV2TargetEndian 8 a).map (fun b => AllocByte.init b none)).length = 8 := by
              change (encodeUInt TargetEndian.little 8 a).length = 8
              rfl
            unfold writeBytes
            rw [hLen8]
            dsimp only [entryMemoryWithCaller]
            rw [hFind]
            dsimp only
            rw [ite_bool_false (b := Nat.beq 8 0) rfl]
            rw [ite_bool_false (by rw [hLive, hBounds, hAlign]; rfl)]
            rw [hMut]

private theorem initStateV2_body1_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    initStateV2 (entryProgForBody Captured.program 1) q =
      .ok ⟨[{
          defId := 1, blockIdx := 0, stmtIdx := 0,
          locals := initLocalsLoop Captured.body_1 q.args 0 Captured.body_1.locals
        }], q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  let ⟨hMem, hArgs, hRefs, hDisj⟩ := hValid
  unfold initStateV2 entryProgForBody Captured.program Trusted.MirSemantics.getElem?
  dsimp only
  have hHdr1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
  have hHdr2 : (!(true : Bool)) = false := rfl
  have hB1 : Captured.body_1.basicBlocks.isEmpty = false := rfl
  have hB2 : (!Nat.blt Captured.body_1.argumentCount Captured.body_1.locals.length) = false := rfl
  have hB3 : (!storageAnnotationsInBounds Captured.body_1) = false := by decide
  have hB4 : (!discriminantTypesValidV2 Captured.body_1) = false := by decide
  have hB5 : (!castTypesValid Captured.body_1) = false := by decide
  have hB6 : (!assertConditionTypesValid Captured.body_1) = false := by decide
  have hB7 : (!Captured.body_1.locals.all isSupportedV2LocalTy) = false := by decide
  rw [ite_bool_false hHdr1, hMem, ite_bool_false hHdr2]
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [ite_bool_false hB1, ite_bool_false hB2, ite_bool_false hB3,
    ite_bool_false hB4, ite_bool_false hB5, ite_bool_false hB6,
    ite_bool_false hB7]
  rw [hArgs, ite_bool_false hHdr2]
  rw [show entryMemoryForArgsV2 q.callerMem
      (List.take Captured.body_1.argumentCount (List.drop 1 Captured.body_1.locals))
      q.args = entryMemoryWithCaller q.callerMem from rfl]
  have hF1 : ((!true || !true) = false) := rfl
  have hR1 : (!refsValidInMemList (entryMemoryWithCaller q.callerMem)
      (List.take Captured.body_1.argumentCount (List.drop 1 Captured.body_1.locals)) q.args ||
      !spansPairwiseDisjoint
        (refAccessSpansList
          (List.take Captured.body_1.argumentCount (List.drop 1 Captured.body_1.locals))
          q.args)) = false := by
    rw [hRefs, hDisj]
    exact hF1
  rw [hR1]
  rfl

private theorem body1_satisfies (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q)
    (contract : SafeContractV2)
    (hCheck : ∀ (pv : PtrVal) (sa sb : ScalarVal) (aid : AllocId) (mem' : MemoryState),
      q.args = [.ptr pv, .scalar sa, .scalar sb] →
      pv.allocId = some aid →
      sa.bits.toNat < Nat.pow 2 64 →
      sb.bits.toNat < Nat.pow 2 64 →
      storeIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .isize false)
        ⟨aid, pv.offsetBytes.toNat⟩ (.scalar ⟨.isize, false, BitVec.ofNat 128 sa.bits.toNat⟩) = .ok mem' →
      if sb.bits.toNat = 0 then
        contract.post q (.aborted (extractCallerMemory q.callerMem mem'))
      else
        contract.post q (.returned ⟨.scalar ⟨.isize, false,
          BitVec.ofNat 128 (sa.bits.toNat / sb.bits.toNat)⟩, extractCallerMemory q.callerMem mem'⟩)) :
    SatisfiesSafeContractV2 (entryProgForBody Captured.program 1) q contract := by
  intro _
  let ⟨pv, sa, sb, hArgs, hWfP, hWA, hSA, hWfA, hWB, hSB, hWfB⟩ :=
    checkArgsMatchV2_body1 hValid.2.1
  let a := sa.bits.toNat
  let b := sb.bits.toNat
  have ha : a < Nat.pow 2 64 := truncateBits_isize_toNat_lt hWA hWfA
  have hb : b < Nat.pow 2 64 := truncateBits_isize_toNat_lt hWB hWfB
  have hsaEq : sa = ⟨.isize, false, BitVec.ofNat 128 a⟩ := scalar_eq_of_fields hWA hSA ha
  have hsbEq : sb = ⟨.isize, false, BitVec.ofNat 128 b⟩ := scalar_eq_of_fields hWB hSB hb
  have hRef : refValidInMem (entryMemoryWithCaller q.callerMem) .mut (.int .isize false)
      (.ptr pv) = .ok () := by
    have hRL := hValid.2.2.1
    rw [hArgs] at hRL
    dsimp only [Captured.body_1, List.drop, List.take, refsValidInMemList, refsValidInMem] at hRL
    cases hR : refValidInMem (entryMemoryWithCaller q.callerMem) .mut (.int .isize false) (.ptr pv) with
    | ok _ => rfl
    | error _ => rw [hR] at hRL; cases hRL
  let ⟨aid, alloc, mem', hAid, hFind, hLive, hMut, hStore⟩ :=
    ref_mut_isize_store_ok q.callerMem pv a ha hRef
  have hInit := initStateV2_body1_ok q hValid
  rw [hArgs, hsaEq, hsbEq] at hInit
  let cm := q.callerMem
  let mem0 := entryMemoryWithCaller cm
  let p1 := entryProgForBody Captured.program 1
  let vp : Val := .ptr pv
  let va : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 a⟩
  let vb : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 b⟩
  have hWfA' := checkValV2_isize_ofNat ha
  have hWfB' := checkValV2_isize_ofNat hb
  let l0 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .dead, .dead, .immediate none]
  let l1 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .immediate none, .dead, .dead, .immediate none]
  let l2 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .immediate (some va), .dead, .dead, .immediate none]
  let l3 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .immediate none, .dead, .dead, .immediate none]
  let l4 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .dead, .dead, .immediate none]
  let l5 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .immediate none, .dead, .immediate none]
  let l6 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .immediate (some va), .dead, .immediate none]
  let l7 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .immediate (some va), .immediate none, .immediate none]
  let l8 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .immediate (some va), .immediate (some vb), .immediate none]
  let l9 : List LocalSlot :=
    [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
     .dead, .immediate (some va), .immediate (some vb), .immediate (some (.bool (Nat.beq b 0)))]
  have hInitLoc : initLocalsLoop Captured.body_1 [vp, va, vb] 0 Captured.body_1.locals = l0 := rfl
  rw [hInitLoc] at hInit
  have h01 : evalStepV2 p1 ⟨[⟨1, 0, 0, l0, none, none, none⟩], cm, mem0⟩ =
      .step ⟨[⟨1, 0, 1, l1, none, none, none⟩], cm, mem0⟩ := rfl
  have h12 : evalStepV2 p1 ⟨[⟨1, 0, 1, l1, none, none, none⟩], cm, mem0⟩ =
      .step ⟨[⟨1, 0, 2, l2, none, none, none⟩], cm, mem0⟩ := by
    rw [evalStepV2_mk_body1 _ cm mem0 _ _ rfl rfl rfl rfl]
    unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2 evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_1, l1, Trusted.MirSemantics.getElem?]
    rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false),
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [ite_bool_false (rfl : (!MirTy.beq (.int .isize false) (.int .isize false)) = false)]
    dsimp only
    unfold writePlaceDestV2
    rw [ite_bool_false (by rw [hWfA']; rfl)]
    rfl
  have hWp2 : writePlaceDestV2 l3 mem0
      (.deref (.int .isize false) ⟨8, 3⟩ pv) (.int .isize false) va =
      .ok (l3, mem') := by
    unfold writePlaceDestV2
    rw [ite_bool_false (by rw [hWfA']; rfl)]
    change (match pv.allocId with
      | none => _
      | some aid =>
        match findAllocation aid mem0.allocations with
        | none => Except.error FaultKind.undefined
        | some alloc =>
          if !alloc.live || !Mutability.beq alloc.mutability .mut then
            Except.error FaultKind.undefined
          else
            match storeIndirectV2 mem0 (.int .isize false) ⟨aid, pv.offsetBytes.toNat⟩ va with
            | Except.ok m' => Except.ok (l3, m')
            | Except.error k => Except.error k) = _
    rw [hAid]
    dsimp only [mem0, entryMemoryWithCaller]
    rw [hFind]
    dsimp only
    rw [ite_bool_false (by rw [hLive, hMut]; rfl)]
    change (match storeIndirectV2 (entryMemoryWithCaller cm) (.int .isize false)
        ⟨aid, pv.offsetBytes.toNat⟩ va with
      | Except.ok m' => Except.ok (l3, m')
      | Except.error k => Except.error k) = _
    rw [hStore]
  have h23 : evalStepV2 p1 ⟨[⟨1, 0, 2, l2, none, none, none⟩], cm, mem0⟩ =
      .step ⟨[⟨1, 0, 3, l3, none, none, none⟩], cm, mem'⟩ := by
    have hDest : resolvePlaceDestV2 Captured.body_1.locals l2 mem0 ⟨1, [.deref]⟩
        (.int .isize false) = .ok (.deref (.int .isize false) ⟨8, 3⟩ pv) := rfl
    rw [evalStepV2_mk_body1 _ cm mem0 _ _ rfl rfl rfl rfl]
    unfold evalStatementV2 placeStaticTyV2
    dsimp only
    rw [show Trusted.MirSemantics.getElem? Captured.body_1.locals 1 =
          some (.ref .mut (.int .isize false)) from rfl]
    dsimp only
    rw [show isUnsizedTy (.int .isize false) = false from rfl,
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [hDest]
    dsimp only
    unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_1, l2, Trusted.MirSemantics.getElem?, liveUninitSlot]
    rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false),
      ite_prop_true rfl, show setElem? l2 4 (.immediate none) = some l3 from rfl]
    dsimp only
    rw [ite_bool_false (rfl : (!MirTy.beq (.int .isize false) (.int .isize false)) = false)]
    dsimp only
    rw [hWp2]
    rfl
  have h34 : evalStepV2 p1 ⟨[⟨1, 0, 3, l3, none, none, none⟩], cm, mem'⟩ =
      .step ⟨[⟨1, 0, 4, l4, none, none, none⟩], cm, mem'⟩ := rfl
  have h45 : evalStepV2 p1 ⟨[⟨1, 0, 4, l4, none, none, none⟩], cm, mem'⟩ =
      .step ⟨[⟨1, 0, 5, l5, none, none, none⟩], cm, mem'⟩ := rfl
  have h56 : evalStepV2 p1 ⟨[⟨1, 0, 5, l5, none, none, none⟩], cm, mem'⟩ =
      .step ⟨[⟨1, 0, 6, l6, none, none, none⟩], cm, mem'⟩ := by
    rw [evalStepV2_mk_body1 _ cm mem' _ _ rfl rfl rfl rfl]
    unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2 evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_1, l5, Trusted.MirSemantics.getElem?]
    rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false),
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [ite_bool_false (rfl : (!MirTy.beq (.int .isize false) (.int .isize false)) = false)]
    dsimp only
    unfold writePlaceDestV2
    rw [ite_bool_false (by rw [hWfA']; rfl)]
    rfl
  have h67 : evalStepV2 p1 ⟨[⟨1, 0, 6, l6, none, none, none⟩], cm, mem'⟩ =
      .step ⟨[⟨1, 0, 7, l7, none, none, none⟩], cm, mem'⟩ := rfl
  have h78 : evalStepV2 p1 ⟨[⟨1, 0, 7, l7, none, none, none⟩], cm, mem'⟩ =
      .step ⟨[⟨1, 0, 8, l8, none, none, none⟩], cm, mem'⟩ := by
    rw [evalStepV2_mk_body1 _ cm mem' _ _ rfl rfl rfl rfl]
    unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2 evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_1, l7, Trusted.MirSemantics.getElem?]
    rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false),
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [ite_bool_false (rfl : (!MirTy.beq (.int .isize false) (.int .isize false)) = false)]
    dsimp only
    unfold writePlaceDestV2
    rw [ite_bool_false (by rw [hWfB']; rfl)]
    rfl
  have h89 : evalStepV2 p1 ⟨[⟨1, 0, 8, l8, none, none, none⟩], cm, mem'⟩ =
      .step ⟨[⟨1, 0, 9, l9, none, none, none⟩], cm, mem'⟩ := by
    rw [evalStepV2_mk_body1 _ cm mem' _ _ rfl rfl rfl rfl]
    unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2 evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_1, l8, Trusted.MirSemantics.getElem?, setElem?]
    rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false),
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
    rw [evalConstLit_isize 0 (by decide)]
    dsimp only
    rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
    dsimp only
    rw [evalBinOp_isize_eq hb (by decide)]
    dsimp only
    unfold writePlaceDestV2
    rfl
  have hToTerm : ReachesV2 p1 ⟨[⟨1, 0, 0, l0, none, none, none⟩], cm, mem0⟩
      ⟨[⟨1, 0, 9, l9, none, none, none⟩], cm, mem'⟩ :=
    ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step
      (ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step (.refl _)
        h01) h12) h23) h34) h45) h56) h67) h78) h89
  have hPostSpec := hCheck pv sa sb aid mem' hArgs hAid ha hb hStore
  cases hBZ : Nat.beq b 0 with
  | true =>
    have hbZ : b = 0 := Nat.eq_of_beq_eq_true hBZ
    rw [ite_prop_true hbZ] at hPostSpec
    have hTerm : evalStepV2 p1 ⟨[⟨1, 0, 9, l9, none, none, none⟩], cm, mem'⟩ =
        .done (.aborted (extractCallerMemory cm mem')) := by
      rw [evalStepV2_term_body1 _ cm mem' _ rfl rfl rfl rfl]
      unfold evalTerminatorV2 evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
      dsimp only [Captured.body_1, l9, Trusted.MirSemantics.getElem?, liveUninitSlot, setElem?]
      rw [ite_bool_false (rfl : (!isSupportedV2LocalTy .bool) = false), ite_prop_true rfl]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false), hBZ]
      rfl
    have hExec := execOutcomeStateV2_of_reaches_post hToTerm
      (execOutcomeStateV2_done (onDone := fun o => o = .aborted (extractCallerMemory cm mem'))
        (onFault := fun _ => False) (fuel := 0) hTerm rfl)
    let ⟨fuel, hExecS0⟩ := hExec
    have hExecProg : execProgV2 p1 fuel q (fun o => o = .aborted (extractCallerMemory cm mem')) := by
      unfold execProgV2
      rw [hInit]
      exact hExecS0
    exact (spec_and_behaviorV2_of_exec_eq hExecProg).2.2.2 (contract.post q) hPostSpec
  | false =>
    have hbPos : 0 < b := Nat.pos_of_ne_zero (fun h => by rw [h] at hBZ; cases hBZ)
    have hbNe : b ≠ 0 := Nat.ne_of_gt hbPos
    rw [ite_prop_false hbNe] at hPostSpec
    let l_b1_0 : List LocalSlot :=
      [.immediate none, .immediate (some vp), .immediate (some va), .immediate (some vb),
       .dead, .immediate (some va), .immediate (some vb), .immediate none]
    let l_b1_1 : List LocalSlot :=
      [.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩)),
       .immediate (some vp), .immediate (some va), .immediate (some vb),
       .dead, .immediate none, .immediate none, .immediate none]
    let l_b1_2 : List LocalSlot :=
      [.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩)),
       .immediate (some vp), .immediate (some va), .immediate (some vb),
       .dead, .immediate none, .dead, .immediate none]
    let l_b1_3 : List LocalSlot :=
      [.immediate (some (.scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩)),
       .immediate (some vp), .immediate (some va), .immediate (some vb),
       .dead, .dead, .dead, .immediate none]
    have hTerm0 : evalStepV2 p1 ⟨[⟨1, 0, 9, l9, none, none, none⟩], cm, mem'⟩ =
        .step ⟨[⟨1, 1, 0, l_b1_0, none, none, none⟩], cm, mem'⟩ := by
      rw [evalStepV2_term_body1 _ cm mem' _ rfl rfl rfl rfl]
      unfold evalTerminatorV2 evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
      dsimp only [Captured.body_1, l9, Trusted.MirSemantics.getElem?, liveUninitSlot, setElem?]
      rw [ite_bool_false (rfl : (!isSupportedV2LocalTy .bool) = false), ite_prop_true rfl]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false), hBZ]
      rfl
    have hDivLt : a / b < Nat.pow 2 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
    have hWfDiv := checkValV2_isize_ofNat hDivLt
    have hB1_01 : evalStepV2 p1 ⟨[⟨1, 1, 0, l_b1_0, none, none, none⟩], cm, mem'⟩ =
        .step ⟨[⟨1, 1, 1, l_b1_1, none, none, none⟩], cm, mem'⟩ := by
      rw [evalStepV2_mk_body1 _ cm mem' _ _ rfl rfl rfl rfl]
      unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2 evalPrimitiveOperandV2 evalOperandToSlotV2 readPlaceV2
      dsimp only [Captured.body_1, l_b1_0, Trusted.MirSemantics.getElem?, liveUninitSlot, setElem?]
      rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false), ite_prop_true rfl]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only [Trusted.MirSemantics.getElem?, liveUninitSlot, setElem?]
      rw [ite_bool_false (rfl : (!isSupportedV2LocalTy (.int .isize false)) = false), ite_prop_true rfl]
      dsimp only [liveUninitSlot, setElem?]
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [evalBinOp_isize_div ha hb hbPos]
      dsimp only
      unfold writePlaceDestV2
      rw [ite_bool_false (by rw [hWfDiv]; rfl)]
      rfl
    have hB1_12 : evalStepV2 p1 ⟨[⟨1, 1, 1, l_b1_1, none, none, none⟩], cm, mem'⟩ =
        .step ⟨[⟨1, 1, 2, l_b1_2, none, none, none⟩], cm, mem'⟩ := rfl
    have hB1_23 : evalStepV2 p1 ⟨[⟨1, 1, 2, l_b1_2, none, none, none⟩], cm, mem'⟩ =
        .step ⟨[⟨1, 1, 3, l_b1_3, none, none, none⟩], cm, mem'⟩ := rfl
    let retVal := Val.scalar ⟨.isize, false, BitVec.ofNat 128 (a / b)⟩
    have hB1_ret : evalStepV2 p1 ⟨[⟨1, 1, 3, l_b1_3, none, none, none⟩], cm, mem'⟩ =
        .done (.returned ⟨retVal, extractCallerMemory cm mem'⟩) := by
      rw [evalStepV2_term_body1 _ cm mem' _ rfl rfl rfl rfl]
      unfold evalTerminatorV2
      dsimp only [Captured.body_1, l_b1_3, Trusted.MirSemantics.getElem?]
      have h0 : hasEscapingRodataPtr cm mem' (.int .isize false) retVal = false := rfl
      have h1 : refsStayInCallerMem cm (.int .isize false) retVal = true := rfl
      have h2 : refsValidInMem mem' (.int .isize false) retVal = true := rfl
      have h3 : spansPairwiseDisjoint (refAccessSpans (.int .isize false) retVal) = true := rfl
      have hGuard : (!refsStayInCallerMem cm (.int .isize false) retVal ||
          !refsValidInMem mem' (.int .isize false) retVal ||
          !spansPairwiseDisjoint (refAccessSpans (.int .isize false) retVal)) = false := by
        rw [h1, h2, h3]; rfl
      rw [ite_bool_false h0, ite_bool_false hGuard]
      rw [rm2_extractReturnMemoryV2_eq _
        (rm2_storeIndirectV2_ids hStore (fun _ hb => rm2_mem_allocIdsOf hb))]
      rfl
    have hToDone := ReachesV2_step (ReachesV2_step (ReachesV2_step (ReachesV2_step (.refl _)
      hTerm0) hB1_01) hB1_12) hB1_23
    let ⟨fuel, hExecS0⟩ := execOutcomeStateV2_of_reaches_post (reachesV2_trans hToTerm hToDone)
      (execOutcomeStateV2_done (onDone := fun o => o = .returned ⟨retVal, extractCallerMemory cm mem'⟩)
        (onFault := fun _ => False) (fuel := 0) hB1_ret rfl)
    have hExecProg : execProgV2 p1 fuel q
        (fun o => o = .returned ⟨retVal, extractCallerMemory cm mem'⟩) := by
      unfold execProgV2
      rw [hInit]
      exact hExecS0
    exact (spec_and_behaviorV2_of_exec_eq hExecProg).2.2.2 (contract.post q) hPostSpec

private theorem body1_allowAbort_contract :
    BodySatisfiesSafeContractV2 Captured.program 1 Captured.body_1
      Spec.writeThenDivAllowAbort := by
  refine ⟨rfl, body1_static_admitted, fun q hValid => ?_⟩
  refine body1_satisfies q hValid Spec.writeThenDivAllowAbort
    (fun pv sa sb aid mem' hArgs hAid ha hb hStore => ?_)
  cases hBZ : Nat.beq sb.bits.toNat 0 with
  | true =>
    have hbZ : sb.bits.toNat = 0 := Nat.eq_of_beq_eq_true hBZ
    rw [ite_prop_true hbZ]
    unfold SafeContractV2.post Spec.writeThenDivAllowAbort Spec.writeThenDivSlotPost
    dsimp only
    rw [hArgs]
    dsimp only
    rw [hAid]
    dsimp only
    refine ⟨rfl, hbZ, ?_⟩
    exact ⟨mem', by
      have hSaEq : sa = ⟨.isize, false, BitVec.ofNat 128 sa.bits.toNat⟩ := by
        let ⟨_, _, _, hArgs', _, hWA, hSA, hWfA, _, _, _⟩ := checkArgsMatchV2_body1 hValid.2.1
        rw [hArgs] at hArgs'
        injection hArgs' with _ hRest
        injection hRest with hEqSa _
        have hEq2 := Val.scalar.inj hEqSa
        subst hEq2
        exact scalar_eq_of_fields hWA hSA ha
      rw [← hSaEq] at hStore
      exact hStore, rfl⟩
  | false =>
    have hbNe : sb.bits.toNat ≠ 0 := fun h => by rw [h] at hBZ; cases hBZ
    rw [ite_prop_false hbNe]
    unfold SafeContractV2.post Spec.writeThenDivAllowAbort Spec.writeThenDivSlotPost
    dsimp only
    rw [hArgs]
    dsimp only
    rw [hAid]
    dsimp only
    have hDivLt : sa.bits.toNat / sb.bits.toNat < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
    have hToNat : (BitVec.ofNat 128 (sa.bits.toNat / sb.bits.toNat)).toNat =
        sa.bits.toNat / sb.bits.toNat :=
      toNat_bvOfNat_128 (Nat.lt_trans hDivLt (by decide))
    refine ⟨rfl, rfl, hToNat, ?_⟩
    exact ⟨mem', by
      have hSaEq : sa = ⟨.isize, false, BitVec.ofNat 128 sa.bits.toNat⟩ := by
        let ⟨_, _, _, hArgs', _, hWA, hSA, hWfA, _, _, _⟩ := checkArgsMatchV2_body1 hValid.2.1
        rw [hArgs] at hArgs'
        injection hArgs' with _ hRest
        injection hRest with hEqSa _
        have hEq2 := Val.scalar.inj hEqSa
        subst hEq2
        exact scalar_eq_of_fields hWA hSA ha
      rw [← hSaEq] at hStore
      exact hStore, rfl⟩

private theorem body1_noAbort_contract :
    BodySatisfiesSafeContractV2 Captured.program 1 Captured.body_1
      Spec.writeThenDivNoAbort := by
  refine ⟨rfl, body1_static_admitted, fun q hValid => ?_⟩
  intro hPre
  refine body1_satisfies q hValid Spec.writeThenDivNoAbort
    (fun pv sa sb aid mem' hArgs hAid ha hb hStore => ?_)
    hPre
  have hbNe : sb.bits.toNat ≠ 0 := by
    unfold Spec.writeThenDivNoAbort at hPre
    dsimp only at hPre
    rw [hArgs] at hPre
    exact hPre
  rw [ite_prop_false hbNe]
  unfold SafeContractV2.post Spec.writeThenDivNoAbort Spec.writeThenDivAllowAbort
    Spec.writeThenDivSlotPost
  dsimp only
  rw [hArgs]
  dsimp only
  rw [hAid]
  dsimp only
  have hDivLt : sa.bits.toNat / sb.bits.toNat < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  have hToNat : (BitVec.ofNat 128 (sa.bits.toNat / sb.bits.toNat)).toNat =
      sa.bits.toNat / sb.bits.toNat :=
    toNat_bvOfNat_128 (Nat.lt_trans hDivLt (by decide))
  refine ⟨rfl, rfl, hToNat, ?_⟩
  exact ⟨mem', by
    have hSaEq : sa = ⟨.isize, false, BitVec.ofNat 128 sa.bits.toNat⟩ := by
      let ⟨_, _, _, hArgs', _, hWA, hSA, hWfA, _, _, _⟩ := checkArgsMatchV2_body1 hValid.2.1
      rw [hArgs] at hArgs'
      injection hArgs' with _ hRest
      injection hRest with hEqSa _
      have hEq2 := Val.scalar.inj hEqSa
      subst hEq2
      exact scalar_eq_of_fields hWA hSA ha
    rw [← hSaEq] at hStore
    exact hStore, rfl⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      exact ⟨rfl, body0_static_admitted, fun q hValid _ =>
        (body0_allowAbort_contract.2.2 q hValid trivial).1⟩
    | succ n =>
      cases n with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        exact ⟨rfl, body1_static_admitted, fun q hValid _ =>
          (body1_allowAbort_contract.2.2 q hValid trivial).1⟩
      | succ _ =>
        change none = some body at hBody
        cases hBody
  · exact ⟨body0_allowAbort_contract, body0_noAbort_contract,
      body1_allowAbort_contract, body1_noAbort_contract⟩

end Proof
