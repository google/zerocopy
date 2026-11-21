-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp
import Anneal.BitVec

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Spec

private def optionU64Ety : EnumTy :=
  { id := 1653338149
    discrWidth := .isize
    discrSigned := true
    tagRepr := .scalar .i64 false
    discriminants := [0, 1]
    variantFields := [[], [.int .i64 false]] }

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by
  decide

private theorem pow64_add_lt_pow128 {a b : BitVec 64} :
    a.toNat + b.toNat < Nat.pow 2 128 :=
  Nat.lt_trans (Nat.add_lt_add a.isLt b.isLt) (by decide)

private theorem pow64_mul_lt_pow128 {a b : BitVec 64} :
    a.toNat * b.toNat < Nat.pow 2 128 := by
  have h1 : a.toNat * b.toNat < Nat.pow 2 64 * Nat.pow 2 64 := by
    have ha : a.toNat ≤ Nat.pow 2 64 - 1 := Nat.le_sub_one_of_lt a.isLt
    have hb : b.toNat ≤ Nat.pow 2 64 - 1 := Nat.le_sub_one_of_lt b.isLt
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul ha hb) (by decide)
  exact Nat.lt_of_lt_of_le h1 (by decide)

private theorem bv128_toNat_of_lt {n : Nat} (h : n < Nat.pow 2 128) :
    (BitVec.ofNat 128 n).toNat = n := by
  change n % Nat.pow 2 128 = n
  exact Nat.mod_eq_of_lt h

private theorem bv128_toNat_u64 (x : BitVec 64) :
    (BitVec.ofNat 128 x.toNat).toNat = x.toNat :=
  bv128_toNat_of_lt (Nat.lt_trans x.isLt pow64_lt_pow128)

private theorem truncateBits_u64 (x : BitVec 64) :
    truncateBits .i64 (BitVec.ofNat 128 x.toNat) = BitVec.ofNat 128 x.toNat := by
  refine truncateBits_of_toNat_lt ?_
  rw [bv128_toNat_u64 x]
  exact x.isLt

private theorem checkVal_u64 (x : BitVec 64) :
    checkVal (u64Val x) (.int .i64 false) = true :=
  checkVal_int_iff.mpr ⟨BitVec.ofNat 128 x.toNat, rfl, truncateBits_u64 x⟩

private theorem val_ty?_u64 (x : BitVec 64) :
    (u64Val x).ty? = some (.int .i64 false) := by
  unfold u64Val Val.ty? ScalarVal.wf
  dsimp only
  rw [truncateBits_u64 x, beq_self_eq_true]
  rfl

private theorem checkVal_u64Range (lo hi : BitVec 64) :
    checkVal (u64RangeVal lo hi) (.adtStruct u64RangeSty) = true := by
  have hTys : Val.tys? [u64Val lo, u64Val hi] =
      some [.int .i64 false, .int .i64 false] := by
    change (match (u64Val lo).ty?,
        (match (u64Val hi).ty?, some ([] : List MirTy) with
          | some ty, some tys => some (ty :: tys)
          | _, _ => none) with
      | some ty, some tys => some (ty :: tys)
      | _, _ => none) = _
    rw [val_ty?_u64 lo, val_ty?_u64 hi]
  change (match (if !areSupportedFieldTys u64RangeSty.fields ||
        isTypeUninhabited (.adtStruct u64RangeSty) then none
      else match Val.tys? [u64Val lo, u64Val hi] with
        | some tys =>
          if MirTy.beqList tys u64RangeSty.fields then
            some (.adtStruct u64RangeSty)
          else none
        | none => none) with
    | some vTy => MirTy.beq vTy (.adtStruct u64RangeSty)
    | none => false) = true
  rw [hTys]
  rfl

private theorem checkVal_u64Bool (x : BitVec 64) (flag : Bool) :
    checkVal (.tuple [u64Val x, .bool flag])
      (.tuple [.int .i64 false, .bool]) = true := by
  have hTys : Val.tys? [u64Val x, .bool flag] =
      some [.int .i64 false, .bool] := by
    change (match (u64Val x).ty?, some [.bool] with
      | some ty, some tys => some (ty :: tys)
      | _, _ => none) = _
    rw [val_ty?_u64 x]
  change (match (match Val.tys? [u64Val x, .bool flag] with
      | some tys => some (.tuple tys)
      | none => none) with
    | some vTy => MirTy.beq vTy (.tuple [.int .i64 false, .bool])
    | none => false) = true
  rw [hTys]
  rfl

private theorem checkVal_optionU64_none :
    checkVal (.enumVal optionU64Ety 0 []) (.enum optionU64Ety) = true := by
  rfl

private theorem checkVal_optionU64_some (x : BitVec 64) :
    checkVal (.enumVal optionU64Ety 1 [u64Val x]) (.enum optionU64Ety) = true := by
  have hTys : Val.tys? [u64Val x] = some [.int .i64 false] := by
    change (match (u64Val x).ty?, some ([] : List MirTy) with
      | some ty, some tys => some (ty :: tys)
      | _, _ => none) = _
    rw [val_ty?_u64 x]
  change (match (if !enumAdmitted optionU64Ety ||
        isVariantUninhabited optionU64Ety 1 ||
        !enumValNicheValid optionU64Ety 1 [u64Val x] then none
      else match fieldsForVariant? optionU64Ety 1, Val.tys? [u64Val x] with
        | some expectedTys, some actualTys =>
          if MirTy.beqList actualTys expectedTys then
            some (.enum optionU64Ety)
          else none
        | _, _ => none) with
    | some vTy => MirTy.beq vTy (.enum optionU64Ety)
    | none => false) = true
  rw [hTys]
  rfl

private theorem decodeScalar_u64 (x : BitVec 64) :
    decodeScalar ⟨.i64, false, BitVec.ofNat 128 x.toNat⟩ = Int.ofNat x.toNat := by
  unfold decodeScalar
  rw [truncateBits_u64 x]
  change Int.ofNat (BitVec.ofNat 128 x.toNat).toNat = Int.ofNat x.toNat
  rw [bv128_toNat_u64 x]

private theorem bvOfInt_ofNat_lt128 {n : Nat} (h : n < Nat.pow 2 128) :
    bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  change BitVec.ofNat 128 (n % Nat.pow 2 128) = BitVec.ofNat 128 n
  rw [Nat.mod_eq_of_lt h]

private theorem nat_le_of_int_le {a b : Nat} (h : Int.ofNat a ≤ Int.ofNat b) :
    a ≤ b := by
  cases Nat.lt_or_ge b a with
  | inr hge => exact hge
  | inl hlt =>
    cases a with
    | zero => cases hlt
    | succ k =>
      change Int.NonNeg (Int.subNatNat b (k + 1)) at h
      unfold Int.subNatNat at h
      cases hd : k + 1 - b with
      | zero =>
        exact False.elim (Nat.not_le_of_gt hlt (Nat.le_of_sub_eq_zero hd))
      | succ d =>
        rw [hd] at h
        cases h

private theorem decide_ofNat_lt_zero (n : Nat) :
    decide (Int.ofNat n < 0) = false := by
  refine decide_eq_false ?_
  intro h
  cases h

private theorem decide_ofNat_ge_pow128 {n : Nat} (h : n < Nat.pow 2 128) :
    decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) = false := by
  refine decide_eq_false ?_
  intro hge
  exact Nat.not_lt_of_ge (nat_le_of_int_le hge) h

private theorem truncateBits_i64_mod {n : Nat} (h : n < Nat.pow 2 128) :
    truncateBits .i64 (BitVec.ofNat 128 n) =
      BitVec.ofNat 128 (n % Nat.pow 2 64) := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, bv128_toNat_of_lt h]
  have hmod : n % Nat.pow 2 64 < Nat.pow 2 128 :=
    Nat.lt_trans (Nat.mod_lt n (by decide)) pow64_lt_pow128
  rw [bv128_toNat_of_lt hmod]
  rfl

private theorem bne_truncateBits_i64 {n : Nat} (h : n < Nat.pow 2 128) :
    (truncateBits .i64 (BitVec.ofNat 128 n) != BitVec.ofNat 128 n) =
      decide (Nat.pow 2 64 ≤ n) := by
  cases Nat.lt_or_ge n (Nat.pow 2 64) with
  | inl hlt =>
    have htr : truncateBits .i64 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
      rw [truncateBits_i64_mod h, Nat.mod_eq_of_lt hlt]
    rw [htr, decide_eq_false (Nat.not_le_of_gt hlt)]
    exact bne_self_eq_false _
  | inr hge =>
    rw [decide_eq_true hge]
    unfold bne
    have hneq :
        (truncateBits .i64 (BitVec.ofNat 128 n) == BitVec.ofNat 128 n) = false := by
      cases hbeq : (truncateBits .i64 (BitVec.ofNat 128 n) ==
          BitVec.ofNat 128 n) with
      | false => rfl
      | true =>
        have heq := eq_of_beq hbeq
        have hnat := congrArg BitVec.toNat heq
        rw [toNat_truncateBits, bv128_toNat_of_lt h] at hnat
        change n % Nat.pow 2 64 = n at hnat
        have hlt : n % Nat.pow 2 64 < Nat.pow 2 64 :=
          Nat.mod_lt n (by decide)
        rw [hnat] at hlt
        exact False.elim (Nat.not_lt_of_ge hge hlt)
    rw [hneq]
    rfl

private theorem evalCoreBuiltin_overflowingAdd_u64 (a b : BitVec 64) :
    evalCoreBuiltin .overflowingAdd (.tuple [.int .i64 false, .bool])
        [u64Val a, u64Val b] =
      .ok (.tuple [u64Val (a + b),
        .bool (decide (Nat.pow 2 64 ≤ a.toNat + b.toNat))]) := by
  have hlt : a.toNat + b.toNat < Nat.pow 2 128 := pow64_add_lt_pow128
  change evalOverflowingArithOp .addWithOverflow .i64 false
      (decodeScalar ⟨.i64, false, BitVec.ofNat 128 a.toNat⟩)
      (decodeScalar ⟨.i64, false, BitVec.ofNat 128 b.toNat⟩) = _
  rw [decodeScalar_u64 a, decodeScalar_u64 b]
  unfold evalOverflowingArithOp truncateScalar
  dsimp only
  have hadd : Int.ofNat a.toNat + Int.ofNat b.toNat =
      Int.ofNat (a.toNat + b.toNat) := rfl
  rw [hadd, decide_ofNat_lt_zero, decide_ofNat_ge_pow128 hlt,
    bvOfInt_ofNat_lt128 hlt, bne_truncateBits_i64 hlt,
    truncateBits_i64_mod hlt]
  rfl

private theorem evalCoreBuiltin_checkedMul_u64 (a b : BitVec 64) :
    evalCoreBuiltin .checkedMul (.enum optionU64Ety) [u64Val a, u64Val b] =
      .ok (if a.toNat * b.toNat < Nat.pow 2 64 then
        .enumVal optionU64Ety 1 [u64Val (Anneal.BitVec.mul a b)]
      else
        .enumVal optionU64Ety 0 []) := by
  have hlt : a.toNat * b.toNat < Nat.pow 2 128 := pow64_mul_lt_pow128
  have hmulOp :
      evalBinOp .mulWithOverflow (u64Val a) (u64Val b) =
        .ok (.tuple [u64Val (Anneal.BitVec.mul a b),
          .bool (decide (Nat.pow 2 64 ≤ a.toNat * b.toNat))]) := by
    change evalOverflowingArithOp .mulWithOverflow .i64 false
        (decodeScalar ⟨.i64, false, BitVec.ofNat 128 a.toNat⟩)
        (decodeScalar ⟨.i64, false, BitVec.ofNat 128 b.toNat⟩) = _
    rw [decodeScalar_u64 a, decodeScalar_u64 b]
    unfold evalOverflowingArithOp truncateScalar
    dsimp only
    have hmul : Int.ofNat a.toNat * Int.ofNat b.toNat =
        Int.ofNat (a.toNat * b.toNat) := rfl
    rw [hmul, decide_ofNat_lt_zero, decide_ofNat_ge_pow128 hlt,
      bvOfInt_ofNat_lt128 hlt, bne_truncateBits_i64 hlt,
      truncateBits_i64_mod hlt]
    have htoNat : (Anneal.BitVec.mul a b).toNat =
        (a.toNat * b.toNat) % Nat.pow 2 64 :=
      Anneal.BitVec.toNat_mul a b
    unfold u64Val
    rw [htoNat]
    rfl
  change evalCheckedArithOp .mulWithOverflow (.enum optionU64Ety)
      ⟨.i64, false, BitVec.ofNat 128 a.toNat⟩
      ⟨.i64, false, BitVec.ofNat 128 b.toNat⟩ = _
  unfold evalCheckedArithOp
  dsimp only
  change (match evalBinOp .mulWithOverflow (u64Val a) (u64Val b) with
    | .ok (.tuple [.scalar wrapped, .bool false]) =>
      let res : Val := .enumVal optionU64Ety 1 [.scalar wrapped]
      if checkVal res (.enum optionU64Ety) then
        Except.ok (ε := FaultKind) res
      else
        Except.error FaultKind.unsupported
    | .ok (.tuple [.scalar _, .bool true]) =>
      let res : Val := .enumVal optionU64Ety 0 []
      if checkVal res (.enum optionU64Ety) then
        Except.ok (ε := FaultKind) res
      else
        Except.error FaultKind.unsupported
    | .error k => Except.error k
    | .ok _ => Except.error FaultKind.unsupported) = _
  rw [hmulOp]
  cases Nat.lt_or_ge (a.toNat * b.toNat) (Nat.pow 2 64) with
  | inl hok =>
    rw [decide_eq_false (Nat.not_le_of_gt hok), ite_prop_true hok]
    change (if checkVal (Val.enumVal optionU64Ety 1 [u64Val (Anneal.BitVec.mul a b)])
        (.enum optionU64Ety) = true then
      Except.ok (ε := FaultKind)
        (Val.enumVal optionU64Ety 1 [u64Val (Anneal.BitVec.mul a b)])
    else Except.error FaultKind.unsupported) = _
    rw [checkVal_optionU64_some (Anneal.BitVec.mul a b)]
    rfl
  | inr hovf =>
    rw [decide_eq_true hovf, ite_prop_false (Nat.not_lt_of_ge hovf)]
    rfl

private theorem step_execState {p : Program} {fuel : Nat} {s s' : State}
    {post : TerminalOut → Prop}
    (h_step : evalStep p 0 s = .step s')
    (h_cont : execState p fuel s' post) :
    execState p (fuel + 1) s post := by
  change (match evalStep p 0 s with
    | .step st' => execState p fuel st' post
    | .done out => post out
    | .fault _ => False)
  rw [h_step]
  exact h_cont

private theorem done_execState {p : Program} {fuel : Nat} {s : State}
    {out : TerminalOut} {post : TerminalOut → Prop}
    (h_done : evalStep p 0 s = .done out)
    (h_post : post out) :
    execState p (fuel + 1) s post := by
  change (match evalStep p 0 s with
    | .step st' => execState p fuel st' post
    | .done o => post o
    | .fault _ => False)
  rw [h_done]
  exact h_post

private theorem step_frame {p : Program} {fuel : Nat}
    {d b i d' b' i' : Nat} {ls ls' : List LocalSlot}
    {rc rc' : Option ReturnContinuation} {callers : List FrameState}
    {callerMem : CallerMemory} {post : TerminalOut → Prop}
    (h_step : evalStep p 0
        { frames := ⟨d, b, i, ls, rc⟩ :: callers, callerMem := callerMem } =
      .step { frames := ⟨d', b', i', ls', rc'⟩ :: callers,
              callerMem := callerMem })
    (h_cont : execState p fuel
      { frames := ⟨d', b', i', ls', rc'⟩ :: callers,
        callerMem := callerMem } post) :
    execState p (fuel + 1)
      { frames := ⟨d, b, i, ls, rc⟩ :: callers,
        callerMem := callerMem } post :=
  step_execState h_step h_cont

private theorem writePlace_ok {localTy : MirTy}
    {locals locals' : List LocalSlot} {dst : Place}
    {dstTy : MirTy} {val : Val} {root root' : SlotVal}
    (h_chk : checkVal val dstTy = true)
    (h_get : Trusted.MirSemantics.getElem? locals dst.localId =
      some (.live root))
    (h_path : writePlaceSlotPath? (.ty localTy) root dst.projection
      val.toSlotVal = some root')
    (h_set : setElem? locals dst.localId (.live root') = some locals') :
    writePlaceWithLocalTy localTy locals dst dstTy val = .ok locals' := by
  unfold writePlaceWithLocalTy
  rw [ite_bool_false (by rw [h_chk]; rfl), h_get]
  dsimp only
  rw [h_path]
  dsimp only
  rw [h_set]

private theorem evalStep_assign {p : Program} {body : Body} {bb : BasicBlock}
    {d b i : Nat} {ls : List LocalSlot} {rc : Option ReturnContinuation}
    {callers : List FrameState} {callerMem : CallerMemory}
    {dstId : LocalId} {rvalue : Rvalue} {localTy dstTy : MirTy}
    {val : Val} {localsAfterRval localsAfterWrite : List LocalSlot}
    (h_body : Trusted.MirSemantics.getElem? p.bodies d = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.assign ⟨dstId, []⟩ rvalue))
    (h_notAgg : match rvalue with | .aggregate _ _ => False | _ => True)
    (h_local : Trusted.MirSemantics.getElem? body.locals dstId =
      some localTy)
    (h_proj : projectTy? localTy [] = some dstTy)
    (h_noOverlap : assignHasUnsupportedOverlap ⟨dstId, []⟩ dstTy rvalue = false)
    (h_rval : evalRvalue body.locals ls dstTy rvalue =
      .ok (val, localsAfterRval))
    (h_write : writePlaceWithLocalTy localTy localsAfterRval ⟨dstId, []⟩ dstTy
      val = .ok localsAfterWrite) :
    evalStep p 0
        { frames := ⟨d, b, i, ls, rc⟩ :: callers, callerMem := callerMem } =
      .step {
        frames := ⟨d, b, i + 1, localsAfterWrite, rc⟩ :: callers
        callerMem := callerMem
      } := by
  unfold evalStep evalStatement
  dsimp only
  rw [h_body]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [h_stmt]
  dsimp only
  rw [h_local]
  dsimp only
  rw [h_proj]
  dsimp only
  rw [ite_bool_false h_noOverlap]
  cases rvalue with
  | aggregate _ _ => exact False.elim h_notAgg
  | _ =>
    dsimp only
    rw [h_rval]
    dsimp only [resolveProjPath]
    rw [h_write]

private theorem writeAggregateFields_cons {bodyLocals : List MirTy}
    {localTy fieldTy : MirTy} {dstLocal idx : Nat}
    {baseProj : List ProjectionElem} {ls ls₁ ls₂ ls₃ : List LocalSlot}
    {opnd : Operand} {ops : List Operand} {fieldTys : List MirTy} {v : Val}
    (h_op : evalOperandToSlot bodyLocals ls opnd =
      .ok (fieldTy, v.toSlotVal, ls₁))
    (h_val : v.toSlotVal.toVal? = some v)
    (h_wr : writePlaceWithLocalTy localTy ls₁
      ⟨dstLocal, baseProj ++ [.field idx fieldTy]⟩ fieldTy v = .ok ls₂)
    (h_rest : writeAggregateFields bodyLocals localTy dstLocal baseProj
      (idx + 1) ls₂ ops fieldTys = .ok ls₃) :
    writeAggregateFields bodyLocals localTy dstLocal baseProj idx ls
      (opnd :: ops) (fieldTy :: fieldTys) = .ok ls₃ := by
  unfold writeAggregateFields
  dsimp only
  rw [h_op]
  dsimp only
  rw [ite_bool_false (by rw [MirTy.beq_iff.mpr rfl]; rfl), h_val]
  dsimp only
  rw [h_wr]
  dsimp only
  exact h_rest

private theorem evalStep_assign_u64Range {p : Program} {body : Body}
    {bb : BasicBlock} {d b i : Nat} {ls ls' : List LocalSlot}
    {rc : Option ReturnContinuation} {callers : List FrameState}
    {callerMem : CallerMemory} {dstId : LocalId} {op1 op2 : Operand}
    (h_body : Trusted.MirSemantics.getElem? p.bodies d = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.assign ⟨dstId, []⟩ (.aggregate (.adtStruct u64RangeSty) [op1, op2])))
    (h_local : Trusted.MirSemantics.getElem? body.locals dstId =
      some (.adtStruct u64RangeSty))
    (h_noOverlap : assignHasUnsupportedOverlap ⟨dstId, []⟩
      (.adtStruct u64RangeSty)
      (.aggregate (.adtStruct u64RangeSty) [op1, op2]) = false)
    (h_fields : writeAggregateFields body.locals (.adtStruct u64RangeSty)
      dstId [] 0 ls [op1, op2] u64RangeSty.fields = .ok ls') :
    evalStep p 0
        { frames := ⟨d, b, i, ls, rc⟩ :: callers, callerMem := callerMem } =
      .step {
        frames := ⟨d, b, i + 1, ls', rc⟩ :: callers
        callerMem := callerMem
      } := by
  unfold evalStep
  dsimp only
  rw [h_body]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [h_stmt]
  dsimp only
  refine evalStatement_assign_aggregate h_local rfl h_noOverlap rfl ?_
  unfold writeAggregate
  exact h_fields

private theorem valid_args_u64_2 {body : Body}
    (h_params : (body.locals.drop 1).take body.argumentCount =
      [.int .i64 false, .int .i64 false])
    {args : List Val} (h : ValidEntryArgs body args) :
    ∃ a b : BitVec 64, args = [u64Val a, u64Val b] := by
  unfold ValidEntryArgs at h
  rw [h_params] at h
  cases args with
  | nil => cases h
  | cons v1 r1 =>
    cases r1 with
    | nil =>
      change (checkVal v1 (.int .i64 false) && false) = true at h
      rw [Bool.and_false] at h; cases h
    | cons v2 r2 =>
      cases r2 with
      | cons _ _ =>
        change (checkVal v1 (.int .i64 false) &&
          (checkVal v2 (.int .i64 false) && false)) = true at h
        rw [Bool.and_false, Bool.and_false] at h; cases h
      | nil =>
        change (checkVal v1 (.int .i64 false) &&
          (checkVal v2 (.int .i64 false) && true)) = true at h
        cases h1 : checkVal v1 (.int .i64 false) with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          cases h2 : checkVal v2 (.int .i64 false) with
          | false => rw [h2] at h; cases h
          | true =>
            let ⟨b1, hv1, ht1⟩ := checkVal_int_iff.mp h1
            let ⟨b2, hv2, ht2⟩ := checkVal_int_iff.mp h2
            have h1lt : b1.toNat < Nat.pow 2 64 := by
              rw [← ht1, toNat_truncateBits]
              exact Nat.mod_lt b1.toNat (by decide)
            have h2lt : b2.toNat < Nat.pow 2 64 := by
              rw [← ht2, toNat_truncateBits]
              exact Nat.mod_lt b2.toNat (by decide)
            refine ⟨BitVec.ofNat 64 b1.toNat, BitVec.ofNat 64 b2.toNat, ?_⟩
            rw [hv1, hv2]
            unfold u64Val
            have he1 : (BitVec.ofNat 64 b1.toNat).toNat = b1.toNat :=
              Nat.mod_eq_of_lt h1lt
            have he2 : (BitVec.ofNat 64 b2.toNat).toNat = b2.toNat :=
              Nat.mod_eq_of_lt h2lt
            have hb1eq : BitVec.ofNat 128 b1.toNat = b1 := by
              apply bitVec_eq_of_toNat_eq
              change b1.toNat % Nat.pow 2 128 = b1.toNat
              exact Nat.mod_eq_of_lt (Nat.lt_trans h1lt pow64_lt_pow128)
            have hb2eq : BitVec.ofNat 128 b2.toNat = b2 := by
              apply bitVec_eq_of_toNat_eq
              change b2.toNat % Nat.pow 2 128 = b2.toNat
              exact Nat.mod_eq_of_lt (Nat.lt_trans h2lt pow64_lt_pow128)
            rw [he1, he2, hb1eq, hb2eq]

private theorem invert_u64Range_val {v : Val}
    (h : checkVal v (.adtStruct u64RangeSty) = true) :
    ∃ lo hi : BitVec 64, v = u64RangeVal lo hi := by
  unfold checkVal at h
  cases hTy : v.ty? with
  | none => rw [hTy] at h; cases h
  | some vTy =>
    rw [hTy] at h
    have hEqTy : vTy = .adtStruct u64RangeSty := MirTy.beq_iff.mp h
    subst hEqTy
    cases v with
    | bool _ | unit | ptr _ | bytes _ =>
      unfold Val.ty? at hTy; cases hTy
    | scalar sv =>
      unfold Val.ty? at hTy
      cases hwf : sv.wf <;> rw [hwf] at hTy <;> cases hTy
    | tuple fs =>
      unfold Val.ty? at hTy
      cases hEmp : fs.isEmpty <;> rw [hEmp] at hTy
      · cases hTs : Val.tys? fs <;> rw [hTs] at hTy <;> cases hTy
      · cases hTy
    | array elemTy elems =>
      unfold Val.ty? at hTy
      cases hC1 : (!isSupportedScalarOrUnitTy elemTy ||
          !elems.length.blt (Nat.pow 2 64) ||
          !elems.length.beq 0 && isTypeUninhabited elemTy) <;>
        rw [hC1] at hTy
      · cases hC2 : (!Val.checkElemsHaveTy elemTy elems) <;>
          rw [hC2] at hTy <;> cases hTy
      · cases hTy
    | enumVal ety v fs =>
      unfold Val.ty? at hTy
      cases hC1 : (!enumAdmitted ety || isVariantUninhabited ety v ||
          !enumValNicheValid ety v fs)
      · rw [ite_bool_false hC1] at hTy
        cases hVf : fieldsForVariant? ety v with
        | none => rw [hVf] at hTy; cases hTy
        | some expTys =>
          rw [hVf] at hTy
          cases hTs : Val.tys? fs with
          | none => rw [hTs] at hTy; cases hTy
          | some actTys =>
            rw [hTs] at hTy
            dsimp only at hTy
            cases hM : MirTy.beqList actTys expTys
            · rw [ite_bool_false hM] at hTy; cases hTy
            · rw [ite_bool_true hM] at hTy; cases hTy
      · rw [ite_bool_true hC1] at hTy; cases hTy
    | structVal sty fs =>
      unfold Val.ty? at hTy
      cases hC1 : (!areSupportedFieldTys sty.fields ||
          isTypeUninhabited (.adtStruct sty))
      · rw [ite_bool_false hC1] at hTy
        cases hTys : Val.tys? fs with
        | none => rw [hTys] at hTy; cases hTy
        | some tys =>
          rw [hTys] at hTy
          dsimp only at hTy
          cases hMatch : MirTy.beqList tys sty.fields with
          | false => rw [ite_bool_false hMatch] at hTy; cases hTy
          | true =>
            rw [ite_bool_true hMatch] at hTy
            injection hTy with hAdt
            injection hAdt with hStyEq
            subst hStyEq
            have hTysEq : tys = [.int .i64 false, .int .i64 false] := by
              cases tys with
              | nil => cases hMatch
              | cons t0 r0 =>
                cases r0 with
                | nil =>
                  change (MirTy.beq t0 (.int .i64 false) && false) = true at hMatch
                  rw [Bool.and_false] at hMatch
                  cases hMatch
                | cons t1 r1 =>
                  cases r1 with
                  | cons _ _ =>
                    change (MirTy.beq t0 (.int .i64 false) &&
                      (MirTy.beq t1 (.int .i64 false) && false)) = true at hMatch
                    rw [Bool.and_false, Bool.and_false] at hMatch
                    cases hMatch
                  | nil =>
                    change (MirTy.beq t0 (.int .i64 false) &&
                      (MirTy.beq t1 (.int .i64 false) && true)) = true at hMatch
                    cases hA : MirTy.beq t0 (.int .i64 false) with
                    | false => rw [hA] at hMatch; cases hMatch
                    | true =>
                      rw [hA] at hMatch
                      cases hB : MirTy.beq t1 (.int .i64 false) with
                      | false => rw [hB] at hMatch; cases hMatch
                      | true =>
                        rw [MirTy.beq_iff.mp hA, MirTy.beq_iff.mp hB]
            rw [hTysEq] at hTys
            cases fs with
            | nil => cases hTys
            | cons f0 r0 =>
              unfold Val.tys? at hTys
              cases hf0 : f0.ty? with
              | none => rw [hf0] at hTys; cases hTys
              | some t0 =>
                rw [hf0] at hTys
                cases htr0 : Val.tys? r0 with
                | none => rw [htr0] at hTys; cases hTys
                | some ts0 =>
                  rw [htr0] at hTys
                  injection hTys with hList0
                  injection hList0 with ht0 hts0
                  subst ht0; subst hts0
                  cases r0 with
                  | nil => cases htr0
                  | cons f1 r1 =>
                    unfold Val.tys? at htr0
                    cases hf1 : f1.ty? with
                    | none => rw [hf1] at htr0; cases htr0
                    | some t1 =>
                      rw [hf1] at htr0
                      cases htr1 : Val.tys? r1 with
                      | none => rw [htr1] at htr0; cases htr0
                      | some ts1 =>
                        rw [htr1] at htr0
                        injection htr0 with hList1
                        injection hList1 with ht1 hts1
                        subst ht1; subst hts1
                        cases r1 with
                        | cons f2 r2 =>
                          unfold Val.tys? at htr1
                          cases hf2 : f2.ty? <;> rw [hf2] at htr1
                          · cases htr1
                          · cases htr2 : Val.tys? r2 <;> rw [htr2] at htr1 <;>
                              cases htr1
                        | nil =>
                          have hchk0 : checkVal f0 (.int .i64 false) = true := by
                            unfold checkVal; rw [hf0]; rfl
                          have hchk1 : checkVal f1 (.int .i64 false) = true := by
                            unfold checkVal; rw [hf1]; rfl
                          let ⟨b0, h0, ht0⟩ := checkVal_int_iff.mp hchk0
                          let ⟨b1, h1, ht1⟩ := checkVal_int_iff.mp hchk1
                          have h0lt : b0.toNat < Nat.pow 2 64 := by
                            rw [← ht0, toNat_truncateBits]
                            exact Nat.mod_lt b0.toNat (by decide)
                          have h1lt : b1.toNat < Nat.pow 2 64 := by
                            rw [← ht1, toNat_truncateBits]
                            exact Nat.mod_lt b1.toNat (by decide)
                          refine ⟨BitVec.ofNat 64 b0.toNat,
                            BitVec.ofNat 64 b1.toNat, ?_⟩
                          rw [h0, h1]
                          unfold u64RangeVal u64Val
                          have he0 : (BitVec.ofNat 64 b0.toNat).toNat = b0.toNat :=
                            Nat.mod_eq_of_lt h0lt
                          have he1 : (BitVec.ofNat 64 b1.toNat).toNat = b1.toNat :=
                            Nat.mod_eq_of_lt h1lt
                          have hb0eq : BitVec.ofNat 128 b0.toNat = b0 := by
                            apply bitVec_eq_of_toNat_eq
                            change b0.toNat % Nat.pow 2 128 = b0.toNat
                            exact Nat.mod_eq_of_lt
                              (Nat.lt_trans h0lt pow64_lt_pow128)
                          have hb1eq : BitVec.ofNat 128 b1.toNat = b1 := by
                            apply bitVec_eq_of_toNat_eq
                            change b1.toNat % Nat.pow 2 128 = b1.toNat
                            exact Nat.mod_eq_of_lt
                              (Nat.lt_trans h1lt pow64_lt_pow128)
                          rw [he0, he1, hb0eq, hb1eq]
      · rw [ite_bool_true hC1] at hTy; cases hTy

private theorem valid_args_u64Range_2 {body : Body}
    (h_params : (body.locals.drop 1).take body.argumentCount =
      [.adtStruct u64RangeSty, .adtStruct u64RangeSty])
    {args : List Val} (h : ValidEntryArgs body args) :
    ∃ a_lo a_hi b_lo b_hi : BitVec 64,
      args = [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] := by
  unfold ValidEntryArgs at h
  rw [h_params] at h
  cases args with
  | nil => cases h
  | cons v1 r1 =>
    cases r1 with
    | nil =>
      change (checkVal v1 (.adtStruct u64RangeSty) && false) = true at h
      rw [Bool.and_false] at h; cases h
    | cons v2 r2 =>
      cases r2 with
      | cons _ _ =>
        change (checkVal v1 (.adtStruct u64RangeSty) &&
          (checkVal v2 (.adtStruct u64RangeSty) && false)) = true at h
        rw [Bool.and_false, Bool.and_false] at h; cases h
      | nil =>
        change (checkVal v1 (.adtStruct u64RangeSty) &&
          (checkVal v2 (.adtStruct u64RangeSty) && true)) = true at h
        cases h1 : checkVal v1 (.adtStruct u64RangeSty) with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          cases h2 : checkVal v2 (.adtStruct u64RangeSty) with
          | false => rw [h2] at h; cases h
          | true =>
            let ⟨a_lo, a_hi, hv1⟩ := invert_u64Range_val h1
            let ⟨b_lo, b_hi, hv2⟩ := invert_u64Range_val h2
            exact ⟨a_lo, a_hi, b_lo, b_hi, by rw [hv1, hv2]⟩

/-! ### Body 0: `U64Range::new` -/

private theorem exec_new (lo hi : BitVec 64) (cm : CallerMemory) :
    execState Captured.program 12
      {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[0]
            [u64Val lo, u64Val hi] 0 Captured.program.bodies[0].locals
        }]
        callerMem := cm
      }
      (fun out =>
        match out with
        | .returned r => r.ret = u64RangeVal lo hi
        | .unwound _ => False) := by
  change execState Captured.program 12
    {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live (.structVal u64RangeSty [.uninit, .uninit]),
          .live (.scalar ⟨.i64, false, BitVec.ofNat 128 lo.toNat⟩),
          .live (.scalar ⟨.i64, false, BitVec.ofNat 128 hi.toNat⟩),
          .dead, .dead
        ]
      }]
      callerMem := cm
    } _
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 lo) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 hi) rfl rfl rfl)) ?_
  refine step_frame
    (evalStep_assign_u64Range (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl rfl rfl
      (writeAggregateFields_cons rfl rfl
        (writePlace_ok (checkVal_u64 lo) rfl rfl rfl)
      (writeAggregateFields_cons rfl rfl
        (writePlace_ok (checkVal_u64 hi) rfl rfl rfl)
      rfl))) ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine done_execState rfl ?_
  rfl

private noncomputable def newCallSpec : CallSpec Captured.program 0 :=
  CallSpec.ofExec Captured.program.bodies[0] rfl rfl 12
    (fun _ => True)
    (fun args retVal _ =>
      ∀ lo hi : BitVec 64,
        args = [u64Val lo, u64Val hi] → retVal = u64RangeVal lo hi)
    (fun _ _ => False)
    (fun args cm hValid _ => by
      let ⟨lo, hi, hEq⟩ := valid_args_u64_2 rfl hValid
      rw [hEq]
      refine execOutcomeState_of_wpOutcomeState
        (wpOutcomeState_mono ?_ (fun _ h => h)
          (wpOutcomeState_of_execOutcomeState (exec_new lo hi cm)))
      intro out hOut
      cases out with
      | unwound _ => exact hOut
      | returned r =>
        intro lo' hi' hArgs
        injection hArgs with h1 hRest
        injection hRest with h2 _
        unfold u64Val at h1 h2
        injection h1 with hSv1
        injection hSv1 with _ _ hBits1
        injection h2 with hSv2
        injection hSv2 with _ _ hBits2
        have hlo : lo = lo' := by
          apply bitVec_eq_of_toNat_eq
          have ht := congrArg BitVec.toNat hBits1
          rw [bv128_toNat_u64 lo, bv128_toNat_u64 lo'] at ht
          exact ht
        have hhi : hi = hi' := by
          apply bitVec_eq_of_toNat_eq
          have ht := congrArg BitVec.toNat hBits2
          rw [bv128_toNat_u64 hi, bv128_toNat_u64 hi'] at ht
          exact ht
        subst hlo; subst hhi
        exact hOut)

/-! ### Body 1: `U64Range::max` -/

private theorem exec_max (cm : CallerMemory) :
    execState Captured.program 16
      {
        frames := [{
          defId := 1
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[1]
            [] 0 Captured.program.bodies[1].locals
        }]
        callerMem := cm
      }
      (fun out =>
        match out with
        | .returned r =>
          r.ret = u64RangeVal (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64)
        | .unwound _ => False) := by
  change execState Captured.program 16
    {
      frames := [{
        defId := 1
        blockIdx := 0
        stmtIdx := 0
        locals := [.live (.structVal u64RangeSty [.uninit, .uninit])]
      }]
      callerMem := cm
    } _
  refine execCallSummary (p := Captured.program) (contFuel := 3)
    newCallSpec
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl True.intro
    (fun retVal cm' hPost => by
      have hRet : retVal =
          u64RangeVal (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64) :=
        hPost (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64) rfl
      subst hRet
      refine ⟨_, writePlace_ok
        (checkVal_u64Range (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64))
        rfl rfl rfl, ?_⟩
      dsimp only
      refine done_execState rfl ?_
      rfl)
    (fun _ hUnw => False.elim hUnw)

private noncomputable def maxCallSpec : CallSpec Captured.program 1 :=
  CallSpec.ofExec Captured.program.bodies[1] rfl rfl 16
    (fun _ => True)
    (fun _ retVal _ =>
      retVal = u64RangeVal (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64))
    (fun _ _ => False)
    (fun args cm hValid _ => by
      cases args with
      | cons _ _ =>
        unfold ValidEntryArgs at hValid
        cases hValid
      | nil => exact exec_max cm)

/-! ### Body 2: `U64Range::add_range` -/

private theorem exec_add_range_step (a_lo a_hi b_lo b_hi minSum maxSum : BitVec 64)
    (minOvf maxOvf : Bool) (cm : CallerMemory)
    (h1 : evalCoreBuiltin .overflowingAdd (.tuple [.int .i64 false, .bool])
        [u64Val a_lo, u64Val b_lo] =
      .ok (.tuple [u64Val minSum, .bool minOvf]))
    (h2 : evalCoreBuiltin .overflowingAdd (.tuple [.int .i64 false, .bool])
        [u64Val a_hi, u64Val b_hi] =
      .ok (.tuple [u64Val maxSum, .bool maxOvf])) :
    execState Captured.program 64
      {
        frames := [{
          defId := 2
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[2]
            [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] 0
            Captured.program.bodies[2].locals
        }]
        callerMem := cm
      }
      (fun out =>
        let resLo :=
          if minOvf != maxOvf then BitVec.ofNat 64 0 else minSum
        let resHi :=
          if minOvf != maxOvf then Anneal.BitVec.allOnes 64 else maxSum
        match out with
        | .returned r => r.ret = u64RangeVal resLo resHi
        | .unwound _ => False) := by
  change execState Captured.program 64
    {
      frames := [{
        defId := 2
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live (.structVal u64RangeSty [.uninit, .uninit]),
          .live (.structVal u64RangeSty [
            .scalar ⟨.i64, false, BitVec.ofNat 128 a_lo.toNat⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 a_hi.toNat⟩]),
          .live (.structVal u64RangeSty [
            .scalar ⟨.i64, false, BitVec.ofNat 128 b_lo.toNat⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 b_hi.toNat⟩]),
          .dead, .dead, .dead, .dead, .dead, .dead, .dead,
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead
        ]
      }]
      callerMem := cm
    } _
  -- bb0: overflowing_add(a_lo, b_lo) -> _5
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 a_lo) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 b_lo) rfl rfl rfl)) ?_
  refine execCallBuiltin (body := Captured.program.bodies[2])
    (bb := Captured.program.bodies[2].basicBlocks[0])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    h1
    (writePlace_ok (checkVal_u64Bool minSum minOvf) rfl rfl rfl) ?_
  -- bb1: unpack _5 into (_3, _4), overflowing_add(a_hi, b_hi) -> _10
  dsimp only
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 minSum) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok rfl rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 a_hi) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 b_hi) rfl rfl rfl)) ?_
  refine execCallBuiltin (body := Captured.program.bodies[2])
    (bb := Captured.program.bodies[2].basicBlocks[1])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    h2
    (writePlace_ok (checkVal_u64Bool maxSum maxOvf) rfl rfl rfl) ?_
  -- bb2: unpack _10 into (_8, _9), _13 = Ne(_4, _9), switchInt _13
  dsimp only
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 maxSum) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok rfl rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok rfl rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok rfl rfl rfl rfl)) ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[2])
      (bb := Captured.program.bodies[2].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok rfl rfl rfl rfl)) ?_
  cases minOvf <;> cases maxOvf
  · -- false, false -> bb4
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[2])
        (bb := Captured.program.bodies[2].basicBlocks[4])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 minSum) rfl rfl rfl)) ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[2])
        (bb := Captured.program.bodies[2].basicBlocks[4])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 maxSum) rfl rfl rfl)) ?_
    refine step_frame
      (evalStep_assign_u64Range (body := Captured.program.bodies[2])
        (bb := Captured.program.bodies[2].basicBlocks[4])
        rfl rfl rfl rfl rfl
        (writeAggregateFields_cons rfl rfl
          (writePlace_ok (checkVal_u64 minSum) rfl rfl rfl)
        (writeAggregateFields_cons rfl rfl
          (writePlace_ok (checkVal_u64 maxSum) rfl rfl rfl)
        rfl))) ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine done_execState rfl ?_
    rfl
  · -- false, true -> bb3
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine execCallSummary (p := Captured.program) (contFuel := 12)
      maxCallSpec
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl True.intro
      (fun retVal cm' hPost => by
        subst hPost
        refine ⟨_, writePlace_ok
          (checkVal_u64Range (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64))
          rfl rfl rfl, ?_⟩
        dsimp only
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine done_execState rfl ?_
        rfl)
      (fun _ hUnw => False.elim hUnw)
  · -- true, false -> bb3
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine execCallSummary (p := Captured.program) (contFuel := 12)
      maxCallSpec
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl True.intro
      (fun retVal cm' hPost => by
        subst hPost
        refine ⟨_, writePlace_ok
          (checkVal_u64Range (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64))
          rfl rfl rfl, ?_⟩
        dsimp only
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine step_frame rfl ?_
        refine done_execState rfl ?_
        rfl)
      (fun _ hUnw => False.elim hUnw)
  · -- true, true -> bb4
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[2])
        (bb := Captured.program.bodies[2].basicBlocks[4])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 minSum) rfl rfl rfl)) ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[2])
        (bb := Captured.program.bodies[2].basicBlocks[4])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 maxSum) rfl rfl rfl)) ?_
    refine step_frame
      (evalStep_assign_u64Range (body := Captured.program.bodies[2])
        (bb := Captured.program.bodies[2].basicBlocks[4])
        rfl rfl rfl rfl rfl
        (writeAggregateFields_cons rfl rfl
          (writePlace_ok (checkVal_u64 minSum) rfl rfl rfl)
        (writeAggregateFields_cons rfl rfl
          (writePlace_ok (checkVal_u64 maxSum) rfl rfl rfl)
        rfl))) ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine done_execState rfl ?_
    rfl

private theorem exec_add_range (a_lo a_hi b_lo b_hi : BitVec 64)
    (cm : CallerMemory) :
    execState Captured.program 64
      {
        frames := [{
          defId := 2
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[2]
            [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] 0
            Captured.program.bodies[2].locals
        }]
        callerMem := cm
      }
      (fun out =>
        let minOvf := decide (Nat.pow 2 64 ≤ a_lo.toNat + b_lo.toNat)
        let maxOvf := decide (Nat.pow 2 64 ≤ a_hi.toNat + b_hi.toNat)
        let resLo :=
          if minOvf != maxOvf then BitVec.ofNat 64 0 else a_lo + b_lo
        let resHi :=
          if minOvf != maxOvf then Anneal.BitVec.allOnes 64 else a_hi + b_hi
        match out with
        | .returned r => r.ret = u64RangeVal resLo resHi
        | .unwound _ => False) :=
  exec_add_range_step a_lo a_hi b_lo b_hi (a_lo + b_lo) (a_hi + b_hi)
    (decide (Nat.pow 2 64 ≤ a_lo.toNat + b_lo.toNat))
    (decide (Nat.pow 2 64 ≤ a_hi.toNat + b_hi.toNat))
    cm
    (evalCoreBuiltin_overflowingAdd_u64 a_lo b_lo)
    (evalCoreBuiltin_overflowingAdd_u64 a_hi b_hi)

/-! ### Body 3: `U64Range::mul_range` -/

private theorem exec_mul_range_step
    (a_lo a_hi b_lo b_hi loProd hiProd : BitVec 64)
    (loOk hiOk : Bool) (cm : CallerMemory)
    (h1 : evalCoreBuiltin .checkedMul (.enum optionU64Ety)
        [u64Val a_lo, u64Val b_lo] =
      .ok (if loOk then .enumVal optionU64Ety 1 [u64Val loProd]
           else .enumVal optionU64Ety 0 []))
    (h2 : evalCoreBuiltin .checkedMul (.enum optionU64Ety)
        [u64Val a_hi, u64Val b_hi] =
      .ok (if hiOk then .enumVal optionU64Ety 1 [u64Val hiProd]
           else .enumVal optionU64Ety 0 [])) :
    execState Captured.program 64
      {
        frames := [{
          defId := 3
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[3]
            [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] 0
            Captured.program.bodies[3].locals
        }]
        callerMem := cm
      }
      (fun out =>
        let ok := loOk && hiOk
        let resLo := if ok then loProd else BitVec.ofNat 64 0
        let resHi := if ok then hiProd else Anneal.BitVec.allOnes 64
        match out with
        | .returned r => r.ret = u64RangeVal resLo resHi
        | .unwound _ => False) := by
  change execState Captured.program 64
    {
      frames := [{
        defId := 3
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live (.structVal u64RangeSty [.uninit, .uninit]),
          .live (.structVal u64RangeSty [
            .scalar ⟨.i64, false, BitVec.ofNat 128 a_lo.toNat⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 a_hi.toNat⟩]),
          .live (.structVal u64RangeSty [
            .scalar ⟨.i64, false, BitVec.ofNat 128 b_lo.toNat⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 b_hi.toNat⟩]),
          .live .uninit,
          .dead, .dead, .dead, .dead,
          .live .uninit, .live .uninit,
          .dead, .dead, .dead, .dead,
          .live .uninit,
          .dead, .dead
        ]
      }]
      callerMem := cm
    } _
  -- bb0: checked_mul(a_lo, b_lo) -> _5
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[3])
      (bb := Captured.program.bodies[3].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 a_lo) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[3])
      (bb := Captured.program.bodies[3].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 b_lo) rfl rfl rfl)) ?_
  cases loOk with
  | false =>
    refine execCallBuiltin (body := Captured.program.bodies[3])
      (bb := Captured.program.bodies[3].basicBlocks[0])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      h1
      (writePlace_ok checkVal_optionU64_none rfl rfl rfl) ?_
    -- bb1: StorageDead 7, 6; _8 = discriminant(_5) (= 0); switchInt -> bb3
    dsimp only
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    -- bb3: StorageDead 5; call max() -> bb8; ret
    refine step_frame rfl ?_
    refine execCallSummary (p := Captured.program) (contFuel := 36)
      maxCallSpec
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl True.intro
      (fun retVal cm' hPost => by
        subst hPost
        refine ⟨_, writePlace_ok
          (checkVal_u64Range (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64))
          rfl rfl rfl, ?_⟩
        dsimp only
        refine done_execState rfl ?_
        rfl)
      (fun _ hUnw => False.elim hUnw)
  | true =>
    refine execCallBuiltin (body := Captured.program.bodies[3])
      (bb := Captured.program.bodies[3].basicBlocks[0])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      h1
      (writePlace_ok (checkVal_optionU64_some loProd) rfl rfl rfl) ?_
    -- bb1: StorageDead 7, 6; _8 = discriminant(_5) (= 1); switchInt -> bb2
    dsimp only
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    -- bb2: _4 = (_5 as Some).0; checked_mul(a_hi, b_hi) -> _11
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[3])
        (bb := Captured.program.bodies[3].basicBlocks[2])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 loProd) rfl rfl rfl)) ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[3])
        (bb := Captured.program.bodies[3].basicBlocks[2])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 a_hi) rfl rfl rfl)) ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[3])
        (bb := Captured.program.bodies[3].basicBlocks[2])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_u64 b_hi) rfl rfl rfl)) ?_
    cases hiOk with
    | false =>
      refine execCallBuiltin (body := Captured.program.bodies[3])
        (bb := Captured.program.bodies[3].basicBlocks[2])
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        h2
        (writePlace_ok checkVal_optionU64_none rfl rfl rfl) ?_
      -- bb4: StorageDead 13, 12; _14 = discriminant(_11) (= 0); switch -> bb6
      dsimp only
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      -- bb6: StorageDead 11; call max() -> bb7; StorageDead 4; goto bb8; ret
      refine step_frame rfl ?_
      refine execCallSummary (p := Captured.program) (contFuel := 23)
        maxCallSpec
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl True.intro
        (fun retVal cm' hPost => by
          subst hPost
          refine ⟨_, writePlace_ok
            (checkVal_u64Range (BitVec.ofNat 64 0) (Anneal.BitVec.allOnes 64))
            rfl rfl rfl, ?_⟩
          dsimp only
          refine step_frame rfl ?_
          refine step_frame rfl ?_
          refine done_execState rfl ?_
          rfl)
        (fun _ hUnw => False.elim hUnw)
    | true =>
      refine execCallBuiltin (body := Captured.program.bodies[3])
        (bb := Captured.program.bodies[3].basicBlocks[2])
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        h2
        (writePlace_ok (checkVal_optionU64_some hiProd) rfl rfl rfl) ?_
      -- bb4: StorageDead 13, 12; _14 = discriminant(_11) (= 1); switch -> bb5
      dsimp only
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      -- bb5: _10 = (_11 as Some).0; aggregate U64Range -> _0; goto bb8; ret
      refine step_frame rfl ?_
      refine step_frame
        (evalStep_assign (body := Captured.program.bodies[3])
          (bb := Captured.program.bodies[3].basicBlocks[5])
          rfl rfl rfl True.intro rfl rfl rfl rfl
          (writePlace_ok (checkVal_u64 hiProd) rfl rfl rfl)) ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame
        (evalStep_assign (body := Captured.program.bodies[3])
          (bb := Captured.program.bodies[3].basicBlocks[5])
          rfl rfl rfl True.intro rfl rfl rfl rfl
          (writePlace_ok (checkVal_u64 loProd) rfl rfl rfl)) ?_
      refine step_frame rfl ?_
      refine step_frame
        (evalStep_assign (body := Captured.program.bodies[3])
          (bb := Captured.program.bodies[3].basicBlocks[5])
          rfl rfl rfl True.intro rfl rfl rfl rfl
          (writePlace_ok (checkVal_u64 hiProd) rfl rfl rfl)) ?_
      refine step_frame
        (evalStep_assign_u64Range (body := Captured.program.bodies[3])
          (bb := Captured.program.bodies[3].basicBlocks[5])
          rfl rfl rfl rfl rfl
          (writeAggregateFields_cons rfl rfl
            (writePlace_ok (checkVal_u64 loProd) rfl rfl rfl)
          (writeAggregateFields_cons rfl rfl
            (writePlace_ok (checkVal_u64 hiProd) rfl rfl rfl)
          rfl))) ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine done_execState rfl ?_
      rfl

private theorem exec_mul_range (a_lo a_hi b_lo b_hi : BitVec 64)
    (cm : CallerMemory) :
    execState Captured.program 64
      {
        frames := [{
          defId := 3
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[3]
            [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] 0
            Captured.program.bodies[3].locals
        }]
        callerMem := cm
      }
      (fun out =>
        let ok := decide (a_lo.toNat * b_lo.toNat < Nat.pow 2 64) &&
          decide (a_hi.toNat * b_hi.toNat < Nat.pow 2 64)
        let resLo :=
          if ok then Anneal.BitVec.mul a_lo b_lo else BitVec.ofNat 64 0
        let resHi :=
          if ok then Anneal.BitVec.mul a_hi b_hi else Anneal.BitVec.allOnes 64
        match out with
        | .returned r => r.ret = u64RangeVal resLo resHi
        | .unwound _ => False) := by
  refine exec_mul_range_step a_lo a_hi b_lo b_hi
    (Anneal.BitVec.mul a_lo b_lo) (Anneal.BitVec.mul a_hi b_hi)
    (decide (a_lo.toNat * b_lo.toNat < Nat.pow 2 64))
    (decide (a_hi.toNat * b_hi.toNat < Nat.pow 2 64))
    cm ?_ ?_
  · rw [evalCoreBuiltin_checkedMul_u64 a_lo b_lo]
    cases Nat.lt_or_ge (a_lo.toNat * b_lo.toNat) (Nat.pow 2 64) with
    | inl h => rw [ite_prop_true h, decide_eq_true h]; rfl
    | inr h =>
      rw [ite_prop_false (Nat.not_lt_of_ge h),
        decide_eq_false (Nat.not_lt_of_ge h)]
      rfl
  · rw [evalCoreBuiltin_checkedMul_u64 a_hi b_hi]
    cases Nat.lt_or_ge (a_hi.toNat * b_hi.toNat) (Nat.pow 2 64) with
    | inl h => rw [ite_prop_true h, decide_eq_true h]; rfl
    | inr h =>
      rw [ite_prop_false (Nat.not_lt_of_ge h),
        decide_eq_false (Nat.not_lt_of_ge h)]
      rfl

private theorem execProg_body2 (a_lo a_hi b_lo b_hi : BitVec 64) :
    execProg (entryProgForBody Captured.program 2) 64
      { args := [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] }
      (fun out =>
        let minOvf := decide (Nat.pow 2 64 ≤ a_lo.toNat + b_lo.toNat)
        let maxOvf := decide (Nat.pow 2 64 ≤ a_hi.toNat + b_hi.toNat)
        let resLo :=
          if minOvf != maxOvf then BitVec.ofNat 64 0 else a_lo + b_lo
        let resHi :=
          if minOvf != maxOvf then Anneal.BitVec.allOnes 64 else a_hi + b_hi
        match out with
        | .returned r => r.ret = u64RangeVal resLo resHi
        | .unwound _ => False) := by
  have h_valid : ValidEntryArgs Captured.program.bodies[2]
      [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] := by
    change (checkVal (u64RangeVal a_lo a_hi) (.adtStruct u64RangeSty) &&
      (checkVal (u64RangeVal b_lo b_hi) (.adtStruct u64RangeSty) && true)) = true
    rw [checkVal_u64Range a_lo a_hi, checkVal_u64Range b_lo b_hi]
    rfl
  unfold execProg
  rw [initState_entryProgForBody (body := Captured.program.bodies[2]) rfl rfl
    h_valid]
  exact exec_add_range a_lo a_hi b_lo b_hi ⟨[]⟩

private theorem execProg_body3 (a_lo a_hi b_lo b_hi : BitVec 64) :
    execProg (entryProgForBody Captured.program 3) 64
      { args := [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] }
      (fun out =>
        let ok := decide (a_lo.toNat * b_lo.toNat < Nat.pow 2 64) &&
          decide (a_hi.toNat * b_hi.toNat < Nat.pow 2 64)
        let resLo :=
          if ok then Anneal.BitVec.mul a_lo b_lo else BitVec.ofNat 64 0
        let resHi :=
          if ok then Anneal.BitVec.mul a_hi b_hi else Anneal.BitVec.allOnes 64
        match out with
        | .returned r => r.ret = u64RangeVal resLo resHi
        | .unwound _ => False) := by
  have h_valid : ValidEntryArgs Captured.program.bodies[3]
      [u64RangeVal a_lo a_hi, u64RangeVal b_lo b_hi] := by
    change (checkVal (u64RangeVal a_lo a_hi) (.adtStruct u64RangeSty) &&
      (checkVal (u64RangeVal b_lo b_hi) (.adtStruct u64RangeSty) && true)) = true
    rw [checkVal_u64Range a_lo a_hi, checkVal_u64Range b_lo b_hi]
    rfl
  unfold execProg
  rw [initState_entryProgForBody (body := Captured.program.bodies[3]) rfl rfl
    h_valid]
  exact exec_mul_range a_lo a_hi b_lo b_hi ⟨[]⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
      have same : Captured.program.bodies[0] = selected := Option.some.inj found
      subst selected
      refine ⟨found, rfl, fun args h_valid _ => ?_⟩
      let ⟨lo, hi, h_eq⟩ := valid_args_u64_2 rfl h_valid
      rw [h_eq]
      have h_prog : execProg (entryProgForBody Captured.program 0) 12
          { args := [u64Val lo, u64Val hi] }
          (fun out =>
            match out with
            | .returned r => r.ret = u64RangeVal lo hi
            | .unwound _ => False) := by
        unfold execProg
        rw [initState_entryProgForBody (body := Captured.program.bodies[0])
          rfl rfl (by
            change (checkVal (u64Val lo) (.int .i64 false) &&
              (checkVal (u64Val hi) (.int .i64 false) && true)) = true
            rw [checkVal_u64 lo, checkVal_u64 hi]; rfl)]
        exact exec_new lo hi ⟨[]⟩
      exact (wellFormed_and_spec_of_wp _ _ _ _ (wpProg_of_execProg h_prog)).1.1
    | succ id1 =>
      cases id1 with
      | zero =>
        have same : Captured.program.bodies[1] = selected :=
          Option.some.inj found
        subst selected
        refine ⟨found, rfl, fun args h_valid _ => ?_⟩
        cases args with
        | cons _ _ => unfold ValidEntryArgs at h_valid; cases h_valid
        | nil =>
          have h_prog : execProg (entryProgForBody Captured.program 1) 16
              { args := [] }
              (fun out =>
                match out with
                | .returned r =>
                  r.ret = u64RangeVal (BitVec.ofNat 64 0)
                    (Anneal.BitVec.allOnes 64)
                | .unwound _ => False) := by
            unfold execProg
            rw [initState_entryProgForBody (p := Captured.program) (defId := 1)
              (body := Captured.program.bodies[1]) (args := []) rfl rfl rfl]
            exact exec_max ⟨[]⟩
          exact (wellFormed_and_spec_of_wp _ _ _ _
            (wpProg_of_execProg h_prog)).1.1
      | succ id2 =>
        cases id2 with
        | zero =>
          have same : Captured.program.bodies[2] = selected :=
            Option.some.inj found
          subst selected
          refine ⟨found, rfl, fun args h_valid _ => ?_⟩
          let ⟨a_lo, a_hi, b_lo, b_hi, h_eq⟩ :=
            valid_args_u64Range_2 rfl h_valid
          rw [h_eq]
          exact (wellFormed_and_spec_of_wp _ _ _ _
            (wpProg_of_execProg (execProg_body2 a_lo a_hi b_lo b_hi))).1.1
        | succ id3 =>
          cases id3 with
          | zero =>
            have same : Captured.program.bodies[3] = selected :=
              Option.some.inj found
            subst selected
            refine ⟨found, rfl, fun args h_valid _ => ?_⟩
            let ⟨a_lo, a_hi, b_lo, b_hi, h_eq⟩ :=
              valid_args_u64Range_2 rfl h_valid
            rw [h_eq]
            exact (wellFormed_and_spec_of_wp _ _ _ _
              (wpProg_of_execProg (execProg_body3 a_lo a_hi b_lo b_hi))).1.1
          | succ _ => cases found
  · constructor
    · intro a_lo x a_hi b_lo y b_hi ha_lo ha_hi hb_lo hb_hi
      let ⟨out, h_beh, h_post⟩ := (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (execProg_body2 a_lo a_hi b_lo b_hi))).2.2
      cases out with
      | unwound _ => exact False.elim h_post
      | returned r =>
        cases r with
        | mk rv cm =>
          dsimp only at h_post
          rw [h_post] at h_beh
          have h_sound := Anneal.BitVec.range_add_sound ha_lo ha_hi hb_lo hb_hi
          exact ⟨_, _, cm, h_beh, h_sound.1, h_sound.2⟩
    · intro a_lo x a_hi b_lo y b_hi ha_lo ha_hi hb_lo hb_hi
      let ⟨out, h_beh, h_post⟩ := (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (execProg_body3 a_lo a_hi b_lo b_hi))).2.2
      cases out with
      | unwound _ => exact False.elim h_post
      | returned r =>
        cases r with
        | mk rv cm =>
          dsimp only at h_post
          rw [h_post] at h_beh
          cases Nat.lt_or_ge (a_hi.toNat * b_hi.toNat) (Nat.pow 2 64) with
          | inl hhi_lt =>
            have hlo_lt : a_lo.toNat * b_lo.toNat < Nat.pow 2 64 :=
              Nat.lt_of_le_of_lt
                (Nat.mul_le_mul (Nat.le_trans ha_lo ha_hi)
                  (Nat.le_trans hb_lo hb_hi)) hhi_lt
            have h_sound := Anneal.BitVec.range_mul_no_overflow_sound
              ha_lo ha_hi hb_lo hb_hi hhi_lt
            rw [decide_eq_true hlo_lt, decide_eq_true hhi_lt] at h_beh
            exact ⟨Anneal.BitVec.mul a_lo b_lo, Anneal.BitVec.mul a_hi b_hi,
              cm, h_beh, h_sound.1, h_sound.2⟩
          | inr hhi_ge =>
            have hok_false :
                (decide (a_lo.toNat * b_lo.toNat < Nat.pow 2 64) &&
                  decide (a_hi.toNat * b_hi.toNat < Nat.pow 2 64)) = false := by
              rw [decide_eq_false (Nat.not_lt_of_ge hhi_ge), Bool.and_false]
            rw [hok_false] at h_beh
            refine ⟨BitVec.ofNat 64 0, Anneal.BitVec.allOnes 64, cm, h_beh, ?_, ?_⟩
            · change (BitVec.ofNat 64 0).toNat ≤
                (BitVec.ofNat 64 (x.toNat * y.toNat)).toNat
              rw [Anneal.BitVec.toNat_zero]
              exact Nat.zero_le _
            · change (BitVec.ofNat 64 (x.toNat * y.toNat)).toNat ≤
                (Anneal.BitVec.allOnes 64).toNat
              rw [Anneal.BitVec.toNat_allOnes]
              exact Nat.le_sub_one_of_lt (BitVec.ofNat 64 (x.toNat * y.toNat)).isLt

end Proof
