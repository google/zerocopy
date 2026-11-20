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
import Anneal.ListChunks

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Spec

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by
  decide

private theorem bitVec128_toNat_of_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (BitVec.ofNat 128 n).toNat = n := by
  change n % Nat.pow 2 128 = n
  exact Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)

private theorem truncateBits_usize {n : Nat} (h : n < Nat.pow 2 64) :
    truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  refine truncateBits_of_toNat_lt ?_
  rw [bitVec128_toNat_of_lt h]
  exact h

private theorem checkVal_usize {n : Nat} (h : n < Nat.pow 2 64) :
    checkVal (usizeVal n) (.int .isize false) = true :=
  checkVal_int_iff.mpr ⟨BitVec.ofNat 128 n, rfl, truncateBits_usize h⟩

private theorem checkVal_usizeBool {n : Nat} {flag : Bool}
    (h : n < Nat.pow 2 64) :
    checkVal (.tuple [usizeVal n, .bool flag])
      (.tuple [.int .isize false, .bool]) = true := by
  have hwf : ScalarVal.wf ⟨.isize, false, BitVec.ofNat 128 n⟩ = true := by
    unfold ScalarVal.wf
    dsimp only
    rw [truncateBits_usize h]
    exact beq_self_eq_true (BitVec.ofNat 128 n)
  have hty : (Val.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩).ty? =
      some (.int .isize false) := by
    unfold Val.ty?
    rw [hwf]
    rfl
  unfold checkVal Val.ty? Val.tys? usizeVal
  rw [hty]
  rfl

private theorem decodeScalar_usize {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  rw [truncateBits_usize h]
  change Int.ofNat (BitVec.ofNat 128 n).toNat = Int.ofNat n
  rw [bitVec128_toNat_of_lt h]

private theorem bvOfInt_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  change BitVec.ofNat 128 (n % Nat.pow 2 128) = BitVec.ofNat 128 n
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow64_lt_pow128)]

private theorem truncateScalar_usize {n : Nat} (h : n < Nat.pow 2 64) :
    truncateScalar .isize false (Int.ofNat n) =
      .ok (⟨.isize, false, BitVec.ofNat 128 n⟩, false) := by
  change (Except.ok (ε := FaultKind)
      (ScalarVal.mk .isize false
          (truncateBits .isize (bvOfInt 128 (Int.ofNat n))),
        truncateBits .isize (bvOfInt 128 (Int.ofNat n)) !=
          bvOfInt 128 (Int.ofNat n))) =
    .ok (⟨.isize, false, BitVec.ofNat 128 n⟩, false)
  rw [bvOfInt_ofNat_lt h, truncateBits_usize h]
  dsimp only [bne]
  rw [beq_self_eq_true (BitVec.ofNat 128 n)]
  rfl

private theorem int_sub_of_ge {a b : Nat} (h : b ≤ a) :
    Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) := by
  cases b with
  | zero =>
    change Int.ofNat (a + 0) = Int.ofNat (a - 0)
    rw [Nat.add_zero, Nat.sub_zero]
  | succ k =>
    change Int.subNatNat a (k + 1) = Int.ofNat (a - (k + 1))
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le h]

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

private theorem decide_ofNat_ge_pow128 {n : Nat} (h : n < Nat.pow 2 64) :
    decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) = false := by
  refine decide_eq_false ?_
  intro hge
  have hle : Nat.pow 2 128 ≤ n := nat_le_of_int_le hge
  exact Nat.not_lt_of_ge hle (Nat.lt_trans h pow64_lt_pow128)

private theorem evalBinOp_usize_eq_zero {n : Nat} (h : n < Nat.pow 2 64) :
    evalBinOp .eq (usizeVal n) (usizeVal 0) = .ok (.bool (Nat.beq n 0)) := by
  change (Except.ok (ε := FaultKind) (Val.bool
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ ==
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩))) =
    .ok (Val.bool (Nat.beq n 0))
  rw [decodeScalar_usize h, decodeScalar_usize (by decide : 0 < Nat.pow 2 64)]
  cases n with
  | zero => rfl
  | succ _ => rfl

private theorem evalBinOp_usize_subWithOverflow {k : Nat}
    (hk : k + 1 < Nat.pow 2 64) :
    evalBinOp .subWithOverflow (usizeVal (k + 1)) (usizeVal 1) =
      .ok (.tuple [usizeVal k, .bool false]) := by
  have hk_lt : k < Nat.pow 2 64 := Nat.lt_of_succ_lt hk
  change evalOverflowingArithOp .subWithOverflow .isize false
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 (k + 1)⟩)
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 1⟩) =
    .ok (.tuple [usizeVal k, .bool false])
  rw [decodeScalar_usize hk, decodeScalar_usize (by decide : 1 < Nat.pow 2 64)]
  unfold evalOverflowingArithOp
  dsimp only
  have hsub : Int.ofNat (k + 1) - Int.ofNat 1 = Int.ofNat k :=
    int_sub_of_ge (Nat.succ_le_succ (Nat.zero_le k))
  rw [hsub, decide_ofNat_lt_zero k, decide_ofNat_ge_pow128 hk_lt,
    truncateScalar_usize hk_lt]
  rfl

private theorem evalBinOp_usize_div {x m : Nat}
    (hx : x < Nat.pow 2 64) (hm : m + 1 < Nat.pow 2 64) :
    evalBinOp .div (usizeVal x) (usizeVal (m + 1)) =
      .ok (usizeVal (Nat.div x (m + 1))) := by
  have hq : Nat.div x (m + 1) < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self x (m + 1)) hx
  change evalArithOp .div .isize false
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 x⟩)
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 (m + 1)⟩) =
    .ok (usizeVal (Nat.div x (m + 1)))
  rw [decodeScalar_usize hx, decodeScalar_usize hm]
  change (match truncateScalar .isize false (Int.ofNat (Nat.div x (m + 1))) with
    | .error k => Except.error k
    | .ok (val, lossy) =>
      if (((decide (Int.ofNat (Nat.div x (m + 1)) < 0) ||
          decide (Int.ofNat (Nat.div x (m + 1)) ≥ HPow.hPow (2 : Int) 128)) ||
          lossy) && false) then
        Except.error FaultKind.undefined
      else
        Except.ok (Val.scalar val)) =
    Except.ok (usizeVal (Nat.div x (m + 1)))
  rw [truncateScalar_usize hq, decide_ofNat_lt_zero, decide_ofNat_ge_pow128 hq]
  rfl

private theorem evalBinOp_usize_addWithOverflow {q : Nat}
    (hq : q + 1 < Nat.pow 2 64) :
    evalBinOp .addWithOverflow (usizeVal q) (usizeVal 1) =
      .ok (.tuple [usizeVal (q + 1), .bool false]) := by
  have hq_lt : q < Nat.pow 2 64 := Nat.lt_of_succ_lt hq
  change evalOverflowingArithOp .addWithOverflow .isize false
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 q⟩)
      (decodeScalar ⟨.isize, false, BitVec.ofNat 128 1⟩) =
    .ok (.tuple [usizeVal (q + 1), .bool false])
  rw [decodeScalar_usize hq_lt,
    decodeScalar_usize (by decide : 1 < Nat.pow 2 64)]
  unfold evalOverflowingArithOp
  dsimp only
  have hadd : Int.ofNat q + Int.ofNat 1 = Int.ofNat (q + 1) := rfl
  rw [hadd, decide_ofNat_lt_zero (q + 1), decide_ofNat_ge_pow128 hq,
    truncateScalar_usize hq]
  rfl

private def divCeilPost (a b : Nat) (out : TerminalOut) : Prop :=
  if a = 0 then
    out = .returned ⟨usizeVal 0, ⟨[]⟩⟩
  else if b = 0 then
    out = .unwound ⟨[]⟩
  else
    out = .returned ⟨usizeVal (Nat.div (a - 1) b + 1), ⟨[]⟩⟩

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

private theorem writePlace_ok {locals locals' : List LocalSlot} {dst : Place}
    {dstTy : MirTy} {val : Val} {root root' : SlotVal}
    (h_chk : checkVal val dstTy = true)
    (h_get : Trusted.MirSemantics.getElem? locals dst.localId =
      some (.live root))
    (h_path : writeSlotPath? root dst.projection val.toSlotVal = some root')
    (h_set : setElem? locals dst.localId (.live root') = some locals') :
    writePlace locals dst dstTy val = .ok locals' := by
  unfold writePlace
  rw [ite_bool_false (by rw [h_chk]; rfl), h_get]
  dsimp only
  rw [h_path]
  dsimp only
  rw [h_set]

private theorem evalRvalue_binop_ok {bodyLocals : List MirTy}
    {locals l1 l2 : List LocalSlot} {dstTy : MirTy} {op : BinOp}
    {lhs rhs : Operand} {vl vr res : Val}
    (h_l : evalPrimitiveOperand bodyLocals locals lhs = .ok (vl, l1))
    (h_r : evalPrimitiveOperand bodyLocals l1 rhs = .ok (vr, l2))
    (h_op : evalBinOp op vl vr = .ok res) :
    evalRvalue bodyLocals locals dstTy (.binaryOp op lhs rhs) =
      .ok (res, l2) := by
  unfold evalRvalue
  dsimp only
  rw [h_l]
  dsimp only
  rw [h_r]
  dsimp only
  rw [h_op]

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

private theorem evalStep_assign {p : Program} {body : Body} {bb : BasicBlock}
    {d b i : Nat} {ls : List LocalSlot} {rc : Option ReturnContinuation}
    {callers : List FrameState} {callerMem : CallerMemory}
    {dst : Place} {rvalue : Rvalue} {localTy dstTy : MirTy}
    {val : Val} {localsAfterRval localsAfterWrite : List LocalSlot}
    (h_body : Trusted.MirSemantics.getElem? p.bodies d = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.assign dst rvalue))
    (h_notAgg : match rvalue with | .aggregateTuple _ => False | _ => True)
    (h_local : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some localTy)
    (h_proj : projectTy? localTy dst.projection = some dstTy)
    (h_noOverlap : assignHasUnsupportedOverlap dst dstTy rvalue = false)
    (h_rval : evalRvalue body.locals ls dstTy rvalue =
      .ok (val, localsAfterRval))
    (h_write : writePlace localsAfterRval dst dstTy val =
      .ok localsAfterWrite) :
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
  | aggregateTuple _ => exact False.elim h_notAgg
  | _ =>
    dsimp only
    rw [h_rval]
    dsimp only
    rw [h_write]

private theorem exec_div_ceil_usize (a b : Nat)
    (ha : a < Nat.pow 2 64) (hb : b < Nat.pow 2 64) :
    execProg (entryProgForBody Captured.program 0) 32
      { args := [usizeVal a, usizeVal b] } (divCeilPost a b) := by
  have h_valid : ValidEntryArgs Captured.program.bodies[0]
      [usizeVal a, usizeVal b] := by
    change (checkVal (usizeVal a) (.int .isize false) &&
      (checkVal (usizeVal b) (.int .isize false) && true)) = true
    rw [checkVal_usize ha, checkVal_usize hb]
    rfl
  unfold execProg
  rw [initState_entryProgForBody (body := Captured.program.bodies[0]) rfl rfl
    h_valid]
  change execState (entryProgForBody Captured.program 0) 32
    {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live .uninit,
          .live (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩),
          .live (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩),
          .dead, .dead, .dead, .dead, .dead,
          .live (.tuple [.uninit, .uninit]),
          .dead,
          .live .uninit,
          .live (.tuple [.uninit, .uninit])
        ]
      }]
      callerMem := ⟨[]⟩
    }
    (divCeilPost a b)
  -- bb0: StorageLive 3, StorageLive 4, _4 = copy _1, _3 = Eq(move _4, 0)
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_usize ha) rfl rfl rfl)) ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl
      (evalRvalue_binop_ok rfl rfl (evalBinOp_usize_eq_zero ha))
      (writePlace_ok rfl rfl rfl rfl)) ?_
  cases a with
  | zero =>
    -- bb0 switchInt (true -> bb1)
    refine step_frame rfl ?_
    -- bb1: StorageDead 4, _0 = 0, goto 6
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    -- bb6: StorageDead 3, return
    refine step_frame rfl ?_
    refine done_execState rfl ?_
    unfold divCeilPost
    rw [ite_prop_true rfl, truncateBits_usize (by decide : 0 < Nat.pow 2 64)]
    rfl
  | succ k =>
    have hk_lt : k < Nat.pow 2 64 := Nat.lt_of_succ_lt ha
    -- bb0 switchInt (false -> bb2)
    refine step_frame rfl ?_
    -- bb2: 4 storage ops + _7 = copy _1 + _8 = subWithOverflow(_7, 1) + assert
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[0])
        (bb := Captured.program.bodies[0].basicBlocks[2])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_usize ha) rfl rfl rfl)) ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[0])
        (bb := Captured.program.bodies[0].basicBlocks[2])
        rfl rfl rfl True.intro rfl rfl rfl
        (evalRvalue_binop_ok rfl rfl (evalBinOp_usize_subWithOverflow ha))
        (writePlace_ok (checkVal_usizeBool hk_lt) rfl rfl rfl)) ?_
    -- bb2 assert (!false -> bb3)
    refine step_frame rfl ?_
    -- bb3: _6 = move _8.0, StorageDead 7, StorageLive 9, _9 = copy _2,
    --      _10 = Eq(_9, 0), assert
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[0])
        (bb := Captured.program.bodies[0].basicBlocks[3])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_usize hk_lt) rfl rfl rfl)) ?_
    refine step_frame rfl ?_
    refine step_frame rfl ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[0])
        (bb := Captured.program.bodies[0].basicBlocks[3])
        rfl rfl rfl True.intro rfl rfl rfl rfl
        (writePlace_ok (checkVal_usize hb) rfl rfl rfl)) ?_
    refine step_frame
      (evalStep_assign (body := Captured.program.bodies[0])
        (bb := Captured.program.bodies[0].basicBlocks[3])
        rfl rfl rfl True.intro rfl rfl rfl
        (evalRvalue_binop_ok rfl rfl (evalBinOp_usize_eq_zero hb))
        (writePlace_ok rfl rfl rfl rfl)) ?_
    cases b with
    | zero =>
      -- bb3 assert fails (`true ≠ false`), unwinds cleanly!
      refine done_execState rfl ?_
      unfold divCeilPost
      rw [ite_prop_false (Nat.succ_ne_zero k), ite_prop_true rfl]
    | succ m =>
      have hq_succ_lt : Nat.div k (m + 1) + 1 < Nat.pow 2 64 :=
        Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.div_le_self k (m + 1))) ha
      have hq_lt : Nat.div k (m + 1) < Nat.pow 2 64 :=
        Nat.lt_of_succ_lt hq_succ_lt
      -- bb3 assert succeeds (`false == false` -> bb4)
      refine step_frame rfl ?_
      -- bb4: _5 = Div(move _6, move _9), StorageDead 9, StorageDead 6,
      --      _11 = AddWithOverflow(_5, 1), assert
      refine step_frame
        (evalStep_assign (body := Captured.program.bodies[0])
          (bb := Captured.program.bodies[0].basicBlocks[4])
          rfl rfl rfl True.intro rfl rfl rfl
          (evalRvalue_binop_ok rfl rfl (evalBinOp_usize_div hk_lt hb))
          (writePlace_ok (checkVal_usize hq_lt) rfl rfl rfl)) ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine step_frame
        (evalStep_assign (body := Captured.program.bodies[0])
          (bb := Captured.program.bodies[0].basicBlocks[4])
          rfl rfl rfl True.intro rfl rfl rfl
          (evalRvalue_binop_ok rfl rfl
            (evalBinOp_usize_addWithOverflow hq_succ_lt))
          (writePlace_ok (checkVal_usizeBool hq_succ_lt) rfl rfl rfl)) ?_
      -- bb4 assert succeeds -> bb5
      refine step_frame rfl ?_
      -- bb5: _0 = move _11.0, StorageDead 5, goto 6
      refine step_frame
        (evalStep_assign (body := Captured.program.bodies[0])
          (bb := Captured.program.bodies[0].basicBlocks[5])
          rfl rfl rfl True.intro rfl rfl rfl rfl
          (writePlace_ok (checkVal_usize hq_succ_lt) rfl rfl rfl)) ?_
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      -- bb6: StorageDead 3, return
      refine step_frame rfl ?_
      refine done_execState rfl ?_
      unfold divCeilPost
      rw [ite_prop_false (Nat.succ_ne_zero k),
        ite_prop_false (Nat.succ_ne_zero m)]
      rfl

private theorem valid_args_usize2 {args : List Val}
    (h : ValidEntryArgs Captured.program.bodies[0] args) :
    ∃ a b : Nat, a < Nat.pow 2 64 ∧ b < Nat.pow 2 64 ∧
      args = [usizeVal a, usizeVal b] := by
  change checkArgsMatch args [.int .isize false, .int .isize false] = true at h
  cases args with
  | nil => cases h
  | cons v1 rest =>
    cases rest with
    | nil =>
      change (checkVal v1 (.int .isize false) && false) = true at h
      rw [Bool.and_false] at h
      cases h
    | cons v2 tail =>
      cases tail with
      | cons _ _ =>
        change (checkVal v1 (.int .isize false) &&
          (checkVal v2 (.int .isize false) && false)) = true at h
        rw [Bool.and_false, Bool.and_false] at h
        cases h
      | nil =>
        change (checkVal v1 (.int .isize false) &&
          (checkVal v2 (.int .isize false) && true)) = true at h
        cases h1 : checkVal v1 (.int .isize false) with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          cases h2 : checkVal v2 (.int .isize false) with
          | false => rw [h2] at h; cases h
          | true =>
            let ⟨b1, hv1, ht1⟩ := checkVal_int_iff.mp h1
            let ⟨b2, hv2, ht2⟩ := checkVal_int_iff.mp h2
            have ha : b1.toNat < Nat.pow 2 64 := by
              rw [← ht1, toNat_truncateBits]
              exact Nat.mod_lt b1.toNat (by decide)
            have hb : b2.toNat < Nat.pow 2 64 := by
              rw [← ht2, toNat_truncateBits]
              exact Nat.mod_lt b2.toNat (by decide)
            refine ⟨b1.toNat, b2.toNat, ha, hb, ?_⟩
            rw [hv1, hv2]
            unfold usizeVal
            rw [bitVec_eq_of_toNat_eq (bitVec128_toNat_of_lt ha),
              bitVec_eq_of_toNat_eq (bitVec128_toNat_of_lt hb)]

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
      have same : Captured.program.bodies[0] = selected := Option.some.inj found
      subst selected
      refine ⟨found, rfl, fun args h_valid _ => ?_⟩
      let ⟨a, b, ha, hb, h_eq⟩ := valid_args_usize2 h_valid
      rw [h_eq]
      exact (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (exec_div_ceil_usize a b ha hb))).1.1
    | succ id => cases found
  · intro a b
    let ⟨out, h_beh, h_post⟩ := (wellFormed_and_spec_of_wp _ _ _ _
      (wpProg_of_execProg
        (exec_div_ceil_usize a.toNat b.toNat a.isLt b.isLt))).2.2
    unfold divCeilPost at h_post
    refine ⟨?_, ?_, ?_⟩
    · intro ha0
      rw [ite_prop_true ha0] at h_post
      rw [← h_post]
      exact h_beh
    · intro hane hb0
      rw [ite_prop_false hane, ite_prop_true hb0] at h_post
      rw [← h_post]
      exact h_beh
    · intro hane hbne
      rw [ite_prop_false hane, ite_prop_false hbne] at h_post
      have hb_pos : 0 < b.toNat := Nat.pos_of_ne_zero hbne
      have h_eq : Nat.div (a.toNat - 1) b.toNat + 1 =
          (a.toNat + b.toNat - 1) / b.toNat := by
        have h1 : Anneal.ListChunks.divCeil a.toNat b.toNat =
            (a.toNat + b.toNat - 1) / b.toNat :=
          Anneal.ListChunks.divCeil_eq_add_sub_div hb_pos
        unfold Anneal.ListChunks.divCeil at h1
        rw [ite_prop_false hane] at h1
        exact h1
      rw [h_eq] at h_post
      rw [← h_post]
      exact h_beh

end Proof
