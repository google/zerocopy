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
import Anneal.LeBytes

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Spec

private def u8Val (b : BitVec 8) : Val :=
  .scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩

private theorem pow8_lt_pow128 : Nat.pow 2 8 < Nat.pow 2 128 := by
  decide

private theorem pow32_lt_pow128 : Nat.pow 2 32 < Nat.pow 2 128 := by
  decide

private theorem pow64_lt_pow128 : Nat.pow 2 64 < Nat.pow 2 128 := by
  decide

private theorem bv128_toNat_u8 (b : BitVec 8) :
    (BitVec.ofNat 128 b.toNat).toNat = b.toNat := by
  change b.toNat % Nat.pow 2 128 = b.toNat
  exact Nat.mod_eq_of_lt (Nat.lt_trans b.isLt pow8_lt_pow128)

private theorem bv128_toNat_u32 (x : BitVec 32) :
    (BitVec.ofNat 128 x.toNat).toNat = x.toNat := by
  change x.toNat % Nat.pow 2 128 = x.toNat
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt pow32_lt_pow128)

private theorem bv128_toNat_u64 (x : BitVec 64) :
    (BitVec.ofNat 128 x.toNat).toNat = x.toNat := by
  change x.toNat % Nat.pow 2 128 = x.toNat
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt pow64_lt_pow128)

private theorem truncateBits_u8 (b : BitVec 8) :
    truncateBits .i8 (BitVec.ofNat 128 b.toNat) = BitVec.ofNat 128 b.toNat := by
  refine truncateBits_of_toNat_lt ?_
  rw [bv128_toNat_u8 b]
  exact b.isLt

private theorem truncateBits_u32 (x : BitVec 32) :
    truncateBits .i32 (BitVec.ofNat 128 x.toNat) = BitVec.ofNat 128 x.toNat := by
  refine truncateBits_of_toNat_lt ?_
  rw [bv128_toNat_u32 x]
  exact x.isLt

private theorem truncateBits_u64 (x : BitVec 64) :
    truncateBits .i64 (BitVec.ofNat 128 x.toNat) = BitVec.ofNat 128 x.toNat := by
  refine truncateBits_of_toNat_lt ?_
  rw [bv128_toNat_u64 x]
  exact x.isLt

private theorem checkVal_u8 (b : BitVec 8) :
    checkVal (u8Val b) (.int .i8 false) = true :=
  checkVal_int_iff.mpr ⟨BitVec.ofNat 128 b.toNat, rfl, truncateBits_u8 b⟩

private theorem checkVal_u32 (x : BitVec 32) :
    checkVal (u32Val x) (.int .i32 false) = true :=
  checkVal_int_iff.mpr ⟨BitVec.ofNat 128 x.toNat, rfl, truncateBits_u32 x⟩

private theorem checkVal_u64 (x : BitVec 64) :
    checkVal (u64Val x) (.int .i64 false) = true :=
  checkVal_int_iff.mpr ⟨BitVec.ofNat 128 x.toNat, rfl, truncateBits_u64 x⟩

private theorem val_ty?_u8 (b : BitVec 8) :
    (u8Val b).ty? = some (.int .i8 false) := by
  unfold u8Val Val.ty? ScalarVal.wf
  dsimp only
  rw [truncateBits_u8 b, beq_self_eq_true]
  rfl

private theorem checkElemsHaveTy_u8BytesToVals :
    ∀ bs : List (BitVec 8),
      Val.checkElemsHaveTy (.int .i8 false) (u8BytesToVals bs) = true
  | [] => rfl
  | b :: rest => by
    unfold u8BytesToVals Val.checkElemsHaveTy
    change (match (u8Val b).ty? with
      | some vTy =>
        vTy.beq (.int .i8 false) &&
          Val.checkElemsHaveTy (.int .i8 false) (u8BytesToVals rest)
      | none => false) = true
    rw [val_ty?_u8 b, checkElemsHaveTy_u8BytesToVals rest]
    rfl

private theorem checkVal_u8Array {len : Nat}
    (hlen : Nat.blt len (Nat.pow 2 64) = true)
    {bs : List (BitVec 8)} (hbs : bs.length = len) :
    checkVal (.array (.int .i8 false) (u8BytesToVals bs))
      (.array (.int .i8 false) len) = true := by
  unfold checkVal Val.ty?
  rw [checkElemsHaveTy_u8BytesToVals bs, length_u8BytesToVals bs, hbs, hlen]
  change (match
      if (false || false || !len.beq 0 && false) = true then none
      else if false = true then none
      else some ((MirTy.int .i8 false).array len) with
    | some vTy => vTy.beq ((MirTy.int .i8 false).array len)
    | none => false) = true
  rw [Bool.and_false]
  exact MirTy.beq_iff.mpr rfl

private theorem evalBinOp_bitOr_u64 (a b : BitVec 64) :
    evalBinOp .bitOr (u64Val a) (u64Val b) =
      .ok (u64Val (Anneal.BitVec.or a b)) := by
  change Except.ok (ε := FaultKind)
      (Val.scalar ⟨.i64, false,
        truncateBits .i64
          (bvOr (truncateBits .i64 (BitVec.ofNat 128 a.toNat))
                (truncateBits .i64 (BitVec.ofNat 128 b.toNat)))⟩) =
    .ok (u64Val (Anneal.BitVec.or a b))
  rw [truncateBits_u64 a, truncateBits_u64 b]
  have hlor :
      bvOr (BitVec.ofNat 128 a.toNat) (BitVec.ofNat 128 b.toNat) =
        BitVec.ofNat 128 (Anneal.BitVec.or a b).toNat := by
    unfold bvOr
    rw [bv128_toNat_u64 a, bv128_toNat_u64 b,
      ← Anneal.BitVec.toNat_or a b]
  rw [hlor, truncateBits_u64 (Anneal.BitVec.or a b)]
  rfl

private theorem evalCoreBuiltin_toLeBytes_u64 (x : BitVec 64) :
    evalCoreBuiltin .toLeBytes (.array (.int .i8 false) 8) [u64Val x] =
      .ok (.array (.int .i8 false)
        (u8BytesToVals (Anneal.LeBytes.u64ToLeBytes x))) := by
  change Except.ok (ε := FaultKind)
      (Val.array (.int .i8 false)
        (u8BytesToVals (scalarToLeBytesAux 8
          (truncateBits .i64 (BitVec.ofNat 128 x.toNat)).toNat))) =
    .ok (.array (.int .i8 false)
      (u8BytesToVals (Anneal.LeBytes.u64ToLeBytes x)))
  rw [truncateBits_u64 x, bv128_toNat_u64 x]
  rfl

private theorem evalCoreBuiltin_toLeBytes_u32 (x : BitVec 32) :
    evalCoreBuiltin .toLeBytes (.array (.int .i8 false) 4) [u32Val x] =
      .ok (.array (.int .i8 false)
        (u8BytesToVals (Anneal.LeBytes.u32ToLeBytes x))) := by
  change Except.ok (ε := FaultKind)
      (Val.array (.int .i8 false)
        (u8BytesToVals (scalarToLeBytesAux 4
          (truncateBits .i32 (BitVec.ofNat 128 x.toNat)).toNat))) =
    .ok (.array (.int .i8 false)
      (u8BytesToVals (Anneal.LeBytes.u32ToLeBytes x)))
  rw [truncateBits_u32 x, bv128_toNat_u32 x]
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

private theorem writeAggregateArrayElems_cons {bodyLocals : List MirTy}
    {localTy elemTy : MirTy} {dstLocal idx : Nat}
    {baseProj : List ProjectionElem} {ls ls₁ ls₂ ls₃ : List LocalSlot}
    {opnd : Operand} {ops : List Operand} {v : Val}
    (h_op : evalOperandToSlot bodyLocals ls opnd =
      .ok (elemTy, v.toSlotVal, ls₁))
    (h_val : v.toSlotVal.toVal? = some v)
    (h_wr : writePlaceWithLocalTy localTy ls₁
      ⟨dstLocal, baseProj ++ [.constantIndex idx (idx + 1) false]⟩ elemTy v =
      .ok ls₂)
    (h_rest : writeAggregateArrayElems bodyLocals localTy dstLocal baseProj
      elemTy (idx + 1) ls₂ ops = .ok ls₃) :
    writeAggregateArrayElems bodyLocals localTy dstLocal baseProj elemTy idx ls
      (opnd :: ops) = .ok ls₃ := by
  unfold writeAggregateArrayElems
  dsimp only
  rw [h_op]
  dsimp only
  rw [ite_bool_false (by rw [MirTy.beq_iff.mpr rfl]; rfl), h_val]
  dsimp only
  rw [h_wr]
  dsimp only
  exact h_rest

private theorem evalStep_assign_array12 {p : Program} {body : Body}
    {bb : BasicBlock} {d b i : Nat} {ls ls' : List LocalSlot}
    {rc : Option ReturnContinuation} {callers : List FrameState}
    {callerMem : CallerMemory} {dstId : LocalId} {ops : List Operand}
    (h_body : Trusted.MirSemantics.getElem? p.bodies d = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.assign ⟨dstId, []⟩ (.aggregate (.array (.int .i8 false)) ops)))
    (h_local : Trusted.MirSemantics.getElem? body.locals dstId =
      some (.array (.int .i8 false) 12))
    (h_noOverlap : assignHasUnsupportedOverlap ⟨dstId, []⟩
      (.array (.int .i8 false) 12)
      (.aggregate (.array (.int .i8 false)) ops) = false)
    (h_len : ops.length = 12)
    (h_elems : writeAggregateArrayElems body.locals (.array (.int .i8 false) 12)
      dstId [] (.int .i8 false) 0 ls ops = .ok ls') :
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
  dsimp only
  rw [h_len]
  cases ops with
  | nil => cases h_len
  | cons _ _ => exact h_elems

private theorem exec_make_identity_bytes
    (length : BitVec 32) (level offset : BitVec 64)
    (o0 o1 o2 o3 o4 o5 o6 o7 c0 c1 c2 c3 : BitVec 8)
    (ho : Anneal.LeBytes.u64ToLeBytes (Anneal.BitVec.or offset level) =
      [o0, o1, o2, o3, o4, o5, o6, o7])
    (hl : Anneal.LeBytes.u32ToLeBytes length = [c0, c1, c2, c3]) :
    execProg (entryProgForBody Captured.program 0) 96
      { args := [u32Val length, u64Val level, u64Val offset] }
      (fun out =>
        out = .returned
          ⟨.array (.int .i8 false)
            (u8BytesToVals [o0, o1, o2, o3, o4, o5, o6, o7, c0, c1, c2, c3]),
            ⟨[]⟩⟩) := by
  let ol := Anneal.BitVec.or offset level
  have h_valid : ValidEntryArgs Captured.program.bodies[0]
      [u32Val length, u64Val level, u64Val offset] := by
    change (checkVal (u32Val length) (.int .i32 false) &&
      (checkVal (u64Val level) (.int .i64 false) &&
        (checkVal (u64Val offset) (.int .i64 false) && true))) = true
    rw [checkVal_u32 length, checkVal_u64 level, checkVal_u64 offset]
    rfl
  unfold execProg
  rw [initState_entryProgForBody (body := Captured.program.bodies[0]) rfl rfl
    h_valid]
  change execState (entryProgForBody Captured.program 0) 96
    {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live (.array (.int .i8 false)
            [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit,
             .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]),
          .live (.scalar ⟨.i32, false, BitVec.ofNat 128 length.toNat⟩),
          .live (.scalar ⟨.i64, false, BitVec.ofNat 128 level.toNat⟩),
          .live (.scalar ⟨.i64, false, BitVec.ofNat 128 offset.toNat⟩),
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
          .dead, .dead, .dead, .dead, .dead, .dead
        ]
      }]
      callerMem := ⟨[]⟩
    } _
  -- bb0: compute `offset | level` and call `to_le_bytes` -> `_12`
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 offset) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u64 level) rfl rfl rfl)) ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl
      (evalRvalue_binop_ok rfl rfl (evalBinOp_bitOr_u64 offset level))
      (writePlace_ok (checkVal_u64 ol) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  have hToLe64 :
      evalCoreBuiltin .toLeBytes (.array (.int .i8 false) 8) [u64Val ol] =
        .ok (.array (.int .i8 false)
          (u8BytesToVals [o0, o1, o2, o3, o4, o5, o6, o7])) := by
    rw [evalCoreBuiltin_toLeBytes_u64 ol, ho]
  refine execCallBuiltin (body := Captured.program.bodies[0])
    (bb := Captured.program.bodies[0].basicBlocks[0])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hToLe64
    (writePlace_ok (checkVal_u8Array rfl rfl) rfl rfl rfl) ?_
  -- bb1: destructure `_12[0..7]` into `_4.._11`, call `to_le_bytes` -> `_20`
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o0) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o1) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o2) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o3) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o4) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o5) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o6) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o7) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u32 length) rfl rfl rfl)) ?_
  have hToLe32 :
      evalCoreBuiltin .toLeBytes (.array (.int .i8 false) 4) [u32Val length] =
        .ok (.array (.int .i8 false) (u8BytesToVals [c0, c1, c2, c3])) := by
    rw [evalCoreBuiltin_toLeBytes_u32 length, hl]
  refine execCallBuiltin (body := Captured.program.bodies[0])
    (bb := Captured.program.bodies[0].basicBlocks[1])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hToLe32
    (writePlace_ok (checkVal_u8Array rfl rfl) rfl rfl rfl) ?_
  -- bb2: destructure `_20[0..3]`, copy to `_22.._33`, aggregate `[u8; 12]`
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c0) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c1) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c2) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c3) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  -- Copy 12 bytes into temps `_22.._33`
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o0) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o1) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o2) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o3) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o4) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o5) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o6) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 o7) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c0) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c1) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c2) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u8 c3) rfl rfl rfl)) ?_
  -- s34: aggregate `[u8; 12]` into `_0`
  refine step_frame
    (evalStep_assign_array12 (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[2])
      rfl rfl rfl rfl rfl rfl
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o0) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o1) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o2) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o3) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o4) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o5) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o6) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 o7) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 c0) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 c1) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 c2) rfl rfl rfl)
      (writeAggregateArrayElems_cons rfl rfl
        (writePlace_ok (checkVal_u8 c3) rfl rfl rfl)
      rfl))))))))))))) ?_
  -- s35..s58 (24 StorageDead statements) + ret
  repeat refine step_frame rfl ?_
  refine done_execState rfl ?_
  rfl

private theorem exec_make_identity
    (length : BitVec 32) (level offset : BitVec 64) :
    execProg (entryProgForBody Captured.program 0) 96
      { args := [u32Val length, u64Val level, u64Val offset] }
      (fun out =>
        out = .returned
          ⟨.array (.int .i8 false)
            (u8BytesToVals
              (Anneal.LeBytes.u64ToLeBytes (Anneal.BitVec.or offset level) ++
                Anneal.LeBytes.u32ToLeBytes length)),
            ⟨[]⟩⟩) := by
  have ho := Anneal.LeBytes.toLeBytes_u64_eq (Anneal.BitVec.or offset level)
  have hl := Anneal.LeBytes.toLeBytes_u32_eq length
  have hExec := exec_make_identity_bytes length level offset _ _ _ _ _ _ _ _
    _ _ _ _ ho hl
  rw [ho, hl]
  exact hExec

private theorem u8BytesToVals_injective :
    ∀ {xs ys : List (BitVec 8)},
      u8BytesToVals xs = u8BytesToVals ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    unfold u8BytesToVals at h
    injection h with hHead hTail
    injection hHead with hSv
    injection hSv with _ _ hBits
    have hToNat := congrArg BitVec.toNat hBits
    rw [bv128_toNat_u8 x, bv128_toNat_u8 y] at hToNat
    have hxy : x = y := bitVec_eq_of_toNat_eq hToNat
    rw [hxy, u8BytesToVals_injective hTail]

private theorem valid_args_make_identity {args : List Val}
    (h : ValidEntryArgs Captured.program.bodies[0] args) :
    ∃ (length : BitVec 32) (level offset : BitVec 64),
      args = [u32Val length, u64Val level, u64Val offset] := by
  change checkArgsMatch args
    [.int .i32 false, .int .i64 false, .int .i64 false] = true at h
  cases args with
  | nil => cases h
  | cons v1 r1 =>
    cases r1 with
    | nil =>
      change (checkVal v1 (.int .i32 false) && false) = true at h
      rw [Bool.and_false] at h; cases h
    | cons v2 r2 =>
      cases r2 with
      | nil =>
        change (checkVal v1 (.int .i32 false) &&
          (checkVal v2 (.int .i64 false) && false)) = true at h
        rw [Bool.and_false, Bool.and_false] at h; cases h
      | cons v3 r3 =>
        cases r3 with
        | cons _ _ =>
          change (checkVal v1 (.int .i32 false) &&
            (checkVal v2 (.int .i64 false) &&
              (checkVal v3 (.int .i64 false) && false))) = true at h
          rw [Bool.and_false, Bool.and_false, Bool.and_false] at h; cases h
        | nil =>
          change (checkVal v1 (.int .i32 false) &&
            (checkVal v2 (.int .i64 false) &&
              (checkVal v3 (.int .i64 false) && true))) = true at h
          cases h1 : checkVal v1 (.int .i32 false) with
          | false => rw [h1] at h; cases h
          | true =>
            rw [h1] at h
            cases h2 : checkVal v2 (.int .i64 false) with
            | false => rw [h2] at h; cases h
            | true =>
              rw [h2] at h
              cases h3 : checkVal v3 (.int .i64 false) with
              | false => rw [h3] at h; cases h
              | true =>
                let ⟨b1, hv1, ht1⟩ := checkVal_int_iff.mp h1
                let ⟨b2, hv2, ht2⟩ := checkVal_int_iff.mp h2
                let ⟨b3, hv3, ht3⟩ := checkVal_int_iff.mp h3
                have h1lt : b1.toNat < Nat.pow 2 32 := by
                  rw [← ht1, toNat_truncateBits]
                  exact Nat.mod_lt b1.toNat (by decide)
                have h2lt : b2.toNat < Nat.pow 2 64 := by
                  rw [← ht2, toNat_truncateBits]
                  exact Nat.mod_lt b2.toNat (by decide)
                have h3lt : b3.toNat < Nat.pow 2 64 := by
                  rw [← ht3, toNat_truncateBits]
                  exact Nat.mod_lt b3.toNat (by decide)
                refine ⟨BitVec.ofNat 32 b1.toNat, BitVec.ofNat 64 b2.toNat,
                  BitVec.ofNat 64 b3.toNat, ?_⟩
                rw [hv1, hv2, hv3]
                unfold Spec.u32Val u64Val
                have heq1 : (BitVec.ofNat 32 b1.toNat).toNat = b1.toNat :=
                  Nat.mod_eq_of_lt h1lt
                have heq2 : (BitVec.ofNat 64 b2.toNat).toNat = b2.toNat :=
                  Nat.mod_eq_of_lt h2lt
                have heq3 : (BitVec.ofNat 64 b3.toNat).toNat = b3.toNat :=
                  Nat.mod_eq_of_lt h3lt
                have hb1eq : BitVec.ofNat 128 b1.toNat = b1 := by
                  apply bitVec_eq_of_toNat_eq
                  change b1.toNat % Nat.pow 2 128 = b1.toNat
                  exact Nat.mod_eq_of_lt (Nat.lt_trans h1lt pow32_lt_pow128)
                have hb2eq : BitVec.ofNat 128 b2.toNat = b2 := by
                  apply bitVec_eq_of_toNat_eq
                  change b2.toNat % Nat.pow 2 128 = b2.toNat
                  exact Nat.mod_eq_of_lt (Nat.lt_trans h2lt pow64_lt_pow128)
                have hb3eq : BitVec.ofNat 128 b3.toNat = b3 := by
                  apply bitVec_eq_of_toNat_eq
                  change b3.toNat % Nat.pow 2 128 = b3.toNat
                  exact Nat.mod_eq_of_lt (Nat.lt_trans h3lt pow64_lt_pow128)
                rw [heq1, heq2, heq3, hb1eq, hb2eq, hb3eq]

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
      have same : Captured.program.bodies[0] = selected := Option.some.inj found
      subst selected
      refine ⟨found, rfl, fun args h_valid _ => ?_⟩
      let ⟨length, level, offset, h_eq⟩ := valid_args_make_identity h_valid
      rw [h_eq]
      exact (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (exec_make_identity length level offset))).1.1
    | succ _ => cases found
  · constructor
    · intro length level offset
      let ⟨out, h_beh, h_post⟩ := (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (exec_make_identity length level offset))).2.2
      rw [h_post] at h_beh
      exact ⟨_, ⟨[]⟩, h_beh⟩
    · intro len₁ len₂ lvl₁ lvl₂ off₁ off₂ out cm₁ cm₂ hoff₁ hoff₂ hlvl₁ hlvl₂
        hbeh₁ hbeh₂
      have hpost₁ := (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (exec_make_identity len₁ lvl₁ off₁))).1.2 _ hbeh₁
      have hpost₂ := (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (exec_make_identity len₂ lvl₂ off₂))).1.2 _ hbeh₂
      injection hpost₁ with hret₁
      injection hpost₂ with hret₂
      have houtEq :
          Val.array (.int .i8 false)
            (u8BytesToVals
              (Anneal.LeBytes.u64ToLeBytes (Anneal.BitVec.or off₁ lvl₁) ++
                Anneal.LeBytes.u32ToLeBytes len₁)) =
          Val.array (.int .i8 false)
            (u8BytesToVals
              (Anneal.LeBytes.u64ToLeBytes (Anneal.BitVec.or off₂ lvl₂) ++
                Anneal.LeBytes.u32ToLeBytes len₂)) := by
        have h1 : out = _ := congrArg (fun r => r.ret) hret₁
        have h2 : out = _ := congrArg (fun r => r.ret) hret₂
        exact Eq.trans (Eq.symm h1) h2
      injection houtEq with _ hvals
      have hbytes := u8BytesToVals_injective hvals
      have ⟨horEq, hlenEq⟩ :=
        Anneal.LeBytes.toLeBytes_append_injective (m := 8) (n := 4) hbytes
      have ⟨hoffEq, hlvlEq⟩ :=
        Anneal.BitVec.aligned_or_bounded_injective (w := 64) (k := 13)
          (by decide) hoff₁ hoff₂ hlvl₁ hlvl₂ horEq
      exact ⟨hlenEq, hlvlEq, hoffEq⟩

end Proof
