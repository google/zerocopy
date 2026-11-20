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

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Spec

private theorem pow32_lt_pow128 : Nat.pow 2 32 < Nat.pow 2 128 := by
  decide

private theorem bitVec128_toNat_u32 {n : Nat} (h : n < Nat.pow 2 32) :
    (BitVec.ofNat 128 n).toNat = n := by
  change n % Nat.pow 2 128 = n
  exact Nat.mod_eq_of_lt (Nat.lt_trans h pow32_lt_pow128)

private theorem truncateBits_u32 {n : Nat} (h : n < Nat.pow 2 32) :
    truncateBits .i32 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  refine truncateBits_of_toNat_lt ?_
  rw [bitVec128_toNat_u32 h]
  exact h

private theorem checkVal_u32 {n : Nat} (h : n < Nat.pow 2 32) :
    checkVal (u32Scalar n) (.int .i32 false) = true :=
  checkVal_int_iff.mpr ⟨BitVec.ofNat 128 n, rfl, truncateBits_u32 h⟩

private theorem decodeScalar_u32 {n : Nat} (h : n < Nat.pow 2 32) :
    decodeScalar ⟨.i32, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  rw [truncateBits_u32 h]
  change Int.ofNat (BitVec.ofNat 128 n).toNat = Int.ofNat n
  rw [bitVec128_toNat_u32 h]

private theorem bvOfInt_ofNat_u32 {n : Nat} (h : n < Nat.pow 2 32) :
    bvOfInt 128 (Int.ofNat n) = BitVec.ofNat 128 n := by
  change BitVec.ofNat 128 (n % Nat.pow 2 128) = BitVec.ofNat 128 n
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h pow32_lt_pow128)]

private theorem truncateScalar_u32 {n : Nat} (h : n < Nat.pow 2 32) :
    truncateScalar .i32 false (Int.ofNat n) =
      .ok (⟨.i32, false, BitVec.ofNat 128 n⟩, false) := by
  change (Except.ok (ε := FaultKind)
      (ScalarVal.mk .i32 false
          (truncateBits .i32 (bvOfInt 128 (Int.ofNat n))),
        truncateBits .i32 (bvOfInt 128 (Int.ofNat n)) !=
          bvOfInt 128 (Int.ofNat n))) =
    .ok (⟨.i32, false, BitVec.ofNat 128 n⟩, false)
  rw [bvOfInt_ofNat_u32 h, truncateBits_u32 h]
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

private theorem int_le_of_nat_le {a b : Nat} (h : a ≤ b) :
    Int.ofNat a ≤ Int.ofNat b := by
  change Int.NonNeg (Int.ofNat b - Int.ofNat a)
  rw [int_sub_of_ge h]
  exact Int.NonNeg.mk (b - a)

private theorem int_sub_lt_zero_of_lt {a b : Nat} (h : a < b) :
    Int.ofNat a - Int.ofNat b < 0 := by
  cases b with
  | zero => cases h
  | succ k =>
    have hle : a ≤ k := Nat.le_of_succ_le_succ h
    have hsub : k + 1 - a = (k - a) + 1 := Nat.succ_sub hle
    change Int.NonNeg (0 - (Int.subNatNat a (k + 1) + 1))
    unfold Int.subNatNat
    rw [hsub]
    dsimp only
    cases k - a with
    | zero => exact Int.NonNeg.mk 0
    | succ d' => exact Int.NonNeg.mk (0 + (d' + 1))

private theorem decide_ofNat_lt_zero (n : Nat) :
    decide (Int.ofNat n < 0) = false := by
  refine decide_eq_false ?_
  intro h
  cases h

private theorem decide_ofNat_ge_pow128 {n : Nat} (h : n < Nat.pow 2 32) :
    decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) = false := by
  refine decide_eq_false ?_
  intro hge
  exact Nat.not_lt_of_ge (nat_le_of_int_le hge)
    (Nat.lt_trans h pow32_lt_pow128)

private theorem evalCoreBuiltin_saturatingSub_u32 {a b : Nat}
    (ha : a < Nat.pow 2 32) (hb : b < Nat.pow 2 32) :
    evalCoreBuiltin .saturatingSub (.int .i32 false)
        [u32Scalar a, u32Scalar b] =
      .ok (u32Scalar (a - b)) := by
  change (match evalOverflowingArithOp .subWithOverflow .i32 false
      (decodeScalar ⟨.i32, false, BitVec.ofNat 128 a⟩)
      (decodeScalar ⟨.i32, false, BitVec.ofNat 128 b⟩) with
    | .ok (.tuple [.scalar wrapped, .bool false]) =>
      Except.ok (Val.scalar wrapped)
    | .ok (.tuple [.scalar _, .bool true]) =>
      Except.ok (Val.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)
    | .error k => Except.error k
    | .ok _ => Except.error FaultKind.unsupported) =
    .ok (u32Scalar (a - b))
  rw [decodeScalar_u32 ha, decodeScalar_u32 hb]
  unfold evalOverflowingArithOp
  dsimp only
  cases Nat.lt_or_ge a b with
  | inr hge =>
    have hd : a - b < Nat.pow 2 32 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
    rw [int_sub_of_ge hge, decide_ofNat_lt_zero, decide_ofNat_ge_pow128 hd,
      truncateScalar_u32 hd]
    rfl
  | inl hlt =>
    have hneg : decide (Int.ofNat a - Int.ofNat b < 0) = true :=
      decide_eq_true (int_sub_lt_zero_of_lt hlt)
    rw [hneg]
    let ⟨sv, lossy, htr⟩ := truncateScalar_ok .i32 false
      (Int.ofNat a - Int.ofNat b)
    rw [htr.1]
    dsimp only [Bool.true_or]
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
    rfl

private theorem countLeadingZerosNat_le (raw : Nat) :
    ∀ width : Nat, countLeadingZerosNat raw width ≤ width
  | 0 => Nat.le_refl 0
  | w + 1 => by
    unfold countLeadingZerosNat
    dsimp only
    cases Nat.testBit raw w with
    | true => exact Nat.zero_le (w + 1)
    | false => exact Nat.succ_le_succ (countLeadingZerosNat_le raw w)

private theorem countLeadingZerosNat_zero_32 :
    countLeadingZerosNat 0 32 = 32 := by
  decide

private theorem evalCoreBuiltin_leadingZeros_u32 {d : Nat}
    (hd : d < Nat.pow 2 32) :
    evalCoreBuiltin .leadingZeros (.int .i32 false) [u32Scalar d] =
      .ok (u32Scalar (countLeadingZerosNat d 32)) := by
  have hclz : countLeadingZerosNat d 32 < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt (countLeadingZerosNat_le d 32) (by decide)
  change Except.ok (ε := FaultKind) (Val.scalar ⟨.i32, false,
      truncateBits .i32 (BitVec.ofNat 128
        (countLeadingZerosNat
          (truncateBits .i32 (BitVec.ofNat 128 d)).toNat 32))⟩) =
    .ok (u32Scalar (countLeadingZerosNat d 32))
  rw [truncateBits_u32 hd, bitVec128_toNat_u32 hd, truncateBits_u32 hclz]
  rfl

private noncomputable def clampGapFn (a b : Nat) : Nat :=
  let z := countLeadingZerosNat (a - b) 32
  if z ≤ 16 then z else 16

private theorem clampGapFn_le_16 (a b : Nat) : clampGapFn a b ≤ 16 := by
  unfold clampGapFn
  dsimp only
  cases Nat.lt_or_ge 16 (countLeadingZerosNat (a - b) 32) with
  | inl hgt =>
    rw [ite_prop_false (Nat.not_le_of_gt hgt)]
    exact Nat.le_refl 16
  | inr hle =>
    rw [ite_prop_true hle]
    exact hle

private theorem clampGapFn_of_le {a b : Nat} (h : a ≤ b) :
    clampGapFn a b = 16 := by
  unfold clampGapFn
  rw [Nat.sub_eq_zero_of_le h, countLeadingZerosNat_zero_32]
  rfl

private theorem evalCoreBuiltin_cmpMin_u32_16 {z : Nat}
    (hz : z < Nat.pow 2 32) :
    evalCoreBuiltin .cmpMin (.int .i32 false) [u32Scalar z, u32Scalar 16] =
      .ok (u32Scalar (if z ≤ 16 then z else 16)) := by
  have h16 : 16 < Nat.pow 2 32 := by decide
  change (if decide (decodeScalar ⟨.i32, false, BitVec.ofNat 128 z⟩ ≤
        decodeScalar ⟨.i32, false, BitVec.ofNat 128 16⟩) = true then
      Except.ok (ε := FaultKind)
        (Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 z)⟩)
    else
      Except.ok (ε := FaultKind)
        (Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 16)⟩)) =
    .ok (u32Scalar (if z ≤ 16 then z else 16))
  rw [decodeScalar_u32 hz, decodeScalar_u32 h16, truncateBits_u32 hz,
    truncateBits_u32 h16]
  cases Nat.lt_or_ge 16 z with
  | inl hgt =>
    have hnle : ¬ (z ≤ 16) := Nat.not_le_of_gt hgt
    have hnleInt : ¬ (Int.ofNat z ≤ Int.ofNat 16) :=
      fun h => hnle (nat_le_of_int_le h)
    rw [decide_eq_false hnleInt, ite_prop_false hnle]
    rfl
  | inr hle =>
    have hleInt : Int.ofNat z ≤ Int.ofNat 16 := int_le_of_nat_le hle
    rw [decide_eq_true hleInt, ite_prop_true hle]
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

private theorem valid_args_u32_2 {body : Body}
    (h_params : (body.locals.drop 1).take body.argumentCount =
      [.int .i32 false, .int .i32 false])
    {args : List Val} (h : ValidEntryArgs body args) :
    ∃ a b : Nat, a < Nat.pow 2 32 ∧ b < Nat.pow 2 32 ∧
      args = [u32Scalar a, u32Scalar b] := by
  unfold ValidEntryArgs at h
  rw [h_params] at h
  cases args with
  | nil => cases h
  | cons v1 rest =>
    cases rest with
    | nil =>
      change (checkVal v1 (.int .i32 false) && false) = true at h
      rw [Bool.and_false] at h
      cases h
    | cons v2 tail =>
      cases tail with
      | cons _ _ =>
        change (checkVal v1 (.int .i32 false) &&
          (checkVal v2 (.int .i32 false) && false)) = true at h
        rw [Bool.and_false, Bool.and_false] at h
        cases h
      | nil =>
        change (checkVal v1 (.int .i32 false) &&
          (checkVal v2 (.int .i32 false) && true)) = true at h
        cases h1 : checkVal v1 (.int .i32 false) with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          cases h2 : checkVal v2 (.int .i32 false) with
          | false => rw [h2] at h; cases h
          | true =>
            let ⟨b1, hv1, ht1⟩ := checkVal_int_iff.mp h1
            let ⟨b2, hv2, ht2⟩ := checkVal_int_iff.mp h2
            have ha : b1.toNat < Nat.pow 2 32 := by
              rw [← ht1, toNat_truncateBits]
              exact Nat.mod_lt b1.toNat (by decide)
            have hb : b2.toNat < Nat.pow 2 32 := by
              rw [← ht2, toNat_truncateBits]
              exact Nat.mod_lt b2.toNat (by decide)
            refine ⟨b1.toNat, b2.toNat, ha, hb, ?_⟩
            rw [hv1, hv2]
            unfold u32Scalar
            rw [bitVec_eq_of_toNat_eq (bitVec128_toNat_u32 ha),
              bitVec_eq_of_toNat_eq (bitVec128_toNat_u32 hb)]

private theorem exec_clamp_gap (a b : Nat)
    (ha : a < Nat.pow 2 32) (hb : b < Nat.pow 2 32) (cm : CallerMemory) :
    execState Captured.program 20
      {
        frames := [{
          defId := 1
          blockIdx := 0
          stmtIdx := 0
          locals := initLocalsLoop Captured.program.bodies[1]
            [u32Scalar a, u32Scalar b] 0 Captured.program.bodies[1].locals
        }]
        callerMem := cm
      }
      (fun out =>
        match out with
        | .returned r => r.ret = u32Scalar (clampGapFn a b)
        | .unwound _ => False) := by
  have hd : a - b < Nat.pow 2 32 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  have hz : countLeadingZerosNat (a - b) 32 < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt (countLeadingZerosNat_le (a - b) 32) (by decide)
  have hout : clampGapFn a b < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt (clampGapFn_le_16 a b) (by decide)
  change execState Captured.program 20
    {
      frames := [{
        defId := 1
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live .uninit,
          .live (.scalar ⟨.i32, false, BitVec.ofNat 128 a⟩),
          .live (.scalar ⟨.i32, false, BitVec.ofNat 128 b⟩),
          .dead, .dead, .dead, .dead, .dead
        ]
      }]
      callerMem := cm
    }
    _
  -- bb0: 5 statements + callBuiltin saturatingSub
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[1])
      (bb := Captured.program.bodies[1].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u32 ha) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[1])
      (bb := Captured.program.bodies[1].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u32 hb) rfl rfl rfl)) ?_
  refine execCallBuiltin (body := Captured.program.bodies[1])
    (bb := Captured.program.bodies[1].basicBlocks[0])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (evalCoreBuiltin_saturatingSub_u32 ha hb)
    (writePlace_ok (checkVal_u32 hd) rfl rfl rfl) ?_
  -- bb1: 5 statements + callBuiltin leadingZeros
  dsimp only
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[1])
      (bb := Captured.program.bodies[1].basicBlocks[1])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u32 hd) rfl rfl rfl)) ?_
  refine execCallBuiltin (body := Captured.program.bodies[1])
    (bb := Captured.program.bodies[1].basicBlocks[1])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (evalCoreBuiltin_leadingZeros_u32 hd)
    (writePlace_ok (checkVal_u32 hz) rfl rfl rfl) ?_
  -- bb2: 1 statement + callBuiltin cmpMin
  dsimp only
  refine step_frame rfl ?_
  refine execCallBuiltin (body := Captured.program.bodies[1])
    (bb := Captured.program.bodies[1].basicBlocks[2])
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (evalCoreBuiltin_cmpMin_u32_16 hz)
    (writePlace_ok (checkVal_u32 hout) rfl rfl rfl) ?_
  -- bb3: 2 storage dead statements + return
  dsimp only
  refine step_frame rfl ?_
  refine step_frame rfl ?_
  refine done_execState rfl ?_
  rfl

private noncomputable def clampGapCallSpec : CallSpec Captured.program 1 :=
  CallSpec.ofExec Captured.program.bodies[1] rfl rfl 20
    (fun _ => True)
    (fun args retVal _ =>
      ∀ a b : Nat, a < Nat.pow 2 32 → b < Nat.pow 2 32 →
        args = [u32Scalar a, u32Scalar b] →
        retVal = u32Scalar (clampGapFn a b))
    (fun _ _ => False)
    (fun args cm hValid _ => by
      let ⟨a, b, ha, hb, hEq⟩ := valid_args_u32_2 rfl hValid
      rw [hEq]
      refine execOutcomeState_of_wpOutcomeState
        (wpOutcomeState_mono ?_ (fun _ h => h)
          (wpOutcomeState_of_execOutcomeState (exec_clamp_gap a b ha hb cm)))
      intro out hOut
      cases out with
      | returned r =>
        intro a' b' ha' hb' hArgs
        injection hArgs with h1 hRest
        injection hRest with h2 _
        have haEq : a = a' := by
          unfold u32Scalar at h1
          injection h1 with hSv
          injection hSv with _ _ hBits
          have hToNat := congrArg BitVec.toNat hBits
          rw [bitVec128_toNat_u32 ha, bitVec128_toNat_u32 ha'] at hToNat
          exact hToNat
        have hbEq : b = b' := by
          unfold u32Scalar at h2
          injection h2 with hSv
          injection hSv with _ _ hBits
          have hToNat := congrArg BitVec.toNat hBits
          rw [bitVec128_toNat_u32 hb, bitVec128_toNat_u32 hb'] at hToNat
          exact hToNat
        subst haEq
        subst hbEq
        exact hOut
      | unwound _ => exact hOut)

private theorem validateCallArgs_u32_2 {a b : Nat}
    (ha : a < Nat.pow 2 32) (hb : b < Nat.pow 2 32) :
    validateCallArgs
        [(.int .i32 false, (u32Scalar a).toSlotVal),
          (.int .i32 false, (u32Scalar b).toSlotVal)]
        [.int .i32 false, .int .i32 false] =
      .ok [u32Scalar a, u32Scalar b] := by
  have h1 : validateCallArgs
      [(.int .i32 false, (u32Scalar b).toSlotVal)]
      [.int .i32 false] = .ok [u32Scalar b] := by
    change (if !checkVal (u32Scalar b) (.int .i32 false) then
        Except.error FaultKind.unsupported
      else
        Except.ok [u32Scalar b]) = .ok [u32Scalar b]
    rw [checkVal_u32 hb]
    rfl
  change (if !checkVal (u32Scalar a) (.int .i32 false) then
      Except.error FaultKind.unsupported
    else
      match validateCallArgs
          [(.int .i32 false, (u32Scalar b).toSlotVal)]
          [.int .i32 false] with
      | .error k => Except.error k
      | .ok vs => Except.ok (u32Scalar a :: vs)) =
    .ok [u32Scalar a, u32Scalar b]
  rw [checkVal_u32 ha, h1]
  rfl

private theorem exec_selected (a b : Nat)
    (ha : a < Nat.pow 2 32) (hb : b < Nat.pow 2 32) :
    execProg (entryProgForBody Captured.program 0) 28
      { args := [u32Scalar a, u32Scalar b] }
      (fun out =>
        match out with
        | .returned r => r.ret = u32Scalar (clampGapFn a b)
        | .unwound _ => False) := by
  have h_valid : ValidEntryArgs Captured.program.bodies[0]
      [u32Scalar a, u32Scalar b] := by
    change (checkVal (u32Scalar a) (.int .i32 false) &&
      (checkVal (u32Scalar b) (.int .i32 false) && true)) = true
    rw [checkVal_u32 ha, checkVal_u32 hb]
    rfl
  have hout : clampGapFn a b < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt (clampGapFn_le_16 a b) (by decide)
  unfold execProg
  rw [initState_entryProgForBody (body := Captured.program.bodies[0]) rfl rfl
    h_valid]
  change execState Captured.program 28
    {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 0
        locals := [
          .live .uninit,
          .live (.scalar ⟨.i32, false, BitVec.ofNat 128 a⟩),
          .live (.scalar ⟨.i32, false, BitVec.ofNat 128 b⟩),
          .dead, .dead
        ]
      }]
      callerMem := ⟨[]⟩
    }
    _
  -- bb0: 4 statements + direct crate-local call to `clamp_gap` (DefId 1)
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u32 ha) rfl rfl rfl)) ?_
  refine step_frame rfl ?_
  refine step_frame
    (evalStep_assign (body := Captured.program.bodies[0])
      (bb := Captured.program.bodies[0].basicBlocks[0])
      rfl rfl rfl True.intro rfl rfl rfl rfl
      (writePlace_ok (checkVal_u32 hb) rfl rfl rfl)) ?_
  refine execCallSummary (p := Captured.program) (contFuel := 3)
    clampGapCallSpec
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (validateCallArgs_u32_2 ha hb)
    True.intro
    (fun retVal cm hPost => by
      have hRet : retVal = u32Scalar (clampGapFn a b) := hPost a b ha hb rfl
      subst hRet
      refine ⟨_, writePlace_ok (checkVal_u32 hout) rfl rfl rfl, ?_⟩
      -- bb1: 2 storage dead statements + return
      dsimp only
      refine step_frame rfl ?_
      refine step_frame rfl ?_
      refine done_execState rfl ?_
      rfl)
    (fun _ hUnw => False.elim hUnw)

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
      have same : Captured.program.bodies[0] = selected := Option.some.inj found
      subst selected
      refine ⟨found, rfl, fun args h_valid _ => ?_⟩
      let ⟨a, b, ha, hb, h_eq⟩ := valid_args_u32_2 rfl h_valid
      rw [h_eq]
      exact (wellFormed_and_spec_of_wp _ _ _ _
        (wpProg_of_execProg (exec_selected a b ha hb))).1.1
    | succ id' =>
      cases id' with
      | zero =>
        have same : Captured.program.bodies[1] = selected :=
          Option.some.inj found
        subst selected
        refine ⟨found, rfl, fun args h_valid _ => ?_⟩
        let ⟨a, b, ha, hb, h_eq⟩ := valid_args_u32_2 rfl h_valid
        rw [h_eq]
        have h_prog : execProg (entryProgForBody Captured.program 1) 20
            { args := [u32Scalar a, u32Scalar b] }
            (fun out =>
              match out with
              | .returned r => r.ret = u32Scalar (clampGapFn a b)
              | .unwound _ => False) := by
          unfold execProg
          rw [initState_entryProgForBody (body := Captured.program.bodies[1])
            rfl rfl (by
              change (checkVal (u32Scalar a) (.int .i32 false) &&
                (checkVal (u32Scalar b) (.int .i32 false) && true)) = true
              rw [checkVal_u32 ha, checkVal_u32 hb]
              rfl)]
          exact exec_clamp_gap a b ha hb ⟨[]⟩
        exact (wellFormed_and_spec_of_wp _ _ _ _
          (wpProg_of_execProg h_prog)).1.1
      | succ _ => cases found
  · intro a b
    let ⟨out, h_beh, h_post⟩ := (wellFormed_and_spec_of_wp _ _ _ _
      (wpProg_of_execProg
        (exec_selected a.toNat b.toNat a.isLt b.isLt))).2.2
    cases out with
    | unwound _ => exact False.elim h_post
    | returned r =>
      dsimp only at h_post
      refine ⟨clampGapFn a.toNat b.toNat, r.callerMem,
        clampGapFn_le_16 a.toNat b.toNat, clampGapFn_of_le, ?_⟩
      cases r with
      | mk rv cm =>
        dsimp only at h_post ⊢
        rw [h_post] at h_beh
        exact h_beh

end Proof
