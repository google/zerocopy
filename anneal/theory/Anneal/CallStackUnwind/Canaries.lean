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
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.ByteSubLens.Lens
public import Anneal.RefFrame.Frame
public import Anneal.CallStackUnwind.SpecCut

public section

/-!
# Call-Stack & Unwind Cleanup Canaries (`Anneal.CallStackUnwind.Canaries`)

End-to-end concrete verification canaries exercising `Anneal.CallStackUnwind`:

1. `f2Normal_concrete_mirWpState`: connects `Anneal.MirWp.wpState`,
   `SafeFrom`, and `wpFrameOutcome_of_mirWpState` on `bodyF2Normal`.
2. `nested3Level_normal_call_framing_sound`: 3-level nested `&mut` call framing
   (`F0 -> F1 -> F2`) over real `Trusted.MirSemantics.evalStep` and
   `LocalSlot.indirect` with sealed `@[irreducible] CallSpecCut`.
3. `callCont4_exit_matrix_sound`: 4-way `CallCont4` boundary matrix and
   multi-frame `StackReaches` abort-termination witness.
4. `nested2Level_unwind_cleanup_propagation_sound`: 2-level unwind cleanup
   ladder (`F2Panic` partial `&mut` write + panic -> `F1` cleanup drop pad ->
   `F0` cleanup assertion) without leaking normal postconditions.
5. `canary_skip_f1_cleanup_violates_f0_precond`: omitting `F1`'s cleanup pad
   aborts `F0`'s cleanup assertion and falsifies `wpFrameOutcome` for all
   `fuel : Nat`.
6. `canary_callStackUnwind_negative_fail_closed_tests`: single-cause fail-closed
   negative checks for non-cleanup targets, non-cleanup `.unwindResume`,
   out-of-frame callee lenses, diverging normal returns, and unreachable unwind.

All definitions are computable (`0` `noncomputable`, `0` `._unsafe_rec`).
Theorems compile with at most `[propext]` (inherited from
`Trusted.MirSemantics.evalStep` / `evalPrimitiveOperand`, with `0`
`Classical.choice` and `0` `Quot.sound`). See `SpecCut.lean` for the exact
theory-layer overlay scope of `StackStep` and `wpFrameOutcome`.
-/

namespace Anneal.CallStackUnwind

open Trusted.MirAst Trusted.MirSemantics
open Anneal.ByteSubLens Anneal.RefFrame

/-! ## 1. Internal Decidability and `evalStep` Indirect-Slot Helpers -/

private theorem boolFalseNeTrueC (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalseC (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandLeftC {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrueC h)
  | true => rfl

private theorem bandRightC {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrueC h)
  | true => exact h

private theorem andb_true_elim {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true :=
  ⟨bandLeftC h, bandRightC h⟩

private theorem ite_bool_trueC {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_falseC {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem natBeq_reflC (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natEq_of_beqC (a b : Nat) (h : Nat.beq a b = true) :
    a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrueC h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrueC h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBle_zero_leftC (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_transC (a b c : Nat) (h1 : Nat.ble a b = true)
    (h2 : Nat.ble b c = true) : Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_leftC c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrueC h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrueC h2)
      | succ c' => exact ih b' c' h1 h2

private theorem natAdd_zero_leftC (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBeq_zero_false_of_blt_zeroC (n : Nat)
    (h : Nat.blt 0 n = true) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (boolFalseNeTrueC h)
  | succ _ => rfl

private theorem getElem_self_length_noneC {α : Type} :
    ∀ (xs : List α), Trusted.MirSemantics.getElem? xs xs.length = none
  | [] => rfl
  | _ :: xs => getElem_self_length_noneC xs

private theorem borFalseElimC {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => exact False.elim (boolTrueNeFalseC h)
  | false => exact ⟨rfl, h⟩

/-- Canary fixture helper `optionNatBeq`. -/
@[expose] def optionNatBeq : Option Nat → Option Nat → Bool
  | none, none => true
  | none, some _ => false
  | some _, none => false
  | some a, some b => Nat.beq a b

/-- Canary fixture helper `allocByteBeq`. -/
@[expose] def allocByteBeq (a b : AllocByte) : Bool :=
  match a with
  | .uninit =>
    match b with
    | .uninit => true
    | .init _ _ => false
  | .init ba pa =>
    match b with
    | .uninit => false
    | .init bb pb => Nat.beq ba.toNat bb.toNat && optionNatBeq pa pb

/-- Canary fixture helper `bytesBeq`. -/
@[expose] def bytesBeq (xs ys : List AllocByte) : Bool :=
  (xs.foldr
    (fun x acc zs =>
      match zs with
      | [] => false
      | z :: zs' => allocByteBeq x z && acc zs')
    (fun zs =>
      match zs with
      | [] => true
      | _ :: _ => false)) ys

/-- Canary fixture helper `valIsU32`. -/
@[expose] def valIsU32 (expected : Nat) (v : Val) : Bool :=
  match v with
  | .scalar sv =>
    let widthOk :=
      match sv.width with
      | .i8 => false
      | .i16 => false
      | .i32 => true
      | .i64 => false
      | .i128 => false
      | .isize => false
    widthOk && (!sv.signed) && Nat.beq sv.bits.toNat expected
  | .ptr _ => false
  | .bool _ => false
  | .char _ => false
  | .ordering _ => false
  | .unit => false
  | .enumVal _ _ => false
  | .tuple _ => false
  | .bytes _ => false
  | .slicePtr _ _ => false
  | .rangeTo _ => false
  | .rangeFrom _ => false
  | .array _ => false

/-- Canary fixture helper `argsIsOneU32`. -/
@[expose] def argsIsOneU32 (expected : Nat) (args : List Val) : Bool :=
  match args with
  | [] => false
  | v :: rest =>
    match rest with
    | [] => valIsU32 expected v
    | _ :: _ => false

private theorem eq_of_optionNatBeq_true (a b : Option Nat)
    (h : optionNatBeq a b = true) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => cases h
  | some xa =>
    cases b with
    | none => cases h
    | some xb =>
      have hEq := natEq_of_beqC xa xb h
      rw [hEq]

private theorem bv_eq_of_toNat {w : Nat} (a b : BitVec w)
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      cases fa with
      | mk va ha =>
        cases fb with
        | mk vb hb =>
          dsimp only [BitVec.toNat] at h
          subst h
          rfl

private theorem bv_eq_ofNat {w : Nat} (a : BitVec w) (n : Nat)
    (h : a.toNat = n) : a = BitVec.ofNat w n := by
  apply bv_eq_of_toNat
  dsimp only [BitVec.toNat] at h
  dsimp only [BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat]
  rw [← h]
  exact (Nat.mod_eq_of_lt a.isLt).symm

private theorem eq_of_allocByteBeq_true (a b : AllocByte)
    (h : allocByteBeq a b = true) : a = b := by
  cases a with
  | uninit =>
    cases b with
    | uninit => rfl
    | init _ _ => cases h
  | init ba pa =>
    cases b with
    | uninit => cases h
    | init bb pb =>
      dsimp only [allocByteBeq] at h
      have hAnd := andb_true_elim h
      have hBNat := natEq_of_beqC ba.toNat bb.toNat hAnd.1
      have hB : ba = bb := by
        cases ba with
        | ofBitVec bva =>
          cases bb with
          | ofBitVec bvb =>
            dsimp only [UInt8.toNat] at hBNat
            rw [bv_eq_of_toNat bva bvb hBNat]
      rw [hB, eq_of_optionNatBeq_true pa pb hAnd.2]

private theorem eq_of_bytesBeq_true :
    ∀ (xs ys : List AllocByte), bytesBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    dsimp only [bytesBeq, List.foldr] at h
    have hAnd := andb_true_elim h
    rw [eq_of_allocByteBeq_true x y hAnd.1,
      eq_of_bytesBeq_true xs ys hAnd.2]
  | [], _ :: _, h => False.elim (by cases h)
  | _ :: _, [], h => False.elim (by cases h)

private theorem bytesBeq_refl : ∀ (xs : List AllocByte), bytesBeq xs xs = true
  | [] => rfl
  | x :: xs => by
    dsimp only [bytesBeq, List.foldr]
    cases x with
    | uninit => exact bytesBeq_refl xs
    | init b p =>
      dsimp only [allocByteBeq]
      rw [natBeq_reflC b.toNat]
      have hOpt : optionNatBeq p p = true := by
        cases p with
        | none => rfl
        | some n => exact natBeq_reflC n
      rw [hOpt]
      exact bytesBeq_refl xs

private theorem eq_of_valIsU32_true (expected : Nat) (v : Val)
    (h : valIsU32 expected v = true) :
    v = .scalar ⟨.i32, false, BitVec.ofNat 128 expected⟩ := by
  cases v with
  | scalar sv =>
    dsimp only [valIsU32] at h
    have hA1 := andb_true_elim h
    have hA2 := andb_true_elim hA1.1
    have hW : sv.width = .i32 := by
      cases hw : sv.width <;> rw [hw] at hA2 <;> first | rfl | cases hA2.1
    have hS : sv.signed = false := by
      cases hs : sv.signed <;> rw [hs] at hA2 <;> first | rfl | cases hA2.2
    have hNat := natEq_of_beqC sv.bits.toNat expected hA1.2
    have hBits := bv_eq_ofNat sv.bits expected hNat
    cases sv
    dsimp only at hW hS hBits
    subst hW hS hBits
    rfl
  | ptr _ => cases h
  | bool _ => cases h
  | char _ => cases h
  | ordering _ => cases h
  | unit => cases h
  | enumVal _ _ => cases h
  | tuple _ => cases h
  | bytes _ => cases h
  | slicePtr _ _ => cases h
  | rangeTo _ => cases h
  | rangeFrom _ => cases h
  | array _ => cases h

/-- Canary fixture helper `u32Ty`. -/
abbrev u32Ty : MirTy := .int .i32 false

/-- Canary fixture helper `mkU32Const`. -/
@[expose] def mkU32Const (n : Nat) : Operand :=
  .constant ⟨u32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Constructs a big-endian 4-byte initialized `u32` `AllocByte` slice without
provenance. -/
@[expose] def mkU32Bytes4 (b3 b2 b1 b0 : UInt8) : List AllocByte :=
  [.init b3 none, .init b2 none, .init b1 none, .init b0 none]

private theorem evalCallArgs_one_const_u32 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (n : Nat)
    (hConst : evalConstLit u32Ty (.scalar (BitVec.ofNat 128 n)) =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩)) :
    EvalCallArgs bodyLocals locals mem [mkU32Const n]
      [.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩] locals mem := by
  refine .cons ?_ .nil
  unfold evalPrimitiveOperand evalOperandToSlot mkU32Const
  dsimp only
  rw [hConst]
  rfl

private theorem evalOperandToSlot_copy_indirect (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (tyOk : MirTy → Bool)
    (id : LocalId) (ty : MirTy) (mplace : MemPlace) (layout : LayoutData)
    (bs : List AllocByte) (v : Val)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hLoc : Trusted.MirSemantics.getElem? locals id = some (.indirect mplace))
    (hTyOk : tyOk ty = true)
    (hLay : layoutOfTy ty = some layout)
    (hRead : readBytes mem mplace layout.size layout.alignLog2 = .ok bs)
    (hDec : decodeVal profileTargetEndian ty bs = .ok (some v)) :
    evalOperandToSlot bodyLocals locals mem tyOk (.copy ⟨id, []⟩) =
      .ok (ty, some v, locals, mem) := by
  unfold evalOperandToSlot
  dsimp only
  rw [hTy, hLoc]
  dsimp only
  have hOkNeg : (!tyOk ty) = false := by rw [hTyOk]; rfl
  rw [ite_bool_falseC hOkNeg]
  rw [ite_bool_falseC (rfl : (!([] : List ProjectionElem).isEmpty) = false)]
  unfold loadIndirect
  rw [hLay]
  dsimp only
  rw [hRead]
  dsimp only
  rw [hDec]

private theorem evalPrimitiveOperand_copy_indirect (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (id : LocalId) (ty : MirTy)
    (mplace : MemPlace) (layout : LayoutData) (bs : List AllocByte) (v : Val)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hLoc : Trusted.MirSemantics.getElem? locals id = some (.indirect mplace))
    (hPrim : isPrimitiveReadableTy ty = true)
    (hLay : layoutOfTy ty = some layout)
    (hRead : readBytes mem mplace layout.size layout.alignLog2 = .ok bs)
    (hDec : decodeVal profileTargetEndian ty bs = .ok (some v)) :
    evalPrimitiveOperand bodyLocals locals mem (.copy ⟨id, []⟩) =
      .ok (v, locals, mem) := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_copy_indirect bodyLocals locals mem
    isPrimitiveReadableTy id ty mplace layout bs v hTy hLoc hPrim hLay hRead
    hDec]
  dsimp only
  have hPrimNeg : (!isPrimitiveReadableTy ty) = false := by rw [hPrim]; rfl
  rw [ite_bool_falseC hPrimNeg]

private theorem evalRvalue_use_copy_indirect (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (id : LocalId)
    (dstTy : MirTy) (mplace : MemPlace) (layout : LayoutData)
    (bs : List AllocByte) (v : Val)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some dstTy)
    (hLoc : Trusted.MirSemantics.getElem? locals id = some (.indirect mplace))
    (hEq : MirTy.beq dstTy dstTy = true)
    (hLay : layoutOfTy dstTy = some layout)
    (hRead : readBytes mem mplace layout.size layout.alignLog2 = .ok bs)
    (hDec : decodeVal profileTargetEndian dstTy bs = .ok (some v)) :
    evalRvalue bodyLocals locals mem dstTy (.use (.copy ⟨id, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalue
  dsimp only
  rw [evalOperandToSlot_copy_indirect bodyLocals locals mem
    (fun srcTy => MirTy.beq srcTy dstTy) id dstTy mplace layout bs v hTy hLoc
    hEq hLay hRead hDec]
  dsimp only
  have hNeg : (!(MirTy.beq dstTy dstTy)) = false := by rw [hEq]; rfl
  rw [ite_bool_falseC hNeg]

private theorem evalRvalue_use_constant (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (dstTy : MirTy)
    (c : ConstOperand) (v : Val)
    (hConst : evalConstLit c.ty c.lit = .ok v)
    (hEq : MirTy.beq c.ty dstTy = true) :
    evalRvalue bodyLocals locals mem dstTy (.use (.constant c)) =
      .ok (v, locals, mem) := by
  unfold evalRvalue evalOperandToSlot
  dsimp only
  rw [hConst]
  dsimp only
  have hNeg : (!(MirTy.beq c.ty dstTy)) = false := by rw [hEq]; rfl
  rw [ite_bool_falseC hNeg]

private theorem evalRvalue_binaryOp_ok (bodyLocals : List MirTy)
    (locals locals₁ locals₂ : List LocalSlot)
    (mem mem₁ mem₂ : MemoryState) (dstTy : MirTy) (op : BinOp)
    (lhs rhs : Operand) (vL vR res : Val)
    (hL : evalPrimitiveOperand bodyLocals locals mem lhs =
      .ok (vL, locals₁, mem₁))
    (hR : evalPrimitiveOperand bodyLocals locals₁ mem₁ rhs =
      .ok (vR, locals₂, mem₂))
    (hBin : evalBinOp op vL vR = .ok res) :
    evalRvalue bodyLocals locals mem dstTy (.binaryOp op lhs rhs) =
      .ok (res, locals₂, mem₂) := by
  unfold evalRvalue
  dsimp only
  rw [hL]
  dsimp only
  rw [hR]
  dsimp only
  rw [hBin]

private theorem writePlace_indirect_ok (locals : List LocalSlot)
    (mem mem' : MemoryState) (dstId : LocalId) (dstTy : MirTy) (v : Val)
    (mplace : MemPlace) (layout : LayoutData) (bs : List AllocByte)
    (hChk : checkVal v dstTy = true)
    (hLoc : Trusted.MirSemantics.getElem? locals dstId =
      some (.indirect mplace))
    (hLay : layoutOfTy dstTy = some layout)
    (hEnc : encodeVal profileTargetEndian dstTy v = .ok bs)
    (hWr : writeBytes mem mplace layout.alignLog2 bs = .ok mem') :
    writePlace locals mem dstId dstTy v = .ok (locals, mem') := by
  unfold writePlace
  have hNeg : (!checkVal v dstTy) = false := by rw [hChk]; rfl
  rw [ite_bool_falseC hNeg, hLoc]
  dsimp only
  unfold storeIndirect
  rw [hLay]
  dsimp only
  rw [hEnc]
  dsimp only
  rw [hWr]

private theorem writePlace_immediate_ok (locals locals' : List LocalSlot)
    (mem : MemoryState) (dstId : LocalId) (dstTy : MirTy) (v : Val)
    (prev : Option Val) (hChk : checkVal v dstTy = true)
    (hLoc : Trusted.MirSemantics.getElem? locals dstId = some (.immediate prev))
    (hSet : Trusted.MirSemantics.setElem? locals dstId (.immediate (some v)) =
      some locals') :
    writePlace locals mem dstId dstTy v = .ok (locals', mem) := by
  unfold writePlace
  have hNeg : (!checkVal v dstTy) = false := by rw [hChk]; rfl
  rw [ite_bool_falseC hNeg, hLoc]
  dsimp only
  rw [hSet]

private theorem evalStep_assign_ok (body : Body) (bb : BasicBlock)
    (frame : FrameState) (cm : CallerMemory) (mem mem₁ mem₂ : MemoryState)
    (dstId : LocalId) (dstTy : MirTy) (rv : Rvalue) (v : Val)
    (locs₁ locs₂ : List LocalSlot)
    (hDef : frame.defId = 0)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dstId, []⟩ rv))
    (hTy : Trusted.MirSemantics.getElem? body.locals dstId = some dstTy)
    (hRv : evalRvalue body.locals frame.locals mem dstTy rv =
      .ok (v, locs₁, mem₁))
    (hWr : writePlace locs₁ mem₁ dstId dstTy v = .ok (locs₂, mem₂))
    (hSys : frame.sysrootOp? = none := by rfl) :
    evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs₂ }],
        cm, mem₂⟩ := by
  unfold evalStep
  dsimp only
  have hBody :
      activeFrameBody (Anneal.MirWp.bodyProg body) frame = some body := by
    unfold activeFrameBody
    rw [hSys, hDef]
    rfl
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [hStmt]
  dsimp only
  unfold evalStatement
  dsimp only
  rw [hTy]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hWr]
  rfl

private theorem evalStep_return_immediate (body : Body) (bb : BasicBlock)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState) (rv : Val)
    (hDef : frame.defId = 0)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hIdx : frame.stmtIdx = bb.statements.length)
    (hClean : bb.cleanup = false)
    (hTerm : bb.terminator = .return_)
    (hLoc0 : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some rv)))
    (hSys : frame.sysrootOp? = none := by rfl) :
    evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ =
      .done (.returned ⟨rv, cm⟩) := by
  unfold evalStep
  dsimp only
  have hBody :
      activeFrameBody (Anneal.MirWp.bodyProg body) frame = some body := by
    unfold activeFrameBody
    rw [hSys, hDef]
    rfl
  rw [hBody]
  dsimp only
  rw [hBb]
  dsimp only
  rw [hIdx, getElem_self_length_noneC bb.statements]
  dsimp only
  rw [ite_bool_trueC (natBeq_reflC bb.statements.length)]
  unfold evalTerminator
  dsimp only
  rw [hTerm]
  dsimp only
  rw [ite_bool_falseC hClean, hLoc0]

private theorem evalPrimitiveOperand_copy_immediate (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (id : LocalId) (ty : MirTy)
    (v : Val)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals id = some ty)
    (hLoc : Trusted.MirSemantics.getElem? locals id =
      some (.immediate (some v)))
    (hPrim : isPrimitiveReadableTy ty = true) :
    evalPrimitiveOperand bodyLocals locals mem (.copy ⟨id, []⟩) =
      .ok (v, locals, mem) := by
  unfold evalPrimitiveOperand evalOperandToSlot
  dsimp only
  rw [hTy, hLoc]
  dsimp only
  rw [ite_bool_falseC (rfl : (!([] : List ProjectionElem).isEmpty) = false)]
  dsimp only
  have hNeg : (!isPrimitiveReadableTy ty) = false := by rw [hPrim]; rfl
  rw [ite_bool_falseC hNeg]

private theorem isInBounds_4_of_8 (a : Allocation)
    (h : isInBounds a 0 8 = true) :
    isInBounds a 0 4 = true ∧ isInBounds a 4 4 = true := by
  dsimp only [isInBounds] at h
  dsimp only [isInBounds]
  rw [natAdd_zero_leftC] at h
  rw [natAdd_zero_leftC]
  exact ⟨natBle_transC 4 8 a.bytes.length rfl h, h⟩

private theorem list_take_take_4_of_8 {α : Type} :
    ∀ (xs : List α), (xs.take 8).take 4 = xs.take 4 := by
  intro xs
  cases xs with
  | nil => rfl
  | cons a0 xs1 =>
    cases xs1 with
    | nil => rfl
    | cons a1 xs2 =>
      cases xs2 with
      | nil => rfl
      | cons a2 xs3 =>
        cases xs3 with
        | nil => rfl
        | cons a3 xs4 => rfl

private theorem list_drop4_take4_of_take8 {α : Type} :
    ∀ (xs : List α), ((xs.take 8).drop 4).take 4 = (xs.drop 4).take 4 := by
  intro xs
  cases xs with
  | nil => rfl
  | cons a0 xs1 =>
    cases xs1 with
    | nil => rfl
    | cons a1 xs2 =>
      cases xs2 with
      | nil => rfl
      | cons a2 xs3 =>
        cases xs3 with
        | nil => rfl
        | cons a3 xs4 =>
          cases xs4 with
          | nil => rfl
          | cons b0 ys1 =>
            cases ys1 with
            | nil => rfl
            | cons b1 ys2 =>
              cases ys2 with
              | nil => rfl
              | cons b2 ys3 =>
                cases ys3 with
                | nil => rfl
                | cons b3 _ => rfl

private theorem list_take8_eq_4_4 {α : Type} (xs : List α) :
    xs.take 8 = xs.take 4 ++ (xs.drop 4).take 4 := by
  cases xs with
  | nil => rfl
  | cons x0 r1 =>
    cases r1 with
    | nil => rfl
    | cons x1 r2 =>
      cases r2 with
      | nil => rfl
      | cons x2 r3 =>
        cases r3 with
        | nil => rfl
        | cons x3 r4 => rfl

private theorem readBytes_sub4_take_of_readBytes_8 (m : MemoryState)
    (allocId : AllocId) (bs8 : List AllocByte)
    (hRead8 : readBytes m ⟨allocId, 0⟩ 8 2 = .ok bs8) :
    readBytes m ⟨allocId, 0⟩ 4 2 = .ok (bs8.take 4) := by
  unfold readBytes at hRead8
  dsimp only at hRead8
  cases hFind : findAllocation allocId m.allocations with
  | none => rw [hFind] at hRead8; cases hRead8
  | some a =>
    rw [hFind] at hRead8
    dsimp only at hRead8
    rw [ite_bool_falseC (rfl : Nat.beq 8 0 = false)] at hRead8
    cases hCond : (!a.live || !isInBounds a 0 8 || !isAligned a 0 2) with
    | true => rw [ite_bool_trueC hCond] at hRead8; cases hRead8
    | false =>
      rw [ite_bool_falseC hCond] at hRead8
      injection hRead8 with hBsEq
      have hG1 := borFalseElimC hCond
      have hG2 := borFalseElimC hG1.1
      have hNotLive : a.live = true := by
        cases hL : a.live with
        | true => rfl
        | false => rw [hL] at hG2; exact False.elim (boolTrueNeFalseC hG2.1)
      have hNotBnd : isInBounds a 0 8 = true := by
        cases hB : isInBounds a 0 8 with
        | true => rfl
        | false => rw [hB] at hG2; exact False.elim (boolTrueNeFalseC hG2.2)
      have hNotAl : isAligned a 0 2 = true := by
        cases hA : isAligned a 0 2 with
        | true => rfl
        | false => rw [hA] at hG1; exact False.elim (boolTrueNeFalseC hG1.2)
      have hBnd4 := (isInBounds_4_of_8 a hNotBnd).1
      have hCond4 : (!a.live || !isInBounds a 0 4 || !isAligned a 0 2) =
          false := by
        rw [hNotLive, hBnd4, hNotAl]; rfl
      unfold readBytes
      dsimp only
      rw [hFind]
      dsimp only
      rw [ite_bool_falseC (rfl : Nat.beq 4 0 = false), ite_bool_falseC hCond4,
        ← hBsEq, list_take_take_4_of_8 (a.bytes.drop 0)]

private theorem readBytes_sub4_drop4_of_readBytes_8 (m : MemoryState)
    (allocId : AllocId) (bs8 : List AllocByte)
    (hRead8 : readBytes m ⟨allocId, 0⟩ 8 2 = .ok bs8) :
    readBytes m ⟨allocId, 4⟩ 4 2 = .ok ((bs8.drop 4).take 4) := by
  unfold readBytes at hRead8
  dsimp only at hRead8
  cases hFind : findAllocation allocId m.allocations with
  | none => rw [hFind] at hRead8; cases hRead8
  | some a =>
    rw [hFind] at hRead8
    dsimp only at hRead8
    rw [ite_bool_falseC (rfl : Nat.beq 8 0 = false)] at hRead8
    cases hCond : (!a.live || !isInBounds a 0 8 || !isAligned a 0 2) with
    | true => rw [ite_bool_trueC hCond] at hRead8; cases hRead8
    | false =>
      rw [ite_bool_falseC hCond] at hRead8
      injection hRead8 with hBsEq
      have hG1 := borFalseElimC hCond
      have hG2 := borFalseElimC hG1.1
      have hNotLive : a.live = true := by
        cases hL : a.live with
        | true => rfl
        | false => rw [hL] at hG2; exact False.elim (boolTrueNeFalseC hG2.1)
      have hNotBnd : isInBounds a 0 8 = true := by
        cases hB : isInBounds a 0 8 with
        | true => rfl
        | false => rw [hB] at hG2; exact False.elim (boolTrueNeFalseC hG2.2)
      have hNotAl : isAligned a 0 2 = true := by
        cases hA : isAligned a 0 2 with
        | true => rfl
        | false => rw [hA] at hG1; exact False.elim (boolTrueNeFalseC hG1.2)
      have hBndHi := (isInBounds_4_of_8 a hNotBnd).2
      have hAlHi : isAligned a 4 2 = true := by
        dsimp only [isAligned] at hNotAl
        dsimp only [isAligned]
        have hAnd := andb_true_elim hNotAl
        rw [hAnd.1]
        rfl
      have hCondHi : (!a.live || !isInBounds a 4 4 || !isAligned a 4 2) =
          false := by
        rw [hNotLive, hBndHi, hAlHi]; rfl
      unfold readBytes
      dsimp only
      rw [hFind]
      dsimp only
      rw [ite_bool_falseC (rfl : Nat.beq 4 0 = false), ite_bool_falseC hCondHi,
        ← hBsEq, list_drop4_take4_of_take8 (a.bytes.drop 0)]
      rfl

private theorem readBytes_8_eq_append_of_4_4 (m : MemoryState)
    (allocId : AllocId) (lo hi bs8 : List AllocByte)
    (hLo : readBytes m ⟨allocId, 0⟩ 4 2 = .ok lo)
    (hHi : readBytes m ⟨allocId, 4⟩ 4 2 = .ok hi)
    (h8 : readBytes m ⟨allocId, 0⟩ 8 2 = .ok bs8) :
    bs8 = lo ++ hi := by
  unfold readBytes at hLo hHi h8
  dsimp only at hLo hHi h8
  cases hFind : findAllocation allocId m.allocations with
  | none => rw [hFind] at h8; cases h8
  | some a =>
    rw [hFind] at hLo hHi h8
    dsimp only at hLo hHi h8
    rw [ite_bool_falseC (rfl : Nat.beq 4 0 = false)] at hLo hHi
    rw [ite_bool_falseC (rfl : Nat.beq 8 0 = false)] at h8
    cases hC0 : (!a.live || !isInBounds a 0 4 || !isAligned a 0 2) with
    | true => rw [ite_bool_trueC hC0] at hLo; cases hLo
    | false =>
      rw [ite_bool_falseC hC0] at hLo
      cases hC4 : (!a.live || !isInBounds a 4 4 || !isAligned a 4 2) with
      | true => rw [ite_bool_trueC hC4] at hHi; cases hHi
      | false =>
        rw [ite_bool_falseC hC4] at hHi
        cases hC8 : (!a.live || !isInBounds a 0 8 || !isAligned a 0 2) with
        | true => rw [ite_bool_trueC hC8] at h8; cases h8
        | false =>
          rw [ite_bool_falseC hC8] at h8
          injection hLo with hLoEq
          injection hHi with hHiEq
          injection h8 with h8Eq
          rw [← h8Eq, ← hLoEq, ← hHiEq]
          exact list_take8_eq_4_4 a.bytes

private theorem readBytes_of_byteSubLensGet (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) (hGet : byteSubLensGet L m = some bs) :
    readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 = .ok bs := by
  have hRefl := updatesOnly_refl L m bs hGet
  cases lens_valid_after_updatesOnly L m m hRefl with
  | intro bs1 hL =>
    cases hL with
    | intro _ hA =>
      have hEq := Eq.trans hA.1.symm hGet
      injection hEq with hBsEq
      rw [← hBsEq]
      exact hA.2.1

private theorem byteSubLensGet_eq_some_of_readBytes (L : ByteSubLens)
    (m : MemoryState) (a : Allocation) (bs : List AllocByte)
    (hPos : Nat.blt 0 L.size = true)
    (hFind : findAllocation L.allocId m.allocations = some a)
    (hMut : a.mutability = .mut)
    (hRead : readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 = .ok bs) :
    byteSubLensGet L m = some bs := by
  rw [byteSubLensGet_eq_mir, hPos]
  dsimp only
  rw [hFind]
  dsimp only
  rw [hMut]
  dsimp only [mutabilityIsMut]
  rw [hRead]

private theorem byteSubLensGet_of_valid (L : ByteSubLens) (m : MemoryState)
    (a : Allocation) (hPos : Nat.blt 0 L.size = true)
    (hFind : findAllocation L.allocId m.allocations = some a)
    (hMut : a.mutability = .mut) (hLive : a.live = true)
    (hBnd : isInBounds a L.offset L.size = true)
    (hAl : isAligned a L.offset L.alignLog2 = true) :
    ∃ bs, byteSubLensGet L m = some bs ∧
      readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 = .ok bs := by
  have hRead : readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 =
      .ok ((a.bytes.drop L.offset).take L.size) := by
    dsimp only [readBytes]
    rw [hFind]
    dsimp only
    rw [natBeq_zero_false_of_blt_zeroC L.size hPos, ite_bool_falseC rfl]
    have hGuard : (!a.live || !isInBounds a L.offset L.size ||
        !isAligned a L.offset L.alignLog2) = false := by
      rw [hLive, hBnd, hAl]; rfl
    rw [ite_bool_falseC hGuard]
  exact ⟨(a.bytes.drop L.offset).take L.size,
    byteSubLensGet_eq_some_of_readBytes L m a _ hPos hFind hMut hRead, hRead⟩

/-- Canary fixture helper `bytesBeq4BE`. -/
@[expose] def bytesBeq4BE (w3 w2 w1 w0 : UInt8) (bs : List AllocByte) : Bool :=
  bytesBeq (bs.take 4) (mkU32Bytes4 w3 w2 w1 w0)

/-! ## 2. 3-Level Nested `&mut` Call-Stack Framing (`F0 -> F1 -> F2`) -/

/-- Callee `DefId`s and hierarchical sub-lenses for `F0 -> F1 -> F2`. -/
@[expose] def defIdF1Normal : DefId := 101
@[expose] def defIdF2Normal : DefId := 102
@[expose] def lensF0 : ByteSubLens := ⟨1, 0, 16, 3⟩
@[expose] def lensF1 : ByteSubLens := ⟨1, 0, 8, 2⟩
@[expose] def lensF2 : ByteSubLens := ⟨1, 0, 4, 2⟩
@[expose] def lensF1Hi : ByteSubLens := ⟨1, 4, 4, 2⟩
@[expose] def lensF0Tail : ByteSubLens := ⟨1, 8, 8, 3⟩

/-- Canary fixture helper `argSlot0`. -/
@[expose] def argSlot0 : List Val → LocalSlot
  | v :: _ => .immediate (some v)
  | [] => .immediate none

/-- Entry locals initializer for leaf callee `F2`. -/
@[expose] def mkLocalsF2 (mutLens : ByteSubLens) (args : List Val) : List
    LocalSlot :=
  [.immediate none, argSlot0 args, .indirect ⟨mutLens.allocId, mutLens.offset⟩,
   .immediate none]

/-- Leaf callee `F2`: adds arg `_1` into indirect `&mut` slot `[0..4)` and
returns the updated `u32`. -/
@[expose] def bodyF2Normal : Body :=
  { argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty, u32Ty]
    basicBlocks :=
      [{ statements :=
          [.assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)),
           .assign ⟨2, []⟩ (.use (.copy ⟨3, []⟩)),
           .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))]
         terminator := .return_
         cleanup := false }] }

/-- Implementation bundle for `F2`. -/
@[expose] def implF2Normal : CallImplBundle :=
  { body := bodyF2Normal, fuel := 5, mkLocals := mkLocalsF2 }

/-- Pure-data contract for `F2` over `lensF2` (`[0..4)`). -/
@[expose] def specF2Normal : CallSpec :=
  { calleeDefId := defIdF2Normal
    mutLens := lensF2
    precondBool := fun preBs args =>
      bytesBeq preBs (mkU32Bytes4 0x10 0x00 0x00 0x01) &&
        argsIsOneU32 0x22000041 args
    ensuresNormalBool := fun _ retVal postBs _ =>
      valIsU32 0x32000042 retVal &&
        bytesBeq postBs (mkU32Bytes4 0x32 0x00 0x00 0x42)
    ensuresUnwindBool := fun _ _ _ => false
    canNormal := true
    canUnwind := false }

/-- Entry locals initializer for middle caller `F1`. -/
@[expose] def mkLocalsF1 (mutLens : ByteSubLens) (args : List Val) : List
    LocalSlot :=
  [.immediate none, argSlot0 args, .indirect ⟨mutLens.allocId, mutLens.offset⟩,
   .indirect ⟨mutLens.allocId, mutLens.offset + 4⟩, .immediate none,
   .immediate none]

/-- Middle caller `F1` parameterized by `calleeF2`, with a cleanup drop pad
stamping `[4..8) := 0xDEADF101` before `.unwindResume`. -/
@[expose] def mkBodyF1 (calleeF2 : DefId) : Body :=
  { argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
    basicBlocks :=
      [{ statements :=
          [.assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))]
         terminator := .call calleeF2 [mkU32Const 0x22000041] ⟨4, []⟩
           (some 1) (.cleanup 2)
         cleanup := false },
       { statements :=
          [.assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (mkU32Const 6)),
           .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨4, []⟩)),
           .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.copy ⟨3, []⟩))]
         terminator := .return_
         cleanup := false },
       { statements :=
          [.assign ⟨3, []⟩ (.use (mkU32Const 0xDEADF101))]
         terminator := .unwindResume
         cleanup := true }] }

@[expose] def bodyF1Normal : Body := mkBodyF1 defIdF2Normal

@[expose] def implF1Normal : CallImplBundle :=
  { body := bodyF1Normal, fuel := 8, mkLocals := mkLocalsF1 }

@[expose] def specF1Normal : CallSpec :=
  { calleeDefId := defIdF1Normal
    mutLens := lensF1
    precondBool := fun preBs args =>
      bytesBeq4BE 0x10 0x00 0x00 0x01 preBs && argsIsOneU32 0x10000010 args
    ensuresNormalBool := fun _ retVal postBs _ =>
      valIsU32 0x8400009B retVal &&
        bytesBeq postBs
          (mkU32Bytes4 0x32 0x00 0x00 0x42 ++
            mkU32Bytes4 0x20 0x00 0x00 0x17)
    ensuresUnwindBool := fun _ _ _ => false
    canNormal := true
    canUnwind := false }

/-- Entry locals initializer for top caller `F0`. -/
@[expose] def mkLocalsF0 (mutLens : ByteSubLens) : List LocalSlot :=
  [.immediate none, .indirect ⟨mutLens.allocId, mutLens.offset⟩,
   .indirect ⟨mutLens.allocId, mutLens.offset + 4⟩, .immediate none,
   .immediate none, .immediate none]

/-- Top caller `F0` parameterized by `calleeF1`, asserting `[4..8) ==
0xDEADF101` inside its cleanup pad before resuming unwind. -/
@[expose] def mkBodyF0 (calleeF1 : DefId) : Body :=
  { argumentCount := 0
    locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, MirTy.bool]
    basicBlocks :=
      [{ statements :=
          [.assign ⟨1, []⟩ (.use (mkU32Const 0x10000001))]
         terminator := .call calleeF1 [mkU32Const 0x10000010] ⟨3, []⟩
           (some 1) (.cleanup 2)
         cleanup := false },
       { statements :=
          [.assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)),
           .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩) (.copy ⟨3, []⟩))]
         terminator := .return_
         cleanup := false },
       { statements :=
          [.assign ⟨5, []⟩
            (.binaryOp .eq (.copy ⟨2, []⟩) (mkU32Const 0xDEADF101))]
         terminator := .assert (.copy ⟨5, []⟩) true .boundsCheck 3 .terminate
         cleanup := true },
       { statements :=
          [.assign ⟨4, []⟩ (.use (.copy ⟨1, []⟩))]
         terminator := .unwindResume
         cleanup := true }] }

@[expose] def bodyF0Normal : Body := mkBodyF0 defIdF1Normal

/-- Seals `F2` behind `@[irreducible] CallSpecCut` (`[propext]`). -/
theorem seal_f2Normal_callSpecCut : CallSpecCut [] implF2Normal specF2Normal :=
  by
  apply seal_callSpecCut
  intro m0 cm0 args
  dsimp only [specF2Normal]
  cases hGet : byteSubLensGet lensF2 m0 with
  | none => exact True.intro
  | some preBs =>
    dsimp only
    intro hPre
    have hAnd := andb_true_elim hPre
    have hPreBsEq : preBs = mkU32Bytes4 0x10 0x00 0x00 0x01 :=
      eq_of_bytesBeq_true preBs _ hAnd.1
    have hArgsEx : ∃ v, args = [v] ∧ valIsU32 0x22000041 v = true := by
      cases args with
      | nil => cases hAnd.2
      | cons v rest =>
        cases rest with
        | cons _ _ => cases hAnd.2
        | nil => exact ⟨v, rfl, hAnd.2⟩
    cases hArgsEx with
    | intro vArg hVArg =>
      have hArgEq := hVArg.1
      have hVArgVal := eq_of_valIsU32_true 0x22000041 vArg hVArg.2
      have hRefl0 := updatesOnly_refl lensF2 m0 preBs hGet
      cases lens_valid_after_updatesOnly lensF2 m0 m0 hRefl0 with
      | intro bs0 hL0 =>
        cases hL0 with
        | intro a0 hA0 =>
          have hRead0 : readBytes m0 ⟨1, 0⟩ 4 2 =
              .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
            rw [← hPreBsEq]
            exact readBytes_of_byteSubLensGet lensF2 m0 preBs hGet
          have hLocsEq : implF2Normal.mkLocals lensF2 args =
              [.immediate none,
               .immediate (some (.scalar ⟨.i32, false,
                 BitVec.ofNat 128 0x22000041⟩)),
               .indirect ⟨1, 0⟩, .immediate none] := by
            rw [hArgEq, hVArgVal]; rfl
          have hStep1 : evalStep (Anneal.MirWp.bodyProg bodyF2Normal) 0
              ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
                  locals := implF2Normal.mkLocals lensF2 args }], cm0, m0⟩ =
              .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x32000042⟩))] }], cm0, m0⟩ := by
            rw [hLocsEq]
            refine evalStep_assign_ok bodyF2Normal _ _ cm0 m0 m0 m0 3 u32Ty
              (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))
              (.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩)
              [.immediate none,
               .immediate (some (.scalar ⟨.i32, false,
                 BitVec.ofNat 128 0x22000041⟩)),
               .indirect ⟨1, 0⟩, .immediate none]
              _ rfl rfl rfl rfl ?_ ?_
            · refine evalRvalue_binaryOp_ok _ _
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩, .immediate none]
                _ m0 m0 m0 u32Ty .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x22000041⟩) _ ?_ ?_ rfl
              · exact evalPrimitiveOperand_copy_indirect _ _ m0 2 u32Ty ⟨1, 0⟩
                  ⟨4, 2⟩ _ _ rfl rfl rfl rfl hRead0 rfl
              · exact evalPrimitiveOperand_copy_immediate _ _ m0 1 u32Ty _
                  rfl rfl rfl
            · exact writePlace_immediate_ok _ _ m0 3 u32Ty _ none rfl rfl rfl
          cases byteSubLensPut_eq_some_of_valid lensF2 m0
              (mkU32Bytes4 0x32 0x00 0x00 0x42) a0 rfl rfl hA0.2.2.1
              hA0.2.2.2.1 hA0.2.2.2.2.1 hA0.2.2.2.2.2.1 hA0.2.2.2.2.2.2 with
          | intro m1 hPut1 =>
            have hStep2 : evalStep (Anneal.MirWp.bodyProg bodyF2Normal) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩))] }], cm0, m0⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 2, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩))] }], cm0, m1⟩ := by
              refine evalStep_assign_ok bodyF2Normal _ _ cm0 m0 m0 m1 2 u32Ty
                (.use (.copy ⟨3, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x32000042⟩))]
                _ rfl rfl rfl rfl ?_ ?_
              · unfold evalRvalue evalOperandToSlot
                dsimp only
                rfl
              · exact writePlace_indirect_ok _ m0 m1 2 u32Ty _ ⟨1, 0⟩ ⟨4, 2⟩
                  (mkU32Bytes4 0x32 0x00 0x00 0x42) rfl rfl rfl rfl hPut1.2.1
            have hStep3 : evalStep (Anneal.MirWp.bodyProg bodyF2Normal) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 2, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩))] }], cm0, m1⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 3, locals :=
                  [.immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩))] }], cm0, m1⟩ := by
              refine evalStep_assign_ok bodyF2Normal _ _ cm0 m1 m1 m1 0 u32Ty
                (.use (.copy ⟨2, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x32000042⟩))]
                _ rfl rfl rfl rfl ?_ ?_
              · exact evalRvalue_use_copy_indirect _ _ m1 2 u32Ty ⟨1, 0⟩ ⟨4, 2⟩
                  _ _ rfl rfl rfl rfl hPut1.2.2.1 rfl
              · exact writePlace_immediate_ok _ _ m1 0 u32Ty _ none rfl rfl rfl
            have hStep4 : evalStep (Anneal.MirWp.bodyProg bodyF2Normal) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 3, locals :=
                  [.immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x32000042⟩))] }], cm0, m1⟩ =
                .done (.returned ⟨.scalar ⟨.i32, false,
                  BitVec.ofNat 128 0x32000042⟩, cm0⟩) :=
              evalStep_return_immediate bodyF2Normal _ _ cm0 m1 _
                rfl rfl rfl rfl rfl rfl
            dsimp only [implF2Normal]
            refine wpFrameOutcome_stmt_step lensF2 (calleeLookup [])
              bodyF2Normal 4 _ cm0 m0 _ _ _ rfl rfl hStep1 ?_
            refine wpFrameOutcome_stmt_step lensF2 (calleeLookup [])
              bodyF2Normal 3 _ cm0 m0 _ _ _ rfl rfl hStep2 ?_
            refine wpFrameOutcome_stmt_step lensF2 (calleeLookup [])
              bodyF2Normal 2 _ cm0 m1 _ _ _ rfl rfl hStep3 ?_
            refine wpFrameOutcome_return_step lensF2 (calleeLookup [])
              bodyF2Normal 1 _ cm0 m1 _ _ _ rfl rfl rfl hStep4 ?_
            exact ⟨rfl, updatesOnly_of_put lensF2 m0 m1
              (mkU32Bytes4 0x32 0x00 0x00 0x42) hPut1.1,
              mkU32Bytes4 0x32 0x00 0x00 0x42, hPut1.2.2.2.1, rfl⟩

/-- Seals `F1` against `specF2Normal` only (never inspects `bodyF2Normal`,
`[propext]`). -/
theorem seal_f1Normal_callSpecCut :
    CallSpecCut [specF2Normal] implF1Normal specF1Normal := by
  apply seal_callSpecCut
  intro m0 cm0 args
  dsimp only [specF1Normal]
  cases hGet8 : byteSubLensGet lensF1 m0 with
  | none => exact True.intro
  | some preBs =>
    dsimp only
    intro hPre
    have hAnd := andb_true_elim hPre
    have hPre4 : preBs.take 4 = mkU32Bytes4 0x10 0x00 0x00 0x01 :=
      eq_of_bytesBeq_true (preBs.take 4) _ hAnd.1
    have hArgsEx : ∃ v, args = [v] ∧ valIsU32 0x10000010 v = true := by
      cases args with
      | nil => cases hAnd.2
      | cons v rest =>
        cases rest with
        | cons _ _ => cases hAnd.2
        | nil => exact ⟨v, rfl, hAnd.2⟩
    cases hArgsEx with
    | intro vArg hVArg =>
      have hArgEq := hVArg.1
      have hVArgVal := eq_of_valIsU32_true 0x10000010 vArg hVArg.2
      have hRead0 : readBytes m0 ⟨1, 0⟩ 4 2 =
          .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
        rw [← hPre4]
        exact readBytes_sub4_take_of_readBytes_8 m0 1 preBs
          (readBytes_of_byteSubLensGet lensF1 m0 preBs hGet8)
      have hRefl0 := updatesOnly_refl lensF1 m0 preBs hGet8
      cases lens_valid_after_updatesOnly lensF1 m0 m0 hRefl0 with
      | intro bs0 hL0 =>
        cases hL0 with
        | intro a0 hA0 =>
          have hBnd4Hi := (isInBounds_4_of_8 a0 hA0.2.2.2.2.2.1).2
          cases byteSubLensPut_eq_some_of_valid lensF1Hi m0
              (mkU32Bytes4 0x20 0x00 0x00 0x11) a0 rfl rfl hA0.2.2.1
              hA0.2.2.2.1 hA0.2.2.2.2.1 hBnd4Hi hA0.2.2.2.2.2.2 with
          | intro m1 hPutHi =>
            have hUpdHi1 : UpdatesOnly lensF1 m0 m1 :=
              updatesOnly_mono_sublens lensF1Hi lensF1 m0 m1 rfl ⟨preBs, hGet8⟩
                (updatesOnly_of_put lensF1Hi m0 m1 _ hPutHi.1)
            have hReadLo1 : readBytes m1 ⟨1, 0⟩ 4 2 =
                .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
              rw [← hRead0]
              exact (hPutHi.2.2.2.2 lensF2 rfl).2
            have hLocs0 : implF1Normal.mkLocals lensF1 args =
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x10000010⟩)),
                 .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                 .immediate none] := by
              rw [hArgEq, hVArgVal]; rfl
            have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyF1Normal) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
                    locals := implF1Normal.mkLocals lensF1 args }], cm0, m0⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x10000010⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                   .immediate none] }], cm0, m1⟩ := by
              rw [hLocs0]
              refine evalStep_assign_ok bodyF1Normal _ _ cm0 m0 m0 m1 3 u32Ty
                (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000011⟩)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x10000010⟩)),
                 .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                 .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · refine evalRvalue_binaryOp_ok _ _
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x10000010⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                   .immediate none]
                  _ m0 m0 m0 u32Ty .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩) _ ?_ ?_
                  rfl
                · exact evalPrimitiveOperand_copy_indirect _ _ m0 2 u32Ty
                    ⟨1, 0⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hRead0 rfl
                · exact evalPrimitiveOperand_copy_immediate _ _ m0 1 u32Ty _
                    rfl rfl rfl
              · exact writePlace_indirect_ok _ m0 m1 3 u32Ty _ ⟨1, 4⟩ ⟨4, 2⟩ _
                  rfl rfl rfl rfl hPutHi.2.1
            cases lens_valid_after_updatesOnly lensF1 m0 m1 hUpdHi1 with
            | intro bs1 hL1 =>
              cases hL1 with
              | intro a1 hA1 =>
                have hGetPreF2 : byteSubLensGet lensF2 m1 =
                    some (mkU32Bytes4 0x10 0x00 0x00 0x01) :=
                  byteSubLensGet_eq_some_of_readBytes lensF2 m1 a1 _ rfl
                    hA1.2.2.1 hA1.2.2.2.1 hReadLo1
                dsimp only [implF1Normal]
                refine wpFrameOutcome_stmt_step lensF1
                  (calleeLookup [specF2Normal]) bodyF1Normal 7 _ cm0 m0 _ _ _
                  rfl rfl hStep0 ?_
                refine wpFrameOutcome_call_step lensF1
                  (calleeLookup [specF2Normal]) bodyF1Normal 6 _ cm0 m1 _
                  defIdF2Normal [mkU32Const 0x22000041] ⟨4, []⟩ (some 1)
                  (.cleanup 2) u32Ty specF2Normal
                  [.scalar ⟨.i32, false, BitVec.ofNat 128 0x22000041⟩] _ m1
                  (mkU32Bytes4 0x10 0x00 0x00 0x01) _
                  rfl rfl rfl rfl rfl rfl rfl
                  (evalCallArgs_one_const_u32 _ _ m1 0x22000041 rfl)
                  hGetPreF2 rfl ?_ (fun hF => False.elim (by cases hF))
                intro _ retVal m2 hUpdF2 hPostF2
                cases hPostF2 with
                | intro postBsF2 hPostF2Ex =>
                  have hAndF2 := andb_true_elim hPostF2Ex.2
                  have hRetValEq :=
                    eq_of_valIsU32_true 0x32000042 retVal hAndF2.1
                  have hPostBsEqF2 :=
                    eq_of_bytesBeq_true postBsF2 _ hAndF2.2
                  have hReadLo2 : readBytes m2 ⟨1, 0⟩ 4 2 =
                      .ok (mkU32Bytes4 0x32 0x00 0x00 0x42) := by
                    rw [← hPostBsEqF2]
                    exact readBytes_of_byteSubLensGet lensF2 m2 postBsF2
                      hPostF2Ex.1
                  have hReadHi2 : readBytes m2 ⟨1, 4⟩ 4 2 =
                      .ok (mkU32Bytes4 0x20 0x00 0x00 0x11) := by
                    have hPres :=
                      ((updatesOnly_preserves_outside lensF2 m1 m2 hUpdF2).1
                        lensF1Hi rfl).2
                    dsimp only [lensF1Hi] at hPres
                    rw [hPres]
                    exact hPutHi.2.2.1
                  have hUpdF1Mid : UpdatesOnly lensF1 m0 m2 :=
                    updatesOnly_trans lensF1 m0 m1 m2 hUpdHi1
                      (updatesOnly_mono_sublens lensF2 lensF1 m1 m2 rfl
                        ⟨bs1, hA1.1⟩ hUpdF2)
                  cases lens_valid_after_updatesOnly lensF1 m0 m2 hUpdF1Mid with
                  | intro bs2_8 hL2 =>
                    cases hL2 with
                    | intro a2 hA2 =>
                      have hBnd2Hi := (isInBounds_4_of_8 a2 hA2.2.2.2.2.2.1).2
                      cases byteSubLensPut_eq_some_of_valid lensF1Hi m2
                          (mkU32Bytes4 0x20 0x00 0x00 0x17) a2 rfl rfl
                          hA2.2.2.1 hA2.2.2.2.1 hA2.2.2.2.2.1 hBnd2Hi
                          hA2.2.2.2.2.2.2 with
                      | intro m3 hPut3 =>
                        have hReadLo3 : readBytes m3 ⟨1, 0⟩ 4 2 =
                            .ok (mkU32Bytes4 0x32 0x00 0x00 0x42) := by
                          rw [← hReadLo2]
                          exact (hPut3.2.2.2.2 lensF2 rfl).2
                        have hUpdFinal : UpdatesOnly lensF1 m0 m3 :=
                          updatesOnly_trans lensF1 m0 m2 m3 hUpdF1Mid
                            (updatesOnly_mono_sublens lensF1Hi lensF1 m2 m3 rfl
                              ⟨bs2_8, hA2.1⟩
                              (updatesOnly_of_put lensF1Hi m2 m3 _ hPut3.1))
                        dsimp only [evalCallExitStep]
                        rw [hRetValEq]
                        have hWrRet : writePlace
                            [.immediate none,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x10000010⟩)),
                             .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                             .immediate none, .immediate none]
                            m2 4 u32Ty
                            (.scalar ⟨.i32, false,
                              BitVec.ofNat 128 0x32000042⟩) =
                            .ok ([.immediate none,
                                  .immediate (some (.scalar ⟨.i32, false,
                                    BitVec.ofNat 128 0x10000010⟩)),
                                  .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                  .immediate (some (.scalar ⟨.i32, false,
                                    BitVec.ofNat 128 0x32000042⟩)),
                                  .immediate none], m2) :=
                          writePlace_immediate_ok _ _ m2 4 u32Ty _ none
                            rfl rfl rfl
                        rw [hWrRet]
                        dsimp only
                        have hStep1 :
                            evalStep (Anneal.MirWp.bodyProg bodyF1Normal) 0
                              ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 0,
                                  locals :=
                                    [.immediate none,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x10000010⟩)),
                                     .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x32000042⟩)),
                                     .immediate none] }], cm0, m2⟩ =
                              .step ⟨[⟨0, 1, 1,
                                  [.immediate none,
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x10000010⟩)),
                                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x32000042⟩)),
                                   .immediate none], none, none, none⟩],
                                cm0, m3⟩ := by
                          refine evalStep_assign_ok bodyF1Normal _ _ cm0 m2 m2
                            m3 3 u32Ty
                            (.binaryOp .add (.copy ⟨3, []⟩) (mkU32Const 6))
                            (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000017⟩)
                            [.immediate none,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x10000010⟩)),
                             .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x32000042⟩)),
                             .immediate none]
                            _ rfl rfl rfl rfl ?_ ?_
                          · refine evalRvalue_binaryOp_ok _ _
                              [.immediate none,
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x10000010⟩)),
                               .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x32000042⟩)),
                               .immediate none]
                              _ m2 m2 m2 u32Ty .add (.copy ⟨3, []⟩)
                              (mkU32Const 6)
                              (.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x20000011⟩)
                              (.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x00000006⟩) _ ?_ rfl rfl
                            exact evalPrimitiveOperand_copy_indirect _ _ m2 3
                              u32Ty ⟨1, 4⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hReadHi2
                              rfl
                          · exact writePlace_indirect_ok _ m2 m3 3 u32Ty _
                              ⟨1, 4⟩ ⟨4, 2⟩ _ rfl rfl rfl rfl hPut3.2.1
                        have hStep2 :
                            evalStep (Anneal.MirWp.bodyProg bodyF1Normal) 0
                              ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 1,
                                  locals :=
                                    [.immediate none,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x10000010⟩)),
                                     .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x32000042⟩)),
                                     .immediate none] }], cm0, m3⟩ =
                              .step ⟨[⟨0, 1, 2,
                                  [.immediate none,
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x10000010⟩)),
                                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x32000042⟩)),
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x64000084⟩))],
                                  none, none, none⟩], cm0, m3⟩ := by
                          refine evalStep_assign_ok bodyF1Normal _ _ cm0 m3 m3
                            m3 5 u32Ty
                            (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨4, []⟩))
                            (.scalar ⟨.i32, false, BitVec.ofNat 128 0x64000084⟩)
                            [.immediate none,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x10000010⟩)),
                             .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x32000042⟩)),
                             .immediate none]
                            _ rfl rfl rfl rfl ?_ ?_
                          · refine evalRvalue_binaryOp_ok _ _
                              [.immediate none,
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x10000010⟩)),
                               .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x32000042⟩)),
                               .immediate none]
                              _ m3 m3 m3 u32Ty .add (.copy ⟨2, []⟩)
                              (.copy ⟨4, []⟩)
                              (.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x32000042⟩)
                              (.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x32000042⟩) _ ?_ ?_ rfl
                            · exact evalPrimitiveOperand_copy_indirect _ _ m3 2
                                u32Ty ⟨1, 0⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hReadLo3
                                rfl
                            · exact evalPrimitiveOperand_copy_immediate _ _ m3 4
                                u32Ty _ rfl rfl rfl
                          · exact writePlace_immediate_ok _ _ m3 5 u32Ty _ none
                              rfl rfl rfl
                        have hStep3 :
                            evalStep (Anneal.MirWp.bodyProg bodyF1Normal) 0
                              ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 2,
                                  locals :=
                                    [.immediate none,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x10000010⟩)),
                                     .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x32000042⟩)),
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x64000084⟩))] }],
                                cm0, m3⟩ =
                              .step ⟨[⟨0, 1, 3,
                                  [.immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x8400009B⟩)),
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x10000010⟩)),
                                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x32000042⟩)),
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x64000084⟩))],
                                  none, none, none⟩], cm0, m3⟩ := by
                          refine evalStep_assign_ok bodyF1Normal _ _ cm0 m3 m3
                            m3 0 u32Ty
                            (.binaryOp .add (.copy ⟨5, []⟩) (.copy ⟨3, []⟩))
                            (.scalar ⟨.i32, false, BitVec.ofNat 128 0x8400009B⟩)
                            [.immediate none,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x10000010⟩)),
                             .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x32000042⟩)),
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x64000084⟩))]
                            _ rfl rfl rfl rfl ?_ ?_
                          · refine evalRvalue_binaryOp_ok _ _
                              [.immediate none,
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x10000010⟩)),
                               .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x32000042⟩)),
                               .immediate (some (.scalar ⟨.i32, false,
                                 BitVec.ofNat 128 0x64000084⟩))]
                              _ m3 m3 m3 u32Ty .add (.copy ⟨5, []⟩)
                              (.copy ⟨3, []⟩)
                              (.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x64000084⟩)
                              (.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x20000017⟩) _ ?_ ?_ rfl
                            · exact evalPrimitiveOperand_copy_immediate _ _ m3 5
                                u32Ty _ rfl rfl rfl
                            · exact evalPrimitiveOperand_copy_indirect _ _ m3 3
                                u32Ty ⟨1, 4⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl
                                hPut3.2.2.1 rfl
                          · exact writePlace_immediate_ok _ _ m3 0 u32Ty _ none
                              rfl rfl rfl
                        have hStep4 :
                            evalStep (Anneal.MirWp.bodyProg bodyF1Normal) 0
                              ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 3,
                                  locals :=
                                    [.immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x8400009B⟩)),
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x10000010⟩)),
                                     .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x32000042⟩)),
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x64000084⟩))] }],
                                cm0, m3⟩ =
                              .done (.returned ⟨.scalar ⟨.i32, false,
                                BitVec.ofNat 128 0x8400009B⟩, cm0⟩) :=
                          evalStep_return_immediate bodyF1Normal _ _ cm0 m3 _
                            rfl rfl rfl rfl rfl rfl
                        cases lens_valid_after_updatesOnly lensF1 m0 m3
                            hUpdFinal with
                        | intro bs3_8 hL3 =>
                          cases hL3 with
                          | intro a3 hA3 =>
                            have hBs3Eq : bs3_8 =
                                mkU32Bytes4 0x32 0x00 0x00 0x42 ++
                                  mkU32Bytes4 0x20 0x00 0x00 0x17 :=
                              readBytes_8_eq_append_of_4_4 m3 1 _ _ bs3_8
                                hReadLo3 hPut3.2.2.1 hA3.2.1
                            refine wpFrameOutcome_stmt_step lensF1
                              (calleeLookup [specF2Normal]) bodyF1Normal 5 _
                              cm0 m2 _ _ _ rfl rfl hStep1 ?_
                            refine wpFrameOutcome_stmt_step lensF1
                              (calleeLookup [specF2Normal]) bodyF1Normal 4 _
                              cm0 m3 _ _ _ rfl rfl hStep2 ?_
                            refine wpFrameOutcome_stmt_step lensF1
                              (calleeLookup [specF2Normal]) bodyF1Normal 3 _
                              cm0 m3 _ _ _ rfl rfl hStep3 ?_
                            refine wpFrameOutcome_return_step lensF1
                              (calleeLookup [specF2Normal]) bodyF1Normal 2 _
                              cm0 m3 _ _ _ rfl rfl rfl hStep4 ?_
                            refine ⟨rfl, hUpdFinal, bs3_8, hA3.1, ?_⟩
                            rw [hBs3Eq]; rfl

/-- Modular verification of `F0` against `specF1Normal` only (never unfolds
`bodyF1Normal` or `bodyF2Normal`, `[propext]`). -/
theorem verify_f0_normal_modular (m0 : MemoryState) (cm0 : CallerMemory)
    (a0 : Allocation)
    (hFind0 : findAllocation 1 m0.allocations = some a0)
    (hMut0 : a0.mutability = .mut) (hLive0 : a0.live = true)
    (hBnd0 : isInBounds a0 0 16 = true) (hAl0 : isAligned a0 0 3 = true) :
    wpFrameOutcome lensF0 (calleeLookup [specF1Normal]) bodyF0Normal 6
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                     locals := mkLocalsF0 lensF0 }]
        callerMem := cm0
        mem := m0 }
      (fun out =>
        match out with
        | .returned retVal mOut =>
          retVal = .scalar ⟨.i32, false, BitVec.ofNat 128 0xD60000F4⟩ ∧
          UpdatesOnly lensF1 m0 mOut ∧
          readBytes mOut ⟨1, 0⟩ 4 2 =
            .ok (mkU32Bytes4 0x32 0x00 0x00 0x42) ∧
          readBytes mOut ⟨1, 4⟩ 4 2 =
            .ok (mkU32Bytes4 0x20 0x00 0x00 0x17) ∧
          (∀ otherL : ByteSubLens, byteLensDisjoint lensF1 otherL = true →
            readBytes mOut ⟨otherL.allocId, otherL.offset⟩ otherL.size
                otherL.alignLog2 =
              readBytes m0 ⟨otherL.allocId, otherL.offset⟩ otherL.size
                otherL.alignLog2) ∧
          (∀ extId : AllocId, Nat.beq extId 1 = false →
            findAllocation extId mOut.allocations =
              findAllocation extId m0.allocations)
        | .unwound _ => False
        | .abortTerminate _ => False) := by
  have hBnd4Lo : isInBounds a0 0 4 = true := by
    dsimp only [isInBounds] at hBnd0
    dsimp only [isInBounds]
    rw [natAdd_zero_leftC] at hBnd0
    rw [natAdd_zero_leftC]
    exact natBle_transC 4 16 a0.bytes.length rfl hBnd0
  have hBnd8Lo : isInBounds a0 0 8 = true := by
    dsimp only [isInBounds] at hBnd0
    dsimp only [isInBounds]
    rw [natAdd_zero_leftC] at hBnd0
    rw [natAdd_zero_leftC]
    exact natBle_transC 8 16 a0.bytes.length rfl hBnd0
  have hAl2Lo : isAligned a0 0 2 = true := by
    dsimp only [isAligned] at hAl0
    dsimp only [isAligned]
    have hAnd := andb_true_elim hAl0
    rw [natBle_transC 2 3 a0.alignLog2 rfl hAnd.1]
    rfl
  cases byteSubLensGet_of_valid lensF1 m0 a0 rfl hFind0 hMut0 hLive0 hBnd8Lo
      hAl2Lo with
  | intro pre8_0 hGetF1_0 =>
    cases byteSubLensPut_eq_some_of_valid lensF2 m0
        (mkU32Bytes4 0x10 0x00 0x00 0x01) a0 rfl rfl hFind0 hMut0 hLive0
        hBnd4Lo hAl2Lo with
    | intro m1 hPut1 =>
      have hUpd01 : UpdatesOnly lensF1 m0 m1 :=
        updatesOnly_mono_sublens lensF2 lensF1 m0 m1 rfl ⟨pre8_0, hGetF1_0.1⟩
          (updatesOnly_of_put lensF2 m0 m1 _ hPut1.1)
      have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyF0Normal) 0
          ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
              locals := mkLocalsF0 lensF0 }], cm0, m0⟩ =
          .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1,
                    locals := mkLocalsF0 lensF0 }], cm0, m1⟩ := by
        refine evalStep_assign_ok bodyF0Normal _ _ cm0 m0 m0 m1 1 u32Ty
          (.use (mkU32Const 0x10000001))
          (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
          (mkLocalsF0 lensF0) _ rfl rfl rfl rfl ?_ ?_
        · exact evalRvalue_use_constant _ _ m0 u32Ty
            ⟨u32Ty, .scalar (BitVec.ofNat 128 0x10000001)⟩ _ rfl rfl
        · exact writePlace_indirect_ok _ m0 m1 1 u32Ty _ ⟨1, 0⟩ ⟨4, 2⟩ _
            rfl rfl rfl rfl hPut1.2.1
      cases lens_valid_after_updatesOnly lensF1 m0 m1 hUpd01 with
      | intro bs1_8 hL1 =>
        cases hL1 with
        | intro a1 hA1 =>
          have hPreLo1 : bs1_8.take 4 = mkU32Bytes4 0x10 0x00 0x00 0x01 := by
            have hSubLo := readBytes_sub4_take_of_readBytes_8 m1 1 bs1_8 hA1.2.1
            have hEqR := Eq.trans hSubLo.symm hPut1.2.2.1
            injection hEqR
          have hPreCond1 : specF1Normal.precondBool bs1_8
              [.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩] = true := by
            dsimp only [specF1Normal, bytesBeq4BE]
            rw [hPreLo1]
            rfl
          refine wpFrameOutcome_stmt_step lensF0
            (calleeLookup [specF1Normal]) bodyF0Normal 5 _ cm0 m0 _ _ _
            rfl rfl hStep0 ?_
          refine wpFrameOutcome_call_step lensF0
            (calleeLookup [specF1Normal]) bodyF0Normal 4 _ cm0 m1 _
            defIdF1Normal [mkU32Const 0x10000010] ⟨3, []⟩ (some 1) (.cleanup 2)
            u32Ty specF1Normal
            [.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩] _ m1 bs1_8 _
            rfl rfl rfl rfl rfl rfl rfl
            (evalCallArgs_one_const_u32 _ _ m1 0x10000010 rfl) hA1.1 hPreCond1
            ?_ (fun hF => False.elim (by cases hF))
          intro _ retVal1 m2 hUpd12 hPostF1
          cases hPostF1 with
          | intro postBs1 hPostEx =>
            have hAndF1 := andb_true_elim hPostEx.2
            have hRet1Eq := eq_of_valIsU32_true 0x8400009B retVal1 hAndF1.1
            have hPostBs1Eq := eq_of_bytesBeq_true postBs1 _ hAndF1.2
            have hRead8_2 : readBytes m2 ⟨1, 0⟩ 8 2 =
                .ok (mkU32Bytes4 0x32 0x00 0x00 0x42 ++
                  mkU32Bytes4 0x20 0x00 0x00 0x17) := by
              rw [← hPostBs1Eq]
              exact readBytes_of_byteSubLensGet lensF1 m2 postBs1 hPostEx.1
            have hReadLo2 := readBytes_sub4_take_of_readBytes_8 m2 1 _ hRead8_2
            have hReadHi2 := readBytes_sub4_drop4_of_readBytes_8 m2 1 _ hRead8_2
            have hUpdFinal := updatesOnly_trans lensF1 m0 m1 m2 hUpd01 hUpd12
            have hPresOut :=
              updatesOnly_preserves_outside lensF1 m0 m2 hUpdFinal
            dsimp only [evalCallExitStep]
            rw [hRet1Eq]
            have hWrRet : writePlace (mkLocalsF0 lensF0) m2 3 u32Ty
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x8400009B⟩) =
                .ok ([.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                      .immediate (some (.scalar ⟨.i32, false,
                        BitVec.ofNat 128 0x8400009B⟩)),
                      .immediate none, .immediate none], m2) :=
              writePlace_immediate_ok (mkLocalsF0 lensF0) _ m2 3 u32Ty _ none
                rfl rfl rfl
            rw [hWrRet]
            dsimp only
            have hStep1 : evalStep (Anneal.MirWp.bodyProg bodyF0Normal) 0
                ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 0, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate none, .immediate none] }], cm0, m2⟩ =
                .step ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 1, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x52000059⟩)),
                   .immediate none] }], cm0, m2⟩ := by
              refine evalStep_assign_ok bodyF0Normal _ _ cm0 m2 m2 m2 4 u32Ty
                (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x52000059⟩)
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x8400009B⟩)),
                 .immediate none, .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · refine evalRvalue_binaryOp_ok _ _
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate none, .immediate none]
                  _ m2 m2 m2 u32Ty .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000017⟩) _ ?_ ?_
                  rfl
                · exact evalPrimitiveOperand_copy_indirect _ _ m2 1 u32Ty
                    ⟨1, 0⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hReadLo2 rfl
                · exact evalPrimitiveOperand_copy_indirect _ _ m2 2 u32Ty
                    ⟨1, 4⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hReadHi2 rfl
              · exact writePlace_immediate_ok _ _ m2 4 u32Ty _ none rfl rfl rfl
            have hStep2 : evalStep (Anneal.MirWp.bodyProg bodyF0Normal) 0
                ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 1, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x52000059⟩)),
                   .immediate none] }], cm0, m2⟩ =
                .step ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 2, locals :=
                  [.immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0xD60000F4⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x52000059⟩)),
                   .immediate none] }], cm0, m2⟩ := by
              refine evalStep_assign_ok bodyF0Normal _ _ cm0 m2 m2 m2 0 u32Ty
                (.binaryOp .add (.copy ⟨4, []⟩) (.copy ⟨3, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0xD60000F4⟩)
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x8400009B⟩)),
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x52000059⟩)),
                 .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · refine evalRvalue_binaryOp_ok _ _
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x52000059⟩)),
                   .immediate none]
                  _ m2 m2 m2 u32Ty .add (.copy ⟨4, []⟩) (.copy ⟨3, []⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x52000059⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x8400009B⟩) _ ?_ ?_
                  rfl
                · exact evalPrimitiveOperand_copy_immediate _ _ m2 4 u32Ty _
                    rfl rfl rfl
                · exact evalPrimitiveOperand_copy_immediate _ _ m2 3 u32Ty _
                    rfl rfl rfl
              · exact writePlace_immediate_ok _ _ m2 0 u32Ty _ none rfl rfl rfl
            have hStep3 : evalStep (Anneal.MirWp.bodyProg bodyF0Normal) 0
                ⟨[{ defId := 0, blockIdx := 1, stmtIdx := 2, locals :=
                  [.immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0xD60000F4⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x8400009B⟩)),
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x52000059⟩)),
                   .immediate none] }], cm0, m2⟩ =
                .done (.returned ⟨.scalar ⟨.i32, false,
                  BitVec.ofNat 128 0xD60000F4⟩, cm0⟩) :=
              evalStep_return_immediate bodyF0Normal _ _ cm0 m2 _
                rfl rfl rfl rfl rfl rfl
            refine wpFrameOutcome_stmt_step lensF0
              (calleeLookup [specF1Normal]) bodyF0Normal 3 _ cm0 m2 _ _ _
              rfl rfl hStep1 ?_
            refine wpFrameOutcome_stmt_step lensF0
              (calleeLookup [specF1Normal]) bodyF0Normal 2 _ cm0 m2 _ _ _
              rfl rfl hStep2 ?_
            refine wpFrameOutcome_return_step lensF0
              (calleeLookup [specF1Normal]) bodyF0Normal 1 _ cm0 m2 _ _ _
              rfl rfl rfl hStep3 ?_
            exact ⟨rfl, hUpdFinal, hReadLo2, hReadHi2,
              fun otherL hD => (hPresOut.1 otherL hD).2, hPresOut.2⟩

/-- Initial 2-allocation `MemoryState` (`allocId = 1` size 16 `.mut` and
external `allocId = 2` `.shared`). -/
@[expose] def mInit16 : MemoryState :=
  { nextAllocId := 3
    allocations :=
      [{ allocId := 1
         alignLog2 := 3
         mutability := .mut
         bytes :=
           mkU32Bytes4 0xA0 0xA1 0xA2 0xA3 ++
           mkU32Bytes4 0xB0 0xB1 0xB2 0xB3 ++
           mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
           mkU32Bytes4 0xC4 0xC5 0xC6 0xC7
         live := true },
       { allocId := 2
         alignLog2 := 3
         mutability := .shared
         bytes :=
           mkU32Bytes4 0xE0 0xE1 0xE2 0xE3 ++
           mkU32Bytes4 0xE4 0xE5 0xE6 0xE7
         live := true }] }

/-- Memory state after initializing `[0..4)` to `0x10000001`. -/
@[expose] def mPre16Concrete : MemoryState :=
  { nextAllocId := 3
    allocations :=
      [{ allocId := 1
         alignLog2 := 3
         mutability := .mut
         bytes :=
           mkU32Bytes4 0x10 0x00 0x00 0x01 ++
           mkU32Bytes4 0xB0 0xB1 0xB2 0xB3 ++
           mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
           mkU32Bytes4 0xC4 0xC5 0xC6 0xC7
         live := true },
       { allocId := 2
         alignLog2 := 3
         mutability := .shared
         bytes :=
           mkU32Bytes4 0xE0 0xE1 0xE2 0xE3 ++
           mkU32Bytes4 0xE4 0xE5 0xE6 0xE7
         live := true }] }

/-- Concrete `Anneal.MirWp.wpState`, `SafeFrom`, and
`wpFrameOutcome_of_mirWpState` witness on `bodyF2Normal` (`[propext]`). -/
theorem f2Normal_concrete_mirWpState :
    byteSubLensPut lensF2 mInit16 (mkU32Bytes4 0x10 0x00 0x00 0x01) =
      some mPre16Concrete ∧
    let sStart : State :=
      ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := implF2Normal.mkLocals lensF2
            [.scalar ⟨.i32, false, BitVec.ofNat 128 0x22000041⟩] }],
        ⟨[]⟩, mPre16Concrete⟩
    Anneal.MirWp.wpState (Anneal.MirWp.bodyProg bodyF2Normal) 5 sStart
      (fun out => out = .returned
        ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩, ⟨[]⟩⟩) ∧
    Anneal.MirWp.SafeFrom bodyF2Normal sStart ∧
    wpFrameOutcome lensF2 (calleeLookup []) bodyF2Normal 5 sStart
      (fun out => ∃ mAny, out = .returned
        (.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩) mAny) := by
  have hPut : byteSubLensPut lensF2 mInit16 (mkU32Bytes4 0x10 0x00 0x00 0x01) =
      some mPre16Concrete := rfl
  let sStart : State :=
    ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := implF2Normal.mkLocals lensF2
          [.scalar ⟨.i32, false, BitVec.ofNat 128 0x22000041⟩] }],
      ⟨[]⟩, mPre16Concrete⟩
  have hExec : Anneal.MirWp.execState (Anneal.MirWp.bodyProg bodyF2Normal) 5
      sStart
      (fun out => out = .returned
        ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 0x32000042⟩, ⟨[]⟩⟩) := rfl
  have hWp := Anneal.MirWp.wpOutcomeState_of_execOutcomeState hExec
  refine ⟨hPut, hWp, Anneal.MirWp.safeFrom_of_wpState hWp, ?_⟩
  refine wpFrameOutcome_of_mirWpState lensF2 (calleeLookup []) bodyF2Normal 5
    sStart _ _ ?_ hWp
  intro rv mem _ hEq
  cases hEq
  exact ⟨mem, rfl⟩

/-- Implementation lookup table for the 3-level normal call stack. -/
@[expose] def implTableNormal : DefId → Option (CallImplBundle × List CallSpec)
    :=
  implLookup [(defIdF1Normal, implF1Normal, [specF2Normal]),
              (defIdF2Normal, implF2Normal, [])]

/-- Depth-2 `CallCutTree` certificate sealing `F1` and `F2`. -/
theorem callCutTree_normal_2 : CallCutTree implTableNormal 2 [specF1Normal] :=
  by
  intro defId cSpec hLook
  dsimp only [calleeLookup, implTableNormal, implLookup, specF1Normal,
    defIdF1Normal, List.foldr] at hLook
  cases hEq1 : Nat.beq 101 defId with
  | false => rw [ite_bool_falseC hEq1] at hLook; cases hLook
  | true =>
    rw [ite_bool_trueC hEq1] at hLook
    injection hLook with hSpecEq
    have hIdEq := natEq_of_beqC 101 defId hEq1
    subst hSpecEq hIdEq
    refine ⟨rfl, implF1Normal, [specF2Normal], rfl, seal_f1Normal_callSpecCut,
      ?_⟩
    intro defId2 cSpec2 hLook2
    dsimp only [calleeLookup, implLookup, specF2Normal, defIdF2Normal,
      List.foldr] at hLook2
    cases hEq2 : Nat.beq 102 defId2 with
    | false => rw [ite_bool_falseC hEq2] at hLook2; cases hLook2
    | true =>
      rw [ite_bool_trueC hEq2] at hLook2
      injection hLook2 with hSpec2Eq
      have hId2Eq := natEq_of_beqC 102 defId2 hEq2
      subst hSpec2Eq hId2Eq
      exact ⟨rfl, implF2Normal, [], rfl, seal_f2Normal_callSpecCut, rfl⟩

/-- 3-level nested `&mut` call framing (`F0 -> F1 -> F2`, `[propext]`):
proves exact post-state bytes across `[0..4)` and `[4..8)` while preserving
`[8..16)` and external `allocId = 2`. -/
theorem nested3Level_normal_call_framing_sound :
    ∃ (mOut : MemoryState),
      StackReaches implTableNormal
        (.running ⟨lensF0, [specF1Normal], bodyF0Normal,
          ⟨0, 0, 0, mkLocalsF0 lensF0, none, none, none⟩⟩ [] mInit16 ⟨[]⟩)
        (.terminated (.returned
          (.scalar ⟨.i32, false, BitVec.ofNat 128 0xD60000F4⟩) mOut)) ∧
      UpdatesOnly lensF1 mInit16 mOut ∧
      readBytes mOut ⟨1, 0⟩ 4 2 = .ok (mkU32Bytes4 0x32 0x00 0x00 0x42) ∧
      readBytes mOut ⟨1, 4⟩ 4 2 = .ok (mkU32Bytes4 0x20 0x00 0x00 0x17) ∧
      readBytes mOut ⟨1, 8⟩ 8 3 =
        .ok (mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
          mkU32Bytes4 0xC4 0xC5 0xC6 0xC7) ∧
      findAllocation 2 mOut.allocations =
        some ⟨2, 3, .shared,
          mkU32Bytes4 0xE0 0xE1 0xE2 0xE3 ++ mkU32Bytes4 0xE4 0xE5 0xE6 0xE7,
          true⟩ := by
  have hWp := verify_f0_normal_modular mInit16 ⟨[]⟩
    ⟨1, 3, .mut,
      mkU32Bytes4 0xA0 0xA1 0xA2 0xA3 ++
      mkU32Bytes4 0xB0 0xB1 0xB2 0xB3 ++
      mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
      mkU32Bytes4 0xC4 0xC5 0xC6 0xC7, true⟩
    rfl rfl rfl rfl rfl
  cases wpFrameOutcome_implies_stackExecutes implTableNormal 2 [specF1Normal]
      callCutTree_normal_2 lensF0 bodyF0Normal 6
        ⟨0, 0, 0, mkLocalsF0 lensF0, none, none, none⟩
        mInit16 ⟨[]⟩ _ hWp with
  | intro out hOut =>
    cases out with
    | unwound _ => exact False.elim hOut.2
    | abortTerminate _ => exact False.elim hOut.2
    | returned rv mOut =>
      have hP := hOut.2
      have hRvEq := hP.1
      rw [hRvEq] at hOut
      refine ⟨mOut, hOut.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, ?_, ?_⟩
      · have hPresTail := hP.2.2.2.2.1 lensF0Tail rfl
        dsimp only [lensF0Tail] at hPresTail
        rw [hPresTail]
        rfl
      · have hPresExt := hP.2.2.2.2.2 2 rfl
        rw [hPresExt]
        rfl

/-! ## 3. 4-Way `CallCont4` Matrix and `.abortTerminate` Stack Witness -/

/-- Canary fixture helper `bodyAbortCallee`. -/
@[expose] def bodyAbortCallee : Body :=
  { argumentCount := 0
    locals := [u32Ty, MirTy.bool]
    basicBlocks :=
      [{ statements :=
          [.assign ⟨1, []⟩
            (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩))]
         terminator := .assert (.copy ⟨1, []⟩) true .boundsCheck 1 .continue_
         cleanup := false },
       { statements := []
         terminator := .return_
         cleanup := false }] }

/-- Canary fixture helper `implAbortCallee`. -/
@[expose] def implAbortCallee : CallImplBundle :=
  { body := bodyAbortCallee
    fuel := 4
    mkLocals := fun _ _ => [.immediate none, .immediate none] }

/-- Canary fixture helper `specAbortCallee`. -/
@[expose] def specAbortCallee : CallSpec :=
  { calleeDefId := 201
    mutLens := lensF2
    precondBool := fun _ _ => true
    ensuresNormalBool := fun _ _ _ _ => false
    ensuresUnwindBool := fun preBs postBs _ => bytesBeq postBs preBs
    canNormal := false
    canUnwind := true }

/-- Canary fixture helper `bodyAbortCaller`. -/
@[expose] def bodyAbortCaller : Body :=
  { argumentCount := 0
    locals := [u32Ty]
    basicBlocks :=
      [{ statements := []
         terminator := .call 201 [] ⟨0, []⟩ (some 1) .terminate
         cleanup := false },
       { statements := []
         terminator := .return_
         cleanup := false }] }

/-- 4-way `CallCont4` exit matrix and concrete `.abortTerminate` multi-frame
stack execution witness (`[propext]`). -/
theorem callCont4_exit_matrix_sound :
    callCont4OfTerminator? (.call 102 [] ⟨4, []⟩ (some 1) (.cleanup 2)) =
      some ⟨some 1, .cleanup 2⟩ ∧
    callCont4OfTerminator? (.goto 0) = none ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .cleanup 2⟩
        (.normal (.scalar ⟨.i32, false, 1⟩) mInit16) =
      .stepNormal 1 (.scalar ⟨.i32, false, 1⟩) mInit16 ∧
    evalCallExitStep bodyF1Normal ⟨none, .continue_⟩ (.normal .unit mInit16) =
      .fault .undefined ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .cleanup 2⟩ (.unwind mInit16) =
      .stepCleanup 2 mInit16 ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .continue_⟩ (.unwind mInit16) =
      .exitUnwind mInit16 ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .unreachable⟩ (.unwind mInit16) =
      .fault .undefined ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .terminate⟩ (.unwind mInit16) =
      .exitTerminate mInit16 ∧
    (∃ mAbort out,
      StackReaches (implLookup [(201, implAbortCallee, [])])
        (.running ⟨lensF1, [specAbortCallee], bodyAbortCaller,
          ⟨0, 0, 0, [.immediate none], none, none, none⟩⟩ [] mInit16 ⟨[]⟩)
        (.terminated out) ∧
      out = .abortTerminate mAbort ∧
      readBytes mAbort ⟨1, 0⟩ 4 2 = .ok (mkU32Bytes4 0xA0 0xA1 0xA2 0xA3)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hCut : CallSpecCut [] implAbortCallee specAbortCallee := by
    apply seal_callSpecCut
    intro m0 cm0 _
    dsimp only [specAbortCallee]
    cases hG : byteSubLensGet lensF2 m0 with
    | none => exact True.intro
    | some preBs =>
      dsimp only
      intro _
      have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyAbortCallee) 0
          ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
              locals := [.immediate none, .immediate none] }], cm0, m0⟩ =
          .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1,
                    locals := [.immediate none,
                      .immediate (some (.bool false))] }], cm0, m0⟩ := by
        refine evalStep_assign_ok bodyAbortCallee _ _ cm0 m0 m0 m0 1 MirTy.bool
          (.use (.constant ⟨MirTy.bool, .scalar (BitVec.ofNat 128 0)⟩))
          (.bool false) [.immediate none, .immediate none] _
          rfl rfl rfl rfl ?_ ?_
        · exact evalRvalue_use_constant _ _ m0 MirTy.bool
            ⟨MirTy.bool, .scalar (BitVec.ofNat 128 0)⟩ _ rfl rfl
        · exact writePlace_immediate_ok _ _ m0 1 MirTy.bool (.bool false) none
            rfl rfl rfl
      have hOp : evalPrimitiveOperand bodyAbortCallee.locals
          [.immediate none, .immediate (some (.bool false))] m0
            (.copy ⟨1, []⟩) =
          .ok (.bool false, [.immediate none, .immediate (some (.bool false))],
            m0) :=
        evalPrimitiveOperand_copy_immediate _ _ m0 1 MirTy.bool (.bool false)
          rfl rfl rfl
      dsimp only [implAbortCallee]
      refine wpFrameOutcome_stmt_step lensF2 (calleeLookup []) bodyAbortCallee
        3 _ cm0 m0 _ _ _ rfl rfl hStep0 ?_
      refine wpFrameOutcome_assert_false_unwind_step lensF2 (calleeLookup [])
        bodyAbortCallee 2 _ cm0 m0 _ (.copy ⟨1, []⟩) true .boundsCheck 1
        .continue_ _ m0 _ rfl rfl rfl hOp ?_
      exact ⟨rfl, updatesOnly_refl lensF2 m0 preBs hG, preBs, hG,
        bytesBeq_refl preBs⟩
  have hTree : CallCutTree (implLookup [(201, implAbortCallee, [])]) 1
      [specAbortCallee] := by
    intro dId s hLk
    dsimp only [calleeLookup, implLookup, specAbortCallee, List.foldr] at hLk
    cases hEq : Nat.beq 201 dId with
    | false => rw [ite_bool_falseC hEq] at hLk; cases hLk
    | true =>
      rw [ite_bool_trueC hEq] at hLk
      injection hLk with hSEq
      have hDEq := natEq_of_beqC 201 dId hEq
      subst hSEq hDEq
      exact ⟨rfl, implAbortCallee, [], rfl, hCut, rfl⟩
  have hWpCaller : wpFrameOutcome lensF1 (calleeLookup [specAbortCallee])
      bodyAbortCaller 4
      ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := [.immediate none] }], ⟨[]⟩, mInit16⟩
      (fun out => ∃ mAbort, out = .abortTerminate mAbort ∧
        readBytes mAbort ⟨1, 0⟩ 4 2 = .ok (mkU32Bytes4 0xA0 0xA1 0xA2 0xA3)) :=
    by
    refine wpFrameOutcome_call_step lensF1 (calleeLookup [specAbortCallee])
      bodyAbortCaller 3 _ ⟨[]⟩ mInit16 _ 201 [] ⟨0, []⟩ (some 1) .terminate
      u32Ty specAbortCallee [] [.immediate none] mInit16
      (mkU32Bytes4 0xA0 0xA1 0xA2 0xA3) _
      rfl rfl rfl rfl rfl rfl rfl .nil rfl rfl
      (fun hF => False.elim (by cases hF)) ?_
    intro _ mAfter _ hPost
    cases hPost with
    | intro postBs hEx =>
      have hEqBs := eq_of_bytesBeq_true postBs (mkU32Bytes4 0xA0 0xA1 0xA2 0xA3)
        hEx.2
      have hReadAfter := readBytes_of_byteSubLensGet lensF2 mAfter postBs hEx.1
      rw [hEqBs] at hReadAfter
      exact ⟨mAfter, rfl, hReadAfter⟩
  cases wpFrameOutcome_implies_stackExecutes _ 1 _ hTree lensF1 bodyAbortCaller
      4 _ mInit16 ⟨[]⟩ _ hWpCaller with
  | intro out hOut =>
    cases hOut.2 with
    | intro mAbort hAb =>
      exact ⟨mAbort, out, hOut.1, hAb.1, hAb.2⟩

/-! ## 4. 2-Level Unwind Cleanup Propagation and Negative Fail-Closed Tests -/

@[expose] def defIdF2Panic : DefId := 103
@[expose] def defIdF1Unwind : DefId := 104
@[expose] def defIdF1Skip : DefId := 105

/-- Leaf panicking callee `F2Panic`: commits partial `&mut` write `0x0BADF299`
on `[0..4)` before failing `.assert` with `.continue_`. -/
@[expose] def bodyF2Panic : Body :=
  { argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty, MirTy.bool]
    basicBlocks :=
      [{ statements :=
          [.assign ⟨2, []⟩ (.use (mkU32Const 0x0BADF299)),
           .assign ⟨3, []⟩
             (.use (.constant ⟨MirTy.bool, .scalar (BitVec.ofNat 128 0)⟩))]
         terminator := .assert (.copy ⟨3, []⟩) true .boundsCheck 1 .continue_
         cleanup := false },
       { statements := []
         terminator := .return_
         cleanup := false }] }

@[expose] def implF2Panic : CallImplBundle :=
  { body := bodyF2Panic, fuel := 4, mkLocals := mkLocalsF2 }

@[expose] def specF2Panic : CallSpec :=
  { calleeDefId := defIdF2Panic
    mutLens := lensF2
    precondBool := fun preBs args =>
      bytesBeq preBs (mkU32Bytes4 0x10 0x00 0x00 0x01) &&
        argsIsOneU32 0x22000041 args
    ensuresNormalBool := fun _ _ _ _ => false
    ensuresUnwindBool := fun _ postPartialBs _ =>
      bytesBeq postPartialBs (mkU32Bytes4 0x0B 0xAD 0xF2 0x99)
    canNormal := false
    canUnwind := true }

@[expose] def bodyF1Unwind : Body := mkBodyF1 defIdF2Panic

@[expose] def implF1Unwind : CallImplBundle :=
  { body := bodyF1Unwind, fuel := 5, mkLocals := mkLocalsF1 }

@[expose] def specF1Unwind : CallSpec :=
  { calleeDefId := defIdF1Unwind
    mutLens := lensF1
    precondBool := fun preBs args =>
      bytesBeq4BE 0x10 0x00 0x00 0x01 preBs && argsIsOneU32 0x10000010 args
    ensuresNormalBool := fun _ _ _ _ => false
    ensuresUnwindBool := fun _ postPartialBs _ =>
      bytesBeq postPartialBs
        (mkU32Bytes4 0x0B 0xAD 0xF2 0x99 ++
          mkU32Bytes4 0xDE 0xAD 0xF1 0x01)
    canNormal := false
    canUnwind := true }

@[expose] def bodyF0Unwind : Body := mkBodyF0 defIdF1Unwind

/-- Seals `F2Panic` (`canNormal = false`, `canUnwind = true`, `[propext]`). -/
theorem seal_f2Panic_callSpecCut : CallSpecCut [] implF2Panic specF2Panic := by
  apply seal_callSpecCut
  intro m0 cm0 args
  dsimp only [specF2Panic]
  cases hGet : byteSubLensGet lensF2 m0 with
  | none => exact True.intro
  | some preBs =>
    dsimp only
    intro hPre
    have hAnd := andb_true_elim hPre
    have hArgsEx : ∃ v, args = [v] ∧ valIsU32 0x22000041 v = true := by
      cases args with
      | nil => cases hAnd.2
      | cons v rest =>
        cases rest with
        | cons _ _ => cases hAnd.2
        | nil => exact ⟨v, rfl, hAnd.2⟩
    cases hArgsEx with
    | intro vArg hVArg =>
      have hArgEq := hVArg.1
      have hVArgVal := eq_of_valIsU32_true 0x22000041 vArg hVArg.2
      have hRefl0 := updatesOnly_refl lensF2 m0 preBs hGet
      cases lens_valid_after_updatesOnly lensF2 m0 m0 hRefl0 with
      | intro _ hL0 =>
        cases hL0 with
        | intro a0 hA0 =>
          cases byteSubLensPut_eq_some_of_valid lensF2 m0
              (mkU32Bytes4 0x0B 0xAD 0xF2 0x99) a0 rfl rfl hA0.2.2.1
              hA0.2.2.2.1 hA0.2.2.2.2.1 hA0.2.2.2.2.2.1 hA0.2.2.2.2.2.2 with
          | intro m1 hPut1 =>
            have hLocs0 : implF2Panic.mkLocals lensF2 args =
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩, .immediate none] := by
              rw [hArgEq, hVArgVal]; rfl
            have hStep1 : evalStep (Anneal.MirWp.bodyProg bodyF2Panic) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
                    locals := implF2Panic.mkLocals lensF2 args }], cm0, m0⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩, .immediate none] }], cm0, m1⟩ := by
              rw [hLocs0]
              refine evalStep_assign_ok bodyF2Panic _ _ cm0 m0 m0 m1 2 u32Ty
                (.use (mkU32Const 0x0BADF299))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x0BADF299⟩)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩, .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · exact evalRvalue_use_constant _ _ m0 u32Ty
                  ⟨u32Ty, .scalar (BitVec.ofNat 128 0x0BADF299)⟩ _ rfl rfl
              · exact writePlace_indirect_ok _ m0 m1 2 u32Ty _ ⟨1, 0⟩ ⟨4, 2⟩ _
                  rfl rfl rfl rfl hPut1.2.1
            have hStep2 : evalStep (Anneal.MirWp.bodyProg bodyF2Panic) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩, .immediate none] }], cm0, m1⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 2, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩, .immediate (some (.bool false))] }],
                  cm0, m1⟩ := by
              refine evalStep_assign_ok bodyF2Panic _ _ cm0 m1 m1 m1 3
                MirTy.bool
                (.use (.constant ⟨MirTy.bool, .scalar (BitVec.ofNat 128 0)⟩))
                (.bool false)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩, .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · exact evalRvalue_use_constant _ _ m1 MirTy.bool
                  ⟨MirTy.bool, .scalar (BitVec.ofNat 128 0)⟩ _ rfl rfl
              · exact writePlace_immediate_ok _ _ m1 3 MirTy.bool (.bool false)
                  none rfl rfl rfl
            have hOp : evalPrimitiveOperand bodyF2Panic.locals
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x22000041⟩)),
                 .indirect ⟨1, 0⟩, .immediate (some (.bool false))] m1
                (.copy ⟨3, []⟩) =
                .ok (.bool false,
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x22000041⟩)),
                   .indirect ⟨1, 0⟩, .immediate (some (.bool false))], m1) :=
              evalPrimitiveOperand_copy_immediate _ _ m1 3 MirTy.bool
                (.bool false) rfl rfl rfl
            dsimp only [implF2Panic]
            refine wpFrameOutcome_stmt_step lensF2 (calleeLookup []) bodyF2Panic
              3 _ cm0 m0 _ _ _ rfl rfl hStep1 ?_
            refine wpFrameOutcome_stmt_step lensF2 (calleeLookup []) bodyF2Panic
              2 _ cm0 m1 _ _ _ rfl rfl hStep2 ?_
            refine wpFrameOutcome_assert_false_unwind_step lensF2
              (calleeLookup []) bodyF2Panic 1 _ cm0 m1 _ (.copy ⟨3, []⟩) true
              .boundsCheck 1 .continue_ _ m1 _ rfl rfl rfl hOp ?_
            exact ⟨rfl, updatesOnly_of_put lensF2 m0 m1 _ hPut1.1,
              mkU32Bytes4 0x0B 0xAD 0xF2 0x99, hPut1.2.2.2.1, rfl⟩

/-- Seals `F1Unwind` against `specF2Panic` only, executing `F1`'s cleanup pad
to stamp `[4..8) := 0xDEADF101` before `.unwindResume` (`[propext]`). -/
theorem seal_f1Unwind_callSpecCut :
    CallSpecCut [specF2Panic] implF1Unwind specF1Unwind := by
  apply seal_callSpecCut
  intro m0 cm0 args
  dsimp only [specF1Unwind]
  cases hGet8 : byteSubLensGet lensF1 m0 with
  | none => exact True.intro
  | some preBs =>
    dsimp only
    intro hPre
    have hAnd := andb_true_elim hPre
    have hPre4 := eq_of_bytesBeq_true (preBs.take 4) _ hAnd.1
    have hArgsEx : ∃ v, args = [v] ∧ valIsU32 0x10000010 v = true := by
      cases args with
      | nil => cases hAnd.2
      | cons v rest =>
        cases rest with
        | cons _ _ => cases hAnd.2
        | nil => exact ⟨v, rfl, hAnd.2⟩
    cases hArgsEx with
    | intro vArg hVArg =>
      have hArgEq := hVArg.1
      have hVArgVal := eq_of_valIsU32_true 0x10000010 vArg hVArg.2
      have hRead0 : readBytes m0 ⟨1, 0⟩ 4 2 =
          .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
        rw [← hPre4]
        exact readBytes_sub4_take_of_readBytes_8 m0 1 preBs
          (readBytes_of_byteSubLensGet lensF1 m0 preBs hGet8)
      have hRefl0 := updatesOnly_refl lensF1 m0 preBs hGet8
      cases lens_valid_after_updatesOnly lensF1 m0 m0 hRefl0 with
      | intro _ hL0 =>
        cases hL0 with
        | intro a0 hA0 =>
          have hBnd4Hi := (isInBounds_4_of_8 a0 hA0.2.2.2.2.2.1).2
          cases byteSubLensPut_eq_some_of_valid lensF1Hi m0
              (mkU32Bytes4 0x20 0x00 0x00 0x11) a0 rfl rfl hA0.2.2.1
              hA0.2.2.2.1 hA0.2.2.2.2.1 hBnd4Hi hA0.2.2.2.2.2.2 with
          | intro m1 hPutHi =>
            have hUpdHi1 : UpdatesOnly lensF1 m0 m1 :=
              updatesOnly_mono_sublens lensF1Hi lensF1 m0 m1 rfl ⟨preBs, hGet8⟩
                (updatesOnly_of_put lensF1Hi m0 m1 _ hPutHi.1)
            have hReadLo1 : readBytes m1 ⟨1, 0⟩ 4 2 =
                .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
              rw [← hRead0]
              exact (hPutHi.2.2.2.2 lensF2 rfl).2
            have hLocs0 : implF1Unwind.mkLocals lensF1 args =
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x10000010⟩)),
                 .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                 .immediate none] := by
              rw [hArgEq, hVArgVal]; rfl
            have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyF1Unwind) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
                    locals := implF1Unwind.mkLocals lensF1 args }], cm0, m0⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x10000010⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                   .immediate none] }], cm0, m1⟩ := by
              rw [hLocs0]
              refine evalStep_assign_ok bodyF1Unwind _ _ cm0 m0 m0 m1 3 u32Ty
                (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000011⟩)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x10000010⟩)),
                 .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                 .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · refine evalRvalue_binaryOp_ok _ _
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x10000010⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                   .immediate none]
                  _ m0 m0 m0 u32Ty .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩) _ ?_ ?_
                  rfl
                · exact evalPrimitiveOperand_copy_indirect _ _ m0 2 u32Ty
                    ⟨1, 0⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hRead0 rfl
                · exact evalPrimitiveOperand_copy_immediate _ _ m0 1 u32Ty _
                    rfl rfl rfl
              · exact writePlace_indirect_ok _ m0 m1 3 u32Ty _ ⟨1, 4⟩ ⟨4, 2⟩ _
                  rfl rfl rfl rfl hPutHi.2.1
            cases lens_valid_after_updatesOnly lensF1 m0 m1 hUpdHi1 with
            | intro bs1 hL1 =>
              cases hL1 with
              | intro a1 hA1 =>
                have hGetPreF2 := byteSubLensGet_eq_some_of_readBytes lensF2 m1
                  a1 _ rfl hA1.2.2.1 hA1.2.2.2.1 hReadLo1
                dsimp only [implF1Unwind]
                refine wpFrameOutcome_stmt_step lensF1
                  (calleeLookup [specF2Panic]) bodyF1Unwind 4 _ cm0 m0 _ _ _
                  rfl rfl hStep0 ?_
                refine wpFrameOutcome_call_step lensF1
                  (calleeLookup [specF2Panic]) bodyF1Unwind 3 _ cm0 m1 _
                  defIdF2Panic [mkU32Const 0x22000041] ⟨4, []⟩ (some 1)
                  (.cleanup 2) u32Ty specF2Panic
                  [.scalar ⟨.i32, false, BitVec.ofNat 128 0x22000041⟩] _ m1
                  (mkU32Bytes4 0x10 0x00 0x00 0x01) _
                  rfl rfl rfl rfl rfl rfl rfl
                  (evalCallArgs_one_const_u32 _ _ m1 0x22000041 rfl)
                  hGetPreF2 rfl (fun hF => False.elim (by cases hF)) ?_
                intro _ m2 hUpdF2 hUnwF2
                cases hUnwF2 with
                | intro postBsF2 hUnwF2Ex =>
                  have hPostBsEqF2 := eq_of_bytesBeq_true postBsF2 _ hUnwF2Ex.2
                  have hReadLo2 : readBytes m2 ⟨1, 0⟩ 4 2 =
                      .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99) := by
                    rw [← hPostBsEqF2]
                    exact readBytes_of_byteSubLensGet lensF2 m2 postBsF2
                      hUnwF2Ex.1
                  have hUpdF1Mid : UpdatesOnly lensF1 m0 m2 :=
                    updatesOnly_trans lensF1 m0 m1 m2 hUpdHi1
                      (updatesOnly_mono_sublens lensF2 lensF1 m1 m2 rfl
                        ⟨bs1, hA1.1⟩ hUpdF2)
                  cases lens_valid_after_updatesOnly lensF1 m0 m2 hUpdF1Mid with
                  | intro bs2_8 hL2 =>
                    cases hL2 with
                    | intro a2 hA2 =>
                      have hBnd2Hi := (isInBounds_4_of_8 a2 hA2.2.2.2.2.2.1).2
                      cases byteSubLensPut_eq_some_of_valid lensF1Hi m2
                          (mkU32Bytes4 0xDE 0xAD 0xF1 0x01) a2 rfl rfl
                          hA2.2.2.1 hA2.2.2.2.1 hA2.2.2.2.2.1 hBnd2Hi
                          hA2.2.2.2.2.2.2 with
                      | intro m3 hPut3 =>
                        have hReadLo3 : readBytes m3 ⟨1, 0⟩ 4 2 =
                            .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99) := by
                          rw [← hReadLo2]
                          exact (hPut3.2.2.2.2 lensF2 rfl).2
                        have hUpdFinal : UpdatesOnly lensF1 m0 m3 :=
                          updatesOnly_trans lensF1 m0 m2 m3 hUpdF1Mid
                            (updatesOnly_mono_sublens lensF1Hi lensF1 m2 m3 rfl
                              ⟨bs2_8, hA2.1⟩
                              (updatesOnly_of_put lensF1Hi m2 m3 _ hPut3.1))
                        have hExit :
                            evalCallExitStep bodyF1Unwind
                              ⟨some 1, .cleanup 2⟩ (.unwind m2) =
                              .stepCleanup 2 m2 := rfl
                        rw [hExit]
                        dsimp only
                        have hStepDrop :
                            evalStep (Anneal.MirWp.bodyProg bodyF1Unwind) 0
                              ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 0,
                                  locals :=
                                    [.immediate none,
                                     .immediate (some (.scalar ⟨.i32, false,
                                       BitVec.ofNat 128 0x10000010⟩)),
                                     .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                     .immediate none, .immediate none] }],
                                cm0, m2⟩ =
                              .step ⟨[⟨0, 2, 1,
                                  [.immediate none,
                                   .immediate (some (.scalar ⟨.i32, false,
                                     BitVec.ofNat 128 0x10000010⟩)),
                                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                                   .immediate none, .immediate none],
                                  none, none, none⟩], cm0, m3⟩ := by
                          refine evalStep_assign_ok bodyF1Unwind _ _ cm0 m2 m2
                            m3 3 u32Ty (.use (mkU32Const 0xDEADF101))
                            (.scalar ⟨.i32, false, BitVec.ofNat 128 0xDEADF101⟩)
                            [.immediate none,
                             .immediate (some (.scalar ⟨.i32, false,
                               BitVec.ofNat 128 0x10000010⟩)),
                             .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                             .immediate none, .immediate none]
                            _ rfl rfl rfl rfl ?_ ?_
                          · exact evalRvalue_use_constant _ _ m2 u32Ty
                              ⟨u32Ty, .scalar (BitVec.ofNat 128 0xDEADF101)⟩ _
                              rfl rfl
                          · exact writePlace_indirect_ok _ m2 m3 3 u32Ty _
                              ⟨1, 4⟩ ⟨4, 2⟩ _ rfl rfl rfl rfl hPut3.2.1
                        cases lens_valid_after_updatesOnly lensF1 m0 m3
                            hUpdFinal with
                        | intro bs3_8 hL3 =>
                          cases hL3 with
                          | intro a3 hA3 =>
                            have hBs3Eq : bs3_8 =
                                mkU32Bytes4 0x0B 0xAD 0xF2 0x99 ++
                                  mkU32Bytes4 0xDE 0xAD 0xF1 0x01 :=
                              readBytes_8_eq_append_of_4_4 m3 1 _ _ bs3_8
                                hReadLo3 hPut3.2.2.1 hA3.2.1
                            refine wpFrameOutcome_stmt_step lensF1
                              (calleeLookup [specF2Panic]) bodyF1Unwind 2 _
                              cm0 m2 _ _ _ rfl rfl hStepDrop ?_
                            refine wpFrameOutcome_unwindResume_step lensF1
                              (calleeLookup [specF2Panic]) bodyF1Unwind 1 _
                              cm0 m3 _ _ rfl rfl rfl rfl ?_
                            refine ⟨rfl, hUpdFinal, bs3_8, hA3.1, ?_⟩
                            rw [hBs3Eq]; rfl

/-- Modular verification of `F0Unwind` against `specF1Unwind` only
(`[propext]`). -/
theorem verify_f0_unwind_modular (m0 : MemoryState) (cm0 : CallerMemory)
    (a0 : Allocation)
    (hFind0 : findAllocation 1 m0.allocations = some a0)
    (hMut0 : a0.mutability = .mut) (hLive0 : a0.live = true)
    (hBnd0 : isInBounds a0 0 16 = true) (hAl0 : isAligned a0 0 3 = true) :
    wpFrameOutcome lensF0 (calleeLookup [specF1Unwind]) bodyF0Unwind 7
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                     locals := mkLocalsF0 lensF0 }]
        callerMem := cm0
        mem := m0 }
      (fun out =>
        match out with
        | .unwound mOut =>
          UpdatesOnly lensF1 m0 mOut ∧
          readBytes mOut ⟨1, 0⟩ 4 2 =
            .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99) ∧
          readBytes mOut ⟨1, 4⟩ 4 2 =
            .ok (mkU32Bytes4 0xDE 0xAD 0xF1 0x01) ∧
          (∀ otherL : ByteSubLens, byteLensDisjoint lensF1 otherL = true →
            readBytes mOut ⟨otherL.allocId, otherL.offset⟩ otherL.size
                otherL.alignLog2 =
              readBytes m0 ⟨otherL.allocId, otherL.offset⟩ otherL.size
                otherL.alignLog2) ∧
          (∀ extId : AllocId, Nat.beq extId 1 = false →
            findAllocation extId mOut.allocations =
              findAllocation extId m0.allocations)
        | .returned _ _ => False
        | .abortTerminate _ => False) := by
  have hBnd4Lo : isInBounds a0 0 4 = true := by
    dsimp only [isInBounds] at hBnd0
    dsimp only [isInBounds]
    rw [natAdd_zero_leftC] at hBnd0
    rw [natAdd_zero_leftC]
    exact natBle_transC 4 16 a0.bytes.length rfl hBnd0
  have hBnd8Lo : isInBounds a0 0 8 = true := by
    dsimp only [isInBounds] at hBnd0
    dsimp only [isInBounds]
    rw [natAdd_zero_leftC] at hBnd0
    rw [natAdd_zero_leftC]
    exact natBle_transC 8 16 a0.bytes.length rfl hBnd0
  have hAl2Lo : isAligned a0 0 2 = true := by
    dsimp only [isAligned] at hAl0
    dsimp only [isAligned]
    have hAnd := andb_true_elim hAl0
    rw [natBle_transC 2 3 a0.alignLog2 rfl hAnd.1]
    rfl
  cases byteSubLensGet_of_valid lensF1 m0 a0 rfl hFind0 hMut0 hLive0 hBnd8Lo
      hAl2Lo with
  | intro pre8_0 hGetF1_0 =>
    cases byteSubLensPut_eq_some_of_valid lensF2 m0
        (mkU32Bytes4 0x10 0x00 0x00 0x01) a0 rfl rfl hFind0 hMut0 hLive0
        hBnd4Lo hAl2Lo with
    | intro m1 hPut1 =>
      have hUpd01 : UpdatesOnly lensF1 m0 m1 :=
        updatesOnly_mono_sublens lensF2 lensF1 m0 m1 rfl ⟨pre8_0, hGetF1_0.1⟩
          (updatesOnly_of_put lensF2 m0 m1 _ hPut1.1)
      have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyF0Unwind) 0
          ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
              locals := mkLocalsF0 lensF0 }], cm0, m0⟩ =
          .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1,
                    locals := mkLocalsF0 lensF0 }], cm0, m1⟩ := by
        refine evalStep_assign_ok bodyF0Unwind _ _ cm0 m0 m0 m1 1 u32Ty
          (.use (mkU32Const 0x10000001))
          (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
          (mkLocalsF0 lensF0) _ rfl rfl rfl rfl ?_ ?_
        · exact evalRvalue_use_constant _ _ m0 u32Ty
            ⟨u32Ty, .scalar (BitVec.ofNat 128 0x10000001)⟩ _ rfl rfl
        · exact writePlace_indirect_ok _ m0 m1 1 u32Ty _ ⟨1, 0⟩ ⟨4, 2⟩ _
            rfl rfl rfl rfl hPut1.2.1
      cases lens_valid_after_updatesOnly lensF1 m0 m1 hUpd01 with
      | intro bs1_8 hL1 =>
        cases hL1 with
        | intro a1 hA1 =>
          have hPreLo1 : bs1_8.take 4 = mkU32Bytes4 0x10 0x00 0x00 0x01 := by
            have hSubLo := readBytes_sub4_take_of_readBytes_8 m1 1 bs1_8 hA1.2.1
            have hEqR := Eq.trans hSubLo.symm hPut1.2.2.1
            injection hEqR
          have hPreCond1 : specF1Unwind.precondBool bs1_8
              [.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩] = true := by
            dsimp only [specF1Unwind, bytesBeq4BE]
            rw [hPreLo1]
            rfl
          refine wpFrameOutcome_stmt_step lensF0
            (calleeLookup [specF1Unwind]) bodyF0Unwind 6 _ cm0 m0 _ _ _
            rfl rfl hStep0 ?_
          refine wpFrameOutcome_call_step lensF0
            (calleeLookup [specF1Unwind]) bodyF0Unwind 5 _ cm0 m1 _
            defIdF1Unwind [mkU32Const 0x10000010] ⟨3, []⟩ (some 1) (.cleanup 2)
            u32Ty specF1Unwind
            [.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩] _ m1 bs1_8 _
            rfl rfl rfl rfl rfl rfl rfl
            (evalCallArgs_one_const_u32 _ _ m1 0x10000010 rfl) hA1.1 hPreCond1
            (fun hF => False.elim (by cases hF)) ?_
          intro _ m2 hUpd12 hUnwF1
          cases hUnwF1 with
          | intro postBs1 hUnwEx =>
            have hPostBs1Eq := eq_of_bytesBeq_true postBs1 _ hUnwEx.2
            have hRead8_2 : readBytes m2 ⟨1, 0⟩ 8 2 =
                .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99 ++
                  mkU32Bytes4 0xDE 0xAD 0xF1 0x01) := by
              rw [← hPostBs1Eq]
              exact readBytes_of_byteSubLensGet lensF1 m2 postBs1 hUnwEx.1
            have hReadLo2 := readBytes_sub4_take_of_readBytes_8 m2 1 _ hRead8_2
            have hReadHi2 := readBytes_sub4_drop4_of_readBytes_8 m2 1 _ hRead8_2
            have hUpdFinal := updatesOnly_trans lensF1 m0 m1 m2 hUpd01 hUpd12
            have hPresOut :=
              updatesOnly_preserves_outside lensF1 m0 m2 hUpdFinal
            have hExit :
                evalCallExitStep bodyF0Unwind ⟨some 1, .cleanup 2⟩
                  (.unwind m2) = .stepCleanup 2 m2 := rfl
            rw [hExit]
            dsimp only [mkLocalsF0]
            have hStepB2 : evalStep (Anneal.MirWp.bodyProg bodyF0Unwind) 0
                ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 0, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none, .immediate none] }],
                  cm0, m2⟩ =
                .step ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 1, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none,
                   .immediate (some (.bool true))] }], cm0, m2⟩ := by
              refine evalStep_assign_ok bodyF0Unwind _ _ cm0 m2 m2 m2 5
                MirTy.bool
                (.binaryOp .eq (.copy ⟨2, []⟩) (mkU32Const 0xDEADF101))
                (.bool true)
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate none, .immediate none, .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · refine evalRvalue_binaryOp_ok _ _
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none, .immediate none]
                  _ m2 m2 m2 MirTy.bool .eq (.copy ⟨2, []⟩)
                  (mkU32Const 0xDEADF101)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0xDEADF101⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0xDEADF101⟩) _ ?_ rfl
                  rfl
                exact evalPrimitiveOperand_copy_indirect _ _ m2 2 u32Ty ⟨1, 4⟩
                  ⟨4, 2⟩ _ _ rfl rfl rfl rfl hReadHi2 rfl
              · exact writePlace_immediate_ok _ _ m2 5 MirTy.bool (.bool true)
                  none rfl rfl rfl
            have hOpOk : evalPrimitiveOperand bodyF0Unwind.locals
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate none, .immediate none,
                 .immediate (some (.bool true))] m2 (.copy ⟨5, []⟩) =
                .ok (.bool true,
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none,
                   .immediate (some (.bool true))], m2) :=
              evalPrimitiveOperand_copy_immediate _ _ m2 5 MirTy.bool
                (.bool true) rfl rfl rfl
            have hStepB3 : evalStep (Anneal.MirWp.bodyProg bodyF0Unwind) 0
                ⟨[{ defId := 0, blockIdx := 3, stmtIdx := 0, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none,
                   .immediate (some (.bool true))] }], cm0, m2⟩ =
                .step ⟨[{ defId := 0, blockIdx := 3, stmtIdx := 1, locals :=
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x0BADF299⟩)),
                   .immediate (some (.bool true))] }], cm0, m2⟩ := by
              refine evalStep_assign_ok bodyF0Unwind _ _ cm0 m2 m2 m2 4 u32Ty
                (.use (.copy ⟨1, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x0BADF299⟩)
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate none, .immediate none,
                 .immediate (some (.bool true))]
                _ rfl rfl rfl rfl ?_ ?_
              · exact evalRvalue_use_copy_indirect _ _ m2 1 u32Ty ⟨1, 0⟩ ⟨4, 2⟩
                  _ _ rfl rfl rfl rfl hReadLo2 rfl
              · exact writePlace_immediate_ok _ _ m2 4 u32Ty _ none rfl rfl rfl
            refine wpFrameOutcome_stmt_step lensF0
              (calleeLookup [specF1Unwind]) bodyF0Unwind 4 _ cm0 m2 _ _ _
              rfl rfl hStepB2 ?_
            refine wpFrameOutcome_assert_true_pass_step lensF0
              (calleeLookup [specF1Unwind]) bodyF0Unwind 3 _ cm0 m2 _
              (.copy ⟨5, []⟩) true .boundsCheck 3 .terminate _ m2 _
              rfl rfl rfl hOpOk ?_
            refine wpFrameOutcome_stmt_step lensF0
              (calleeLookup [specF1Unwind]) bodyF0Unwind 2 _ cm0 m2 _ _ _
              rfl rfl hStepB3 ?_
            refine wpFrameOutcome_unwindResume_step lensF0
              (calleeLookup [specF1Unwind]) bodyF0Unwind 1 _ cm0 m2 _ _
              rfl rfl rfl rfl ?_
            exact ⟨hUpdFinal, hReadLo2, hReadHi2,
              fun otherL hD => (hPresOut.1 otherL hD).2, hPresOut.2⟩

@[expose] def implTableUnwind : DefId → Option (CallImplBundle × List CallSpec)
    :=
  implLookup [(defIdF1Unwind, implF1Unwind, [specF2Panic]),
              (defIdF2Panic, implF2Panic, [])]

theorem callCutTree_unwind_2 : CallCutTree implTableUnwind 2 [specF1Unwind] :=
  by
  intro defId cSpec hLook
  dsimp only [calleeLookup, implTableUnwind, implLookup, specF1Unwind,
    defIdF1Unwind, List.foldr] at hLook
  cases hEq1 : Nat.beq 104 defId with
  | false => rw [ite_bool_falseC hEq1] at hLook; cases hLook
  | true =>
    rw [ite_bool_trueC hEq1] at hLook
    injection hLook with hSpecEq
    have hIdEq := natEq_of_beqC 104 defId hEq1
    subst hSpecEq hIdEq
    refine ⟨rfl, implF1Unwind, [specF2Panic], rfl, seal_f1Unwind_callSpecCut,
      ?_⟩
    intro defId2 cSpec2 hLook2
    dsimp only [calleeLookup, implLookup, specF2Panic, defIdF2Panic,
      List.foldr] at hLook2
    cases hEq2 : Nat.beq 103 defId2 with
    | false => rw [ite_bool_falseC hEq2] at hLook2; cases hLook2
    | true =>
      rw [ite_bool_trueC hEq2] at hLook2
      injection hLook2 with hSpec2Eq
      have hId2Eq := natEq_of_beqC 103 defId2 hEq2
      subst hSpec2Eq hId2Eq
      exact ⟨rfl, implF2Panic, [], rfl, seal_f2Panic_callSpecCut, rfl⟩

/-- 2-level nested unwind cleanup propagation (`F2Panic -> F1 cleanup -> F0
cleanup`, `[propext]`): commits partial write `0x0BADF299` on `[0..4)`, stamps
drop marker `0xDEADF101` on `[4..8)`, passes `F0`'s cleanup assertion, preserves
`[8..16)` and external `allocId = 2`, and leaks no normal `ensures`. -/
theorem nested2Level_unwind_cleanup_propagation_sound :
    specF2Panic.canNormal = false ∧
    specF1Unwind.canNormal = false ∧
    (∀ pre rv post args,
      specF2Panic.ensuresNormalBool pre rv post args = false) ∧
    (∀ pre rv post args,
      specF1Unwind.ensuresNormalBool pre rv post args = false) ∧
    ∃ (mOut : MemoryState),
      StackReaches implTableUnwind
        (.running ⟨lensF0, [specF1Unwind], bodyF0Unwind,
          ⟨0, 0, 0, mkLocalsF0 lensF0, none, none, none⟩⟩ [] mInit16 ⟨[]⟩)
        (.terminated (.unwound mOut)) ∧
      UpdatesOnly lensF1 mInit16 mOut ∧
      readBytes mOut ⟨1, 0⟩ 4 2 = .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99) ∧
      readBytes mOut ⟨1, 4⟩ 4 2 = .ok (mkU32Bytes4 0xDE 0xAD 0xF1 0x01) ∧
      readBytes mOut ⟨1, 8⟩ 8 3 =
        .ok (mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
          mkU32Bytes4 0xC4 0xC5 0xC6 0xC7) ∧
      findAllocation 2 mOut.allocations =
        some ⟨2, 3, .shared,
          mkU32Bytes4 0xE0 0xE1 0xE2 0xE3 ++ mkU32Bytes4 0xE4 0xE5 0xE6 0xE7,
          true⟩ := by
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_⟩
  have hWp := verify_f0_unwind_modular mInit16 ⟨[]⟩
    ⟨1, 3, .mut,
      mkU32Bytes4 0xA0 0xA1 0xA2 0xA3 ++
      mkU32Bytes4 0xB0 0xB1 0xB2 0xB3 ++
      mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
      mkU32Bytes4 0xC4 0xC5 0xC6 0xC7, true⟩
    rfl rfl rfl rfl rfl
  cases wpFrameOutcome_implies_stackExecutes implTableUnwind 2 [specF1Unwind]
      callCutTree_unwind_2 lensF0 bodyF0Unwind 7
        ⟨0, 0, 0, mkLocalsF0 lensF0, none, none, none⟩
        mInit16 ⟨[]⟩ _ hWp with
  | intro out hOut =>
    cases out with
    | returned _ _ => exact False.elim hOut.2
    | abortTerminate _ => exact False.elim hOut.2
    | unwound mOut =>
      have hP := hOut.2
      refine ⟨mOut, hOut.1, hP.1, hP.2.1, hP.2.2.1, ?_, ?_⟩
      · have hPresTail := hP.2.2.2.1 lensF0Tail rfl
        dsimp only [lensF0Tail] at hPresTail
        rw [hPresTail]
        rfl
      · have hPresExt := hP.2.2.2.2 2 rfl
        rw [hPresExt]
        rfl

/-- Canary fixture helper `bodyF1SkipCleanup`. -/
@[expose] def bodyF1SkipCleanup : Body :=
  { argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
    basicBlocks :=
      [{ statements :=
          [.assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))]
         terminator := .call defIdF2Panic [mkU32Const 0x22000041] ⟨4, []⟩
           (some 1) .continue_
         cleanup := false },
       { statements := []
         terminator := .return_
         cleanup := false }] }

/-- Canary fixture helper `implF1Skip`. -/
@[expose] def implF1Skip : CallImplBundle :=
  { body := bodyF1SkipCleanup, fuel := 3, mkLocals := mkLocalsF1 }

/-- Canary fixture helper `specF1Skip`. -/
@[expose] def specF1Skip : CallSpec :=
  { calleeDefId := defIdF1Skip
    mutLens := lensF1
    precondBool := fun preBs args =>
      bytesBeq4BE 0x10 0x00 0x00 0x01 preBs && argsIsOneU32 0x10000010 args
    ensuresNormalBool := fun _ _ _ _ => false
    ensuresUnwindBool := fun _ postPartialBs _ =>
      bytesBeq postPartialBs
        (mkU32Bytes4 0x0B 0xAD 0xF2 0x99 ++
          mkU32Bytes4 0x20 0x00 0x00 0x11)
    canNormal := false
    canUnwind := true }

/-- Canary fixture helper `bodyF0Skip`. -/
@[expose] def bodyF0Skip : Body := mkBodyF0 defIdF1Skip

private theorem seal_f1Skip_callSpecCut :
    CallSpecCut [specF2Panic] implF1Skip specF1Skip := by
  apply seal_callSpecCut
  intro m0 cm0 args
  dsimp only [specF1Skip]
  cases hGet8 : byteSubLensGet lensF1 m0 with
  | none => exact True.intro
  | some preBs =>
    dsimp only
    intro hPre
    have hAnd := andb_true_elim hPre
    have hPre4 := eq_of_bytesBeq_true (preBs.take 4) _ hAnd.1
    have hArgsEx : ∃ v, args = [v] ∧ valIsU32 0x10000010 v = true := by
      cases args with
      | nil => cases hAnd.2
      | cons v rest =>
        cases rest with
        | cons _ _ => cases hAnd.2
        | nil => exact ⟨v, rfl, hAnd.2⟩
    cases hArgsEx with
    | intro vArg hVArg =>
      have hArgEq := hVArg.1
      have hVArgVal := eq_of_valIsU32_true 0x10000010 vArg hVArg.2
      have hRead0 : readBytes m0 ⟨1, 0⟩ 4 2 =
          .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
        rw [← hPre4]
        exact readBytes_sub4_take_of_readBytes_8 m0 1 preBs
          (readBytes_of_byteSubLensGet lensF1 m0 preBs hGet8)
      have hRefl0 := updatesOnly_refl lensF1 m0 preBs hGet8
      cases lens_valid_after_updatesOnly lensF1 m0 m0 hRefl0 with
      | intro _ hL0 =>
        cases hL0 with
        | intro a0 hA0 =>
          have hBnd4Hi := (isInBounds_4_of_8 a0 hA0.2.2.2.2.2.1).2
          cases byteSubLensPut_eq_some_of_valid lensF1Hi m0
              (mkU32Bytes4 0x20 0x00 0x00 0x11) a0 rfl rfl hA0.2.2.1
              hA0.2.2.2.1 hA0.2.2.2.2.1 hBnd4Hi hA0.2.2.2.2.2.2 with
          | intro m1 hPutHi =>
            have hUpdHi1 : UpdatesOnly lensF1 m0 m1 :=
              updatesOnly_mono_sublens lensF1Hi lensF1 m0 m1 rfl ⟨preBs, hGet8⟩
                (updatesOnly_of_put lensF1Hi m0 m1 _ hPutHi.1)
            have hReadLo1 : readBytes m1 ⟨1, 0⟩ 4 2 =
                .ok (mkU32Bytes4 0x10 0x00 0x00 0x01) := by
              rw [← hRead0]; exact (hPutHi.2.2.2.2 lensF2 rfl).2
            have hLocs0 : implF1Skip.mkLocals lensF1 args =
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x10000010⟩)),
                 .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                 .immediate none] := by
              rw [hArgEq, hVArgVal]; rfl
            have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyF1SkipCleanup) 0
                ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
                    locals := implF1Skip.mkLocals lensF1 args }], cm0, m0⟩ =
                .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1, locals :=
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x10000010⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                   .immediate none] }], cm0, m1⟩ := by
              rw [hLocs0]
              refine evalStep_assign_ok bodyF1SkipCleanup _ _ cm0 m0 m0 m1 3
                u32Ty (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000011⟩)
                [.immediate none,
                 .immediate (some (.scalar ⟨.i32, false,
                   BitVec.ofNat 128 0x10000010⟩)),
                 .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                 .immediate none]
                _ rfl rfl rfl rfl ?_ ?_
              · refine evalRvalue_binaryOp_ok _ _
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i32, false,
                     BitVec.ofNat 128 0x10000010⟩)),
                   .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩, .immediate none,
                   .immediate none]
                  _ m0 m0 m0 u32Ty .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
                  (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩) _ ?_ ?_
                  rfl
                · exact evalPrimitiveOperand_copy_indirect _ _ m0 2 u32Ty
                    ⟨1, 0⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hRead0 rfl
                · exact evalPrimitiveOperand_copy_immediate _ _ m0 1 u32Ty _
                    rfl rfl rfl
              · exact writePlace_indirect_ok _ m0 m1 3 u32Ty _ ⟨1, 4⟩ ⟨4, 2⟩ _
                  rfl rfl rfl rfl hPutHi.2.1
            cases lens_valid_after_updatesOnly lensF1 m0 m1 hUpdHi1 with
            | intro bs1 hL1 =>
              cases hL1 with
              | intro a1 hA1 =>
                have hGetPreF2 := byteSubLensGet_eq_some_of_readBytes lensF2 m1
                  a1 _ rfl hA1.2.2.1 hA1.2.2.2.1 hReadLo1
                dsimp only [implF1Skip]
                refine wpFrameOutcome_stmt_step lensF1
                  (calleeLookup [specF2Panic]) bodyF1SkipCleanup 2 _ cm0 m0
                  _ _ _ rfl rfl hStep0 ?_
                refine wpFrameOutcome_call_step lensF1
                  (calleeLookup [specF2Panic]) bodyF1SkipCleanup 1 _ cm0 m1 _
                  defIdF2Panic [mkU32Const 0x22000041] ⟨4, []⟩ (some 1)
                  .continue_ u32Ty specF2Panic
                  [.scalar ⟨.i32, false, BitVec.ofNat 128 0x22000041⟩] _ m1
                  (mkU32Bytes4 0x10 0x00 0x00 0x01) _
                  rfl rfl rfl rfl rfl rfl rfl
                  (evalCallArgs_one_const_u32 _ _ m1 0x22000041 rfl)
                  hGetPreF2 rfl (fun hF => False.elim (by cases hF)) ?_
                intro _ m2 hUpdF2 hUnwF2
                cases hUnwF2 with
                | intro postBsF2 hUnwF2Ex =>
                  have hPostBsEqF2 := eq_of_bytesBeq_true postBsF2 _ hUnwF2Ex.2
                  have hReadLo2 : readBytes m2 ⟨1, 0⟩ 4 2 =
                      .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99) := by
                    rw [← hPostBsEqF2]
                    exact readBytes_of_byteSubLensGet lensF2 m2 postBsF2
                      hUnwF2Ex.1
                  have hReadHi2 : readBytes m2 ⟨1, 4⟩ 4 2 =
                      .ok (mkU32Bytes4 0x20 0x00 0x00 0x11) := by
                    have hPres :=
                      ((updatesOnly_preserves_outside lensF2 m1 m2 hUpdF2).1
                        lensF1Hi rfl).2
                    dsimp only [lensF1Hi] at hPres
                    rw [hPres]
                    exact hPutHi.2.2.1
                  have hUpdFinal : UpdatesOnly lensF1 m0 m2 :=
                    updatesOnly_trans lensF1 m0 m1 m2 hUpdHi1
                      (updatesOnly_mono_sublens lensF2 lensF1 m1 m2 rfl
                        ⟨bs1, hA1.1⟩ hUpdF2)
                  cases lens_valid_after_updatesOnly lensF1 m0 m2 hUpdFinal with
                  | intro bs2_8 hL2 =>
                    cases hL2 with
                    | intro a2 hA2 =>
                      have hBs2Eq : bs2_8 =
                          mkU32Bytes4 0x0B 0xAD 0xF2 0x99 ++
                            mkU32Bytes4 0x20 0x00 0x00 0x11 :=
                        readBytes_8_eq_append_of_4_4 m2 1 _ _ bs2_8 hReadLo2
                          hReadHi2 hA2.2.1
                      dsimp only [evalCallExitStep]
                      refine ⟨rfl, hUpdFinal, bs2_8, hA2.1, ?_⟩
                      rw [hBs2Eq]; rfl

/-- Canary fixture helper `implTableSkip`. -/
@[expose] def implTableSkip : DefId → Option (CallImplBundle × List CallSpec) :=
  implLookup [(defIdF1Skip, implF1Skip, [specF2Panic]),
              (defIdF2Panic, implF2Panic, [])]

private theorem callCutTree_skip_2 :
    CallCutTree implTableSkip 2 [specF1Skip] := by
  intro defId cSpec hLook
  dsimp only [calleeLookup, implTableSkip, implLookup, specF1Skip, defIdF1Skip,
    List.foldr] at hLook
  cases hEq1 : Nat.beq 105 defId with
  | false => rw [ite_bool_falseC hEq1] at hLook; cases hLook
  | true =>
    rw [ite_bool_trueC hEq1] at hLook
    injection hLook with hSpecEq
    have hIdEq := natEq_of_beqC 105 defId hEq1
    subst hSpecEq hIdEq
    refine ⟨rfl, implF1Skip, [specF2Panic], rfl, seal_f1Skip_callSpecCut, ?_⟩
    intro defId2 cSpec2 hLook2
    dsimp only [calleeLookup, implLookup, specF2Panic, defIdF2Panic,
      List.foldr] at hLook2
    cases hEq2 : Nat.beq 103 defId2 with
    | false => rw [ite_bool_falseC hEq2] at hLook2; cases hLook2
    | true =>
      rw [ite_bool_trueC hEq2] at hLook2
      injection hLook2 with hSpec2Eq
      have hId2Eq := natEq_of_beqC 103 defId2 hEq2
      subst hSpec2Eq hId2Eq
      exact ⟨rfl, implF2Panic, [], rfl, seal_f2Panic_callSpecCut, rfl⟩

/-- Negative canary (`[propext]`): skipping `F1`'s cleanup pad leaves
`[4..8) = 0x20000011`, drives `F0` into `.abortTerminate`, and falsifies
`wpFrameOutcome` expecting `.unwound` for every `fuel : Nat`. -/
theorem canary_skip_f1_cleanup_violates_f0_precond :
    ∃ (mSkip : MemoryState) (postSkip : List AllocByte),
      StackReaches implTableSkip
        (.running ⟨lensF0, [specF1Skip], bodyF0Skip,
          ⟨0, 0, 0, mkLocalsF0 lensF0, none, none, none⟩⟩ [] mInit16 ⟨[]⟩)
        (.terminated (.abortTerminate mSkip)) ∧
      byteSubLensGet lensF1 mSkip = some postSkip ∧
      specF1Unwind.ensuresUnwindBool [] postSkip [] = false ∧
      readBytes mSkip ⟨1, 4⟩ 4 2 = .ok (mkU32Bytes4 0x20 0x00 0x00 0x11) ∧
      (∀ (fuel : Nat),
        ¬ wpFrameOutcome lensF0 (calleeLookup [specF1Unwind]) bodyF0Unwind fuel
            ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 0,
                locals := mkLocalsF0 lensF0 }], ⟨[]⟩, mSkip⟩
            (fun out =>
              match out with
              | .returned _ _ => False
              | .unwound _ => True
              | .abortTerminate _ => False)) := by
  have hWpSkip : wpFrameOutcome lensF0 (calleeLookup [specF1Skip]) bodyF0Skip 5
      ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := mkLocalsF0 lensF0 }], ⟨[]⟩, mInit16⟩
      (fun out =>
        match out with
        | .abortTerminate mSkip =>
          ∃ postSkip,
            byteSubLensGet lensF1 mSkip = some postSkip ∧
            specF1Unwind.ensuresUnwindBool [] postSkip [] = false ∧
            readBytes mSkip ⟨1, 4⟩ 4 2 = .ok (mkU32Bytes4 0x20 0x00 0x00 0x11)
        | .returned _ _ => False
        | .unwound _ => False) := by
    let a0 : Allocation :=
      ⟨1, 3, .mut,
        mkU32Bytes4 0xA0 0xA1 0xA2 0xA3 ++
        mkU32Bytes4 0xB0 0xB1 0xB2 0xB3 ++
        mkU32Bytes4 0xC0 0xC1 0xC2 0xC3 ++
        mkU32Bytes4 0xC4 0xC5 0xC6 0xC7, true⟩
    cases byteSubLensGet_of_valid lensF1 mInit16 a0 rfl rfl rfl rfl rfl rfl with
    | intro pre8_0 hGetF1_0 =>
      cases byteSubLensPut_eq_some_of_valid lensF2 mInit16
          (mkU32Bytes4 0x10 0x00 0x00 0x01) a0 rfl rfl rfl rfl rfl rfl rfl with
      | intro m1 hPut1 =>
        have hUpd01 : UpdatesOnly lensF1 mInit16 m1 :=
          updatesOnly_mono_sublens lensF2 lensF1 mInit16 m1 rfl
            ⟨pre8_0, hGetF1_0.1⟩
              (updatesOnly_of_put lensF2 mInit16 m1 _ hPut1.1)
        have hStep0 : evalStep (Anneal.MirWp.bodyProg bodyF0Skip) 0
            ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
                locals := mkLocalsF0 lensF0 }], ⟨[]⟩, mInit16⟩ =
            .step ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 1,
                      locals := mkLocalsF0 lensF0 }], ⟨[]⟩, m1⟩ := by
          refine evalStep_assign_ok bodyF0Skip _ _ ⟨[]⟩ mInit16 mInit16 m1 1
            u32Ty (.use (mkU32Const 0x10000001))
            (.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000001⟩)
            (mkLocalsF0 lensF0) _ rfl rfl rfl rfl ?_ ?_
          · exact evalRvalue_use_constant _ _ mInit16 u32Ty
              ⟨u32Ty, .scalar (BitVec.ofNat 128 0x10000001)⟩ _ rfl rfl
          · exact writePlace_indirect_ok _ mInit16 m1 1 u32Ty _ ⟨1, 0⟩ ⟨4, 2⟩ _
              rfl rfl rfl rfl hPut1.2.1
        cases lens_valid_after_updatesOnly lensF1 mInit16 m1 hUpd01 with
        | intro bs1_8 hL1 =>
          cases hL1 with
          | intro a1 hA1 =>
            have hPreLo1 : bs1_8.take 4 = mkU32Bytes4 0x10 0x00 0x00 0x01 := by
              have hSubLo := readBytes_sub4_take_of_readBytes_8 m1 1 bs1_8
                hA1.2.1
              have hEqR := Eq.trans hSubLo.symm hPut1.2.2.1
              injection hEqR
            have hPreCond1 : specF1Skip.precondBool bs1_8
                [.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩] = true :=
              by
              dsimp only [specF1Skip, bytesBeq4BE]
              rw [hPreLo1]
              rfl
            refine wpFrameOutcome_stmt_step lensF0 (calleeLookup [specF1Skip])
              bodyF0Skip 4 _ ⟨[]⟩ mInit16 _ _ _ rfl rfl hStep0 ?_
            refine wpFrameOutcome_call_step lensF0 (calleeLookup [specF1Skip])
              bodyF0Skip 3 _ ⟨[]⟩ m1 _ defIdF1Skip [mkU32Const 0x10000010]
              ⟨3, []⟩ (some 1) (.cleanup 2) u32Ty specF1Skip
              [.scalar ⟨.i32, false, BitVec.ofNat 128 0x10000010⟩] _ m1 bs1_8 _
              rfl rfl rfl rfl rfl rfl rfl
              (evalCallArgs_one_const_u32 _ _ m1 0x10000010 rfl) hA1.1 hPreCond1
              (fun hF => False.elim (by cases hF)) ?_
            intro _ m2 _ hUnwF1
            cases hUnwF1 with
            | intro postBs1 hUnwEx =>
              have hPostBs1Eq := eq_of_bytesBeq_true postBs1 _ hUnwEx.2
              have hRead8_2 : readBytes m2 ⟨1, 0⟩ 8 2 =
                  .ok (mkU32Bytes4 0x0B 0xAD 0xF2 0x99 ++
                    mkU32Bytes4 0x20 0x00 0x00 0x11) := by
                rw [← hPostBs1Eq]
                exact readBytes_of_byteSubLensGet lensF1 m2 postBs1 hUnwEx.1
              have hReadHi2 := readBytes_sub4_drop4_of_readBytes_8 m2 1 _
                hRead8_2
              have hExit :
                  evalCallExitStep bodyF0Skip ⟨some 1, .cleanup 2⟩
                    (.unwind m2) = .stepCleanup 2 m2 := rfl
              rw [hExit]
              dsimp only [mkLocalsF0]
              have hStepB2 : evalStep (Anneal.MirWp.bodyProg bodyF0Skip) 0
                  ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 0, locals :=
                    [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                     .immediate none, .immediate none, .immediate none] }],
                    ⟨[]⟩, m2⟩ =
                  .step ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 1, locals :=
                    [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                     .immediate none, .immediate none,
                     .immediate (some (.bool false))] }], ⟨[]⟩, m2⟩ := by
                refine evalStep_assign_ok bodyF0Skip _ _ ⟨[]⟩ m2 m2 m2 5
                  MirTy.bool
                  (.binaryOp .eq (.copy ⟨2, []⟩) (mkU32Const 0xDEADF101))
                  (.bool false)
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none, .immediate none]
                  _ rfl rfl rfl rfl ?_ ?_
                · refine evalRvalue_binaryOp_ok _ _
                    [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                     .immediate none, .immediate none, .immediate none]
                    _ m2 m2 m2 MirTy.bool .eq (.copy ⟨2, []⟩)
                    (mkU32Const 0xDEADF101)
                    (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000011⟩)
                    (.scalar ⟨.i32, false, BitVec.ofNat 128 0xDEADF101⟩) _ ?_
                    rfl rfl
                  exact evalPrimitiveOperand_copy_indirect _ _ m2 2 u32Ty
                    ⟨1, 4⟩ ⟨4, 2⟩ _ _ rfl rfl rfl rfl hReadHi2 rfl
                · exact writePlace_immediate_ok _ _ m2 5 MirTy.bool
                    (.bool false) none rfl rfl rfl
              have hOpFalse : evalPrimitiveOperand bodyF0Skip.locals
                  [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                   .immediate none, .immediate none,
                   .immediate (some (.bool false))] m2 (.copy ⟨5, []⟩) =
                  .ok (.bool false,
                    [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                     .immediate none, .immediate none,
                     .immediate (some (.bool false))], m2) :=
                evalPrimitiveOperand_copy_immediate _ _ m2 5 MirTy.bool
                  (.bool false) rfl rfl rfl
              refine wpFrameOutcome_stmt_step lensF0 (calleeLookup [specF1Skip])
                bodyF0Skip 2 _ ⟨[]⟩ m2 _ _ _ rfl rfl hStepB2 ?_
              refine wpFrameOutcome_assert_false_unwind_step lensF0
                (calleeLookup [specF1Skip]) bodyF0Skip 1 _ ⟨[]⟩ m2 _
                (.copy ⟨5, []⟩) true .boundsCheck 3 .terminate _ m2 _
                rfl rfl rfl hOpFalse ?_
              refine ⟨postBs1, hUnwEx.1, ?_, hReadHi2⟩
              dsimp only [specF1Unwind]
              rw [hPostBs1Eq]
              rfl
  cases wpFrameOutcome_implies_stackExecutes implTableSkip 2 [specF1Skip]
      callCutTree_skip_2 lensF0 bodyF0Skip 5
        ⟨0, 0, 0, mkLocalsF0 lensF0, none, none, none⟩
        mInit16 ⟨[]⟩ _ hWpSkip with
  | intro out hOut =>
    cases out with
    | returned _ _ => exact False.elim hOut.2
    | unwound _ => exact False.elim hOut.2
    | abortTerminate mSkip =>
      cases hOut.2 with
      | intro postSkip hPost =>
        refine ⟨mSkip, postSkip, hOut.1, hPost.1, hPost.2.1, hPost.2.2, ?_⟩
        intro fuel hWp
        cases fuel with
        | zero => exact hWp
        | succ fuel1 =>
          have hStepB2 : evalStep (Anneal.MirWp.bodyProg bodyF0Unwind) 0
              ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 0,
                  locals := mkLocalsF0 lensF0 }], ⟨[]⟩, mSkip⟩ =
              .step ⟨[{ defId := 0, blockIdx := 2, stmtIdx := 1, locals :=
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate none, .immediate none,
                 .immediate (some (.bool false))] }], ⟨[]⟩, mSkip⟩ := by
            dsimp only [mkLocalsF0]
            refine evalStep_assign_ok bodyF0Unwind _ _ ⟨[]⟩ mSkip mSkip mSkip 5
              MirTy.bool
              (.binaryOp .eq (.copy ⟨2, []⟩) (mkU32Const 0xDEADF101))
              (.bool false)
              [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
               .immediate none, .immediate none, .immediate none]
              _ rfl rfl rfl rfl ?_ ?_
            · refine evalRvalue_binaryOp_ok _ _
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate none, .immediate none, .immediate none]
                _ mSkip mSkip mSkip MirTy.bool .eq (.copy ⟨2, []⟩)
                (mkU32Const 0xDEADF101)
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0x20000011⟩)
                (.scalar ⟨.i32, false, BitVec.ofNat 128 0xDEADF101⟩) _ ?_ rfl
                rfl
              exact evalPrimitiveOperand_copy_indirect _ _ mSkip 2 u32Ty ⟨1, 4⟩
                ⟨4, 2⟩ _ _ rfl rfl rfl rfl hPost.2.2 rfl
            · exact writePlace_immediate_ok _ _ mSkip 5 MirTy.bool
                (.bool false) none rfl rfl rfl
          have hOpFalse : evalPrimitiveOperand bodyF0Unwind.locals
              [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
               .immediate none, .immediate none,
               .immediate (some (.bool false))] mSkip (.copy ⟨5, []⟩) =
              .ok (.bool false,
                [.immediate none, .indirect ⟨1, 0⟩, .indirect ⟨1, 4⟩,
                 .immediate none, .immediate none,
                 .immediate (some (.bool false))], mSkip) :=
            evalPrimitiveOperand_copy_immediate _ _ mSkip 5 MirTy.bool
              (.bool false) rfl rfl rfl
          have hWp1 := wpFrameOutcome_stmt_step_inv lensF0
            (calleeLookup [specF1Unwind]) bodyF0Unwind fuel1 _ ⟨[]⟩ mSkip _ _ _
            rfl rfl hStepB2 hWp
          cases fuel1 with
          | zero => exact hWp1
          | succ fuel2 =>
            exact wpFrameOutcome_assert_false_unwind_inv lensF0
              (calleeLookup [specF1Unwind]) bodyF0Unwind fuel2 _ ⟨[]⟩ mSkip _
              (.copy ⟨5, []⟩) true .boundsCheck 3 .terminate _ mSkip _
              rfl rfl rfl hOpFalse hWp1

/-- Canary fixture helper `bodyBadUnwindResume`. -/
@[expose] def bodyBadUnwindResume : Body :=
  { argumentCount := 0
    locals := [u32Ty]
    basicBlocks :=
      [{ statements := [], terminator := .unwindResume, cleanup := false }] }

/-- Canary fixture helper `specOutOfFrame`. -/
@[expose] def specOutOfFrame : CallSpec :=
  { calleeDefId := defIdF1Normal
    mutLens := lensF1
    precondBool := fun _ _ => true
    ensuresNormalBool := fun _ _ _ _ => false
    ensuresUnwindBool := fun _ _ _ => true
    canNormal := false
    canUnwind := true }

/-- Canary fixture helper `bodyCallOutOfFrame`. -/
@[expose] def bodyCallOutOfFrame : Body :=
  { argumentCount := 0
    locals := [u32Ty]
    basicBlocks :=
      [{ statements := []
         terminator := .call defIdF1Normal [] ⟨0, []⟩ none .continue_
         cleanup := false }] }

/-- Single-cause fail-closed negative regression suite (`[propext]`):
1. `.cleanup` targeting a non-cleanup block (`bb 1`) faults `.undefined`;
2. `.cleanup` targeting an out-of-bounds block (`bb 99`) faults `.undefined`;
3. `.unwindResume` inside a `cleanup = false` block falsifies `wpFrameOutcome`;
4. calling a callee whose `mutLens` exceeds `callerLens` (`lensF1 ⊄ lensF2`)
   falsifies `wpFrameOutcome`, paired with its positive `lensF0` twin
   (`lensF1 ⊆ lensF0`) to certify single-cause isolation;
5. normal return into `onRet = none` faults `.undefined`;
6. unwind into `onUnwind = .unreachable` faults `.undefined`. -/
theorem canary_callStackUnwind_negative_fail_closed_tests :
    evalCallExitStep bodyF1Normal ⟨some 1, .cleanup 1⟩ (.unwind mInit16) =
      .fault .undefined ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .cleanup 99⟩ (.unwind mInit16) =
      .fault .undefined ∧
    (¬ wpFrameOutcome lensF0 (calleeLookup []) bodyBadUnwindResume 2
        ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
            locals := [.immediate none] }], ⟨[]⟩, mInit16⟩
        (fun _ => True)) ∧
    (¬ wpFrameOutcome lensF2 (calleeLookup [specOutOfFrame])
        bodyCallOutOfFrame 2
        ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
            locals := [.immediate none] }], ⟨[]⟩, mInit16⟩
        (fun _ => True)) ∧
    wpFrameOutcome lensF0 (calleeLookup [specOutOfFrame])
      bodyCallOutOfFrame 2
      ⟨[{ defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := [.immediate none] }], ⟨[]⟩, mInit16⟩
      (fun _ => True) ∧
    evalCallExitStep bodyF1Normal ⟨none, .continue_⟩ (.normal .unit mInit16) =
      .fault .undefined ∧
    evalCallExitStep bodyF1Normal ⟨some 1, .unreachable⟩ (.unwind mInit16) =
      .fault .undefined := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro hWp
    unfold wpFrameOutcome at hWp
    dsimp only [bodyBadUnwindResume, checkCleanupBlock] at hWp
    cases hWp.1
  · intro hWp
    unfold wpFrameOutcome at hWp
    dsimp only [bodyCallOutOfFrame, calleeLookup, specOutOfFrame, defIdF1Normal,
      lensF1, lensF2, subLensContained, List.foldr] at hWp
    cases hWp.1
  · unfold wpFrameOutcome
    dsimp only [bodyCallOutOfFrame, calleeLookup, specOutOfFrame, defIdF1Normal,
      lensF1, lensF0, subLensContained, List.foldr]
    refine ⟨rfl, [], [.immediate none], mInit16, EvalCallArgs.nil,
      mkU32Bytes4 0xA0 0xA1 0xA2 0xA3 ++ mkU32Bytes4 0xB0 0xB1 0xB2 0xB3,
      rfl, rfl, ?_, ?_⟩
    · intro hNorm
      exact Bool.noConfusion hNorm
    · intro _ _ _ _
      exact True.intro

end Anneal.CallStackUnwind

end
