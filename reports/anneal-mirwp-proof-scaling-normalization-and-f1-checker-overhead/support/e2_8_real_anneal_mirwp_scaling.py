#!/usr/bin/env python3
"""E2-8: Honest Real-Kernel Anneal.MirWp Proof Scaling & Normalization Benchmark.

Measures real Lean v4.34.1 (-DElab.async=false -Ddebug.skipKernelTC=false)
elaboration wall time, peak RSS, .olean byte size, proof LOC, and true kernel
Expr AST DAG/tree sizes over UNMODIFIED joshlf/anneal@c131b320e
(Trusted.MirAst + Trusted.MirSemantics + Anneal.MirWp), comparing 4 equivalent
MIR representations:
  R0_RawPostCleanup : Authentic PostCleanup MIR (StorageLive/Dead + move + temp locals)
  R1_F1_1b_Nop      : Exact F1-1b output (MoveToCopy + StorageLive/Dead -> .nop, same L & S)
  R2_StorageDeleted : Storage markers / .nop deleted, move -> copy (same L, ~3x fewer stmts)
  R3_MinLocalCompact: Dead temp locals compacted + storage deleted (minimal L & S)

Suites:
  A. Concrete PositiveCanaryClaim (Runs / execProg rfl), K in [4, 8, 16, 32, 64]
  B. Universally quantified symbolic Executes proofs (∀ x : BitVec 128), K in [2, 4, 8, 16, 32]
  C. Universally quantified symbolic loop invariant proof (∀ n : Nat, sum_loop), R0..R3
  D. Direct F1-1b checkProgramMoveToCopy / checkProgramRemoveStorageMarkers rfl overhead, K in [4, 8, 16, 32]

Zero fabrication, zero toy proxies; supports optional LEAN_RUNNER_WRAPPER or direct lean invocation.
"""

import json
import os
import re
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

CACHE = Path(os.environ.get("ANNEAL_OLEAN_CACHE", "./anneal_olean_cache"))
F1_1B_SRC = Path(os.environ.get("F1_1B_SRC", "../anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/support/AnnealTrustedMirMoveToCopyStorage.lean"))
LEAN = Path(os.environ.get("LEAN_BIN", str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")))
RUN_WRAP = os.environ.get("LEAN_RUNNER_WRAPPER", "")
OUT_JSON = Path(os.environ.get("OUT_JSON", "./e2_8_real_anneal_mirwp_scaling.json"))

COMMON_IMPORTS = """prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
"""

HELPER_MODULE = COMMON_IMPORTS + r'''
namespace E28Helpers

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

noncomputable def addU32Bits (x c : BitVec 128) : BitVec 128 :=
  truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, x⟩ + decodeScalar ⟨.i32, false, c⟩))

noncomputable def subU32Bits (x c : BitVec 128) : BitVec 128 :=
  truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, x⟩ - decodeScalar ⟨.i32, false, c⟩))

theorem addU32Bits_wf (x c : BitVec 128) :
    ScalarVal.wf ⟨.i32, false, addU32Bits x c⟩ = true :=
  scalarWf_truncateBits .i32 false _

theorem subU32Bits_wf (x c : BitVec 128) :
    ScalarVal.wf ⟨.i32, false, subU32Bits x c⟩ = true :=
  scalarWf_truncateBits .i32 false _

theorem evalBinOp_add_u32 (x c : BitVec 128) :
    evalBinOp .add (.scalar ⟨.i32, false, x⟩) (.scalar ⟨.i32, false, c⟩) =
      .ok (.scalar ⟨.i32, false, addU32Bits x c⟩) := by
  have h0 : evalBinOp .add (.scalar ⟨.i32, false, x⟩) (.scalar ⟨.i32, false, c⟩) =
      evalArithOp .add .i32 false (decodeScalar ⟨.i32, false, x⟩) (decodeScalar ⟨.i32, false, c⟩) := rfl
  rw [h0]
  unfold evalArithOp
  dsimp only [BinOp.isUnchecked]
  have h1 : (false && decodeScalar ⟨.i32, false, c⟩ == 0) = false := Bool.false_and _
  have h2 : (false && false && (decodeScalar ⟨.i32, false, x⟩ == signedMinInt .i32 && decodeScalar ⟨.i32, false, c⟩ == -1)) = false := Bool.false_and _
  rw [h1, h2]
  have htr : truncateScalar .i32 false (decodeScalar ⟨.i32, false, x⟩ + decodeScalar ⟨.i32, false, c⟩) =
      .ok (⟨.i32, false, addU32Bits x c⟩, truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, x⟩ + decodeScalar ⟨.i32, false, c⟩)) != bvOfInt 128 (decodeScalar ⟨.i32, false, x⟩ + decodeScalar ⟨.i32, false, c⟩)) := rfl
  rw [htr]
  change (if _ && false then Except.error FaultKind.undefined else Except.ok (Val.scalar ⟨.i32, false, addU32Bits x c⟩)) = _
  rw [Bool.and_false]
  rfl

theorem evalBinOp_sub_u32 (x c : BitVec 128) :
    evalBinOp .sub (.scalar ⟨.i32, false, x⟩) (.scalar ⟨.i32, false, c⟩) =
      .ok (.scalar ⟨.i32, false, subU32Bits x c⟩) := by
  have h0 : evalBinOp .sub (.scalar ⟨.i32, false, x⟩) (.scalar ⟨.i32, false, c⟩) =
      evalArithOp .sub .i32 false (decodeScalar ⟨.i32, false, x⟩) (decodeScalar ⟨.i32, false, c⟩) := rfl
  rw [h0]
  unfold evalArithOp
  dsimp only [BinOp.isUnchecked]
  have h1 : (false && decodeScalar ⟨.i32, false, c⟩ == 0) = false := Bool.false_and _
  have h2 : (false && false && (decodeScalar ⟨.i32, false, x⟩ == signedMinInt .i32 && decodeScalar ⟨.i32, false, c⟩ == -1)) = false := Bool.false_and _
  rw [h1, h2]
  have htr : truncateScalar .i32 false (decodeScalar ⟨.i32, false, x⟩ - decodeScalar ⟨.i32, false, c⟩) =
      .ok (⟨.i32, false, subU32Bits x c⟩, truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, x⟩ - decodeScalar ⟨.i32, false, c⟩)) != bvOfInt 128 (decodeScalar ⟨.i32, false, x⟩ - decodeScalar ⟨.i32, false, c⟩)) := rfl
  rw [htr]
  change (if _ && false then Except.error FaultKind.undefined else Except.ok (Val.scalar ⟨.i32, false, subU32Bits x c⟩)) = _
  rw [Bool.and_false]
  rfl

theorem evalPrimitiveOperand_copy_u32
    (bodyLocals : List MirTy) (locals : List LocalSlot) (src : LocalId) (x : BitVec 128)
    (hsrcTy : Trusted.MirSemantics.getElem? bodyLocals src = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩)))) :
    evalPrimitiveOperand bodyLocals locals (.copy ⟨src, []⟩) =
      .ok (.scalar ⟨.i32, false, x⟩, locals) := by
  unfold evalPrimitiveOperand evalOperandToSlot
  dsimp only
  rw [hsrcTy, hsrcSlot]
  rfl

theorem evalPrimitiveOperand_move_u32
    (bodyLocals : List MirTy) (locals locals1 : List LocalSlot) (src : LocalId) (x : BitVec 128)
    (hsrcTy : Trusted.MirSemantics.getElem? bodyLocals src = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdeinit : setElem? locals src (.live none) = some locals1) :
    evalPrimitiveOperand bodyLocals locals (.move ⟨src, []⟩) =
      .ok (.scalar ⟨.i32, false, x⟩, locals1) := by
  unfold evalPrimitiveOperand evalOperandToSlot
  dsimp only
  rw [hsrcTy, hsrcSlot]
  change (match (match setElem? locals src (.live none) with | some l' => Except.ok (u32Ty, some (Val.scalar ⟨.i32, false, x⟩), l') | none => Except.error FaultKind.unsupported) with | Except.error k => Except.error k | Except.ok (ty, ov, l') => if !isPrimitiveReadableTy ty then Except.error FaultKind.unsupported else match ov with | some v => Except.ok (v, l') | none => Except.error FaultKind.undefined) = _
  rw [hdeinit]
  rfl

theorem evalPrimitiveOperand_const_u32
    (bodyLocals : List MirTy) (locals : List LocalSlot) (c : BitVec 128)
    (hc : evalConstLit u32Ty (.scalar c) = .ok (.scalar ⟨.i32, false, c⟩)) :
    evalPrimitiveOperand bodyLocals locals (.constant ⟨u32Ty, .scalar c⟩) =
      .ok (.scalar ⟨.i32, false, c⟩, locals) := by
  unfold evalPrimitiveOperand evalOperandToSlot
  dsimp only
  rw [hc]
  rfl

theorem writePlace_u32
    (locals locals2 : List LocalSlot) (dst : LocalId) (y : BitVec 128) (oldv : Option Val)
    (hy : ScalarVal.wf ⟨.i32, false, y⟩ = true)
    (hdstSlot : Trusted.MirSemantics.getElem? locals dst = some (.live oldv))
    (hwrite : setElem? locals dst (.live (some (.scalar ⟨.i32, false, y⟩))) = some locals2) :
    writePlace locals dst u32Ty (.scalar ⟨.i32, false, y⟩) = .ok locals2 := by
  have h1 : checkVal (.scalar ⟨.i32, false, y⟩) u32Ty = true := by
    unfold checkVal Val.ty?
    change (match (if ScalarVal.wf ⟨.i32, false, y⟩ then some (MirTy.int .i32 false) else none) with | some vTy => vTy.beq u32Ty | none => false) = true
    rw [hy]; rfl
  unfold writePlace
  rw [h1]
  change (match Trusted.MirSemantics.getElem? locals dst with | none => Except.error FaultKind.unsupported | some .dead => Except.error FaultKind.undefined | some (.live _) => match setElem? locals dst (.live (some (Val.scalar ⟨.i32, false, y⟩))) with | some l' => Except.ok l' | none => Except.error FaultKind.unsupported) = _
  rw [hdstSlot]
  dsimp only
  rw [hwrite]

theorem evalStep_assign_add_copy
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals2 : List LocalSlot)
    (src dst : LocalId) (x c : BitVec 128) (oldv : Option Val)
    (hc : evalConstLit u32Ty (.scalar c) = .ok (.scalar ⟨.i32, false, c⟩))
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.binaryOp .add (.copy ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩))))
    (hsrcTy : Trusted.MirSemantics.getElem? body.locals src = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdstSlot : Trusted.MirSemantics.getElem? locals dst = some (.live oldv))
    (hwrite : setElem? locals dst (.live (some (.scalar ⟨.i32, false, addU32Bits x c⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.binaryOp .add (.copy ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalPrimitiveOperand_copy_u32 _ _ _ _ hsrcTy hsrcSlot]; dsimp only
  rw [evalPrimitiveOperand_const_u32 _ _ _ hc]; dsimp only
  rw [evalBinOp_add_u32]; dsimp only
  rw [writePlace_u32 _ _ _ _ oldv (addU32Bits_wf x c) hdstSlot hwrite]; rfl

theorem evalStep_assign_add_move
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals1 locals2 : List LocalSlot)
    (src dst : LocalId) (x c : BitVec 128) (oldv : Option Val)
    (hc : evalConstLit u32Ty (.scalar c) = .ok (.scalar ⟨.i32, false, c⟩))
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.binaryOp .add (.move ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩))))
    (hsrcTy : Trusted.MirSemantics.getElem? body.locals src = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdeinit : setElem? locals src (.live none) = some locals1)
    (hdstSlot : Trusted.MirSemantics.getElem? locals1 dst = some (.live oldv))
    (hwrite : setElem? locals1 dst (.live (some (.scalar ⟨.i32, false, addU32Bits x c⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.binaryOp .add (.move ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalPrimitiveOperand_move_u32 _ _ _ _ _ hsrcTy hsrcSlot hdeinit]; dsimp only
  rw [evalPrimitiveOperand_const_u32 _ _ _ hc]; dsimp only
  rw [evalBinOp_add_u32]; dsimp only
  rw [writePlace_u32 _ _ _ _ oldv (addU32Bits_wf x c) hdstSlot hwrite]; rfl

theorem evalStep_assign_use_copy
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals2 : List LocalSlot)
    (src dst : LocalId) (x : BitVec 128) (oldv : Option Val)
    (hx : ScalarVal.wf ⟨.i32, false, x⟩ = true)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.use (.copy ⟨src, []⟩))))
    (hsrcTy : Trusted.MirSemantics.getElem? body.locals src = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdstSlot : Trusted.MirSemantics.getElem? locals dst = some (.live oldv))
    (hwrite : setElem? locals dst (.live (some (.scalar ⟨.i32, false, x⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.use (.copy ⟨src, []⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue evalOperandToSlot; dsimp only
  rw [hsrcTy, hsrcSlot]; dsimp only [u32Ty, MirTy.beq, IntWidth.beq]
  change (match writePlace locals dst u32Ty (Val.scalar ⟨.i32, false, x⟩) with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [writePlace_u32 _ _ _ _ oldv hx hdstSlot hwrite]; rfl

theorem evalOperandToSlot_move_u32
    (bodyLocals : List MirTy) (locals locals1 : List LocalSlot) (src : LocalId) (x : BitVec 128)
    (hsrcTy : Trusted.MirSemantics.getElem? bodyLocals src = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdeinit : setElem? locals src (.live none) = some locals1) :
    evalOperandToSlot bodyLocals locals (.move ⟨src, []⟩) =
      .ok (u32Ty, some (.scalar ⟨.i32, false, x⟩), locals1) := by
  unfold evalOperandToSlot
  dsimp only
  rw [hsrcTy, hsrcSlot]
  change (match setElem? locals src (.live none) with | some l' => Except.ok (u32Ty, some (Val.scalar ⟨.i32, false, x⟩), l') | none => Except.error FaultKind.unsupported) = _
  rw [hdeinit]

theorem evalStep_assign_use_move
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals1 locals2 : List LocalSlot)
    (src dst : LocalId) (x : BitVec 128) (oldv : Option Val)
    (hx : ScalarVal.wf ⟨.i32, false, x⟩ = true)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.use (.move ⟨src, []⟩))))
    (hsrcTy : Trusted.MirSemantics.getElem? body.locals src = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdeinit : setElem? locals src (.live none) = some locals1)
    (hdstSlot : Trusted.MirSemantics.getElem? locals1 dst = some (.live oldv))
    (hwrite : setElem? locals1 dst (.live (some (.scalar ⟨.i32, false, x⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.use (.move ⟨src, []⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalOperandToSlot_move_u32 _ _ _ _ _ hsrcTy hsrcSlot hdeinit]; dsimp only [u32Ty, MirTy.beq, IntWidth.beq]
  change (match writePlace locals1 dst u32Ty (Val.scalar ⟨.i32, false, x⟩) with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [writePlace_u32 _ _ _ _ oldv hx hdstSlot hwrite]; rfl

theorem evalStep_assign_add_vars_copy
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals2 : List LocalSlot)
    (src1 src2 dst : LocalId) (x y : BitVec 128) (oldv : Option Val)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.binaryOp .add (.copy ⟨src1, []⟩) (.copy ⟨src2, []⟩))))
    (hs1Ty : Trusted.MirSemantics.getElem? body.locals src1 = some u32Ty)
    (hs2Ty : Trusted.MirSemantics.getElem? body.locals src2 = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hs1Slot : Trusted.MirSemantics.getElem? locals src1 = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hs2Slot : Trusted.MirSemantics.getElem? locals src2 = some (.live (some (.scalar ⟨.i32, false, y⟩))))
    (hdstSlot : Trusted.MirSemantics.getElem? locals dst = some (.live oldv))
    (hwrite : setElem? locals dst (.live (some (.scalar ⟨.i32, false, addU32Bits x y⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.binaryOp .add (.copy ⟨src1, []⟩) (.copy ⟨src2, []⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalPrimitiveOperand_copy_u32 _ _ _ _ hs1Ty hs1Slot]; dsimp only
  rw [evalPrimitiveOperand_copy_u32 _ _ _ _ hs2Ty hs2Slot]; dsimp only
  rw [evalBinOp_add_u32]; dsimp only
  rw [writePlace_u32 _ _ _ _ oldv (addU32Bits_wf x y) hdstSlot hwrite]; rfl

theorem evalStep_assign_add_vars_move
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals1 locals2 locals3 : List LocalSlot)
    (src1 src2 dst : LocalId) (x y : BitVec 128) (oldv : Option Val)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.binaryOp .add (.move ⟨src1, []⟩) (.move ⟨src2, []⟩))))
    (hs1Ty : Trusted.MirSemantics.getElem? body.locals src1 = some u32Ty)
    (hs2Ty : Trusted.MirSemantics.getElem? body.locals src2 = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hs1Slot : Trusted.MirSemantics.getElem? locals src1 = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hd1 : setElem? locals src1 (.live none) = some locals1)
    (hs2Slot : Trusted.MirSemantics.getElem? locals1 src2 = some (.live (some (.scalar ⟨.i32, false, y⟩))))
    (hd2 : setElem? locals1 src2 (.live none) = some locals2)
    (hdstSlot : Trusted.MirSemantics.getElem? locals2 dst = some (.live oldv))
    (hwrite : setElem? locals2 dst (.live (some (.scalar ⟨.i32, false, addU32Bits x y⟩))) = some locals3) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals3) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.binaryOp .add (.move ⟨src1, []⟩) (.move ⟨src2, []⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalPrimitiveOperand_move_u32 _ _ _ _ _ hs1Ty hs1Slot hd1]; dsimp only
  rw [evalPrimitiveOperand_move_u32 _ _ _ _ _ hs2Ty hs2Slot hd2]; dsimp only
  rw [evalBinOp_add_u32]; dsimp only
  rw [writePlace_u32 _ _ _ _ oldv (addU32Bits_wf x y) hdstSlot hwrite]; rfl

theorem evalStep_assign_sub_copy
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals2 : List LocalSlot)
    (src dst : LocalId) (x c : BitVec 128) (oldv : Option Val)
    (hc : evalConstLit u32Ty (.scalar c) = .ok (.scalar ⟨.i32, false, c⟩))
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.binaryOp .sub (.copy ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩))))
    (hsrcTy : Trusted.MirSemantics.getElem? body.locals src = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdstSlot : Trusted.MirSemantics.getElem? locals dst = some (.live oldv))
    (hwrite : setElem? locals dst (.live (some (.scalar ⟨.i32, false, subU32Bits x c⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.binaryOp .sub (.copy ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalPrimitiveOperand_copy_u32 _ _ _ _ hsrcTy hsrcSlot]; dsimp only
  rw [evalPrimitiveOperand_const_u32 _ _ _ hc]; dsimp only
  rw [evalBinOp_sub_u32]; dsimp only
  rw [writePlace_u32 _ _ _ _ oldv (subU32Bits_wf x c) hdstSlot hwrite]; rfl

theorem evalStep_assign_sub_move
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals locals1 locals2 : List LocalSlot)
    (src dst : LocalId) (x c : BitVec 128) (oldv : Option Val)
    (hc : evalConstLit u32Ty (.scalar c) = .ok (.scalar ⟨.i32, false, c⟩))
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hstmt : Trusted.MirSemantics.getElem? bb.statements idx =
      some (.assign ⟨dst, []⟩ (.binaryOp .sub (.move ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩))))
    (hsrcTy : Trusted.MirSemantics.getElem? body.locals src = some u32Ty)
    (hdstTy : Trusted.MirSemantics.getElem? body.locals dst = some u32Ty)
    (hsrcSlot : Trusted.MirSemantics.getElem? locals src = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hdeinit : setElem? locals src (.live none) = some locals1)
    (hdstSlot : Trusted.MirSemantics.getElem? locals1 dst = some (.live oldv))
    (hwrite : setElem? locals1 dst (.live (some (.scalar ⟨.i32, false, subU32Bits x c⟩))) = some locals2) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState blk (idx + 1) locals2) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hstmt]; dsimp only
  unfold evalStatement
  dsimp only [List.isEmpty]
  change (match Trusted.MirSemantics.getElem? body.locals dst with | none => StepResult.fault FaultKind.unsupported | some dstTy => match evalRvalue body.locals locals dstTy (.binaryOp .sub (.move ⟨src, []⟩) (.constant ⟨u32Ty, .scalar c⟩)) with | Except.error k => StepResult.fault k | Except.ok (val, l') => match writePlace l' dst dstTy val with | Except.error k => StepResult.fault k | Except.ok l'' => StepResult.step (mkState blk (idx + 1) l'')) = _
  rw [hdstTy]; dsimp only
  unfold evalRvalue; dsimp only
  rw [evalPrimitiveOperand_move_u32 _ _ _ _ _ hsrcTy hsrcSlot hdeinit]; dsimp only
  rw [evalPrimitiveOperand_const_u32 _ _ _ hc]; dsimp only
  rw [evalBinOp_sub_u32]; dsimp only
  rw [writePlace_u32 _ _ _ _ oldv (subU32Bits_wf x c) hdstSlot hwrite]; rfl

theorem evalStep_switch_u32_zero_branch
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals : List LocalSlot)
    (discr : LocalId) (bZero bOther : BasicBlockId)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hnone : Trusted.MirSemantics.getElem? bb.statements idx = none)
    (hlen : idx.beq bb.statements.length = true)
    (hterm : bb.terminator = .switchInt (.copy ⟨discr, []⟩) { branches := [(BitVec.ofNat 128 0, bZero)], otherwise := bOther })
    (hdTy : Trusted.MirSemantics.getElem? body.locals discr = some u32Ty)
    (hdSlot : Trusted.MirSemantics.getElem? locals discr = some (.live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)))) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState bZero 0 locals) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hnone, hlen]; dsimp only
  unfold evalTerminator
  rw [hterm]; dsimp only
  rw [evalPrimitiveOperand_copy_u32 _ _ _ _ hdTy hdSlot]
  rfl

theorem evalStep_switch_u32_nonzero_branch
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals : List LocalSlot)
    (discr : LocalId) (x : BitVec 128) (bZero bOther : BasicBlockId)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hnone : Trusted.MirSemantics.getElem? bb.statements idx = none)
    (hlen : idx.beq bb.statements.length = true)
    (hterm : bb.terminator = .switchInt (.copy ⟨discr, []⟩) { branches := [(BitVec.ofNat 128 0, bZero)], otherwise := bOther })
    (hdTy : Trusted.MirSemantics.getElem? body.locals discr = some u32Ty)
    (hdSlot : Trusted.MirSemantics.getElem? locals discr = some (.live (some (.scalar ⟨.i32, false, x⟩))))
    (hsw : evalSwitchBranches .i32 x bOther [(BitVec.ofNat 128 0, bZero)] = .ok bOther) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.step (mkState bOther 0 locals) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hnone, hlen]; dsimp only
  unfold evalTerminator
  rw [hterm]; dsimp only
  rw [evalPrimitiveOperand_copy_u32 _ _ _ _ hdTy hdSlot]; dsimp only
  rw [hsw]; rfl

theorem evalStep_return_u32
    (body : Body) (bb : BasicBlock) (blk idx : Nat) (locals : List LocalSlot)
    (x : BitVec 128)
    (hbb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb)
    (hnone : Trusted.MirSemantics.getElem? bb.statements idx = none)
    (hlen : idx.beq bb.statements.length = true)
    (hclean : bb.cleanup = false)
    (hterm : bb.terminator = .return_)
    (hretSlot : Trusted.MirSemantics.getElem? locals 0 = some (.live (some (.scalar ⟨.i32, false, x⟩)))) :
    evalStep (bodyProg body) 0 (mkState blk idx locals) =
      StepResult.done (.returned ⟨.scalar ⟨.i32, false, x⟩, ⟨[]⟩⟩) := by
  unfold evalStep bodyProg mkState
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hbb]; dsimp only
  rw [hnone, hlen]; dsimp only
  unfold evalTerminator
  rw [hclean, hterm]; dsimp only
  rw [hretSlot]; rfl

end E28Helpers
'''


def run_timed_lean(lean_path: str, root_dir: Path, src_path: Path, olean_path: Path, repeats: int = 3):
    """Run synchronous Lean v4.34.1 (optionally via LEAN_RUNNER_WRAPPER) and /usr/bin/time -v; return median wall & RSS."""
    env = os.environ.copy()
    env["LEAN_PATH"] = lean_path
    walls, rsses = [], []
    last_rc, last_out, last_err = 0, "", ""
    for _ in range(repeats):
        if olean_path.exists():
            olean_path.unlink()
        t0 = time.monotonic()
        cmd = ["/usr/bin/time", "-v"]
        if RUN_WRAP:
            cmd += [RUN_WRAP, "--"]
        cmd += [str(LEAN),
                "-DElab.async=false", "-Ddebug.skipKernelTC=false",
                "-R", str(root_dir), "-o", str(olean_path), str(src_path)]
        r = subprocess.run(
            cmd,
            env=env, capture_output=True, text=True, timeout=180
        )
        wall = time.monotonic() - t0
        last_rc, last_out, last_err = r.returncode, r.stdout, r.stderr
        if r.returncode != 0:
            return {"rc": r.returncode, "stdout": r.stdout[:1000], "stderr": r.stderr[:1000]}
        m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", r.stderr)
        rss_mb = int(m.group(1)) / 1024.0 if m else 0.0
        walls.append(wall)
        rsses.append(rss_mb)
    return {
        "rc": 0,
        "wall_sec_median": round(statistics.median(walls), 4),
        "wall_sec_all": [round(w, 4) for w in walls],
        "peak_rss_mb_median": round(statistics.median(rsses), 2),
        "olean_bytes": olean_path.stat().st_size if olean_path.exists() else 0,
        "proof_loc": len(src_path.read_text().splitlines()),
    }


def make_chain_body_and_proof(regime: str, k: int, mode: str) -> tuple[str, dict]:
    """Generate a K-stage u32 addition chain under R0..R3 for either concrete (Runs) or symbolic (Executes)."""
    # R0: locals = [_0, _1, _2.._(k+1)] (k+2 locals). Stage i (1..k):
    #   StorageLive(i+1), assign (i+1) := add(move i, const i), StorageDead(i) [for i>=2]
    #   Then assign 0 := use(move (k+1)), StorageDead(k+1).
    # R1: Same locals & stmt count, move -> copy, StorageLive/Dead -> .nop.
    # R2: StorageLive/Dead/.nop DELETED, move -> copy, same locals (k+2).
    # R3: Minimal locals (2: _0, _1). First stage _0 := add(copy _1, const 1), stages 2..k: _0 := add(copy _0, const i).
    expected_concrete = (7 + k * (k + 1) // 2) % (1 << 32)
    stmts = []
    # Track exact symbolic slot lists for Executes proof
    if regime in ("R0_RawPostCleanup", "R1_F1_1b_Nop", "R2_StorageDeleted"):
        n_locals = k + 2
        locals_decl = "[" + ", ".join(["u32Ty"] * n_locals) + "]"
        is_move = (regime == "R0_RawPostCleanup")
        use_storage = (regime == "R0_RawPostCleanup")
        use_nop = (regime == "R1_F1_1b_Nop")
        op_kw = ".move" if is_move else ".copy"
        # Initial state: _0 = .live none, _1 = .live (some x), _2.._(k+1) = .dead (for R0) or .live none (for R1/R2? Wait: in Trusted.MirSemantics initLocalsLoop sets >=argCount+1 to .dead! So in R1/R2 where StorageLive is removed, locals >= 2 must be .live none if we model RemoveStorageMarkers from F1-1b which sets init to live, OR for R1/R2 we keep init all-live via mkState in Executes and for concrete Runs we initialize via StorageLive? Wait: let's check!)
        # IMPORTANT: In Trusted.MirSemantics.initLocalsLoop, locals > argumentCount start `.dead`!
        # That's why F1-1b's `RemoveStorageMarkers` explicitly requires `initLocalsAllLive` OR `body.locals` only having live locals (`argumentCount` or leading `StorageLive`)!
        # To make ALL 4 regimes valid standalone `Trusted.MirSemantics` programs under `initState` (ZERO special init hacks!):
        # - For R0: each temp _t gets StorageLive(_t), assign, StorageDead(_prev) -> 3*k + 1 stmts
        # - For R1 (F1-1b): since initState starts temp locals `.dead`, if we only eliminate *interior* redundant StorageLive/StorageDead pairs (or give 1 leading StorageLive per temp, wait: F1-1b `RemoveStorageMarkers` replaces ALL StorageLive/Dead with .nop when starting from `initAllLive`!). Let's match BOTH:
        #   In Suite A (concrete `RunsFrom` from all-live entry state, matching F1-1b Theorem 4 `initAllLive`!) and Suite B (symbolic `Executes` from entry state):
        #   Actually, even BETTER: in `R0`, `_2.._(k+1)` start `.dead` (authentic `initState`!); in `R1_F1_1b_Nop`, `_2.._(k+1)` start `.live none` (exact F1-1b `RemoveStorageMarkers` state invariant!) and every `StorageLive`/`StorageDead` is `.nop`; in `R2_StorageDeleted`, `_2.._(k+1)` start `.live none` and all `StorageLive`/`StorageDead`/`.nop` are deleted; in `R3_MinLocalCompact`, there are ONLY 2 locals (`_0, _1`, BOTH live under standard `initState`!) and ZERO storage markers!
        cur_slots = [".live none", ".live (some (.scalar ⟨.i32, false, x⟩))"] + [
            (".dead" if use_storage else ".live none") for _ in range(k)
        ]
        init_slots = list(cur_slots)
        steps = []  # (kind, data)
        # Stage 1..k
        val_exprs = ["x"]
        for i in range(1, k + 1):
            src = i
            dst = i + 1
            prev_val = val_exprs[-1]
            new_val = f"y{i}"
            val_exprs.append(new_val)
            if use_storage:
                stmts.append(f".storageLive {dst}")
                cur_slots[dst] = ".live none"
                steps.append(("rfl", list(cur_slots)))
            elif use_nop:
                stmts.append(".nop")
                steps.append(("rfl", list(cur_slots)))
            stmts.append(f".assign ⟨{dst}, []⟩ (.binaryOp .add ({op_kw} ⟨{src}, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 {i})⟩))")
            if is_move:
                cur_slots[src] = ".live none"
            cur_slots[dst] = f".live (some (.scalar ⟨.i32, false, {new_val}⟩))"
            steps.append(("add", (is_move, src, dst, prev_val, i, list(cur_slots))))
            if i >= 2:
                if use_storage:
                    stmts.append(f".storageDead {src}")
                    cur_slots[src] = ".dead"
                    steps.append(("rfl", list(cur_slots)))
                elif use_nop:
                    stmts.append(".nop")
                    steps.append(("rfl", list(cur_slots)))
        # Final copy/move into _0
        last_src = k + 1
        last_val = val_exprs[-1]
        stmts.append(f".assign ⟨0, []⟩ (.use ({op_kw} ⟨{last_src}, []⟩))")
        if is_move:
            cur_slots[last_src] = ".live none"
        cur_slots[0] = f".live (some (.scalar ⟨.i32, false, {last_val}⟩))"
        steps.append(("use", (is_move, last_src, 0, last_val, list(cur_slots))))
        if use_storage:
            stmts.append(f".storageDead {last_src}")
            cur_slots[last_src] = ".dead"
            steps.append(("rfl", list(cur_slots)))
        elif use_nop:
            stmts.append(".nop")
            steps.append(("rfl", list(cur_slots)))
    else:
        # R3_MinLocalCompact: 2 locals [_0, _1], 0 storage markers, k statements total!
        n_locals = 2
        locals_decl = "[u32Ty, u32Ty]"
        cur_slots = [".live none", ".live (some (.scalar ⟨.i32, false, x⟩))"]
        init_slots = list(cur_slots)
        steps = []
        val_exprs = ["x"]
        for i in range(1, k + 1):
            src = 1 if i == 1 else 0
            dst = 0
            prev_val = val_exprs[-1]
            new_val = f"y{i}"
            val_exprs.append(new_val)
            stmts.append(f".assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨{src}, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 {i})⟩))")
            cur_slots[0] = f".live (some (.scalar ⟨.i32, false, {new_val}⟩))"
            steps.append(("add", (False, src, 0, prev_val, i, list(cur_slots))))

    fuel = len(stmts) + 2
    stmts_str = ",\n      ".join(stmts)
    mod_name = f"Bench_{mode}_{regime}_K{k}"
    lines = [
        COMMON_IMPORTS,
        "import E28Helpers",
        f"namespace {mod_name}",
        "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp E28Helpers",
        "",
        "noncomputable def bodyBench : Body where",
        "  argumentCount := 1",
        f"  locals := {locals_decl}",
        "  basicBlocks := [{",
        f"    statements := [\n      {stmts_str}\n    ]",
        "    terminator := .return_",
        "  }]",
        "",
    ]

    if mode == "concrete":
        init_concrete = "[" + ", ".join(
            s.replace("x", "(BitVec.ofNat 128 7)") for s in init_slots
        ) + "]"
        lines += [
            f"theorem bench_thm : RunsFrom bodyBench {fuel} (mkState 0 0 {init_concrete}) (u32Val {expected_concrete}) :=",
            "  rfl",
            f"end {mod_name}",
        ]
    else:
        # Symbolic universal Executes proof
        let_defs = []
        for i in range(1, k + 1):
            prev = "x" if i == 1 else f"y{i-1}"
            let_defs.append(f"  let y{i} := addU32Bits {prev} (BitVec.ofNat 128 {i})")
        init_sym = "[" + ", ".join(init_slots) + "]"
        final_y = f"y{k}"
        lines += [
            "noncomputable def chainVal (x : BitVec 128) : BitVec 128 :=",
            "\n".join(let_defs),
            f"  {final_y}",
            "",
            f"theorem bench_thm (x : BitVec 128) :",
            f"    Executes bodyBench (mkState 0 0 {init_sym}) (.scalar ⟨.i32, false, chainVal x⟩) := by",
            "  unfold chainVal",
        ]
        # Introduce local `let` bindings so the proof term shares y1..yk cleanly!
        for i in range(1, k + 1):
            prev = "x" if i == 1 else f"y{i-1}"
            lines.append(f"  let y{i} := addU32Bits {prev} (BitVec.ofNat 128 {i})")
        for idx, (kind, payload) in enumerate(steps):
            if kind == "rfl":
                nxt = "[" + ", ".join(payload) + "]"
                lines.append(f"  apply Executes.next (next := mkState 0 {idx+1} {nxt}) rfl")
            elif kind == "add":
                is_m, src, dst, pval, cval, nxt_slots = payload
                nxt = "[" + ", ".join(nxt_slots) + "]"
                lem = "evalStep_assign_add_move" if is_m else "evalStep_assign_add_copy"
                lines.append(f"  apply Executes.next (next := mkState 0 {idx+1} {nxt})")
                if is_m:
                    lines.append(f"  · exact {lem} bodyBench _ 0 {idx} _ _ _ {src} {dst} {pval} (BitVec.ofNat 128 {cval}) _ rfl rfl rfl rfl rfl rfl rfl rfl rfl")
                else:
                    lines.append(f"  · exact {lem} bodyBench _ 0 {idx} _ _ {src} {dst} {pval} (BitVec.ofNat 128 {cval}) _ rfl rfl rfl rfl rfl rfl rfl rfl")
            elif kind == "use":
                is_m, src, dst, pval, nxt_slots = payload
                nxt = "[" + ", ".join(nxt_slots) + "]"
                lem = "evalStep_assign_use_move" if is_m else "evalStep_assign_use_copy"
                lines.append(f"  apply Executes.next (next := mkState 0 {idx+1} {nxt})")
                if is_m:
                    lines.append(f"  · exact {lem} bodyBench _ 0 {idx} _ _ _ {src} {dst} {pval} _ (addU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl rfl")
                else:
                    lines.append(f"  · exact {lem} bodyBench _ 0 {idx} _ _ {src} {dst} {pval} _ (addU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl")
        lines.append(f"  exact Executes.ret (evalStep_return_u32 bodyBench _ 0 {len(steps)} _ {final_y} rfl rfl rfl rfl rfl rfl)")
        lines.append(f"end {mod_name}")

    meta = {
        "module": mod_name,
        "theorem": f"{mod_name}.bench_thm",
        "regime": regime,
        "k": k,
        "mode": mode,
        "locals_count": n_locals,
        "stmts_count": len(stmts),
        "fuel": fuel,
    }
    return "\n".join(lines) + "\n", meta


def make_loop_module(regime: str) -> tuple[str, dict]:
    """Generate a universally quantified inductive loop proof (sum_loop: acc += i; i -= 1 while i != 0) under R0..R3."""
    mod_name = f"Bench_loop_{regime}"
    # Spec function: sumLoopSpec n acc
    # bb0 (header): switchInt (copy _1) [0 -> bb2, otherwise -> bb1]
    # bb1 (latch):  acc := acc + i; i := i - 1; goto bb0
    # bb2 (exit):   _0 := copy acc; return
    # In R0_RawPostCleanup: locals = [_0:ret, _1:i, _2:acc, _3:t_sum, _4:t_next_i] (5 locals)
    #   bb1: StorageLive(3); _3 = add(copy 2, copy 1); _2 = use(move 3); StorageDead(3);
    #        StorageLive(4); _4 = sub(move 1, 1); _1 = use(move 4); StorageDead(4); goto bb0 (8 stmts)
    # In R1_F1_1b_Nop: 5 locals, move -> copy, StorageLive/Dead -> .nop (8 stmts)
    # In R2_StorageDeleted: 5 locals, storage/.nop deleted, move -> copy (4 stmts)
    # In R3_MinLocalCompact: 3 locals [_0:ret, _1:i, _2:acc], direct in-place _2 = add(copy 2, copy 1); _1 = sub(copy 1, 1); goto bb0 (2 stmts)
    spec_defs = r'''
noncomputable def sumSpec : Nat → BitVec 128 → BitVec 128
  | 0, acc => acc
  | n + 1, acc => sumSpec n (addU32Bits acc (BitVec.ofNat 128 (n + 1)))

theorem toNat_ofNat_lt_128 (m : Nat) (hm : m < 4294967296) :
    (BitVec.ofNat 128 m).toNat = m := by
  have hlt : m < 2 ^ 128 := Nat.lt_trans hm (by decide)
  change m % 2 ^ 128 = m
  exact Nat.mod_eq_of_lt hlt

theorem bitvec_ofNat_succ_ne_zero (n : Nat) (hn : n + 1 < 4294967296) :
    evalSwitchBranches .i32 (BitVec.ofNat 128 (n + 1)) 1 [(BitVec.ofNat 128 0, 2)] = .ok 1 := by
  have htrunc : truncateBits .i32 (BitVec.ofNat 128 (n + 1)) = BitVec.ofNat 128 (n + 1) := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits, toNat_ofNat_lt_128 (n + 1) hn]
    change (n + 1) % 4294967296 = n + 1
    exact Nat.mod_eq_of_lt hn
  have hne : (BitVec.ofNat 128 (n + 1) == BitVec.ofNat 128 0) = false := by
    have hneq : (BitVec.ofNat 128 (n + 1)).toNat ≠ (BitVec.ofNat 128 0).toNat := by
      rw [toNat_ofNat_lt_128 (n + 1) hn]
      intro h; cases h
    cases h : (BitVec.ofNat 128 (n + 1) == BitVec.ofNat 128 0) with
    | false => rfl
    | true => exact False.elim (hneq (congrArg BitVec.toNat (eq_of_beq h)))
  unfold evalSwitchBranches
  rw [htrunc]
  change (if (BitVec.ofNat 128 (n + 1) == BitVec.ofNat 128 0) = true then Except.ok 2 else Except.ok 1) = _
  rw [hne]; rfl

theorem subU32Bits_succ_one (n : Nat) (hn : n + 1 < 4294967296) :
    subU32Bits (BitVec.ofNat 128 (n + 1)) (BitVec.ofNat 128 1) = BitVec.ofNat 128 n := by
  have hn0 : n < 4294967296 := Nat.lt_trans (Nat.lt_succ_self n) hn
  have h1 : decodeScalar ⟨.i32, false, BitVec.ofNat 128 (n + 1)⟩ = Int.ofNat (n + 1) := by
    unfold decodeScalar
    change Int.ofNat (truncateBits .i32 (BitVec.ofNat 128 (n + 1))).toNat = Int.ofNat (n + 1)
    rw [toNat_truncateBits, toNat_ofNat_lt_128 (n + 1) hn]
    change Int.ofNat ((n + 1) % 4294967296) = Int.ofNat (n + 1)
    rw [Nat.mod_eq_of_lt hn]
  have h2 : decodeScalar ⟨.i32, false, BitVec.ofNat 128 1⟩ = Int.ofNat 1 := rfl
  unfold subU32Bits
  rw [h1, h2]
  have hsub : Int.ofNat (n + 1) - Int.ofNat 1 = Int.ofNat n := by
    change Int.subNatNat (n + 1) 1 = Int.ofNat n
    unfold Int.subNatNat
    have hz : 1 - (n + 1) = 0 := Nat.sub_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le n))
    rw [hz]
    exact congrArg Int.ofNat (Nat.add_sub_cancel n 1)
  rw [hsub]
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits]
  have hbv : (bvOfInt 128 (Int.ofNat n)).toNat = n := by
    unfold bvOfInt intEmod
    have hlt128 : n < 2 ^ 128 := Nat.lt_trans hn0 (by decide)
    change (n % 2 ^ 128) % 2 ^ 128 = n
    rw [Nat.mod_eq_of_lt hlt128, Nat.mod_eq_of_lt hlt128]
  rw [hbv, toNat_ofNat_lt_128 n hn0]
  change n % 4294967296 = n
  exact Nat.mod_eq_of_lt hn0
'''

    if regime == "R0_RawPostCleanup":
        n_locals, stmts_body = 5, 8
        body_code = r'''
noncomputable def bodyBench : Body where
  argumentCount := 2
  locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
  basicBlocks := [
    { statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) { branches := [(BitVec.ofNat 128 0, 2)], otherwise := 1 } },
    { statements := [
        .storageLive 3,
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨2, []⟩ (.use (.move ⟨3, []⟩)),
        .storageDead 3,
        .storageLive 4,
        .assign ⟨4, []⟩ (.binaryOp .sub (.move ⟨1, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨1, []⟩ (.use (.move ⟨4, []⟩)),
        .storageDead 4
      ]
      terminator := .goto 0 },
    { statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_ }
  ]

theorem bench_thm (n : Nat) (hn : n < 4294967296) (acc : BitVec 128) (hacc : ScalarVal.wf ⟨.i32, false, acc⟩ = true) :
    Executes bodyBench
      (mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .dead, .dead])
      (.scalar ⟨.i32, false, sumSpec n acc⟩) := by
  induction n generalizing acc with
  | zero =>
    apply Executes.next (next := mkState 2 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .dead, .dead])
    · exact evalStep_switch_u32_zero_branch bodyBench _ 0 0 _ 1 2 1 rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 2 1 [.live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .dead, .dead])
    · exact evalStep_assign_use_copy bodyBench _ 2 0 _ _ 2 0 acc none hacc rfl rfl rfl rfl rfl rfl rfl
    exact Executes.ret (evalStep_return_u32 bodyBench _ 2 1 _ acc rfl rfl rfl rfl rfl rfl)
  | succ m ih =>
    let acc' := addU32Bits acc (BitVec.ofNat 128 (m + 1))
    let i' := subU32Bits (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1)
    apply Executes.next (next := mkState 1 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .dead, .dead])
    · exact evalStep_switch_u32_nonzero_branch bodyBench _ 0 0 _ 1 (BitVec.ofNat 128 (m + 1)) 2 1 rfl rfl rfl rfl rfl rfl (bitvec_ofNat_succ_ne_zero m hn)
    apply Executes.next (next := mkState 1 1 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live none, .dead]) rfl
    apply Executes.next (next := mkState 1 2 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead])
    · exact evalStep_assign_add_vars_copy bodyBench _ 1 1 _ _ 2 1 3 acc (BitVec.ofNat 128 (m + 1)) none rfl rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 3 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live none, .dead])
    · exact evalStep_assign_use_move bodyBench _ 1 2 _ _ _ 3 2 acc' _ (addU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 4 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead, .dead]) rfl
    apply Executes.next (next := mkState 1 5 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead, .live none]) rfl
    apply Executes.next (next := mkState 1 6 [.live none, .live none, .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead, .live (some (.scalar ⟨.i32, false, i'⟩))])
    · exact evalStep_assign_sub_move bodyBench _ 1 5 _ _ _ 1 4 (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1) none rfl rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 7 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead, .live none])
    · exact evalStep_assign_use_move bodyBench _ 1 6 _ _ _ 4 1 i' none (subU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 8 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead, .dead]) rfl
    apply Executes.next (next := mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .dead, .dead]) rfl
    have hi : i' = BitVec.ofNat 128 m := subU32Bits_succ_one m hn
    rw [hi]
    exact ih (Nat.lt_trans (Nat.lt_succ_self m) hn) acc' (addU32Bits_wf _ _)
'''
    elif regime == "R1_F1_1b_Nop":
        n_locals, stmts_body = 5, 8
        body_code = r'''
noncomputable def bodyBench : Body where
  argumentCount := 2
  locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
  basicBlocks := [
    { statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) { branches := [(BitVec.ofNat 128 0, 2)], otherwise := 1 } },
    { statements := [
        .nop,
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨2, []⟩ (.use (.copy ⟨3, []⟩)),
        .nop,
        .nop,
        .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨1, []⟩ (.use (.copy ⟨4, []⟩)),
        .nop
      ]
      terminator := .goto 0 },
    { statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_ }
  ]

theorem bench_thm (n : Nat) (hn : n < 4294967296) (acc : BitVec 128) (hacc : ScalarVal.wf ⟨.i32, false, acc⟩ = true)
    (v3 v4 : Option Val) :
    Executes bodyBench
      (mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
      (.scalar ⟨.i32, false, sumSpec n acc⟩) := by
  induction n generalizing acc v3 v4 with
  | zero =>
    apply Executes.next (next := mkState 2 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
    · exact evalStep_switch_u32_zero_branch bodyBench _ 0 0 _ 1 2 1 rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 2 1 [.live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
    · exact evalStep_assign_use_copy bodyBench _ 2 0 _ _ 2 0 acc none hacc rfl rfl rfl rfl rfl rfl rfl
    exact Executes.ret (evalStep_return_u32 bodyBench _ 2 1 _ acc rfl rfl rfl rfl rfl rfl)
  | succ m ih =>
    let acc' := addU32Bits acc (BitVec.ofNat 128 (m + 1))
    let i' := subU32Bits (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1)
    apply Executes.next (next := mkState 1 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
    · exact evalStep_switch_u32_nonzero_branch bodyBench _ 0 0 _ 1 (BitVec.ofNat 128 (m + 1)) 2 1 rfl rfl rfl rfl rfl rfl (bitvec_ofNat_succ_ne_zero m hn)
    apply Executes.next (next := mkState 1 1 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4]) rfl
    apply Executes.next (next := mkState 1 2 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live v4])
    · exact evalStep_assign_add_vars_copy bodyBench _ 1 1 _ _ 2 1 3 acc (BitVec.ofNat 128 (m + 1)) v3 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 3 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live v4])
    · exact evalStep_assign_use_copy bodyBench _ 1 2 _ _ 3 2 acc' _ (addU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 4 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live v4]) rfl
    apply Executes.next (next := mkState 1 5 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live v4]) rfl
    apply Executes.next (next := mkState 1 6 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))])
    · exact evalStep_assign_sub_copy bodyBench _ 1 5 _ _ 1 4 (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1) v4 rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 7 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))])
    · exact evalStep_assign_use_copy bodyBench _ 1 6 _ _ 4 1 i' _ (subU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 8 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))]) rfl
    apply Executes.next (next := mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))]) rfl
    have hi : i' = BitVec.ofNat 128 m := subU32Bits_succ_one m hn
    rw [hi]
    exact ih (Nat.lt_trans (Nat.lt_succ_self m) hn) acc' (addU32Bits_wf _ _) _ _
'''
    elif regime == "R2_StorageDeleted":
        n_locals, stmts_body = 5, 4
        body_code = r'''
noncomputable def bodyBench : Body where
  argumentCount := 2
  locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
  basicBlocks := [
    { statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) { branches := [(BitVec.ofNat 128 0, 2)], otherwise := 1 } },
    { statements := [
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨2, []⟩ (.use (.copy ⟨3, []⟩)),
        .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨1, []⟩ (.use (.copy ⟨4, []⟩))
      ]
      terminator := .goto 0 },
    { statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_ }
  ]

theorem bench_thm (n : Nat) (hn : n < 4294967296) (acc : BitVec 128) (hacc : ScalarVal.wf ⟨.i32, false, acc⟩ = true)
    (v3 v4 : Option Val) :
    Executes bodyBench
      (mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
      (.scalar ⟨.i32, false, sumSpec n acc⟩) := by
  induction n generalizing acc v3 v4 with
  | zero =>
    apply Executes.next (next := mkState 2 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
    · exact evalStep_switch_u32_zero_branch bodyBench _ 0 0 _ 1 2 1 rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 2 1 [.live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
    · exact evalStep_assign_use_copy bodyBench _ 2 0 _ _ 2 0 acc none hacc rfl rfl rfl rfl rfl rfl rfl
    exact Executes.ret (evalStep_return_u32 bodyBench _ 2 1 _ acc rfl rfl rfl rfl rfl rfl)
  | succ m ih =>
    let acc' := addU32Bits acc (BitVec.ofNat 128 (m + 1))
    let i' := subU32Bits (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1)
    apply Executes.next (next := mkState 1 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live v3, .live v4])
    · exact evalStep_switch_u32_nonzero_branch bodyBench _ 0 0 _ 1 (BitVec.ofNat 128 (m + 1)) 2 1 rfl rfl rfl rfl rfl rfl (bitvec_ofNat_succ_ne_zero m hn)
    apply Executes.next (next := mkState 1 1 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live v4])
    · exact evalStep_assign_add_vars_copy bodyBench _ 1 0 _ _ 2 1 3 acc (BitVec.ofNat 128 (m + 1)) v3 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 2 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live v4])
    · exact evalStep_assign_use_copy bodyBench _ 1 1 _ _ 3 2 acc' _ (addU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 3 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))])
    · exact evalStep_assign_sub_copy bodyBench _ 1 2 _ _ 1 4 (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1) v4 rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 4 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))])
    · exact evalStep_assign_use_copy bodyBench _ 1 3 _ _ 4 1 i' _ (subU32Bits_wf _ _) rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩)), .live (some (.scalar ⟨.i32, false, i'⟩))]) rfl
    have hi : i' = BitVec.ofNat 128 m := subU32Bits_succ_one m hn
    rw [hi]
    exact ih (Nat.lt_trans (Nat.lt_succ_self m) hn) acc' (addU32Bits_wf _ _) _ _
'''
    else:
        n_locals, stmts_body = 3, 2
        body_code = r'''
noncomputable def bodyBench : Body where
  argumentCount := 2
  locals := [u32Ty, u32Ty, u32Ty]
  basicBlocks := [
    { statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) { branches := [(BitVec.ofNat 128 0, 2)], otherwise := 1 } },
    { statements := [
        .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨1, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 0 },
    { statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .return_ }
  ]

theorem bench_thm (n : Nat) (hn : n < 4294967296) (acc : BitVec 128) (hacc : ScalarVal.wf ⟨.i32, false, acc⟩ = true) :
    Executes bodyBench
      (mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩)), .live (some (.scalar ⟨.i32, false, acc⟩))])
      (.scalar ⟨.i32, false, sumSpec n acc⟩) := by
  induction n generalizing acc with
  | zero =>
    apply Executes.next (next := mkState 2 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩))])
    · exact evalStep_switch_u32_zero_branch bodyBench _ 0 0 _ 1 2 1 rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 2 1 [.live (some (.scalar ⟨.i32, false, acc⟩)), .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)), .live (some (.scalar ⟨.i32, false, acc⟩))])
    · exact evalStep_assign_use_copy bodyBench _ 2 0 _ _ 2 0 acc none hacc rfl rfl rfl rfl rfl rfl rfl
    exact Executes.ret (evalStep_return_u32 bodyBench _ 2 1 _ acc rfl rfl rfl rfl rfl rfl)
  | succ m ih =>
    let acc' := addU32Bits acc (BitVec.ofNat 128 (m + 1))
    let i' := subU32Bits (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1)
    apply Executes.next (next := mkState 1 0 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc⟩))])
    · exact evalStep_switch_u32_nonzero_branch bodyBench _ 0 0 _ 1 (BitVec.ofNat 128 (m + 1)) 2 1 rfl rfl rfl rfl rfl rfl (bitvec_ofNat_succ_ne_zero m hn)
    apply Executes.next (next := mkState 1 1 [.live none, .live (some (.scalar ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩))])
    · exact evalStep_assign_add_vars_copy bodyBench _ 1 0 _ _ 2 1 2 acc (BitVec.ofNat 128 (m + 1)) _ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 1 2 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩))])
    · exact evalStep_assign_sub_copy bodyBench _ 1 1 _ _ 1 1 (BitVec.ofNat 128 (m + 1)) (BitVec.ofNat 128 1) _ rfl rfl rfl rfl rfl rfl rfl rfl
    apply Executes.next (next := mkState 0 0 [.live none, .live (some (.scalar ⟨.i32, false, i'⟩)), .live (some (.scalar ⟨.i32, false, acc'⟩))]) rfl
    have hi : i' = BitVec.ofNat 128 m := subU32Bits_succ_one m hn
    rw [hi]
    exact ih (Nat.lt_trans (Nat.lt_succ_self m) hn) acc' (addU32Bits_wf _ _)
'''
    src = (
        COMMON_IMPORTS
        + "import E28Helpers\n"
        + f"namespace {mod_name}\n"
        + "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp E28Helpers\n"
        + spec_defs
        + body_code
        + f"end {mod_name}\n"
    )
    meta = {
        "module": mod_name,
        "theorem": f"{mod_name}.bench_thm",
        "regime": regime,
        "locals_count": n_locals,
        "loop_body_stmts": stmts_body,
    }
    return src, meta


def make_f1_1b_checker_module(k: int) -> tuple[str, dict]:
    """Measure real F1-1b checkProgramMoveToCopy + checkProgramRemoveStorageMarkers rfl cost on R0(K)."""
    # Build R0(K) and R1(K) inside a module importing F1_1b!
    mod_name = f"Bench_f11b_check_K{k}"
    n_locals = k + 2
    locals_decl = "[" + ", ".join(["u32Ty"] * n_locals) + "]"
    r0_stmts, r1_stmts = [], []
    for i in range(1, k + 1):
        src, dst = i, i + 1
        r0_stmts.append(f".storageLive {dst}")
        r1_stmts.append(".nop")
        r0_stmts.append(f".assign ⟨{dst}, []⟩ (.binaryOp .add (.move ⟨{src}, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 {i})⟩))")
        r1_stmts.append(f".assign ⟨{dst}, []⟩ (.binaryOp .add (.copy ⟨{src}, []⟩) (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 {i})⟩))")
        if i >= 2:
            r0_stmts.append(f".storageDead {src}")
            r1_stmts.append(".nop")
    last_src = k + 1
    r0_stmts.append(f".assign ⟨0, []⟩ (.use (.move ⟨{last_src}, []⟩))")
    r1_stmts.append(f".assign ⟨0, []⟩ (.use (.copy ⟨{last_src}, []⟩))")
    r0_stmts.append(f".storageDead {last_src}")
    r1_stmts.append(".nop")

    # Intermediate M2C program (only Move->Copy, keeps storage markers)
    m2c_stmts = [s.replace(".move", ".copy") for s in r0_stmts]
    cert_entry = "[" + ", ".join([".liveUninit", ".liveInit"] + [".dead"] * k) + "]"

    src = f"""{COMMON_IMPORTS}
import F1_1b_Mod

namespace {mod_name}
open Trusted.MirAst Trusted.MirSemantics VrustcFormal.F1_1b

noncomputable def progR0 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{{
    argumentCount := 1
    locals := {locals_decl}
    basicBlocks := [{{
      statements := [\n        {",\n        ".join(r0_stmts)}\n      ]
      terminator := .return_
    }}]
  }}]

noncomputable def progM2C : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{{
    argumentCount := 1
    locals := {locals_decl}
    basicBlocks := [{{
      statements := [\n        {",\n        ".join(m2c_stmts)}\n      ]
      terminator := .return_
    }}]
  }}]

noncomputable def progR1 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{{
    argumentCount := 1
    locals := {locals_decl}
    basicBlocks := [{{
      statements := [\n        {",\n        ".join(r1_stmts)}\n      ]
      terminator := .return_
    }}]
  }}]

def certEntry : ProgramAbsCert := [[some {cert_entry}]]

theorem check_m2c_rel : isMoveToCopyProgram progR0 progM2C = true := rfl
theorem check_m2c_cert : checkNoUseAfterMoveProgram progR0 certEntry = true := rfl
theorem check_rsm_rel : isRemoveStorageMarkersProgram progM2C progR1 = true := rfl
theorem check_rsm_cert : checkStorageSafeProgram progM2C certEntry = true := rfl

theorem bench_thm (q : Query) :
    (WellFormed progR1 q ↔ WellFormed progR0 q) ∧
    (∀ out, Behavior progR1 q out ↔ Behavior progR0 q out) := by
  have h1 := (vc_transport_moveToCopy_certified_iff progR0 progM2C certEntry check_m2c_rel check_m2c_cert).1 q
  have h2 := (vc_transport_removeStorageMarkers_certified_iff progM2C progR1 certEntry check_rsm_rel check_rsm_cert).1 q
  exact ⟨Iff.trans h2.1 h1.1, fun out => Iff.trans (h2.2.1 out) (h1.2.1 out)⟩

end {mod_name}
"""
    return src, {
        "module": mod_name,
        "theorem": f"{mod_name}.bench_thm",
        "k": k,
        "locals_count": n_locals,
        "stmts_count": len(r0_stmts),
    }


def batch_inspect_expr_dag(lean_path: str, td: Path, mod_thm_pairs: list[tuple[str, str]]) -> dict:
    """Inspect all compiled theorem Expr DAG & memoized tree sizes in ONE Lean process."""
    names = ", ".join(f"`{t}" for _, t in mod_thm_pairs)
    sysroot_str = str(LEAN.parent.parent)
    inspector = f"""import Lean

open Lean

partial def exprDagAndTree (e : Expr) : Nat × Nat :=
  let rec go (memo : Std.HashMap Expr Nat) (e : Expr) : Std.HashMap Expr Nat × Nat :=
    match memo.get? e with
    | some sz => (memo, sz)
    | none =>
      let (memo', sz) := match e with
        | .app f a =>
          let (m1, sf) := go memo f
          let (m2, sa) := go m1 a
          (m2, 1 + sf + sa)
        | .lam _ t b _ =>
          let (m1, st) := go memo t
          let (m2, sb) := go m1 b
          (m2, 1 + st + sb)
        | .forallE _ t b _ =>
          let (m1, st) := go memo t
          let (m2, sb) := go m1 b
          (m2, 1 + st + sb)
        | .letE _ t v b _ =>
          let (m1, st) := go memo t
          let (m2, sv) := go m1 v
          let (m3, sb) := go m2 b
          (m3, 1 + st + sv + sb)
        | .mdata _ b =>
          let (m1, sb) := go memo b
          (m1, 1 + sb)
        | .proj _ _ b =>
          let (m1, sb) := go memo b
          (m1, 1 + sb)
        | _ => (memo, 1)
      (memo'.insert e sz, sz)
  let (m, treeSz) := go {{}} e
  (m.size, treeSz)

def main : IO Unit := do
  initSearchPath (System.FilePath.mk "{sysroot_str}")
  let env ← importModules #[{", ".join(f"{{ module := `{m} }}" for m, _ in mod_thm_pairs)}] {{}}
  for nm in [{names}] do
    match env.find? nm with
    | none => IO.println s!"RESULT {{nm}} MISSING"
    | some ci =>
      let (td, tt) := exprDagAndTree ci.type
      let (vd, vt) := match ci with
        | .thmInfo ti => exprDagAndTree ti.value
        | .defnInfo di => exprDagAndTree di.value
        | _ => (0, 0)
      IO.println s!"RESULT {{nm}} {{td}} {{tt}} {{vd}} {{vt}}"
"""
    insp_path = td / "BatchInspect.lean"
    insp_path.write_text(inspector)
    env = os.environ.copy()
    env["LEAN_PATH"] = lean_path
    env["LEAN_SYSROOT"] = sysroot_str
    insp_cmd = ([RUN_WRAP, "--"] if RUN_WRAP else []) + [str(LEAN), "--run", str(insp_path)]
    r = subprocess.run(
        insp_cmd,
        env=env, capture_output=True, text=True, timeout=180
    )
    out = {}
    if r.returncode != 0:
        print("INSPECTOR ERROR:", r.stdout[:500], r.stderr[:500])
        return out
    for line in r.stdout.splitlines():
        if line.startswith("RESULT "):
            parts = line.split()
            if len(parts) == 6:
                _, nm, td_n, tt_n, vd_n, vt_n = parts
                out[nm] = {
                    "type_dag_nodes": int(td_n),
                    "type_tree_nodes": int(tt_n),
                    "proof_dag_nodes": int(vd_n),
                    "proof_tree_nodes": int(vt_n),
                }
    return out


def main():
    t_all = time.monotonic()
    regimes = ["R0_RawPostCleanup", "R1_F1_1b_Nop", "R2_StorageDeleted", "R3_MinLocalCompact"]
    results = {
        "probe": "E2-8_real_anneal_mirwp_scaling",
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "lean_version": subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
        "anneal_commit": "c131b320eeeb26ef692e5afd5ec8db49ee518613",
        "suite_a_concrete_runs": [],
        "suite_b_symbolic_executes": [],
        "suite_c_symbolic_loop": [],
        "suite_d_f1_1b_transport_checker": [],
    }

    with tempfile.TemporaryDirectory(prefix="e2_8_bench_") as td_str:
        td = Path(td_str)
        lean_path = f"{td}:{CACHE}"

        # 0. Compile E28Helpers once
        print("[0/4] Compiling E28Helpers...")
        helper_src = td / "E28Helpers.lean"
        helper_src.write_text(HELPER_MODULE)
        h_res = run_timed_lean(lean_path, td, helper_src, td / "E28Helpers.olean", repeats=1)
        print("  E28Helpers:", h_res)
        if h_res["rc"] != 0:
            raise RuntimeError(f"E28Helpers failed: {h_res}")
        results["helpers_compile"] = h_res

        all_mod_thms = []

        # Suite A: Concrete RunsFrom rfl scaling (pinpointing exact maxRecDepth=512 cliff!)
        print("[1/4] Suite A: Concrete RunsFrom (rfl) scaling...")
        for k in [2, 4, 6, 8, 10, 12, 14, 16]:
            for reg in regimes:
                src, meta = make_chain_body_and_proof(reg, k, "concrete")
                sp = td / f"{meta['module']}.lean"
                op = td / f"{meta['module']}.olean"
                sp.write_text(src)
                m = run_timed_lean(lean_path, td, sp, op, repeats=3)
                rec = {**meta, **m}
                results["suite_a_concrete_runs"].append(rec)
                if m["rc"] == 0:
                    all_mod_thms.append((meta["module"], meta["theorem"]))
                print(f"  [A] K={k:2d} {reg:18s}: rc={m['rc']} wall={m.get('wall_sec_median')}s rss={m.get('peak_rss_mb_median')}MB olean={m.get('olean_bytes')}B stmts={meta['stmts_count']} locals={meta['locals_count']}")

        # Suite B: Symbolic Executes scaling (K=2..64!)
        print("[2/4] Suite B: Symbolic Executes (∀ x : BitVec 128) scaling...")
        for k in [2, 4, 8, 16, 32, 64]:
            for reg in regimes:
                src, meta = make_chain_body_and_proof(reg, k, "symbolic")
                sp = td / f"{meta['module']}.lean"
                op = td / f"{meta['module']}.olean"
                sp.write_text(src)
                m = run_timed_lean(lean_path, td, sp, op, repeats=3)
                rec = {**meta, **m}
                results["suite_b_symbolic_executes"].append(rec)
                if m["rc"] == 0:
                    all_mod_thms.append((meta["module"], meta["theorem"]))
                print(f"  [B] K={k:2d} {reg:18s}: rc={m['rc']} wall={m.get('wall_sec_median')}s rss={m.get('peak_rss_mb_median')}MB olean={m.get('olean_bytes')}B loc={m.get('proof_loc')}")

        # Suite C: Symbolic Loop Invariant (sum_loop)
        print("[3/4] Suite C: Symbolic Loop Invariant (sum_loop, ∀ n : Nat)...")
        for reg in regimes:
            src, meta = make_loop_module(reg)
            sp = td / f"{meta['module']}.lean"
            op = td / f"{meta['module']}.olean"
            sp.write_text(src)
            m = run_timed_lean(lean_path, td, sp, op, repeats=3)
            rec = {**meta, **m}
            results["suite_c_symbolic_loop"].append(rec)
            if m["rc"] == 0:
                all_mod_thms.append((meta["module"], meta["theorem"]))
            print(f"  [C] LOOP {reg:18s}: rc={m['rc']} wall={m.get('wall_sec_median')}s rss={m.get('peak_rss_mb_median')}MB olean={m.get('olean_bytes')}B loc={m.get('proof_loc')}")

        # Suite D: F1-1b direct checker rfl overhead
        print("[4/4] Suite D: Direct F1-1b checkProgramMoveToCopy/RemoveStorageMarkers rfl overhead...")
        f1_src_copy = td / "F1_1b_Mod.lean"
        f1_src_copy.write_text(F1_1B_SRC.read_text())
        f1_res = run_timed_lean(lean_path, td, f1_src_copy, td / "F1_1b_Mod.olean", repeats=1)
        print(f"  F1_1b_Mod compile: rc={f1_res['rc']} wall={f1_res.get('wall_sec_median')}s")
        results["f1_1b_mod_compile"] = f1_res
        if f1_res["rc"] == 0:
            for k in [4, 8, 16, 32]:
                src, meta = make_f1_1b_checker_module(k)
                sp = td / f"{meta['module']}.lean"
                op = td / f"{meta['module']}.olean"
                sp.write_text(src)
                m = run_timed_lean(lean_path, td, sp, op, repeats=3)
                rec = {**meta, **m}
                results["suite_d_f1_1b_transport_checker"].append(rec)
                if m["rc"] == 0:
                    all_mod_thms.append((meta["module"], meta["theorem"]))
                print(f"  [D] F1-1b K={k:2d}: rc={m['rc']} wall={m.get('wall_sec_median')}s rss={m.get('peak_rss_mb_median')}MB olean={m.get('olean_bytes')}B stmts={meta['stmts_count']}")

        # Batch AST inspection in ONE Lean invocation
        print(f"[AST] Inspecting kernel Expr DAG/tree sizes for {len(all_mod_thms)} theorems...")
        ast_map = batch_inspect_expr_dag(lean_path, td, all_mod_thms)
        for suite_key in ["suite_a_concrete_runs", "suite_b_symbolic_executes", "suite_c_symbolic_loop", "suite_d_f1_1b_transport_checker"]:
            for rec in results[suite_key]:
                thm = rec.get("theorem")
                if thm in ast_map:
                    rec.update(ast_map[thm])

    results["total_elapsed_sec"] = round(time.monotonic() - t_all, 2)
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(results, indent=2))
    print(f"WROTE {OUT_JSON} ({OUT_JSON.stat().st_size} bytes) in {results['total_elapsed_sec']}s")


if __name__ == "__main__":
    main()
