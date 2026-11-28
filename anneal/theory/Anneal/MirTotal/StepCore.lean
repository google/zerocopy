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
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops

public section

namespace Anneal.MirTotal

open Trusted.MirAst Trusted.MirSemantics

/-!
# Parametric Computable MIR Step Core (`MirTotal.StepCore`)

Defines a single `(tyEq : MirTy → MirTy → Bool)`-parameterized, LCNF-computable
(`0` `noncomputable`, `0` `._unsafe_rec`) single-frame MIR evaluator and static
entry-admission checker, together with parametric equational equivalence
theorems (`*_eq`) against `Trusted.MirSemantics` and `Anneal.MirWp` adequacy
lifts whenever `∀ a b, tyEq a b = MirTy.beq a b`.

Specializing `tyEq` to `mirTyBeqAt fuel` yields an executable depth-bounded
evaluator (`evalMirStepAt`), while specializing `tyEq` to `MirTy.beq`
in `MirTotal.ExecTotal` yields a premise-free, unbounded-depth mirror of
`Trusted.MirSemantics.evalStep` without duplicating step logic.
-/

/-! ## Depth-Bounded Computable `MirTy` Equality -/

/-- Depth-bounded LCNF-computable structural equality on `MirTy` (`0`
`noncomputable`), returning `false` once `.tuple`, `.ref`, or `.rawPtr` nesting
exceeds `fuel`. -/
@[expose] def mirTyBeqAt (fuel : Nat) : MirTy → MirTy → Bool :=
  @Nat.rec (fun _ => MirTy → MirTy → Bool)
    (fun _ _ => false)
    (fun _ ih a b =>
      match a with
      | .bool =>
        match b with
        | .bool => true
        | .int _ _ | .unit | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .int w1 s1 =>
        match b with
        | .int w2 s2 => intWidthBeqComp w1 w2 && boolBeqComp s1 s2
        | .bool | .unit | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .unit =>
        match b with
        | .unit => true
        | .bool | .int _ _ | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .never =>
        match b with
        | .never => true
        | .bool | .int _ _ | .unit | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .char =>
        match b with
        | .char => true
        | .bool | .int _ _ | .unit | .never | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .ordering =>
        match b with
        | .ordering => true
        | .bool | .int _ _ | .unit | .never | .char | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .enum e1 =>
        match b with
        | .enum e2 => enumTyBeqComp e1 e2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .tuple fs1 =>
        match b with
        | .tuple fs2 =>
          List.foldr
            (fun (x : MirTy) (lih : List MirTy → Bool) (ys : List MirTy) =>
              match ys with
              | [] => false
              | y :: tl => ih x y && lih tl)
            (fun ys => match ys with | [] => true | _ :: _ => false)
            fs1 fs2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .ref m1 p1 =>
        match b with
        | .ref m2 p2 => mutabilityBeqComp m1 m2 && ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .rawPtr m1 p1 =>
        match b with
        | .rawPtr m2 p2 => mutabilityBeqComp m1 m2 && ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .slice _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .slice p1 =>
        match b with
        | .slice p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .str | .array _ _ | .vec _ | .box _
        | .rangeTo _
        | .rangeFrom _ | .unsupported | .option _ | .range _
        | .struct_ _ _ => false
      | .str =>
        match b with
        | .str => true
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
        | .vec _ | .box _
        | .rangeFrom _ | .unsupported | .option _ | .range _
        | .struct_ _ _ => false
      | .vec p1 =>
        match b with
        | .vec p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .box _
        | .rangeTo _ | .rangeFrom _ | .unsupported | .array _ _ | .option _ | .range _
        | .struct_ _ _ => false
      | .box p1 =>
        match b with
        | .box p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .vec _
        | .rangeTo _ | .rangeFrom _ | .unsupported | .option _ | .range _ | .array _ _
        | .struct_ _ _ => false
      | .array p1 n1 =>
        match b with
        | .array p2 n2 => Nat.beq n1 n2 && ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .rangeTo _
        | .rangeFrom _ | .range _ | .option _ | .unsupported | .box _ | .vec _
        | .struct_ _ _ => false
      | .rangeTo p1 =>
        match b with
        | .rangeTo p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .vec _
        | .box _ | .rangeFrom _ | .range _ | .option _ | .unsupported
        | .struct_ _ _ => false
      | .rangeFrom p1 =>
        match b with
        | .rangeFrom p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _ | .rangeTo _
        | .range _ | .option _ | .unsupported | .box _ | .vec _ | .struct_ _ _ => false
      | .range p1 =>
        match b with
        | .range p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .vec _ | .box _
        | .rangeTo _
        | .rangeFrom _ | .option _ | .unsupported | .array _ _ | .struct_ _ _ => false
      | .option p1 =>
        match b with
        | .option p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .rangeTo _
        | .rangeFrom _ | .range _ | .unsupported | .array _ _ | .box _ | .vec _ | .struct_ _ _ => false
      | .struct_ l1 fs1 =>
        match b with
        | .struct_ l2 fs2 =>
          structLayoutBeqComp l1 l2 &&
            List.foldr
              (fun (x : MirTy) (lih : List MirTy → Bool) (ys : List MirTy) =>
                match ys with
                | [] => false
                | y :: tl => ih x y && lih tl)
              (fun ys => match ys with | [] => true | _ :: _ => false)
              fs1 fs2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .array _ _
        | .rangeTo _ | .rangeFrom _
        | .range _ | .option _ | .box _ | .vec _ | .unsupported => false
      | .unsupported =>
        match b with
        | .unsupported => true
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .str | .vec _ | .box _
        | .array _ _ | .rangeTo _ | .rangeFrom _ | .range _ | .option _
        | .struct_ _ _ => false)
    fuel

/-! ## `tyEq`-Parameterized Value Encoding and Indirect Stores -/

/-- Computable mirror of `Trusted.MirSemantics.checkVal` parameterized by
`tyEq`. -/
@[expose] def checkValBy (tyEq : MirTy → MirTy → Bool) (v : Val) (ty : MirTy) : Bool :=
  match valTy?Comp v with
  | some vTy => tyEq vTy ty
  | none => false

/-- Agreement between `checkValBy` and `checkVal` when `tyEq` agrees with
`MirTy.beq`. -/
theorem checkValBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (v : Val) (ty : MirTy) :
    checkValBy tyEq v ty = checkVal v ty := by
  unfold checkValBy checkVal
  rw [valTy?Comp_eq]
  cases v.ty? with
  | none => rfl
  | some vTy => exact hTyEq vTy ty

/-- Computable mirror of `Trusted.MirSemantics.encodeVal` parameterized by
`tyEq`. -/
@[expose] def encodeValBy (tyEq : MirTy → MirTy → Bool) (endian : TargetEndian)
    (ty : MirTy) (v : Val) : Except FaultKind (List AllocByte) :=
  if !checkValBy tyEq v ty then .error .unsupported
  else
    match ty, v with
    | .int w _, .scalar sv =>
      .ok ((encodeUIntComp endian (byteSizeComp w) sv.bits.toNat).map
        (fun b => AllocByte.init b none))
    | .bool, .bool b =>
      .ok [AllocByte.init (if b then 1 else 0) none]
    | .char, .char c =>
      .ok ((encodeUIntComp endian 4 c.toNat).map (fun b => AllocByte.init b none))
    | .ordering, .ordering ord =>
      .ok ((encodeUIntComp endian 1 (orderingTagBitsComp ord)).map
        (fun b => AllocByte.init b none))
    | .unit, .unit => .ok []
    | .enum ety, .enumVal _ variant =>
      match ety.tagRepr with
      | .zeroSized => .ok []
      | .scalar tagW _ =>
        match compGetElem? ety.discriminants variant with
        | some disc =>
          .ok ((encodeUIntComp endian (byteSizeComp tagW) disc).map
            (fun b => AllocByte.init b none))
        | none => .error .unsupported
    | .tuple [.int w _, .bool], .tuple [.scalar sv, .bool b] =>
      .ok ((encodeUIntComp endian (byteSizeComp w) sv.bits.toNat).map
          (fun byte => AllocByte.init byte none) ++
        [AllocByte.init (if b then 1 else 0) none] ++
        List.replicate (byteSizeComp w - 1) AllocByte.uninit)
    | _, _ => .error .unsupported

/-- Agreement between `encodeValBy` and `encodeVal` when `tyEq` agrees with
`MirTy.beq`. -/
theorem encodeValBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (endian : TargetEndian) (ty : MirTy) (v : Val) :
    encodeValBy tyEq endian ty v = encodeVal endian ty v := by
  dsimp only [encodeValBy, encodeVal, orderingTagBitsComp, orderingTagBits]
  rw [checkValBy_eq tyEq hTyEq]
  cases checkVal v ty with
  | false => rfl
  | true =>
    cases ty with
    | int w _ =>
      cases v with
      | scalar _ => dsimp only; rw [byteSizeComp_eq, encodeUIntComp_eq]
      | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
    | char =>
      cases v with
      | char _ => dsimp only; rw [encodeUIntComp_eq]
      | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
      | optionVal _ | bool _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
    | ordering =>
      cases v with
      | ordering ord => dsimp only; rw [encodeUIntComp_eq]; cases ord <;> rfl
      | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
      | optionVal _ | bool _ | char _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
    | enum ety =>
      cases v with
      | enumVal _ variant =>
        dsimp only
        cases ety.tagRepr with
        | zeroSized => rfl
        | scalar tagW _ =>
          dsimp only
          rw [compGetElem?_eq, byteSizeComp_eq]
          cases Trusted.MirSemantics.getElem? ety.discriminants variant with
          | none => rfl
          | some disc => dsimp only; rw [encodeUIntComp_eq]
      | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
      | optionVal _ | bool _ | char _ | ordering _ | unit | tuple _ | array _ | bytes _ => rfl
    | tuple fs =>
      cases fs with
      | nil => rfl
      | cons t1 r1 =>
        cases t1 with
        | int w _ =>
          cases r1 with
          | nil => rfl
          | cons t2 r2 =>
            cases t2 with
            | bool =>
              cases r2 with
              | cons _ _ => rfl
              | nil =>
                cases v with
                | tuple vs =>
                  cases vs with
                  | nil => rfl
                  | cons v1 vr1 =>
                    cases v1 with
                    | scalar _ =>
                      cases vr1 with
                      | nil => rfl
                      | cons v2 vr2 =>
                        cases v2 with
                        | bool _ =>
                          cases vr2 with
                          | nil => dsimp only; rw [byteSizeComp_eq, encodeUIntComp_eq]
                          | cons _ _ => rfl
                        | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _
                        | range _ _ | optionVal _ | char _ | ordering _ | unit
                        | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
                    | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
                    | optionVal _ | bool _ | char _ | ordering _ | unit | enumVal _ _
                    | tuple _ | array _ | bytes _ => rfl
                | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
                | optionVal _ | bool _ | char _ | ordering _ | unit | enumVal _ _
                | array _ | bytes _ => rfl
            | int _ _ | char | ordering | unit | never | enum _ | tuple _
            | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | vec _ | box _
            | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported
            | struct_ _ _ => rfl
        | bool | char | ordering | unit | never | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | slice _ | str | vec _ | box _ | array _ _ | rangeTo _ | rangeFrom _
        | range _ | option _ | unsupported | struct_ _ _ => rfl
    | bool | unit | never | ref _ _ | rawPtr _ _ | slice _ | str | vec _ | box _ | array _ _ | rangeTo _
    | rangeFrom _ | range _ | option _ | unsupported | struct_ _ _ => cases v <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.storeIndirect` parameterized by
`tyEq`. -/
@[expose] def storeIndirectBy (tyEq : MirTy → MirTy → Bool) (mem : MemoryState)
    (ty : MirTy) (place : MemPlace) (v : Val) : Except FaultKind MemoryState :=
  match layoutOfTyComp ty with
  | none => .error .unsupported
  | some layout =>
    match encodeValBy tyEq .big ty v with
    | .error k => .error k
    | .ok bytes => writeBytesComp mem place layout.alignLog2 bytes

/-- Agreement between `storeIndirectBy` and `storeIndirect` when `tyEq` agrees
with `MirTy.beq`. -/
theorem storeIndirectBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (mem : MemoryState) (ty : MirTy) (place : MemPlace) (v : Val) :
    storeIndirectBy tyEq mem ty place v = storeIndirect mem ty place v := by
  unfold storeIndirectBy storeIndirect profileTargetEndian
  rw [layoutOfTyComp_eq]
  cases layoutOfTy ty with
  | none => rfl
  | some layout =>
    dsimp only
    rw [encodeValBy_eq tyEq hTyEq]
    cases encodeVal .big ty v with
    | error _ => rfl
    | ok bytes => exact writeBytesComp_eq mem place layout.alignLog2 bytes

/-! ## Operands, Rvalues, Statements, Terminators, and Step Core -/

/-- Computable mirror of `Trusted.MirSemantics.evalOperandToSlot`. -/
@[expose] def evalOperandToSlotComp (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (tyOk : MirTy → Bool) (opnd : Operand) :
    Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState) :=
  match opnd with
  | .copy place =>
    match compGetElem? bodyLocals place.localId, compGetElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some ty, some (.immediate optVal) =>
      if !place.projection.isEmpty then .error .unsupported
      else .ok (ty, optVal, locals, mem)
    | some ty, some (.indirect mplace) =>
      if !place.projection.isEmpty then .error .unsupported
      else if !tyOk ty then .error .unsupported
      else
        match loadIndirectComp mem ty mplace with
        | .ok optVal => .ok (ty, optVal, locals, mem)
        | .error k => .error k
    | _, _ => .error .unsupported
  | .move place =>
    match compGetElem? bodyLocals place.localId, compGetElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some ty, some (.immediate optVal) =>
      if !place.projection.isEmpty then .error .unsupported
      else
        match compSetElem? locals place.localId (liveUninitSlotComp ty) with
        | some locals' => .ok (ty, optVal, locals', mem)
        | none => .error .unsupported
    | some ty, some (.indirect mplace) =>
      if !place.projection.isEmpty then .error .unsupported
      else if !tyOk ty then .error .unsupported
      else
        match loadIndirectComp mem ty mplace with
        | .error k => .error k
        | .ok optVal =>
          match deinitIndirectComp mem ty mplace with
          | .ok mem' => .ok (ty, optVal, locals, mem')
          | .error k => .error k
    | _, _ => .error .unsupported
  | .constant c =>
    match evalConstLitComp c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals, mem)
    | .error k => .error k

/-- Agreement between `evalOperandToSlotComp` and `evalOperandToSlot` under
pointwise agreement of `tyOk1` and `tyOk2`. -/
theorem evalOperandToSlotComp_eq (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (tyOk1 tyOk2 : MirTy → Bool) (opnd : Operand)
    (hTyOk : ∀ ty, tyOk1 ty = tyOk2 ty) :
    evalOperandToSlotComp bodyLocals locals mem tyOk1 opnd =
      evalOperandToSlot bodyLocals locals mem tyOk2 opnd := by
  cases opnd with
  | copy place =>
    dsimp only [evalOperandToSlotComp, evalOperandToSlot]
    rw [compGetElem?_eq, compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? bodyLocals place.localId with
    | none => rfl
    | some ty =>
      cases Trusted.MirSemantics.getElem? locals place.localId with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | immediate _ | partialTuple _ => rfl
        | indirect mplace =>
          dsimp only
          rw [hTyOk ty, loadIndirectComp_eq]
          cases loadIndirect mem ty mplace <;> rfl
  | move place =>
    dsimp only [evalOperandToSlotComp, evalOperandToSlot]
    rw [compGetElem?_eq, compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? bodyLocals place.localId with
    | none => rfl
    | some ty =>
      cases Trusted.MirSemantics.getElem? locals place.localId with
      | none => rfl
      | some slot =>
        cases slot with
        | dead | partialTuple _ => rfl
        | immediate _ =>
          dsimp only
          rw [liveUninitSlotComp_eq, compSetElem?_eq]
          cases setElem? locals place.localId (liveUninitSlot ty) <;> rfl
        | indirect mplace =>
          dsimp only
          rw [hTyOk ty, loadIndirectComp_eq, deinitIndirectComp_eq]
          cases loadIndirect mem ty mplace with
          | error _ => rfl
          | ok _ => cases deinitIndirect mem ty mplace <;> rfl
  | constant c =>
    dsimp only [evalOperandToSlotComp, evalOperandToSlot]
    rw [evalConstLitComp_eq]
    cases evalConstLit c.ty c.lit <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.evalPrimitiveOperand`. -/
@[expose] def evalPrimitiveOperandComp (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match evalOperandToSlotComp bodyLocals locals mem isPrimitiveReadableTyComp opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals', mem') =>
    if !isPrimitiveReadableTyComp ty then .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals', mem')
      | none => .error .undefined

/-- Agreement between `evalPrimitiveOperandComp` and `evalPrimitiveOperand`. -/
theorem evalPrimitiveOperandComp_eq (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (opnd : Operand) :
    evalPrimitiveOperandComp bodyLocals locals mem opnd =
      evalPrimitiveOperand bodyLocals locals mem opnd := by
  unfold evalPrimitiveOperandComp evalPrimitiveOperand
  rw [evalOperandToSlotComp_eq bodyLocals locals mem
    isPrimitiveReadableTyComp isPrimitiveReadableTy opnd isPrimitiveReadableTyComp_eq]
  cases evalOperandToSlot bodyLocals locals mem isPrimitiveReadableTy opnd with
  | error _ => rfl
  | ok quad =>
    cases quad with
    | mk ty rest =>
      cases rest with
      | mk optVal _ =>
        dsimp only
        rw [isPrimitiveReadableTyComp_eq]
        cases optVal <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.evalDiscriminantOfVal`. -/
@[expose] def evalDiscriminantOfValComp (ety : EnumTy) (optVal : Option Val)
    (locals : List LocalSlot) (mem : MemoryState) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  if !enumAdmittedComp ety then .error .unsupported
  else
    match ety.tagRepr, optVal with
    | .zeroSized, none =>
      match compGetElem? ety.discriminants 0 with
      | some disc =>
        .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
          truncateBitsComp ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals, mem)
      | none => .error .unsupported
    | .zeroSized, some (.enumVal ety' v) =>
      if enumTyBeqComp ety ety' && Nat.beq v 0 then
        match compGetElem? ety.discriminants 0 with
        | some disc =>
          .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
            truncateBitsComp ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals, mem)
        | none => .error .unsupported
      else .error .unsupported
    | .zeroSized, some _ => .error .unsupported
    | .scalar _ _, none => .error .undefined
    | .scalar _ _, some (.enumVal ety' v) =>
      if enumTyBeqComp ety ety' && Nat.blt v ety.discriminants.length then
        match compGetElem? ety.discriminants v with
        | some disc =>
          .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
            truncateBitsComp ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals, mem)
        | none => .error .unsupported
      else .error .unsupported
    | .scalar _ _, some _ => .error .unsupported

/-- Agreement between `evalDiscriminantOfValComp` and
`evalDiscriminantOfVal`. -/
theorem evalDiscriminantOfValComp_eq (ety : EnumTy) (optVal : Option Val)
    (locals : List LocalSlot) (mem : MemoryState) :
    evalDiscriminantOfValComp ety optVal locals mem =
      evalDiscriminantOfVal ety optVal locals mem := by
  unfold evalDiscriminantOfValComp evalDiscriminantOfVal
  rw [enumAdmittedComp_eq]
  cases ety.tagRepr with
  | zeroSized =>
    cases optVal with
    | none =>
      dsimp only
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;>
        first | rfl | (dsimp only; rw [truncateBitsComp_eq])
    | some v =>
      cases v with
      | enumVal _ _ =>
        dsimp only
        rw [enumTyBeqComp_eq, compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;>
          first | rfl | (dsimp only; rw [truncateBitsComp_eq])
      | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
      | optionVal _ | bool _ | char _ | ordering _ | unit | tuple _ | array _ | bytes _ => rfl
  | scalar _ _ =>
    cases optVal with
    | none => rfl
    | some v =>
      cases v with
      | enumVal _ var =>
        dsimp only
        rw [enumTyBeqComp_eq, compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? ety.discriminants var <;>
          first | rfl | (dsimp only; rw [truncateBitsComp_eq])
      | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
      | optionVal _ | bool _ | char _ | ordering _ | unit | tuple _ | array _ | bytes _ => rfl

/-- Computable mirror of
`Trusted.MirSemantics.evalOrderingDiscriminantOfVal`. -/
@[expose] def evalOrderingDiscriminantOfValComp (optVal : Option Val)
    (locals : List LocalSlot) (mem : MemoryState) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match optVal with
  | none => .error .undefined
  | some (.ordering ord) =>
    .ok (.scalar ⟨.i8, true, BitVec.ofNat 128 (orderingTagBitsComp ord)⟩, locals, mem)
  | some _ => .error .unsupported

/-- Agreement between `evalOrderingDiscriminantOfValComp` and
`evalOrderingDiscriminantOfVal`. -/
theorem evalOrderingDiscriminantOfValComp_eq (optVal : Option Val)
    (locals : List LocalSlot) (mem : MemoryState) :
    evalOrderingDiscriminantOfValComp optVal locals mem =
      evalOrderingDiscriminantOfVal optVal locals mem := by
  cases optVal with
  | none => rfl
  | some v => cases v <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.evalRvalue` parameterized by
`tyEq`. -/
@[expose] def evalRvalueBy (tyEq : MirTy → MirTy → Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (dstTy : MirTy) (rv : Rvalue) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match rv with
  | .use opnd =>
    match evalOperandToSlotComp bodyLocals locals mem
        (fun srcTy => tyEq srcTy dstTy) opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals1, mem1) =>
      if !(tyEq srcTy dstTy) then .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals1, mem1)
        | none => .error .undefined
  | .binaryOp op lhs rhs =>
    match evalPrimitiveOperandComp bodyLocals locals mem lhs with
    | .error k => .error k
    | .ok (lVal, locals1, mem1) =>
      match evalPrimitiveOperandComp bodyLocals locals1 mem1 rhs with
      | .error k => .error k
      | .ok (rVal, locals2, mem2) =>
        match evalBinOpComp op lVal rVal with
        | .error k => .error k
        | .ok res => .ok (res, locals2, mem2)
  | .unaryOp op opnd =>
    match evalPrimitiveOperandComp bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (v, locals1, mem1) =>
      match evalUnOpComp op v with
      | .error k => .error k
      | .ok res => .ok (res, locals1, mem1)
  | .cast .intToInt opnd castTy =>
    match evalOperandToSlotComp bodyLocals locals mem isIntLikeTyComp opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals1, mem1) =>
      if !isIntLikeTyComp srcTy then .error .unsupported
      else
        match optVal with
        | none => .error .undefined
        | some v =>
          match evalIntToIntCastComp v castTy with
          | .error k => .error k
          | .ok res => .ok (res, locals1, mem1)
  | .discriminant place =>
    match compGetElem? bodyLocals place.localId, compGetElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some srcTy, some (.immediate optVal) =>
      if !place.projection.isEmpty then .error .unsupported
      else
        match srcTy with
        | .enum ety => evalDiscriminantOfValComp ety optVal locals mem
        | .ordering => evalOrderingDiscriminantOfValComp optVal locals mem
        | _ => .error .unsupported
    | some srcTy, some (.indirect mplace) =>
      if !place.projection.isEmpty then .error .unsupported
      else
        match srcTy with
        | .enum ety =>
          match loadIndirectComp mem srcTy mplace with
          | .error k => .error k
          | .ok optVal => evalDiscriminantOfValComp ety optVal locals mem
        | .ordering =>
          match loadIndirectComp mem srcTy mplace with
          | .error k => .error k
          | .ok optVal => evalOrderingDiscriminantOfValComp optVal locals mem
        | _ => .error .unsupported
    | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Agreement between `evalRvalueBy` and `evalRvalue` when `tyEq` agrees with
`MirTy.beq`. -/
theorem evalRvalueBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (dstTy : MirTy) (rv : Rvalue) :
    evalRvalueBy tyEq bodyLocals locals mem dstTy rv =
      evalRvalue bodyLocals locals mem dstTy rv := by
  cases rv with
  | use opnd =>
    dsimp only [evalRvalueBy, evalRvalue]
    rw [evalOperandToSlotComp_eq bodyLocals locals mem
      (fun srcTy => tyEq srcTy dstTy) (fun srcTy => MirTy.beq srcTy dstTy)
      opnd (fun srcTy => hTyEq srcTy dstTy)]
    cases evalOperandToSlot bodyLocals locals mem (fun srcTy => MirTy.beq srcTy dstTy) opnd with
    | error _ => rfl
    | ok quad =>
      cases quad with
      | mk srcTy rest =>
        cases rest with
        | mk optVal _ =>
          dsimp only
          rw [hTyEq srcTy dstTy]
          cases optVal <;> rfl
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalueBy, evalRvalue]
    rw [evalPrimitiveOperandComp_eq]
    cases evalPrimitiveOperand bodyLocals locals mem lhs with
    | error _ => rfl
    | ok t1 =>
      cases t1 with
      | mk lVal rest1 =>
        cases rest1 with
        | mk l1 m1 =>
          dsimp only
          rw [evalPrimitiveOperandComp_eq]
          cases evalPrimitiveOperand bodyLocals l1 m1 rhs with
          | error _ => rfl
          | ok t2 =>
            cases t2 with
            | mk rVal _ =>
              dsimp only
              rw [evalBinOpComp_eq]
              cases evalBinOp op lVal rVal <;> rfl
  | unaryOp op opnd =>
    dsimp only [evalRvalueBy, evalRvalue]
    rw [evalPrimitiveOperandComp_eq]
    cases evalPrimitiveOperand bodyLocals locals mem opnd with
    | error _ => rfl
    | ok t1 =>
      cases t1 with
      | mk v _ =>
        dsimp only
        rw [evalUnOpComp_eq]
        cases evalUnOp op v <;> rfl
  | cast ck opnd castTy =>
    cases ck with
    | ptrToPtr | intToPtr | unsize | boxAsRef | unsupported => rfl
    | intToInt =>
      dsimp only [evalRvalueBy, evalRvalue]
      rw [evalOperandToSlotComp_eq bodyLocals locals mem isIntLikeTyComp isIntLikeTy
        opnd isIntLikeTyComp_eq]
      cases evalOperandToSlot bodyLocals locals mem isIntLikeTy opnd with
      | error _ => rfl
      | ok quad =>
        cases quad with
        | mk srcTy rest =>
          cases rest with
          | mk optVal _ =>
            dsimp only
            rw [isIntLikeTyComp_eq]
            cases optVal with
            | none => rfl
            | some v =>
              dsimp only
              rw [evalIntToIntCastComp_eq]
              cases evalIntToIntCast v castTy <;> rfl
  | discriminant place =>
    dsimp only [evalRvalueBy, evalRvalue]
    rw [compGetElem?_eq, compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? bodyLocals place.localId with
    | none => rfl
    | some srcTy =>
      cases Trusted.MirSemantics.getElem? locals place.localId with
      | none => rfl
      | some slot =>
        cases slot with
        | dead | partialTuple _ => rfl
        | immediate optVal =>
          dsimp only
          cases (!place.projection.isEmpty) with
          | true => rfl
          | false =>
            cases srcTy <;>
              first
                | rfl
                | exact evalDiscriminantOfValComp_eq _ _ _ _
                | exact evalOrderingDiscriminantOfValComp_eq _ _ _
        | indirect mplace =>
          dsimp only
          cases (!place.projection.isEmpty) with
          | true => rfl
          | false =>
            cases srcTy with
            | enum ety =>
              dsimp only
              rw [loadIndirectComp_eq]
              cases loadIndirect mem (.enum ety) mplace with
              | error _ => rfl
              | ok optVal => exact evalDiscriminantOfValComp_eq _ _ _ _
            | ordering =>
              dsimp only
              rw [loadIndirectComp_eq]
              cases loadIndirect mem .ordering mplace with
              | error _ => rfl
              | ok optVal => exact evalOrderingDiscriminantOfValComp_eq _ _ _
            | bool | int _ _ | char | unit | never | tuple _ | ref _ _ | rawPtr _ _
            | slice _ | str | array _ _ | vec _ | box _ | rangeTo _ | rangeFrom _
            | range _ | option _ | unsupported | struct_ _ _ => rfl
  | useRetag _ | ref _ _ | addressOf _ _ | fakeAddressOf _ | aggregateTuple _
  | aggregateArray _ _ | repeat_ _ _ _ | aggregateRangeTo _
  | aggregateRangeFrom _ | aggregateRange _ _ _ | aggregateOption _ _ _
  | unsupported | aggregateStruct _ _ => rfl

/-- Computable mirror of `Trusted.MirSemantics.writePlace` parameterized by
`tyEq`. -/
@[expose] def writePlaceBy (tyEq : MirTy → MirTy → Bool) (locals : List LocalSlot)
    (mem : MemoryState) (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot × MemoryState) :=
  if !checkValBy tyEq val dstTy then .error .unsupported
  else
    match compGetElem? locals dstLocalId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.partialTuple _) => .error .unsupported
    | some (.immediate _) =>
      match compSetElem? locals dstLocalId (.immediate (some val)) with
      | some locals' => .ok (locals', mem)
      | none => .error .unsupported
    | some (.indirect mplace) =>
      match storeIndirectBy tyEq mem dstTy mplace val with
      | .ok mem' => .ok (locals, mem')
      | .error k => .error k

/-- Agreement between `writePlaceBy` and `writePlace` when `tyEq` agrees with
`MirTy.beq`. -/
theorem writePlaceBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (locals : List LocalSlot) (mem : MemoryState)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    writePlaceBy tyEq locals mem dstLocalId dstTy val =
      writePlace locals mem dstLocalId dstTy val := by
  dsimp only [writePlaceBy, writePlace]
  rw [checkValBy_eq tyEq hTyEq, compGetElem?_eq]
  cases Trusted.MirSemantics.getElem? locals dstLocalId with
  | none => rfl
  | some slot =>
    cases slot with
    | dead | partialTuple _ => rfl
    | immediate _ =>
      dsimp only
      rw [compSetElem?_eq]
      cases setElem? locals dstLocalId (.immediate (some val)) <;> rfl
    | indirect mplace =>
      dsimp only
      rw [storeIndirectBy_eq tyEq hTyEq]
      cases storeIndirect mem dstTy mplace val <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.evalStatement` parameterized by
`tyEq`. -/
@[expose] def evalStatementBy (tyEq : MirTy → MirTy → Bool) (body : Body)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory)
    (stmt : StatementKind) : StepResult State TerminalOut :=
  match stmt with
  | .nop =>
    .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], callerMem, mem }
  | .storageLive localId =>
    match compGetElem? body.locals localId with
    | none => .fault .unsupported
    | some localTy =>
      match compGetElem? frame.locals localId with
      | none => .fault .unsupported
      | some old =>
        match compSetElem? frame.locals localId (liveUninitSlotComp localTy) with
        | none => .fault .unsupported
        | some locals' =>
          match deallocateLocalComp mem old with
          | .error k => .fault k
          | .ok mem' =>
            .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals' }],
                    callerMem, mem := mem' }
  | .storageDead localId =>
    if Nat.beq localId 0 then .fault .unsupported
    else
      match compGetElem? frame.locals localId with
      | none => .fault .unsupported
      | some old =>
        match compSetElem? frame.locals localId .dead with
        | none => .fault .unsupported
        | some locals' =>
          match deallocateLocalComp mem old with
          | .error k => .fault k
          | .ok mem' =>
            .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals' }],
                    callerMem, mem := mem' }
  | .assign dst rvalue =>
    if !dst.projection.isEmpty then .fault .unsupported
    else
      match compGetElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match evalRvalueBy tyEq body.locals frame.locals mem dstTy rvalue with
        | .error k => .fault k
        | .ok (val, localsAfterRval, memAfterRval) =>
          match writePlaceBy tyEq localsAfterRval memAfterRval dst.localId dstTy val with
          | .error k => .fault k
          | .ok (localsAfterWrite, memAfterWrite) =>
            .step { frames :=
                      [{ frame with stmtIdx := frame.stmtIdx + 1, locals := localsAfterWrite }],
                    callerMem, mem := memAfterWrite }
  | .unsupported => .fault .unsupported

/-- Agreement between `evalStatementBy` and `evalStatement` when `tyEq` agrees
with `MirTy.beq`. -/
theorem evalStatementBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (body : Body) (frame : FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) (stmt : StatementKind) :
    evalStatementBy tyEq body frame mem callerMem stmt =
      evalStatement body frame mem callerMem stmt := by
  cases stmt with
  | nop | unsupported => rfl
  | storageLive localId =>
    dsimp only [evalStatementBy, evalStatement]
    rw [compGetElem?_eq, compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? body.locals localId with
    | none => rfl
    | some localTy =>
      cases Trusted.MirSemantics.getElem? frame.locals localId with
      | none => rfl
      | some old =>
        dsimp only
        rw [liveUninitSlotComp_eq, compSetElem?_eq, deallocateLocalComp_eq]
        cases setElem? frame.locals localId (liveUninitSlot localTy) with
        | none => rfl
        | some _ => cases deallocateLocal mem old <;> rfl
  | storageDead localId =>
    dsimp only [evalStatementBy, evalStatement]
    cases Nat.beq localId 0 with
    | true => rfl
    | false =>
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? frame.locals localId with
      | none => rfl
      | some old =>
        dsimp only
        rw [compSetElem?_eq, deallocateLocalComp_eq]
        cases setElem? frame.locals localId .dead with
        | none => rfl
        | some _ => cases deallocateLocal mem old <;> rfl
  | assign dst rvalue =>
    dsimp only [evalStatementBy, evalStatement]
    cases (!dst.projection.isEmpty) with
    | true => rfl
    | false =>
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp only
        rw [evalRvalueBy_eq tyEq hTyEq]
        cases evalRvalue body.locals frame.locals mem dstTy rvalue with
        | error _ => rfl
        | ok triple =>
          cases triple with
          | mk val rest =>
            cases rest with
            | mk localsAfterRval memAfterRval =>
              dsimp only
              rw [writePlaceBy_eq tyEq hTyEq]
              cases writePlace localsAfterRval memAfterRval dst.localId dstTy val with
              | error _ => rfl
              | ok pair => cases pair; rfl

/-- Computable mirror of `Trusted.MirSemantics.evalSwitchBranches`. -/
@[expose] def evalSwitchBranchesComp (w : IntWidth) (discrBits : BitVec 128)
    (otherwise : BasicBlockId) (branches : List (BitVec 128 × BasicBlockId)) :
    Except FaultKind BasicBlockId :=
  List.foldr
    (fun (entry : BitVec 128 × BasicBlockId) (acc : Except FaultKind BasicBlockId) =>
      let caseBits := entry.1
      let target := entry.2
      if !(bv128BeqComp (truncateBitsComp w caseBits) caseBits) then
        .error .unsupported
      else if bv128BeqComp (truncateBitsComp w discrBits) (truncateBitsComp w caseBits) then
        .ok target
      else
        acc)
    (.ok otherwise)
    branches

/-- Agreement between `evalSwitchBranchesComp` and `evalSwitchBranches`. -/
theorem evalSwitchBranchesComp_eq (w : IntWidth) (discrBits : BitVec 128)
    (otherwise : BasicBlockId) (branches : List (BitVec 128 × BasicBlockId)) :
    evalSwitchBranchesComp w discrBits otherwise branches =
      evalSwitchBranches w discrBits otherwise branches := by
  induction branches with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | mk caseBits target =>
      change (if !(bv128BeqComp (truncateBitsComp w caseBits) caseBits) then
            Except.error FaultKind.unsupported
          else if bv128BeqComp (truncateBitsComp w discrBits) (truncateBitsComp w caseBits) then
            Except.ok target
          else evalSwitchBranchesComp w discrBits otherwise rest) =
        (if truncateBits w caseBits != caseBits then Except.error FaultKind.unsupported
          else if truncateBits w discrBits == truncateBits w caseBits then Except.ok target
          else evalSwitchBranches w discrBits otherwise rest)
      rw [bv128BneComp_eq, bv128BeqComp_eq_beq, truncateBitsComp_eq, truncateBitsComp_eq, ih]

/-- Computable mirror of `Trusted.MirSemantics.evalBoolSwitchBranches`. -/
@[expose] def evalBoolSwitchBranchesComp (discr : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) : Except FaultKind BasicBlockId :=
  List.foldr
    (fun (entry : BitVec 128 × BasicBlockId) (acc : Except FaultKind BasicBlockId) =>
      let caseBits := entry.1
      let target := entry.2
      match evalConstLitComp .bool (.scalar caseBits) with
      | .ok (.bool false) => if !discr then .ok target else acc
      | .ok (.bool true) => if discr then .ok target else acc
      | .error k => .error k
      | .ok _ => .error .unsupported)
    (.ok otherwise)
    branches

/-- Agreement between `evalBoolSwitchBranchesComp` and
`evalBoolSwitchBranches`. -/
theorem evalBoolSwitchBranchesComp_eq (discr : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    evalBoolSwitchBranchesComp discr otherwise branches =
      evalBoolSwitchBranches discr otherwise branches := by
  induction branches with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | mk caseBits target =>
      change (match evalConstLitComp .bool (.scalar caseBits) with
          | .ok (.bool false) =>
            if !discr then Except.ok target else evalBoolSwitchBranchesComp discr otherwise rest
          | .ok (.bool true) =>
            if discr then Except.ok target else evalBoolSwitchBranchesComp discr otherwise rest
          | .error k => Except.error k
          | .ok _ => Except.error FaultKind.unsupported) =
        (match evalConstLit .bool (.scalar caseBits) with
          | .ok (.bool false) =>
            if !discr then Except.ok target else evalBoolSwitchBranches discr otherwise rest
          | .ok (.bool true) =>
            if discr then Except.ok target else evalBoolSwitchBranches discr otherwise rest
          | .error k => Except.error k
          | .ok _ => Except.error FaultKind.unsupported)
      rw [evalConstLitComp_eq, ih]

/-- Computable mirror of `Trusted.MirSemantics.evalCharSwitchBranches`. -/
@[expose] def evalCharSwitchBranchesComp (discr : Char) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) : Except FaultKind BasicBlockId :=
  List.foldr
    (fun (entry : BitVec 128 × BasicBlockId) (acc : Except FaultKind BasicBlockId) =>
      let caseBits := entry.1
      let target := entry.2
      match evalConstLitComp .char (.scalar caseBits) with
      | .ok (.char c) => if Nat.beq discr.toNat c.toNat then .ok target else acc
      | .error k => .error k
      | .ok _ => .error .unsupported)
    (.ok otherwise)
    branches

/-- Agreement between `evalCharSwitchBranchesComp` and
`evalCharSwitchBranches`. -/
theorem evalCharSwitchBranchesComp_eq (discr : Char) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    evalCharSwitchBranchesComp discr otherwise branches =
      evalCharSwitchBranches discr otherwise branches := by
  induction branches with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | mk caseBits target =>
      change (match evalConstLitComp .char (.scalar caseBits) with
          | .ok (.char c) =>
            if Nat.beq discr.toNat c.toNat then Except.ok target
            else evalCharSwitchBranchesComp discr otherwise rest
          | .error k => Except.error k
          | .ok _ => Except.error FaultKind.unsupported) =
        (match evalConstLit .char (.scalar caseBits) with
          | .ok (.char c) =>
            if Nat.beq discr.toNat c.toNat then Except.ok target
            else evalCharSwitchBranches discr otherwise rest
          | .error k => Except.error k
          | .ok _ => Except.error FaultKind.unsupported)
      rw [evalConstLitComp_eq, ih]

@[expose] def jumpToBlockComp (frame : FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) (target : BasicBlockId) : StepResult State TerminalOut :=
  .step { frames := [{ frame with blockIdx := target, stmtIdx := 0 }], callerMem, mem }

/-- Computable mirror of `Trusted.MirSemantics.evalAssertFailure`. -/
@[expose] def evalAssertFailureComp (msg : AssertKind)
    (panicStrategy : PanicStrategy) (unwind : UnwindAction)
    (callerMem : CallerMemory) (hasLocalPanicHandler : Bool := true)
    (overflowChecks : Bool := false) :
    StepResult State TerminalOut :=
  match msg with
  | .misalignedPtrDeref | .nullPtrDeref => .fault .undefined
  | .boundsCheck | .overflow .div | .overflow .rem
  | .divByZero | .remByZero =>
    if hasLocalPanicHandler then
      .fault .unsupported
    else
      match panicStrategy, unwind with
      | .abort, .continue_ | .abort, .unreachable | .abort, .terminate =>
        .done (.aborted callerMem)
      | _, _ => .fault .unsupported
  | .overflow .add | .overflow .sub | .overflow .mul | .overflow .shl
  | .overflow .shr | .overflowNeg =>
    if !overflowChecks || hasLocalPanicHandler then
      .fault .unsupported
    else
      match panicStrategy, unwind with
      | .abort, .continue_ | .abort, .unreachable | .abort, .terminate =>
        .done (.aborted callerMem)
      | _, _ => .fault .unsupported
  | .overflow _ | .unsupported => .fault .unsupported

/-- Agreement between `evalAssertFailureComp` and `evalAssertFailure`. -/
theorem evalAssertFailureComp_eq (msg : AssertKind)
    (panicStrategy : PanicStrategy) (unwind : UnwindAction)
    (callerMem : CallerMemory) (hasLocalPanicHandler : Bool := true)
    (overflowChecks : Bool := false) :
    evalAssertFailureComp msg panicStrategy unwind callerMem
        hasLocalPanicHandler overflowChecks =
      evalAssertFailure msg panicStrategy unwind callerMem
        hasLocalPanicHandler overflowChecks := rfl

/-- Computable mirror of `Trusted.MirSemantics.evalTerminator`. -/
@[expose] def evalTerminatorComp (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory)
    (panicStrategy : PanicStrategy := .unwind)
    (hasLocalPanicHandler : Bool := true) :
    StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlockComp frame mem callerMem target
  | .return_ =>
    if bb.cleanup then .fault .unsupported
    else
      match compGetElem? frame.locals 0 with
      | some (.immediate (some retVal)) => .done (.returned ⟨retVal, callerMem⟩)
      | some (.immediate none) | some .dead => .fault .undefined
      | some (.partialTuple _) => .fault .unsupported
      | some (.indirect mplace) =>
        match compGetElem? body.locals 0 with
        | none => .fault .unsupported
        | some retTy =>
          match loadIndirectComp mem retTy mplace with
          | .ok (some retVal) => .done (.returned ⟨retVal, callerMem⟩)
          | .ok none => .fault .undefined
          | .error k => .fault k
      | none => .fault .unsupported
  | .unreachable => .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperandComp body.locals frame.locals mem discr with
    | .error k => .fault k
    | .ok (discrVal, localsAfterDiscr, memAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv => evalSwitchBranchesComp sv.width sv.bits targets.otherwise targets.branches
        | .bool b => evalBoolSwitchBranchesComp b targets.otherwise targets.branches
        | .char c => evalCharSwitchBranchesComp c targets.otherwise targets.branches
        | _ =>
          match targets.branches with
          | [] => .ok targets.otherwise
          | _ :: _ => .error .unsupported
      match targetRes with
      | .error k => .fault k
      | .ok target =>
        jumpToBlockComp { frame with locals := localsAfterDiscr } memAfterDiscr callerMem target
  | .assert cond expected msg target unwind =>
    match evalPrimitiveOperandComp body.locals frame.locals mem cond with
    | .error k => .fault k
    | .ok (condVal, locals1, mem1) =>
      match condVal with
      | .bool b =>
        if b == expected then
          jumpToBlockComp { frame with locals := locals1 } mem1 callerMem target
        else
          evalAssertFailureComp msg panicStrategy unwind callerMem
            hasLocalPanicHandler
      | _ => .fault .unsupported
  | .unwindResume | .call _ _ _ _ _ | .coreCall _ _ _ _ _
  | .sysrootCall _ _ _ _ _ | .callNe _ _ _ _ _ | .drop _ _ _ | .unsupported =>
    .fault .unsupported

/-- Agreement between `evalTerminatorComp` and `evalTerminator`. -/
theorem evalTerminatorComp_eq (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory)
    (panicStrategy : PanicStrategy := .unwind)
    (hasLocalPanicHandler : Bool := true) :
    evalTerminatorComp body bb frame mem callerMem panicStrategy
        hasLocalPanicHandler =
      evalTerminator body bb frame mem callerMem panicStrategy
        hasLocalPanicHandler := by
  unfold evalTerminatorComp evalTerminator
  cases bb.terminator with
  | goto _ | unreachable | unwindResume | call _ _ _ _ _ | coreCall _ _ _ _ _
  | sysrootCall _ _ _ _ _ | unsupported | callNe _ _ _ _ _ | drop _ _ _ => rfl
  | assert cond expected msg target unwind =>
    dsimp only
    rw [evalPrimitiveOperandComp_eq]
    cases evalPrimitiveOperand body.locals frame.locals mem cond with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk condVal rest =>
        cases rest with
        | mk locals1 mem1 =>
          cases condVal with
          | bool b =>
            dsimp only
            cases b == expected with
            | true => rfl
            | false =>
              exact evalAssertFailureComp_eq msg panicStrategy unwind callerMem
                hasLocalPanicHandler
          | scalar _ | char _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
          | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ | array _
          | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ => rfl
  | return_ =>
    dsimp only
    cases bb.cleanup with
    | true => rfl
    | false =>
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead | partialTuple _ => rfl
        | immediate optV => cases optV <;> rfl
        | indirect mplace =>
          dsimp only
          rw [compGetElem?_eq]
          cases Trusted.MirSemantics.getElem? body.locals 0 with
          | none => rfl
          | some retTy =>
            dsimp only
            rw [loadIndirectComp_eq]
            cases loadIndirect mem retTy mplace with
            | error _ => rfl
            | ok optRet => cases optRet <;> rfl
  | switchInt discr targets =>
    dsimp only
    rw [evalPrimitiveOperandComp_eq]
    cases evalPrimitiveOperand body.locals frame.locals mem discr with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk discrVal rest =>
        cases rest with
        | mk localsAfterDiscr memAfterDiscr =>
          cases discrVal with
          | scalar sv =>
            dsimp only
            rw [evalSwitchBranchesComp_eq]
            cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;> rfl
          | bool b =>
            dsimp only
            rw [evalBoolSwitchBranchesComp_eq]
            cases evalBoolSwitchBranches b targets.otherwise targets.branches <;> rfl
          | char c =>
            dsimp only
            rw [evalCharSwitchBranchesComp_eq]
            cases evalCharSwitchBranches c targets.otherwise targets.branches <;> rfl
          | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
          | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ =>
            dsimp only
            cases targets.branches <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.natListContains`. -/
@[expose] def natListContainsComp (x : Nat) (xs : List Nat) : Bool :=
  List.foldr (fun y ih => Nat.beq x y || ih) false xs

theorem natListContainsComp_eq (x : Nat) (xs : List Nat) :
    natListContainsComp x xs = natListContains x xs := by
  induction xs with
  | nil => rfl
  | cons y rest ih =>
    change (Nat.beq x y || natListContainsComp x rest) =
      (Nat.beq x y || natListContains x rest)
    rw [ih]

/-- Computable mirror of `Trusted.MirSemantics.movePlaceList`. -/
@[expose] def movePlaceListComp (args : List Operand) : List Place :=
  List.foldr
    (fun op acc => match op with | .move p => p :: acc | _ => acc)
    [] args

theorem movePlaceListComp_eq (args : List Operand) :
    movePlaceListComp args = movePlaceList args := by
  induction args with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | copy _ | constant _ => exact ih
    | move _ => exact congrArg (_ :: ·) ih

/-- Computable mirror of `Trusted.MirSemantics.placesDisjointAux`. -/
@[expose] def placesDisjointAuxComp (seen : List LocalId) (ps : List Place) : Bool :=
  List.foldr
    (fun (p : Place) (ih : List LocalId → Bool) (s : List LocalId) =>
      if !p.projection.isEmpty || natListContainsComp p.localId s then
        false
      else
        ih (p.localId :: s))
    (fun _ => true)
    ps seen

theorem placesDisjointAuxComp_eq (seen : List LocalId) (ps : List Place) :
    placesDisjointAuxComp seen ps = placesDisjointAux seen ps := by
  induction ps generalizing seen with
  | nil => rfl
  | cons p rest ih =>
    change (if !p.projection.isEmpty || natListContainsComp p.localId seen then
        false else placesDisjointAuxComp (p.localId :: seen) rest) =
      (if !p.projection.isEmpty || natListContains p.localId seen then
        false else placesDisjointAux (p.localId :: seen) rest)
    rw [natListContainsComp_eq, ih (p.localId :: seen)]

/-- Computable mirror of `Trusted.MirSemantics.moveDefinitelyDisjoint`. -/
@[expose] def moveDefinitelyDisjointComp (args : List Operand) (dst : Place) : Bool :=
  placesDisjointAuxComp [] (movePlaceListComp args ++ [dst])

theorem moveDefinitelyDisjointComp_eq (args : List Operand) (dst : Place) :
    moveDefinitelyDisjointComp args dst = moveDefinitelyDisjoint args dst := by
  unfold moveDefinitelyDisjointComp moveDefinitelyDisjoint
  rw [movePlaceListComp_eq, placesDisjointAuxComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.callArgsMatchBody` parameterized
by `tyEq`. -/
@[expose] def callArgsMatchBodyBy (tyEq : MirTy → MirTy → Bool)
    (bodyLocals : List MirTy) (args : List Operand) (paramTys : List MirTy) :
    Bool :=
  List.foldr
    (fun (opnd : Operand) (ih : List MirTy → Bool) (ps : List MirTy) =>
      match ps with
      | [] => false
      | paramTy :: restParams =>
        let argOk : Bool :=
          match opnd with
          | .copy place | .move place =>
            if !place.projection.isEmpty then false
            else
              match compGetElem? bodyLocals place.localId with
              | some argTy => tyEq argTy paramTy
              | none => false
          | .constant c =>
            tyEq c.ty paramTy &&
              match evalConstLitComp c.ty c.lit with
              | .ok _ => true
              | .error _ => false
        argOk && ih restParams)
    (fun ps => match ps with | [] => true | _ :: _ => false)
    args paramTys

private theorem if_true_eq_true {α : Type} (t e : α) :
    (if true = true then t else e) = t := by
  simp

private theorem if_false_eq_true {α : Type} (t e : α) :
    (if false = true then t else e) = e := by
  simp

theorem callArgsMatchBodyBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (bodyLocals : List MirTy) (args : List Operand) (paramTys : List MirTy) :
    callArgsMatchBodyBy tyEq bodyLocals args paramTys =
      callArgsMatchBody bodyLocals args paramTys := by
  induction args generalizing paramTys with
  | nil => cases paramTys <;> rfl
  | cons opnd rest ih =>
    cases paramTys with
    | nil => rfl
    | cons paramTy restParams =>
      change (_ && callArgsMatchBodyBy tyEq bodyLocals rest restParams) =
        (_ && callArgsMatchBody bodyLocals rest restParams)
      rw [ih restParams]
      cases opnd with
      | copy place | move place =>
        dsimp only
        cases (!place.projection.isEmpty) with
        | true => rfl
        | false =>
          rw [if_false_eq_true, if_false_eq_true, compGetElem?_eq]
          cases Trusted.MirSemantics.getElem? bodyLocals place.localId with
          | none => rfl
          | some argTy => dsimp only; rw [hTyEq argTy paramTy]
      | constant c =>
        dsimp only
        rw [hTyEq c.ty paramTy, evalConstLitComp_eq]
        rfl

/-- Computable mirror of `Trusted.MirSemantics.sysrootNumBinOp`. -/
@[expose] def sysrootNumBinOpComp : SysrootNumKind → BinOp
  | .uncheckedAdd => .addUnchecked
  | .uncheckedSub => .subUnchecked
  | .uncheckedMul => .mulUnchecked
  | .wrappingAdd => .add
  | .wrappingSub => .sub
  | .wrappingMul => .mul

theorem sysrootNumBinOpComp_eq (k : SysrootNumKind) :
    sysrootNumBinOpComp k = sysrootNumBinOp k := by
  cases k <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.sysrootNumBody`. -/
@[expose] def sysrootNumBodyComp (op : SysrootNumOp) : Body :=
  let ty : MirTy := .int op.width op.signed
  let isUnsafe : Bool :=
    match op.kind with
    | .uncheckedAdd | .uncheckedSub | .uncheckedMul => true
    | .wrappingAdd | .wrappingSub | .wrappingMul => false
  {
    identity := "core::num::sysroot"
    isUnsafe := isUnsafe
    argumentCount := 2
    locals := [ty, ty, ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp (sysrootNumBinOpComp op.kind)
          (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
      cleanup := false
    }]
  }

theorem sysrootNumBodyComp_eq (op : SysrootNumOp) :
    sysrootNumBodyComp op = sysrootNumBody op := by
  unfold sysrootNumBodyComp sysrootNumBody
  rw [sysrootNumBinOpComp_eq]
  rfl

/-- Computable mirror of `Trusted.MirSemantics.activeFrameBody`. -/
@[expose] def activeFrameBodyComp (p : Program) (frame : FrameState) : Option Body :=
  match frame.sysrootOp? with
  | some op => some (sysrootNumBodyComp op)
  | none => compGetElem? p.bodies frame.defId

theorem activeFrameBodyComp_eq (p : Program) (frame : FrameState) :
    activeFrameBodyComp p frame = activeFrameBody p frame := by
  unfold activeFrameBodyComp activeFrameBody
  cases frame.sysrootOp? with
  | some op => dsimp only; rw [sysrootNumBodyComp_eq]
  | none => dsimp only; rw [compGetElem?_eq]

/-- Computable mirror of `Trusted.MirSemantics.callTargetAdmitted` parameterized
by `tyEq`. -/
@[expose] def callTargetAdmittedBy (tyEq : MirTy → MirTy → Bool) (body : Body)
    (bb : BasicBlock) (calleeBody : Body) (args : List Operand) (dst : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) : Bool :=
  !bb.cleanup &&
    (match unwind with | .cleanup _ => false | _ => true) &&
    (match target with
     | none => true
     | some tgt => Nat.blt tgt body.basicBlocks.length) &&
    dst.projection.isEmpty &&
    moveDefinitelyDisjointComp args dst &&
    Nat.beq args.length calleeBody.argumentCount &&
    Nat.blt calleeBody.argumentCount calleeBody.locals.length &&
    (match compGetElem? body.locals dst.localId,
        compGetElem? calleeBody.locals 0 with
     | some dstTy, some retTy =>
       isSupportedScalarOrUnitTyComp dstTy && tyEq dstTy retTy
     | _, _ => false) &&
    callArgsMatchBodyBy tyEq body.locals args
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount)

theorem callTargetAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (body : Body) (bb : BasicBlock)
    (calleeBody : Body) (args : List Operand) (dst : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) :
    callTargetAdmittedBy tyEq body bb calleeBody args dst target unwind =
      callTargetAdmitted body bb calleeBody args dst target unwind := by
  unfold callTargetAdmittedBy callTargetAdmitted
  rw [moveDefinitelyDisjointComp_eq, compGetElem?_eq, compGetElem?_eq,
    callArgsMatchBodyBy_eq tyEq hTyEq]
  cases Trusted.MirSemantics.getElem? body.locals dst.localId with
  | none => rfl
  | some dstTy =>
    cases Trusted.MirSemantics.getElem? calleeBody.locals 0 with
    | none => rfl
    | some retTy =>
      dsimp only
      rw [isSupportedScalarOrUnitTyComp_eq, hTyEq]
      rfl

/-- Computable mirror of `Trusted.MirSemantics.callsAdmitted` parameterized by
`tyEq`. -/
@[expose] def callsAdmittedBy (tyEq : MirTy → MirTy → Bool) (p : Program) (body : Body) :
    Bool :=
  body.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .call callee args dst target unwind =>
      match compGetElem? p.bodies callee with
      | none => false
      | some calleeBody =>
        !calleeBody.isUnsafe &&
          callTargetAdmittedBy tyEq body bb calleeBody args dst target unwind
    | .sysrootCall op args dst target unwind =>
      callTargetAdmittedBy tyEq body bb (sysrootNumBodyComp op) args dst
        target unwind
    | _ => true)

theorem callsAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (body : Body) :
    callsAdmittedBy tyEq p body = callsAdmitted p body := by
  unfold callsAdmittedBy callsAdmitted
  refine listAll_congr body.basicBlocks (fun bb => ?_)
  cases bb.terminator with
  | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
  | assert _ _ _ _ _ | coreCall _ _ _ _ _ | callNe _ _ _ _ _ | drop _ _ _
  | unsupported => rfl
  | call callee args dst target unwind =>
    dsimp only
    rw [compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? p.bodies callee with
    | none => rfl
    | some calleeBody =>
      exact congrArg (fun b => !calleeBody.isUnsafe && b)
        (callTargetAdmittedBy_eq tyEq hTyEq body bb calleeBody args dst target
          unwind)
  | sysrootCall op args dst target unwind =>
    dsimp only
    rw [sysrootNumBodyComp_eq]
    exact callTargetAdmittedBy_eq tyEq hTyEq body bb (sysrootNumBody op) args dst target unwind

/-- Computable mirror of `Trusted.MirSemantics.bodyHasAnyCall`. -/
@[expose] def bodyHasAnyCallComp (body : Body) : Bool :=
  body.basicBlocks.any (fun bb =>
    match bb.terminator with
    | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
    | _ => false)

theorem bodyHasAnyCallComp_eq (body : Body) :
    bodyHasAnyCallComp body = bodyHasAnyCall body := rfl

/-- Computable mirror of `Trusted.MirSemantics.attachCallers`. -/
@[expose] def attachCallersComp (callers : List FrameState)
    (res : StepResult State TerminalOut) : StepResult State TerminalOut :=
  match callers with
  | [] => res
  | _ :: _ =>
    match res with
    | .step s' => .step { s' with frames := s'.frames ++ callers }
    | .done out => .done out
    | .fault k => .fault k

theorem attachCallersComp_eq (callers : List FrameState)
    (res : StepResult State TerminalOut) :
    attachCallersComp callers res = attachCallers callers res := by
  cases callers <;> cases res <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.evalCallArg` parameterized by
`tyEq`. -/
@[expose] def evalCallArgBy (tyEq : MirTy → MirTy → Bool) (callerLocalsTys : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (hasMove : Bool)
    (opnd : Operand) (paramTy : MirTy) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  let indirectBlocked : Bool :=
    match opnd with
    | .copy place =>
      hasMove &&
        match compGetElem? locals place.localId with
        | some (.indirect _) => true
        | _ => false
    | .move place =>
      match compGetElem? locals place.localId with
      | some (.indirect _) => true
      | _ => false
    | _ => false
  if indirectBlocked then
    .error .unsupported
  else
    match evalOperandToSlotComp callerLocalsTys locals mem
        (fun srcTy => tyEq srcTy paramTy) opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals', mem') =>
      if !tyEq srcTy paramTy then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals', mem')
        | none => .error .undefined

theorem evalCallArgBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (callerLocalsTys : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (hasMove : Bool)
    (opnd : Operand) (paramTy : MirTy) :
    evalCallArgBy tyEq callerLocalsTys locals mem hasMove opnd paramTy =
      evalCallArg callerLocalsTys locals mem hasMove opnd paramTy := by
  unfold evalCallArgBy evalCallArg
  cases opnd with
  | constant c =>
    dsimp only
    rw [if_false_eq_true, if_false_eq_true, evalOperandToSlotComp_eq callerLocalsTys locals mem
      (fun srcTy => tyEq srcTy paramTy) (fun srcTy => MirTy.beq srcTy paramTy) (.constant c)
      (fun srcTy => hTyEq srcTy paramTy)]
    cases evalOperandToSlot callerLocalsTys locals mem
        (fun srcTy => MirTy.beq srcTy paramTy) (.constant c) with
    | error _ => rfl
    | ok quad =>
      cases quad with
      | mk srcTy rest =>
        cases rest with
        | mk optVal rest2 =>
          cases rest2 with
          | mk locals' mem' =>
            dsimp only
            rw [hTyEq srcTy paramTy]
            rfl
  | copy place =>
    dsimp only
    rw [compGetElem?_eq]
    cases hasMove with
    | false =>
      rw [Bool.false_and, Bool.false_and, if_false_eq_true, if_false_eq_true,
        evalOperandToSlotComp_eq callerLocalsTys locals mem
        (fun srcTy => tyEq srcTy paramTy) (fun srcTy => MirTy.beq srcTy paramTy) (.copy place)
        (fun srcTy => hTyEq srcTy paramTy)]
      cases evalOperandToSlot callerLocalsTys locals mem
          (fun srcTy => MirTy.beq srcTy paramTy) (.copy place) with
      | error _ => rfl
      | ok quad =>
        cases quad with
        | mk srcTy rest =>
          cases rest with
          | mk optVal rest2 =>
            cases rest2 with
            | mk locals' mem' =>
              dsimp only
              rw [hTyEq srcTy paramTy]
              rfl
    | true =>
      cases Trusted.MirSemantics.getElem? locals place.localId with
      | none =>
        dsimp only
        rw [Bool.true_and, if_false_eq_true, if_false_eq_true,
          evalOperandToSlotComp_eq callerLocalsTys locals mem
          (fun srcTy => tyEq srcTy paramTy) (fun srcTy => MirTy.beq srcTy paramTy) (.copy place)
          (fun srcTy => hTyEq srcTy paramTy)]
        cases evalOperandToSlot callerLocalsTys locals mem
            (fun srcTy => MirTy.beq srcTy paramTy) (.copy place) with
        | error _ => rfl
        | ok quad =>
          cases quad with
          | mk srcTy rest =>
            cases rest with
            | mk optVal rest2 =>
              cases rest2 with
              | mk locals' mem' =>
                dsimp only
                rw [hTyEq srcTy paramTy]
                rfl
      | some sl =>
        cases sl with
        | dead | immediate _ | partialTuple _ =>
          dsimp only
          rw [Bool.true_and, if_false_eq_true, if_false_eq_true,
            evalOperandToSlotComp_eq callerLocalsTys locals mem
            (fun srcTy => tyEq srcTy paramTy) (fun srcTy => MirTy.beq srcTy paramTy) (.copy place)
            (fun srcTy => hTyEq srcTy paramTy)]
          cases evalOperandToSlot callerLocalsTys locals mem
              (fun srcTy => MirTy.beq srcTy paramTy) (.copy place) with
          | error _ => rfl
          | ok quad =>
            cases quad with
            | mk srcTy rest =>
              cases rest with
              | mk optVal rest2 =>
                cases rest2 with
                | mk locals' mem' =>
                  dsimp only
                  rw [hTyEq srcTy paramTy]
                  rfl
        | indirect _ =>
          dsimp only
          rw [Bool.true_and, if_true_eq_true, if_true_eq_true]
  | move place =>
    dsimp only
    rw [compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? locals place.localId with
    | none =>
      dsimp only
      rw [if_false_eq_true, if_false_eq_true, evalOperandToSlotComp_eq callerLocalsTys locals mem
        (fun srcTy => tyEq srcTy paramTy) (fun srcTy => MirTy.beq srcTy paramTy) (.move place)
        (fun srcTy => hTyEq srcTy paramTy)]
      cases evalOperandToSlot callerLocalsTys locals mem
          (fun srcTy => MirTy.beq srcTy paramTy) (.move place) with
      | error _ => rfl
      | ok quad =>
        cases quad with
        | mk srcTy rest =>
          cases rest with
          | mk optVal rest2 =>
            cases rest2 with
            | mk locals' mem' =>
              dsimp only
              rw [hTyEq srcTy paramTy]
              rfl
    | some sl =>
      cases sl with
      | dead | immediate _ | partialTuple _ =>
        dsimp only
        rw [if_false_eq_true, if_false_eq_true, evalOperandToSlotComp_eq callerLocalsTys locals mem
          (fun srcTy => tyEq srcTy paramTy) (fun srcTy => MirTy.beq srcTy paramTy) (.move place)
          (fun srcTy => hTyEq srcTy paramTy)]
        cases evalOperandToSlot callerLocalsTys locals mem
            (fun srcTy => MirTy.beq srcTy paramTy) (.move place) with
        | error _ => rfl
        | ok quad =>
          cases quad with
          | mk srcTy rest =>
            cases rest with
            | mk optVal rest2 =>
              cases rest2 with
              | mk locals' mem' =>
                dsimp only
                rw [hTyEq srcTy paramTy]
                rfl
      | indirect _ =>
        dsimp only
        rw [if_true_eq_true, if_true_eq_true]

/-- Computable mirror of `Trusted.MirSemantics.evalCallArgs` parameterized by
`tyEq`. -/
@[expose] def evalCallArgsBy (tyEq : MirTy → MirTy → Bool) (callerLocalsTys : List MirTy)
    (hasMove : Bool) (args : List Operand) (paramTys : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    Except FaultKind (List Val × List LocalSlot × MemoryState) :=
  List.foldr
    (fun (opnd : Operand)
         (ih : List MirTy → List LocalSlot → MemoryState →
           Except FaultKind (List Val × List LocalSlot × MemoryState))
         (ps : List MirTy) (ls : List LocalSlot) (m : MemoryState) =>
      match ps with
      | [] => .error .unsupported
      | paramTy :: restParams =>
        match evalCallArgBy tyEq callerLocalsTys ls m hasMove opnd paramTy with
        | .error k => .error k
        | .ok (v, ls₁, m₁) =>
          match ih restParams ls₁ m₁ with
          | .error k => .error k
          | .ok (vs, ls₂, m₂) => .ok (v :: vs, ls₂, m₂))
    (fun ps ls m =>
      match ps with
      | [] => .ok ([], ls, m)
      | _ :: _ => .error .unsupported)
    args paramTys locals mem

theorem evalCallArgsBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (callerLocalsTys : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (hasMove : Bool)
    (args : List Operand) (paramTys : List MirTy) :
    evalCallArgsBy tyEq callerLocalsTys hasMove args paramTys locals mem =
      evalCallArgs callerLocalsTys locals mem hasMove args paramTys := by
  induction args generalizing paramTys locals mem with
  | nil => cases paramTys <;> rfl
  | cons opnd restArgs ih =>
    cases paramTys with
    | nil => rfl
    | cons paramTy restParams =>
      change ((match evalCallArgBy tyEq callerLocalsTys locals mem hasMove opnd
            paramTy with
          | Except.error k => Except.error k
          | Except.ok (v, ls₁, m₁) =>
            match evalCallArgsBy tyEq callerLocalsTys hasMove restArgs restParams
                ls₁ m₁ with
            | Except.error k => Except.error k
            | Except.ok (vs, ls₂, m₂) => Except.ok (v :: vs, ls₂, m₂)) :
            Except FaultKind (List Val × List LocalSlot × MemoryState)) =
        (match evalCallArg callerLocalsTys locals mem hasMove opnd paramTy with
          | Except.error k => Except.error k
          | Except.ok (v, ls₁, m₁) =>
            match evalCallArgs callerLocalsTys ls₁ m₁ hasMove restArgs
                restParams with
            | Except.error k => Except.error k
            | Except.ok (vs, ls₂, m₂) => Except.ok (v :: vs, ls₂, m₂))
      rw [evalCallArgBy_eq tyEq hTyEq]
      cases evalCallArg callerLocalsTys locals mem hasMove opnd paramTy with
      | error _ => rfl
      | ok triple =>
        cases triple with
        | mk v rest =>
          cases rest with
          | mk ls₁ m₁ =>
            dsimp only
            rw [ih ls₁ m₁ restParams]

/-- Computable mirror of `Trusted.MirSemantics.stmtHasStorageMarker`. -/
@[expose] def stmtHasStorageMarkerComp (localId : LocalId) (stmt : StatementKind) : Bool :=
  match stmt with
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Agreement between `stmtHasStorageMarkerComp` and `stmtHasStorageMarker`. -/
theorem stmtHasStorageMarkerComp_eq (localId : LocalId) (stmt : StatementKind) :
    stmtHasStorageMarkerComp localId stmt = stmtHasStorageMarker localId stmt := by
  cases stmt <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.hasStorageAnnotation`. -/
@[expose] def hasStorageAnnotationComp (body : Body) (localId : LocalId) : Bool :=
  body.basicBlocks.any (fun bb => bb.statements.any (stmtHasStorageMarkerComp localId))

/-- Agreement between `hasStorageAnnotationComp` and `hasStorageAnnotation`. -/
theorem hasStorageAnnotationComp_eq (body : Body) (localId : LocalId) :
    hasStorageAnnotationComp body localId = hasStorageAnnotation body localId := by
  unfold hasStorageAnnotationComp hasStorageAnnotation
  exact listAny_congr body.basicBlocks (fun bb =>
    listAny_congr bb.statements (stmtHasStorageMarkerComp_eq localId))

/-- Computable mirror of `Trusted.MirSemantics.storageAnnotationsInBounds`. -/
@[expose] def storageAnnotationsInBoundsComp (body : Body) : Bool :=
  let numLocals := body.locals.length
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true))

/-- Agreement between `storageAnnotationsInBoundsComp` and
`storageAnnotationsInBounds`. -/
theorem storageAnnotationsInBoundsComp_eq (body : Body) :
    storageAnnotationsInBoundsComp body = storageAnnotationsInBounds body := rfl

/-- Computable mirror of `Trusted.MirSemantics.discriminantTypesValid`
parameterized by `tyEq`. -/
@[expose] def discriminantTypesValidBy (tyEq : MirTy → MirTy → Bool) (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .discriminant src =>
          if dst.projection.isEmpty && src.projection.isEmpty then
            match compGetElem? body.locals src.localId with
            | some srcTy =>
              match srcTy with
              | .enum ety =>
                match compGetElem? body.locals dst.localId with
                | some dstTy =>
                  if enumAdmittedComp ety then
                    tyEq dstTy (.int ety.discrWidth ety.discrSigned)
                  else true
                | none => true
              | .ordering =>
                match compGetElem? body.locals dst.localId with
                | some dstTy => tyEq dstTy (.int .i8 true)
                | none => true
              | _ => true
            | none => true
          else true
        | _ => true
      | _ => true))

/-- Agreement between `discriminantTypesValidBy` and `discriminantTypesValid`
when `tyEq` agrees with `MirTy.beq`. -/
theorem discriminantTypesValidBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (body : Body) :
    discriminantTypesValidBy tyEq body = discriminantTypesValid body := by
  unfold discriminantTypesValidBy discriminantTypesValid
  refine listAll_congr body.basicBlocks (fun bb => listAll_congr bb.statements (fun stmt => ?_))
  cases stmt with
  | nop | storageLive _ | storageDead _ | unsupported => rfl
  | assign dst rv =>
    cases rv with
    | use _ | useRetag _ | binaryOp _ _ _ | unaryOp _ _ | cast _ _ _ | ref _ _
    | addressOf _ _ | fakeAddressOf _ | aggregateTuple _ | aggregateArray _ _
    | repeat_ _ _ _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
    | aggregateRange _ _ _ | aggregateOption _ _ _ | unsupported
    | aggregateStruct _ _ => rfl
    | discriminant src =>
      dsimp only
      cases (dst.projection.isEmpty && src.projection.isEmpty) with
      | false => rfl
      | true =>
        rw [compGetElem?_eq, compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? body.locals src.localId with
        | none => rfl
        | some srcTy =>
          cases srcTy with
          | enum ety =>
            dsimp only
            rw [enumAdmittedComp_eq]
            cases Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => rfl
            | some dstTy =>
              cases enumAdmitted ety with
              | false => rfl
              | true => exact hTyEq dstTy (.int ety.discrWidth ety.discrSigned)
          | ordering =>
            dsimp only
            cases Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => rfl
            | some dstTy => exact hTyEq dstTy (.int .i8 true)
          | bool | int _ _ | char | unit | never | tuple _ | ref _ _ | rawPtr _ _
          | slice _ | str | array _ _ | vec _ | box _ | rangeTo _ | rangeFrom _
          | range _ | option _ | unsupported | struct_ _ _ => rfl

/-- Computable mirror of `Trusted.MirSemantics.castTypesValid` parameterized by
`tyEq`. -/
@[expose] def castTypesValidBy (tyEq : MirTy → MirTy → Bool) (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .cast .intToInt _ castTy =>
          if dst.projection.isEmpty then
            match compGetElem? body.locals dst.localId with
            | some dstTy => tyEq dstTy castTy
            | none => true
          else true
        | _ => true
      | _ => true))

/-- Agreement between `castTypesValidBy` and `castTypesValid` when `tyEq` agrees
with `MirTy.beq`. -/
theorem castTypesValidBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (body : Body) :
    castTypesValidBy tyEq body = castTypesValid body := by
  unfold castTypesValidBy castTypesValid
  refine listAll_congr body.basicBlocks (fun bb => listAll_congr bb.statements (fun stmt => ?_))
  cases stmt with
  | nop | storageLive _ | storageDead _ | unsupported => rfl
  | assign dst rv =>
    cases rv with
    | use _ | useRetag _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _ | ref _ _
    | addressOf _ _ | fakeAddressOf _ | aggregateTuple _ | aggregateArray _ _
    | repeat_ _ _ _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
    | aggregateRange _ _ _ | aggregateOption _ _ _ | unsupported
    | aggregateStruct _ _ => rfl
    | cast ck _ castTy =>
      cases ck with
      | ptrToPtr | intToPtr | unsize | boxAsRef | unsupported => rfl
      | intToInt =>
        dsimp only
        cases dst.projection.isEmpty with
        | false => rfl
        | true =>
          rw [compGetElem?_eq]
          cases Trusted.MirSemantics.getElem? body.locals dst.localId with
          | none => rfl
          | some dstTy => exact hTyEq dstTy castTy

/-- Computable mirror of `Trusted.MirSemantics.localOperandMatchesTy`
parameterized by `tyEq`. -/
@[expose] def localOperandMatchesTyBy (tyEq : MirTy → MirTy → Bool)
    (locals : List MirTy) (opnd : Operand) (expected : MirTy) : Bool :=
  match opnd with
  | .copy p | .move p =>
    if p.projection.isEmpty then
      match compGetElem? locals p.localId with
      | some srcTy => tyEq srcTy expected
      | none => true
    else
      true
  | .constant _ => true

theorem localOperandMatchesTyBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (locals : List MirTy) (opnd : Operand) (expected : MirTy) :
    localOperandMatchesTyBy tyEq locals opnd expected =
      localOperandMatchesTy locals opnd expected := by
  cases opnd with
  | constant _ => rfl
  | copy p | move p =>
    dsimp only [localOperandMatchesTyBy, localOperandMatchesTy]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? locals p.localId with
      | none => rfl
      | some srcTy => exact hTyEq srcTy expected

/-- Computable mirror of `Trusted.MirSemantics.operandTy?`. -/
@[expose] def operandTyComp? (locals : List MirTy) : Operand → Option MirTy
  | .copy p | .move p =>
    if p.projection.isEmpty then compGetElem? locals p.localId else none
  | .constant c => some c.ty

theorem operandTyComp?_eq (locals : List MirTy) (opnd : Operand) :
    operandTyComp? locals opnd = operandTy? locals opnd := by
  cases opnd with
  | constant _ => rfl
  | copy p | move p =>
    dsimp only [operandTyComp?, operandTy?]
    cases p.projection.isEmpty with
    | false => rfl
    | true => rw [compGetElem?_eq]

@[expose] def binOpLeftHomogeneousComp : BinOp → Bool
  | .add | .addUnchecked | .sub | .subUnchecked | .mul | .mulUnchecked
  | .div | .rem | .bitXor | .bitAnd | .bitOr | .offset
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow
  | .eq | .ne | .lt | .le | .gt | .ge | .cmp => false

@[expose] def binOpRightHomogeneousComp : BinOp → Bool
  | .add | .addUnchecked | .addWithOverflow | .sub | .subUnchecked
  | .subWithOverflow | .mul | .mulUnchecked | .mulWithOverflow | .div | .rem
  | .bitXor | .bitAnd | .bitOr | .eq | .ne | .lt | .le | .gt | .ge
  | .cmp => true
  | .offset | .shl | .shlUnchecked | .shr | .shrUnchecked => false

@[expose] def unOpHomogeneousComp : UnOp → Bool
  | .not | .neg => true
  | .ptrMetadata => false

theorem binOpLeftHomogeneousComp_eq (op : BinOp) :
    binOpLeftHomogeneousComp op = binOpLeftHomogeneous op := by
  cases op <;> rfl

theorem binOpRightHomogeneousComp_eq (op : BinOp) :
    binOpRightHomogeneousComp op = binOpRightHomogeneous op := by
  cases op <;> rfl

theorem unOpHomogeneousComp_eq (op : UnOp) :
    unOpHomogeneousComp op = unOpHomogeneous op := by
  cases op <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.assignTypesValid`
parameterized by `tyEq`. -/
@[expose] def assignTypesValidBy (tyEq : MirTy → MirTy → Bool) (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        if dst.projection.isEmpty then
          match compGetElem? body.locals dst.localId with
          | none => true
          | some dstTy =>
            match rv with
            | .use opnd => localOperandMatchesTyBy tyEq body.locals opnd dstTy
            | .binaryOp op lhs rhs =>
              let lhsOk : Bool :=
                if binOpLeftHomogeneousComp op then
                  localOperandMatchesTyBy tyEq body.locals lhs dstTy
                else
                  true
              let rhsOk : Bool :=
                if binOpRightHomogeneousComp op then
                  match operandTyComp? body.locals lhs with
                  | none => true
                  | some lTy => localOperandMatchesTyBy tyEq body.locals rhs lTy
                else
                  true
              lhsOk && rhsOk
            | .unaryOp op opnd =>
              if unOpHomogeneousComp op then
                localOperandMatchesTyBy tyEq body.locals opnd dstTy
              else
                true
            | _ => true
        else
          true
      | _ => true))

/-- Agreement between `assignTypesValidBy` and `assignTypesValid` when `tyEq`
agrees with `MirTy.beq`. -/
theorem assignTypesValidBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (body : Body) :
    assignTypesValidBy tyEq body = assignTypesValid body := by
  unfold assignTypesValidBy assignTypesValid
  refine listAll_congr body.basicBlocks (fun bb => listAll_congr bb.statements (fun stmt => ?_))
  cases stmt with
  | nop | storageLive _ | storageDead _ | unsupported => rfl
  | assign dst rv =>
    dsimp only
    cases dst.projection.isEmpty with
    | false => rfl
    | true =>
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rfl
      | some dstTy =>
        cases rv with
        | discriminant _ | cast _ _ _ | ref _ _ | addressOf _ _
        | fakeAddressOf _
        | aggregateTuple _ | unsupported | useRetag _ | aggregateRangeTo _ _
        | aggregateRangeFrom _ _ | aggregateArray _ _ | repeat_ _ _ _
        | aggregateOption _ _ _ | aggregateRange _ _ _
        | aggregateStruct _ _ => rfl
        | use opnd => exact localOperandMatchesTyBy_eq tyEq hTyEq body.locals opnd dstTy
        | binaryOp op lhs rhs =>
          dsimp only
          rw [binOpLeftHomogeneousComp_eq, binOpRightHomogeneousComp_eq,
            operandTyComp?_eq,
            localOperandMatchesTyBy_eq tyEq hTyEq body.locals lhs dstTy]
          cases operandTy? body.locals lhs with
          | none => rfl
          | some lTy =>
            dsimp only
            rw [localOperandMatchesTyBy_eq tyEq hTyEq body.locals rhs lTy]
        | unaryOp op opnd =>
          dsimp only
          rw [unOpHomogeneousComp_eq,
            localOperandMatchesTyBy_eq tyEq hTyEq body.locals opnd dstTy]

/-- Computable mirror of `Trusted.MirSemantics.assertConditionTypesValid`
parameterized by `tyEq`. -/
@[expose] def assertConditionTypesValidBy (tyEq : MirTy → MirTy → Bool)
    (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .assert cond _ _ _ _ =>
      match cond with
      | .copy p | .move p =>
        if p.projection.isEmpty then
          match compGetElem? body.locals p.localId with
          | some condTy => tyEq condTy .bool
          | none => true
        else true
      | .constant c => tyEq c.ty .bool
    | _ => true)

/-- Agreement between `assertConditionTypesValidBy` and
`assertConditionTypesValid` when `tyEq` agrees with `MirTy.beq`. -/
theorem assertConditionTypesValidBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (body : Body) :
    assertConditionTypesValidBy tyEq body = assertConditionTypesValid body := by
  unfold assertConditionTypesValidBy assertConditionTypesValid
  refine listAll_congr body.basicBlocks (fun bb => ?_)
  cases bb.terminator with
  | assert cond _ _ _ _ =>
    cases cond with
    | copy p | move p =>
      dsimp only
      cases p.projection.isEmpty with
      | false => rfl
      | true =>
        rw [compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? body.locals p.localId with
        | none => rfl
        | some condTy => exact hTyEq condTy .bool
    | constant c => exact hTyEq c.ty .bool
  | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
  | call _ _ _ _ _ | coreCall _ _ _ _ _ | sysrootCall _ _ _ _ _
  | callNe _ _ _ _ _ | drop _ _ _ | unsupported => rfl

/-- Computable mirror of `Trusted.MirSemantics.checkArgsMatch` parameterized by
`tyEq`. -/
@[expose] def checkArgsMatchBy (tyEq : MirTy → MirTy → Bool) (vs : List Val)
    (tys : List MirTy) : Bool :=
  List.foldr
    (fun (v : Val) (ih : List MirTy → Bool) (ts : List MirTy) =>
      match ts with
      | [] => false
      | ty :: tl => checkValBy tyEq v ty && ih tl)
    (fun ts => match ts with | [] => true | _ :: _ => false)
    vs tys

/-- Agreement between `checkArgsMatchBy` and `checkArgsMatch` when `tyEq` agrees
with `MirTy.beq`. -/
theorem checkArgsMatchBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (vs : List Val) (tys : List MirTy) :
    checkArgsMatchBy tyEq vs tys = checkArgsMatch vs tys := by
  induction vs generalizing tys with
  | nil => cases tys <;> rfl
  | cons v _ ih =>
    cases tys with
    | nil => rfl
    | cons ty tl =>
      change (checkValBy tyEq v ty && checkArgsMatchBy tyEq _ tl) =
        (checkVal v ty && checkArgsMatch _ tl)
      rw [checkValBy_eq tyEq hTyEq, ih tl]

/-- Computable mirror of `Trusted.MirSemantics.initLocalsLoop`. -/
@[expose] def initLocalsLoopComp (body : Body) (args : List Val) (startIdx : Nat)
    (tys : List MirTy) : List LocalSlot :=
  List.foldr
    (fun (ty : MirTy) (ih : Nat → List LocalSlot) (idx : Nat) =>
      let slot : LocalSlot :=
        if Nat.beq idx 0 then liveUninitSlotComp ty
        else if Nat.ble idx body.argumentCount then
          match compGetElem? args (idx - 1) with
          | some v => .immediate (some v)
          | none => .dead
        else if hasStorageAnnotationComp body idx then .dead
        else liveUninitSlotComp ty
      slot :: ih (idx + 1))
    (fun _ => [])
    tys startIdx

/-- Agreement between `initLocalsLoopComp` and `initLocalsLoop`. -/
theorem initLocalsLoopComp_eq (body : Body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    initLocalsLoopComp body args idx tys = initLocalsLoop body args idx tys := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty tl ih =>
    change (if Nat.beq idx 0 then liveUninitSlotComp ty
        else if Nat.ble idx body.argumentCount then
          match compGetElem? args (idx - 1) with
          | some v => LocalSlot.immediate (some v)
          | none => LocalSlot.dead
        else if hasStorageAnnotationComp body idx then .dead
        else liveUninitSlotComp ty) :: initLocalsLoopComp body args (idx + 1) tl =
      (if Nat.beq idx 0 then liveUninitSlot ty
        else if Nat.ble idx body.argumentCount then
          match Trusted.MirSemantics.getElem? args (idx - 1) with
          | some v => LocalSlot.immediate (some v)
          | none => LocalSlot.dead
        else if hasStorageAnnotation body idx then .dead
        else liveUninitSlot ty) :: initLocalsLoop body args (idx + 1) tl
    rw [liveUninitSlotComp_eq, compGetElem?_eq, hasStorageAnnotationComp_eq]
    exact congrArg _ (ih (idx + 1))

/-- Computable mirror of `Trusted.MirSemantics.evalCallTerminator` parameterized
by `tyEq`. -/
@[expose] def evalCallTerminatorBy (tyEq : MirTy → MirTy → Bool) (callerBody : Body)
    (bb : BasicBlock) (caller : FrameState) (callers : List FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (calleeDefId : DefId)
    (sysrootOp? : Option SysrootNumOp) (calleeBody : Body)
    (args : List Operand) (dst : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) : StepResult State TerminalOut :=
  if !callTargetAdmittedBy tyEq callerBody bb calleeBody args dst target
        unwind ||
      calleeBody.basicBlocks.isEmpty ||
      !storageAnnotationsInBoundsComp calleeBody ||
      !discriminantTypesValidBy tyEq calleeBody ||
      !castTypesValidBy tyEq calleeBody ||
      !assignTypesValidBy tyEq calleeBody ||
      !calleeBody.locals.all isSupportedScalarOrUnitTyComp then
    .fault .unsupported
  else
    let hasMove : Bool :=
      args.any (fun a => match a with | .move _ => true | _ => false)
    let paramTys := (calleeBody.locals.drop 1).take calleeBody.argumentCount
    match evalCallArgsBy tyEq callerBody.locals hasMove args paramTys
        caller.locals mem with
    | .error k => .fault k
    | .ok (argVals, callerLocals', mem') =>
      match compGetElem? callerLocals' dst.localId with
      | none => .fault .unsupported
      | some .dead => .fault .undefined
      | some (.indirect _) => .fault .unsupported
      | some (.partialTuple _) => .fault .unsupported
      | some (.immediate _) =>
        let calleeLocals :=
          initLocalsLoopComp calleeBody argVals 0 calleeBody.locals
        let calleeFrame : FrameState := {
          defId := calleeDefId
          blockIdx := 0
          stmtIdx := 0
          locals := calleeLocals
          sysrootOp? := sysrootOp?
          retDst? := some dst
          retTarget? := target
        }
        let caller' : FrameState := { caller with locals := callerLocals' }
        .step {
          frames := calleeFrame :: caller' :: callers
          callerMem := callerMem
          mem := mem'
        }

theorem evalCallTerminatorBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (callerBody : Body)
    (bb : BasicBlock) (caller : FrameState) (callers : List FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (calleeDefId : DefId)
    (sysrootOp? : Option SysrootNumOp) (calleeBody : Body)
    (args : List Operand) (dst : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) :
    evalCallTerminatorBy tyEq callerBody bb caller callers mem callerMem
        calleeDefId sysrootOp? calleeBody args dst target unwind =
      evalCallTerminator callerBody bb caller callers mem callerMem
        calleeDefId sysrootOp? calleeBody args dst target unwind := by
  unfold evalCallTerminatorBy evalCallTerminator
  rw [callTargetAdmittedBy_eq tyEq hTyEq, storageAnnotationsInBoundsComp_eq,
    discriminantTypesValidBy_eq tyEq hTyEq, castTypesValidBy_eq tyEq hTyEq,
    assignTypesValidBy_eq tyEq hTyEq,
    listAll_congr calleeBody.locals isSupportedScalarOrUnitTyComp_eq]
  cases (!callTargetAdmitted callerBody bb calleeBody args dst target unwind ||
      calleeBody.basicBlocks.isEmpty ||
      !storageAnnotationsInBounds calleeBody ||
      !discriminantTypesValid calleeBody ||
      !castTypesValid calleeBody ||
      !assignTypesValid calleeBody ||
      !calleeBody.locals.all isSupportedScalarOrUnitTy) with
  | true => rfl
  | false =>
    dsimp only
    rw [evalCallArgsBy_eq tyEq hTyEq]
    cases evalCallArgs callerBody.locals caller.locals mem _ args _ with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk argVals rest =>
        cases rest with
        | mk callerLocals' mem' =>
          dsimp only
          rw [compGetElem?_eq]
          cases Trusted.MirSemantics.getElem? callerLocals' dst.localId with
          | none => rfl
          | some slot =>
            cases slot with
            | dead | indirect _ | partialTuple _ => rfl
            | immediate _ =>
              dsimp only
              rw [initLocalsLoopComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.localsHaveIndirect`. -/
@[expose] def localsHaveIndirectComp (locals : List LocalSlot) : Bool :=
  locals.any (fun slot => match slot with | .indirect _ => true | _ => false)

theorem localsHaveIndirectComp_eq (locals : List LocalSlot) :
    localsHaveIndirectComp locals = localsHaveIndirect locals := rfl

/-- Computable mirror of `Trusted.MirSemantics.evalNonRootReturn`
parameterized by `tyEq`. -/
@[expose] def evalNonRootReturnBy (tyEq : MirTy → MirTy → Bool) (p : Program)
    (calleeBody : Body) (bb : BasicBlock) (callee : FrameState)
    (caller : FrameState) (restCallers : List FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) : StepResult State TerminalOut :=
  if bb.cleanup || localsHaveIndirectComp callee.locals then
    .fault .unsupported
  else
    let retRead : Except FaultKind Val :=
      match compGetElem? callee.locals 0 with
      | some (.immediate (some retVal)) => .ok retVal
      | some (.immediate none) | some .dead => .error .undefined
      | some (.partialTuple _) => .error .unsupported
      | some (.indirect mplace) =>
        match compGetElem? calleeBody.locals 0 with
        | none => .error .unsupported
        | some retTy =>
          match loadIndirectComp mem retTy mplace with
          | .ok (some retVal) => .ok retVal
          | .ok none => .error .undefined
          | .error k => .error k
      | none => .error .unsupported
    match retRead with
    | .error k => .fault k
    | .ok retVal =>
      match callee.retDst? with
      | none => .fault .unsupported
      | some dst =>
        if !dst.projection.isEmpty then
          .fault .unsupported
        else
          match activeFrameBodyComp p caller with
          | none => .fault .unsupported
          | some callerBody =>
            match compGetElem? callerBody.locals dst.localId with
            | none => .fault .unsupported
            | some dstTy =>
              match writePlaceBy tyEq caller.locals mem dst.localId dstTy
                  retVal with
              | .error k => .fault k
              | .ok (callerLocals', mem') =>
                match callee.retTarget? with
                | none => .fault .undefined
                | some tgt =>
                  .step {
                    frames := {
                      caller with
                      blockIdx := tgt
                      stmtIdx := 0
                      locals := callerLocals'
                    } :: restCallers
                    callerMem := callerMem
                    mem := mem'
                  }

private theorem evalNonRootReturnWrite_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program)
    (callee caller : FrameState) (restCallers : List FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (retVal : Val) :
    (match callee.retDst? with
     | none => StepResult.fault FaultKind.unsupported
     | some dst =>
       if (!dst.projection.isEmpty) = true then
         StepResult.fault FaultKind.unsupported
       else
         match activeFrameBodyComp p caller with
         | none => StepResult.fault FaultKind.unsupported
         | some callerBody =>
           match compGetElem? callerBody.locals dst.localId with
           | none => StepResult.fault FaultKind.unsupported
           | some dstTy =>
             match writePlaceBy tyEq caller.locals mem dst.localId dstTy
                 retVal with
             | Except.error k => StepResult.fault k
             | Except.ok (callerLocals', mem') =>
               match callee.retTarget? with
               | none => StepResult.fault FaultKind.undefined
               | some tgt =>
                 (StepResult.step ({
                   frames := ({
                     caller with
                     blockIdx := tgt
                     stmtIdx := 0
                     locals := callerLocals'
                   } : FrameState) :: restCallers
                   callerMem := callerMem
                   mem := mem'
                 } : State) : StepResult State TerminalOut)) =
    (match callee.retDst? with
     | none => StepResult.fault FaultKind.unsupported
     | some dst =>
       if (!dst.projection.isEmpty) = true then
         StepResult.fault FaultKind.unsupported
       else
         match activeFrameBody p caller with
         | none => StepResult.fault FaultKind.unsupported
         | some callerBody =>
           match Trusted.MirSemantics.getElem? callerBody.locals dst.localId with
           | none => StepResult.fault FaultKind.unsupported
           | some dstTy =>
             match writePlace caller.locals mem dst.localId dstTy retVal with
             | Except.error k => StepResult.fault k
             | Except.ok (callerLocals', mem') =>
               match callee.retTarget? with
               | none => StepResult.fault FaultKind.undefined
               | some tgt =>
                 (StepResult.step ({
                   frames := ({
                     caller with
                     blockIdx := tgt
                     stmtIdx := 0
                     locals := callerLocals'
                   } : FrameState) :: restCallers
                   callerMem := callerMem
                   mem := mem'
                 } : State) : StepResult State TerminalOut)) := by
  cases callee.retDst? with
  | none => rfl
  | some dst =>
    dsimp only
    cases hProj : dst.projection.isEmpty with
    | false =>
      rw [show (!false) = true from rfl, if_true_eq_true, if_true_eq_true]
    | true =>
      rw [show (!true) = false from rfl, if_false_eq_true, if_false_eq_true,
        activeFrameBodyComp_eq]
      cases activeFrameBody p caller with
      | none => rfl
      | some callerBody =>
        dsimp only
        rw [compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? callerBody.locals dst.localId with
        | none => rfl
        | some dstTy =>
          dsimp only
          rw [writePlaceBy_eq tyEq hTyEq]

theorem evalNonRootReturnBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program)
    (calleeBody : Body) (bb : BasicBlock) (callee : FrameState)
    (caller : FrameState) (restCallers : List FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) :
    evalNonRootReturnBy tyEq p calleeBody bb callee caller restCallers mem
        callerMem =
      evalNonRootReturn p calleeBody bb callee caller restCallers mem
        callerMem := by
  unfold evalNonRootReturnBy evalNonRootReturn
  rw [localsHaveIndirectComp_eq]
  cases (bb.cleanup || localsHaveIndirect callee.locals) with
  | true => rfl
  | false =>
    dsimp only
    rw [if_false_eq_true, if_false_eq_true, compGetElem?_eq]
    cases Trusted.MirSemantics.getElem? callee.locals 0 with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | partialTuple _ => rfl
      | immediate optV =>
        cases optV with
        | none => rfl
        | some retVal =>
          dsimp only
          exact evalNonRootReturnWrite_eq tyEq hTyEq p callee caller restCallers mem callerMem retVal
      | indirect mplace =>
        dsimp only
        rw [compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? calleeBody.locals 0 with
        | none => rfl
        | some retTy =>
          dsimp only
          rw [loadIndirectComp_eq]
          cases loadIndirect mem retTy mplace with
          | error _ => rfl
          | ok opt =>
            cases opt with
            | none => rfl
            | some retVal =>
              dsimp only
              exact evalNonRootReturnWrite_eq tyEq hTyEq p callee caller restCallers mem callerMem retVal

/-- Single-step MIR evaluator (`0` `noncomputable`) parameterized by `tyEq`. -/
@[expose] def evalMirStepBy (tyEq : MirTy → MirTy → Bool) (p : Program) (_c : Choice)
    (s : State) : StepResult State TerminalOut :=
  match s.frames with
  | frame :: callers =>
    match activeFrameBodyComp p frame with
    | none => .fault .unsupported
    | some body =>
      match compGetElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match compGetElem? bb.statements frame.stmtIdx with
        | some stmt =>
          attachCallersComp callers
            (evalStatementBy tyEq body frame s.mem s.callerMem stmt)
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            match bb.terminator with
            | .call callee args dst target unwind =>
              match compGetElem? p.bodies callee with
              | none => .fault .unsupported
              | some calleeBody =>
                evalCallTerminatorBy tyEq body bb frame callers s.mem
                  s.callerMem callee none calleeBody args dst target unwind
            | .sysrootCall op args dst target unwind =>
              evalCallTerminatorBy tyEq body bb frame callers s.mem
                s.callerMem 0 (some op) (sysrootNumBodyComp op) args dst target
                unwind
            | .return_ =>
              match callers with
              | [] =>
                evalTerminatorComp body bb frame s.mem s.callerMem
                  p.panicStrategy p.hasLocalPanicHandler
              | caller :: rest =>
                evalNonRootReturnBy tyEq p body bb frame caller rest s.mem
                  s.callerMem
            | _ =>
              attachCallersComp callers
                (evalTerminatorComp body bb frame s.mem s.callerMem
                  p.panicStrategy p.hasLocalPanicHandler)
          else
            .fault .unsupported
  | [] => .fault .unsupported

/-- Agreement between `evalMirStepBy` and `Trusted.MirSemantics.evalStep` when
`tyEq` agrees with `MirTy.beq`. -/
theorem evalMirStepBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (p : Program) (c : Choice) (s : State) :
    evalMirStepBy tyEq p c s = evalStep p c s := by
  unfold evalMirStepBy evalStep
  cases s.frames with
  | nil => rfl
  | cons frame callers =>
    dsimp only
    rw [activeFrameBodyComp_eq]
    cases activeFrameBody p frame with
    | none => rfl
    | some body =>
      dsimp only
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => rfl
      | some bb =>
        dsimp only
        rw [compGetElem?_eq]
        cases Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some stmt =>
          dsimp only
          rw [attachCallersComp_eq,
            evalStatementBy_eq tyEq hTyEq body frame s.mem s.callerMem stmt]
        | none =>
          dsimp only
          cases Nat.beq frame.stmtIdx bb.statements.length with
          | false => rfl
          | true =>
            rw [if_true_eq_true, if_true_eq_true]
            cases hTerm : bb.terminator with
            | call callee args dst target unwind =>
              dsimp only
              rw [compGetElem?_eq]
              cases Trusted.MirSemantics.getElem? p.bodies callee with
              | none => rfl
              | some calleeBody =>
                exact evalCallTerminatorBy_eq tyEq hTyEq body bb frame callers
                  s.mem s.callerMem callee none calleeBody args dst target unwind
            | sysrootCall op args dst target unwind =>
              dsimp only
              rw [sysrootNumBodyComp_eq]
              exact evalCallTerminatorBy_eq tyEq hTyEq body bb frame callers
                s.mem s.callerMem 0 (some op)
                (sysrootNumBody op) args dst target unwind
            | return_ =>
              cases callers with
              | nil =>
                dsimp only
                exact evalTerminatorComp_eq body bb frame s.mem s.callerMem
                  p.panicStrategy p.hasLocalPanicHandler
              | cons caller rest =>
                exact evalNonRootReturnBy_eq tyEq hTyEq p body bb frame caller
                  rest s.mem s.callerMem
            | goto _ | switchInt _ _ | unreachable | unwindResume
            | assert _ _ _ _ _ | coreCall _ _ _ _ _ | callNe _ _ _ _ _
            | drop _ _ _ | unsupported =>
              dsimp only
              rw [attachCallersComp_eq,
                evalTerminatorComp_eq body bb frame s.mem s.callerMem
                  p.panicStrategy p.hasLocalPanicHandler]

/-- Depth-bounded LCNF-computable single-step MIR evaluator (`0`
`noncomputable`). -/
@[expose] def evalMirStepAt (fuel : Nat) (p : Program) (c : Choice) (s : State) :
    StepResult State TerminalOut :=
  evalMirStepBy (mirTyBeqAt fuel) p c s

/-- Fuel-bounded MIR evaluator (`0` `noncomputable`) parameterized by `tyEq`. -/
@[expose] def evalMirFuelBy (tyEq : MirTy → MirTy → Bool) (p : Program) (fuel : Nat)
    (s : State) : StepResult State TerminalOut :=
  @Nat.rec (fun _ => State → StepResult State TerminalOut)
    (fun st => .step st)
    (fun _ ih st =>
      match evalMirStepBy tyEq p 0 st with
      | .step st' => ih st'
      | .done out => .done out
      | .fault k => .fault k)
    fuel s

/-- Lifts fuel-bounded `evalMirFuelBy` outcomes into
`Anneal.MirWp.execOutcomeState` when `tyEq` agrees with `MirTy.beq`. -/
theorem execOutcomeState_of_evalMirFuelBy {tyEq : MirTy → MirTy → Bool}
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      (match evalMirFuelBy tyEq p fuel s with
       | .done out => onDone out
       | .fault k => onFault k
       | .step _ => False) →
      Anneal.MirWp.execOutcomeState p onDone onFault fuel s
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    change (match (match evalMirStepBy tyEq p 0 s with
        | .step st' => evalMirFuelBy tyEq p fuel st'
        | .done out => StepResult.done out
        | .fault k => StepResult.fault k) with
      | .done out => onDone out
      | .fault k => onFault k
      | .step _ => False) at h
    refine Anneal.Framework.StepWp.execStepPred_succ_iff.mpr ?_
    rw [evalMirStepBy_eq tyEq hTyEq p 0 s] at h
    cases hStep : evalStep p 0 s with
    | step st' =>
      rw [hStep] at h
      exact execOutcomeState_of_evalMirFuelBy hTyEq h
    | done out =>
      rw [hStep] at h
      exact h
    | fault k =>
      rw [hStep] at h
      exact h

/-- Lifts fuel-bounded `evalMirFuelBy` outcomes to `Anneal.MirWp.wpOutcomeState`
when `tyEq` agrees with `MirTy.beq`. -/
theorem wpOutcomeState_of_evalMirFuelBy {tyEq : MirTy → MirTy → Bool}
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : match evalMirFuelBy tyEq p fuel s with
         | .done out => onDone out
         | .fault k => onFault k
         | .step _ => False) :
    Anneal.MirWp.wpOutcomeState p onDone onFault fuel s :=
  Anneal.MirWp.wpOutcomeState_of_execOutcomeState
    (execOutcomeState_of_evalMirFuelBy hTyEq h)

/-! ## Static Entry-Admission and `initState` Core -/

/-- Computable mirror of `Trusted.MirSemantics.singleBodyStaticAdmitted`
parameterized by `tyEq`. -/
@[expose] def singleBodyStaticAdmittedBy (tyEq : MirTy → MirTy → Bool) (p : Program)
    (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !body.identity.toByteArray.data.toList.isEmpty &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBoundsComp body &&
    discriminantTypesValidBy tyEq body &&
    castTypesValidBy tyEq body &&
    assertConditionTypesValidBy tyEq body &&
    body.locals.all isSupportedScalarOrUnitTyComp &&
    callsAdmittedBy tyEq p body

theorem singleBodyStaticAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (body : Body) :
    singleBodyStaticAdmittedBy tyEq p body = singleBodyStaticAdmitted p body := by
  unfold singleBodyStaticAdmittedBy singleBodyStaticAdmitted
  rw [stringIsEmptyComp_eq, storageAnnotationsInBoundsComp_eq,
      discriminantTypesValidBy_eq tyEq hTyEq,
      castTypesValidBy_eq tyEq hTyEq,
      assertConditionTypesValidBy_eq tyEq hTyEq,
      listAll_congr body.locals isSupportedScalarOrUnitTyComp_eq,
      callsAdmittedBy_eq tyEq hTyEq]

/-- Computable mirror of `Trusted.MirSemantics.callBodyStaticAdmitted`
parameterized by `tyEq`. -/
@[expose] def callBodyStaticAdmittedBy (tyEq : MirTy → MirTy → Bool) (p : Program)
    (body : Body) : Bool :=
  singleBodyStaticAdmittedBy tyEq p body && assignTypesValidBy tyEq body

theorem callBodyStaticAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (body : Body) :
    callBodyStaticAdmittedBy tyEq p body = callBodyStaticAdmitted p body := by
  unfold callBodyStaticAdmittedBy callBodyStaticAdmitted
  rw [singleBodyStaticAdmittedBy_eq tyEq hTyEq, assignTypesValidBy_eq tyEq hTyEq]

/-- Computable mirror of `Trusted.MirSemantics.allCallBodiesStaticAdmitted`
parameterized by `tyEq`. -/
@[expose] def allCallBodiesStaticAdmittedBy (tyEq : MirTy → MirTy → Bool) (p : Program)
    (body : Body) : Bool :=
  if bodyHasAnyCallComp body then
    assignTypesValidBy tyEq body &&
      p.bodies.all (callBodyStaticAdmittedBy tyEq p)
  else
    true

theorem allCallBodiesStaticAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (body : Body) :
    allCallBodiesStaticAdmittedBy tyEq p body =
      allCallBodiesStaticAdmitted p body := by
  unfold allCallBodiesStaticAdmittedBy allCallBodiesStaticAdmitted
  rw [bodyHasAnyCallComp_eq, assignTypesValidBy_eq tyEq hTyEq,
    listAll_congr p.bodies (callBodyStaticAdmittedBy_eq tyEq hTyEq p)]

/-- Computable mirror of `Trusted.MirSemantics.BodyStaticAdmitted` parameterized
by `tyEq`. -/
@[expose] def bodyStaticAdmittedBy (tyEq : MirTy → MirTy → Bool) (p : Program)
    (body : Body) : Bool :=
  singleBodyStaticAdmittedBy tyEq p body &&
    allCallBodiesStaticAdmittedBy tyEq p body

/-- Agreement between `bodyStaticAdmittedBy` and `BodyStaticAdmitted` when
`tyEq` agrees with `MirTy.beq`. -/
theorem bodyStaticAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (body : Body) :
    bodyStaticAdmittedBy tyEq p body = BodyStaticAdmitted p body := by
  unfold bodyStaticAdmittedBy BodyStaticAdmitted
  rw [singleBodyStaticAdmittedBy_eq tyEq hTyEq,
      allCallBodiesStaticAdmittedBy_eq tyEq hTyEq]

/-- Computable mirror of `Trusted.MirSemantics.initState` parameterized by
`tyEq`. -/
@[expose] def initStateBy (tyEq : MirTy → MirTy → Bool) (p : Program) (q : Query) :
    Except FaultKind State :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then
    .error .unsupported
  else if !q.callerMem.allocations.isEmpty then
    .error .unsupported
  else
    match compGetElem? p.bodies p.entryDefId with
    | none => .error .unsupported
    | some body =>
      if body.basicBlocks.isEmpty then .error .unsupported
      else if !Nat.blt body.argumentCount body.locals.length then .error .unsupported
      else if !storageAnnotationsInBoundsComp body then .error .unsupported
      else if !discriminantTypesValidBy tyEq body then .error .unsupported
      else if !castTypesValidBy tyEq body then .error .unsupported
      else if !assertConditionTypesValidBy tyEq body then .error .unsupported
      else if !body.locals.all isSupportedScalarOrUnitTyComp then .error .unsupported
      else if !callsAdmittedBy tyEq p body then .error .unsupported
      else if !allCallBodiesStaticAdmittedBy tyEq p body then .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatchBy tyEq q.args paramTys then .error .unsupported
        else
          .ok {
            frames := [{
              defId := p.entryDefId
              blockIdx := 0
              stmtIdx := 0
              locals := initLocalsLoopComp body q.args 0 body.locals
            }]
            callerMem := q.callerMem
            mem := entryMemoryComp
          }

/-- Agreement between `initStateBy` and `initState` when `tyEq` agrees with
`MirTy.beq`. -/
theorem initStateBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (q : Query) :
    initStateBy tyEq p q = initState p q := by
  dsimp only [initStateBy, initState]
  rw [compGetElem?_eq]
  cases Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
  | none => rfl
  | some body =>
    dsimp only
    rw [storageAnnotationsInBoundsComp_eq,
      discriminantTypesValidBy_eq tyEq hTyEq,
      castTypesValidBy_eq tyEq hTyEq,
      assertConditionTypesValidBy_eq tyEq hTyEq,
      listAll_congr body.locals isSupportedScalarOrUnitTyComp_eq,
      callsAdmittedBy_eq tyEq hTyEq,
      allCallBodiesStaticAdmittedBy_eq tyEq hTyEq,
      checkArgsMatchBy_eq tyEq hTyEq, initLocalsLoopComp_eq, entryMemoryComp_eq]

end Anneal.MirTotal

end
