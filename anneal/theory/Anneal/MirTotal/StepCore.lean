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
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .int w1 s1 =>
        match b with
        | .int w2 s2 => intWidthBeqComp w1 w2 && boolBeqComp s1 s2
        | .bool | .unit | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .unit =>
        match b with
        | .unit => true
        | .bool | .int _ _ | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .never =>
        match b with
        | .never => true
        | .bool | .int _ _ | .unit | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .char =>
        match b with
        | .char => true
        | .bool | .int _ _ | .unit | .never | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .ordering =>
        match b with
        | .ordering => true
        | .bool | .int _ _ | .unit | .never | .char | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .enum e1 =>
        match b with
        | .enum e2 => enumTyBeqComp e1 e2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
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
        | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .ref m1 p1 =>
        match b with
        | .ref m2 p2 => mutabilityBeqComp m1 m2 && ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .rawPtr m1 p1 =>
        match b with
        | .rawPtr m2 p2 => mutabilityBeqComp m1 m2 && ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .slice p1 =>
        match b with
        | .slice p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .rangeTo _ | .rangeFrom _ | .unsupported => false
      | .rangeTo p1 =>
        match b with
        | .rangeTo p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeFrom _ | .unsupported => false
      | .rangeFrom p1 =>
        match b with
        | .rangeFrom p2 => ih p1 p2
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .unsupported => false
      | .unsupported =>
        match b with
        | .unsupported => true
        | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
        | .tuple _ | .ref _ _ | .rawPtr _ _ | .slice _ | .rangeTo _ | .rangeFrom _ => false)
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
      | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
    | char =>
      cases v with
      | char _ => dsimp only; rw [encodeUIntComp_eq]
      | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
    | ordering =>
      cases v with
      | ordering ord => dsimp only; rw [encodeUIntComp_eq]; cases ord <;> rfl
      | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | char _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
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
      | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | char _ | ordering _ | unit | tuple _ | bytes _ => rfl
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
                        | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
                        | char _ | ordering _ | unit | enumVal _ _
                        | tuple _ | bytes _ => rfl
                    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
                    | bool _ | char _ | ordering _ | unit | enumVal _ _
                    | tuple _ | bytes _ => rfl
                | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
                | bool _ | char _ | ordering _ | unit | enumVal _ _
                | bytes _ => rfl
            | int _ _ | char | ordering | unit | never | enum _ | tuple _
            | ref _ _ | rawPtr _ _ | slice _ | rangeTo _ | rangeFrom _ | unsupported => rfl
        | bool | char | ordering | unit | never | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | slice _ | rangeTo _ | rangeFrom _ | unsupported => rfl
    | bool | unit | never | ref _ _ | rawPtr _ _ | slice _ | rangeTo _ | rangeFrom _
    | unsupported => cases v <;> rfl

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
        | immediate _ => rfl
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
        | dead => rfl
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
      | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | char _ | ordering _ | unit | tuple _ | bytes _ => rfl
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
      | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | char _ | ordering _ | unit | tuple _ | bytes _ => rfl

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
    | ptrToPtr | intToPtr | unsupported => rfl
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
        | dead => rfl
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
            | slice _ | rangeTo _ | rangeFrom _ | unsupported => rfl
  | useRetag _ | ref _ _ | addressOf _ _ | aggregateTuple _ | aggregateRangeTo _
  | aggregateRangeFrom _ | unsupported => rfl

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
    | dead => rfl
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

/-- Computable mirror of `Trusted.MirSemantics.evalTerminator`. -/
@[expose] def evalTerminatorComp (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory) :
    StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlockComp frame mem callerMem target
  | .return_ =>
    if bb.cleanup then .fault .unsupported
    else
      match compGetElem? frame.locals 0 with
      | some (.immediate (some retVal)) => .done (.returned ⟨retVal, callerMem⟩)
      | some (.immediate none) | some .dead => .fault .undefined
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
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .coreCall _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-- Agreement between `evalTerminatorComp` and `evalTerminator`. -/
theorem evalTerminatorComp_eq (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory) :
    evalTerminatorComp body bb frame mem callerMem =
      evalTerminator body bb frame mem callerMem := by
  unfold evalTerminatorComp evalTerminator
  cases bb.terminator with
  | goto _ | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | coreCall _ _ _ _ _ | unsupported => rfl
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
        | dead => rfl
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
          | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
          | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ =>
            dsimp only
            cases targets.branches <;> rfl

/-- Single-step MIR evaluator (`0` `noncomputable`) parameterized by `tyEq`. -/
@[expose] def evalMirStepBy (tyEq : MirTy → MirTy → Bool) (p : Program) (_c : Choice)
    (s : State) : StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match compGetElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match compGetElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match compGetElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatementBy tyEq body frame s.mem s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminatorComp body bb frame s.mem s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Agreement between `evalMirStepBy` and `Trusted.MirSemantics.evalStep` when
`tyEq` agrees with `MirTy.beq`. -/
theorem evalMirStepBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    (p : Program) (c : Choice) (s : State) :
    evalMirStepBy tyEq p c s = evalStep p c s := by
  unfold evalMirStepBy evalStep
  cases s.frames with
  | nil => rfl
  | cons frame tail =>
    cases tail with
    | cons _ _ => rfl
    | nil =>
      dsimp only
      rw [compGetElem?_eq]
      cases Trusted.MirSemantics.getElem? p.bodies frame.defId with
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
          | some stmt => exact evalStatementBy_eq tyEq hTyEq body frame s.mem s.callerMem stmt
          | none =>
            dsimp only
            cases Nat.beq frame.stmtIdx bb.statements.length with
            | false => rfl
            | true => exact evalTerminatorComp_eq body bb frame s.mem s.callerMem

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
    | addressOf _ _ | aggregateTuple _ | aggregateRangeTo _ | aggregateRangeFrom _
    | unsupported => rfl
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
          | slice _ | rangeTo _ | rangeFrom _ | unsupported => rfl

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
    | addressOf _ _ | aggregateTuple _ | aggregateRangeTo _ | aggregateRangeFrom _
    | unsupported => rfl
    | cast ck _ castTy =>
      cases ck with
      | ptrToPtr | intToPtr | unsupported => rfl
      | intToInt =>
        dsimp only
        cases dst.projection.isEmpty with
        | false => rfl
        | true =>
          rw [compGetElem?_eq]
          cases Trusted.MirSemantics.getElem? body.locals dst.localId with
          | none => rfl
          | some dstTy => exact hTyEq dstTy castTy

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

/-- Computable mirror of `Trusted.MirSemantics.BodyStaticAdmitted` parameterized
by `tyEq`. -/
@[expose] def bodyStaticAdmittedBy (tyEq : MirTy → MirTy → Bool) (p : Program)
    (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !body.identity.toByteArray.data.toList.isEmpty &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBoundsComp body &&
    discriminantTypesValidBy tyEq body &&
    castTypesValidBy tyEq body &&
    body.locals.all isSupportedScalarOrUnitTyComp

/-- Agreement between `bodyStaticAdmittedBy` and `BodyStaticAdmitted` when
`tyEq` agrees with `MirTy.beq`. -/
theorem bodyStaticAdmittedBy_eq (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b) (p : Program) (body : Body) :
    bodyStaticAdmittedBy tyEq p body = BodyStaticAdmitted p body := by
  unfold bodyStaticAdmittedBy BodyStaticAdmitted
  rw [stringIsEmptyComp_eq, storageAnnotationsInBoundsComp_eq,
      discriminantTypesValidBy_eq tyEq hTyEq,
      castTypesValidBy_eq tyEq hTyEq,
      listAll_congr body.locals isSupportedScalarOrUnitTyComp_eq]

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
      else if !body.locals.all isSupportedScalarOrUnitTyComp then .error .unsupported
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
      listAll_congr body.locals isSupportedScalarOrUnitTyComp_eq,
      checkArgsMatchBy_eq tyEq hTyEq, initLocalsLoopComp_eq, entryMemoryComp_eq]

end Anneal.MirTotal

end
