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
public import Anneal.MirTotal.Ops
public import Anneal.AiPcc.BitArith
public import Anneal.AiPcc.Tnum
public import Anneal.AiPcc.WrappedInterval
public import Anneal.AiPcc.ReducedProduct
public import Anneal.AiPcc.MirBridge

public section

namespace Anneal.AiPcc

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# Single-Step MIR Abstract Transfer & Soundness (`Anneal.AiPcc.MirTransfer`)

Computable Pass-1 abstract transfer functions for MIR operands, rvalues,
statements (`stepStmtAbs`), and terminators (`stepTermAbs`) over `MirAbsEnv`,
together with kernel-checked 1-step fault-freedom and soundness theorems
directly against `Trusted.MirSemantics.{evalStatement, evalTerminator}`.
-/

universe u

private theorem ite_bool_false_t {α : Sort u} {c : Bool}
    {d : Decidable (c = true)} (hc : c = false) (a b : α) :
    @ite α (c = true) d a b = b := by
  cases d with
  | isTrue h => rw [hc] at h; nomatch h
  | isFalse _ => rfl

private theorem ite_bool_true_t {α : Sort u} {c : Bool}
    {d : Decidable (c = true)} (hc : c = true) (a b : α) :
    @ite α (c = true) d a b = a := by
  cases d with
  | isTrue _ => rfl
  | isFalse h => exact False.elim (h hc)

/-! ## 1. Abstract Values and Operand Evaluation -/

/-- Abstract evaluated MIR operand value, optionally remembering the copied
source local `srcReg?` for relational comparison guard synthesis. -/
inductive MirAbsVal where
  | uint (w : IntWidth) (a : AbsVal) (srcReg? : Option LocalId)
  | bool (b : BoolAbs)
  | unit

/-- Concrete MIR type corresponding to a `MirAbsVal`. -/
@[expose] def MirAbsVal.mirTy : MirAbsVal → MirTy
  | .uint w _ _ => .int w false
  | .bool _ => .bool
  | .unit => .unit

/-- Convert a `MirAbsVal` to a `MirAbsSlot`. -/
@[expose] def MirAbsVal.toSlot : MirAbsVal → MirAbsSlot
  | .uint w a _ => .uint w a
  | .bool b => .bool b
  | .unit => .unit

/-- Concrete denotation of an evaluated `MirAbsVal` on `(ty, val)` in
`locals`. -/
@[expose] def MirAbsVal.denote (locals : List LocalSlot) (av : MirAbsVal) (ty :
    MirTy)
    (v : Val) : Prop :=
  match av with
  | .uint w a srcReg? =>
    ty = .int w false ∧
    a.isInit = true ∧
    match v with
    | .scalar sv =>
      sv.width = w ∧ sv.signed = false ∧
      sv.bits.toNat < modPow2 (bitWidthComp w) ∧
      a.denote (bitWidthComp w) (some sv.bits.toNat) ∧
      (match srcReg? with
       | none => True
       | some r => localUintNat? locals r w = some sv.bits.toNat)
    | _ => False
  | .bool ba =>
    ty = .bool ∧
    match v with
    | .bool _ => ba.denote locals (some v)
    | _ => False
  | .unit => ty = .unit ∧ v = .unit

private theorem absVal_const_sound_lt {w x : Nat} (hw : validWidth w = true)
    (hLt : x < modPow2 w) :
    (AbsVal.const w x).denote w (some x) := by
  have h := absVal_const_sound (w := w) (c := x) hw
  dsimp only [wrapVal] at h
  rw [nat_mod_eq_of_lt hLt] at h
  exact h

private theorem absVal_const_isInit {w x : Nat} (hw : validWidth w = true) :
    (AbsVal.const w x).isInit = true := by
  dsimp only [AbsVal.const, AbsVal.isInit]
  rw [hw]

private theorem absVal_exactVal?_eq {w c x : Nat} {a : AbsVal}
    (hEx : a.exactVal? w = some c) (ha : a.denote w (some x)) : x = c := by
  have h := absVal_exactVal?_sound hEx ha
  injection h.1

/-- True iff `ba` guarantees an initialized `bool` value. -/
@[expose] def BoolAbs.isInit : BoolAbs → Bool
  | .top _ => true
  | .exact _ _ => true
  | .bot | .uninit => false

/-- True iff `slot` is live (`≠ .dead`). -/
@[expose] def MirAbsSlot.isLive : MirAbsSlot → Bool
  | .dead => false
  | _ => true

/-- True iff `slot` guarantees an initialized value. -/
@[expose] def MirAbsSlot.isInit : MirAbsSlot → Bool
  | .dead => false
  | .uint _ a => a.isInit
  | .bool ba => ba.isInit
  | .unit => true

/-- Structural equality on supported scalar/bool/unit `MirTy` values. -/
@[expose] def mirTySupportedBeq : MirTy → MirTy → Bool
  | .int w1 false, .int w2 false => intWidthBeqComp w1 w2
  | .bool, .bool => true
  | .unit, .unit => true
  | _, _ => false

private theorem mirTy_eq_of_supportedBeq {t1 t2 : MirTy}
    (h : mirTySupportedBeq t1 t2 = true) : t1 = t2 := by
  cases t1 with
  | unit => cases t2 <;> first | rfl | nomatch h
  | bool => cases t2 <;> first | rfl | nomatch h
  | int w1 s1 =>
    cases s1 with
    | true => cases t2 <;> nomatch h
    | false =>
      cases t2 with
      | int w2 s2 =>
        cases s2 with
        | true => nomatch h
        | false => rw [intWidth_eq_of_beqComp h]
      | _ => nomatch h
  | _ => cases t2 <;> nomatch h

private theorem mirTy_beq_refl_supported {t : MirTy}
    (h : mirTySupportedBeq t t = true) : MirTy.beq t t = true := by
  cases t with
  | unit => rfl
  | bool => rfl
  | int w s =>
    cases s with
    | true => nomatch h
    | false =>
      dsimp only [MirTy.beq]
      rw [intWidth_beq_refl w]
      rfl
  | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
  | never | unsupported => nomatch h

/-- Abstract constant literal evaluator matching `MirSemantics.evalConstLit`
for unsigned integers, booleans, and unit. -/
@[expose] def evalConstLitAbs (c : ConstOperand) : Option MirAbsVal :=
  match c.ty, c.lit with
  | .int w false, .scalar bits =>
    if Nat.blt bits.toNat (modPow2 (bitWidthComp w)) then
      some (.uint w (AbsVal.const (bitWidthComp w) bits.toNat) none)
    else
      none
  | .bool, .scalar bits =>
    if Nat.beq bits.toNat 0 then
      some (.bool (.exact false .none))
    else if Nat.beq bits.toNat 1 then
      some (.bool (.exact true .none))
    else
      none
  | .unit, .zeroSized => some .unit
  | _, _ => none

/-- Soundness of `evalConstLitAbs` against `MirSemantics.evalConstLit`. -/
theorem evalConstLitAbs_sound {locals : List LocalSlot} {c : ConstOperand}
    {av : MirAbsVal} (h : evalConstLitAbs c = some av) :
    ∃ v, evalConstLit c.ty c.lit = .ok v ∧ av.denote locals c.ty v := by
  cases c with
  | mk ty lit =>
    cases ty with
    | int w s =>
      cases s with
      | true => cases lit <;> nomatch h
      | false =>
        cases lit with
        | scalar bits =>
          dsimp only [evalConstLitAbs] at h
          cases hLtB : Nat.blt bits.toNat (modPow2 (bitWidthComp w)) with
          | false => rw [hLtB] at h; nomatch h
          | true =>
            rw [hLtB] at h
            injection h with hAv
            subst hAv
            have hLt : bits.toNat < modPow2 (bitWidthComp w) := lt_of_blt_true hLtB
            have hTr : truncateBits w bits = bits := truncateBits_of_lt hLt
            have hNeF : (truncateBits w bits != bits) = false := by
              rw [hTr]; dsimp only [bne, BEq.beq]; rw [decide_eq_true rfl]; rfl
            refine ⟨.scalar ⟨w, false, bits⟩, ?_, ?_⟩
            · dsimp only [evalConstLit]
              rw [ite_bool_false_t hNeF, hTr]
            · exact ⟨rfl, absVal_const_isInit (bitWidthComp_valid w),
                rfl, rfl, hLt,
                absVal_const_sound_lt (bitWidthComp_valid w) hLt, True.intro⟩
        | zeroSized => nomatch h
    | bool =>
      cases lit with
      | scalar bits =>
        dsimp only [evalConstLitAbs] at h
        cases hZ : Nat.beq bits.toNat 0 with
        | true =>
          rw [hZ] at h
          injection h with hAv
          subst hAv
          have hBits0 : bits = BitVec.ofNat 128 0 := by
            have hEq := Nat.eq_of_beq_eq_true hZ
            have h1 := bitVec128_ofNat_toNat bits
            rw [hEq] at h1
            exact h1.symm
          subst hBits0
          exact ⟨.bool false, rfl, rfl, rfl, True.intro⟩
        | false =>
          rw [hZ] at h
          cases hO : Nat.beq bits.toNat 1 with
          | false => rw [hO] at h; nomatch h
          | true =>
            rw [hO] at h
            injection h with hAv
            subst hAv
            have hBits1 : bits = BitVec.ofNat 128 1 := by
              have hEq := Nat.eq_of_beq_eq_true hO
              have h1 := bitVec128_ofNat_toNat bits
              rw [hEq] at h1
              exact h1.symm
            subst hBits1
            exact ⟨.bool true, rfl, rfl, rfl, True.intro⟩
      | zeroSized => nomatch h
    | unit =>
      cases lit with
      | zeroSized =>
        injection h with hAv; subst hAv
        exact ⟨.unit, rfl, rfl, rfl⟩
      | scalar _ => nomatch h
    | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
    | never | unsupported => cases lit <;> nomatch h

/-- Abstract operand evaluation for `.copy`, `.move`, and `.constant` operands
over immediate unsigned/bool/unit locals. -/
@[expose] def evalOperandAbs (bodyLocals : List MirTy) (env : MirAbsEnv) :
    Operand → Option (MirAbsVal × MirAbsEnv)
  | .copy place =>
    if !place.projection.isEmpty then none
    else
      match compGetElem? bodyLocals place.localId,
            compGetElem? env place.localId with
      | some (.int w false), some (.uint w' a) =>
        if intWidthBeqComp w w' && a.isInit then
          some (.uint w a (some place.localId), env)
        else none
      | some .bool, some (.bool ba) =>
        if ba.isInit then some (.bool ba, env) else none
      | some .unit, some .unit => some (.unit, env)
      | _, _ => none
  | .move place =>
    if !place.projection.isEmpty then none
    else
      match compGetElem? bodyLocals place.localId,
            compGetElem? env place.localId with
      | some (.int w false), some (.uint w' a) =>
        if intWidthBeqComp w w' && a.isInit then
          match setMirAbsSlot place.localId
              (.uint w (AbsVal.uninit (bitWidthComp w))) env with
          | some env' => some (.uint w a none, env')
          | none => none
        else none
      | some .bool, some (.bool ba) =>
        if ba.isInit then
          match setMirAbsSlot place.localId (.bool .uninit) env with
          | some env' =>
            let ba' :=
              match ba with
              | .exact v _ => .exact v .none
              | .top _ => .top .none
              | other => other
            some (.bool ba', env')
          | none => none
        else none
      | some .unit, some .unit =>
        match setMirAbsSlot place.localId .unit env with
        | some env' => some (.unit, env')
        | none => none
      | _, _ => none
  | .constant c =>
    match evalConstLitAbs c with
    | some av => some (av, env)
    | none => none

private theorem compGetElem?_exists_of_len_t {α β : Type} :
    ∀ (xs : List α) (ys : List β) (i : Nat) (y : β),
      xs.length = ys.length → compGetElem? ys i = some y →
      ∃ x, compGetElem? xs i = some x
  | [], [], _, _, _, hY => nomatch hY
  | [], _ :: _, _, _, hL, _ => nomatch hL
  | _ :: _, [], _, _, hL, _ => nomatch hL
  | x :: _, _ :: _, 0, _, _, _ => ⟨x, rfl⟩
  | _ :: xs, _ :: ys, i + 1, y, hL, hY => by
    injection hL with hL'
    exact compGetElem?_exists_of_len_t xs ys i y hL' hY

/-- Soundness of `evalOperandAbs` against `MirSemantics.evalOperandToSlot`. -/
theorem evalOperandAbs_sound {bodyLocals : List MirTy} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {mem : MemoryState} {tyOk : MirTy → Bool}
    {opnd : Operand} {av : MirAbsVal}
    (hEnv : mirAbsEnvDenote bodyLocals env locals)
    (hAbs : evalOperandAbs bodyLocals env opnd = some (av, env')) :
    ∃ v locals',
      evalOperandToSlot bodyLocals locals mem tyOk opnd =
        .ok (av.mirTy, some v, locals', mem) ∧
      av.denote locals' av.mirTy v ∧
      mirAbsEnvDenote bodyLocals env' locals' := by
  cases opnd with
  | constant c =>
    dsimp only [evalOperandAbs] at hAbs
    cases hC : evalConstLitAbs c with
    | none => rw [hC] at hAbs; nomatch hAbs
    | some av0 =>
      rw [hC] at hAbs
      injection hAbs with hPair
      have hAvEq : av0 = av := congrArg Prod.fst hPair
      have hEnvEq : env = env' := congrArg Prod.snd hPair
      subst hAvEq; subst hEnvEq
      cases evalConstLitAbs_sound (locals := locals) hC with
      | intro v hv =>
        have hTyEq : av0.mirTy = c.ty := by
          cases av0 with
          | uint w a _ => exact hv.2.1.symm
          | bool ba => exact hv.2.1.symm
          | unit => exact hv.2.1.symm
        refine ⟨v, locals, ?_, ?_, hEnv⟩
        · dsimp only [evalOperandToSlot]
          rw [hv.1, hTyEq]
        · rw [hTyEq]; exact hv.2
  | copy place =>
    dsimp only [evalOperandAbs] at hAbs
    cases hProj : place.projection.isEmpty with
    | false => rw [hProj] at hAbs; nomatch hAbs
    | true =>
      rw [ite_bool_false_t (c := !place.projection.isEmpty) (by rw [hProj]; rfl)] at hAbs
      cases hTy : compGetElem? bodyLocals place.localId with
      | none => rw [hTy] at hAbs; nomatch hAbs
      | some ty =>
        cases hSlot : compGetElem? env place.localId with
        | none =>
          rw [hTy, hSlot] at hAbs
          cases ty with
          | int _ sg => cases sg <;> nomatch hAbs
          | _ => nomatch hAbs
        | some s =>
          rw [hTy, hSlot] at hAbs
          have hExCs := compGetElem?_exists_of_len_t locals bodyLocals
            place.localId ty hEnv.2.1 hTy
          cases hExCs with | intro cs hCs =>
          have hDen := hEnv.2.2 place.localId ty s cs hTy hSlot hCs
          have hNotProj : (!place.projection.isEmpty) = false := by
            rw [hProj]; rfl
          cases ty with
          | int w sg =>
            cases sg with
            | true => nomatch hAbs
            | false =>
              cases s with
              | dead | bool _ | unit => nomatch hAbs
              | uint w' a =>
                dsimp only at hAbs
                cases hC : intWidthBeqComp w w' && a.isInit with
                | false => rw [hC] at hAbs; nomatch hAbs
                | true =>
                  rw [hC] at hAbs
                  injection hAbs with hPair
                  have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                  have hInit := bool_and_true_right hC
                  subst hwEq
                  cases cs with
                  | dead | indirect _ => exact False.elim hDen.2
                  | immediate opt =>
                    cases opt with
                    | none =>
                      cases absVal_init_of_isInit hInit hDen.2 with
                      | intro _ hx => nomatch hx.1
                    | some v =>
                      cases v with
                      | scalar sv =>
                        have hLoc : localUintNat? locals place.localId w =
                            some sv.bits.toNat := by
                          dsimp only [localUintNat?]
                          rw [hCs]; dsimp only
                          rw [hDen.2.1, hDen.2.2.1]
                          have hRefl : intWidthBeqComp w w = true := by
                            cases w <;> rfl
                          rw [hRefl]; rfl
                        have hAvEq : av = .uint w a (some place.localId) :=
                          congrArg Prod.fst hPair.symm
                        have hEnvEq : env' = env :=
                          congrArg Prod.snd hPair.symm
                        subst hAvEq; subst hEnvEq
                        refine ⟨.scalar sv, locals, ?_, ?_, hEnv⟩
                        · dsimp only [evalOperandToSlot]
                          rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hCs]
                          dsimp only
                          rw [ite_bool_false_t hNotProj]
                          rfl
                        · exact ⟨rfl, hInit, hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                            hDen.2.2.2.2, hLoc⟩
                      | ptr _ | bool _ | char _ | ordering _ | unit
                      | enumVal _ _ | tuple _ | bytes _ =>
                        exact False.elim hDen.2
          | bool =>
            cases s with
            | dead | uint _ _ | unit => nomatch hAbs
            | bool ba =>
              dsimp only at hAbs
              cases hI : ba.isInit with
              | false => rw [hI] at hAbs; nomatch hAbs
              | true =>
                rw [hI] at hAbs
                injection hAbs with hPair
                have hAvEq : av = .bool ba := congrArg Prod.fst hPair.symm
                have hEnvEq : env' = env := congrArg Prod.snd hPair.symm
                subst hAvEq; subst hEnvEq
                cases cs with
                | dead | indirect _ => exact False.elim hDen.2
                | immediate opt =>
                  cases opt with
                  | none =>
                    cases ba <;> first | exact False.elim hDen.2 | nomatch hI
                  | some v =>
                    cases v with
                    | bool bv =>
                      refine ⟨.bool bv, locals, ?_, ⟨rfl, hDen.2⟩, hEnv⟩
                      dsimp only [evalOperandToSlot]
                      rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hCs]
                      dsimp only
                      rw [ite_bool_false_t hNotProj]
                      rfl
                    | scalar _ | ptr _ | char _ | ordering _ | unit
                    | enumVal _ _ | tuple _ | bytes _ =>
                      exact False.elim hDen.2
          | unit =>
            cases s with
            | dead | uint _ _ | bool _ => nomatch hAbs
            | unit =>
              injection hAbs with hPair
              have hAvEq : av = .unit := congrArg Prod.fst hPair.symm
              have hEnvEq : env' = env := congrArg Prod.snd hPair.symm
              subst hAvEq; subst hEnvEq
              have hCsEq : cs = .immediate (some .unit) := hDen.2
              subst hCsEq
              refine ⟨.unit, locals, ?_, ⟨rfl, rfl⟩, hEnv⟩
              dsimp only [evalOperandToSlot]
              rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hCs]
              dsimp only
              rw [ite_bool_false_t hNotProj]
              rfl
          | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
          | never | unsupported => nomatch hAbs
  | move place =>
    dsimp only [evalOperandAbs] at hAbs
    cases hProj : place.projection.isEmpty with
    | false => rw [hProj] at hAbs; nomatch hAbs
    | true =>
      rw [ite_bool_false_t (c := !place.projection.isEmpty) (by rw [hProj]; rfl)] at hAbs
      cases hTy : compGetElem? bodyLocals place.localId with
      | none => rw [hTy] at hAbs; nomatch hAbs
      | some ty =>
        cases hSlot : compGetElem? env place.localId with
        | none =>
          rw [hTy, hSlot] at hAbs
          cases ty with
          | int _ sg => cases sg <;> nomatch hAbs
          | _ => nomatch hAbs
        | some s =>
          rw [hTy, hSlot] at hAbs
          have hExCs := compGetElem?_exists_of_len_t locals bodyLocals
            place.localId ty hEnv.2.1 hTy
          cases hExCs with | intro cs hCs =>
          have hDen := hEnv.2.2 place.localId ty s cs hTy hSlot hCs
          have hNotProj : (!place.projection.isEmpty) = false := by
            rw [hProj]; rfl
          cases ty with
          | int w sg =>
            cases sg with
            | true => nomatch hAbs
            | false =>
              cases s with
              | dead | bool _ | unit => nomatch hAbs
              | uint w' a =>
                dsimp only at hAbs
                cases hC : intWidthBeqComp w w' && a.isInit with
                | false => rw [hC] at hAbs; nomatch hAbs
                | true =>
                  rw [hC] at hAbs
                  have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                  have hInit := bool_and_true_right hC
                  subst hwEq
                  cases hSetAbs : setMirAbsSlot place.localId
                      (.uint w (AbsVal.uninit (bitWidthComp w))) env with
                  | none => rw [hSetAbs] at hAbs; nomatch hAbs
                  | some envNew =>
                    rw [hSetAbs] at hAbs
                    injection hAbs with hPair
                    have hAvEq : av = .uint w a none :=
                      congrArg Prod.fst hPair.symm
                    have hEnvEq : env' = envNew :=
                      congrArg Prod.snd hPair.symm
                    subst hAvEq; subst hEnvEq
                    cases cs with
                    | dead | indirect _ => exact False.elim hDen.2
                    | immediate opt =>
                      cases opt with
                      | none =>
                        cases absVal_init_of_isInit hInit hDen.2 with
                        | intro _ hx => nomatch hx.1
                      | some v =>
                        cases v with
                        | scalar sv =>
                          cases compSetElem?_exists_of_get locals place.localId
                              (liveUninitSlot (.int w false)) hCs with
                          | intro locals' hSetConc =>
                            have hEnv' := setMirAbsSlot_sound hEnv hTy hSetAbs
                              hSetConc ⟨rfl, absVal_uninit_sound_none⟩
                            refine ⟨.scalar sv, locals', ?_, ?_, hEnv'⟩
                            · dsimp only [evalOperandToSlot]
                              rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hCs]
                              dsimp only
                              rw [ite_bool_false_t hNotProj, ← compSetElem?_eq,
                                  hSetConc]
                              rfl
                            · exact ⟨rfl, hInit, hDen.2.1, hDen.2.2.1, hDen.2.2.2.1,
                                hDen.2.2.2.2, True.intro⟩
                        | ptr _ | bool _ | char _ | ordering _ | unit
                        | enumVal _ _ | tuple _ | bytes _ =>
                          exact False.elim hDen.2
          | bool =>
            cases s with
            | dead | uint _ _ | unit => nomatch hAbs
            | bool ba =>
              dsimp only at hAbs
              cases hI : ba.isInit with
              | false => rw [hI] at hAbs; nomatch hAbs
              | true =>
                rw [hI] at hAbs
                cases hSetAbs : setMirAbsSlot place.localId (.bool .uninit) env with
                | none => rw [hSetAbs] at hAbs; nomatch hAbs
                | some envNew =>
                  rw [hSetAbs] at hAbs
                  injection hAbs with hPair
                  have hEnvEq : env' = envNew := congrArg Prod.snd hPair.symm
                  subst hEnvEq
                  cases cs with
                  | dead | indirect _ => exact False.elim hDen.2
                  | immediate opt =>
                    cases opt with
                    | none =>
                      cases ba <;> first | exact False.elim hDen.2 | nomatch hI
                    | some v =>
                      cases v with
                      | bool bv =>
                        cases compSetElem?_exists_of_get locals place.localId
                            (liveUninitSlot .bool) hCs with
                        | intro locals' hSetConc =>
                          have hEnv' := setMirAbsSlot_sound hEnv hTy hSetAbs
                            hSetConc ⟨rfl, True.intro⟩
                          have hAvEq := congrArg Prod.fst hPair.symm
                          subst hAvEq
                          refine ⟨.bool bv, locals', ?_, ?_, hEnv'⟩
                          · dsimp only [evalOperandToSlot]
                            rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hCs]
                            dsimp only
                            rw [ite_bool_false_t hNotProj, ← compSetElem?_eq,
                                hSetConc]
                            rfl
                          · cases ba with
                            | bot | uninit => nomatch hI
                            | top _ => exact ⟨rfl, True.intro⟩
                            | exact ev _ => exact ⟨rfl, hDen.2.1, True.intro⟩
                      | scalar _ | ptr _ | char _ | ordering _ | unit
                      | enumVal _ _ | tuple _ | bytes _ =>
                        exact False.elim hDen.2
          | unit =>
            cases s with
            | dead | uint _ _ | bool _ => nomatch hAbs
            | unit =>
              dsimp only at hAbs
              cases hSetAbs : setMirAbsSlot place.localId .unit env with
              | none => rw [hSetAbs] at hAbs; nomatch hAbs
              | some envNew =>
                rw [hSetAbs] at hAbs
                injection hAbs with hPair
                have hAvEq : av = .unit := congrArg Prod.fst hPair.symm
                have hEnvEq : env' = envNew := congrArg Prod.snd hPair.symm
                subst hAvEq; subst hEnvEq
                have hCsEq : cs = .immediate (some .unit) := hDen.2
                subst hCsEq
                cases compSetElem?_exists_of_get locals place.localId
                    (liveUninitSlot .unit) hCs with
                | intro locals' hSetConc =>
                  have hEnv' := setMirAbsSlot_sound hEnv hTy hSetAbs hSetConc
                    ⟨rfl, rfl⟩
                  refine ⟨.unit, locals', ?_, ⟨rfl, rfl⟩, hEnv'⟩
                  dsimp only [evalOperandToSlot]
                  rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hCs]
                  dsimp only
                  rw [ite_bool_false_t hNotProj, ← compSetElem?_eq, hSetConc]
                  rfl
          | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
          | never | unsupported => nomatch hAbs

/-- Soundness of `evalOperandAbs` against `evalPrimitiveOperand` for unsigned
integer and boolean operands. -/
theorem evalOperandAbs_primitive_sound {bodyLocals : List MirTy}
    {env env' : MirAbsEnv} {locals : List LocalSlot} {mem : MemoryState}
    {opnd : Operand} {av : MirAbsVal}
    (hEnv : mirAbsEnvDenote bodyLocals env locals)
    (hAbs : evalOperandAbs bodyLocals env opnd = some (av, env'))
    (hPrim : isPrimitiveReadableTy av.mirTy = true) :
    ∃ v locals',
      evalPrimitiveOperand bodyLocals locals mem opnd =
        .ok (v, locals', mem) ∧
      av.denote locals' av.mirTy v ∧
      mirAbsEnvDenote bodyLocals env' locals' := by
  cases evalOperandAbs_sound (mem := mem) (tyOk := isPrimitiveReadableTy)
      hEnv hAbs with
  | intro v hv =>
    cases hv with
    | intro locals' hRest =>
      refine ⟨v, locals', ?_, hRest.2.1, hRest.2.2⟩
      dsimp only [evalPrimitiveOperand]
      rw [hRest.1]
      dsimp only
      have hNotP : (!isPrimitiveReadableTy av.mirTy) = false := by
        rw [hPrim]; rfl
      rw [ite_bool_false_t hNotP]

/-! ## 2. Abstract Rvalue Evaluation (`evalRvalueAbs`) -/

/-- True iff `opnd` does not mutate `locals` (`.copy` or `.constant`). -/
@[expose] def operandIsPure : Operand → Bool
  | .copy _ => true
  | .constant _ => true
  | .move _ => false

private theorem evalOperandAbs_pure_locals_eq {bodyLocals : List MirTy}
    {env env' : MirAbsEnv} {locals locals' : List LocalSlot}
    {mem : MemoryState} {opnd : Operand} {av : MirAbsVal} {v : Val}
    (hPure : operandIsPure opnd = true)
    (hEval : evalPrimitiveOperand bodyLocals locals mem opnd =
      .ok (v, locals', mem))
    (hAbs : evalOperandAbs bodyLocals env opnd = some (av, env')) :
    locals' = locals := by
  cases opnd with
  | move _ => nomatch hPure
  | constant c =>
    dsimp only [evalPrimitiveOperand, evalOperandToSlot] at hEval
    cases hC : evalConstLit c.ty c.lit with
    | error k => rw [hC] at hEval; nomatch hEval
    | ok vc =>
      rw [hC] at hEval
      dsimp only at hEval
      cases hP : isPrimitiveReadableTy c.ty with
      | false =>
        rw [ite_bool_true_t (by rw [hP]; rfl)] at hEval
        nomatch hEval
      | true =>
        rw [ite_bool_false_t (by rw [hP]; rfl)] at hEval
        injection hEval with hEq
        exact (congrArg (fun p => p.2.1) hEq).symm
  | copy place =>
    dsimp only [evalOperandAbs] at hAbs
    cases hProj : place.projection.isEmpty with
    | false => rw [hProj] at hAbs; nomatch hAbs
    | true =>
      dsimp only [evalPrimitiveOperand, evalOperandToSlot] at hEval
      cases hT : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hT] at hEval; nomatch hEval
      | some ty =>
        cases hS : Trusted.MirSemantics.getElem? locals place.localId with
        | none => rw [hT, hS] at hEval; nomatch hEval
        | some cs =>
          rw [hT, hS] at hEval
          cases cs with
          | dead => dsimp only at hEval; nomatch hEval
          | immediate opt =>
            dsimp only at hEval
            rw [ite_bool_false_t (by rw [hProj]; rfl)] at hEval
            dsimp only at hEval
            cases hP : isPrimitiveReadableTy ty with
            | false =>
              rw [ite_bool_true_t (by rw [hP]; rfl)] at hEval
              nomatch hEval
            | true =>
              rw [ite_bool_false_t (by rw [hP]; rfl)] at hEval
              cases opt with
              | none => nomatch hEval
              | some vc =>
                injection hEval with hEq
                exact (congrArg (fun p => p.2.1) hEq).symm
          | indirect mp =>
            dsimp only at hEval
            rw [ite_bool_false_t (by rw [hProj]; rfl)] at hEval
            cases hP : isPrimitiveReadableTy ty with
            | false =>
              rw [ite_bool_true_t (by rw [hP]; rfl)] at hEval
              nomatch hEval
            | true =>
              rw [ite_bool_false_t (by rw [hP]; rfl)] at hEval
              cases hLd : loadIndirect mem ty mp with
              | error k => rw [hLd] at hEval; nomatch hEval
              | ok opt =>
                rw [hLd] at hEval
                dsimp only at hEval
                rw [ite_bool_false_t (by rw [hP]; rfl)] at hEval
                cases opt with
                | none => nomatch hEval
                | some vc =>
                  injection hEval with hEq
                  exact (congrArg (fun p => p.2.1) hEq).symm

/-- Synthesize a `RelGuard` from an unsigned comparison on pure operands. -/
@[expose] def synthCmpGuard (op : BinOp) (w : IntWidth)
    (srcL? srcR? : Option LocalId) (a1 a2 : AbsVal) : RelGuard :=
  match op, srcL?, srcR?, a1.exactVal? (bitWidthComp w),
        a2.exactVal? (bitWidthComp w) with
  | .le, some r, _, _, some b => .uleConst r w b
  | .gt, some r, _, _, some b => .ugtConst r w b
  | .lt, some r, _, _, some b =>
    match b with
    | 0 => .none
    | k + 1 => .uleConst r w k
  | .ge, some r, _, _, some b =>
    match b with
    | 0 => .none
    | k + 1 => .ugtConst r w k
  | .lt, some l, some r, _, _ => .ultReg l r w
  | .ge, some l, some r, _, _ => .ugeReg l r w
  | .gt, some l, some r, _, _ => .ultReg r l w
  | .le, some l, some r, _, _ => .ugeReg r l w
  | .eq, some r, _, _, some v => .ueqConst r w v
  | .ne, some r, _, _, some v => .uneConst r w v
  | .eq, _, some r, some v, _ => .ueqConst r w v
  | .ne, _, some r, some v, _ => .uneConst r w v
  | _, _, _, _, _ => .none

/-- Static decision of unsigned comparison `op` between `a1` and `a2`. -/
@[expose] def decideCmpAbs (op : BinOp) (w : Nat) (a1 a2 : AbsVal) : Option Bool
    :=
  match op with
  | .eq => AbsVal.decideEq? w a1 a2
  | .ne => (AbsVal.decideEq? w a1 a2).map Bool.not
  | .le => AbsVal.decideLe? w a1 a2
  | .lt => AbsVal.decideLt? w a1 a2
  | .ge => AbsVal.decideLe? w a2 a1
  | .gt => AbsVal.decideLt? w a2 a1
  | _ => none

/-- Build a `BoolAbs` from an optional statically known boolean and guard. -/
@[expose] def mkBoolAbs (known? : Option Bool) (g : RelGuard) : BoolAbs :=
  match known? with
  | some v => .exact v g
  | none => .top g

/-- Unsigned integer-to-integer cast transfer in `AbsVal`. -/
@[expose] def castUintAbs (wSrc wDst : IntWidth) (a : AbsVal) : AbsVal :=
  if Nat.beq (bitWidthComp wSrc) (bitWidthComp wDst) then
    a
  else
    match a.exactVal? (bitWidthComp wSrc) with
    | some x => AbsVal.const (bitWidthComp wDst) (wrapVal (bitWidthComp wDst) x)
    | none =>
      if Nat.ble (bitWidthComp wSrc) (bitWidthComp wDst) then
        AbsVal.refineUleConst (bitWidthComp wDst)
          (AbsVal.topInit (bitWidthComp wDst)) (modPow2 (bitWidthComp wSrc) - 1)
      else
        AbsVal.topInit (bitWidthComp wDst)

/-- Soundness of `castUintAbs`. -/
theorem castUintAbs_sound {wSrc wDst : IntWidth} {a : AbsVal} {x : Nat}
    (ha : a.denote (bitWidthComp wSrc) (some x))
    (hx : x < modPow2 (bitWidthComp wSrc)) :
    (castUintAbs wSrc wDst a).denote (bitWidthComp wDst)
      (some (wrapVal (bitWidthComp wDst) x)) := by
  dsimp only [castUintAbs]
  cases hEq : Nat.beq (bitWidthComp wSrc) (bitWidthComp wDst) with
  | true =>
    have hw : bitWidthComp wSrc = bitWidthComp wDst := Nat.eq_of_beq_eq_true hEq
    rw [ite_bool_true_t (c := true) rfl, ← hw]
    dsimp only [wrapVal]
    rw [nat_mod_eq_of_lt hx]
    exact ha
  | false =>
    rw [ite_bool_false_t (c := false) rfl]
    cases hEx : a.exactVal? (bitWidthComp wSrc) with
    | some c =>
      have hXc := absVal_exactVal?_eq hEx ha
      subst hXc
      exact absVal_const_sound_lt (bitWidthComp_valid wDst)
        (nat_mod_lt x (modPow2_pos (bitWidthComp wDst)))
    | none =>
      cases hLe : Nat.ble (bitWidthComp wSrc) (bitWidthComp wDst) with
      | true =>
        rw [ite_bool_true_t (c := true) rfl]
        have hPowLe : modPow2 (bitWidthComp wSrc) ≤ modPow2 (bitWidthComp wDst) :=
          modPow2_mono (Nat.le_of_ble_eq_true hLe)
        have hLtDst : x < modPow2 (bitWidthComp wDst) :=
          Nat.lt_of_lt_of_le hx hPowLe
        have hWrap : wrapVal (bitWidthComp wDst) x = x := nat_mod_eq_of_lt hLtDst
        rw [hWrap]
        have hLeB : x ≤ modPow2 (bitWidthComp wSrc) - 1 := Nat.le_pred_of_lt hx
        exact absVal_refineUleConst_sound (bitWidthComp_valid wDst)
          (absVal_topInit_sound hLtDst) rfl hLeB
      | false =>
        rw [ite_bool_false_t (c := false) rfl]
        exact absVal_topInit_sound
          (nat_mod_lt x (modPow2_pos (bitWidthComp wDst)))

/-- Abstract rvalue evaluator matching `Trusted.MirSemantics.evalRvalue` over
immediate unsigned integer, boolean, and unit operations. -/
@[expose] def evalRvalueAbs (bodyLocals : List MirTy) (env : MirAbsEnv) (dstTy :
    MirTy) :
    Rvalue → Option (MirAbsSlot × MirAbsEnv)
  | .use opnd =>
    match evalOperandAbs bodyLocals env opnd with
    | some (av, env₁) =>
      if mirTySupportedBeq av.mirTy dstTy then
        some (av.toSlot, env₁)
      else none
    | none => none
  | .unaryOp .not opnd =>
    match evalOperandAbs bodyLocals env opnd with
    | some (.bool ba, env₁) =>
      if mirTySupportedBeq .bool dstTy then
        let negBa : BoolAbs :=
          match ba with
          | .exact v g => .exact (!v) g.negate
          | .top g => .top g.negate
          | other => other
        some (.bool negBa, env₁)
      else none
    | _ => none
  | .cast .intToInt opnd (.int wDst false) =>
    if mirTySupportedBeq (.int wDst false) dstTy then
      match evalOperandAbs bodyLocals env opnd with
      | some (.uint wSrc a _, env₁) =>
        some (.uint wDst (castUintAbs wSrc wDst a), env₁)
      | _ => none
    else none
  | .binaryOp op lhs rhs =>
    match evalOperandAbs bodyLocals env lhs with
    | none => none
    | some (.uint w1 a1 srcL?, env₁) =>
      match evalOperandAbs bodyLocals env₁ rhs with
      | none => none
      | some (.uint w2 a2 srcR?, env₂) =>
        let bw := bitWidthComp w1
        let bw2 := bitWidthComp w2
        match op with
        | .add =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy then
            some (.uint w1 (AbsVal.addWrap bw a1 a2), env₂)
          else none
        | .addUnchecked =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy &&
             AbsVal.noOverflowAdd bw a1 a2 then
            some (.uint w1 (AbsVal.addWrap bw a1 a2), env₂)
          else none
        | .sub =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy then
            some (.uint w1 (AbsVal.subWrap bw a1 a2), env₂)
          else none
        | .subUnchecked =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy &&
             AbsVal.noUnderflowSub bw a1 a2 then
            some (.uint w1 (AbsVal.subWrap bw a1 a2), env₂)
          else none
        | .bitAnd =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy then
            some (.uint w1 (AbsVal.bitAnd bw a1 a2), env₂)
          else none
        | .bitOr =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy then
            some (.uint w1 (AbsVal.bitOr bw a1 a2), env₂)
          else none
        | .bitXor =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy then
            some (.uint w1 (AbsVal.bitXor bw a1 a2), env₂)
          else none
        | .shl =>
          if mirTySupportedBeq (.int w1 false) dstTy then
            let resA :=
              match a2.exactVal? bw2 with
              | some k => AbsVal.shlConst bw (Nat.mod k bw) a1
              | none => AbsVal.topInit bw
            some (.uint w1 resA, env₂)
          else none
        | .shlUnchecked =>
          if mirTySupportedBeq (.int w1 false) dstTy &&
             AbsVal.shiftInBounds bw bw2 a2 then
            let resA :=
              match a2.exactVal? bw2 with
              | some k => AbsVal.shlConst bw k a1
              | none => AbsVal.topInit bw
            some (.uint w1 resA, env₂)
          else none
        | .shr =>
          if mirTySupportedBeq (.int w1 false) dstTy then
            let resA :=
              match a2.exactVal? bw2 with
              | some k => AbsVal.shrConst bw (Nat.mod k bw) a1
              | none => AbsVal.topInit bw
            some (.uint w1 resA, env₂)
          else none
        | .shrUnchecked =>
          if mirTySupportedBeq (.int w1 false) dstTy &&
             AbsVal.shiftInBounds bw bw2 a2 then
            let resA :=
              match a2.exactVal? bw2 with
              | some k => AbsVal.shrConst bw k a1
              | none => AbsVal.topInit bw
            some (.uint w1 resA, env₂)
          else none
        | .div | .rem =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq (.int w1 false) dstTy &&
             AbsVal.nonzeroDiv bw a2 then
            some (.uint w1 (AbsVal.topInit bw), env₂)
          else none
        | .eq | .ne | .lt | .le | .gt | .ge =>
          if intWidthBeqComp w1 w2 && mirTySupportedBeq .bool dstTy then
            let g :=
              if operandIsPure lhs && operandIsPure rhs then
                synthCmpGuard op w1 srcL? srcR? a1 a2
              else .none
            some (.bool (mkBoolAbs (decideCmpAbs op bw a1 a2) g), env₂)
          else none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

private theorem bool_not_eq_of_eq {b1 b2 : Bool} (h : b1 = b2) :
    (!b1) = (!b2) := congrArg Bool.not h

private theorem evalCmp_bool_sound {w : IntWidth} {op : BinOp}
    {locals : List LocalSlot} {srcL? srcR? : Option LocalId}
    {a1 a2 : AbsVal} {b1 b2 : BitVec 128}
    (h1 : b1.toNat < modPow2 (bitWidthComp w))
    (h2 : b2.toNat < modPow2 (bitWidthComp w))
    (ha1 : a1.denote (bitWidthComp w) (some b1.toNat))
    (ha2 : a2.denote (bitWidthComp w) (some b2.toNat))
    (hSrcL : match srcL? with
      | none => True
      | some r => localUintNat? locals r w = some b1.toNat)
    (hSrcR : match srcR? with
      | none => True
      | some r => localUintNat? locals r w = some b2.toNat)
    (hCmpOp : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) :
    ∃ resB : Bool,
      evalBinOp op (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
        .ok (.bool resB) ∧
      (mkBoolAbs (decideCmpAbs op (bitWidthComp w) a1 a2)
        (synthCmpGuard op w srcL? srcR? a1 a2)).denote locals
        (some (.bool resB)) ∧
      (mkBoolAbs (decideCmpAbs op (bitWidthComp w) a1 a2) .none).denote locals
        (some (.bool resB)) := by
  have hMk : ∀ (k? : Option Bool) (g : RelGuard) (rb : Bool),
      (∀ v, k? = some v → rb = v) →
      g.denote locals rb →
      (mkBoolAbs k? g).denote locals (some (.bool rb)) ∧
      (mkBoolAbs k? .none).denote locals (some (.bool rb)) := by
    intro k? g rb hk hg
    cases k? with
    | none => exact ⟨hg, True.intro⟩
    | some v => exact ⟨⟨hk v rfl, hg⟩, ⟨hk v rfl, True.intro⟩⟩
  have hEqNat : ∀ x y : Nat, (Nat.beq x y = true) ↔ (x = y) := fun x y =>
    ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h, nat_beq_refl]⟩
  have hNeNat : ∀ x y : Nat, ((!Nat.beq x y) = true) ↔ (x ≠ y) := fun x y => by
    cases hB : Nat.beq x y with
    | true =>
      have hE := Nat.eq_of_beq_eq_true hB
      exact ⟨(fun hF => nomatch hF), fun hN => False.elim (hN hE)⟩
    | false =>
      have hN : x ≠ y := fun hE => by rw [hE, nat_beq_refl] at hB; nomatch hB
      exact ⟨fun _ => hN, fun _ => rfl⟩
  have hLtNat : ∀ x y : Nat, (Nat.blt x y = true) ↔ (x < y) := fun x y =>
    ⟨lt_of_blt_true, blt_true_of_lt⟩
  have hLeNat : ∀ x y : Nat, (Nat.ble x y = true) ↔ (x ≤ y) := fun x y =>
    ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩
  cases hCmpOp with
  | inl hOp =>
    subst hOp
    refine ⟨Nat.beq b1.toNat b2.toNat, evalBinOp_uint_eq h1 h2, ?_⟩
    apply hMk
    · intro v hv
      exact absVal_decideEq?_sound hv ha1 ha2
    · dsimp only [synthCmpGuard]
      cases srcL? with
      | some r =>
        cases hEx2 : a2.exactVal? (bitWidthComp w) with
        | some v =>
          have h2Eq := absVal_exactVal?_eq hEx2 ha2
          intro x hx
          rw [hSrcL] at hx
          injection hx with hxEq
          subst hxEq
          rw [h2Eq]
          exact hEqNat b1.toNat v
        | none =>
          cases srcR? with
          | some r2 =>
            cases hEx1 : a1.exactVal? (bitWidthComp w) with
            | some v =>
              have h1Eq := absVal_exactVal?_eq hEx1 ha1
              intro x hx
              rw [hSrcR] at hx
              injection hx with hxEq
              subst hxEq
              rw [h1Eq]
              constructor
              · intro hB; exact (Nat.eq_of_beq_eq_true hB).symm
              · intro hE; rw [hE, nat_beq_refl]
            | none => exact True.intro
          | none => exact True.intro
      | none =>
        cases srcR? with
        | some r2 =>
          cases hEx1 : a1.exactVal? (bitWidthComp w) with
          | some v =>
            have h1Eq := absVal_exactVal?_eq hEx1 ha1
            intro x hx
            rw [hSrcR] at hx
            injection hx with hxEq
            subst hxEq
            rw [h1Eq]
            constructor
            · intro hB; exact (Nat.eq_of_beq_eq_true hB).symm
            · intro hE; rw [hE, nat_beq_refl]
          | none => exact True.intro
        | none => exact True.intro
  | inr hCmpOp =>
    cases hCmpOp with
    | inl hOp =>
      subst hOp
      refine ⟨!Nat.beq b1.toNat b2.toNat, evalBinOp_uint_ne h1 h2, ?_⟩
      apply hMk
      · intro v hv
        dsimp only [decideCmpAbs] at hv
        cases hD : AbsVal.decideEq? (bitWidthComp w) a1 a2 with
        | none => rw [hD] at hv; nomatch hv
        | some bv =>
          rw [hD] at hv
          injection hv with hvEq
          subst hvEq
          exact bool_not_eq_of_eq (absVal_decideEq?_sound hD ha1 ha2)
      · dsimp only [synthCmpGuard]
        cases srcL? with
        | some r =>
          cases hEx2 : a2.exactVal? (bitWidthComp w) with
          | some v =>
            have h2Eq := absVal_exactVal?_eq hEx2 ha2
            intro x hx
            rw [hSrcL] at hx
            injection hx with hxEq
            subst hxEq
            rw [h2Eq]
            exact hNeNat b1.toNat v
          | none =>
            cases srcR? with
            | some r2 =>
              cases hEx1 : a1.exactVal? (bitWidthComp w) with
              | some v =>
                have h1Eq := absVal_exactVal?_eq hEx1 ha1
                intro x hx
                rw [hSrcR] at hx
                injection hx with hxEq
                subst hxEq
                rw [h1Eq]
                have hI := hNeNat v b2.toNat
                exact ⟨fun hB hE => hI.mp hB hE.symm, fun hN => hI.mpr (fun hE => hN hE.symm)⟩
              | none => exact True.intro
            | none => exact True.intro
        | none =>
          cases srcR? with
          | some r2 =>
            cases hEx1 : a1.exactVal? (bitWidthComp w) with
            | some v =>
              have h1Eq := absVal_exactVal?_eq hEx1 ha1
              intro x hx
              rw [hSrcR] at hx
              injection hx with hxEq
              subst hxEq
              rw [h1Eq]
              have hI := hNeNat v b2.toNat
              exact ⟨fun hB hE => hI.mp hB hE.symm, fun hN => hI.mpr (fun hE => hN hE.symm)⟩
            | none => exact True.intro
          | none => exact True.intro
    | inr hCmpOp =>
      cases hCmpOp with
      | inl hOp =>
        subst hOp
        refine ⟨Nat.blt b1.toNat b2.toNat, evalBinOp_uint_lt h1 h2, ?_⟩
        apply hMk
        · intro v hv
          exact absVal_decideLt?_sound hv ha1 ha2
        · dsimp only [synthCmpGuard]
          cases srcL? with
          | none => exact True.intro
          | some l =>
            cases hEx2 : a2.exactVal? (bitWidthComp w) with
            | some b =>
              have h2Eq := absVal_exactVal?_eq hEx2 ha2
              cases b with
              | zero => exact True.intro
              | succ k =>
                intro x hx
                rw [hSrcL] at hx
                injection hx with hxEq
                subst hxEq
                rw [h2Eq]
                constructor
                · intro hB; exact Nat.le_of_lt_succ (lt_of_blt_true hB)
                · intro hL; exact blt_true_of_lt (Nat.lt_succ_of_le hL)
            | none =>
              cases srcR? with
              | none => exact True.intro
              | some r =>
                intro x y hx hy
                rw [hSrcL] at hx; rw [hSrcR] at hy
                injection hx with hxEq; injection hy with hyEq
                subst hxEq; subst hyEq
                exact hLtNat b1.toNat b2.toNat
      | inr hCmpOp =>
        cases hCmpOp with
        | inl hOp =>
          subst hOp
          refine ⟨Nat.ble b1.toNat b2.toNat, evalBinOp_uint_le h1 h2, ?_⟩
          apply hMk
          · intro v hv
            exact absVal_decideLe?_sound hv ha1 ha2
          · dsimp only [synthCmpGuard]
            cases srcL? with
            | none => exact True.intro
            | some l =>
              cases hEx2 : a2.exactVal? (bitWidthComp w) with
              | some b =>
                have h2Eq := absVal_exactVal?_eq hEx2 ha2
                intro x hx
                rw [hSrcL] at hx
                injection hx with hxEq
                subst hxEq
                rw [h2Eq]
                exact hLeNat b1.toNat b
              | none =>
                cases srcR? with
                | none => exact True.intro
                | some r =>
                  intro x y hx hy
                  rw [hSrcR] at hx; rw [hSrcL] at hy
                  injection hx with hxEq; injection hy with hyEq
                  subst hxEq; subst hyEq
                  exact hLeNat b1.toNat b2.toNat
        | inr hCmpOp =>
          cases hCmpOp with
          | inl hOp =>
            subst hOp
            refine ⟨Nat.blt b2.toNat b1.toNat, evalBinOp_uint_gt h1 h2, ?_⟩
            apply hMk
            · intro v hv
              exact absVal_decideLt?_sound hv ha2 ha1
            · dsimp only [synthCmpGuard]
              cases srcL? with
              | none => exact True.intro
              | some l =>
                cases hEx2 : a2.exactVal? (bitWidthComp w) with
                | some b =>
                  have h2Eq := absVal_exactVal?_eq hEx2 ha2
                  intro x hx
                  rw [hSrcL] at hx
                  injection hx with hxEq
                  subst hxEq
                  rw [h2Eq]
                  exact hLtNat b b1.toNat
                | none =>
                  cases srcR? with
                  | none => exact True.intro
                  | some r =>
                    intro x y hx hy
                    rw [hSrcR] at hx; rw [hSrcL] at hy
                    injection hx with hxEq; injection hy with hyEq
                    subst hxEq; subst hyEq
                    exact hLtNat b2.toNat b1.toNat
          | inr hOp =>
            subst hOp
            refine ⟨Nat.ble b2.toNat b1.toNat, evalBinOp_uint_ge h1 h2, ?_⟩
            apply hMk
            · intro v hv
              exact absVal_decideLe?_sound hv ha2 ha1
            · dsimp only [synthCmpGuard]
              cases srcL? with
              | none => exact True.intro
              | some l =>
                cases hEx2 : a2.exactVal? (bitWidthComp w) with
                | some b =>
                  have h2Eq := absVal_exactVal?_eq hEx2 ha2
                  cases b with
                  | zero => exact True.intro
                  | succ k =>
                    intro x hx
                    rw [hSrcL] at hx
                    injection hx with hxEq
                    subst hxEq
                    rw [h2Eq]
                    constructor
                    · intro hB; exact Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hB)
                    · intro hGt; exact Nat.ble_eq_true_of_le (Nat.succ_le_of_lt hGt)
                | none =>
                  cases srcR? with
                  | none => exact True.intro
                  | some r =>
                    intro x y hx hy
                    rw [hSrcL] at hx; rw [hSrcR] at hy
                    injection hx with hxEq; injection hy with hyEq
                    subst hxEq; subst hyEq
                    exact hLeNat b2.toNat b1.toNat

private theorem noOverflowAdd_lt {w x y : Nat} {a1 a2 : AbsVal}
    (hOk : AbsVal.noOverflowAdd w a1 a2 = true)
    (ha1 : a1.denote w (some x)) (ha2 : a2.denote w (some y)) :
    x + y < modPow2 w := by
  cases absVal_noOverflowAdd_sound hOk ha1 ha2 with
  | intro x' hx =>
    cases hx with | intro y' hxy =>
    injection hxy.1 with hxEq
    injection hxy.2.1 with hyEq
    rw [hxEq, hyEq]
    exact hxy.2.2.1

private theorem noUnderflowSub_le {w x y : Nat} {a1 a2 : AbsVal}
    (hOk : AbsVal.noUnderflowSub w a1 a2 = true)
    (ha1 : a1.denote w (some x)) (ha2 : a2.denote w (some y)) :
    y ≤ x := by
  cases absVal_noUnderflowSub_sound hOk ha1 ha2 with
  | intro x' hx =>
    cases hx with | intro y' hxy =>
    injection hxy.1 with hxEq
    injection hxy.2.1 with hyEq
    rw [hxEq, hyEq]
    exact hxy.2.2.1

private theorem shiftInBounds_lt {w rhsW y : Nat} {b : AbsVal}
    (hOk : AbsVal.shiftInBounds w rhsW b = true)
    (hb : b.denote rhsW (some y)) :
    y < w := by
  cases absVal_shiftInBounds_sound hOk hb with
  | intro y' hy =>
    injection hy.1 with hyEq
    rw [hyEq]
    exact hy.2.1

private theorem nonzeroDiv_pos {w y : Nat} {b : AbsVal}
    (hOk : AbsVal.nonzeroDiv w b = true)
    (hb : b.denote w (some y)) :
    0 < y := by
  cases absVal_nonzeroDiv_sound hOk hb with
  | intro y' hy =>
    injection hy.1 with hyEq
    rw [hyEq]
    exact hy.2.1

/-- Soundness of `evalRvalueAbs` against `Trusted.MirSemantics.evalRvalue`. -/
theorem evalRvalueAbs_sound {bodyLocals : List MirTy} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {mem : MemoryState} {dstTy : MirTy}
    {rv : Rvalue} {resSlot : MirAbsSlot}
    (hEnv : mirAbsEnvDenote bodyLocals env locals)
    (hAbs : evalRvalueAbs bodyLocals env dstTy rv = some (resSlot, env')) :
    ∃ v locals',
      evalRvalue bodyLocals locals mem dstTy rv = .ok (v, locals', mem) ∧
      checkVal v dstTy = true ∧
      resSlot.denote dstTy locals' (.immediate (some v)) ∧
      mirAbsEnvDenote bodyLocals env' locals' := by
  cases rv with
  | use opnd =>
    dsimp only [evalRvalueAbs] at hAbs
    cases hOp : evalOperandAbs bodyLocals env opnd with
    | none => rw [hOp] at hAbs; nomatch hAbs
    | some p =>
      cases p with | mk av env₁ =>
      rw [hOp] at hAbs
      dsimp only at hAbs
      cases hTyEqB : mirTySupportedBeq av.mirTy dstTy with
      | false => rw [hTyEqB] at hAbs; nomatch hAbs
      | true =>
        rw [hTyEqB] at hAbs
        injection hAbs with hPair
        have hSlotEq : resSlot = av.toSlot := congrArg Prod.fst hPair.symm
        have hEnvEq : env' = env₁ := congrArg Prod.snd hPair.symm
        subst hSlotEq; subst hEnvEq
        have hTyEq := mirTy_eq_of_supportedBeq hTyEqB
        have hTyRefl : MirTy.beq dstTy dstTy = true :=
          mirTy_beq_refl_supported (by rw [hTyEq] at hTyEqB; exact hTyEqB)
        cases evalOperandAbs_sound (mem := mem)
            (tyOk := fun srcTy => MirTy.beq srcTy dstTy) hEnv hOp with
        | intro v hv =>
          cases hv with | intro locals₁ hR =>
          refine ⟨v, locals₁, ?_, ?_, ?_, hR.2.2⟩
          · dsimp only [evalRvalue]
            rw [hR.1]
            dsimp only
            have hNotB : (!MirTy.beq av.mirTy dstTy) = false := by
              rw [hTyEq, hTyRefl]; rfl
            rw [ite_bool_false_t hNotB]
          · cases av with
            | uint w a _ =>
              dsimp only [MirAbsVal.mirTy] at hTyEq
              subst hTyEq
              cases v with
              | scalar sv =>
                have hW := hR.2.1.2.2.1
                have hS := hR.2.1.2.2.2.1
                have hLt := hR.2.1.2.2.2.2.1
                cases sv with
                | mk sw ss sb =>
                  dsimp only at hW hS hLt
                  subst hW; subst hS
                  exact checkVal_uint_of_lt hLt
              | _ => exact False.elim hR.2.1.2.2
            | bool ba =>
              dsimp only [MirAbsVal.mirTy] at hTyEq
              subst hTyEq
              cases v with
              | bool _ => rfl
              | _ => exact False.elim hR.2.1.2
            | unit =>
              dsimp only [MirAbsVal.mirTy] at hTyEq
              subst hTyEq
              rw [hR.2.1.2]; rfl
          · cases av with
            | uint w a _ =>
              dsimp only [MirAbsVal.mirTy] at hTyEq
              subst hTyEq
              cases v with
              | scalar sv =>
                exact ⟨rfl, hR.2.1.2.2.1, hR.2.1.2.2.2.1, hR.2.1.2.2.2.2.1,
                  hR.2.1.2.2.2.2.2.1⟩
              | _ => exact False.elim hR.2.1.2.2
            | bool ba =>
              dsimp only [MirAbsVal.mirTy] at hTyEq
              subst hTyEq
              cases v with
              | bool bv => exact ⟨rfl, hR.2.1.2⟩
              | _ => exact False.elim hR.2.1.2
            | unit =>
              dsimp only [MirAbsVal.mirTy] at hTyEq
              subst hTyEq
              exact ⟨rfl, congrArg (fun x => LocalSlot.immediate (some x)) hR.2.1.2⟩
  | unaryOp uop opnd =>
    cases uop with
    | neg | ptrMetadata => nomatch hAbs
    | not =>
      dsimp only [evalRvalueAbs] at hAbs
      cases hOp : evalOperandAbs bodyLocals env opnd with
      | none => rw [hOp] at hAbs; nomatch hAbs
      | some p =>
        cases p with | mk av env₁ =>
        rw [hOp] at hAbs
        cases av with
        | uint _ _ _ | unit => nomatch hAbs
        | bool ba =>
          dsimp only at hAbs
          cases hTyB : mirTySupportedBeq .bool dstTy with
          | false => rw [hTyB] at hAbs; nomatch hAbs
          | true =>
            rw [hTyB] at hAbs
            have hDst : dstTy = .bool := (mirTy_eq_of_supportedBeq hTyB).symm
            subst hDst
            injection hAbs with hPair
            have hSlotEq := congrArg Prod.fst hPair.symm
            have hEnvEq : env' = env₁ := congrArg Prod.snd hPair.symm
            subst hSlotEq; subst hEnvEq
            cases evalOperandAbs_primitive_sound (mem := mem) hEnv hOp rfl with
            | intro v hv =>
              cases hv with | intro locals₁ hR =>
              cases v with
              | bool bv =>
                refine ⟨.bool (!bv), locals₁, ?_, rfl, ?_, hR.2.2⟩
                · dsimp only [evalRvalue]
                  rw [hR.1]
                  rfl
                · refine ⟨rfl, ?_⟩
                  cases ba with
                  | bot => exact False.elim hR.2.1.2
                  | uninit => exact True.intro
                  | top g => exact relGuard_negate_sound hR.2.1.2
                  | exact ev g =>
                    exact ⟨bool_not_eq_of_eq hR.2.1.2.1,
                      relGuard_negate_sound hR.2.1.2.2⟩
              | scalar _ | ptr _ | char _ | ordering _ | unit
              | enumVal _ _ | tuple _ | bytes _ =>
                exact False.elim hR.2.1.2
  | cast ck opnd castTy =>
    cases ck with
    | unsupported => nomatch hAbs
    | intToInt =>
      cases castTy with
      | int wDst sg =>
        cases sg with
        | true => nomatch hAbs
        | false =>
          dsimp only [evalRvalueAbs] at hAbs
          cases hTyB : mirTySupportedBeq (.int wDst false) dstTy with
          | false => rw [hTyB] at hAbs; nomatch hAbs
          | true =>
            rw [hTyB] at hAbs
            have hDst := (mirTy_eq_of_supportedBeq hTyB).symm
            subst hDst
            cases hOp : evalOperandAbs bodyLocals env opnd with
            | none => rw [hOp] at hAbs; nomatch hAbs
            | some p =>
              cases p with | mk av env₁ =>
              rw [hOp] at hAbs
              cases av with
              | bool _ | unit => nomatch hAbs
              | uint wSrc a srcR? =>
                injection hAbs with hPair
                have hSlotEq := congrArg Prod.fst hPair.symm
                have hEnvEq : env' = env₁ := congrArg Prod.snd hPair.symm
                subst hSlotEq; subst hEnvEq
                cases evalOperandAbs_sound (mem := mem) (tyOk := isIntLikeTy)
                    hEnv hOp with
                | intro v hv =>
                  cases hv with | intro locals₁ hR =>
                  cases v with
                  | scalar sv =>
                    cases sv with | mk sw ss sb =>
                    have hW : sw = wSrc := hR.2.1.2.2.1
                    have hS : ss = false := hR.2.1.2.2.2.1
                    have hLt := hR.2.1.2.2.2.2.1
                    have ha := hR.2.1.2.2.2.2.2.1
                    dsimp only at hLt ha
                    subst sw; subst ss
                    have hResLt : wrapVal (bitWidthComp wDst) sb.toNat <
                        modPow2 (bitWidthComp wDst) :=
                      nat_mod_lt sb.toNat (modPow2_pos (bitWidthComp wDst))
                    have hRes128 : wrapVal (bitWidthComp wDst) sb.toNat <
                        Nat.pow 2 128 :=
                      Nat.lt_of_lt_of_le hResLt (modPow2_bitWidth_le_128 wDst)
                    have hToNat :
                        (BitVec.ofNat 128 (wrapVal (bitWidthComp wDst) sb.toNat)).toNat =
                          wrapVal (bitWidthComp wDst) sb.toNat :=
                      bitVec_toNat_ofNat_lt hRes128
                    refine ⟨.scalar ⟨wDst, false,
                      BitVec.ofNat 128 (wrapVal (bitWidthComp wDst) sb.toNat)⟩,
                      locals₁, ?_, ?_, ?_, hR.2.2⟩
                    · dsimp only [evalRvalue]
                      rw [hR.1]
                      dsimp only [MirAbsVal.mirTy]
                      rw [ite_bool_false_t (c := !isIntLikeTy (.int wSrc false)) rfl]
                      rw [evalIntToIntCast_uint hLt]
                    · apply checkVal_uint_of_lt
                      rw [hToNat]; exact hResLt
                    · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
                      · rw [hToNat]; exact hResLt
                      · rw [hToNat]; exact castUintAbs_sound ha hLt
                  | ptr _ | bool _ | char _ | ordering _ | unit
                  | enumVal _ _ | tuple _ | bytes _ =>
                    exact False.elim hR.2.1.2.2
      | unit | bool | char | rawPtr _ _ | ref _ _ | tuple _ | enum _
      | ordering | never | unsupported => nomatch hAbs
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalueAbs] at hAbs
    cases hOp1 : evalOperandAbs bodyLocals env lhs with
    | none => rw [hOp1] at hAbs; nomatch hAbs
    | some p1 =>
      cases p1 with | mk av1 env₁ =>
      rw [hOp1] at hAbs
      cases av1 with
      | bool _ | unit => nomatch hAbs
      | uint w1 a1 srcL? =>
        dsimp only at hAbs
        cases hOp2 : evalOperandAbs bodyLocals env₁ rhs with
        | none => rw [hOp2] at hAbs; nomatch hAbs
        | some p2 =>
          cases p2 with | mk av2 env₂ =>
          rw [hOp2] at hAbs
          cases av2 with
          | bool _ | unit => nomatch hAbs
          | uint w2 a2 srcR? =>
            cases evalOperandAbs_primitive_sound (mem := mem) hEnv hOp1 rfl with
            | intro v1 hv1 =>
              cases hv1 with | intro locals₁ hR1 =>
              cases evalOperandAbs_primitive_sound (mem := mem) hR1.2.2 hOp2 rfl with
              | intro v2 hv2 =>
                cases hv2 with | intro locals₂ hR2 =>
                cases v1 with
                | scalar sv1 =>
                  cases v2 with
                  | scalar sv2 =>
                    cases sv1 with | mk sw1 ss1 sb1 =>
                    cases sv2 with | mk sw2 ss2 sb2 =>
                    have hInit1 := hR1.2.1.2.1
                    have hW1 : sw1 = w1 := hR1.2.1.2.2.1
                    have hS1 : ss1 = false := hR1.2.1.2.2.2.1
                    have hLt1 := hR1.2.1.2.2.2.2.1
                    have ha1 := hR1.2.1.2.2.2.2.2.1
                    have hSrcL := hR1.2.1.2.2.2.2.2.2
                    have hInit2 := hR2.2.1.2.1
                    have hW2 : sw2 = w2 := hR2.2.1.2.2.1
                    have hS2 : ss2 = false := hR2.2.1.2.2.2.1
                    have hLt2 := hR2.2.1.2.2.2.2.1
                    have ha2 := hR2.2.1.2.2.2.2.2.1
                    have hSrcR := hR2.2.1.2.2.2.2.2.2
                    dsimp only at hLt1 ha1 hSrcL hLt2 ha2 hSrcR
                    subst sw1; subst ss1; subst sw2; subst ss2
                    have hWrapFinish :
                        ∀ (n : Nat) (aRes : AbsVal),
                          n < modPow2 (bitWidthComp w1) →
                          aRes.denote (bitWidthComp w1) (some n) →
                          evalBinOp op (.scalar ⟨w1, false, sb1⟩)
                            (.scalar ⟨w2, false, sb2⟩) =
                            .ok (.scalar ⟨w1, false, BitVec.ofNat 128 n⟩) →
                          dstTy = .int w1 false →
                          resSlot = .uint w1 aRes →
                          env' = env₂ →
                          ∃ v locals',
                            evalRvalue bodyLocals locals mem dstTy
                              (.binaryOp op lhs rhs) = .ok (v, locals', mem) ∧
                            checkVal v dstTy = true ∧
                            resSlot.denote dstTy locals' (.immediate (some v)) ∧
                            mirAbsEnvDenote bodyLocals env' locals' := by
                      intro n aRes hNlt hADen hBin hDst hSl hEn
                      subst hDst; subst hSl; subst hEn
                      have hN128 : n < Nat.pow 2 128 :=
                        Nat.lt_of_lt_of_le hNlt (modPow2_bitWidth_le_128 w1)
                      have hToNat : (BitVec.ofNat 128 n).toNat = n :=
                        bitVec_toNat_ofNat_lt hN128
                      refine ⟨.scalar ⟨w1, false, BitVec.ofNat 128 n⟩,
                        locals₂, ?_, ?_, ?_, hR2.2.2⟩
                      · dsimp only [evalRvalue]
                        rw [hR1.1]
                        dsimp only
                        rw [hR2.1]
                        dsimp only
                        rw [hBin]
                      · apply checkVal_uint_of_lt; rw [hToNat]; exact hNlt
                      · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
                        · rw [hToNat]; exact hNlt
                        · rw [hToNat]; exact hADen
                    cases op with
                    | add =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right hC)).symm
                        subst hwEq
                        injection hAbs with hPair
                        exact hWrapFinish _ _
                          (nat_mod_lt _ (modPow2_pos _))
                          (absVal_addWrap_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_add hLt1 hLt2)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | addUnchecked =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy &&
                          AbsVal.noOverflowAdd (bitWidthComp w1) a1 a2 with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have h12 := bool_and_true_left hC
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left h12)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right h12)).symm
                        have hNoOv := bool_and_true_right hC
                        subst hwEq
                        injection hAbs with hPair
                        exact hWrapFinish _ _
                          (nat_mod_lt _ (modPow2_pos _))
                          (absVal_addWrap_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_addUnchecked hLt1 hLt2
                            (noOverflowAdd_lt hNoOv ha1 ha2))
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | sub =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right hC)).symm
                        subst hwEq
                        injection hAbs with hPair
                        exact hWrapFinish _ _
                          (nat_mod_lt _ (modPow2_pos _))
                          (absVal_subWrap_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_sub hLt1 hLt2)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | subUnchecked =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy &&
                          AbsVal.noUnderflowSub (bitWidthComp w1) a1 a2 with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have h12 := bool_and_true_left hC
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left h12)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right h12)).symm
                        have hNoU := bool_and_true_right hC
                        subst hwEq
                        injection hAbs with hPair
                        exact hWrapFinish _ _
                          (nat_mod_lt _ (modPow2_pos _))
                          (absVal_subWrap_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_subUnchecked hLt1 hLt2
                            (noUnderflowSub_le hNoU ha1 ha2))
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | bitAnd =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right hC)).symm
                        subst hwEq
                        injection hAbs with hPair
                        have hLtAnd : Nat.land sb1.toNat sb2.toNat <
                            modPow2 (bitWidthComp w1) :=
                          lt_modPow2_of_bitAt_zero (fun k hk => by
                            rw [bitAt_land, bitAt_zero_ge_of_lt_modPow2 hLt1 k hk]; rfl)
                        exact hWrapFinish _ _ hLtAnd
                          (absVal_bitAnd_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_bitAnd hLt1 hLt2)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | bitOr =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right hC)).symm
                        subst hwEq
                        injection hAbs with hPair
                        have hLtOr : Nat.lor sb1.toNat sb2.toNat <
                            modPow2 (bitWidthComp w1) :=
                          lt_modPow2_of_bitAt_zero (fun k hk => by
                            rw [bitAt_lor, bitAt_zero_ge_of_lt_modPow2 hLt1 k hk,
                                bitAt_zero_ge_of_lt_modPow2 hLt2 k hk]; rfl)
                        exact hWrapFinish _ _ hLtOr
                          (absVal_bitOr_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_bitOr hLt1 hLt2)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | bitXor =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right hC)).symm
                        subst hwEq
                        injection hAbs with hPair
                        have hLtXor : Nat.xor sb1.toNat sb2.toNat <
                            modPow2 (bitWidthComp w1) :=
                          lt_modPow2_of_bitAt_zero (fun k hk => by
                            rw [bitAt_xor, bitAt_zero_ge_of_lt_modPow2 hLt1 k hk,
                                bitAt_zero_ge_of_lt_modPow2 hLt2 k hk]; rfl)
                        exact hWrapFinish _ _ hLtXor
                          (absVal_bitXor_sound (bitWidthComp_valid w1) ha1 ha2 hInit1 hInit2)
                          (evalBinOp_uint_bitXor hLt1 hLt2)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | shl =>
                      dsimp only at hAbs
                      cases hC : mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hDst := (mirTy_eq_of_supportedBeq hC).symm
                        cases hEx : a2.exactVal? (bitWidthComp w2) with
                        | none =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          exact hWrapFinish _ _ (nat_mod_lt _ (modPow2_pos _))
                            (absVal_topInit_sound (nat_mod_lt _ (modPow2_pos _)))
                            (evalBinOp_uint_shl hLt1 hLt2)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                        | some k =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          have hkEq := absVal_exactVal?_eq hEx ha2
                          have hShlDen : (AbsVal.shlConst (bitWidthComp w1)
                              (Nat.mod k (bitWidthComp w1)) a1).denote (bitWidthComp w1)
                              (some (wrapVal (bitWidthComp w1)
                                (Nat.shiftLeft sb1.toNat
                                  (Nat.mod sb2.toNat (bitWidthComp w1))))) := by
                            rw [hkEq]
                            exact absVal_shlConst_sound (bitWidthComp_valid w1) ha1 hInit1
                          exact hWrapFinish _ _ (nat_mod_lt _ (modPow2_pos _))
                            hShlDen (evalBinOp_uint_shl hLt1 hLt2)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                    | shlUnchecked =>
                      dsimp only at hAbs
                      cases hC : mirTySupportedBeq (.int w1 false) dstTy &&
                          AbsVal.shiftInBounds (bitWidthComp w1) (bitWidthComp w2) a2 with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_left hC)).symm
                        have hInB := shiftInBounds_lt (bool_and_true_right hC) ha2
                        cases hEx : a2.exactVal? (bitWidthComp w2) with
                        | none =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          exact hWrapFinish _ _ (nat_mod_lt _ (modPow2_pos _))
                            (absVal_topInit_sound (nat_mod_lt _ (modPow2_pos _)))
                            (evalBinOp_uint_shlUnchecked hLt1 hLt2 hInB)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                        | some k =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          have hkEq := absVal_exactVal?_eq hEx ha2
                          have hShlDen : (AbsVal.shlConst (bitWidthComp w1) k a1).denote
                              (bitWidthComp w1)
                              (some (wrapVal (bitWidthComp w1)
                                (Nat.shiftLeft sb1.toNat sb2.toNat))) := by
                            rw [hkEq]
                            exact absVal_shlConst_sound (bitWidthComp_valid w1) ha1 hInit1
                          exact hWrapFinish _ _ (nat_mod_lt _ (modPow2_pos _))
                            hShlDen (evalBinOp_uint_shlUnchecked hLt1 hLt2 hInB)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                    | shr =>
                      dsimp only at hAbs
                      cases hC : mirTySupportedBeq (.int w1 false) dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hDst := (mirTy_eq_of_supportedBeq hC).symm
                        have hLtShr :
                            Nat.shiftRight sb1.toNat (Nat.mod sb2.toNat (bitWidthComp w1)) <
                              modPow2 (bitWidthComp w1) :=
                          lt_modPow2_of_bitAt_zero (fun k hk => by
                            rw [bitAt_shiftRight]
                            exact bitAt_zero_ge_of_lt_modPow2 hLt1 _
                              (Nat.le_trans hk (Nat.le_add_right _ _)))
                        cases hEx : a2.exactVal? (bitWidthComp w2) with
                        | none =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          exact hWrapFinish _ _ hLtShr
                            (absVal_topInit_sound hLtShr)
                            (evalBinOp_uint_shr hLt1 hLt2)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                        | some k =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          have hkEq := absVal_exactVal?_eq hEx ha2
                          have hShrDen : (AbsVal.shrConst (bitWidthComp w1)
                              (Nat.mod k (bitWidthComp w1)) a1).denote (bitWidthComp w1)
                              (some (Nat.shiftRight sb1.toNat
                                (Nat.mod sb2.toNat (bitWidthComp w1)))) := by
                            rw [hkEq]
                            exact absVal_shrConst_sound (bitWidthComp_valid w1) ha1 hInit1
                          exact hWrapFinish _ _ hLtShr
                            hShrDen (evalBinOp_uint_shr hLt1 hLt2)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                    | shrUnchecked =>
                      dsimp only at hAbs
                      cases hC : mirTySupportedBeq (.int w1 false) dstTy &&
                          AbsVal.shiftInBounds (bitWidthComp w1) (bitWidthComp w2) a2 with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_left hC)).symm
                        have hInB := shiftInBounds_lt (bool_and_true_right hC) ha2
                        have hLtShr : Nat.shiftRight sb1.toNat sb2.toNat <
                            modPow2 (bitWidthComp w1) :=
                          lt_modPow2_of_bitAt_zero (fun k hk => by
                            rw [bitAt_shiftRight]
                            exact bitAt_zero_ge_of_lt_modPow2 hLt1 _
                              (Nat.le_trans hk (Nat.le_add_right _ _)))
                        cases hEx : a2.exactVal? (bitWidthComp w2) with
                        | none =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          exact hWrapFinish _ _ hLtShr
                            (absVal_topInit_sound hLtShr)
                            (evalBinOp_uint_shrUnchecked hLt1 hLt2 hInB)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                        | some k =>
                          rw [hEx] at hAbs
                          injection hAbs with hPair
                          have hkEq := absVal_exactVal?_eq hEx ha2
                          have hShrDen : (AbsVal.shrConst (bitWidthComp w1) k a1).denote
                              (bitWidthComp w1)
                              (some (Nat.shiftRight sb1.toNat sb2.toNat)) := by
                            rw [hkEq]
                            exact absVal_shrConst_sound (bitWidthComp_valid w1) ha1 hInit1
                          exact hWrapFinish _ _ hLtShr
                            hShrDen (evalBinOp_uint_shrUnchecked hLt1 hLt2 hInB)
                            hDst (congrArg Prod.fst hPair.symm)
                            (congrArg Prod.snd hPair.symm)
                    | div =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy &&
                          AbsVal.nonzeroDiv (bitWidthComp w1) a2 with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have h12 := bool_and_true_left hC
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left h12)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right h12)).symm
                        subst hwEq
                        have hPos := nonzeroDiv_pos (bool_and_true_right hC) ha2
                        injection hAbs with hPair
                        have hLtDiv : Nat.div sb1.toNat sb2.toNat < modPow2 (bitWidthComp w1) :=
                          Nat.lt_of_le_of_lt (Nat.div_le_self sb1.toNat sb2.toNat) hLt1
                        exact hWrapFinish _ _ hLtDiv
                          (absVal_topInit_sound hLtDiv)
                          (evalBinOp_uint_div hLt1 hLt2 hPos)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | rem =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq (.int w1 false) dstTy &&
                          AbsVal.nonzeroDiv (bitWidthComp w1) a2 with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have h12 := bool_and_true_left hC
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left h12)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right h12)).symm
                        subst hwEq
                        have hPos := nonzeroDiv_pos (bool_and_true_right hC) ha2
                        injection hAbs with hPair
                        have hLtRem : Nat.mod sb1.toNat sb2.toNat < modPow2 (bitWidthComp w1) :=
                          Nat.lt_trans (nat_mod_lt sb1.toNat hPos) hLt2
                        exact hWrapFinish _ _ hLtRem
                          (absVal_topInit_sound hLtRem)
                          (evalBinOp_uint_rem hLt1 hLt2 hPos)
                          hDst (congrArg Prod.fst hPair.symm)
                          (congrArg Prod.snd hPair.symm)
                    | eq | ne | lt | le | gt | ge =>
                      dsimp only at hAbs
                      cases hC : intWidthBeqComp w1 w2 &&
                          mirTySupportedBeq .bool dstTy with
                      | false => rw [hC] at hAbs; nomatch hAbs
                      | true =>
                        rw [hC] at hAbs
                        have hwEq := intWidth_eq_of_beqComp (bool_and_true_left hC)
                        have hDst := (mirTy_eq_of_supportedBeq (bool_and_true_right hC)).symm
                        subst hwEq; subst hDst
                        injection hAbs with hPair
                        injection hPair with hSl hEn
                        subst resSlot; subst env'
                        have hCmpGo :
                            ∀ (opC : BinOp),
                              (opC = .eq ∨ opC = .ne ∨ opC = .lt ∨
                               opC = .le ∨ opC = .gt ∨ opC = .ge) →
                              ∃ v locals',
                                evalRvalue bodyLocals locals mem .bool
                                  (.binaryOp opC lhs rhs) = .ok (v, locals', mem) ∧
                                checkVal v .bool = true ∧
                                MirAbsSlot.denote .bool locals'
                                  (.bool (mkBoolAbs (decideCmpAbs opC (bitWidthComp w1) a1 a2)
                                    (if operandIsPure lhs && operandIsPure rhs then
                                      synthCmpGuard opC w1 srcL? srcR? a1 a2
                                     else .none)))
                                  (.immediate (some v)) ∧
                                mirAbsEnvDenote bodyLocals env₂ locals' := by
                          intro opC hCmpTag
                          cases hPure : operandIsPure lhs && operandIsPure rhs with
                          | true =>
                            have hLoc2Eq : locals₂ = locals₁ :=
                              evalOperandAbs_pure_locals_eq
                                (bool_and_true_right hPure) hR2.1 hOp2
                            rw [← hLoc2Eq] at hSrcL
                            cases evalCmp_bool_sound (op := opC) (srcL? := srcL?) (srcR? := srcR?)
                                hLt1 hLt2 ha1 ha2 hSrcL hSrcR hCmpTag with
                            | intro resB hB =>
                              refine ⟨.bool resB, locals₂, ?_, rfl, ⟨rfl, ?_⟩, hR2.2.2⟩
                              · dsimp only [evalRvalue]
                                rw [hR1.1]; dsimp only; rw [hR2.1]; dsimp only; rw [hB.1]
                              · rw [ite_bool_true_t (c := true) rfl]; exact hB.2.1
                          | false =>
                            cases evalCmp_bool_sound (op := opC) (srcL? := none) (srcR? := srcR?)
                                hLt1 hLt2 ha1 ha2 True.intro hSrcR hCmpTag with
                            | intro resB hB =>
                              refine ⟨.bool resB, locals₂, ?_, rfl, ⟨rfl, ?_⟩, hR2.2.2⟩
                              · dsimp only [evalRvalue]
                                rw [hR1.1]; dsimp only; rw [hR2.1]; dsimp only; rw [hB.1]
                              · rw [ite_bool_false_t (c := false) rfl]; exact hB.2.2
                        first
                        | exact hCmpGo .eq (Or.inl rfl)
                        | exact hCmpGo .ne (Or.inr (Or.inl rfl))
                        | exact hCmpGo .lt (Or.inr (Or.inr (Or.inl rfl)))
                        | exact hCmpGo .le (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                        | exact hCmpGo .gt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                        | exact hCmpGo .ge (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
                    | mul | mulUnchecked | addWithOverflow | subWithOverflow
                    | mulWithOverflow | cmp | offset => nomatch hAbs
                  | ptr _ | bool _ | char _ | ordering _ | unit
                  | enumVal _ _ | tuple _ | bytes _ =>
                    exact False.elim hR2.2.1.2.2
                | ptr _ | bool _ | char _ | ordering _ | unit
                | enumVal _ _ | tuple _ | bytes _ =>
                  exact False.elim hR1.2.1.2.2
  | ref _ _ | addressOf _ _ | aggregateTuple _ | discriminant _
  | unsupported => nomatch hAbs

/-! ## 3. Single-Step Statement & Terminator Abstract Transfer -/

/-- Abstract transfer for a single MIR statement. -/
@[expose] def stepStmtAbs (bodyLocals : List MirTy) (env : MirAbsEnv) :
    StatementKind → Option MirAbsEnv
  | .nop => some env
  | .storageLive localId =>
    match compGetElem? bodyLocals localId, compGetElem? env localId with
    | some ty, some _ =>
      match liveUninitAbsSlot? ty with
      | some slot => setMirAbsSlot localId slot env
      | none => none
    | _, _ => none
  | .storageDead localId =>
    if Nat.beq localId 0 then none
    else
      match compGetElem? env localId with
      | some _ => setMirAbsSlot localId .dead env
      | none => none
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else
      match compGetElem? bodyLocals dst.localId with
      | none => none
      | some dstTy =>
        match evalRvalueAbs bodyLocals env dstTy rv with
        | none => none
        | some (newSlot, envAfterRval) =>
          match compGetElem? envAfterRval dst.localId with
          | some dstSlot =>
            if dstSlot.isLive then setMirAbsSlot dst.localId newSlot envAfterRval
            else none
          | none => none
  | .unsupported => none

private theorem deallocateLocal_nonIndirect (mem : MemoryState)
    {ty : MirTy} {locals : List LocalSlot} {s : MirAbsSlot} {cs : LocalSlot}
    (hDen : s.denote ty locals cs) :
    deallocateLocal mem cs = .ok mem := by
  cases cs with
  | dead => rfl
  | immediate _ => rfl
  | indirect _ =>
    cases s with
    | dead => nomatch hDen
    | unit => nomatch hDen.2
    | uint _ _ => exact False.elim hDen.2
    | bool _ => exact False.elim hDen.2

/-- 1-step soundness of `stepStmtAbs` against `MirSemantics.evalStatement`. -/
theorem stepStmtAbs_sound {body : Body} {frame : FrameState}
    {mem : MemoryState} {callerMem : CallerMemory}
    {env env' : MirAbsEnv} {stmt : StatementKind}
    (hEnv : mirAbsEnvDenote body.locals env frame.locals)
    (hStep : stepStmtAbs body.locals env stmt = some env') :
    ∃ locals',
      evalStatement body frame mem callerMem stmt =
        .step {
          frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals' }]
          callerMem
          mem
        } ∧
      mirAbsEnvDenote body.locals env' locals' := by
  cases stmt with
  | unsupported => nomatch hStep
  | nop =>
    injection hStep with hEq; subst hEq
    exact ⟨frame.locals, rfl, hEnv⟩
  | storageLive localId =>
    dsimp only [stepStmtAbs] at hStep
    cases hTy : compGetElem? body.locals localId with
    | none => rw [hTy] at hStep; nomatch hStep
    | some ty =>
      cases hS : compGetElem? env localId with
      | none => rw [hTy, hS] at hStep; nomatch hStep
      | some oldS =>
        rw [hTy, hS] at hStep
        dsimp only at hStep
        cases hU : liveUninitAbsSlot? ty with
        | none => rw [hU] at hStep; nomatch hStep
        | some slot =>
          rw [hU] at hStep
          have hExCs := compGetElem?_exists_of_len_t frame.locals body.locals
            localId ty hEnv.2.1 hTy
          cases hExCs with | intro oldCs hOldCs =>
          have hOldDen := hEnv.2.2 localId ty oldS oldCs hTy hS hOldCs
          have hDealloc := deallocateLocal_nonIndirect mem hOldDen
          cases compSetElem?_exists_of_get frame.locals localId
              (liveUninitSlot ty) hOldCs with
          | intro locals' hSetConc =>
            have hNewDen : slot.denote ty locals' (liveUninitSlot ty) := by
              cases ty with
              | int w sg =>
                cases sg with
                | true => nomatch hU
                | false =>
                  injection hU with hEq; subst hEq
                  exact ⟨rfl, absVal_uninit_sound_none⟩
              | bool =>
                injection hU with hEq; subst hEq
                exact ⟨rfl, True.intro⟩
              | unit =>
                injection hU with hEq; subst hEq
                exact ⟨rfl, rfl⟩
              | char | rawPtr _ _ | ref _ _ | tuple _ | enum _
              | ordering | never | unsupported => nomatch hU
            have hEnv' := setMirAbsSlot_sound hEnv hTy hStep hSetConc hNewDen
            refine ⟨locals', ?_, hEnv'⟩
            dsimp only [evalStatement]
            rw [← compGetElem?_eq, hTy, ← compGetElem?_eq, hOldCs]
            dsimp only
            rw [← compSetElem?_eq, hSetConc]
            dsimp only
            rw [hDealloc]
  | storageDead localId =>
    dsimp only [stepStmtAbs] at hStep
    cases hZ : Nat.beq localId 0 with
    | true => rw [hZ] at hStep; nomatch hStep
    | false =>
      rw [hZ] at hStep
      cases hS : compGetElem? env localId with
      | none => rw [hS] at hStep; nomatch hStep
      | some oldS =>
        rw [hS] at hStep
        have hExTy := compGetElem?_exists_of_len_t body.locals env
          localId oldS hEnv.1.symm hS
        cases hExTy with | intro ty hTy =>
        have hExCs := compGetElem?_exists_of_len_t frame.locals body.locals
          localId ty hEnv.2.1 hTy
        cases hExCs with | intro oldCs hOldCs =>
        have hOldDen := hEnv.2.2 localId ty oldS oldCs hTy hS hOldCs
        have hDealloc := deallocateLocal_nonIndirect mem hOldDen
        cases compSetElem?_exists_of_get frame.locals localId .dead hOldCs with
        | intro locals' hSetConc =>
          have hEnv' := setMirAbsSlot_sound hEnv hTy hStep hSetConc rfl
          refine ⟨locals', ?_, hEnv'⟩
          dsimp only [evalStatement]
          rw [ite_bool_false_t hZ, ← compGetElem?_eq, hOldCs,
              ← compSetElem?_eq, hSetConc]
          dsimp only
          rw [hDealloc]
  | assign dst rv =>
    dsimp only [stepStmtAbs] at hStep
    cases hProj : dst.projection.isEmpty with
    | false => rw [hProj] at hStep; nomatch hStep
    | true =>
      rw [ite_bool_false_t (c := !dst.projection.isEmpty) (by rw [hProj]; rfl)] at hStep
      cases hTy : compGetElem? body.locals dst.localId with
      | none => rw [hTy] at hStep; nomatch hStep
      | some dstTy =>
        rw [hTy] at hStep
        dsimp only at hStep
        cases hRv : evalRvalueAbs body.locals env dstTy rv with
        | none => rw [hRv] at hStep; nomatch hStep
        | some p =>
          cases p with | mk newSlot envAfterRval =>
          rw [hRv] at hStep
          dsimp only at hStep
          cases hDstS : compGetElem? envAfterRval dst.localId with
          | none => rw [hDstS] at hStep; nomatch hStep
          | some dstSlot =>
            rw [hDstS] at hStep
            dsimp only at hStep
            cases hLive : dstSlot.isLive with
            | false => rw [hLive] at hStep; nomatch hStep
            | true =>
              rw [hLive] at hStep
              cases evalRvalueAbs_sound (mem := mem) hEnv hRv with
              | intro v hv =>
                cases hv with | intro localsAfterRval hR =>
                have hExDst := compGetElem?_exists_of_len_t localsAfterRval
                  body.locals dst.localId dstTy hR.2.2.2.2.1 hTy
                cases hExDst with | intro oldDst hOldDst =>
                have hDstDen := hR.2.2.2.2.2 dst.localId dstTy dstSlot oldDst
                  hTy hDstS hOldDst
                have hImm : ∃ opt, oldDst = .immediate opt := by
                  cases oldDst with
                  | immediate opt => exact ⟨opt, rfl⟩
                  | dead =>
                    cases dstSlot with
                    | dead => nomatch hLive
                    | uint _ _ | bool _ => exact False.elim hDstDen.2
                    | unit => nomatch hDstDen.2
                  | indirect _ =>
                    cases dstSlot with
                    | dead => nomatch hLive
                    | uint _ _ | bool _ => exact False.elim hDstDen.2
                    | unit => nomatch hDstDen.2
                cases hImm with | intro opt hOldEq =>
                subst hOldEq
                cases compSetElem?_exists_of_get localsAfterRval dst.localId
                    (.immediate (some v)) hOldDst with
                | intro localsAfterWrite hSetConc =>
                  have hWriteDen :
                      newSlot.denote dstTy localsAfterWrite (.immediate (some v)) := by
                    cases newSlot with
                    | dead => exact hR.2.2.1
                    | unit => exact hR.2.2.1
                    | uint _ _ => exact hR.2.2.1
                    | bool ba =>
                      refine ⟨hR.2.2.1.1, ?_⟩
                      cases v with
                      | bool bv =>
                        -- If `newSlot` carries a `RelGuard`, it cannot mention
                        -- `dst.localId` because `dst.localId` has type `bool`
                        -- while `RelGuard` only reads unsigned scalar locals!
                        have hLocalUintSame :
                            ∀ r w, localUintNat? localsAfterWrite r w =
                              localUintNat? localsAfterRval r w := by
                          intro r w
                          cases hEqR : Nat.beq dst.localId r with
                          | false =>
                            have hNe : dst.localId ≠ r := fun hE => by
                              rw [hE, nat_beq_refl r] at hEqR; nomatch hEqR
                            dsimp only [localUintNat?]
                            rw [compGetElem?_setElem_ne hSetConc hNe]
                          | true =>
                            have hEq := Nat.eq_of_beq_eq_true hEqR
                            subst hEq
                            have hDstBool : dstTy = .bool := hR.2.2.1.1
                            subst hDstBool
                            dsimp only [localUintNat?]
                            rw [compGetElem?_setElem_same hSetConc, hOldDst]
                            cases opt with
                            | none => rfl
                            | some ov =>
                              cases ov with
                              | scalar _ =>
                                cases dstSlot with
                                | dead => nomatch hLive
                                | uint _ _ | unit => nomatch hDstDen.1
                                | bool _ => exact False.elim hDstDen.2
                              | ptr _ | bool _ | char _ | ordering _ | unit
                              | enumVal _ _ | tuple _ | bytes _ => rfl
                        have hGuardPres :
                            ∀ (g : RelGuard), g.denote localsAfterRval bv →
                              g.denote localsAfterWrite bv := by
                          intro g hg
                          cases g with
                          | none => exact True.intro
                          | uleConst r w _ | ugtConst r w _
                          | ueqConst r w _ | uneConst r w _ =>
                            intro x hx
                            rw [hLocalUintSame r w] at hx
                            exact hg x hx
                          | ultReg l r w | ugeReg l r w =>
                            intro x y hx hy
                            rw [hLocalUintSame l w] at hx
                            rw [hLocalUintSame r w] at hy
                            exact hg x y hx hy
                        cases ba with
                        | bot => exact False.elim hR.2.2.1.2
                        | uninit => exact True.intro
                        | top g => exact hGuardPres g hR.2.2.1.2
                        | exact ev g =>
                          exact ⟨hR.2.2.1.2.1, hGuardPres g hR.2.2.1.2.2⟩
                      | scalar _ | ptr _ | char _ | ordering _ | unit
                      | enumVal _ _ | tuple _ | bytes _ =>
                        exact False.elim hR.2.2.1.2
                  have hEnv' := setMirAbsSlot_sound hR.2.2.2 hTy hStep hSetConc
                    hWriteDen
                  refine ⟨localsAfterWrite, ?_, hEnv'⟩
                  dsimp only [evalStatement]
                  have hNotProj : (!dst.projection.isEmpty) = false := by
                    rw [hProj]; rfl
                  rw [ite_bool_false_t hNotProj, ← compGetElem?_eq, hTy]
                  dsimp only
                  rw [hR.1]
                  dsimp only [writePlace]
                  have hNotChk : (!checkVal v dstTy) = false := by
                    rw [hR.2.1]; rfl
                  rw [ite_bool_false_t hNotChk, ← compGetElem?_eq, hOldDst]
                  dsimp only
                  rw [← compSetElem?_eq, hSetConc]

/-- Evaluates a `SwitchTargets` branch list on a concrete `Bool` value,
failing closed (`none`) on any out-of-range case constant (`> 1`) reached
before the first matching branch (matching
`Trusted.MirSemantics.evalBoolSwitchBranches`). -/
@[expose] def evalBoolSwitchTarget (discr : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) : Option BasicBlockId :=
  branches.foldr
    (fun p ih =>
      if Nat.beq p.1.toNat 0 then
        if !discr then some p.2 else ih
      else if Nat.beq p.1.toNat 1 then
        if discr then some p.2 else ih
      else
        none)
    (some otherwise)

private theorem evalBoolSwitchTarget_cons (discr : Bool)
    (otherwise : BasicBlockId) (caseBits : BitVec 128) (target : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId)) :
    evalBoolSwitchTarget discr otherwise ((caseBits, target) :: rest) =
      if Nat.beq caseBits.toNat 0 then
        if !discr then some target else evalBoolSwitchTarget discr otherwise rest
      else if Nat.beq caseBits.toNat 1 then
        if discr then some target else evalBoolSwitchTarget discr otherwise rest
      else
        none := rfl

private theorem evalBoolSwitchTarget_sound {discr : Bool}
    {otherwise target : BasicBlockId} {branches : List (BitVec 128 × BasicBlockId)}
    (h : evalBoolSwitchTarget discr otherwise branches = some target) :
    evalBoolSwitchBranches discr otherwise branches = .ok target := by
  induction branches with
  | nil =>
    injection h with hEq; subst hEq; rfl
  | cons hd rest ih =>
    cases hd with | mk caseBits tgt =>
    rw [evalBoolSwitchTarget_cons] at h
    cases hZ : Nat.beq caseBits.toNat 0 with
    | true =>
      rw [hZ] at h
      have hB0 : caseBits = BitVec.ofNat 128 0 := by
        have h1 := bitVec128_ofNat_toNat caseBits
        rw [Nat.eq_of_beq_eq_true hZ] at h1
        exact h1.symm
      subst hB0
      dsimp only [evalBoolSwitchBranches]
      cases discr with
      | false =>
        injection h with hEq; subst hEq; rfl
      | true =>
        exact ih h
    | false =>
      rw [hZ] at h
      cases hO : Nat.beq caseBits.toNat 1 with
      | false => rw [hO] at h; nomatch h
      | true =>
        rw [hO] at h
        have hB1 : caseBits = BitVec.ofNat 128 1 := by
          have h1 := bitVec128_ofNat_toNat caseBits
          rw [Nat.eq_of_beq_eq_true hO] at h1
          exact h1.symm
        subst hB1
        dsimp only [evalBoolSwitchBranches]
        cases discr with
        | true =>
          injection h with hEq; subst hEq; rfl
        | false =>
          exact ih h

/-- Abstract `switchInt` successor computation for unsigned scalar
discriminants, pruning statically impossible branches and refining copied
discriminants on matched cases. -/
@[expose] def evalUintSwitchEdges (w : IntWidth) (a : AbsVal)
    (srcReg? : Option LocalId) (env : MirAbsEnv) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    Option (List (BasicBlockId × MirAbsEnv)) :=
  branches.foldr
    (fun p ih =>
      if !Nat.blt p.1.toNat (modPow2 (bitWidthComp w)) then
        none
      else
        let caseA := AbsVal.const (bitWidthComp w) p.1.toNat
        match AbsVal.decideEq? (bitWidthComp w) a caseA with
        | some true =>
          let envT :=
            match srcReg? with
            | some r => refineEnvByGuard env (.ueqConst r w p.1.toNat) true
            | none => env
          some [(p.2, envT)]
        | some false => ih
        | none =>
          match ih with
          | none => none
          | some restEdges =>
            let envT :=
              match srcReg? with
              | some r => refineEnvByGuard env (.ueqConst r w p.1.toNat) true
              | none => env
            some ((p.2, envT) :: restEdges))
    (some [(otherwise, env)])

private theorem evalUintSwitchEdges_cons (w : IntWidth) (a : AbsVal)
    (srcReg? : Option LocalId) (env : MirAbsEnv) (otherwise : BasicBlockId)
    (caseBits : BitVec 128) (target : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId)) :
    evalUintSwitchEdges w a srcReg? env otherwise ((caseBits, target) :: rest) =
      if !Nat.blt caseBits.toNat (modPow2 (bitWidthComp w)) then
        none
      else
        match AbsVal.decideEq? (bitWidthComp w) a
            (AbsVal.const (bitWidthComp w) caseBits.toNat) with
        | some true =>
          some [(target,
            match srcReg? with
            | some r => refineEnvByGuard env (.ueqConst r w caseBits.toNat) true
            | none => env)]
        | some false =>
          evalUintSwitchEdges w a srcReg? env otherwise rest
        | none =>
          match evalUintSwitchEdges w a srcReg? env otherwise rest with
          | none => none
          | some restEdges =>
            some ((target,
              match srcReg? with
              | some r => refineEnvByGuard env (.ueqConst r w caseBits.toNat) true
              | none => env) :: restEdges) := rfl

private theorem switchCaseRefine_some_sound {bodyLocals : List MirTy} {w : IntWidth}
    {r : LocalId} {env : MirAbsEnv} {locals : List LocalSlot}
    {discrNat caseNat : Nat}
    (hEnv : mirAbsEnvDenote bodyLocals env locals)
    (hSrc : localUintNat? locals r w = some discrNat)
    (hEqN : discrNat = caseNat) :
    mirAbsEnvDenote bodyLocals
      (refineEnvByGuard env (.ueqConst r w caseNat) true) locals := by
  apply refineEnvByGuard_sound hEnv
  intro x hx
  rw [hSrc] at hx
  injection hx with hxEq
  subst hxEq
  exact ⟨fun _ => hEqN, fun _ => rfl⟩

private theorem evalUintSwitchEdges_sound {bodyLocals : List MirTy}
    {w : IntWidth} {a : AbsVal} {srcReg? : Option LocalId}
    {env : MirAbsEnv} {locals : List LocalSlot} {discrBits : BitVec 128}
    {otherwise : BasicBlockId} {branches : List (BitVec 128 × BasicBlockId)}
    {edges : List (BasicBlockId × MirAbsEnv)}
    (hEnv : mirAbsEnvDenote bodyLocals env locals)
    (hLt : discrBits.toNat < modPow2 (bitWidthComp w))
    (ha : a.denote (bitWidthComp w) (some discrBits.toNat))
    (hSrc : match srcReg? with
      | none => True
      | some r => localUintNat? locals r w = some discrBits.toNat)
    (hAbs : evalUintSwitchEdges w a srcReg? env otherwise branches = some edges) :
    ∃ target envT,
      evalSwitchBranches w discrBits otherwise branches = .ok target ∧
      (target, envT) ∈ edges ∧
      mirAbsEnvDenote bodyLocals envT locals := by
  revert edges hAbs
  induction branches with
  | nil =>
    intro edges hAbs
    injection hAbs with hEq; subst hEq
    exact ⟨otherwise, env, rfl, List.Mem.head _, hEnv⟩
  | cons hd rest ih =>
    intro edges hAbs
    cases hd with | mk caseBits target =>
    rw [evalUintSwitchEdges_cons] at hAbs
    cases hCLtB : Nat.blt caseBits.toNat (modPow2 (bitWidthComp w)) with
    | false => rw [hCLtB] at hAbs; nomatch hAbs
    | true =>
      rw [ite_bool_false_t (c := !Nat.blt caseBits.toNat (modPow2 (bitWidthComp w)))
        (by rw [hCLtB]; rfl)] at hAbs
      have hCLt : caseBits.toNat < modPow2 (bitWidthComp w) := lt_of_blt_true hCLtB
      have hCTr : truncateBits w caseBits = caseBits := truncateBits_of_lt hCLt
      have hDTr : truncateBits w discrBits = discrBits := truncateBits_of_lt hLt
      have hCNeF : (truncateBits w caseBits != caseBits) = false := by
        rw [hCTr]; dsimp only [bne, BEq.beq]; rw [decide_eq_true rfl]; rfl
      have hCaseDen : (AbsVal.const (bitWidthComp w) caseBits.toNat).denote
          (bitWidthComp w) (some caseBits.toNat) :=
        absVal_const_sound_lt (bitWidthComp_valid w) hCLt
      cases hDec : AbsVal.decideEq? (bitWidthComp w) a
          (AbsVal.const (bitWidthComp w) caseBits.toNat) with
      | some decB =>
        rw [hDec] at hAbs
        have hEqB := absVal_decideEq?_sound hDec ha hCaseDen
        cases decB with
        | true =>
          injection hAbs with hEq; subst hEq
          have hEqN := Nat.eq_of_beq_eq_true hEqB
          have hBvEq : discrBits = caseBits := by
            have h1 := bitVec128_ofNat_toNat discrBits
            have h2 := bitVec128_ofNat_toNat caseBits
            rw [← h1, ← h2, hEqN]
          have hBeqT : (truncateBits w discrBits == truncateBits w caseBits) = true := by
            rw [hDTr, hCTr, hBvEq]
            dsimp only [BEq.beq]; exact decide_eq_true rfl
          refine ⟨target, _, ?_, List.Mem.head _, by
            cases srcReg? with
            | none => exact hEnv
            | some r => exact switchCaseRefine_some_sound hEnv hSrc hEqN⟩
          dsimp only [evalSwitchBranches]
          rw [ite_bool_false_t hCNeF, ite_bool_true_t hBeqT]
        | false =>
          have hNeBv : discrBits ≠ caseBits := by
            intro hE
            rw [hE, nat_beq_refl] at hEqB
            nomatch hEqB
          have hBeqF : (truncateBits w discrBits == truncateBits w caseBits) = false := by
            rw [hDTr, hCTr]
            dsimp only [BEq.beq]
            exact decide_eq_false hNeBv
          cases ih hAbs with
          | intro tgt ht =>
            cases ht with | intro envT hT =>
            refine ⟨tgt, envT, ?_, hT.2.1, hT.2.2⟩
            dsimp only [evalSwitchBranches]
            rw [ite_bool_false_t hCNeF, ite_bool_false_t hBeqF]
            exact hT.1
      | none =>
        rw [hDec] at hAbs
        cases hRest : evalUintSwitchEdges w a srcReg? env otherwise rest with
        | none => rw [hRest] at hAbs; nomatch hAbs
        | some restEdges =>
          rw [hRest] at hAbs
          injection hAbs with hEq; subst hEq
          cases hMatch : Nat.beq discrBits.toNat caseBits.toNat with
          | true =>
            have hEqN := Nat.eq_of_beq_eq_true hMatch
            have hBvEq : discrBits = caseBits := by
              have h1 := bitVec128_ofNat_toNat discrBits
              have h2 := bitVec128_ofNat_toNat caseBits
              rw [← h1, ← h2, hEqN]
            have hBeqT : (truncateBits w discrBits == truncateBits w caseBits) = true := by
              rw [hDTr, hCTr, hBvEq]
              dsimp only [BEq.beq]; exact decide_eq_true rfl
            refine ⟨target, _, ?_, List.Mem.head _, by
              cases srcReg? with
              | none => exact hEnv
              | some r => exact switchCaseRefine_some_sound hEnv hSrc hEqN⟩
            dsimp only [evalSwitchBranches]
            rw [ite_bool_false_t hCNeF, ite_bool_true_t hBeqT]
          | false =>
            have hNeBv : discrBits ≠ caseBits := by
              intro hE
              rw [hE, nat_beq_refl] at hMatch
              nomatch hMatch
            have hBeqF : (truncateBits w discrBits == truncateBits w caseBits) = false := by
              rw [hDTr, hCTr]
              dsimp only [BEq.beq]
              exact decide_eq_false hNeBv
            cases ih hRest with
            | intro tgt ht =>
              cases ht with | intro envT hT =>
              refine ⟨tgt, envT, ?_, List.Mem.tail _ hT.2.1, hT.2.2⟩
              dsimp only [evalSwitchBranches]
              rw [ite_bool_false_t hCNeF, ite_bool_false_t hBeqF]
              exact hT.1

/-- Abstract terminator outcome: either a verified normal `.return_` with
initialized `_0` slot, or a list of feasible `(targetBb, refinedEnv)` edges. -/
inductive TermAbsOutcome where
  | ret (retSlot : MirAbsSlot)
  | edges (succs : List (BasicBlockId × MirAbsEnv))

/-- Abstract transfer for a basic block's terminator. Rejects `.unreachable`,
cleanup `.return_`, uninitialized `_0`, and unsupported terminators. -/
@[expose] def stepTermAbs (bodyLocals : List MirTy) (bb : BasicBlock) (env :
    MirAbsEnv) :
    Option TermAbsOutcome :=
  match bb.terminator with
  | .goto target => some (.edges [(target, env)])
  | .return_ =>
    if bb.cleanup then none
    else
      match compGetElem? env 0 with
      | some retSlot =>
        if retSlot.isInit then some (.ret retSlot) else none
      | none => none
  | .switchInt discr targets =>
    match evalOperandAbs bodyLocals env discr with
    | some (.bool ba, env₁) =>
      match ba with
      | .exact v g =>
        match evalBoolSwitchTarget v targets.otherwise targets.branches with
        | some tgt => some (.edges [(tgt, refineEnvByGuard env₁ g v)])
        | none => none
      | .top g =>
        match evalBoolSwitchTarget false targets.otherwise targets.branches,
              evalBoolSwitchTarget true targets.otherwise targets.branches with
        | some tgtF, some tgtT =>
          some (.edges [(tgtF, refineEnvByGuard env₁ g false),
                        (tgtT, refineEnvByGuard env₁ g true)])
        | _, _ => none
      | .bot | .uninit => none
    | some (.uint w a srcReg?, env₁) =>
      match evalUintSwitchEdges w a srcReg? env₁ targets.otherwise
          targets.branches with
      | some es => some (.edges es)
      | none => none
    | _ => none
  | .unreachable | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _
  | .unsupported => none

/-- 1-step soundness of `stepTermAbs` against `MirSemantics.evalTerminator`. -/
theorem stepTermAbs_sound {body : Body} {bb : BasicBlock} {frame : FrameState}
    {mem : MemoryState} {callerMem : CallerMemory}
    {env : MirAbsEnv} {out : TermAbsOutcome}
    (hEnv : mirAbsEnvDenote body.locals env frame.locals)
    (hTerm : stepTermAbs body.locals bb env = some out) :
    match out with
    | .ret retSlot =>
      ∃ retVal retTy,
        compGetElem? body.locals 0 = some retTy ∧
        evalTerminator body bb frame mem callerMem =
          .done (.returned ⟨retVal, callerMem⟩) ∧
        retSlot.denote retTy frame.locals (.immediate (some retVal))
    | .edges succs =>
      ∃ target envT locals',
        (target, envT) ∈ succs ∧
        evalTerminator body bb frame mem callerMem =
          .step {
            frames := [{ frame with blockIdx := target, stmtIdx := 0, locals := locals' }]
            callerMem
            mem
          } ∧
        mirAbsEnvDenote body.locals envT locals' := by
  cases hT : bb.terminator with
  | goto target =>
    dsimp only [stepTermAbs] at hTerm
    rw [hT] at hTerm
    injection hTerm with hOut; subst hOut
    refine ⟨target, env, frame.locals, List.Mem.head _, ?_, hEnv⟩
    dsimp only [evalTerminator]
    rw [hT]; rfl
  | return_ =>
    dsimp only [stepTermAbs] at hTerm
    rw [hT] at hTerm
    dsimp only at hTerm
    cases hCl : bb.cleanup with
    | true => rw [hCl] at hTerm; nomatch hTerm
    | false =>
      rw [ite_bool_false_t hCl] at hTerm
      cases hS0 : compGetElem? env 0 with
      | none => rw [hS0] at hTerm; nomatch hTerm
      | some retSlot =>
        rw [hS0] at hTerm
        dsimp only at hTerm
        cases hI : retSlot.isInit with
        | false => rw [hI] at hTerm; nomatch hTerm
        | true =>
          rw [hI] at hTerm
          injection hTerm with hOut; subst hOut
          have hExTy0 := compGetElem?_exists_of_len_t body.locals env 0 retSlot
            hEnv.1.symm hS0
          cases hExTy0 with | intro retTy hTy0 =>
          have hExCs0 := compGetElem?_exists_of_len_t frame.locals body.locals 0
            retTy hEnv.2.1 hTy0
          cases hExCs0 with | intro cs0 hCs0 =>
          have hDen0 := hEnv.2.2 0 retTy retSlot cs0 hTy0 hS0 hCs0
          have hImmSome : ∃ rv, cs0 = .immediate (some rv) := by
            cases cs0 with
            | dead | indirect _ =>
              cases retSlot with
              | dead => nomatch hI
              | uint _ _ | bool _ => exact False.elim hDen0.2
              | unit => nomatch hDen0.2
            | immediate opt =>
              cases opt with
              | some rv => exact ⟨rv, rfl⟩
              | none =>
                cases retSlot with
                | dead => nomatch hI
                | unit => nomatch hDen0.2
                | uint w a =>
                  cases absVal_init_of_isInit hI hDen0.2 with
                  | intro _ hx => nomatch hx.1
                | bool ba =>
                  cases ba with
                  | bot | uninit => nomatch hI
                  | top _ | exact _ _ => exact False.elim hDen0.2
          cases hImmSome with | intro retVal hCs0Eq =>
          subst hCs0Eq
          refine ⟨retVal, retTy, hTy0, ?_, hDen0⟩
          dsimp only [evalTerminator]
          rw [hT, ite_bool_false_t hCl, ← compGetElem?_eq, hCs0]
  | switchInt discr targets =>
    dsimp only [stepTermAbs] at hTerm
    rw [hT] at hTerm
    dsimp only at hTerm
    cases hOp : evalOperandAbs body.locals env discr with
    | none => rw [hOp] at hTerm; nomatch hTerm
    | some p =>
      cases p with | mk av env₁ =>
      rw [hOp] at hTerm
      cases av with
      | unit => nomatch hTerm
      | bool ba =>
        cases evalOperandAbs_primitive_sound (mem := mem) hEnv hOp rfl with
        | intro v hv =>
          cases hv with | intro locals₁ hR =>
          cases v with
          | bool bv =>
            cases ba with
            | bot | uninit => nomatch hTerm
            | exact ev g =>
              dsimp only at hTerm
              cases hTg : evalBoolSwitchTarget ev targets.otherwise targets.branches with
              | none => rw [hTg] at hTerm; nomatch hTerm
              | some tgt =>
                rw [hTg] at hTerm
                injection hTerm with hOut; subst hOut
                have hBvEq : bv = ev := hR.2.1.2.1
                subst hBvEq
                have hSw := evalBoolSwitchTarget_sound hTg
                refine ⟨tgt, refineEnvByGuard env₁ g bv, locals₁, List.Mem.head _,
                  ?_, refineEnvByGuard_sound hR.2.2 hR.2.1.2.2⟩
                dsimp only [evalTerminator]
                rw [hT]
                dsimp only
                rw [hR.1]
                dsimp only
                rw [hSw]
                rfl
            | top g =>
              dsimp only at hTerm
              cases hTgF : evalBoolSwitchTarget false targets.otherwise targets.branches with
              | none => rw [hTgF] at hTerm; nomatch hTerm
              | some tgtF =>
                cases hTgT : evalBoolSwitchTarget true targets.otherwise targets.branches with
                | none => rw [hTgF, hTgT] at hTerm; nomatch hTerm
                | some tgtT =>
                  rw [hTgF, hTgT] at hTerm
                  injection hTerm with hOut; subst hOut
                  cases bv with
                  | false =>
                    have hSw := evalBoolSwitchTarget_sound hTgF
                    refine ⟨tgtF, refineEnvByGuard env₁ g false, locals₁,
                      List.Mem.head _, ?_, refineEnvByGuard_sound hR.2.2 hR.2.1.2⟩
                    dsimp only [evalTerminator]
                    rw [hT]; dsimp only; rw [hR.1]; dsimp only; rw [hSw]; rfl
                  | true =>
                    have hSw := evalBoolSwitchTarget_sound hTgT
                    refine ⟨tgtT, refineEnvByGuard env₁ g true, locals₁,
                      List.Mem.tail _ (List.Mem.head _), ?_,
                      refineEnvByGuard_sound hR.2.2 hR.2.1.2⟩
                    dsimp only [evalTerminator]
                    rw [hT]; dsimp only; rw [hR.1]; dsimp only; rw [hSw]; rfl
          | scalar _ | ptr _ | char _ | ordering _ | unit
          | enumVal _ _ | tuple _ | bytes _ =>
            exact False.elim hR.2.1.2
      | uint w a srcReg? =>
        dsimp only at hTerm
        cases hEs : evalUintSwitchEdges w a srcReg? env₁ targets.otherwise
            targets.branches with
        | none => rw [hEs] at hTerm; nomatch hTerm
        | some es =>
          rw [hEs] at hTerm
          injection hTerm with hOut; subst hOut
          cases evalOperandAbs_primitive_sound (mem := mem) hEnv hOp rfl with
          | intro v hv =>
            cases hv with | intro locals₁ hR =>
            cases v with
            | scalar sv =>
              cases sv with | mk sw ss sb =>
              have hW := hR.2.1.2.2.1
              have hS := hR.2.1.2.2.2.1
              have hLt := hR.2.1.2.2.2.2.1
              have ha := hR.2.1.2.2.2.2.2.1
              have hSrc := hR.2.1.2.2.2.2.2.2
              dsimp only at hW hS hLt ha hSrc
              subst hW; subst hS
              cases evalUintSwitchEdges_sound hR.2.2 hLt ha hSrc hEs with
              | intro tgt ht =>
                cases ht with | intro envT hTgt =>
                refine ⟨tgt, envT, locals₁, hTgt.2.1, ?_, hTgt.2.2⟩
                dsimp only [evalTerminator]
                rw [hT]; dsimp only; rw [hR.1]; dsimp only; rw [hTgt.1]; rfl
            | ptr _ | bool _ | char _ | ordering _ | unit
            | enumVal _ _ | tuple _ | bytes _ =>
              exact False.elim hR.2.1.2.2
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | unsupported =>
    dsimp only [stepTermAbs] at hTerm
    rw [hT] at hTerm
    nomatch hTerm

end Anneal.AiPcc

end
