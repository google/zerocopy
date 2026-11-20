-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal.MirWp
import Inputs

namespace Endianness

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem bvZeroExtend_128_toNat (w : Word) :
    (bvZeroExtend 128 w).toNat = w.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide))

theorem truncateBits_i64_ofNat (n : Nat) :
    truncateBits .i64 (BitVec.ofNat 128 n) =
      bvZeroExtend 128 (BitVec.ofNat 64 n) := by
  apply BitVec.eq_of_toNat_eq
  unfold truncateBits IntWidth.bitWidth IntWidth.byteSize bvExtractLsb
    bvExtractLsb' bvZeroExtend
  simp only [BitVec.toNat_ofNat]
  change (n % 2 ^ 128) % 2 ^ 64 % 2 ^ 128 = n % 2 ^ 64 % 2 ^ 128
  rw [Nat.mod_mod_of_dvd n (by decide : 2 ^ 64 ∣ 2 ^ 128)]

theorem truncateBits_i64_bvZeroExtend (w : Word) :
    truncateBits .i64 (bvZeroExtend 128 w) = bvZeroExtend 128 w := by
  change truncateBits .i64 (BitVec.ofNat 128 w.toNat) = bvZeroExtend 128 w
  rw [truncateBits_i64_ofNat]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem checkVal_u64Val (w : Word) :
    checkVal (u64Val w) (.int .i64 false) = true := by
  change checkVal (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩)
    (.int .i64 false) = true
  rw [← truncateBits_i64_bvZeroExtend w]
  exact checkVal_u64_truncateBits (bvZeroExtend 128 w)

noncomputable def u64BitAndVal (x y : Word) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvAnd (truncateBits .i64 (bvZeroExtend 128 x))
      (truncateBits .i64 (bvZeroExtend 128 y)))⟩

noncomputable def u64BitOrVal (x y : Word) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvOr (truncateBits .i64 (bvZeroExtend 128 x))
      (truncateBits .i64 (bvZeroExtend 128 y)))⟩

noncomputable def u64ShlVal (x : Word) (k : Nat) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvOfInt 128
      (.ofNat (Nat.shiftLeft
        (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩

noncomputable def u64ShrVal (x : Word) (k : Nat) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvOfInt 128
      (.ofNat (Nat.shiftRight
        (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩

theorem u64BitAndVal_eq (x y : Word) :
    u64BitAndVal x y = u64Val (x &&& y) := by
  unfold u64BitAndVal u64Val bvAnd
  rw [truncateBits_i64_bvZeroExtend x, truncateBits_i64_bvZeroExtend y,
      bvZeroExtend_128_toNat x, bvZeroExtend_128_toNat y,
      truncateBits_i64_ofNat]
  have h : BitVec.ofNat 64 (Nat.land x.toNat y.toNat) = x &&& y := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_and]
    change (x.toNat &&& y.toNat) % 2 ^ 64 = x.toNat &&& y.toNat
    exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow x.toNat y.isLt)
  rw [h]
  rfl

theorem u64BitOrVal_eq (x y : Word) :
    u64BitOrVal x y = u64Val (x ||| y) := by
  unfold u64BitOrVal u64Val bvOr
  rw [truncateBits_i64_bvZeroExtend x, truncateBits_i64_bvZeroExtend y,
      bvZeroExtend_128_toNat x, bvZeroExtend_128_toNat y,
      truncateBits_i64_ofNat]
  have h : BitVec.ofNat 64 (Nat.lor x.toNat y.toNat) = x ||| y := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_or]
    change (x.toNat ||| y.toNat) % 2 ^ 64 = x.toNat ||| y.toNat
    exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.isLt y.isLt)
  rw [h]
  rfl

theorem u64ShlVal_eq (x : Word) (k : Nat) :
    u64ShlVal x k = u64Val (x <<< k) := by
  unfold u64ShlVal u64Val bvOfInt intEmod
  rw [truncateBits_i64_bvZeroExtend x, bvZeroExtend_128_toNat x]
  dsimp only [Int.natAbs, Int.toNat]
  rw [truncateBits_i64_ofNat]
  have h : BitVec.ofNat 64
      (Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 128)) = x <<< k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
    change (x.toNat <<< k) % 2 ^ 128 % 2 ^ 64 = (x.toNat <<< k) % 2 ^ 64
    exact Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 128)
  rw [h]
  rfl

theorem u64ShrVal_eq (x : Word) (k : Nat) :
    u64ShrVal x k = u64Val (x >>> k) := by
  unfold u64ShrVal u64Val bvOfInt intEmod
  rw [truncateBits_i64_bvZeroExtend x, bvZeroExtend_128_toNat x]
  dsimp only [Int.natAbs, Int.toNat]
  rw [truncateBits_i64_ofNat]
  have h : BitVec.ofNat 64
      (Nat.mod (Nat.shiftRight x.toNat k) (Nat.pow 2 128)) = x >>> k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
    change (x.toNat >>> k) % 2 ^ 128 % 2 ^ 64 = x.toNat >>> k
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 128)]
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)
  rw [h]
  rfl

noncomputable def evalAssignVal (body : Body) (s : State) : Option Val :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some (.assign dst rvalue) =>
        match Trusted.MirSemantics.getElem? body.locals dst.localId with
        | some dstTy =>
          match evalRvalue body.locals frame.locals dstTy rvalue with
          | .ok (val, _) => some val
          | .error _ => none
        | none => none
      | _ => none
    | none => none
  | _ => none

noncomputable def evalAssignWith (body : Body) (s : State)
    (overrideVal : Val) : StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match Nat.beq frame.defId 0 with
    | false => .fault .unsupported
    | true =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some (.assign dst rvalue) =>
          match dst.projection.isEmpty with
          | false => .fault .unsupported
          | true =>
            match Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => .fault .unsupported
            | some dstTy =>
              match MirTy.beq dstTy (.int .i64 false) with
              | false => .fault .unsupported
              | true =>
                match evalRvalue body.locals frame.locals dstTy rvalue with
                | .error k => .fault k
                | .ok (_, localsAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | none => .fault .unsupported
                  | some .dead => .fault .undefined
                  | some (.live _) =>
                    match setElem? localsAfterRval dst.localId
                        (.live (some overrideVal)) with
                    | some localsAfterWrite =>
                      .step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterWrite
                        }]
                        callerMem := s.callerMem
                      }
                    | none => .fault .unsupported
        | _ => .fault .unsupported
  | _ => .fault .unsupported

theorem mirTy_eq_u64_of_beq {ty : MirTy}
    (h : MirTy.beq ty (.int .i64 false) = true) : ty = .int .i64 false := by
  cases ty with
  | int w s =>
    unfold MirTy.beq IntWidth.beq at h
    cases w <;> cases s <;> first | rfl | cases h
  | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
  | unsupported =>
    unfold MirTy.beq at h
    cases h

theorem step_eq_evalAssignWith {body : Body} {s next : State} {val : Val}
    {w : Word}
    (h_val : evalAssignVal body s = some val)
    (h_eq : val = u64Val w)
    (h_next : evalAssignWith body s (u64Val w) = .step next) :
    evalStep (bodyProg body) 0 s = .step next := by
  unfold evalAssignVal at h_val
  unfold evalAssignWith at h_next
  unfold bodyProg evalStep
  cases h_fr : s.frames with
  | nil => rw [h_fr] at h_next; cases h_next
  | cons frame rest =>
    cases rest with
    | cons _ _ => rw [h_fr] at h_next; cases h_next
    | nil =>
      rw [h_fr] at h_val h_next
      dsimp only at h_val h_next ⊢
      cases h_def : Nat.beq frame.defId 0 with
      | false => rw [h_def] at h_next; cases h_next
      | true =>
        rw [h_def] at h_next
        dsimp only at h_next
        have h_def0 : frame.defId = 0 := Nat.eq_of_beq_eq_true h_def
        rw [h_def0]
        rw [show Trusted.MirSemantics.getElem? [body] 0 = some body from rfl]
        dsimp only
        cases h_bb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [h_bb] at h_next; cases h_next
        | some bb =>
          rw [h_bb] at h_val h_next
          dsimp only at h_val h_next ⊢
          cases h_st :
              Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | none => rw [h_st] at h_next; cases h_next
          | some stmt =>
            rw [h_st] at h_val h_next
            dsimp only at h_val h_next ⊢
            cases stmt with
            | nop | storageLive _ | storageDead _ | unsupported => cases h_next
            | assign dst rvalue =>
              dsimp only at h_val h_next
              unfold evalStatement
              dsimp only
              cases h_proj : dst.projection.isEmpty with
              | false => rw [h_proj] at h_next; cases h_next
              | true =>
                rw [h_proj] at h_next
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                dsimp only at h_next
                cases h_dst :
                    Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [h_dst] at h_next; cases h_next
                | some dstTy =>
                  rw [h_dst] at h_val h_next
                  dsimp only at h_val h_next ⊢
                  cases h_ty : MirTy.beq dstTy (.int .i64 false) with
                  | false => rw [h_ty] at h_next; cases h_next
                  | true =>
                    rw [h_ty] at h_next
                    dsimp only at h_next
                    have h_ty_eq := mirTy_eq_u64_of_beq h_ty
                    subst h_ty_eq
                    cases h_rv : evalRvalue body.locals frame.locals
                        (.int .i64 false) rvalue with
                    | error k => rw [h_rv] at h_val; cases h_val
                    | ok pair =>
                      rw [h_rv] at h_val h_next
                      dsimp only at h_val h_next ⊢
                      injection h_val with h_v
                      have h_vw : pair.1 = u64Val w := h_v.trans h_eq
                      rw [h_vw]
                      unfold writePlace
                      rw [checkVal_u64Val w]
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                      cases h_slot :
                          Trusted.MirSemantics.getElem? pair.2 dst.localId with
                      | none => rw [h_slot] at h_next; cases h_next
                      | some slot =>
                        rw [h_slot] at h_next
                        cases slot with
                        | dead => cases h_next
                        | live _ =>
                          dsimp only at h_next ⊢
                          cases h_set : setElem? pair.2 dst.localId
                              (.live (some (u64Val w))) with
                          | none => rw [h_set] at h_next; cases h_next
                          | some localsAfterWrite =>
                            rw [h_set] at h_next
                            exact h_next

theorem step_u64Use {body : Body} {s next : State} (x : Word)
    (h_val : evalAssignVal body s = some (u64Val x))
    (h_next : evalAssignWith body s (u64Val x) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val rfl h_next

theorem step_u64And {body : Body} {s next : State} (x y : Word)
    (h_val : evalAssignVal body s = some (u64BitAndVal x y))
    (h_next : evalAssignWith body s (u64Val (x &&& y)) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val (u64BitAndVal_eq x y) h_next

theorem step_u64Or {body : Body} {s next : State} (x y : Word)
    (h_val : evalAssignVal body s = some (u64BitOrVal x y))
    (h_next : evalAssignWith body s (u64Val (x ||| y)) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val (u64BitOrVal_eq x y) h_next

theorem step_u64Shl {body : Body} {s next : State} (x : Word) (k : Nat)
    (h_val : evalAssignVal body s = some (u64ShlVal x k))
    (h_next : evalAssignWith body s (u64Val (x <<< k)) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val (u64ShlVal_eq x k) h_next

theorem step_u64Shr {body : Body} {s next : State} (x : Word) (k : Nat)
    (h_val : evalAssignVal body s = some (u64ShrVal x k))
    (h_next : evalAssignWith body s (u64Val (x >>> k)) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val (u64ShrVal_eq x k) h_next

theorem natListBeq_eq {xs ys : List Nat} (h : natListBeq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      change (Nat.beq x y && natListBeq xs ys) = true at h
      have h1 : Nat.beq x y = true := by
        cases h_xy : Nat.beq x y
        · rw [h_xy] at h; cases h
        · rfl
      have h2 : natListBeq xs ys = true := by
        rw [h1] at h; exact h
      rw [Nat.eq_of_beq_eq_true h1, ih h2]

theorem intWidth_beq_eq {w1 w2 : IntWidth}
    (h : IntWidth.beq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | cases h

theorem enumTagRepr_beq_eq {r1 r2 : EnumTagRepr}
    (h : EnumTagRepr.beq r1 r2 = true) : r1 = r2 := by
  cases r1 with
  | zeroSized =>
    cases r2 with
    | zeroSized => rfl
    | scalar _ _ => cases h
  | scalar w1 s1 =>
    cases r2 with
    | zeroSized => cases h
    | scalar w2 s2 =>
      cases w1 <;> cases w2 <;> cases s1 <;> cases s2 <;> first | rfl | cases h

theorem enumTy_beq_eq {e1 e2 : EnumTy}
    (h : EnumTy.beq e1 e2 = true) : e1 = e2 := by
  cases e1 with
  | mk id1 dw1 ds1 tr1 discs1 =>
    cases e2 with
    | mk id2 dw2 ds2 tr2 discs2 =>
      unfold EnumTy.beq at h
      dsimp only at h
      cases h1 : Nat.beq id1 id2 <;>
        cases h2 : IntWidth.beq dw1 dw2 <;>
        cases h3 : (ds1 == ds2) <;>
        cases h4 : EnumTagRepr.beq tr1 tr2 <;>
        cases h5 : natListBeq discs1 discs2 <;>
        rw [h1, h2, h3, h4, h5] at h <;>
        try cases h
      rw [Nat.eq_of_beq_eq_true h1, intWidth_beq_eq h2, eq_of_beq h3,
        enumTagRepr_beq_eq h4, natListBeq_eq h5]

theorem checkVal_bool_elim {v : Val} (h : checkVal v .bool = true) :
    ∃ b : Bool, v = .bool b := by
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | scalar sv =>
    cases h_wf : sv.wf <;> simp [checkVal, Val.ty?, h_wf, MirTy.beq] at h
  | enumVal ety var =>
    cases h_adm : (enumAdmitted ety && Nat.blt var ety.discriminants.length) <;>
      simp [checkVal, Val.ty?, h_adm, MirTy.beq] at h
  | ptr _ | unit | tuple _ | bytes _ => cases h

theorem checkVal_dataWidth_elim {ety : EnumTy}
    (h_ds : ety.discriminants = [0, 1, 2, 3]) {v : Val}
    (h : checkVal v (.enum ety) = true) :
    ∃ w : Fin 4, v = .enumVal ety w.val := by
  cases v with
  | enumVal ety' var =>
    cases h_adm : (enumAdmitted ety' && Nat.blt var ety'.discriminants.length) with
    | false => simp [checkVal, Val.ty?, h_adm] at h
    | true =>
      have h_ty :
          MirTy.beq (.enum ety') (.enum ety) = true := by
        unfold checkVal Val.ty? at h
        dsimp only at h
        rw [h_adm] at h
        exact h
      unfold MirTy.beq at h_ty
      have h_eq := enumTy_beq_eq h_ty
      subst h_eq
      have h_blt : Nat.blt var 4 = true := by
        rw [h_ds] at h_adm
        cases h_e : enumAdmitted ety'
        · rw [h_e] at h_adm; cases h_adm
        · rw [h_e] at h_adm; exact h_adm
      have h_lt : var < 4 := Nat.le_of_ble_eq_true h_blt
      exact ⟨⟨var, h_lt⟩, rfl⟩
  | scalar sv =>
    cases h_wf : sv.wf <;> simp [checkVal, Val.ty?, h_wf, MirTy.beq] at h
  | bool _ | ptr _ | unit | tuple _ | bytes _ => cases h

theorem checkVal_u64_elim {v : Val}
    (h : checkVal v (.int .i64 false) = true) :
    ∃ w : Word, v = u64Val w := by
  cases v with
  | scalar sv =>
    cases sv with
    | mk width signed bits =>
      cases h_wf : ScalarVal.wf ⟨width, signed, bits⟩ with
      | false => simp [checkVal, Val.ty?, h_wf] at h
      | true =>
        have h_beq :
            MirTy.beq (.int width signed) (.int .i64 false) = true := by
          unfold checkVal Val.ty? at h
          dsimp only at h
          rw [h_wf] at h
          exact h
        have h_ty : MirTy.int width signed = .int .i64 false :=
          mirTy_eq_u64_of_beq h_beq
        injection h_ty with h_w h_s
        subst h_w h_s
        unfold ScalarVal.wf at h_wf
        have h_trunc : truncateBits .i64 bits = bits := eq_of_beq h_wf
        exact ⟨bvExtractLsb 63 0 bits,
          congrArg (fun b => Val.scalar ⟨.i64, false, b⟩) h_trunc.symm⟩
  | enumVal ety var =>
    cases h_adm : (enumAdmitted ety && Nat.blt var ety.discriminants.length) <;>
      simp [checkVal, Val.ty?, h_adm, MirTy.beq] at h
  | bool _ | ptr _ | unit | tuple _ | bytes _ => cases h

theorem bodyDataWidthVal_of_paramTys (body : Body) (ety : EnumTy)
    (paramTys : (body.locals.drop 1).take body.argumentCount =
      [.bool, .enum ety, .int .i64 false])
    (w : Nat) :
    bodyDataWidthVal body w = .enumVal ety w := by
  cases h_loc : body.locals with
  | nil => simp [h_loc] at paramTys
  | cons l0 ls0 =>
    cases ls0 with
    | nil => simp [h_loc] at paramTys
    | cons l1 ls1 =>
      cases ls1 with
      | nil =>
        cases h_ac : body.argumentCount with
        | zero => simp [h_loc, h_ac] at paramTys
        | succ k => simp [h_loc, h_ac] at paramTys
      | cons l2 ls2 =>
        cases h_ac : body.argumentCount with
        | zero => simp [h_loc, h_ac] at paramTys
        | succ k0 =>
          cases k0 with
          | zero => simp [h_loc, h_ac] at paramTys
          | succ k1 =>
            have h_l2 : l2 = .enum ety := by
              simp [h_loc, h_ac] at paramTys
              exact paramTys.2.1
            subst h_l2
            simp [bodyDataWidthVal, h_loc]

/-- Valid source entries have exactly the finite flag and width cases. -/
theorem validArgs3_elim (body : Body) (ety : EnumTy)
    (paramTys : (body.locals.drop 1).take body.argumentCount =
      [.bool, .enum ety, .int .i64 false])
    (h_ds : ety.discriminants = [0, 1, 2, 3])
    (p : List Val → Prop)
    (inputs : ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      p (bodyEndianArgs body flag width.val value)) :
    ∀ args, ValidEntryArgs body args → p args := by
  intro args valid
  unfold ValidEntryArgs at valid
  rw [paramTys] at valid
  cases args with
  | nil => cases valid
  | cons a0 rest0 =>
    cases rest0 with
    | nil => simp [checkArgsMatch] at valid
    | cons a1 rest1 =>
      cases rest1 with
      | nil => simp [checkArgsMatch] at valid
      | cons a2 rest2 =>
        cases rest2 with
        | cons _ _ => simp [checkArgsMatch] at valid
        | nil =>
          simp only [checkArgsMatch, Bool.and_eq_true] at valid
          let ⟨flag, hf⟩ := checkVal_bool_elim valid.1
          let ⟨width, hw⟩ := checkVal_dataWidth_elim h_ds valid.2.1
          let ⟨value, hv⟩ := checkVal_u64_elim valid.2.2.1
          subst hf hw hv
          have h_dw := bodyDataWidthVal_of_paramTys body ety paramTys
            width.val
          have h_eq :
              [.bool flag, .enumVal ety width.val, u64Val value] =
              bodyEndianArgs body flag width.val value := by
            unfold bodyEndianArgs
            rw [h_dw]
          rw [h_eq]
          exact inputs flag width value

theorem enumTy_beq_self (e : EnumTy) : EnumTy.beq e e = true := by
  cases e with
  | mk id dw ds tr discs =>
    have hw : IntWidth.beq dw dw = true := by cases dw <;> rfl
    have htr : EnumTagRepr.beq tr tr = true := by
      cases tr with
      | zeroSized => rfl
      | scalar w s => cases w <;> cases s <;> rfl
    have hdl : natListBeq discs discs = true := by
      induction discs with
      | nil => rfl
      | cons x xs ih =>
        change (Nat.beq x x && natListBeq xs xs) = true
        rw [Nat.beq_refl, ih]
        rfl
    unfold EnumTy.beq
    dsimp only
    rw [Nat.beq_refl, hw, beq_self_eq_true, htr, hdl]
    rfl

theorem validEntryArgs_bodyEndianArgs (body : Body) (ety : EnumTy)
    (paramTys : (body.locals.drop 1).take body.argumentCount =
      [.bool, .enum ety, .int .i64 false])
    (h_ds : ety.discriminants = [0, 1, 2, 3])
    (h_adm : enumAdmitted ety = true)
    (flag : Bool) (width : Fin 4) (value : Word) :
    ValidEntryArgs body (bodyEndianArgs body flag width.val value) := by
  unfold ValidEntryArgs bodyEndianArgs
  rw [paramTys, bodyDataWidthVal_of_paramTys body ety paramTys width.val]
  have h_blt : Nat.blt width.val ety.discriminants.length = true := by
    rw [h_ds]
    exact Nat.ble_eq_true_of_le width.isLt
  have h_enum : checkVal (.enumVal ety width.val) (.enum ety) = true := by
    simp [checkVal, Val.ty?, h_adm, h_blt, MirTy.beq, enumTy_beq_self]
  have h_bool : checkVal (.bool flag) .bool = true := rfl
  have h_u64 : checkVal (u64Val value) (.int .i64 false) = true :=
    checkVal_u64Val value
  simp [checkArgsMatch, h_bool, h_enum, h_u64]

end Endianness
