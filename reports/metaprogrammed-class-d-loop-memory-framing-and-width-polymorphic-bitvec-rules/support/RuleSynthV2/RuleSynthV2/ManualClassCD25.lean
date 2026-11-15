-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynthV2.MacrosV2

/-!
# Manual Baseline Proofs for 25 Class C/D Rules & 30 `BitVec w` Rules (`ManualClassCD25.lean`)

Provides the explicit, constructor-by-constructor manual proof baseline for the 25 Class C
memory-frame and Class D loop rules (`ClassCDDeriv`) and 30 width-polymorphic `BitVec w`
rules (`BVRewrite w`) without using `prove_loop_mem_sound`, `prove_loop_mem_iff_valid`, or
`prove_bitvec_rw_sound`, enabling a direct head-to-head measurement of LOC compression,
elaboration time, and `.olean` footprint against `SynthesizedClassCD25.lean`.
-/

namespace RuleSynthV2.Manual

open RuleSynthV2

theorem checkClassCDDeriv_sound_manual (src tgt : Stmt) (d : ClassCDDeriv) :
    checkClassCDDeriv src tgt d = true → stmtRefines src tgt := by
  intro h
  unfold checkClassCDDeriv at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨rfl, rfl⟩, hcond⟩
  cases d with
  | c01_deadStoreOverwrite slot e1 e2 =>
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr_setSlot, setSlot_overwrite]
  | c02_storeLoadForward dst slot e =>
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr_setSlot, setSlot_get_same]
  | c03_disjointStoreComm s1 s2 e1 e2 =>
    simp only [inferClassCDRule, decide_eq_true_eq] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr_setSlot, setSlot_comm st _ _ hcond]
  | c04_disjointStoreLoadHoist dst sStore sLoad e =>
    simp only [inferClassCDRule, Bool.and_eq_true, decide_eq_true_eq] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, setSlot_get_ne _ _ hcond.1,
               evalExpr_setReg_of_notReads _ _ _ _ hcond.2, setReg_setSlot_comm]
  | c05_loadLoadCSE r1 r2 slot =>
    simp only [inferClassCDRule, decide_eq_true_eq] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, setReg_slots, evalExpr, setReg_get_same]
  | c06_deadRegOverwrite r e1 e2 =>
    simp only [inferClassCDRule] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr_setReg_of_notReads _ _ _ _ hcond, setReg_overwrite]
  | c07_storeAssignComm slot r eStore eReg =>
    simp only [inferClassCDRule] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr_setSlot,
               evalExpr_setReg_of_notReads _ _ _ _ hcond, setReg_setSlot_comm]
  | c08_redundantStoreAfterLoad r slot =>
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr, setReg_get_same,
               setReg_setSlot_comm, setSlot_get_self_eq]
  | d09_whileZeroElim body =>
    intro st _
    simp only [inferClassCDRule, evalStmt_while_zero]
  | d10_whileOnePeel body =>
    intro st _
    simp only [inferClassCDRule, evalStmt]
    cases evalStmt st body <;> rfl
  | d11_whilePeelFirst k body =>
    intro st _
    simp only [inferClassCDRule, evalStmt_while_peel1]
  | d12_whilePeelTwo k body =>
    intro st _
    simp only [inferClassCDRule, evalStmt_while_peel2]
  | d13_whileUnroll2x k body =>
    clear hcond
    intro st hno_ub
    clear hno_ub
    simp only [inferClassCDRule]
    induction k generalizing st with
    | zero => simp [evalStmt]
    | succ k' ih =>
      have h_mul : 2 * (k' + 1) = (2 * k') + 2 := by omega
      rw [h_mul, evalStmt_while_peel2, evalStmt_while_peel1]
      simp only [evalStmt]
      cases h1 : evalStmt st body with
      | val st1 =>
        simp only []
        cases h2 : evalStmt st1 body with
        | val st2 =>
          simp only []
          exact (ih st2)
        | panic => rfl
        | ub => rfl
      | panic => rfl
      | ub => rfl
  | d14_whileReroll2x k body =>
    clear hcond
    intro st hno_ub
    clear hno_ub
    simp only [inferClassCDRule]
    induction k generalizing st with
    | zero => simp [evalStmt]
    | succ k' ih =>
      have h_mul : 2 * (k' + 1) = (2 * k') + 2 := by omega
      rw [h_mul, evalStmt_while_peel2, evalStmt_while_peel1]
      simp only [evalStmt]
      cases h1 : evalStmt st body with
      | val st1 =>
        simp only []
        cases h2 : evalStmt st1 body with
        | val st2 =>
          simp only []
          exact (ih st2)
        | panic => rfl
        | ub => rfl
      | panic => rfl
      | ub => rfl
  | d15_whileSplit k1 k2 body =>
    clear hcond
    intro st hno_ub
    clear hno_ub
    simp only [inferClassCDRule]
    induction k1 generalizing st with
    | zero => simp [evalStmt]
    | succ k1' ih =>
      have h_add : (k1' + 1) + k2 = (k1' + k2) + 1 := by omega
      rw [h_add]
      simp only [evalStmt]
      cases h1 : evalStmt st body with
      | val st1 =>
        simp only []
        have ih1 := ih st1
        simp only [evalStmt] at ih1
        exact ih1
      | panic => rfl
      | ub => rfl
  | d16_whileFuseSameBody k1 k2 body =>
    clear hcond
    intro st hno_ub
    clear hno_ub
    simp only [inferClassCDRule]
    induction k1 generalizing st with
    | zero => simp [evalStmt]
    | succ k1' ih =>
      have h_add : (k1' + 1) + k2 = (k1' + k2) + 1 := by omega
      rw [h_add]
      simp only [evalStmt]
      cases h1 : evalStmt st body with
      | val st1 =>
        simp only []
        have ih1 := ih st1
        simp only [evalStmt] at ih1
        exact ih1
      | panic => rfl
      | ub => rfl
  | d17_whileSkipBody k =>
    intro st _
    simp only [inferClassCDRule, evalStmt_while_zero]
  | d18_whileLicmSkipPre k body =>
    intro st _
    simp only [inferClassCDRule, evalStmt_seq_skip_left]
  | d19_whileLicmSkipPost k body =>
    intro st _
    simp only [inferClassCDRule, evalStmt_seq_skip_right]
  | d20_tailCallToCallPure dst arg =>
    intro st _
    simp only [inferClassCDRule, evalStmt]
  | d21_callPureCSE r1 r2 arg =>
    simp only [inferClassCDRule, Bool.and_eq_true, decide_eq_true_eq] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr,
               evalExpr_setReg_of_notReads _ _ _ _ hcond.2, setReg_get_same]
  | d22_callPureStoreComm dst slot arg eStore =>
    simp only [inferClassCDRule] at hcond
    intro st _
    simp only [inferClassCDRule, evalStmt, evalExpr_setSlot,
               evalExpr_setReg_of_notReads _ _ _ _ hcond, setReg_setSlot_comm]
  | d23_elimAssumeNonNegUB r =>
    intro st hno_ub
    simp only [inferClassCDRule, evalStmt] at hno_ub ⊢
    by_cases hr : 0 ≤ st.regs r <;> simp [hr] at hno_ub ⊢
  | d24_ifZeroTrueBranch t e =>
    intro st _
    simp [inferClassCDRule, evalStmt]
  | d25_ifZeroFalseBranch t e =>
    intro st _
    simp [inferClassCDRule, evalStmt]

theorem checkClassCDDeriv_complete_manual (src tgt : Stmt) (d : ClassCDDeriv) :
    ValidClassCDDeriv src tgt d → checkClassCDDeriv src tgt d = true := by
  intro ⟨hs, ht, hc⟩
  cases d <;> simp [checkClassCDDeriv, hs, ht, hc]

theorem checkClassCDDeriv_iff_valid_manual (src tgt : Stmt) (d : ClassCDDeriv) :
    checkClassCDDeriv src tgt d = true ↔ ValidClassCDDeriv src tgt d := by
  constructor
  · intro h
    unfold checkClassCDDeriv at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · exact checkClassCDDeriv_complete_manual src tgt d

theorem checkBVRewrite_sound_manual {w : WidthTag} (rw : BVRewrite w)
    (env : Nat → PoisonOr (BitVec w.bits)) :
    refinesPoison (evalBVExpr env (inferBVRewrite rw).1) (evalBVExpr env (inferBVRewrite rw).2) := by
  cases rw with
  | r01_addZeroRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.add_zero]
  | r02_addZeroLeft e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.zero_add]
  | r03_subZeroRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.sub_zero]
  | r04_subSelfToZero e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.sub_self]
  | r05_andSelf e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.and_self]
  | r06_andZeroRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.and_zero]
  | r07_andZeroLeft e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.zero_and]
  | r08_mulOneRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.mul_one]
  | r09_mulOneLeft e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.one_mul]
  | r10_orSelf e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.or_self]
  | r11_orZeroRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.or_zero]
  | r12_orZeroLeft e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.zero_or]
  | r13_mulZeroRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.mul_zero]
  | r14_mulZeroLeft e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.zero_mul]
  | r15_xorSelfToZero e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.xor_self]
  | r16_xorZeroRight e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.xor_zero]
  | r17_xorZeroLeft e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.zero_xor]
  | r18_mulComm a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a <;> cases evalBVExpr env b <;> simp [liftBV2, refinesPoison, BitVec.mul_comm]
  | r19_addComm a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a <;> cases evalBVExpr env b <;> simp [liftBV2, refinesPoison, BitVec.add_comm]
  | r20_andComm a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a <;> cases evalBVExpr env b <;> simp [liftBV2, refinesPoison, BitVec.and_comm]
  | r21_orComm a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a <;> cases evalBVExpr env b <;> simp [liftBV2, refinesPoison, BitVec.or_comm]
  | r22_xorComm a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a <;> cases evalBVExpr env b <;> simp [liftBV2, refinesPoison, BitVec.xor_comm]
  | r23_shlZero e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV1, refinesPoison, BitVec.shiftLeft_zero]
  | r24_ushrZero e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV1, refinesPoison, BitVec.ushiftRight_zero]
  | r25_dropAddNuw a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a with
    | poison => exact Or.inl rfl
    | val va =>
      cases evalBVExpr env b with
      | poison => exact Or.inl rfl
      | val vb =>
        simp only [liftBV2]
        by_cases h_ok : va.toNat + vb.toNat < 2 ^ w.bits <;> simp [h_ok, refinesPoison]
  | r26_dropSubNuw a b =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env a with
    | poison => exact Or.inl rfl
    | val va =>
      cases evalBVExpr env b with
      | poison => exact Or.inl rfl
      | val vb =>
        simp only [liftBV2]
        by_cases h_ok : vb.toNat ≤ va.toNat <;> simp [h_ok, refinesPoison]
  | r27_freezeZeroConst =>
    exact Or.inr rfl
  | r28_freezeIdem e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [refinesPoison]
  | r29_insertFreeze e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [refinesPoison]
  | r30_doubleSubCancel e =>
    simp only [inferBVRewrite, evalBVExpr]
    cases evalBVExpr env e <;> simp [liftBV2, refinesPoison, BitVec.add_zero, BitVec.sub_zero]

end RuleSynthV2.Manual
