-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import W6Proto.Checker

namespace W6Proto

/-- Frame lemma: modifying a stack/memory slot preserves evaluation of pure
register expressions (`evalExpr`). This discharges the implicit frame obligation
in `promoteSlotToAssign`, `forwardStoreAcrossNoAlias`, and `elimOverwrittenStore`. -/
theorem evalExpr_setSlot (st : State) (s : SlotId) (v : Int) (e : Expr) :
    evalExpr (st.setSlot s v) e = evalExpr st e := by
  induction e with
  | const _ => rfl
  | var _ => rfl
  | add a b iha ihb => simp [evalExpr, iha, ihb]
  | sub a b iha ihb => simp [evalExpr, iha, ihb]
  | mul a b iha ihb => simp [evalExpr, iha, ihb]

theorem inferExprRewrite_sound (rw : ExprRewrite) (st : State) :
    evalExpr st (inferExprRewrite rw).1 = evalExpr st (inferExprRewrite rw).2 := by
  induction rw with
  | refl e => rfl
  | addZeroRight e => simp [inferExprRewrite, evalExpr]
  | addZeroLeft e => simp [inferExprRewrite, evalExpr]
  | subSelf e => simp [inferExprRewrite, evalExpr]
  | mulOneRight e => simp [inferExprRewrite, evalExpr]
  | constAdd a b => simp [inferExprRewrite, evalExpr]
  | constMul a b => simp [inferExprRewrite, evalExpr]
  | congAdd r1 r2 ih1 ih2 =>
    simp only [inferExprRewrite, evalExpr, ih1, ih2]
  | congSub r1 r2 ih1 ih2 =>
    simp only [inferExprRewrite, evalExpr, ih1, ih2]
  | congMul r1 r2 ih1 ih2 =>
    simp only [inferExprRewrite, evalExpr, ih1, ih2]

theorem setSlot_get_same (st : State) (s : SlotId) (v : Int) :
    (st.setSlot s v).slots s = v := by
  simp [State.setSlot]

theorem setSlot_get_ne (st : State) {s1 s2 : SlotId} (v : Int) (hne : s1 ≠ s2) :
    (st.setSlot s2 v).slots s1 = st.slots s1 := by
  simp [State.setSlot, hne]

theorem setSlot_overwrite (st : State) (s : SlotId) (v1 v2 : Int) :
    (st.setSlot s v1).setSlot s v2 = st.setSlot s v2 := by
  cases st
  simp only [State.setSlot, State.mk.injEq, true_and]
  funext s'
  split <;> rfl

/-- Statement-level soundness: any derivation accepted by `checkStmtDeriv`
preserves semantics under `stmtRefines`. -/
theorem checkStmtDeriv_sound {src tgt : Stmt} {d : StmtDeriv}
    (h : checkStmtDeriv src tgt d = true) : stmtRefines src tgt := by
  induction d generalizing src tgt with
  | refl s =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    exact stmtRefines_refl _
  | rewriteAssign dst rw =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt, inferExprRewrite_sound rw st]
  | promoteSlotToAssign slot tag dst e =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt, setSlot_get_same, evalExpr_setSlot]
  | forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
    simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
    rcases h with ⟨⟨hne_s, _⟩, ⟨rfl, rfl⟩⟩
    intro st _
    simp only [evalStmt, setSlot_get_ne _ _ hne_s, setSlot_get_same, evalExpr_setSlot]
  | elimOverwrittenStore slot t1 t2 e1 e2 =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt, setSlot_overwrite, evalExpr_setSlot]
  | elimSkipLeft s =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt]
  | elimSkipRight s =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st hno_ub
    simp only [evalStmt] at hno_ub ⊢
    cases evalStmt st tgt <;> rfl
  | elimAssumeUB r limit =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st hno_ub
    simp only [evalStmt] at hno_ub ⊢
    by_cases hcond : st.regs r ≤ limit
    · simp [hcond]
    · simp [hcond] at hno_ub
  | seqCong d1 d2 ih1 ih2 =>
    cases src <;> cases tgt <;> simp only [checkStmtDeriv, Bool.and_eq_true] at h <;> try contradiction
    exact stmtRefines_seq (ih1 h.1) (ih2 h.2)
  | trans mid d1 d2 ih1 ih2 =>
    simp only [checkStmtDeriv, Bool.and_eq_true] at h
    exact stmtRefines_trans (ih1 h.1) (ih2 h.2)

/-- Top-level checker soundness theorem (`checkDeriv_sound`). -/
theorem checkDeriv_sound (src tgt : Prog) (d : Derivation)
    (h_check : checkDeriv src tgt d = true) (st : State) :
    refines (evalProg st src) (evalProg st tgt) := by
  simp only [checkDeriv, Bool.and_eq_true, decide_eq_true_eq] at h_check
  rcases h_check with ⟨⟨h_src_ret, h_tgt_ret⟩, h_body⟩
  have h_stmt := checkStmtDeriv_sound h_body st
  intro hno_ub
  simp only [evalProg] at hno_ub ⊢
  cases h_s : evalStmt st src.body with
  | val st' =>
    have h_ne : Outcome.val st' ≠ Outcome.ub := by nofun
    have h_t : evalStmt st tgt.body = Outcome.val st' := by
      rw [← h_s]
      exact h_stmt (by rw [h_s]; exact h_ne)
    rw [h_t, h_src_ret, h_tgt_ret]
  | panic =>
    have h_ne : (Outcome.panic : Outcome State) ≠ Outcome.ub := by nofun
    have h_t : evalStmt st tgt.body = Outcome.panic := by
      rw [← h_s]
      exact h_stmt (by rw [h_s]; exact h_ne)
    rw [h_t]
  | ub =>
    simp only [h_s] at hno_ub
    exact False.elim (hno_ub rfl)

end W6Proto
