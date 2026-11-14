-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynth.Rules40

namespace RuleSynth.Manual40

/-- Handwritten (`W6`-style) soundness proof for all 25 `ExprRewrite` constructors. -/
theorem inferExprRewrite_sound_manual (rw : ExprRewrite) (st : State) :
    evalExpr st (inferExprRewrite rw).1 = evalExpr st (inferExprRewrite rw).2 := by
  cases rw with
  | refl e =>
    rfl
  | addZeroRight e =>
    simp [inferExprRewrite, evalExpr, Int.add_zero]
  | addZeroLeft e =>
    simp [inferExprRewrite, evalExpr, Int.zero_add]
  | subZeroRight e =>
    simp [inferExprRewrite, evalExpr, Int.sub_zero]
  | subSelf e =>
    simp [inferExprRewrite, evalExpr, Int.sub_self]
  | mulOneRight e =>
    simp [inferExprRewrite, evalExpr, Int.mul_one]
  | mulOneLeft e =>
    simp [inferExprRewrite, evalExpr, Int.one_mul]
  | mulZeroRight e =>
    simp [inferExprRewrite, evalExpr, Int.mul_zero]
  | mulZeroLeft e =>
    simp [inferExprRewrite, evalExpr, Int.zero_mul]
  | negNeg e =>
    simp [inferExprRewrite, evalExpr, Int.neg_neg]
  | addNegSelf e =>
    simp [inferExprRewrite, evalExpr, Int.add_right_neg]
  | subNegToAdd a b =>
    simp [inferExprRewrite, evalExpr, Int.sub_neg]
  | addComm a b =>
    simp [inferExprRewrite, evalExpr, Int.add_comm]
  | mulComm a b =>
    simp [inferExprRewrite, evalExpr, Int.mul_comm]
  | bitAndSelf e =>
    simp [inferExprRewrite, evalExpr, intBitAnd_self]
  | bitAndZeroRight e =>
    simp [inferExprRewrite, evalExpr]
  | bitAndZeroLeft e =>
    simp [inferExprRewrite, evalExpr, intBitAnd_zero_left]
  | bitAndComm a b =>
    simp [inferExprRewrite, evalExpr, intBitAnd_comm]
  | bitOrSelf e =>
    simp [inferExprRewrite, evalExpr, intBitOr_self]
  | bitOrZeroRight e =>
    simp [inferExprRewrite, evalExpr]
  | bitOrZeroLeft e =>
    simp [inferExprRewrite, evalExpr, intBitOr_zero_left]
  | bitOrComm a b =>
    simp [inferExprRewrite, evalExpr, intBitOr_comm]
  | bitXorSelf e =>
    simp [inferExprRewrite, evalExpr, intBitXor_self]
  | shiftLeftZeroId e =>
    simp [inferExprRewrite, evalExpr]
  | freezeIdemp e =>
    simp [inferExprRewrite, evalExpr]

/-- Handwritten (`W6`-style) soundness proof for all 15 `StmtDeriv` constructors
(40 total `-O3` rules combined with `ExprRewrite`), including explicit $15 \times 15 = 225$
off-diagonal constructor elimination in `seqCong`. -/
theorem checkStmtDeriv_sound_manual (src tgt : Stmt) (d : StmtDeriv)
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
    simp only [evalStmt, inferExprRewrite_sound_manual rw st]
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
  | forwardAtomicAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
    simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
    rcases h with ⟨⟨hne_s, _⟩, ⟨rfl, rfl⟩⟩
    intro st _
    simp only [evalStmt, setSlot_get_ne _ _ hne_s, setSlot_get_same, evalExpr_setSlot]
  | elimOverwrittenStore slot t1 t2 e1 e2 =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt, setSlot_overwrite, evalExpr_setSlot]
  | elimOverwrittenAssign dst v1 v2 =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt, evalExpr, setReg_overwrite]
  | foldReadOnlyCall dst arg =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt]
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
  | elimDbgValue r metaId =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt]
  | elimAssumeOverflowUB r limit =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st hno_ub
    simp only [evalStmt] at hno_ub ⊢
    by_cases hcond : st.regs r ≤ limit
    · simp [hcond]
    · simp [hcond] at hno_ub
  | elimAssumeNonNegUB r =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st hno_ub
    simp only [evalStmt] at hno_ub ⊢
    by_cases hcond : 0 ≤ st.regs r
    · simp [hcond]
    · simp [hcond] at hno_ub
  | foldIfZeroTrue thenBr elseBr =>
    simp only [checkStmtDeriv, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    intro st _
    simp only [evalStmt, ↓reduceIte]
  | seqCong d1 d2 ih1 ih2 =>
    cases src <;> cases tgt <;> simp only [checkStmtDeriv, Bool.and_eq_true] at h <;> try contradiction
    exact stmtRefines_seq (ih1 _ _ h.1) (ih2 _ _ h.2)

/-- Handwritten (`W6`-style) completeness proof across all 15 `StmtDeriv` constructors. -/
theorem checkStmtDeriv_complete_manual {src tgt : Stmt} {d : StmtDeriv}
    (h : ValidStmtDeriv src tgt d) : checkStmtDeriv src tgt d = true := by
  induction h with
  | refl s =>
    simp [checkStmtDeriv]
  | rewriteAssign dst rw =>
    simp [checkStmtDeriv]
  | promoteSlotToAssign slot tag dst e =>
    simp [checkStmtDeriv]
  | forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 h_slot h_tag =>
    simp [checkStmtDeriv, checkDisjointNoAlias, h_slot, h_tag]
  | forwardAtomicAcrossNoAlias s1 s2 t1 t2 dst e1 e2 h_slot h_tag =>
    simp [checkStmtDeriv, checkDisjointNoAlias, h_slot, h_tag]
  | elimOverwrittenStore slot t1 t2 e1 e2 =>
    simp [checkStmtDeriv]
  | elimOverwrittenAssign dst v1 v2 =>
    simp [checkStmtDeriv]
  | foldReadOnlyCall dst arg =>
    simp [checkStmtDeriv]
  | elimSkipLeft s =>
    simp [checkStmtDeriv]
  | elimSkipRight s =>
    simp [checkStmtDeriv]
  | elimDbgValue r metaId =>
    simp [checkStmtDeriv]
  | elimAssumeOverflowUB r limit =>
    simp [checkStmtDeriv]
  | elimAssumeNonNegUB r =>
    simp [checkStmtDeriv]
  | foldIfZeroTrue thenBr elseBr =>
    simp [checkStmtDeriv]
  | seqCong _ _ ih1 ih2 =>
    simp [checkStmtDeriv, ih1, ih2]

/-- Handwritten (`W6`-style) bidirectional equivalence proof across all 15 `StmtDeriv` constructors. -/
theorem checkStmtDeriv_iff_valid_manual {src tgt : Stmt} {d : StmtDeriv} :
    checkStmtDeriv src tgt d = true ↔ ValidStmtDeriv src tgt d := by
  constructor
  · intro h
    induction d generalizing src tgt with
    | refl s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .refl _
    | rewriteAssign dst rw =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .rewriteAssign dst rw
    | promoteSlotToAssign slot tag dst e =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .promoteSlotToAssign slot tag dst e
    | forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
      simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
      rcases h with ⟨⟨hs, ht⟩, ⟨rfl, rfl⟩⟩
      exact .forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 hs ht
    | forwardAtomicAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
      simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
      rcases h with ⟨⟨hs, ht⟩, ⟨rfl, rfl⟩⟩
      exact .forwardAtomicAcrossNoAlias s1 s2 t1 t2 dst e1 e2 hs ht
    | elimOverwrittenStore slot t1 t2 e1 e2 =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimOverwrittenStore slot t1 t2 e1 e2
    | elimOverwrittenAssign dst v1 v2 =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimOverwrittenAssign dst v1 v2
    | foldReadOnlyCall dst arg =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .foldReadOnlyCall dst arg
    | elimSkipLeft s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimSkipLeft _
    | elimSkipRight s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimSkipRight _
    | elimDbgValue r metaId =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimDbgValue r metaId
    | elimAssumeOverflowUB r limit =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimAssumeOverflowUB r limit
    | elimAssumeNonNegUB r =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimAssumeNonNegUB r
    | foldIfZeroTrue thenBr elseBr =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .foldIfZeroTrue _ elseBr
    | seqCong d1 d2 ih1 ih2 =>
      cases src <;> cases tgt <;> simp only [checkStmtDeriv, Bool.and_eq_true] at h <;> try contradiction
      exact .seqCong (ih1 h.1) (ih2 h.2)
  · exact checkStmtDeriv_complete_manual

end RuleSynth.Manual40
