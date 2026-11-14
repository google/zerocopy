-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynth.Rules40

namespace RuleSynth

/-- Synthesized inversion lemma for `.seqCong` over the 15-constructor `Stmt` type.
Eliminates the $15 \times 15 = 225$ off-diagonal case split (`PITFALL-4`) inside
`checkStmtDeriv_sound` and `checkStmtDeriv_iff_valid`. -/
theorem checkSeqCong_inv {src tgt : Stmt} {d1 d2 : StmtDeriv}
    (h : checkStmtDeriv src tgt (.seqCong d1 d2) = true) :
    ∃ s1 s2 t1 t2, src = .seq s1 s2 ∧ tgt = .seq t1 t2 ∧
      checkStmtDeriv s1 t1 d1 = true ∧ checkStmtDeriv s2 t2 d2 = true := by
  cases src <;> cases tgt <;> simp only [checkStmtDeriv, Bool.and_eq_true] at h <;> try contradiction
  exact ⟨_, _, _, _, rfl, rfl, h.1, h.2⟩

/-- Custom tactic `prove_expr_rw_sound` discharging all 25 Class A `ExprRewrite`
algebraic and bitwise soundness goals from `inferExprRewrite` in one line. -/
macro "prove_expr_rw_sound" rw:term : tactic =>
  `(tactic| (
    cases $rw:term <;>
      simp [inferExprRewrite, evalExpr,
            Int.add_zero, Int.zero_add, Int.sub_zero, Int.sub_self,
            Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul,
            Int.neg_neg, Int.add_right_neg, Int.sub_neg,
            Int.add_comm, Int.mul_comm,
            intBitAnd_self, intBitAnd_zero_right, intBitAnd_zero_left, intBitAnd_comm,
            intBitOr_self, intBitOr_zero_right, intBitOr_zero_left, intBitOr_comm,
            intBitXor_self]
  ))

/-- Custom tactic `prove_hybrid_complete` discharging 100% of `ValidStmtDeriv`
completeness obligations (`checkStmtDeriv_complete`) in a single line. -/
macro "prove_hybrid_complete" : tactic =>
  `(tactic| (
    intro h
    induction h <;> simp_all [checkStmtDeriv, checkDisjointNoAlias]
  ))

/-- Generic constructor-independent tactic `prove_hybrid_iff_valid` discharging
bidirectional equivalence (`checkStmtDeriv src tgt d = true ↔ ValidStmtDeriv src tgt d`)
across all 15 `StmtDeriv` constructors without naming individual rules. -/
macro "prove_hybrid_iff_valid" src:ident tgt:ident d:term : tactic =>
  `(tactic| (
    constructor
    · intro h
      induction $d:term generalizing $src $tgt with
      | seqCong d1 d2 ih1 ih2 =>
        rcases checkSeqCong_inv h with ⟨s1, s2, t1, t2, h1, h2, hc1, hc2⟩
        subst h1; subst h2
        exact .seqCong (ih1 hc1) (ih2 hc2)
      | _ =>
        simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
        first
        | (rcases h with ⟨⟨hs, ht⟩, ⟨h1, h2⟩⟩; subst h1; subst h2; constructor <;> assumption)
        | (rcases h with ⟨h1, h2⟩; subst h1; subst h2; constructor)
    · prove_hybrid_complete
  ))

/-- Generic constructor-independent tactic `prove_hybrid_sound` discharging all 15
`StmtDeriv` constructors across Classes A, B, and C using frame commutation
lemmas and `checkSeqCong_inv`. -/
macro "prove_hybrid_sound" src:ident tgt:ident d:term "using" exprSoundLem:term : tactic =>
  `(tactic| (
    intro h
    induction $d:term generalizing $src $tgt with
    | seqCong d1 d2 ih1 ih2 =>
      rcases checkSeqCong_inv h with ⟨s1, s2, t1, t2, h1, h2, hc1, hc2⟩
      subst h1; subst h2
      exact stmtRefines_seq (ih1 hc1) (ih2 hc2)
    | elimSkipRight s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨h1, h2⟩; subst h1; subst h2
      intro st hno_ub; simp only [evalStmt] at hno_ub ⊢; cases evalStmt st $tgt:term <;> rfl
    | elimAssumeOverflowUB r limit =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨h1, h2⟩; subst h1; subst h2
      intro st hno_ub; simp only [evalStmt] at hno_ub ⊢
      by_cases hcond : st.regs r ≤ limit <;> simp [hcond] at hno_ub ⊢
    | elimAssumeNonNegUB r =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨h1, h2⟩; subst h1; subst h2
      intro st hno_ub; simp only [evalStmt] at hno_ub ⊢
      by_cases hcond : 0 ≤ st.regs r <;> simp [hcond] at hno_ub ⊢
    | _ =>
      simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
      first
      | (rcases h with ⟨⟨hne_s, _⟩, ⟨h1, h2⟩⟩; subst h1; subst h2;
         intro st _; simp only [evalStmt, setSlot_get_ne _ _ hne_s, setSlot_get_same, evalExpr_setSlot]; rfl)
      | (rcases h with ⟨h1, h2⟩; subst h1; subst h2;
         first
         | exact stmtRefines_refl _
         | (intro st _; simp only [evalStmt, evalExpr, setSlot_get_same, setSlot_overwrite,
                                   setReg_overwrite, evalExpr_setSlot, ↓reduceIte];
            try rw [$exprSoundLem]))
  ))

end RuleSynth
