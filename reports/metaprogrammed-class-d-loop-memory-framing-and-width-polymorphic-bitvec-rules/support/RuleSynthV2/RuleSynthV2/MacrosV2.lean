-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynthV2.Rules55

/-!
# Metaprogrammed Elaboration Macros for Class C/D Loop & Memory Rules (`MacrosV2.lean`)

Provides the `RuleSynthV2` tactic macros:
1. `prove_loop_mem_sound`: Discharges all 25 Class C memory-frame and Class D fuel-indexed loop
   soundness goals using the algebraic memory-lens `@[simp]` set (`setSlot_comm`,
   `evalExpr_setReg_of_notReads`, `setSlot_overwrite`) and reusable loop combinators
   (`evalStmt_while_unroll2`, `evalStmt_while_split`, `evalStmt_while_peel2`);
2. `prove_loop_mem_complete` & `prove_loop_mem_iff_valid`: Discharges 100% of completeness and
   bidirectional validity obligations in 1 line.
-/

namespace RuleSynthV2

@[simp] theorem setSlot_get_self_eq (st : State) (slot : SlotId) :
    st.setSlot slot (st.slots slot) = st := by
  cases st; simp only [State.setSlot, State.mk.injEq, true_and]
  funext s'; split
  · rename_i h; subst h; rfl
  · rfl

/-- Generic constructor-independent tactic macro discharging all 25 Class C memory-frame
and Class D loop soundness obligations in a single invocation, without naming individual
rule constructors! -/
macro "prove_loop_mem_sound" d:term : tactic =>
  `(tactic| (
    intro h
    unfold checkClassCDDeriv at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h_src, h_tgt⟩, hcond⟩
    subst h_src; subst h_tgt
    cases $d:term <;>
    first
    | (simp only [inferClassCDRule, evalStmt_while_unroll2, evalStmt_while_split,
                  evalStmt_while_peel2, evalStmt_while_peel1, evalStmt_while_zero,
                  evalStmt_seq_skip_right, evalStmt_seq_skip_left];
       intro st _; rfl; done)
    | (simp only [inferClassCDRule, Bool.and_eq_true, decide_eq_true_eq] at hcond;
       rcases hcond with ⟨hc1, hc2⟩;
       intro st _;
       simp only [inferClassCDRule, evalStmt, evalExpr, setSlot_get_ne _ _ hc1,
                  evalExpr_setReg_of_notReads _ _ _ _ hc2, setReg_get_same, setReg_setSlot_comm]; done)
    | (simp only [inferClassCDRule, decide_eq_true_eq] at hcond;
       intro st _;
       first
       | (simp only [inferClassCDRule, evalStmt, evalExpr_setSlot, setSlot_comm st _ _ hcond]; done)
       | (simp only [inferClassCDRule, evalStmt, setReg_slots, evalExpr, setReg_get_same]; done)
       | (simp only [inferClassCDRule, evalStmt, evalExpr_setReg_of_notReads _ _ _ _ hcond, setReg_overwrite]; done)
       | (simp only [inferClassCDRule, evalStmt, evalExpr_setSlot, evalExpr_setReg_of_notReads _ _ _ _ hcond, setReg_setSlot_comm]; done))
    | (intro st hno_ub;
       simp only [inferClassCDRule, evalStmt] at hno_ub ⊢;
       split at hno_ub <;> simp_all; done)
    | (intro st _;
       simp [inferClassCDRule, evalStmt, evalExpr, setSlot_overwrite, setSlot_get_same,
             setReg_get_same, setReg_setSlot_comm, setSlot_get_self_eq]; done)
    | (intro st _;
       simp only [inferClassCDRule, evalStmt]; cases evalStmt st _ <;> rfl; done)
  ))

/-- Generic completeness macro for `ValidClassCDDeriv`. -/
macro "prove_loop_mem_complete" : tactic =>
  `(tactic| (
    intro ⟨hs, ht, hc⟩
    simp [checkClassCDDeriv, hs, ht, hc]
  ))

/-- Generic bidirectional validity macro for `ClassCDDeriv`. -/
macro "prove_loop_mem_iff_valid" : tactic =>
  `(tactic| (
    constructor
    · intro h
      unfold checkClassCDDeriv at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · prove_loop_mem_complete
  ))

end RuleSynthV2
