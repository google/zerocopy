-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynth.Macros

namespace RuleSynth.Synthesized40

/-- Metaprogrammed 1-line soundness proof for all 25 `ExprRewrite` constructors. -/
theorem inferExprRewrite_sound_synth (rw : ExprRewrite) (st : State) :
    evalExpr st (inferExprRewrite rw).1 = evalExpr st (inferExprRewrite rw).2 := by
  prove_expr_rw_sound rw

/-- Metaprogrammed 1-line soundness proof for all 15 `StmtDeriv` constructors
(covering all 40 `-O3` rules across Classes A, B, and C). -/
theorem checkStmtDeriv_sound_synth {src tgt : Stmt} {d : StmtDeriv} :
    checkStmtDeriv src tgt d = true → stmtRefines src tgt := by
  prove_hybrid_sound src tgt d using inferExprRewrite_sound_synth

/-- Metaprogrammed 1-line completeness proof for all 15 `StmtDeriv` constructors. -/
theorem checkStmtDeriv_complete_synth {src tgt : Stmt} {d : StmtDeriv} :
    ValidStmtDeriv src tgt d → checkStmtDeriv src tgt d = true := by
  prove_hybrid_complete

/-- Metaprogrammed 1-line bidirectional equivalence proof (`checkStmtDeriv = true ↔ ValidStmtDeriv`). -/
theorem checkStmtDeriv_iff_valid_synth {src tgt : Stmt} {d : StmtDeriv} :
    checkStmtDeriv src tgt d = true ↔ ValidStmtDeriv src tgt d := by
  prove_hybrid_iff_valid src tgt d

#print axioms inferExprRewrite_sound_synth
#print axioms checkStmtDeriv_sound_synth
#print axioms checkStmtDeriv_complete_synth
#print axioms checkStmtDeriv_iff_valid_synth

end RuleSynth.Synthesized40
