-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynthV2.MacrosV2

/-!
# Synthesized Soundness, Completeness, and Bidirectional Validity for 55 Rules (`SynthesizedClassCD25.lean`)

Discharges the full soundness, completeness, and bidirectional validity of all 25 Class C
memory-frame and Class D fuel-indexed loop rules (`ClassCDDeriv`) plus all 30 width-polymorphic
`BitVec w` (`8..128`-bit) Class A rules (`BVRewrite w`) in single-line `RuleSynthV2` macro invocations.
-/

namespace RuleSynthV2.Synthesized

open RuleSynthV2

theorem checkClassCDDeriv_sound_synth (src tgt : Stmt) (d : ClassCDDeriv) :
    checkClassCDDeriv src tgt d = true → stmtRefines src tgt := by
  prove_loop_mem_sound d

theorem checkClassCDDeriv_complete_synth (src tgt : Stmt) (d : ClassCDDeriv) :
    ValidClassCDDeriv src tgt d → checkClassCDDeriv src tgt d = true := by
  prove_loop_mem_complete

theorem checkClassCDDeriv_iff_valid_synth (src tgt : Stmt) (d : ClassCDDeriv) :
    checkClassCDDeriv src tgt d = true ↔ ValidClassCDDeriv src tgt d := by
  prove_loop_mem_iff_valid

theorem checkBVRewrite_sound_synth {w : WidthTag} (rw : BVRewrite w)
    (env : Nat → PoisonOr (BitVec w.bits)) :
    refinesPoison (evalBVExpr env (inferBVRewrite rw).1) (evalBVExpr env (inferBVRewrite rw).2) := by
  prove_bitvec_rw_sound w, rw with_env env

end RuleSynthV2.Synthesized
