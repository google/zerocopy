-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp.Execution

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩
  intro id body found
  cases id with
  | zero =>
    injection found with hEq
    subst hEq
    refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)
    unfold ValidEntryArgs at valid
    change checkArgsMatch args [.int .isize false] = true at valid
    rw [checkArgsMatch_cons_iff] at valid
    let ⟨v, rest, hCons, hv, hNil⟩ := valid
    rw [checkArgsMatch_nil_iff] at hNil
    subst hCons; subst hNil
    rw [checkVal_int_iff] at hv
    let ⟨bits, hvEq, _⟩ := hv
    subst hvEq
    have hRun :
        Runs Captured.body_0 8 [.scalar ⟨.isize, false, bits⟩]
          (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
    exact (run_initial_success hRun).1
  | succ id => cases found

end Proof
