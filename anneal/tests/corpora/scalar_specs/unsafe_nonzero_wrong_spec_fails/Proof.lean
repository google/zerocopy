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

-- === scope: nonzero_only ===
theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun _ _ _ => ?_)
      have hRun : Runs Captured.body_0 16
          [.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩]
          (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := by rfl
      exact (run_initial_success hRun).1
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, fun _ _ _ => ?_⟩
    have hRun : Runs Captured.body_0 16
        [.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩]
        (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := by rfl
    exact behavior_of_returns rfl rfl (by rfl) (run_initial_success hRun).2
-- === end-scope ===

end Proof
