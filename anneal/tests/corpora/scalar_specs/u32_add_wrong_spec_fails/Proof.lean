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

-- === scope: add ===
theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      exact bodyVerified_of_safe rfl rfl (fun _ _ _ => by rfl)
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, fun _ _ _ _ => ?_⟩
    exact behavior_of_returns rfl rfl (by rfl)
      (run_initial_success (fuel := 16)
        (args := [.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩,
                  .scalar ⟨.i32, false, BitVec.ofNat 128 1⟩])
        (value := .scalar ⟨.i32, false, BitVec.ofNat 128 0⟩) rfl).2
-- === end-scope ===

end Proof
