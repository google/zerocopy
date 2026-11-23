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

-- === scope: bad_ub ===
theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩
  intro id body found
  cases id with
  | zero =>
    injection found with hEq
    subst hEq
    refine bodyVerified_of_safe rfl rfl (fun _ _ hUnsafe => ?_)
    have _ : Captured.body_0.isUnsafe = true := by rfl
    exact absurd (hUnsafe this) (fun _ => True.intro)
  | succ id => cases found
-- === end-scope ===

end Proof
