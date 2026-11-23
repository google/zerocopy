-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteBase

/-!
# Positive Sanity Check for Guard-Mutation CI

Confirms that a basic UB-free program (`30u32 + 12u32 = 42u32`) still proves
against every single-guard mutant of `Trusted.MirSemantics`.

Why this matters: positive proofs keep passing when a UB guard is deleted or
weakened, which is precisely why guard-mutation CI pairs this sanity check with
explicit negative refutations. Passing this file on each mutant also rules out
accidental syntax or type errors that would otherwise masquerade as mutant
kills.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

theorem positive_sanity_add_u32 :
    Behavior (mkBinOpProg .add u32Ty u32Ty u32Ty)
      { args := [u32Val 30, u32Val 12] }
      (.returned ⟨u32Val 42, ⟨[]⟩⟩) :=
  behavior_of_execDone (fuel := 2) rfl

end GuardMutation
