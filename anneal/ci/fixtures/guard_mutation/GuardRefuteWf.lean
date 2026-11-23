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
# `WellFormed` Refutation Helper for Guard-Mutation Fixtures

Separated from `GuardRefuteBase` so `Boundary.lean` mutations that weaken
`WellFormed` can recompile `GuardRefuteBase` and `PositiveSanity` cleanly
before failing specifically inside `BoundaryRefutations.lean`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Lift `execFaultProg` into `ReachesResult p q (.fault k) ∧ ¬ WellFormed p q`.
-/
theorem refutes_wf_of_execFault {p : Program} {fuel : Nat} {q : Query}
    {k : FaultKind} (h : execFaultProg p fuel q k) :
    ReachesResult p q (.fault k) ∧ ¬ WellFormed p q :=
  let hReach := reachesResult_of_execFault h
  ⟨hReach, fun hWf => hWf.2 k hReach⟩

end GuardMutation
