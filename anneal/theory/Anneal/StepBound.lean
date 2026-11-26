-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.StepBound.Core
public import Anneal.StepBound.V2Loop
public import Anneal.StepBound.CnfOrdBridge

/-!
# Quantitative Step-Bound Library (`Anneal.StepBound`)

Umbrella module exporting Pass-1-portable (`0`-TCB, zero banned tactics, zero
`._unsafe_rec`) quantitative MIR step-bound abstractions and loop combinators:

- `Anneal.StepBound.Core`: `ReachesDoneWithin` / `ExecWithinSteps` (Profile v1),
  `ReachesDoneWithinV2` / `ExecWithinStepsV2` (Profile v2), exact equivalences
  with `wpProg` / `execProgV2`, `v2_adequacy_bounded`,
  `StepsToV1` / `StepsToV2`,
  `BoundedReachV1` / `BoundedReachV2`, and non-vacuity / under-budget
  refutation helpers.
- `Anneal.StepBound.V2Loop`: sequential composition (`b₁ + b₂`), constant-bound
  and rank-decreasing bounded loops (`n * bodyBound + exitBound`), linear
  progress-weighted (`K * m + C`) byte-credit loops, and `BodyCtx` wrappers.
- `Anneal.StepBound.CnfOrdBridge`: `< ω^ω` ordinal step-budget extraction over
  `Anneal.CnfOrd`, closed-form quadratic ceiling `lex2Bound` for bounded-reset
  nested loops (`ω^1 · outer + ω^0 · inner`), reactive per-frame prefix
  contracts (`ReactiveStepContractV2`), and `Worklist` / `CnfStepConverges`
  step-bound bridges.
-/
