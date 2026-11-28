-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.Backend.Rules
public import Anneal.Backend.CtxFact
public import Anneal.Backend.CongruenceDagCtx
public import Anneal.Backend.PassRefines

/-!
# Checked E-Graph Translation Validation (`Anneal.Backend`)

Pass-1 theory modules for translation validation of e-graph expression-DAG
rewrites and contextual assertion-guard elision over `Anneal.Hybrid`:

- `Anneal.Backend.Rules`: arena-free 64-bit `PoisonOr` word semantics,
  two-polarity `RelKind` (`eqExact` vs. `refines`), `freeze` monotonicity, and
  algebraic and contextual rewrite soundness theorems.
- `Anneal.Backend.CtxFact`: `TrustTier.proven` candidate filtering,
  value-evaluated assertion guards (`GuardCond`), conditional refinement
  (`SemRefinesUnder`), and guard-discharge soundness.
- `Anneal.Backend.CongruenceDagCtx`: topologically ordered two-polarity DAG
  congruence and rewrite trace checker (`verifyDagGoal_sound`,
  `checkBlockOpt_sound`).
- `Anneal.Backend.PassRefines`: `Anneal.Hybrid` gate composition
  (`PassRefines`, `verifiedPassToGate`, `composePassGates`), conditional
  contract lifting (`liftContractAlongRefinement`), `blockOptGate`, and
  `baselineIdentityPass`.
-/
