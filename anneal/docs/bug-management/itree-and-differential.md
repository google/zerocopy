<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Differential & Interaction-Tree Bugs (`ITREE-*`, `DIFF-*`)

This note explains how findings from multi-step differential testing and
fuzzing map onto [two-phase bug management][two-phase]:

- `ITREE-<CATEGORY>-<12hex>`: multi-call and observable-trace differential
  fuzzing under [`tests/itree_diff/`][itree-outcome].
- `DIFF-<CATEGORY>-<12hex>`: standalone differential harnesses outside
  `itree_diff` (for example single-step interpreter comparisons and fuzzers).

## Which verdicts trigger Phase 0

Not every divergence between Miri/`rustc` and `Trusted.MirSemantics` is a
soundness defect:

- **Immediate Phase 0 (`UnsoundAccept` / `undeclared_ub_fault: true`):**
  Trigger Phase 0 immediately when a reference authority exhibits UB,
  diverges, or disagrees on terminal outcomes, observable events, or
  caller-frame preservation while `anneal-rustc-capture` and
  `Trusted.MirSemantics` accept the program, or when `.fault .undefined`
  fires on an accepting Miri run without a matching `DisclosedGapSpec`
  ([`TraceVerdict`][itree-outcome]).
- **Triage only (`ConservativeOverApprox`, `undeclared_ub_fault: false`):**
  Returning `.fault .unsupported` or refusing capture where Miri/`rustc`
  succeeds is a valid forward-simulation refinement (`forwardSim` holds).
  It never licenses UB refutation and does **not** require an emergency
  tripwire.
- **Harness errors (`ToolError`):** Fix harness, cache, or toolchain skew
  rather than adding capture refusals.

## Selecting Phase 0 containment vs. runtime fallback

1. **Prefer [`tripwires.rs`][tripwires-rs] (`Crate` or `Body` predicate):**
   Use static `PHASE0_TRIPWIRE!` rules whenever the defect correlates cleanly
   with crate options, unstable features, or specific MIR instructions, casts,
   or rvalues in `&mir::Body<'_>`. Static capture refusals leave Lean `.olean`
   proof caches and semantics proofs completely untouched.
2. **Fall back to [`Trusted/MirSemantics/`][step-lean] only when necessary:**
   When refusing an entire MIR construct statically would reject valid proof
   crates too broadly, add a bounded dynamic guard returning
   `.fault .unsupported` with a `-- PHASE0_TRIPWIRE(...)` annotation and a
   matching negative regression test.

## Phase 1 cleanup and witness replay

When landing the Phase-1 operational semantics fix:

1. Delete the `PHASE0_TRIPWIRE!` entry (or Lean guard + annotation) cleanly so
   `check_phase0_tripwires.py --mode phase1-cleanup` finds zero residual bug
   references in `anneal/trusted/`.
2. Retain the bound regression test function under
   `anneal/tests/{rustc-capture,itree_diff}/tests/` and flip it from
   `[PHASE0_TRIPWIRE:<BUG_ID>]` refusal to positive verification or `FaultUb`
   parity.
3. Replay all shrunk minimal witness programs bucketed under `<BUG_ID>` on the
   un-tripwired Phase-1 tree; never treat a leftover `[PHASE0_TRIPWIRE:*]`
   refusal as a passing fix.

[two-phase]: ../two-phase-bug-management.md
[itree-outcome]: ../../tests/itree_diff/src/outcome.rs
[tripwires-rs]: ../../trusted/rustc-capture/src/tripwires.rs
[step-lean]: ../../trusted/lean/Trusted/MirSemantics/Step.lean
