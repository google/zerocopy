<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Correspondence Divergences (`LMIRI-*`, `MINIRUST-*`)

Anneal anchors `Trusted.MirSemantics` against two independent Rust MIR
specifications tracked under two distinct bug namespaces in
[two-phase bug management][two-phase]:

- `LMIRI-<CATEGORY>-<12hex>`: correspondence or semantic gaps against vendored
  `vendor/lean-miri/` and [`MirCorrespondenceProof`][lmiri-proof].
- `MINIRUST-<CATEGORY>-<12hex>`: correspondence or admission gaps against
  vendored `vendor/minirust/` specifications (`SpecAnchor`) and
  [`MiniRustProof`][minirust-proof].

Splitting these namespaces reflects their independent audit surfaces, anchor
tables, and failure modes: a discrepancy against `lean-miri`'s executable
interpreter may not exist in MiniRust's relational semantics, and vice versa.

## Intentional conservative gaps vs. actionable bugs

Not every divergence from a reference specification is a bug:

- **Documented conservative bounds (expected, no bug):** Deliberately stricter
  rules proved safe under forward simulation do not open bug records—for
  example `deinitMovedPlace = true` in [`mir-correspondence-design.md`][corr]
  or non-vacuous admission restrictions separating `MiniRustAdmitted` from
  `MiniRustExactAdmitted` in [`MiniRustProof`][minirust-proof].
- **Actionable `LMIRI-*` / `MINIRUST-*` bugs:** Open a public GitHub issue and
  consider a Phase-0 tripwire whenever an audit, canary, or theorem update
  exposes an unintended soundness mismatch (Anneal admits an execution the
  reference classifies as UB, breaks a codec round-trip invariant, or relies on
  an ungrounded admission assumption).

## Phase 0 and Phase 1 handling

- **Phase 0:** If a `LMIRI-*` or `MINIRUST-*` defect exposes `main` to accepting
  unsound crates while the correspondence update is in progress, isolate the
  affected MIR shape via `PHASE0_TRIPWIRE!` in [`tripwires.rs`][tripwires-rs]
  (preferring static capture refusal over touching `Trusted/MirSemantics/`).
- **Phase 1:** Fix `Trusted.MirSemantics`, extend the correspondence theorems
  and `SpecAnchor` mappings, update guard-mutation refutations in
  [`check_guard_mutation.py`][guard-mut] and [`check_minirust_pin.py`][pin-ci],
  delete the Phase-0 tripwire, and verify `--mode phase1-cleanup`.

[two-phase]: ../two-phase-bug-management.md
[lmiri-proof]: ../../correspondence/Anneal/MirCorrespondenceProof.lean
[minirust-proof]: ../../correspondence/Anneal/MiniRustProof.lean
[corr]: ../mir-correspondence-design.md
[tripwires-rs]: ../../trusted/rustc-capture/src/tripwires.rs
[guard-mut]: ../../ci/check_guard_mutation.py
[pin-ci]: ../../ci/check_minirust_pin.py
